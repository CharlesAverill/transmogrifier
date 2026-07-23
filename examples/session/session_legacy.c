/* An authentication-handshake validator that gates a
 * resource: a client must send HELLO, then AUTH with the right token, before
 * any REQUEST is honored.
 *
 * Alphabet (one message opcode per input byte):
 *   'h' = HELLO   'a' = AUTH (length-prefixed token field follows)
 *   'r' = REQUEST 'k' = KEEPALIVE   'x' = CLOSE
 * Per-message output (the disposition, printed -- one per opcode):
 *   DENY, WAIT, PROCEED, GRANT, BYE
 *
 * Vulnerability: an AUTH message whose length-prefixed token field exceeds the 
 * 32-byte on-stack scratch buffer overflows it.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

/* The phase (0 init, 1 hello-seen, 2 authed) is the real state. The `armed`
 * bit, the `step` counter and the flag words are redundant with it; reflag()
 * keeps them in sync. */
static int  phase = 0;
static int  armed = 0;          /* "have we seen HELLO" -- redundant with phase>=1 */
static int  step  = 0;          /* messages processed; feeds only the history ring */
static unsigned flagword = 0;
#define F_BYE    0x01u
#define F_HELLO  0x02u
#define F_AUTHED 0x04u
#define F_DIRTY  0x08u

#define HIST 8
static int  hist[HIST];
static int  hist_i = 0;
static void remember(int c) { hist[hist_i] = c; hist_i = (hist_i + 1) % HIST; }

static const char *SECRET_TOKEN = "s3cr3t-handshake-key";

static void emit(const char *s) { fputs(s, stdout); fputc('\n', stdout); }

/* Mirror `phase` into the redundant flag bits. */
static void reflag(void) {
    if (phase >= 1) flagword |=  F_HELLO;  else flagword &= ~F_HELLO;
    if (phase >= 2) flagword |=  F_AUTHED; else flagword &= ~F_AUTHED;
    armed = (phase >= 1);
    flagword &= ~F_DIRTY;
}

/* Copy the presented token into an on-stack scratch buffer and compare it to
 * the secret. */
__attribute__((noinline))
static int slurp_token(const char *wire, size_t n) {
    char scratch[32];
    volatile char sink = 0;
    memcpy(scratch, wire, n);
    scratch[n < sizeof(scratch) ? n : sizeof(scratch) - 1] = '\0';
    for (size_t i = 0; i < sizeof(scratch); i++) sink ^= scratch[i];
    (void) sink;
    return strcmp(scratch, SECRET_TOKEN) == 0;
}

/* AUTH handler, a recursive descent over the token field. `depth` distinguishes
 * the initial call from the tail call that decides. */
static int handle_auth(char *wire, int field_len, int got, int depth) {
    if (depth == 0) {
        /* pull the remaining token bytes off stdin into wire[] */
        while (got < field_len) {
            int b = getchar();
            if (b == EOF) return -1;        /* signal: hit EOF mid-field */
            wire[got++] = (char) b;
        }
        return handle_auth(wire, field_len, got, 1);   /* tail: decide */
    }
    /* depth==1: field fully present. Copy runs regardless of phase. */
    int token_ok = slurp_token(wire, (size_t) field_len);
    return (phase == 1 && token_ok) ? 1 : 0;
}

int main(void) {
    int ch;

    /* Each opcode jumps to its label and falls through to `commit`. */
    for (;;) {
        ch = getchar();
        if (ch == EOF) goto done;
        step++;
        remember(ch);

        if (ch == '\n') continue;
        if (ch == 'h') goto L_hello;
        if (ch == 'a') goto L_auth;
        if (ch == 'r') goto L_request;
        if (ch == 'k') goto L_keepalive;
        if (ch == 'x') goto L_close;
        continue;                            /* junk byte */

    L_hello:
        if (!(flagword & F_HELLO) && phase == 0) {
            phase = 1; reflag(); emit("WAIT");
        } else {
            emit("DENY");                    /* HELLO out of order */
        }
        goto commit;

    L_auth: {
            int field_len = getchar();
            if (field_len == EOF) goto done;
            char *wire = malloc(field_len ? field_len : 1);
            if (!wire) goto done;
            int r = handle_auth(wire, field_len, 0, 0);
            free(wire);
            if (r < 0) goto done;            /* EOF mid-field */
            if (r == 1) { phase = 2; reflag(); emit("PROCEED"); }
            else        { emit("DENY"); }    /* bad token or wrong phase */
        }
        goto commit;

    L_request:
        /* GRANT iff authenticated. The flag check is redundant with the phase
         * check; reflag() keeps them in agreement. */
        if (phase == 2 && (flagword & F_AUTHED)) emit("GRANT");
        else                                     emit("DENY");
        goto commit;

    L_keepalive:
        if (phase == 0 && !armed) emit("DENY");
        else                      emit("PROCEED");   /* stay put */
        goto commit;

    L_close:
        flagword |= F_BYE; emit("BYE");
        goto commit;

    commit:
        if (flagword & F_BYE) break;
    }

done:
    return 0;
}
