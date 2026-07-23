/* An update to session_legacy.c that uses a learned Mealy machine
 * rather than a custom implementation
 */

#include <stdio.h>
#include <string.h>
#include "session.h"

enum { SYM_HELLO = SYM_H, SYM_AUTH = SYM_A, SYM_REQUEST = SYM_R, SYM_KEEPALIVE = SYM_K,
       SYM_CLOSE = SYM_X };

static const char *OUT_NAMES[] = { "DENY", "WAIT", "PROCEED", "GRANT", "BYE" };
#define NOUT     ((int)(sizeof OUT_NAMES / sizeof OUT_NAMES[0]))
#define OUT_DENY 0

static const char *SECRET = "s3cr3t-handshake-key";

/* Read a length-prefixed token from stdin and decide whether it is the secret. */
static int check_token(int *eof) {
    char buf[64];
    size_t n = 0;
    int field_len = getchar();
    if (field_len == EOF) { *eof = 1; return 0; }

    for (int i = 0; i < field_len; i++) {
        int b = getchar();
        if (b == EOF) { *eof = 1; break; }
        if (n < sizeof buf - 1) buf[n++] = (char) b;   /* bounded store */
    }
    buf[n] = '\0';
    return n == strlen(SECRET) && memcmp(buf, SECRET, n) == 0;
}

static void print_out(mealy_output_t o) {
    if (o < (mealy_output_t) NOUT) puts(OUT_NAMES[o]);
    else                           puts("DENY");   /* sink index -> reject */
}

int main(void) {
    mealy_state_t q = q0;
    int ch;

    while ((ch = getchar()) != EOF) {
        mealy_symbol_t sym;
        switch (ch) {
            case 'h': sym = SYM_HELLO;     break;
            case 'r': sym = SYM_REQUEST;   break;
            case 'k': sym = SYM_KEEPALIVE; break;
            case 'x': sym = SYM_CLOSE;     break;
            case 'a': {
                /* AUTH: validate the token outside the FSM. */
                int eof = 0;
                int ok = check_token(&eof);
                if (!ok) {
                    /* bad token: do NOT take the AUTH edge; phase unchanged. */
                    print_out(OUT_DENY);
                    if (eof) {
                        sym = SYM_CLOSE;
                        break;
                    }
                    continue;
                }
                sym = SYM_AUTH;            /* valid token -> take the AUTH edge */
                break;
            }
            case '\n': continue;
            default:   continue;          /* ignore junk */
        }

        mealy_output_t o;
        q = delta(q, sym, &o);            /* verified transition + output */
        print_out(o);

        if (sym == SYM_CLOSE) break;
    }

done:
    return 0;
}
