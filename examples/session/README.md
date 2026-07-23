# Session Handshake Example

Learn the state machine encoded by a piece of memory-unsafe legacy C ([`session_legacy.c`](session_legacy.c)), then
replace that C with a functionally-equivalent but memory-safe compiled state machine ([`session_modern.c`](session_modern.c) and [`out/session.c`](out/session.c)).

- Input alphabet: `h` HELLO, `a` AUTH, `r` REQUEST, `k` KEEPALIVE, `x` CLOSE
- Output alphabet: `DENY`, `WAIT`, `PROCEED`, `GRANT`, `BYE`
- Wire format: one opcode byte each, except `a` `<len>` `<len token bytes>`

## Running

```bash
# from the repository root
./examples/session/session_demo.sh
```

Requires `ccomp`, `dune`, and `python3`, plus a compiler that accepts
`-fsanitize=address` for the two sections that demonstrate the bug. Everything
the demo generates lands in [`out/`](out/), which is safe to delete and safe to
gitignore.

```
--- 1. legacy normal operation ---
WAIT
PROCEED
GRANT
PROCEED
GRANT
```

## Memory Vulnerability

`slurp_token` copies the presented token into a 32-byte stack buffer, bounded by
the length prefix off the wire rather than by the size of the buffer:

```c
static int slurp_token(const char *wire, size_t n) {
    char scratch[32];
    memcpy(scratch, wire, n);        /* n is attacker-controlled */
```

```
--- 2. legacy memory error ---
==554==ERROR: AddressSanitizer: stack-buffer-overflow on address 0x7f133e600060
    #0 ... in memcpy
    #1 ... in slurp_token examples/session/session_legacy.c:74
    #2 ... in handle_auth examples/session/session_legacy.c:101
    #3 ... in handle_auth examples/session/session_legacy.c:98
    #4 ... in main examples/session/session_legacy.c:136
```

## Learning

[`learn_compile.ml`](learn_compile.ml) learns a Mealy machine that encodes the
same state machine behavior as the legacy machine.

```
--- 3. learner ---
Accuracy: 780/780
Wrote .../examples/session/out/session.c
Wrote .../examples/session/out/session.h (4 states)
```

Four states are learned: the three handshake phases plus an absorbing state entered on CLOSE.

| | `h` | `a` | `r` | `k` | `x` |
| --- | --- | --- | --- | --- | --- |
| **3** init | 2 / `WAIT` | 3 / `DENY` | 3 / `DENY` | 3 / `DENY` | 1 / `BYE` |
| **2** hello-seen | 2 / `DENY` | 0 / `PROCEED` | 2 / `DENY` | 2 / `PROCEED` | 1 / `BYE` |
| **0** authed | 0 / `DENY` | 0 / `DENY` | 0 / `GRANT` | 0 / `PROCEED` | 1 / `BYE` |
| **1** closed | 1 / `BYE` | 1 / `BYE` | 1 / `BYE` | 1 / `BYE` | 1 / `BYE` |

## The compiled machine

`out/session.c`, emitted as Clight and compiled by CompCert. Two flat tables and
a bounds-checked lookup:

```c
unsigned long long const table[20] = { 0LL, 0LL, 0LL, 0LL, 1LL, 1LL, 1LL,
  1LL, 1LL, 1LL, 2LL, 0LL, 2LL, 2LL, 1LL, 2LL, 3LL, 3LL, 3LL, 1LL, };

unsigned long long const otable[20] = { 0LL, 0LL, 3LL, 2LL, 4LL, 4LL, 4LL,
  4LL, 4LL, 4LL, 0LL, 2LL, 0LL, 2LL, 4LL, 1LL, 0LL, 0LL, 0LL, 4LL, };

unsigned long long delta(unsigned long long $5, unsigned long long $6, unsigned long long *$7)
{
  if ($5 < 4LLU & $6 < 5LLU) {
    *$7 = *(otable + ($5 * 5LLU + $6));
    return *(table + ($5 * 5LLU + $6));
  } else {
    *$7 = 5LLU;
    return 4LLU;
  }
}

unsigned long long const q0 = 3LL;
```

`delta(q, a, &o)` returns the successor state and writes the output index of
that edge through `o`, which is `compile_delta_correct`.

## The replacement

[`session_modern.c`](session_modern.c) uses the safe compiled version of the state machine.
Session token validation is not a part of the state machine.

Section 5 of the demo script runs both binaries over the same words:

```
Token    Legacy Response                    Modern Response                    Matching
h        WAIT                               WAIT                               ok
a        DENY                               DENY                               ok
r        DENY                               DENY                               ok
x        BYE                                BYE                                ok
ha       WAIT PROCEED                       WAIT PROCEED                       ok
har      WAIT PROCEED GRANT                 WAIT PROCEED GRANT                 ok
hark     WAIT PROCEED GRANT PROCEED         WAIT PROCEED GRANT PROCEED         ok
harkr    WAIT PROCEED GRANT PROCEED GRANT   WAIT PROCEED GRANT PROCEED GRANT   ok
rrr      DENY DENY DENY                     DENY DENY DENY                     ok
hax      WAIT PROCEED BYE                   WAIT PROCEED BYE                   ok
kkk      DENY DENY DENY                     DENY DENY DENY                     ok
harxr    WAIT PROCEED GRANT BYE             WAIT PROCEED GRANT BYE             ok
harrr    WAIT PROCEED GRANT GRANT GRANT     WAIT PROCEED GRANT GRANT GRANT     ok
```

Section 6 runs ASan on the modern binary and finds no stack buffer overflow vulnerability.
