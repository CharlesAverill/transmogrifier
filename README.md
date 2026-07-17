# Transmogrifier

A formally-verified extension to CompCert for compiling finite state automata.
Built atop [lstar-rocq](https://github.com/CharlesAverill/lstar-rocq).

Currently-supported automata:
- [x] DFAs
- [ ] NFAs
- [x] Moore Machines
- [ ] Mealy Machines

## Building

```bash
# Clone
git clone --recurse-submodules https://github.com/CharlesAverill/Transmogfrifier
cd Transmogrifier

# Install Dependencies
opam switch create rocq 4.14.3
opam repo add rocq-released https://rocq-prover.org/opam/released && opam update
opam pin add rocq-runtime 9.1.0
opam install . --deps-only

# Build
dune build
```

## Correctness

Verified against CompCert's Clight semantics in [`dfaproofs.v`](theories/transparency/dfaproofs.v):

- `compile_delta_correct` - `delta(q_i, s_i)` evaluates to the index of `δ(q, s)`
- `compile_delta_sink` - `delta` returns `|Q|` on out-of-range input
- `compile_accept_correct` - `accept(q_i)` returns `1` iff `q \in F`
- `compile_run_correct` - `run(w, |w|)` evaluates to the index of `δ*(q_0, w)`

## Example

Consider the language of alternating bitstrings:

$$
\\{\\, w \in \\{0,1\\}^* \mid \forall i \in [1,|w|-1],\\; w_i \neq w_{i+1} \\,\\}.
$$

This language can be recognized by the following 4-state DFA:

![alternating DFA](vendor/alternating_1.png)

[`alternating.ml`](examples/alternating.ml) initializes a teacher for this language, initiates the learning loop, and generates a C program containing a reference to the initial state, the transition function, the accept function, and a run function at [`alternating.c`](examples/alternating.c):

```c
unsigned long long delta(unsigned long long, unsigned long long);
_Bool accept(unsigned long long);
unsigned long long run(unsigned long long *, unsigned long long);
int $12(void);
unsigned long long const table[8] = { 2LL, 1LL, 1LL, 1LL, 1LL, 0LL, 2LL, 0LL,
  };

unsigned int const atable[4] = { 1, 0, 1, 1, };

unsigned long long delta(unsigned long long $6, unsigned long long $7)
{
  if ($6 < 4LLU & $7 < 2LLU) {
    return *(table + ($6 * 2LLU + $7));
  } else {
    return 4LLU;
  }
}

_Bool accept(unsigned long long $6)
{
  if ($6 < 4LLU) {
    return *(atable + $6);
  } else {
    return (_Bool) 0U;
  }
}

unsigned long long const q0 = 3LL;

unsigned long long run(unsigned long long *$8, unsigned long long $9)
{
  register unsigned long long $10;
  register unsigned long long $6;
  $10 = 0LLU;
  $6 = 3LLU;
  while (1) {
    if (! ($10 < $9)) {
      break;
    }
    $6 = delta($6, *($8 + $10));
    $10 = $10 + 1LLU;
  }
  return $6;
}

int $12(void)
{
  return 0;
}
```

Compiling with CompCert, we get the following machine code:

```
$ ccomp -c -O3 examples/alternating.c
$ objdump -d alternating.o 

alternating.o:     file format elf64-x86-64


Disassembly of section .text:

0000000000000000 <delta>:
   0:   48 83 ec 08             sub    $0x8,%rsp
   4:   48 8d 44 24 10          lea    0x10(%rsp),%rax
   9:   48 89 04 24             mov    %rax,(%rsp)
   d:   48 83 ff 04             cmp    $0x4,%rdi
  11:   0f 92 c2                setb   %dl
  14:   0f b6 d2                movzbl %dl,%edx
  17:   48 83 fe 02             cmp    $0x2,%rsi
  1b:   41 0f 92 c0             setb   %r8b
  1f:   45 0f b6 c0             movzbl %r8b,%r8d
  23:   44 21 c2                and    %r8d,%edx
  26:   83 fa 00                cmp    $0x0,%edx
  29:   74 11                   je     3c <delta+0x3c>
  2b:   4c 8d 05 00 00 00 00    lea    0x0(%rip),%r8        # 32 <delta+0x32>
  32:   48 8d 0c 7e             lea    (%rsi,%rdi,2),%rcx
  36:   49 8b 04 c8             mov    (%r8,%rcx,8),%rax
  3a:   eb 05                   jmp    41 <delta+0x41>
  3c:   b8 04 00 00 00          mov    $0x4,%eax
  41:   48 83 c4 08             add    $0x8,%rsp
  45:   c3                      ret
  46:   66 2e 0f 1f 84 00 00    cs nopw 0x0(%rax,%rax,1)
  4d:   00 00 00 

0000000000000050 <accept>:
  50:   48 83 ec 08             sub    $0x8,%rsp
  54:   48 8d 44 24 10          lea    0x10(%rsp),%rax
  59:   48 89 04 24             mov    %rax,(%rsp)
  5d:   48 83 ff 04             cmp    $0x4,%rdi
  61:   73 15                   jae    78 <accept+0x28>
  63:   48 8d 05 00 00 00 00    lea    0x0(%rip),%rax        # 6a <accept+0x1a>
  6a:   8b 04 b8                mov    (%rax,%rdi,4),%eax
  6d:   83 f8 00                cmp    $0x0,%eax
  70:   0f 95 c0                setne  %al
  73:   0f b6 c0                movzbl %al,%eax
  76:   eb 02                   jmp    7a <accept+0x2a>
  78:   31 c0                   xor    %eax,%eax
  7a:   48 83 c4 08             add    $0x8,%rsp
  7e:   c3                      ret
  7f:   90                      nop

0000000000000080 <run>:
  80:   48 83 ec 28             sub    $0x28,%rsp
  84:   48 8d 44 24 30          lea    0x30(%rsp),%rax
  89:   48 89 04 24             mov    %rax,(%rsp)
  8d:   48 89 5c 24 08          mov    %rbx,0x8(%rsp)
  92:   48 89 6c 24 10          mov    %rbp,0x10(%rsp)
  97:   4c 89 64 24 18          mov    %r12,0x18(%rsp)
  9c:   48 89 f3                mov    %rsi,%rbx
  9f:   48 89 fd                mov    %rdi,%rbp
  a2:   4d 31 e4                xor    %r12,%r12
  a5:   bf 03 00 00 00          mov    $0x3,%edi
  aa:   49 39 dc                cmp    %rbx,%r12
  ad:   73 14                   jae    c3 <run+0x43>
  af:   4a 8b 74 e5 00          mov    0x0(%rbp,%r12,8),%rsi
  b4:   e8 00 00 00 00          call   b9 <run+0x39>
  b9:   48 89 c7                mov    %rax,%rdi
  bc:   4d 8d 64 24 01          lea    0x1(%r12),%r12
  c1:   eb e7                   jmp    aa <run+0x2a>
  c3:   48 89 f8                mov    %rdi,%rax
  c6:   48 8b 5c 24 08          mov    0x8(%rsp),%rbx
  cb:   48 8b 6c 24 10          mov    0x10(%rsp),%rbp
  d0:   4c 8b 64 24 18          mov    0x18(%rsp),%r12
  d5:   48 83 c4 28             add    $0x28,%rsp
  d9:   c3                      ret
  da:   66 0f 1f 44 00 00       nopw   0x0(%rax,%rax,1)

00000000000000e0 <$12>:
  e0:   48 83 ec 08             sub    $0x8,%rsp
  e4:   48 8d 44 24 10          lea    0x10(%rsp),%rax
  e9:   48 89 04 24             mov    %rax,(%rsp)
  ed:   31 c0                   xor    %eax,%eax
  ef:   48 83 c4 08             add    $0x8,%rsp
  f3:   c3                      ret
```
