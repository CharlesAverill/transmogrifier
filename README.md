# Transmogrifier

A formally-verified extension to CompCert for compiling finite state automata.
Built atop [lstar-rocq](https://github.com/CharlesAverill/lstar-rocq).

Currently-supported automata:
- [x] DFAs
- [ ] NFAs
- [ ] Moore Machines
- [ ] Mealy Machines

## Building

```bash
# Clone
git clone --recurse-submodules https://github.com/CharlesAverill/Transmogfrifier
cd Transmogrifier
git submodule update --init

# Install Dependencies
opam switch create rocq 4.14.3
opam repo add rocq-released https://rocq-prover.org/opam/released && opam update
opam pin add rocq-runtime 9.1.0
opam pin add lstar-rocq git+https://github.com/CharlesAverill/lstar-rocq.git
opam install . --deps-only

# Build
dune build
```

## Example

Consider the language of alternating bitstrings:

$$
\\{\\, w \in \\{0,1\\}^* \mid \forall i \in [1,|w|-1],\\; w_i \neq w_{i+1} \\,\\}.
$$

This language can be recognized by the following 4-state DFA:

![alternating DFA](vendor/alternating_1.png)

[`alternating.ml`](examples/alternating.ml) initializes a teacher for this language, initiates the learning loop, and generates a C program containing a reference to the initial state, the transition function, and the accept function at [`alternating.c`](examples/alternating.c):

```c
unsigned long long delta(unsigned long long, unsigned long long);
_Bool accept(unsigned long long);
unsigned long long run(unsigned long long *, unsigned long long);
int $11(void);
unsigned long long const table[8] = { 2LL, 1LL, 1LL, 1LL, 1LL, 0LL, 2LL, 0LL,
  };

unsigned long long delta(unsigned long long $5, unsigned long long $6)
{
  if ($5 < 4LLU & $6 < 2LLU) {
    return *(table + ($5 * 2LLU + $6));
  } else {
    return 4LLU;
  }
}

_Bool accept(unsigned long long $5)
{
  if ($5 == 3LLU) {
    return 1;
  } else {
    if ($5 == 2LLU) {
      return 1;
    } else {
      if ($5 == 0LLU) {
        return 1;
      } else {
        return 0;
      }
    }
  }
}

unsigned long long const q0 = 3LL;

unsigned long long run(unsigned long long *$7, unsigned long long $8)
{
  register unsigned long long $9;
  register unsigned long long $5;
  $9 = 0LLU;
  $5 = 3LLU;
  while (1) {
    if (! ($9 < $8)) {
      break;
    }
    $5 = delta($5, *($7 + $9));
    $9 = $9 + 1LLU;
  }
  return $5;
}

int $11(void)
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
  5d:   48 83 ff 03             cmp    $0x3,%rdi
  61:   74 1e                   je     81 <accept+0x31>
  63:   48 83 ff 02             cmp    $0x2,%rdi
  67:   74 11                   je     7a <accept+0x2a>
  69:   48 83 ff 00             cmp    $0x0,%rdi
  6d:   74 04                   je     73 <accept+0x23>
  6f:   31 c0                   xor    %eax,%eax
  71:   eb 13                   jmp    86 <accept+0x36>
  73:   b8 01 00 00 00          mov    $0x1,%eax
  78:   eb 0c                   jmp    86 <accept+0x36>
  7a:   b8 01 00 00 00          mov    $0x1,%eax
  7f:   eb 05                   jmp    86 <accept+0x36>
  81:   b8 01 00 00 00          mov    $0x1,%eax
  86:   48 83 c4 08             add    $0x8,%rsp
  8a:   c3                      ret
  8b:   0f 1f 44 00 00          nopl   0x0(%rax,%rax,1)

0000000000000090 <run>:
  90:   48 83 ec 28             sub    $0x28,%rsp
  94:   48 8d 44 24 30          lea    0x30(%rsp),%rax
  99:   48 89 04 24             mov    %rax,(%rsp)
  9d:   48 89 5c 24 08          mov    %rbx,0x8(%rsp)
  a2:   48 89 6c 24 10          mov    %rbp,0x10(%rsp)
  a7:   4c 89 64 24 18          mov    %r12,0x18(%rsp)
  ac:   48 89 f3                mov    %rsi,%rbx
  af:   48 89 fd                mov    %rdi,%rbp
  b2:   4d 31 e4                xor    %r12,%r12
  b5:   bf 03 00 00 00          mov    $0x3,%edi
  ba:   49 39 dc                cmp    %rbx,%r12
  bd:   73 14                   jae    d3 <run+0x43>
  bf:   4a 8b 74 e5 00          mov    0x0(%rbp,%r12,8),%rsi
  c4:   e8 00 00 00 00          call   c9 <run+0x39>
  c9:   48 89 c7                mov    %rax,%rdi
  cc:   4d 8d 64 24 01          lea    0x1(%r12),%r12
  d1:   eb e7                   jmp    ba <run+0x2a>
  d3:   48 89 f8                mov    %rdi,%rax
  d6:   48 8b 5c 24 08          mov    0x8(%rsp),%rbx
  db:   48 8b 6c 24 10          mov    0x10(%rsp),%rbp
  e0:   4c 8b 64 24 18          mov    0x18(%rsp),%r12
  e5:   48 83 c4 28             add    $0x28,%rsp
  e9:   c3                      ret
  ea:   66 0f 1f 44 00 00       nopw   0x0(%rax,%rax,1)

00000000000000f0 <$11>:
  f0:   48 83 ec 08             sub    $0x8,%rsp
  f4:   48 8d 44 24 10          lea    0x10(%rsp),%rax
  f9:   48 89 04 24             mov    %rax,(%rsp)
  fd:   31 c0                   xor    %eax,%eax
  ff:   48 83 c4 08             add    $0x8,%rsp
 103:   c3                      ret
```
