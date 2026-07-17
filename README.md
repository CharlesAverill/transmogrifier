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
L = \\{\\, w \in \\{0,1\\}^* \mid \forall i \in [1,|w|-1],\\; w_i \neq w_{i+1} \\,\\}.
$$

This language can be recognized by the following 4-state DFA:

![alternating DFA](vendor/alternating_1.png)

[`alternating.ml`](examples/alternating.ml) initializes a teacher for this language, initiates the learning loop, and generates a C program containing a reference to the initial state, the transition function, and the accept function at [`alternating.c`](examples/alternating.c):

```c
unsigned int delta(unsigned int, unsigned int);
unsigned int accept(unsigned int);
unsigned int delta(unsigned int $4, unsigned int $5)
{
  if ($4 == 3U) {
    if ($5 == 1U) {
      return 0U;
    } else {
      if ($5 == 0U) {
        return 2U;
      } else {
        return 4U;
      }
    }
  } else {
    if ($4 == 2U) {
      if ($5 == 1U) {
        return 0U;
      } else {
        if ($5 == 0U) {
          return 1U;
        } else {
          return 4U;
        }
      }
    } else {
      if ($4 == 1U) {
        if ($5 == 1U) {
          return 1U;
        } else {
          if ($5 == 0U) {
            return 1U;
          } else {
            return 4U;
          }
        }
      } else {
        if ($4 == 0U) {
          if ($5 == 1U) {
            return 1U;
          } else {
            if ($5 == 0U) {
              return 2U;
            } else {
              return 4U;
            }
          }
        } else {
          return 4U;
        }
      }
    }
  }
}

unsigned int accept(unsigned int $4)
{
  if ($4 == 3U) {
    return 1U;
  } else {
    if ($4 == 2U) {
      return 1U;
    } else {
      if ($4 == 0U) {
        return 1U;
      } else {
        return 0U;
      }
    }
  }
}

unsigned int const q0 = 3;
```

Compiling with CompCert, we get the following machine code:

```
$ ccomp -c examples/alternating.c
$ objdump -d alternating.o 

alternating.o:     file format elf64-x86-64


Disassembly of section .text:

0000000000000000 <delta>:
   0:   48 83 ec 08             sub    $0x8,%rsp
   4:   48 8d 44 24 10          lea    0x10(%rsp),%rax
   9:   48 89 04 24             mov    %rax,(%rsp)
   d:   83 ff 03                cmp    $0x3,%edi
  10:   74 70                   je     82 <delta+0x82>
  12:   83 ff 02                cmp    $0x2,%edi
  15:   74 4f                   je     66 <delta+0x66>
  17:   83 ff 01                cmp    $0x1,%edi
  1a:   74 2b                   je     47 <delta+0x47>
  1c:   83 ff 00                cmp    $0x0,%edi
  1f:   74 07                   je     28 <delta+0x28>
  21:   b8 04 00 00 00          mov    $0x4,%eax
  26:   eb 74                   jmp    9c <delta+0x9c>
  28:   83 fe 01                cmp    $0x1,%esi
  2b:   74 13                   je     40 <delta+0x40>
  2d:   83 fe 00                cmp    $0x0,%esi
  30:   74 07                   je     39 <delta+0x39>
  32:   b8 04 00 00 00          mov    $0x4,%eax
  37:   eb 63                   jmp    9c <delta+0x9c>
  39:   b8 02 00 00 00          mov    $0x2,%eax
  3e:   eb 5c                   jmp    9c <delta+0x9c>
  40:   b8 01 00 00 00          mov    $0x1,%eax
  45:   eb 55                   jmp    9c <delta+0x9c>
  47:   83 fe 01                cmp    $0x1,%esi
  4a:   74 13                   je     5f <delta+0x5f>
  4c:   83 fe 00                cmp    $0x0,%esi
  4f:   74 07                   je     58 <delta+0x58>
  51:   b8 04 00 00 00          mov    $0x4,%eax
  56:   eb 44                   jmp    9c <delta+0x9c>
  58:   b8 01 00 00 00          mov    $0x1,%eax
  5d:   eb 3d                   jmp    9c <delta+0x9c>
  5f:   b8 01 00 00 00          mov    $0x1,%eax
  64:   eb 36                   jmp    9c <delta+0x9c>
  66:   83 fe 01                cmp    $0x1,%esi
  69:   74 13                   je     7e <delta+0x7e>
  6b:   83 fe 00                cmp    $0x0,%esi
  6e:   74 07                   je     77 <delta+0x77>
  70:   b8 04 00 00 00          mov    $0x4,%eax
  75:   eb 25                   jmp    9c <delta+0x9c>
  77:   b8 01 00 00 00          mov    $0x1,%eax
  7c:   eb 1e                   jmp    9c <delta+0x9c>
  7e:   31 c0                   xor    %eax,%eax
  80:   eb 1a                   jmp    9c <delta+0x9c>
  82:   83 fe 01                cmp    $0x1,%esi
  85:   74 13                   je     9a <delta+0x9a>
  87:   83 fe 00                cmp    $0x0,%esi
  8a:   74 07                   je     93 <delta+0x93>
  8c:   b8 04 00 00 00          mov    $0x4,%eax
  91:   eb 09                   jmp    9c <delta+0x9c>
  93:   b8 02 00 00 00          mov    $0x2,%eax
  98:   eb 02                   jmp    9c <delta+0x9c>
  9a:   31 c0                   xor    %eax,%eax
  9c:   48 83 c4 08             add    $0x8,%rsp
  a0:   c3                      ret
  a1:   66 66 2e 0f 1f 84 00    data16 cs nopw 0x0(%rax,%rax,1)
  a8:   00 00 00 00 
  ac:   0f 1f 40 00             nopl   0x0(%rax)

00000000000000b0 <accept>:
  b0:   48 83 ec 08             sub    $0x8,%rsp
  b4:   48 8d 44 24 10          lea    0x10(%rsp),%rax
  b9:   48 89 04 24             mov    %rax,(%rsp)
  bd:   83 ff 03                cmp    $0x3,%edi
  c0:   74 1c                   je     de <accept+0x2e>
  c2:   83 ff 02                cmp    $0x2,%edi
  c5:   74 10                   je     d7 <accept+0x27>
  c7:   83 ff 00                cmp    $0x0,%edi
  ca:   74 04                   je     d0 <accept+0x20>
  cc:   31 c0                   xor    %eax,%eax
  ce:   eb 13                   jmp    e3 <accept+0x33>
  d0:   b8 01 00 00 00          mov    $0x1,%eax
  d5:   eb 0c                   jmp    e3 <accept+0x33>
  d7:   b8 01 00 00 00          mov    $0x1,%eax
  dc:   eb 05                   jmp    e3 <accept+0x33>
  de:   b8 01 00 00 00          mov    $0x1,%eax
  e3:   48 83 c4 08             add    $0x8,%rsp
  e7:   c3                      ret
```
