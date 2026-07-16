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
L = \\{\\, w \in \\{0,1\\}^* \mid \forall i \in \\{1,\dots,|w|-1\\},\; w_i \neq w_{i+1} \\,\\}.
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
