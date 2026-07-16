(lang dune 3.21)
(using rocq 0.11)

(name transmogrifier)

(generate_opam_files true)

(source
 (github CharlesAverill/transmogrifier))

(authors
 "Charles Averill <charlesaverill20@gmail.com>")

(maintainers
 "Charles Averill <charlesaverill20@gmail.com>")

(license MIT)

(documentation https://github.com/CharlesAverill/transmogrifier)

(package
 (name transmogrifier)
 (synopsis "Verified finite state automata compiler")
 (description "A formally-verified extension to CompCert for compiling finite state automata")
 (depends
  (dune (>= 3.21.0))
  (rocq-prover (>= 9.1.0))
   coq-compcert))
