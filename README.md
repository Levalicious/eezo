# eezo

The Eezo evaluator: runs the bytecode [eezoc](https://github.com/Levalicious/eezoc) emits (`eezo -f xbcl`), with the
STG-style machine, garbage collector, the Lazy-K stream I/O (`-i`, stdlib `stream.eezo`) and the monadic I/O (`-m`,
stdlib `io.eezo`: the program is `run(m)`, the driver performs its actions putc, getc, exit). Links [libeezo](https://github.com/Levalicious/libeezo) from
`../libeezo`, so it sits beside it in a workspace (the [umbrella](https://github.com/Levalicious/umbrella) repository
lays one out).

Build: `mk` (see [mk](https://github.com/Levalicious/mk), [mkroot](https://github.com/Levalicious/mkroot)).
Dependencies and their pinned commits: `deps.lock`; `ci/deps.sh` fetches them beside this checkout. Its behaviour is
exercised by eezoc's suites (modes, stream, io, gc_regress, xbcl), which need both binaries.
