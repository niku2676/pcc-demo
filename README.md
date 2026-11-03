# pcc-demo

Demo repository for [Proof-Carrying Code](https://github.com/hosbe1/Proof-Carrying-Code-Meta-AI-Hackathon-2026).
Every pull request runs the `pcc-check` action: changed Python functions are translated to Dafny, specified,
tested and proven. A real bug turns the check red with a counterexample; correct code turns it green with a
certificate in `proofs/` that anyone can re-check with `dafny verify proofs/dfyconfig.toml`.

The code in `strings/` is copied from [TheAlgorithms/Python](https://github.com/TheAlgorithms/Python) under
its MIT license (see `LICENSE.md`). The demo replays a real historical bug:
[TheAlgorithms/Python#12941](https://github.com/TheAlgorithms/Python/issues/12941), fixed in
[#12946](https://github.com/TheAlgorithms/Python/pull/12946).
