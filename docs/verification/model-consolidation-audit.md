# Model vocabulary preservation audit

The six vocabulary modules were consolidated into `Model/ProblemSetting.lean`.
A Lean environment comparison checked all 78 declarations, including generated
fields and instances. All 78 types and 74 of 75 bodies agree after erasing bound
variable names. One body, `BitMatching.intersection`, selects a different
Decidable instance after the broader imports. A complete Lean theorem proves
the captured old function and the current function extensionally equal.
Raw byte identity is not claimed.

The [audit bundle](model-consolidation-audit.tar.gz) contains the exact historical
captures, original and portable probes, source snapshots, checksums and logs.
It is 288,678bytes. Its SHA256 is:

```
fd674370efdeba8930857ae8f9494ec3fc6d942c767abc0b5bf1d500b05fbea2
```

Extract it, build this checkout using its pinned toolchain, and run:

```sh
python3 /path/to/model-consolidation-audit/run.py --repo /path/to/checkout
```

The portable runner was tested successfully: both strict Lean commands exited 0,
the current capture matched the saved after-capture exactly, all 78 type and 74
body equalities passed the kernel, and the remaining extensional equality used
only `propext`, `Classical.choice` and `Quot.sound`. The runner writes to a fresh
external directory and checks the bundle and checkout pins before replaying.
See its README for the optional output directory and failure behavior.

The historical before-capture is preserved input; its six source modules no
longer exist in the consolidated checkout. The portable replay checks those
saved raw expressions against the current environment. This mathematical
preservation audit does not approve native Tex2Lean bindings or certify the
completion of any remaining manuscript target.
