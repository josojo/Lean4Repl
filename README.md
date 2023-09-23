# Repl env for interactive theorem testing

This repo contains the Lean4Repl.lean file that helps executing lean commands against a state.

The builds for Lean4Repl can be built by running:

```cmd
lake build Lean4Repl
```

## Setup

The to be tested theorem can be put into a environment to load the dependent packages by providing a [MWE](https://leanprover-community.github.io/mwe.html) in the MAIN.lean file. This enables loading the correct name spaces and providing definitions that can be used during the interactions.

An example MWE for the theorem minFacHelper_0 is provided in the Main.lean file.

To have all dependencies already build before interacting - this will save time - one can build the whole dependency of mathlib by running

```cmd
lake build BuildAllDependencies
```

This creates the binaries which can then be found in the build directory and will be used to speed up all future imports


## Running Repl

Simply modify the Main.lean with your setup + theorem and remove the proof by replacing it with run:

```cmd
=: by lean_dojo_repl sorry
```

and then run

```sh
lake env lean Main.lean
```

and it will return:

```sh
REPL> {"tacticState": "n : ℕ\nh1 : ble 2 n = true\nh2 : 1 = n % 2\n⊢ MinFacHelper n 3", "sid": 0, "error": null}
```

Now, you can provide commands like this:

```sh
{"sid": 0, "cmd": [" refine \u27e8by norm_num, by norm_num, ?_\u27e9 ","  refine (le_minFac'.mpr \u03bb p hp hpn \u21a6 ?_).resolve_left (Nat.ne_of_gt (Nat.le_of_ble_eq_true h1))"," rcases hp.eq_or_lt with rfl|h"," \u00b7 simp [(Nat.dvd_iff_mod_eq_zero ..).1 hpn] at h2 "," \u00b7 exact h"]}
```
