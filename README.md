# lean2dk

lean4dk is a tool for translating Lean to Dedukti. The implementation is still a work-in-progress.

## Building

See [here](https://lean-lang.org/lean4/doc/quickstart.html) for how to install Lean and `elan`. With `elan` installed, compile lean2dk by running:
```
lake build
```

### macOS note

On recent macOS (Darwin 25.x+), dyld requires the `__DATA_CONST` segment of an
executable to carry the `SG_READ_ONLY` flag; the Lean v4.18 toolchain's linker
does not set it, so the freshly-linked `lean2dk` binary aborts at launch with
`__DATA_CONST segment missing SG_READ_ONLY flag`. `scripts/patch_macho.py`
patches the flag (and ad-hoc re-signs) post-link. The `lake run` scripts below
(`trans`, `trans_only`, `patch`) invoke it automatically on macOS. If you run
the binary directly (`lake exe lean2dk ...`), first run `lake run patch` once
after each relink so the flag is set.

## Running

After `lake build`, the lean2dk executable can be found in `.lake/build/bin/lean4less`.

The command line arguments are:

> `lean2dk [--search-path path] [--no-elim] [--all] [--only const] [--print] [--write] [MOD]`

* `MOD`: a required lean module name to load the environment for translation, like `Init.Classical`.
* `search-path` (`-s`): Set Lean search path directory (for finding `MOD`).
* `no-elim` (`-ne`): Do not eliminate definitional equalities via Lean4Less translation (e.g. when using -s with a pre-translated library).
* `all` (`-a`): Also translate all constants from the dependencies of the specified module (not just the ones appearing in the module itself).
* `only` (`-o`): Only translate the specified constants and their dependencies.
* `print` (`-p`): Print translation of specified constants to standard output (relevant only with '-o ...').
* `write` (`-w`): Also write translation of specified constants (with dependencies) to file (relevant only with '-p').

If `--only` is not specified, the translated environment, consisting of the translations of all of the constants in `MOD` + all of their (transitive) dependencies, is output in the folder `dk/out/` as a set of `.dk` files, one for each of the original input Lean modules.

You can run the executable using `lake exe`. For instance, to translate the module `Init.Data.Nat.Lemmas` to Dedukti, run:
```
 $ lake exe lean2dk Init.Data.Nat.Lemmas
```
To translate only the definition `Classical.em`, and all of its dependencies, run:
```
 $ lake exe lean2dk Init.Classical --only Classical.em
```

To translate a different Lean package, navigate the directory of the target project, then use `lake env path/to/lean2dk/.lake/build/bin/lean2dk <args>` to run `lean2dk` in the context of the target project, for example:
```
 $ (cd ~/projects/mathlib4/ && lake env ~/projects/lean2dk/.lake/build/bin/lean2dk Mathlib.Data.Real.Basic --only Real)
```

## Checking the translated output (requires a patched Dedukti)

The translated `.dk` files in `dk/out/` are type-checked with Dedukti. lean2dk's
output of Lean **well-founded definitions** (e.g. `Nat.modCore`) is, however, only
checkable by a Dedukti kernel with **lazy-delta congruence**, enabled by the
`DK_LAZY_DELTA` environment variable.

Why: such definitions translate (via the `WellFounded.fix`/`Acc.rec` encoding)
to terms whose accessibility proofs have no strong normal form for symbolic
arguments — Lean's kernel only stays out of that loop because it is lazy and
compares a shared head's *arguments* before unfolding it. Stock Dedukti
`whnf`-unfolds the recursor first and is dragged into the non-terminating
reduction. `DK_LAZY_DELTA` gives Dedukti the same arg-wise-congruence escape
hatch. (Background: the non-termination is documented, with a kernel-side
reproducer, on the `acc-wf-nontermination-demo` branch of
[Lean4Lean](https://github.com/rish987/Lean4Lean).)

### Building the patched Dedukti

The patch lives on the `lazy-delta-congruence` branch of the
[rish987/Dedukti](https://github.com/rish987/Dedukti/tree/lazy-delta-congruence)
fork (forked from upstream `v2.7`). Build it with the OCaml/opam toolchain:
```
 $ git clone -b lazy-delta-congruence git@github.com:rish987/Dedukti.git ~/projects/Dedukti
 $ (cd ~/projects/Dedukti && dune build commands/main.exe)
```
This produces the kernel binary at
`~/projects/Dedukti/_build/default/commands/main.exe` (a `dk`-compatible
multicall: `… check`, `… dep`, etc.). Alternatively, install it as your `dk`
with `opam pin add dedukti ~/projects/Dedukti`.

### Running the check

`dk/Makefile` is pre-wired for this: it `export`s `DK_LAZY_DELTA := 1` and uses a
`DK` variable that defaults to the fork build above (override with
`make DK=dk …` if you installed the patched kernel on `PATH`). So:
```
 $ lake run check                      # type-check everything currently in dk/out/
 $ lake run trans Init.Data.Nat.Lemmas # translate a module AND check it
 $ make check -C dk                    # (equivalent to `lake run check`)
```
With a stock (unpatched) Dedukti, checking modules that contain well-founded
definitions will not terminate.
