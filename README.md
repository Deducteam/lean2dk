# lean2dk

lean4dk is a tool for translating Lean to Dedukti. The implementation is still a work-in-progress.

## Building

See [here](https://lean-lang.org/lean4/doc/quickstart.html) for how to install Lean and `elan`. With `elan` installed, compile lean2dk by running:
```
lake build
```

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
