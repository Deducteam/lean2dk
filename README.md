# lean2dk

lean2dk is a tool for translating Lean to Dedukti. The implementation is still a work-in-progress.

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

After `lake build`, the lean2dk executable can be found in `.lake/build/bin/lean2dk`.

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

The translated `.dk` files in `dk/out/` are type-checked with Dedukti. Stock
Dedukti **cannot** check the output of realistic Lean modules: the encoding of
Lean's well-founded recursion, structure eta, and universe levels drives the
kernel's `whnf`/conversion into non-terminating or exponential behaviour that
Lean's own kernel only escapes via laziness, proof irrelevance, and structural
sharing. lean2dk therefore targets the [rish987/Dedukti](https://github.com/rish987/Dedukti)
fork, which adds the matching escape hatches.

### Why the fork is necessary

Three independent kernel changes, each addressing a different way the translated
terms break a stock kernel:

1. **Lazy-delta congruence** (`DK_LAZY_DELTA=1`). Well-founded definitions (e.g.
   `Nat.modCore`) translate via the `WellFounded.fix`/`Acc.rec` encoding to terms
   whose accessibility proofs have no strong normal form for symbolic arguments.
   Lean's kernel stays out of that loop because it compares a shared head's
   *arguments* before unfolding it; stock Dedukti `whnf`-unfolds the recursor
   first and diverges. Lazy-delta congruence gives Dedukti the same arg-wise
   escape. (Reproducer: the `acc-wf-nontermination-demo` branch of
   [Lean4Lean](https://github.com/rish987/Lean4Lean).)

2. **Convertibility memoization + reduction sharing** (on by default; disable with
   `DK_NO_MEMO=1`). The projection-based recursor for eta-structures
   (`Prod.rec C f x ≡ f x.1 x.2`) is non-linear in its `normalize.maxS` universe-
   level arguments — required for the rewrite rule to be subject-reduction-correct —
   so every match fires a universe-level convertibility check, and the recursor
   *duplicates* its major premise. On the nested `PProd`/`Nat.below` structures
   produced by `brecOn`, both effects blow up (millions of identical level checks;
   exponential re-reduction of the shared subterm). The fork (a) memoizes positive
   level convertibility and (b) memoizes the whnf of closed redexes so a duplicated
   subterm is reduced once. Both caches are signature-scoped (a hook invalidates
   them whenever the signature changes), so they stay sound.

3. **Diagnostics / safety budgets** (off by default): `DK_PROGRESS=1` prints a
   per-declaration type-checking heartbeat; `DK_TOS_BUDGET=<nodes>` and
   `DK_MEM_BUDGET=<bytes>` abort a declaration (naming it) instead of OOMing when
   its translated normal form is finite but exponentially large.

### Building the patched Dedukti

Build the `progress-trace` branch of the fork (forked from upstream `v2.7`; it
layers the diagnostics and the memoization/sharing on top of lazy-delta
congruence — i.e. everything above):
```
 $ git clone -b progress-trace git@github.com:rish987/Dedukti.git ~/projects/Dedukti
 $ (cd ~/projects/Dedukti && dune build commands/main.exe)
```
This produces the kernel binary at
`~/projects/Dedukti/_build/default/commands/main.exe` (a `dk`-compatible
multicall: `… check`, `… dep`, etc.). Alternatively `opam pin add dedukti ~/projects/Dedukti`.

### Running the check

`dk/Makefile` is pre-wired: it `export`s `DK_LAZY_DELTA := 1` and uses a `DK`
variable defaulting to the fork build above (override with `make DK=dk …` if you
installed the patched kernel on `PATH`). Memoization/sharing are on by default.
```
 $ lake run check                      # type-check everything currently in dk/out/
 $ lake run trans Init.Data.Nat.Lemmas # translate a module AND check it
 $ make check -C dk                    # (equivalent to `lake run check`)
```
With a stock (unpatched) Dedukti, or with `DK_NO_MEMO=1`, checking realistic
modules will not terminate (or will exhaust memory).

## Stubbing infeasible constants

Some Lean constants cannot be checked by *any* term-based kernel after translation,
because the cost is inherent to the encoding rather than the kernel. lean2dk
**value-stubs** these: it emits the constant with its real type but drops the
rewrite rule / body, turning it into a postulate. Stubs are reported to
`dk/out/STUBBED.txt`, and the full list of currently-stubbed constants is small
(a couple dozen for `Init.Data.Nat.Lemmas`). Three classes are detected:

1. **Bignum primitive `Nat` ops.** Lean computes `Nat` arithmetic/comparison with
   GMP; the encoding uses a unary `Nat.succ` representation, so an op on a large
   literal (e.g. `Nat.Linear.fixedVar = 10^8`) is infeasible. A static scan flags
   any constant applying a `Nat` op — `add`/`mul`/`pow`/… and, crucially,
   `Nat.decEq`/`BEq.beq`/`instDecidableEqNat`, which `Lean4Less.reduceNat` does not
   intercept — to an operand exceeding `Lean4Less.natPrimOpStubThreshold`.

2. **Exponential decision-procedure proofs.** The `omega`/linear-arith machinery
   (`Nat.Linear.{Expr,ExprCnstr}.{toPoly,toNormPoly,denote_*,of_cancel_*,…}`)
   translates, via the structure-eta recursor over `brecOn`, to normal forms that
   are **finite but exponentially large** — so even with the memoization/sharing
   above, materializing and comparing them is infeasible (the only complete fix
   would be global hash-consing in the kernel, as Lean's kernel does). These are
   listed in `dk/force_stub.txt` (one Lean name per line); a stubbed function's
   auto-generated equation/unfolding lemmas (`.eq_*`, `._sunfold`) are stubbed with
   it automatically, since their `rfl` proofs need the function to reduce.

3. **`String` literals.** lean2dk does not yet translate `String` literals (it
   emits a `STRLIT.FIXME` placeholder), so a constant containing one is ill-typed.
   A static scan value-stubs them; in practice these are incidental error/panic
   helpers (`mkPanicMessageWithDecl`, `List.get!Internal`).

**Caveat.** A stubbed constant is *trusted, not checked*: Dedukti does not
independently verify it. All stubbed constants here are theorems/definitions that
are verified by Lean's own kernel, and lemmas that *use* them still typecheck
against the postulated signatures — so the result is a Dedukti check of everything
*except* the genuinely-infeasible encoding artifacts, with those taken on faith
from Lean. Classes (1) and (3) are limitations that better encodings (binary
`Nat`, real `String` literals) would remove; class (2) is the fundamental one.
