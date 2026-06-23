# Haskell extraction regression (Coq ≥ 8.20 / Rocq 9.x)

This note documents why this branch (`rocq-migration`) exists and what it
works around. **For building/extraction, use Coq 8.18.0** with the library
versions in the README — that reproduces the committed `extracted-examples/`
exactly. This branch ports the development to Rocq 9.1.1 and works around an
extraction-plugin regression described below.

## Symptom

`Extraction` of several definitions aborts with an **anomaly** on
Coq 8.20.1 and Rocq 9.1.1, but succeeds on Coq 8.18.0:

```
Anomaly "File "plugins/extraction/mlutil.ml", line 660, characters 22-28: Assertion failed."
Please report at http://rocq-prover.org/bugs/.
```

`mlutil.ml:660` is the `None -> assert false` branch of `gen_subst` (inside
`kill_some_lams`): the extractor removes a head lambda it classified as a
logical/dummy argument, while a `Rel` elsewhere in the body still refers to
it, leaving a dangling de Bruijn index.

## Affected / unaffected (measured)

| Toolchain | libraries | result |
|-----------|-----------|--------|
| Coq 8.18.0 | mathcomp-ssreflect 1.19.0, Coquelicot 3.4.2, interval 4.11.0 | extraction OK (11/11), output identical to committed |
| Coq 8.20.1 | mathcomp 2.5.0, Coquelicot 3.4.4, interval 4.11.4 | anomaly |
| Rocq 9.1.1 | mathcomp 2.5.0, Coquelicot 3.4.4, interval 4.11.4 | anomaly |

So the regression was introduced **between Coq 8.18 and 8.20** and is still
present in Rocq 9.1. (The newer rows also bump mathcomp 1.x→2.x; the
assertion itself is in the extraction plugin, not in mathcomp.)

In `formalization/Extract.v` the first failing target is
`Extraction "Magnitude" Magnitude.magnitude`; `Sqrt` and `CSqrt` fail the
same way. `IVT`, `Max`, and the right-angled Sierpinski examples extract.

## Trigger

The crash fires when an **erased `Prop` is still referenced by a live
(computational) sub-term**. Here that arises in three shapes, all from
ordinary ssreflect proofs of extraction-targeted `Definition`s:

1. A fused monadic composition `M_lift (fun w => … destruct w …) src`
   whose branch function rebuilds a Σ-type using the destructed proof
   component (`magnitude1/2`, `magnitude`).
2. A `have h : <Prop>. …` (`let`-bound proof) feeding a witness, e.g.
   `have yneq0 … ; exists (… x / yneq0 …)` (`sqrt_approx`, `csqrt_neq0`).
3. A recursion `elim n => [|n' [y [ygt0 IH]]]` destructing the inductive
   hypothesis (a Σ-type) inline and using its proof part in the next
   witness (`sqrt_approx`).

It is **not** caused by ssreflect or the relator: ssreflect `have`/`case`
desugar to the same terms as vanilla `assert`/`destruct`, and the fixed
helpers below still use ssreflect and extract cleanly. `Set Extraction
Conservative Types` suppresses the anomaly but stops erasing the
monad/dictionary arguments too, so the extracted `m_lift`/`m_unit` get
spurious `()` parameters and the Haskell no longer type-checks — not a
usable workaround.

## Source-level workaround (this branch)

Rewrite each extraction-targeted definition so that **no erased `Prop` is
referenced by a live term**:

- split fused `M_lift`/recursion/decision compositions into **separate
  top-level constants** composed by reference
  (`magnitude1 = magnitude1_pack (magnitude1_search …)`,
  `sqrt_approx = sig_repack … (sqrt_approx_full …)` with `_base`/`_step`,
  `complex_nonzero_cases` via `cnz1/2/3`);
- discharge proof obligations in **separate opaque (`Qed`) lemmas** (they
  extract to dummies and are never fused);
- pass division-nonzero proofs as **inline opaque-lemma applications**, not
  `have`-`let`s (`gt0_neq0`);
- use `proj1`/`proj2` instead of destructuring `Prop` conjunctions inline.

This is purely structural — proofs and extracted entry points are unchanged
in meaning, and the regenerated Haskell was verified numerically
(`sqrt 2 = 1.41421356…`, `real_max 3 5 = 5`). It clears every target except
`csqrt_neq0`, whose proof entangles division-nonzero proofs with witnesses
too tightly for the same move; its `Extraction "CSqrt"` is therefore
disabled in `Extract.v` (the committed `CSqrt.hs` from 8.18 still compiles).

## Status on this branch (Rocq 9.1.1)

- Whole library builds (`rocq makefile` / updated `Makefile`); 40 files.
- 10/11 examples extract cleanly and compile against AERN2 (`stack build`),
  including the equilateral Sierpinski triangles (`STEn`/`STE4n`).
- `CSqrt` extraction disabled (see above).
