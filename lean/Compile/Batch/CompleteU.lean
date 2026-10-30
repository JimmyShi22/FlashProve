-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteU.lean: tools for completeness of the compiled scheme with free empty slots
(no query for an empty slot: `argBU`, Compile/Batch/StarU.lean): `runEager_completenessExp`,
`verifyAll_true`, `pr_law_eq`.

Notation: `W`: a `QueryLayout lam L` (Iop/BatchWire.lean): a wire record (lean/GLOSSARY.md: wire); `WP`: a
`WireBP L` (Iop/BatchWireP.lean): the prover's data for the three protocols, and the enumeration of
the encoding randomness; `p`: a `Params` (Compile/Star.lean), with the fields sMT, sFS, M, s1; the
number of copies is `p.M` + 1; `f`: a `Fam` (Rom/OSpec.lean): a whole family of functions; `b`: a
`List (X × Unit)`: a batch, as P of a `Gen.Arg` (ZKCP/Gen.lean) takes it: a list of pairs, here with
`Unit` in the second place; pT, pL, pO: fields of an `LH.Nums` (Iop/InteractiveOracleProof.lean: all numbers of the
interface), in ℝ≥0∞; N: `L.maxBatchSize`; `L.maxBatchSize`: a natural number: the number of slots (`BatchProtocol`, Iop/Batch.lean).

Limits: this file does not prove completeness of the scheme (the bound `alphaB`, pT + pL + N pO:
Compile/Batch/Spec.lean; with proof-of-work bits `alphaBG`: Compile/Batch/SpecGrind.lean). Nothing
on batches that are chosen after the key or the oracles (adaptive and refined completeness).
-/
import Compile.Batch.CompleteUAcc
import Compile.Batch.CompleteUUnif
import Compile.Batch.CompleteURef
import Compile.Batch.CompleteURefNoGhost

noncomputable section

namespace Compile.Batch
open Iop Rom Prob MeasureTheory RefU
open scoped ENNReal

namespace CompleteBU

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (f : Fam (spec lam W.K L)) (i : I) (b : List (X × Unit))

private theorem bindE {S : OSpec} {α β : Type} (x : OComp S α) (g : α → OComp S β) :
    (x >>= g) = x.bind g := rfl
private theorem pureE {S : OSpec} {α : Type} (a : α) : (pure a : OComp S α) = OComp.pure a := rfl

/-- the completeness experiment, for fixed oracle functions, in terms of the honest run -/
theorem runEager_completenessExp :
    (ZKCP.Gen.completenessExp (argBU W WP p) i b).runEager f =
      ((runAllBU W WP p i b).runEager f).bind fun z =>
        (ZKCP.Gen.verifyAll (argBU W WP p) z.1 ((b.map Prod.fst).zip z.2)).runEager f := by
  simp only [ZKCP.Gen.completenessExp, ZKCP.Gen.sessionExp, runAllBU, argBU, bindE,
    OComp.runEager_bind, OComp.runEager, PMF.pure_bind, PMF.bind_bind]

/-- V accepts all if it accepts each. -/
theorem verifyAll_true (ivk : IVK lam L) :
    ∀ l : List (X × Prf lam L), (∀ xp ∈ l, (V W p ivk xp.1 xp.2).runEager f = PMF.pure true) →
      (ZKCP.Gen.verifyAll (argBU W WP p) ivk l).runEager f = PMF.pure true
  | [], _ => rfl
  | (x, π) :: rest, h => by
      have h1 : (V W p ivk x π).runEager f = PMF.pure true := h (x, π) List.mem_cons_self
      have h2 := verifyAll_true ivk rest fun xp hxp => h xp (List.mem_cons_of_mem _ hxp)
      simp only [ZKCP.Gen.verifyAll, bindE, pureE, OComp.runEager_bind, OComp.runEager]
      rw [show ((argBU W WP p).V ivk x π).runEager f = PMF.pure true from h1,
        PMF.pure_bind, h2, PMF.pure_bind]
      rfl

variable {Ryes Rno : I → X → Prop} {M : LH.Nums}

/-- An event of the honest run that has, for every fixed family, the distribution of a small
experiment c, has under lazy oracles the probability that c outputs true. -/
theorem pr_law_eq {c : TypedOracleComputation lam W.K L Bool} (φ : IVK lam L × List (Prf lam L) → Bool)
    (h : ∀ f, ((runAllBU W WP p i b).runEager f).map φ = c.runEager f) :
    pr (runAllBU W WP p i b).law {z | φ z = true} = pr c.law {x | x = true} := by
  have h1 := Rom.map_runLazy_congr
    (c₁ := runAllBU W WP p i b) (c₂ := c) φ id (fun f => by rw [h f, PMF.map_id]) (Table.empty _)
  have h2 : (runAllBU W WP p i b).law.map φ = c.law := by
    unfold OComp.law
    rw [PMF.map_comp]
    exact h1
  rw [← h2, pr_map]
  rfl

end CompleteBU



end Compile.Batch
