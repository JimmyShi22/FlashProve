-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CutFit.lean: the splitting step (Rom/SpecCut.lean) at schemes with proof-of-work bits:
a Fiat-Shamir answer is split after block 0; at a query of committer or prover whose component has
such bits, the rest is queried only if the check passes on block 0 or the attempt is the last (words
of this library: lean/GLOSSARY.md).

  `cutFS`  For K = K' + 2 a Fiat-Shamir answer (K hash blocks and a chaining value) is split into
           block 0 and the rest (the blocks 1, .., K'; the chaining value; the last block). (`cutFb`
           goes by cases on K, so that no cast along K = K' + 2 occurs.) With fewer than two blocks
           it is not split, and no other oracle is (nor the ghost names `fbw t j`: no scheme queries
           them after `realQ`, Compile/Batch/Oracles.lean).
  `needT W`  The rule, read off the plain part of the query (`tryInfoT`,
             Compile/Batch/SpecOneCall.lean): the check on block 0, or the last attempt; at a query
             without proof-of-work bits: always.
  `needOKCut_of`  If `Test0` holds (the proof-of-work check depends on block 0 alone) and committer
                  and prover of a scheme go on in the same way after two answers that are both
                  failed attempts before the last (`Spec.facF`, at the relation `agF`), then the
                  scheme meets the step's condition `NeedOKCut`: committer and prover under the
                  rule, the verifier under "always". No table of blocks enters. (Tables of blocks:
                  Compile/Batch/NeedTable.lean. `Test0`, `agF`, `Spec.facF`:
                  Compile/Batch/SpecOneCall.lean.)
  `needOKCut_PL`  Under `Test0`, `W.OKG`, σ.o = other, the scheme with the lazy prover
                  (`Seed.argPL`) and pruned Merkle paths meets `NeedOKCut` (`facF_PL`,
                  Compile/Batch/DeadL.lean).
  `cutPL`  At that scheme, under the same hypotheses and `WholeOnly` (the extractor reads only
           oracles that are not split; `wholeOnly_cutFS`), `IsZKCPArgWith` (ZKCP/Gen.lean),
           extractor and simulator named, carries over to the split scheme with the same three
           bounds.

Limits: with fewer than two blocks nothing is split, and the statements say nothing new. The step's
own limits hold of `cutPL` too: the head of Rom/SpecCut.lean. Nothing on the state-expansion step
(Compile/Batch/CutLinks.lean). Nothing on the one hash function. No count.
-/
import Rom.CutTop
import Rom.CutKit
import Compile.Batch.DeadL
import Compile.Batch.OneCall

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- K + 2 hash blocks and a chaining value: block 0; the blocks 1, .., K, the chaining value, the
last block -/
def eCut (lam K : ℕ) :
    ((Fin (K + 2) → Dig lam) × Dig lam) ≃ Dig lam × ((Fin K → Dg lam) × Dg lam × Dg lam) where
  toFun r := (r.1 0, (fun j => r.1 j.castSucc.succ, r.2, r.1 (Fin.last (K + 1))))
  invFun s :=
    (Fin.cons (α := fun _ => Dig lam) s.1 (Fin.snoc (α := fun _ => Dig lam) s.2.1 s.2.2.2), s.2.2.1)
  left_inv r := by
    ext1
    · funext j
      refine Fin.cases ?_ (fun i => ?_) j
      · rfl
      · refine Fin.lastCases ?_ (fun i' => ?_) i <;> simp
    · rfl
  right_inv s := by
    obtain ⟨a, b, t, h⟩ := s
    simp

/-- how a Fiat-Shamir answer is treated -/
def cutFb (lam : ℕ) : (K : ℕ) → OCut ((Fin K → Dig lam) × Dig lam)
  | 0 => .whole
  | 1 => .whole
  | K + 2 =>
    .cut (Dig lam) ((Fin K → Dg lam) × Dg lam × Dg lam) inferInstance inferInstance inferInstance
      (eCut lam K) (fun _ => dig0 lam, dig0 lam, dig0 lam)

/-- Which oracles are split. -/
def cutFS (lam K : ℕ) (L : BatchProtocol I X) : ∀ o, OCut ((spec lam K L).Rng o)
  | .fb _ => cutFb lam K
  | .leaf => .whole
  | .node => .whole
  | .rleaf => .whole
  | .rnode => .whole
  | .fbw _ _ => .whole
  | .g _ => .whole
  | .ann => .whole
  | .other => .whole

/-- block 0, read off the first part -/
def frontBl (lam : ℕ) : (K : ℕ) → (cutFb lam K).Front → Dig lam
  | 0, _ => dig0 lam
  | 1, a => a.1 0
  | _ + 2, a => a

theorem frontBl_front :
    ∀ (K : ℕ) (h0 : 0 < K) (r : (Fin K → Dig lam) × Dig lam),
      frontBl lam K ((cutFb lam K).front r) = r.1 ⟨0, h0⟩
  | 1, _, _ => rfl
  | _ + 2, _, _ => rfl

/-- The rule. -/
def needT (W : QueryLayout lam L) : NeedCut (cutFS lam W.K L)
  | .fb t, q, a =>
      match tryInfoT W t (q : FbIn lam L t).plain with
      | some x => x.1 (fun _ => frontBl lam W.K a) || x.2
      | none => true
  | .leaf, _, _ => true
  | .node, _, _ => true
  | .rleaf, _, _ => true
  | .rnode, _, _ => true
  | .fbw _ _, _, _ => true
  | .g _, _, _ => true
  | .ann, _, _ => true
  | .other, _, _ => true

theorem isWhole_cutFS {K : ℕ} {o : OracleName} (ho : ∀ t, o ≠ .fb t) :
    (cutFS lam K L o).isWhole = true := by
  cases o with
  | fb t => exact absurd rfl (ho t)
  | _ => rfl

/-- Under `Test0`: an answer as the rule shows it (`shownCut`) is the answer itself, or related to
it by `agF`. -/
theorem shownT_or (W : QueryLayout lam L) (hT : Test0 W) (o : OracleName)
    (q : domOf lam L o) (r : rngOf lam W.K o) :
    shownCut (cutFS lam W.K L) (needT W) o q r = r ∨
    agF W o q r (shownCut (cutFS lam W.K L) (needT W) o q r) := by
  by_cases hw : (cutFS lam W.K L o).isWhole = true
  · exact .inl (by rw [shownCut_of_skip _ (by rw [hw]; rfl), OCut.alone_whole _ hw])
  · have ho : ∃ t, o = .fb t := by
      by_contra hn
      exact hw (isWhole_cutFS fun t e => hn ⟨t, e⟩)
    obtain ⟨t, rfl⟩ := ho
    by_cases hc : ((cutFS lam W.K L (.fb t)).isWhole ||
        !needT W (.fb t) q ((cutFS lam W.K L (.fb t)).front r)) = true
    · refine .inr ?_
      rw [shownCut_of_skip _ hc]
      have hn : needT W (.fb t) q ((cutFS lam W.K L (.fb t)).front r) = false := by
        rw [Bool.eq_false_of_not_eq_true hw] at hc
        simpa using hc
      have hn' : (match tryInfoT W t (q : FbIn lam L t).plain with
          | some x => x.1 (fun _ => frontBl lam W.K ((cutFb lam W.K).front r)) || x.2
          | none => true) = false := hn
      cases hx : tryInfoT W t (q : FbIn lam L t).plain with
      | none =>
        rw [hx] at hn'
        exact nomatch hn'
      | some x =>
        rw [hx] at hn'
        obtain ⟨h0, hdep⟩ := hT t _ x hx
        rw [frontBl_front W.K h0] at hn'
        obtain ⟨h2, h3⟩ := Bool.or_eq_false_iff.1 hn'
        have f : ∀ r' : rngOf lam W.K (.fb t),
            r'.1 ⟨0, h0⟩ = r.1 ⟨0, h0⟩ → failsAt W t q r'.1 = true := fun r' e => by
          unfold failsAt
          rw [hx]
          show (!x.1 r'.1 && !x.2) = true
          rw [hdep r'.1 (fun _ => r.1 ⟨0, h0⟩) fun _ => e, h2, h3]
          rfl
        refine ⟨f r rfl, f _ ?_⟩
        rw [← frontBl_front W.K h0, ← frontBl_front W.K h0 r]
        exact congrArg (frontBl lam W.K) ((cutFb lam W.K).front_alone _)
    · exact .inl (shownCut_of_ask _ hc)

variable {IVK ISK Pf : Type}

/-- Under `Test0`: the splitting step's condition, from "C and P read their answers up to agF"
(`Spec.facF`). -/
theorem needOKCut_of (W : QueryLayout lam L) (hT : Test0 W)
    (A : Gen.Arg (spec lam W.K L) I X Unit IVK ISK Pf) (hF : Spec.facF W A) :
    NeedOKCut (cutFS lam W.K L) A (needT W) (needT W) fun _ _ _ => true where
  com := fun i => readsCut_of _ (shownT_or W hT) _ (hF.1 i)
  prv := fun k b => readsCut_of _ (shownT_or W hT) _ (hF.2 k b)
  ver := fun _ _ _ => cutAll _ _ _ _

theorem needOKCut_PL (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (bk : CoinPlan)
    (σ : SeedOracle (spec lam W.K L)) (ℓ : ℕ) (hT : Test0 W) (hW : W.OKG) (hσ : σ.o = OracleName.other) :
    NeedOKCut (cutFS lam W.K L) (prunedK W p (Seed.argPL W WP p bk σ ℓ Seed.noK)) (needT W)
      (needT W) fun _ _ _ => true :=
  needOKCut_of W hT _ (Dead.facF_PL I X lam L W WP p bk σ ℓ hW hσ)

/-- under `Need.Std` (Compile/Batch/NeedTable.lean): a Fiat-Shamir oracle whose answer is one block
has K = 0, and is not split -/
theorem isWhole_of_blocks_one
    {K : ℕ} {m : OracleCoding (spec lam K L) lam} (hm : Need.Std m) (o : OracleName) (h1 : m.blocks o = 1) :
    (cutFS lam K L o).isWhole = true := by
  by_cases ho : ∃ t, o = .fb t
  · obtain ⟨t, rfl⟩ := ho
    have hK : K = 0 := by
      have : K + 1 = 1 := (hm.blocks (.fb t)).symm.trans h1
      omega
    subst hK
    rfl
  · exact isWhole_cutFS fun t e => ho ⟨t, e⟩

/-- under `Need.Std`: an extractor that reads one-block oracles only reads only oracles that are not
split -/
theorem wholeOnly_cutFS {K : ℕ} {m : OracleCoding (spec lam K L) lam} (hm : Need.Std m) {Wt IVK' Pf' : Type}
    (E : Gen.Extractor (spec lam K L) I X Wt IVK' Pf') (hE : LocalTo E m) :
    WholeOnly (cutFS lam K L) E :=
  wholeOnly_of_localTo _ m (isWhole_of_blocks_one hm) E hE

/-- The splitting step at the scheme with the lazy prover and pruned Merkle paths, under the
hypotheses below. -/
theorem cutPL (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (bk : CoinPlan)
    (σ : SeedOracle (spec lam W.K L)) (ℓ : ℕ) (hT : Test0 W) (hW : W.OKG) (hσ : σ.o = OracleName.other)
    {PP : Type} (R : Gen.RelPair I X Unit PP) (B : ℕ)
    (E : Gen.Extractor (spec lam W.K L) I X Unit (IVKKO lam L) (PrfKO lam L))
    (Sim : Gen.Simulator (spec lam W.K L) PP (IVKKO lam L) X (PrfKO lam L)) (α : ℝ≥0∞)
    (ε ζ : ℕ → ℕ → ℝ≥0∞) (hE : WholeOnly (cutFS lam W.K L) E)
    (h : Gen.IsZKCPArgWith R (prunedK W p (Seed.argPL W WP p bk σ ℓ Seed.noK)) B E Sim α ε ζ) :
    Gen.IsZKCPArgWith R
      (cutArg (cutFS lam W.K L) (needT W) (needT W) (fun _ _ _ => true)
        (prunedK W p (Seed.argPL W WP p bk σ ℓ Seed.noK)))
      B (extCut _ E) (simCut _ Sim) α ε ζ :=
  cutExit _ _ _ _ _ _ _ _ _ R _ B E Sim α ε ζ _ _ _ (needOKCut_PL W WP p bk σ ℓ hT hW hσ) hE h

end Compile.Batch
