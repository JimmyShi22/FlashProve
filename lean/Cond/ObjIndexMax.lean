-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cond/ObjIndexMax.lean: the largest error of a list, with and without proof of work, and the bound
of Cond/ObjIndex.lean as such a number.

Definitions, statements and proofs.

Limits: this file says nothing on numerals.

Terms: lean/GLOSSARY.md.
-/
import Cond.ObjIndex
import CompileK.WideIndex
import Ior.KnowCollRulesChainErr

set_option autoImplicit false

noncomputable section

namespace Iop
open scoped ENNReal

/-- The largest error of a list, as a probability. -/
def Err.maxPr : {s : Shape} → Err s → ℝ≥0∞
  | [], _ => 0
  | r :: _, (e, ε) => Max.max ((e : ℝ≥0∞) / (Fintype.card r.Chal : ℝ≥0∞)) (Err.maxPr ε)

/-- The same, counting the proof-of-work bits of each round. -/
def Err.maxPrG : {s : Shape} → GBits s → Err s → ℝ≥0∞
  | [], _, _ => 0
  | r :: _, (b, g), (e, ε) =>
    Max.max ((e : ℝ≥0∞) / ((2 : ℝ≥0∞) ^ b * (Fintype.card r.Chal : ℝ≥0∞))) (Err.maxPrG g ε)

/-- The maximum of the quotients of two plain lists, pair by pair. -/
def maxQuot : List ℕ → List ℕ → ℝ≥0∞
  | e :: es, n :: ns => Max.max ((e : ℝ≥0∞) / (n : ℝ≥0∞)) (maxQuot es ns)
  | _, _ => 0

theorem Err.below_iff_maxPr_le : ∀ {s : Shape} (ε : Err s) (c : ℝ≥0∞), Err.Below ε c ↔ ε.maxPr ≤ c
  | [], _, _ => ⟨fun _ => _root_.zero_le _, fun _ => trivial⟩
  | r :: _, (e, ε), c => by
    have h0 : (Fintype.card r.Chal : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have ht : (Fintype.card r.Chal : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    show ((e : ℝ≥0∞) ≤ c * (Fintype.card r.Chal : ℝ≥0∞) ∧ Err.Below ε c) ↔
      Max.max ((e : ℝ≥0∞) / (Fintype.card r.Chal : ℝ≥0∞)) ε.maxPr ≤ c
    rw [_root_.max_le_iff, Err.below_iff_maxPr_le ε c, ENNReal.div_le_iff h0 ht]

theorem Err.belowG_iff_maxPrG_le :
    ∀ {s : Shape} (g : GBits s) (ε : Err s) (c : ℝ≥0∞), Err.BelowG g ε c ↔ ε.maxPrG g ≤ c
  | [], _, _, _ => ⟨fun _ => _root_.zero_le _, fun _ => trivial⟩
  | r :: _, (b, g), (e, ε), c => by
    have h0 : (2 : ℝ≥0∞) ^ b * (Fintype.card r.Chal : ℝ≥0∞) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ two_ne_zero) (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
    have ht : (2 : ℝ≥0∞) ^ b * (Fintype.card r.Chal : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top) (ENNReal.natCast_ne_top _)
    show ((e : ℝ≥0∞) ≤ c * ((2 : ℝ≥0∞) ^ b * (Fintype.card r.Chal : ℝ≥0∞)) ∧ Err.BelowG g ε c) ↔
      Max.max ((e : ℝ≥0∞) / ((2 : ℝ≥0∞) ^ b * (Fintype.card r.Chal : ℝ≥0∞))) (ε.maxPrG g) ≤ c
    rw [_root_.max_le_iff, Err.belowG_iff_maxPrG_le g ε c, ENNReal.div_le_iff h0 ht]

theorem Err.maxPr_lists : ∀ {s : Shape} (ε : Err s), ε.maxPr = maxQuot ε.toList s.chalList
  | [], _ => rfl
  | r :: _, (e, ε) => by
    show Max.max ((e : ℝ≥0∞) / (Fintype.card r.Chal : ℝ≥0∞)) ε.maxPr =
      Max.max ((e : ℝ≥0∞) / ((Fintype.card r.Chal : ℕ) : ℝ≥0∞)) (maxQuot ε.toList _)
    rw [Err.maxPr_lists ε]

end Iop

namespace Hiop.SubsR
open Iop
open scoped ENNReal
variable {C : ConfigurationWithOutOfDomainSample} {S : SubsR C}

/-- The largest round error of the offline phase: weights-formedness, the test at one instance, the
link. -/
def Nums.idxMax {Nn : Type} (P : S.Nums) : Option (S.Wk Nn) → ℝ≥0∞
  | none => max P.wf.err.maxPr (max P.linOff.err.maxPr P.link.err.maxPr)
  | some w =>
    max (P.wf.err.maxPrG w.g.wf) (max (P.linOff.err.maxPrG w.g.linOff) (P.link.err.maxPrG w.g.link))

theorem Nums.idxBelowO_iff {Nn : Type} (P : S.Nums) (c₀ : ℝ≥0∞) :
    ∀ o : Option (S.Wk Nn), P.IdxBelowO c₀ o ↔ P.idxMax o ≤ c₀
  | none => by
    show P.IdxBelow c₀ ↔ max P.wf.err.maxPr (max P.linOff.err.maxPr P.link.err.maxPr) ≤ c₀
    rw [max_le_iff, max_le_iff, ← Err.below_iff_maxPr_le,
      ← Err.below_iff_maxPr_le, ← Err.below_iff_maxPr_le]
    exact ⟨fun h => ⟨h.wf, h.linOff, h.link⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩
  | some w => by
    show P.IdxBelowG w.g c₀ ↔
      max (P.wf.err.maxPrG w.g.wf)
          (max (P.linOff.err.maxPrG w.g.linOff) (P.link.err.maxPrG w.g.link)) ≤ c₀
    rw [max_le_iff, max_le_iff, ← Err.belowG_iff_maxPrG_le,
      ← Err.belowG_iff_maxPrG_le, ← Err.belowG_iff_maxPrG_le]
    exact ⟨fun h => ⟨h.wf, h.linOff, h.link⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

end Hiop.SubsR

namespace TopC
open Iop Rom ZKCP Compile Compile.Batch Top.Batch Top.ProgDraw Hiop
open scoped ENNReal

namespace Spec

/-- States that every round's error, as a probability, is at most c exactly if the largest is;
`err_belowG_maxPrG`: the same counting proof-of-work bits. -/
def err_below_maxPr : Prop := ∀ (s : Shape) (ε : Err s) (c : ℝ≥0∞), Err.Below ε c ↔ ε.maxPr ≤ c
def err_belowG_maxPrG : Prop :=
  ∀ (s : Shape) (g : GBits s) (ε : Err s) (c : ℝ≥0∞), Err.BelowG g ε c ↔ ε.maxPrG g ≤ c
/-- `maxPr` in plain lists. -/
def err_maxPr_lists : Prop := ∀ (s : Shape) (ε : Err s), ε.maxPr = maxQuot ε.toList s.chalList
/-- States that the condition `P.IdxBelowO` of Cond/ObjIndex.lean says: c₀ is at least the
largest round error of the three lists. -/
def target_idxMax : Prop :=
  ∀ (Nn : Type) (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (c₀ : ℝ≥0∞) (o : Option (S.Wk Nn)),
    P.IdxBelowO c₀ o ↔ P.idxMax o ≤ c₀

end Spec

theorem err_below_maxPr : Spec.err_below_maxPr := fun _ ε c => Err.below_iff_maxPr_le ε c
theorem err_belowG_maxPrG : Spec.err_belowG_maxPrG := fun _ g ε c => Err.belowG_iff_maxPrG_le g ε c
theorem err_maxPr_lists : Spec.err_maxPr_lists := fun _ ε => Err.maxPr_lists ε
theorem target_idxMax : Spec.target_idxMax := fun _ _ _ P c₀ o => P.idxBelowO_iff c₀ o

end TopC
