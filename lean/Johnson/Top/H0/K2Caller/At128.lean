-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/At128.lean: the bounds of WrittenLit.lean and Reading.lean at the 5 and the
25 written records of Lit.lean, WITH THE NUMBER 128 WRITTEN OUT.

WrittenMeets.lean, WrittenLit.lean and Reading.lean end in 2⁻¹ ^ r.set.target. Level.lean has, by an
evaluation in Lean's kernel, that the target is 128 at each written record (`small_works`,
`full_works`). Here the two are laid together. Theorems with their proofs.

  target_small, target_full: the target is 128 at each written record
  letters_small, letters_full: the letters have a value at each written record (`Letters.plain`,
      Member.lean: a poor one)
  written_small_128, written_full_128: `Err.Below` of the library's written counts at 2⁻¹ ^ 128
  reading_small_128, reading_full_128: `Err.Below` of `(switchMaps …).err` at 2⁻¹ ^ 128
  K02At128, k02At128: the last two at the 25 records of the full example as one closed proposition;
      its proof
Limits: those of WrittenLit.lean and Reading.lean. A bound on counts, each as a share of its written
round's verifier messages, test bits among them: 20 of the 128 bits at "LOC" are work. That the
written tables are what Table.lean makes of the two examples' public files is a test by evaluation
in TestTableSmall.lean and TestTableFull.lean [not in this library]. It is no soundness of the
protocol. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.WrittenLit
import Johnson.Top.H0.K2Caller.Reading

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Flat OnBytes.Maker Iop
open _root_.Run (PQ.RD ckP)
open _root_.Run.PQ (uL)
open scoped ENNReal

theorem target_small (r : SwRow) (hr : r ∈ tableSmallLit) : r.set.target = 128 :=
  congrArg Prod.fst (of_decide_eq_true (List.all_eq_true.1 small_works r hr))

theorem target_full (r : SwRow) (hr : r ∈ tableFullLit) : r.set.target = 128 :=
  congrArg Prod.fst (of_decide_eq_true (List.all_eq_true.1 full_works r hr))

theorem letters_small (r : SwRow) (hr : r ∈ tableSmallLit) :
    Nonempty (Letters r (r.ok_says (List.all_eq_true.1 tableSmallLit_ok r hr))) :=
  ⟨Letters.plain r _⟩

theorem letters_full (r : SwRow) (hr : r ∈ tableFullLit) :
    Nonempty (Letters r (r.ok_says (List.all_eq_true.1 tableFullLit_ok r hr))) :=
  ⟨Letters.plain r _⟩

/-- **The written counts at the 5 switches of the small example.** -/
theorem written_small_128 (F : Type) (r : SwRow) (hr : r ∈ tableSmallLit)
    (X : Letters r (r.ok_says (List.all_eq_true.1 tableSmallLit_ok r hr))) (ds : List PQ.RD)
    (hd : WrittenAs r.set .request ds r.specs) :
    Err.Below (OnBytes.Flat.Held.cnts (uL (ckP .two) ds) (OnBytes.Flat.Held.wsOf ds (allRead ds))
      (Cb.Pv.SendLocRide.R X.caller).shape (Cb.Pv.SendLocRide.eps X.caller))
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  target_small r hr ▸ written_small_at F r hr X ds hd

/-- **The written counts at the 25 switches of the full example.** -/
theorem written_full_128 (F : Type) (r : SwRow) (hr : r ∈ tableFullLit)
    (X : Letters r (r.ok_says (List.all_eq_true.1 tableFullLit_ok r hr))) (ds : List PQ.RD)
    (hd : WrittenAs r.set .request ds r.specs) :
    Err.Below (OnBytes.Flat.Held.cnts (uL (ckP .two) ds) (OnBytes.Flat.Held.wsOf ds (allRead ds))
      (Cb.Pv.SendLocRide.R X.caller).shape (Cb.Pv.SendLocRide.eps X.caller))
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  target_full r hr ▸ written_full_at F r hr X ds hd

/-- **Along the reading, at the small example.** -/
theorem reading_small_128 (r : SwRow) (hr : r ∈ tableSmallLit)
    (X : Letters r (r.ok_says (List.all_eq_true.1 tableSmallLit_ok r hr))) (d₁ d₂ : RDT)
    (ρ : WordsOf X.caller d₁) (w : K2Wr r d₁ d₂) :
    Err.Below ((switchMaps X d₁ d₂ ρ).err (Cb.Pv.SendLocRide.eps X.caller)) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  target_small r hr ▸ switch_written (List.all_eq_true.1 tableSmallLit_ok r hr)
    (List.all_eq_true.1 small_written_ok r hr) X d₁ d₂ ρ w

/-- **Along the reading, at the full example.** -/
theorem reading_full_128 (r : SwRow) (hr : r ∈ tableFullLit)
    (X : Letters r (r.ok_says (List.all_eq_true.1 tableFullLit_ok r hr))) (d₁ d₂ : RDT)
    (ρ : WordsOf X.caller d₁) (w : K2Wr r d₁ d₂) :
    Err.Below ((switchMaps X d₁ d₂ ρ).err (Cb.Pv.SendLocRide.eps X.caller)) ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  target_full r hr ▸ switch_written (List.all_eq_true.1 tableFullLit_ok r hr)
    (List.all_eq_true.1 full_written_ok r hr) X d₁ d₂ ρ w

/-- **At the full example's 25 records, as one closed proposition.** -/
def K02At128 : Prop :=
  ∀ (r : SwRow) (hr : r ∈ tableFullLit)
    (X : Letters r (r.ok_says (List.all_eq_true.1 tableFullLit_ok r hr))),
    (∀ ds : List PQ.RD, WrittenAs r.set .request ds r.specs →
      Err.Below (OnBytes.Flat.Held.cnts (uL (ckP .two) ds)
        (OnBytes.Flat.Held.wsOf ds (allRead ds)) (Cb.Pv.SendLocRide.R X.caller).shape
        (Cb.Pv.SendLocRide.eps X.caller)) ((2 : ℝ≥0∞)⁻¹ ^ 128)) ∧
    ∀ (d₁ d₂ : RDT) (ρ : WordsOf X.caller d₁), K2Wr r d₁ d₂ →
      Err.Below ((switchMaps X d₁ d₂ ρ).err (Cb.Pv.SendLocRide.eps X.caller))
        ((2 : ℝ≥0∞)⁻¹ ^ 128)

theorem k02At128 : K02At128 := fun r hr X =>
  ⟨fun ds hd => written_full_128 Unit r hr X ds hd,
    fun d₁ d₂ ρ w => reading_full_128 r hr X d₁ d₂ ρ w⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.target_full
#print axioms VerifiableInference.Desc.First.K2Caller.letters_full
#print axioms VerifiableInference.Desc.First.K2Caller.written_full_128
#print axioms VerifiableInference.Desc.First.K2Caller.reading_full_128
#print axioms VerifiableInference.Desc.First.K2Caller.k02At128
