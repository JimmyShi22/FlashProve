-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieClaimLayer.lean: THE
CLAIMS' TIE BEHIND THE LAYER OF EACH LOOKUP (borders 6 and 12 of the key file's first chain), ONE
WAY: the table's claim gives the relation of the links' row: the fourth of the four implications
that a tie by Leads.conseq asks at the fields r1_5 and r1_11. And the rule of consequence in the
form that lets the second implication spend the piece's own yes.

Main names:
  keeps_conseq_yes: Keeps between two rows gives Keeps between two others, under four implications,
    EACH OF WHICH BUT THE FIRST MAY SPEND "the piece says yes from a to b".
  claim_layer₀: On₁ … 6 b, RowsOff and KeysLow of b's record, Cl₁ … 6 b ⊢ (rowT 0 4).rel b.
  claim_layer₁: the like at border 12 and (rowT 1 4).

Object: the links' rows, the table; Iop.Reduction.Leads.conseq (Johnson/Desc/Plain/Leads.lean).
User: FieldsLayer.lean.
Letters and premises: those of claim_back₀ (TieClaimBack.lean).

Limits. One way. Nothing on soundness.

-/
import Johnson.RunOne.Law.TieClaimL1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TieClaimLayer
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading)
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Source KRead Where KItem)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁ On₁ Cl₁)
open Johnson.RunOne.KeyRows1 (open₁ n₁ on₁_two plan₁ meaning₁At)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.SeatsAtFK
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtCut
open Johnson.RunOne.Law.LettersAt
open Johnson.RunOne.Law.OffWalk
open Johnson.RunOne.Law.TieStated
open Johnson.RunOne.Law.TiePromise
open Johnson.RunOne.Law.TieKeys
open Johnson.RunOne.Law.TieClaimFront
open Johnson.RunOne.Law.TieClaimBack
open Johnson.RunOne.Law.TieAgree
open Johnson.RunOne.Law.TieEarly

/-- **The rule of consequence for Keeps, with the piece's yes in hand.** -/
theorem keeps_conseq_yes {A₀ B₀ : Type} {K : Iop.Reduction A₀ B₀} {on on₀ L L₀ : A₀ → Prop}
    {on' on₀' L' L₀' : B₀ → Prop} {ε : Iop.Err K.shape} (h : K.Keeps on on' L L' ε)
    (h1 : ∀ a, on₀ a → on a)
    (h2 : ∀ a τ b, on₀ a → K.out a τ = some b → on' b → L a → L₀ a)
    (h3 : ∀ a τ b, on₀ a → K.out a τ = some b → on' b → on₀' b)
    (h4 : ∀ a τ b, on₀ a → K.out a τ = some b → on' b → L₀' b → L' b) :
    K.Keeps on₀ on₀' L₀ L₀' ε :=
  Iop.Reduction.Leads.conseq h h1 fun a τ b ha hout hq =>
    ⟨h3 a τ b ha hout hq.1, fun hl => h2 a τ b ha hout hq.1 (hq.2 (h4 a τ b ha hout hq.1 hl))⟩

variable {Cells Mm Smp Rec : Type} {X : Source} {N : H2U.PlaceNums}
  {P : VerifiableInference.Desc.Key.LaterPlaces} {D : WholeD} {B : BaseSt Cells Mm Smp Rec}
  {at_ : Where} {R : KRead Cells Mm} {coll : Strs → Rec → Prop}

/-- **THE CLAIMS' TIE BEHIND THE LAYER OF LOOKUP 0, ONE WAY**: border 6. -/
theorem claim_layer₀ (hS : B.SmReads) (hsame : R.same = fun a b => readE a = readE b)
    (hp : (FK X N P).planOk = true) (hn : X.Y.k.oneTime.ranges.lookups.length = 2)
    (b : (Xi × FirstState) × (fr₁ D).E.Str) (hon : On₁ X N P D B at_ R coll 6 b)
    (hoff : RowsOff b.1.2) (hlow : KeysLow b.1.2) (hcl : Cl₁ X N P D B at_ R 6 b) :
    (rowT X N P D B at_ R coll 0 4).rel b := by
  obtain ⟨⟨p₀, s⟩, y⟩ := b
  have h2 := on₁_two _ _ _ _ _ _ _ 6 _ hon
  have hW := fk_admitted X N P hp
  have t0 := tests_at hW (i := 0) (by rw [hn]; omega)
  have t1 := tests_at hW (i := 1) (by rw [hn]; omega)
  obtain ⟨w', hw'⟩ := hcl
  have hall : ∀ i ∈ open₁ (n₁ X.Y.k.oneTime) 6, _ := hw'
  rw [h2] at hall
  have iT := hall .pinT (by decide)
  have i0 := hall (.pin 0) (by decide)
  have i1 := hall (.pin 1) (by decide)
  have s0 := hall (.srow 0) (by decide)
  have s1 := hall (.srow 1) (by decide)
  have r1 := hall (.inRange 1) (by decide)
  have ro := hall (.rows 0) (by decide)
  have kc := hall (.kclaims 0) (by decide)
  obtain ⟨u, hu⟩ := decT_of_pins (X := X) (N := N) (P := P) (D := D) (B := B) (at_ := at_)
    (a := (pullK (stK p₀ 0 s), y)) (w := w')
    ⟨(pinw_atSt p₀ 0 s _ _).2 iT, (pin_atSt hS p₀ 0 s _ _ _ _).2 i0,
      (pin_atSt hS p₀ 0 s _ _ _ _).2 i1⟩
  obtain ⟨q1, q2, q3⟩ := decT_some hu
  have hag : Agree R w' u := agree_of_pins 6 (by omega) (by omega) ((p₀, s), y) hon w' u iT
    ((pinw_atSt p₀ 0 s _ _).1 q1) i0 ((pin_atSt hS p₀ 0 s _ _ _ _).1 q2) i1
    ((pin_atSt hS p₀ 0 s _ _ _ _).1 q3)
  have h3 := size_three 6 (by omega) (by omega) ((p₀, s), y) hon
  obtain ⟨rows, a1, a2⟩ := allSay_of_rows (X := X) hsame 0 p₀ 0 s _ u hoff
    (rows_agree hag 0 (p₀, s) h3 _ ro)
  obtain ⟨keys, k1, k2⟩ := pend_of_kclaims (X := X) hsame 0 p₀ s _ u _ t0.1
    (kclaims_agree hag 0 (p₀, s) h3 hlow _ kc)
  unfold rowT
  refine (upF_rel (Fr := fr₁ D) _ p₀ s y).2 ⟨(u, ()), ⟨hu, fun k hk => absurd hk (Nat.not_lt_zero
      _),
    fun k h1 hk => ?_,
    fun y' => ⟨srow_to_atSt 0 p₀ 0 s _ _ _ (srow_agree _ hag 0 (p₀, s) h3 _ s0),
      srow_to_atSt 1 p₀ 0 s _ _ _ (srow_agree _ hag 1 (p₀, s) h3 _ s1)⟩⟩,
    rows, keys, a1, k1, (allSay_same Reading.gl (stm_same p₀ 0 s) rows _).1 a2, k2⟩
  obtain rfl : k = 1 := by
    rw [hn] at hk
    omega
  obtain ⟨L', e1, e2⟩ := inRange_agree X.Y.k.oneTime hag 1 r1
  obtain rfl : L' = _ := Option.some.inj (e1.symm.trans t1.1)
  rw [hsame] at e2
  exact (inRange_iff _ _ _ _ t1.2.1 t1.2.2).1 e2

/-- **THE CLAIMS' TIE BEHIND THE LAYER OF LOOKUP 1, ONE WAY**: border 12. -/
theorem claim_layer₁ (hS : B.SmReads) (hsame : R.same = fun a b => readE a = readE b)
    (hp : (FK X N P).planOk = true) (hn : X.Y.k.oneTime.ranges.lookups.length = 2)
    (b : (Xi × FirstState) × (fr₁ D).E.Str) (hon : On₁ X N P D B at_ R coll 12 b)
    (hoff : RowsOff b.1.2) (hlow : KeysLow b.1.2) (hcl : Cl₁ X N P D B at_ R 12 b) :
    (rowT X N P D B at_ R coll 1 4).rel b := by
  obtain ⟨⟨p₀, s⟩, y⟩ := b
  have h2 := on₁_two _ _ _ _ _ _ _ 12 _ hon
  have hW := fk_admitted X N P hp
  have t0 := tests_at hW (i := 0) (by rw [hn]; omega)
  have t1 := tests_at hW (i := 1) (by rw [hn]; omega)
  obtain ⟨w', hw'⟩ := hcl
  have hall : ∀ i ∈ open₁ (n₁ X.Y.k.oneTime) 12, _ := hw'
  rw [h2] at hall
  have iT := hall .pinT (by decide)
  have i0 := hall (.pin 0) (by decide)
  have i1 := hall (.pin 1) (by decide)
  have s0 := hall (.srow 0) (by decide)
  have s1 := hall (.srow 1) (by decide)
  have ro := hall (.rows 0) (by decide)
  have kc := hall (.kclaims 0) (by decide)
  have ro1 := hall (.rows 1) (by decide)
  have kc1 := hall (.kclaims 1) (by decide)
  obtain ⟨u, hu⟩ := decT_of_pins (X := X) (N := N) (P := P) (D := D) (B := B) (at_ := at_)
    (a := (pullK (stK p₀ 1 s), y)) (w := w')
    ⟨(pinw_atSt p₀ 1 s _ _).2 iT, (pin_atSt hS p₀ 1 s _ _ _ _).2 i0,
      (pin_atSt hS p₀ 1 s _ _ _ _).2 i1⟩
  obtain ⟨q1, q2, q3⟩ := decT_some hu
  have hag : Agree R w' u := agree_of_pins 12 (by omega) (by omega) ((p₀, s), y) hon w' u iT
    ((pinw_atSt p₀ 1 s _ _).1 q1) i0 ((pin_atSt hS p₀ 1 s _ _ _ _).1 q2) i1
    ((pin_atSt hS p₀ 1 s _ _ _ _).1 q3)
  have h3 := size_three 12 (by omega) (by omega) ((p₀, s), y) hon
  obtain ⟨rows, a1, a2⟩ := allSay_of_rows (X := X) hsame 0 p₀ 1 s _ u hoff
    (rows_agree hag 0 (p₀, s) h3 _ ro)
  obtain ⟨keys, k1, k2⟩ := pend_of_kclaims (X := X) hsame 0 p₀ s _ u _ t0.1
    (kclaims_agree hag 0 (p₀, s) h3 hlow _ kc)
  obtain ⟨rows1, c1, c2⟩ := allSay_of_rows (X := X) hsame 1 p₀ 1 s _ u hoff
    (rows_agree hag 1 (p₀, s) h3 _ ro1)
  obtain ⟨keys1, d1, d2⟩ := pend_of_kclaims (X := X) hsame 1 p₀ s _ u _ t1.1
    (kclaims_agree hag 1 (p₀, s) h3 hlow _ kc1)
  unfold rowT
  refine (upF_rel (Fr := fr₁ D) _ p₀ s y).2 ⟨(u, ()), ⟨hu, fun k hk => ?_,
    fun k h1 hk => absurd hk (by rw [hn]; omega),
    fun y' => ⟨srow_to_atSt 0 p₀ 1 s _ _ _ (srow_agree _ hag 0 (p₀, s) h3 _ s0),
      srow_to_atSt 1 p₀ 1 s _ _ _ (srow_agree _ hag 1 (p₀, s) h3 _ s1)⟩⟩,
    rows1, keys1, c1, d1, (allSay_same Reading.gl (stm_same p₀ 1 s) rows1 _).1 c2, d2⟩
  obtain rfl : k = 0 := by omega
  refine ⟨rows, keys, ?_, ?_, a2, k2⟩
  · show (s.base.rows.take 1)[0]? = some rows
    rw [List.getElem?_take_of_lt (by omega)]
    exact a1
  · show (s.base.keys.take 1)[0]? = some keys
    rw [List.getElem?_take_of_lt (by omega)]
    exact k1

end Johnson.RunOne.Law.TieClaimLayer

#print axioms Johnson.RunOne.Law.TieClaimLayer.keeps_conseq_yes
#print axioms Johnson.RunOne.Law.TieClaimLayer.claim_layer₀
#print axioms Johnson.RunOne.Law.TieClaimLayer.claim_layer₁
