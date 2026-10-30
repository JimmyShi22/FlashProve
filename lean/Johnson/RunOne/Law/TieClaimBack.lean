-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieClaimBack.lean: THE
CLAIMS' TIE AT BORDER 4 OF THE KEY FILE'S FIRST CHAIN (in front of the kind's own block of the first
lookup), THE OTHER WAY, AND SO BOTH WAYS: under the table's promise with its history the table's
claim gives the relation of the links' row at the filling from the table's letters: the witness map:
the table's witness is pinned, so the decoder gives a witness; the two agree (TieAgree.lean); the
riding items pass from the one to the other.

Main names:
  srow_to_atSt: the sample rows' item at the record gives it at the riding part's record.
  decT_of_pins: where a witness is pinned the decoder gives one.
  claim_back₀: On₁' … 4 a, Cl₁ … 4 a ⊢ (rowT 0 2).rel a.
  tie_claim₀: TieClaim … 0 2: ONE TIE OF CLAIMS AT ONE BORDER, WHOLE.

Object: the links' rows and the table of the first chain (TieStated.lean).
User: none yet.
Letters and premises: those of claim_front₀ (TieClaimFront.lean).

Limits. One border, at which neither forms nor worth nor rows nor kclaims is open. IT CLOSES NO
FIELD THAT IS OWED: border 4 lies in front of the kind's block: of r1_4 it gives the second
implication (had already); the other way belongs to the seat before, which the frame fills itself.
Its worth is the method. Nothing on soundness.

-/
import Johnson.RunOne.Law.TieAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TieClaimBack
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (Xi FirstState Source KRead Where KItem rowHolds_congr)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁ Cl₁)
open Johnson.RunOne.KeyRows1 (open₁ n₁ on₁_two plan₁ meaning₁At)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.SeatsAtFK
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LinkAtCut
open Johnson.RunOne.Law.LettersAt
open Johnson.RunOne.Law.TieStated
open Johnson.RunOne.Law.TiePromise
open Johnson.RunOne.Law.TieKeys
open Johnson.RunOne.Law.TieClaimFront
open Johnson.RunOne.Law.TieAgree
open LPFD (On₁')

variable {Cells Mm Smp Rec : Type} {X : Source} {N : H2U.PlaceNums}
  {P : VerifiableInference.Desc.Key.LaterPlaces} {D : WholeD} {B : BaseSt Cells Mm Smp Rec}
  {at_ : Where} {R : KRead Cells Mm} {coll : Strs → Rec → Prop}

/-- The sample rows' item at the record gives it at the riding part's record. -/
theorem srow_to_atSt (k : ℕ) (p₀ : Xi) (i : ℕ) (s : FirstState) (y y' : Strs)
    (w : Wit Cells Unit Mm) (h : (meaning₁At X.Y.k.oneTime R).srow k (p₀, s) y w) :
    (meaning₁At X.Y.k.oneTime R).srow k (atSt (pullK (stK p₀ i s))) y' w := by
  obtain ⟨o, x, h1, h2, h3, h4, h5⟩ := h
  have h2' : s.d.st.oracles[o]? = some x := h2
  refine ⟨o, bareO x, h1, ?_, h3, h4, fun r hr =>
    (rowHolds_congr R.same (sameTables_stm p₀ i s) _ r).2 (h5 r hr)⟩
  show (s.d.st.oracles.map bareO)[o]? = some (bareO x)
  rw [Array.getElem?_map, h2']
  rfl

/-- Where a witness is pinned the decoder gives one. -/
theorem decT_of_pins {a : (Xi × Statement) × (fr₁ D).E.Str} {w : Wit Cells Unit Mm}
    (h : PinsT X N P B at_ a.1 (strsOf (fr₁ D) a.2) w) : ∃ u, decT X N P D B at_ a = some u := by
  unfold decT
  rw [dif_pos ⟨w, h⟩]
  exact ⟨_, rfl⟩

/-- **THE CLAIMS' TIE IN FRONT OF THE KIND'S BLOCK OF LOOKUP 0, THE OTHER WAY.** -/
theorem claim_back₀ (hS : B.SmReads) (hsame : R.same = fun a b => readE a = readE b)
    (hp : (FK X N P).planOk = true) (hn : X.Y.k.oneTime.ranges.lookups.length = 2)
    (a : (Xi × FirstState) × (fr₁ D).E.Str) (hon : On₁' X N P D B at_ R coll 4 a)
    (hcl : Cl₁ X N P D B at_ R 4 a) : (rowT X N P D B at_ R coll 0 2).rel a := by
  obtain ⟨⟨p₀, s⟩, y⟩ := a
  have h2 := on₁_two _ _ _ _ _ _ _ 4 _ hon.1
  have hW := fk_admitted X N P hp
  have t0 := tests_at hW (i := 0) (by rw [hn]; omega)
  have t1 := tests_at hW (i := 1) (by rw [hn]; omega)
  obtain ⟨w', hw'⟩ := hcl
  have hall : ∀ i ∈ open₁ (n₁ X.Y.k.oneTime) 4, _ := hw'
  rw [h2] at hall
  have iT := hall .pinT (by decide)
  have i0 := hall (.pin 0) (by decide)
  have i1 := hall (.pin 1) (by decide)
  have r0 := hall (.inRange 0) (by decide)
  have r1 := hall (.inRange 1) (by decide)
  have s0 := hall (.srow 0) (by decide)
  have s1 := hall (.srow 1) (by decide)
  obtain ⟨u, hu⟩ := decT_of_pins (X := X) (N := N) (P := P) (D := D) (B := B) (at_ := at_)
    (a := (pullK (stK p₀ 0 s), y)) (w := w')
    ⟨(pinw_atSt p₀ 0 s _ _).2 iT, (pin_atSt hS p₀ 0 s _ _ _ _).2 i0,
      (pin_atSt hS p₀ 0 s _ _ _ _).2 i1⟩
  obtain ⟨q1, q2, q3⟩ := decT_some hu
  have hag : Agree R w' u := agree_of_pins 4 (by omega) (by omega) ((p₀, s), y) hon.1 w' u iT
    ((pinw_atSt p₀ 0 s _ _).1 q1) i0 ((pin_atSt hS p₀ 0 s _ _ _ _).1 q2) i1
    ((pin_atSt hS p₀ 0 s _ _ _ _).1 q3)
  have h3 := size_three 4 (by omega) (by omega) ((p₀, s), y) hon.1
  have key : ∀ l L, X.Y.k.oneTime.ranges.lookups[l]? = some L → Wf.lookupOk Wf.fBits L = true →
      Wf.fitsMatrix (Wf.matrixOf X.Y.k.oneTime.lin) L = true →
      (meaning₁At X.Y.k.oneTime R).inRange l w' →
      KeysIn X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin) L
        (cutM (Wf.matrixOf X.Y.k.oneTime.lin) (mxT X R u)) := by
    intro l L hl a1 a2 hx
    obtain ⟨L', e1, e2⟩ := inRange_agree X.Y.k.oneTime hag l hx
    obtain rfl : L' = L := Option.some.inj (e1.symm.trans hl)
    rw [hsame] at e2
    exact (inRange_iff _ _ _ _ a1 a2).1 e2
  unfold rowT
  refine (upF_rel (Fr := fr₁ D) _ p₀ s y).2 ⟨(u, ()), ⟨hu, fun k hk => absurd hk (Nat.not_lt_zero
      _),
    fun k h1 hk => ?_, fun y' => ⟨srow_to_atSt 0 p₀ 0 s _ _ _ (srow_agree _ hag 0 (p₀, s) h3 _ s0),
      srow_to_atSt 1 p₀ 0 s _ _ _ (srow_agree _ hag 1 (p₀, s) h3 _ s1)⟩⟩, ?_⟩
  · obtain rfl : k = 1 := by
      rw [hn] at hk
      omega
    exact key 1 _ t1.1 t1.2.1 t1.2.2 r1
  · refine (in_iff _ _ _ _ _ _ _).2 ?_
    rw [matOf_cut]
    exact key 0 _ t0.1 t0.2.1 t0.2.2 r0

/-- **ONE TIE OF CLAIMS AT ONE BORDER, WHOLE.** -/
theorem tie_claim₀ (hS : B.SmReads) (hsame : R.same = fun a b => readE a = readE b)
    (hp : (FK X N P).planOk = true) (hn : X.Y.k.oneTime.ranges.lookups.length = 2) :
    TieClaim X N P D B at_ R coll 0 2 :=
  fun b hb => ⟨claim_back₀ hS hsame hp hn b hb, claim_front₀ hS hsame hp hn b hb⟩

end Johnson.RunOne.Law.TieClaimBack

#print axioms Johnson.RunOne.Law.TieClaimBack.claim_back₀
#print axioms Johnson.RunOne.Law.TieClaimBack.tie_claim₀
