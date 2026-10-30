-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/SigPins.lean: THEOREMS, KIND-FREE: OwedPinsStay (OwedSig.lean) IS PROVED: two
records at which the members at a seat have one sample, and two strings with one column at the
seat's tree, have one "shown", one "no collision" and one "pin" at that seat.
  word_col      the committed word of a tenant of tree j reads of the strings the column of tree j
                alone (wordOf, Johnson/Desc/Msg.lean).
  member_stays  at ONE member that sits at (j, t): ShownAt, CfAt and PinAt
                (Johnson/Desc/Sound/MsgSig.lean) are the same at (a, y) and at (a', y').
  pinsStay      the statement: member by member.
What is not claimed. Nothing of any block's step: who gives the two premises is the caller's matter.
Nothing on soundness.

-/
import Johnson.Desc.K13.Law.OwedSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.Sound (MsgT Sending Mem SitsAt pinJT noCollJT shownJT PinAt CfAt
  ShownAt)

/-- A tenant's committed word reads the column of its own tree alone. -/
theorem word_col {Xi : Type} (G : FileDescription Xi) (y y' : Strs) (j t : ℕ)
    (h : ∀ z, y'.col j z = y.col j z) : wordOf G y' j t = wordOf G y j t := by
  funext z
  unfold wordOf
  rw [h z]

/-- **At one member that sits at (j, t).** -/
theorem member_stays {A Xi Cells Tok : Type} (cs : Codes) (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (j t : ℕ) (a a' : A) (y y' : Strs) (hcol : ∀ z, y'.col j z = y.col j z) (x : Mem)
    (hs : SitsAt x j t) (hsm : smp a' x.1 x.2 = smp a x.1 x.2) :
    (ShownAt G cs x.1.l x.1.seat y x.2 ↔ ShownAt G cs x.1.l x.1.seat y' x.2) ∧
      (CfAt G cs x.1.l x.1.seat (fun z => smp z x.1) x.2 a y ↔
        CfAt G cs x.1.l x.1.seat (fun z => smp z x.1) x.2 a' y') ∧
      ∀ w : Desc.Wit Cells Tok MsgT,
        PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a y w ↔
          PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a' y' w := by
  have hj : (x.1.seat x.2).1 = j := congrArg Prod.fst hs
  have e0 : wordOf G y' (x.1.seat x.2).1 (x.1.seat x.2).2 =
      wordOf G y (x.1.seat x.2).1 (x.1.seat x.2).2 :=
    word_col G y y' _ _ (by rw [hj]; exact hcol)
  have eW : Sound.wordsOf G cs x.1.l x.1.seat y' x.2 = Sound.wordsOf G cs x.1.l x.1.seat y x.2 := by
    unfold Sound.wordsOf Sound.wordAt
    rw [e0]
  have eS : ShownAt G cs x.1.l x.1.seat y' x.2 ↔ ShownAt G cs x.1.l x.1.seat y x.2 := by
    unfold ShownAt
    rw [e0]
  refine ⟨eS.symm, ?_, fun w => ?_⟩
  · unfold CfAt
    simp only [eW, eS, hsm]
  · unfold PinAt
    simp only [eW, eS, hsm]

/-- **One "shown", one "no collision", one "pin".** -/
theorem pinsStay : OwedPinsStay := by
  intro A Xi Cells Tok cs G arr smp ms j t a a' y y' hcol hsm
  have M := fun (x : Mem) (hx : x ∈ ms) (hs : SitsAt x j t) =>
    member_stays (Cells := Cells) (Tok := Tok) cs G arr smp j t a a' y y' hcol x hs (hsm x hx hs)
  refine ⟨?_, ?_, fun w => ?_⟩
  · unfold shownJT
    exact and_congr_right fun _ =>
      forall_congr' fun x => forall_congr' fun hx => forall_congr' fun hs => (M x hx hs).1
  · unfold noCollJT
    exact forall_congr' fun x => forall_congr' fun hx => forall_congr' fun hs => (M x hx hs).2.1
  · unfold pinJT
    exact and_congr_right fun _ =>
      forall_congr' fun x => forall_congr' fun hx => forall_congr' fun hs => (M x hx hs).2.2 w

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.member_stays
#print axioms VerifiableInference.Desc.K13.Law.pinsStay
