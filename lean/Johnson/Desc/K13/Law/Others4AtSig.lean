-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Others4AtSig.lean: THE PROOF OF THE STATEMENT THAT
Johnson/Desc/K13/Law/OwedOthers4.lean WRITES AS OWED: all seven clauses of `Others4`
(Johnson/Desc/K13/Law/FillFromSentences.lean: what stays at W's commitment), at the reader through
the record's own book (`rwBook`) and at six letters of the form `SigLetters`
(Johnson/Desc/K13/Law/Others3AtSig.lean). Statements with their proofs. The pattern, clause by
clause: `others3_at_sig` there.
Main names:
  `held4`: over a step of W's commitment a sample that is held in front is held behind: WITH NO
    PREMISE ON THE BOOK's SIZE (`K1.smpHeldStays` at `smpStay4` and the book's own
    equation).
  `olderStay4`: over such a step ALL THAT IS OLDER STAYS (`OlderStay`,
    Johnson/Desc/K13/Law/SmpEarlierMessages.lean): the code table; of every message in front its shape, mark,
    sample rows and pad (the sending leaves it whole; the block behind it leaves these four); every
    place and every tree of the book in front (`atM4_seated`).
  `others4_at_sig`: **the owed statement.** reader: `reader4`, its four premises out of
    "K13.pileMasks" in Q, `K1.indexThereB`, the second conjunct of `First.bookAt`, and
    `place_in_book` from "K12.seatsCarried" in Q and hbelow · held: `held4` · shown, noColl,
    pinIBack: `pinsStay`, with the premise `SmpOld` fed by the step's first part, the clause's own
    `First.bookAt` and "held", and `olderStay4` · decodes, pinWBack: `decodes_M4`, `pinWBack_M4`.
What is not claimed. The statement's own premises (what Mg says at the two items; hbelow;
`SmpOld`; `DecBlind`; `SigLetters`). Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.OwedOthers4
import Johnson.Desc.K13.Law.Reader4
import Johnson.Desc.K13.Law.SigHeld
import Johnson.Desc.K13.Law.SigPins
import Johnson.Desc.K12.Door.DoorGives

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (MsgT Sending Mem SitsAt)
open VerifiableInference.Desc.K12.Door (seatsCarriedB placesBelowB place_in_book)

section
variable {Pp Cl : Type} {P : Where} {P' : K1.Par} {x x' : Pp × S}

/-- **A sample that is held in front of W's commitment is held behind it.** -/
theorem held4 (h : StepM4 Cl P P' x x') (j t : ℕ) (hh : smpHeld x.2.st x.2.book j t = true) :
    smpHeld x'.2.st x'.2.book j t = true := by
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  exact (K1.smpHeldStays x.2.st x'.2.st x.2.book x'.2.book _ j t (smpStay4 h)
    (atM4_booked hd).place hh).2.2.2

/-- **Over a step of W's commitment all that is older stays.** -/
theorem olderStay4 (h : StepM4 Cl P P' x x') : OlderStay x.2 x'.2 := by
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  obtain ⟨s₁, g₁, rs₂, g₂, h1, h2⟩ := atM4_mid hd
  have hk := K1.sendAtS_kept P' x.2 s₁ _ g₁ h1
  have hs := rowsB_same h2
  have hseat := (atM4_seated hd).seated
  refine ⟨hs.1.trans hk.1, fun o ho => ?_, hseat.places, hseat.trees⟩
  rw [hs.2 o]
  unfold sampleOf
  rw [hk.2.2 o ho]

end

/-- **The owed statement.** -/
theorem others4_at_sig : OwedOthers4 := by
  intro Pp Cl Xi Cells Tok nR P P' arr mat N Mg Q p cs G smp ms decT L hG hpIn hsIn hPM hSe hT
    hbelow hsmp hdec
  refine
    { reader := fun x x' w h hQ _ hit hbk h0 => ?_
      held := fun x x' h h0 => ?_
      shown := fun y y' ho h0 => ?_
      noColl := fun x x' y y' h hh hbk ho h0 => ?_
      decodes := fun x x' y y' h hc h0 => ?_
      pinWBack := fun x x' y y' w h hc h0 => ?_
      pinIBack := fun x x' y y' w h hh hbk ho h0 => ?_ }
  · have hOn : pileMasksC x.2 = true := by
      rw [← hPM x]
      exact hQ _ hpIn
    have hseats : seatsCarriedB L x.2.book = true := by
      rw [← hSe x]
      exact hQ _ hsIn
    have hlt : x.2.out.indexMasks < x.2.st.oracles.size := by
      have e : (x.2.st.oracles[x.2.out.indexMasks]?).isSome = true := hT x hit
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 e
      exact (Array.getElem?_eq_some_iff.1 ha).1
    have hsz : x.2.book.place.size = x.2.st.oracles.size := by
      unfold First.bookAt at hbk
      simp only [Bool.and_eq_true, beq_iff_eq] at hbk
      exact hbk.1.2
    have htree : ∀ q, x.2.book.place[x.2.out.indexMasks]? = some q →
        q.1 < x.2.book.trees.size := by
      intro q hq
      obtain ⟨q', hq', hl⟩ := place_in_book hseats hsz (hbelow x p hbk hseats) _ hlt
      obtain rfl : q = q' := Option.some.inj (hq.symm.trans hq')
      exact hl
    exact reader4 arr mat P P' x x' w h hOn hlt hsz htree h0
  · rw [hG.held] at h0 ⊢
    exact held4 h _ _ h0
  · exact (hG.shown y').2 (((pinsStay (A := Unit) (Cells := Cells) (Tok := Tok) cs G arr
      (fun _ _ _ => none) ms N.index.1 N.index.2 () () y y' ho.2 fun _ _ _ => rfl).1).1
      ((hG.shown y).1 h0))
  · rw [hG.held] at hh
    exact (hG.noColl x' y').2 (((pinsStay (Cells := Cells) (Tok := Tok) cs G arr smp ms N.index.1
      N.index.2 x x' y y' ho.2 fun m hi hm =>
        hsmp x x' m hi hm h.1 hbk hh (olderStay4 h)).2.1).1
      ((hG.noColl x y).1 h0))
  · rw [hG.decodes] at h0 ⊢
    exact decodes_M4 hdec x x' y y' h hc h0
  · rw [hG.pinW] at h0 ⊢
    exact pinWBack_M4 hdec x x' y y' w h hc h0
  · rw [hG.held] at hh
    exact (hG.pin x y w).2 (((pinsStay cs G arr smp ms N.index.1 N.index.2 x x' y y' ho.2
      fun m hi hm => hsmp x x' m hi hm h.1 hbk hh (olderStay4 h)).2.2 w).2
      ((hG.pin x' y' w).1 h0))

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.held4
#print axioms VerifiableInference.Desc.K13.Law.olderStay4
#print axioms VerifiableInference.Desc.K13.Law.others4_at_sig
