-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/HandedLetters.lean: THE HONEST SIDE's FRAME: WHAT ITS FIELDS HAND AT A MEMBER, TURNED
ONCE INTO THE LETTERS THAT OUR LEMMAS ON A WALK ASK. A lemma; NONE OF THE LIBRARY's GOALS. No new
argument. Nothing on completeness, soundness or hiding.

  **`handed_letters`**   letter_starts, letter_tree
      (Johnson/Desc/ProofFile/Honest/Law/CoverLetter.lean); the texts of silentQ, marksQuiet
      (CoverJoin.lean) and fitMarks (CoverFit.lean)
Why. These lines stand in five proofs of ours, each time anew: Johnson/P1K8R/AsksSymbols.lean,
AsksLooks.lean, AsksLayersLive.lean, AsksHeadLive.lean and AsksAllLive.lean. These five have
their own lines; Johnson/P1K8R/FieldAtHead.lean, FieldAtAtt.lean and FieldAtLay.lean call this
lemma.
Kin. The frame's authors' hP_reach (Johnson/Desc/ProofFile/Honest/Law/CoverOwn.lean): whoever proves
the field hP' may take besides, as a premise, that the state is reached by the wrapped blocks: it
works on the same premises; another end.
Limits. General in the description, the prover and the list of marks: all are letters; no filling is
named. It says nothing on whether a walk returns, nor on what the silence costs. Two tactics that
search, once each: simp, simpa.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverLetter
import Johnson.Desc.ProofFile.Honest.Law.CoverFit
import Johnson.Desc.ProofFile.Honest.Law.CoverJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open VerifiableInference.Desc
open ProofFile.Honest (Mark Prover Ready ChainAt Local at₁ ChainProgress Mid silentQ marksQuiet fitMarks drawsFit
  letter_starts letter_tree)

variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- **FROM WHAT THE FRAME's FIELDS hP' AND hPM HAND, TO THE WALK's OWN LETTERS.** F: any
description; the walk's letter Xc is the frame's own (hXc). Given the cut of the first chain's list
at a member b, the length of the challenges in front, the marks' silence in the field's form, and a
start: the list cut at b; the walk's first tree is 0; the start comes from `ChainProgress.start` at the
description's own first state; the challenges are as many as the rounds in front; the marks' silence
in the form of `marksQuiet`; and the fit's mark of each member in front is among the marks asked. -/
theorem handed_letters (F : FileDescription Xi) (P : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (R : Ready W₀ Rc Xi Ky Tr X₀ X)
    (Xc : List Fmt.Drawn → ChainAt F.S₁ F.Cl (Local W₀ Rc Xi Tr) X)
    (hXc : Xc = fun _ => at₁ F P w₀ rc x R) (hm : List Mark)
    {pre₁ : List (Block F.S₁ F.Cl)} {e₁ : Block F.S₁ F.Cl} (cut : F.first.blocksInOrder = pre₁ ++ [e₁])
    {A B : List (Block F.S₁ F.Cl)} {b b' : Block F.S₁ F.Cl} (e : pre₁ = A ++ b :: b' :: B)
    {fr : List Fmt.Drawn} {a : ChainProgress F.S₁ F.Cl (Local W₀ Rc Xi Tr) X}
    (h2 : (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length)
    (h4 : silentQ (hm ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr)
    (y1 : (Xc (fr.take 0)).start = some a) :
    F.first.blocksInOrder = A ++ b :: (b' :: B ++ [e₁]) ∧ (Xc (fr.take 0)).lay.firstTree = 0 ∧
      (∃ m₀ : Option (Mid (Local W₀ Rc Xi Tr) X), m₀.isSome = true ∧
        ChainProgress.start (Xc (fr.take 0)).lay F.first.blocksInOrder m₀ (some (F.start₁ (F.pub x))) [] = .ok a) ∧
      fr.length = (A.flatMap (·.rounds)).length ∧
      marksQuiet (hm ++ fitMarks pre₁) A [] fr = true ∧
      ∀ d ∈ A, (⟨d.place,
        fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
        ⟨0, 1⟩⟩ : Mark) ∈ hm ++ fitMarks pre₁ := by
  have htk : pre₁.take (0 + A.length) = A := by
    rw [e, Nat.zero_add]
    exact List.take_left' rfl
  have hq : marksQuiet (hm ++ fitMarks pre₁) A [] fr = true := by
    have h4' : marksQuiet (hm ++ fitMarks pre₁) (pre₁.take (0 + A.length)) (fr.take 0)
      (fr.drop 0) = true := h4
    rw [htk] at h4'
    exact h4'
  refine ⟨?_, letter_tree F P w₀ rc x R Xc hXc (fr.take 0),
    letter_starts F P w₀ rc x R Xc hXc _ a y1, by simpa using h2, hq, fun d hd =>
      List.mem_append_right _ (List.mem_map.2
        ⟨d, by rw [e]; exact List.mem_append_left _ hd, rfl⟩)⟩
  rw [cut, e]
  simp

end P1K8

#print axioms P1K8.handed_letters
