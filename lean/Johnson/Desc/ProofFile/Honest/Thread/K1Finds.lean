-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/K1Finds.lean: WHAT THE LIST OF K1's LOT (lotHalves,
Honest/K1/PlaceJob.lean, of other authors) HOLDS AT THE FIRST SEGMENT's OPENING AND AT A BUILT
SEGMENT's READS AND DIGITS. At the lot's own list, at letters wit, no, D, Z, G: no filling, no
prover. Six statements with their proofs.

  pieces_of_numbers   the two pieces that the library's linkNumbers names are 4 and 6, or 5 and 7
  mem_lotHalves       a side of K1's list is the opening's, or a built segment's reads' or digits'
  later_mem           the two sides of a built segment stand in K1's list
  k1_find_first · k1_find_reads · k1_find_digits   what K1's list holds at these places

The premises. hX: Y is segment number l of the ground · hN: the library's linkNumbers
(Johnson/Desc/ProofFile/Lot/K1.lean) answers (pr, pd, r, d) at Y · hy: y is a side of the list.

They are lemmas on other authors' list, typed off its text. Where the list's authors have the like
in a file of their own, theirs is the one to keep and this one to strike.

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. That a sub-protocol stands at one of these places is not said here. On lists and places
alone. No property of a prover or a protocol is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob
import Johnson.Desc.ProofFile.Honest.Thread.FindBasics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstFill
open VerifiableInference.Desc (Place KindName)
open OnBytes.Model.Stages (LinkH)

/-- The two pieces that linkNumbers names are 4 and 6, or 5 and 7. -/
theorem pieces_of_numbers {G : Ground} {Y : LinkH} {pr pd : Nat} {r d : Option (List Nat)}
    (h : VerifiableInference.Desc.K1.linkNumbers G Y = some (pr, pd, r, d)) :
    (pr = 4 ∧ pd = 6) ∨ (pr = 5 ∧ pd = 7) := by
  unfold VerifiableInference.Desc.K1.linkNumbers at h
  split at h
  · obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.1 h
    cases e
    exact Or.inl ⟨rfl, rfl⟩
  · split at h
    · obtain ⟨_, _, e⟩ := Option.map_eq_some_iff.1 h
      cases e
      exact Or.inl ⟨rfl, rfl⟩
    · cases h
      exact Or.inr ⟨rfl, rfl⟩

section
variable {V W X Xi : Type} (wit : W → K1.PlaceIn Xi) (no : Place → Nat)
  (D : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground)

/-- **A side of K1's list is the opening's, or a built segment's reads' or digits'.** -/
theorem mem_lotHalves {y : Placed V W X} (hy : y ∈ K1.lotHalves wit no D Z G) :
    y = K1.placeHalf wit (K1.placeJob (VerifiableInference.Desc.K1.firstPar G.first
        (VerifiableInference.Desc.K1.gpOf Z)) (no ⟨1, some 0, 1, .K1⟩) (K1.firstFold G.first)
        (D Z G)) ∨
      ∃ (Y : LinkH) (l pr pd : Nat) (r d : Option (List Nat)), G.built[l]? = some Y ∧
        VerifiableInference.Desc.K1.linkNumbers G Y = some (pr, pd, r, d) ∧
        (y = K1.placeHalf wit (K1.laterJobAt G.first (VerifiableInference.Desc.K1.gpOf Z) l pr 1
            (no ⟨1, some l, pr, .K1⟩) (D Z G)) ∨
          y = K1.placeHalf wit (K1.laterJobAt G.first (VerifiableInference.Desc.K1.gpOf Z) l pd 2
            (no ⟨1, some l, pd, .K1⟩) (D Z G))) := by
  rcases List.mem_cons.1 hy with h | h
  · exact Or.inl h
  · obtain ⟨⟨Y, l⟩, hm, hz⟩ := List.mem_flatMap.1 h
    rw [List.mk_mem_zipIdx_iff_getElem?, Array.getElem?_toList] at hm
    dsimp only at hz
    split at hz
    · cases hz
    · rename_i pr pd r d hN
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      exact Or.inr ⟨Y, l, pr, pd, r, d, hm, hN, hz⟩

/-- What K1's list holds at the first segment's opening. No premise. -/
theorem k1_find_first :
    (K1.lotHalves (V := V) (X := X) wit no D Z G).find?
        (fun g => g.place == ⟨1, some 0, 1, .K1⟩) =
      some (K1.placeHalf wit (K1.placeJob (VerifiableInference.Desc.K1.firstPar G.first
        (VerifiableInference.Desc.K1.gpOf Z)) (no ⟨1, some 0, 1, .K1⟩) (K1.firstFold G.first)
        (D Z G))) :=
  List.find?_cons_of_pos (by exact beq_self_eq_true _)

variable {l pr pd : Nat} {Y : LinkH} {r d : Option (List Nat)}

/-- The two sides of a built segment stand in K1's list. -/
theorem later_mem (hX : G.built[l]? = some Y)
    (hN : VerifiableInference.Desc.K1.linkNumbers G Y = some (pr, pd, r, d)) :
    (K1.placeHalf (V := V) (X := X) wit (K1.laterJobAt G.first
        (VerifiableInference.Desc.K1.gpOf Z) l pr 1 (no ⟨1, some l, pr, .K1⟩) (D Z G)) ∈
        K1.lotHalves wit no D Z G) ∧
      (K1.placeHalf (V := V) (X := X) wit (K1.laterJobAt G.first
        (VerifiableInference.Desc.K1.gpOf Z) l pd 2 (no ⟨1, some l, pd, .K1⟩) (D Z G)) ∈
        K1.lotHalves wit no D Z G) := by
  have hm : (Y, l) ∈ G.built.toList.zipIdx := by
    rw [List.mk_mem_zipIdx_iff_getElem?, Array.getElem?_toList]
    exact hX
  constructor
  · refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨(Y, l), hm, ?_⟩)
    dsimp only
    rw [hN]
    exact List.mem_cons_self ..
  · refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨(Y, l), hm, ?_⟩)
    dsimp only
    rw [hN]
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

/-- **What K1's list holds at a built segment's reads.** -/
theorem k1_find_reads (hX : G.built[l]? = some Y)
    (hN : VerifiableInference.Desc.K1.linkNumbers G Y = some (pr, pd, r, d)) :
    (K1.lotHalves (V := V) (X := X) wit no D Z G).find?
        (fun g => g.place == ⟨1, some l, pr, .K1⟩) =
      some (K1.placeHalf wit (K1.laterJobAt G.first (VerifiableInference.Desc.K1.gpOf Z) l pr 1
        (no ⟨1, some l, pr, .K1⟩) (D Z G))) := by
  refine find_of_unique (later_mem wit no D Z G hX hN).1 fun y hy e => ?_
  have e' : y.place = ⟨1, some l, pr, .K1⟩ := e
  have hP := pieces_of_numbers hN
  rcases mem_lotHalves wit no D Z G hy with rfl | ⟨Y', l', pr', pd', r', d', hX', hN', rfl | rfl⟩
  · have e1 : (1 : Nat) = pr := congrArg Place.piece e'
    omega
  · have el : l' = l := Option.some.inj (congrArg Place.link e')
    subst el
    obtain rfl : Y' = Y := Option.some.inj (hX'.symm.trans hX)
    cases hN'.symm.trans hN
    rfl
  · have el : l' = l := Option.some.inj (congrArg Place.link e')
    subst el
    obtain rfl : Y' = Y := Option.some.inj (hX'.symm.trans hX)
    cases hN'.symm.trans hN
    have e1 : pd = pr := congrArg Place.piece e'
    omega

/-- **What K1's list holds at a built segment's digits.** -/
theorem k1_find_digits (hX : G.built[l]? = some Y)
    (hN : VerifiableInference.Desc.K1.linkNumbers G Y = some (pr, pd, r, d)) :
    (K1.lotHalves (V := V) (X := X) wit no D Z G).find?
        (fun g => g.place == ⟨1, some l, pd, .K1⟩) =
      some (K1.placeHalf wit (K1.laterJobAt G.first (VerifiableInference.Desc.K1.gpOf Z) l pd 2
        (no ⟨1, some l, pd, .K1⟩) (D Z G))) := by
  refine find_of_unique (later_mem wit no D Z G hX hN).2 fun y hy e => ?_
  have e' : y.place = ⟨1, some l, pd, .K1⟩ := e
  have hP := pieces_of_numbers hN
  rcases mem_lotHalves wit no D Z G hy with rfl | ⟨Y', l', pr', pd', r', d', hX', hN', rfl | rfl⟩
  · have e1 : (1 : Nat) = pd := congrArg Place.piece e'
    omega
  · have el : l' = l := Option.some.inj (congrArg Place.link e')
    subst el
    obtain rfl : Y' = Y := Option.some.inj (hX'.symm.trans hX)
    cases hN'.symm.trans hN
    have e1 : pr = pd := congrArg Place.piece e'
    omega
  · have el : l' = l := Option.some.inj (congrArg Place.link e')
    subst el
    obtain rfl : Y' = Y := Option.some.inj (hX'.symm.trans hX)
    cases hN'.symm.trans hN
    rfl

end

end ProofFile.Honest.FirstFill

#print axioms ProofFile.Honest.FirstFill.pieces_of_numbers
#print axioms ProofFile.Honest.FirstFill.mem_lotHalves
#print axioms ProofFile.Honest.FirstFill.k1_find_first
#print axioms ProofFile.Honest.FirstFill.later_mem
#print axioms ProofFile.Honest.FirstFill.k1_find_reads
#print axioms ProofFile.Honest.FirstFill.k1_find_digits
