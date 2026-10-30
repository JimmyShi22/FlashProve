-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/HalfAtAnyFill.lean: the proofs of the three statements of
Honest/K11/Plays/HalfAtAnyFillStatement.lean, to the letter. Lemmas; none of the library's goals.

How. The first: by induction on the list. At a lot with L's halves the search stops, at g. At a lot
whose halves stand at places of other kinds it finds nothing and goes on; such a lot is not the one
that has L's halves, since g stands among these at p. The second: `atPureOpens` (AtPureOpens.lean of
this folder): the prover's first list is the list of halves lot by lot; then the first, at L := the
kind's lot and p := the kind's place, whose kind is K11 by its text. The third: the second, read
at the public data, the ground and the place that the head gives: it calls `halfAtAnyFill` and
rewrites by these three equations.

Near. The first two could be calls of the frame's authors' `firstOf_find_kind` and
`atPure_first_find_kind` (Honest/FirstFindKind.lean), which are not imported here: see the
statements' file.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.HalfAtAnyFillStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.AtPureOpens
import Johnson.Desc.ProofFile.Honest.K11.Plays.SeatAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull placeOfLot)

/-- **The search in the list of halves lot by lot.** -/
theorem findOfLots : FindOfLots := by
  intro V W X Z G ls L p g
  induction ls with
  | nil =>
    rintro ⟨M, hM, _⟩
    cases hM
  | cons M₀ ls ih =>
    intro hex ho hg
    show (List.find? _ (M₀.halves Z G ++ firstOf Z G ls)) = _
    rw [List.find?_append]
    rcases ho M₀ (List.mem_cons_self ..) with hk | he
    · have hn : ((M₀.halves Z G).find? fun x => x.place == p) = none := by
        rw [List.find?_eq_none]
        intro y hy hb
        exact hk y hy (congrArg VerifiableInference.Desc.Place.kind (eq_of_beq hb))
      rw [hn, Option.none_or]
      refine ih ?_ (fun M hM => ho M (List.mem_cons_of_mem _ hM)) hg
      obtain ⟨M, hM, hMe⟩ := hex
      rcases List.mem_cons.1 hM with rfl | hM'
      · exfalso
        rw [hMe, hg] at hn
        cases hn
      · exact ⟨M, hM', hMe⟩
    · rw [he, hg]
      rfl

/-- **At the prover that the maker builds, at any filling.** -/
theorem halfAtAnyFill : HalfAtAnyFill := by
  intro W₀ Rc Tr X₀ X o pol lay KL P A claims weights hA hex ho
  obtain ⟨_, _, hF⟩ := atPureOpens _ _ _ _ _ _ _ _ _ _ A hA
  rw [hF]
  refine findOfLots _ _ _ A.Z A.G P.lots (headMergeLot claims weights) _ _ hex ho ?_
  show (List.find? _ [headMergeHalf (claims A.Z A.G) weights (_root_.K11.parOf A.Z A.G)]) = _
  rw [List.find?_cons_of_pos (by exact beq_self_eq_true _)]

/-- **Under the head.** -/
theorem halfAtAnyFillHead : HalfAtAnyFillHead := by
  intro Z D r Zp Np cF x h W₀ Rc Tr X₀ X P A Bs claims weights hB hA hex ho
  obtain ⟨hZ, hG, _⟩ := atPureOpens _ _ _ _ _ _ _ _ _ _ A hA
  have e1 : A.Z = Zp := Except.ok.inj (hZ.symm.trans h.laid.pub)
  obtain ⟨Bs', base, Op⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (Op.made.symm.trans hB)
  have e2 : A.G = Bs'.G₀ := by
    rw [e1] at hG
    exact Option.some.inj (hG.symm.trans Op.blank)
  obtain ⟨Bs'', _, _, hB'', _, _, _, _, _, hl⟩ := headMergeAtFull Z D r Zp Np cF x h
  obtain rfl : Bs'' = Bs' := Except.ok.inj (hB''.symm.trans hB)
  have hp : headMergePlace (_root_.K11.parOf Zp Bs''.G₀) = IM.k11Place :=
    (headMergePlaceIs _).trans (placeOfLot Zp Bs''.G₀ hl)
  have hh := halfAtAnyFill _ _ _ _ _ _ _ _ _ P A claims weights hA hex ho
  rw [e1, e2, hp] at hh
  exact ⟨e1, e2, hh⟩

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.findOfLots
#print axioms ProofFile.Honest.K11.halfAtAnyFill
#print axioms ProofFile.Honest.K11.halfAtAnyFillHead
