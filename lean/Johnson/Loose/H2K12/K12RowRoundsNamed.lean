-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/K12RowRoundsNamed.lean: CONDITIONAL: UNDER THE PREMISE hV, WHICH IS SHOWN OF NO
PUBLIC FILES BY LEAN's KERNEL: THE PROXIMITY TEST's (the kind K12's)
SECOND ROW IN THE FORM "at the written name of the sub-protocol's own place": FOR EACH SUB-PROTOCOL
b OF THE LOT: b.rounds IS THE WRITTEN TABLE's LIST AT nameW b.place: the premise w of
ProofFile.Sk.Full.rows_by_place (Johnson/Desc/ProofFile/Law/Skel/Full/Names.lean) at
Q := ProofFile.Sk.Lst listAt (…/Skel/SkelLists.lean: not imported): ProofFile.Sk.Lst listAt (nameW b.place)
b.rounds is Or.inr of the end. NO SPOT, NO LIST OF SPOTS, NO PREMISE ON A SPOT's NAME:
THE ONE PREMISE IS hV.
THIS FILE HOLDS BOTH: THREE EVALUATIONS IN LEAN's KERNEL (decide +kernel) AND ONE LAW.
  nameW_at_F2      the written name at ⟨1, none, 2, K12⟩ is "F:2". A closed equation of two strings;
                   nameW bears the empty name where no written spot has the place: so it says by the
                   way that a written spot has this one
  nameW_at_M3      at ⟨1, none, 3, K13⟩ it is "M:3": the look-up tells two places apart
  nameW_at_F2_no   A COROLLARY, NO CONTROL: at ⟨1, none, 2, K12⟩ it is NOT "M:3": it follows from
                   nameW_at_F2 and the two strings' being unlike, so it cannot fail: to be counted
                   nowhere as a negative test
  k12_row_named    from hV (the first row's own premise: the numbers which the list of rounds gives
                   are the written member piLFull): the row. By k12_blocks_rounds
                   (H2K12/K12RowRounds.lean) and nameW_at_F2
NEAREST KIN, DECLARED: names_full (Names.lean): at each written spot's place the name
that is looked up is its own. nameW_at_F2 is no bare instance of it: that would want "a spot with
this name and place is among the written spots", a closed fact of the same cost.
WHO PAYS "the places are the written ones" (rows_by_place's h₁ : B.spots = spotsW) IS THE CALLER's
MATTER, NOT THIS FILE's. G IS IDLE: the lot reads no ground. hV is shown of no public files by
Lean's kernel. The full size alone. No soundness statement. Nothing on hiding.

-/
import Johnson.Loose.H2K12.K12RowRounds
import Johnson.Desc.ProofFile.Law.Skel.Full.Names

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open H2K.Member (piLFull)

theorem nameW_at_F2 : ProofFile.Sk.Full.nameW ⟨1, none, 2, .K12⟩ = "F:2" := by
  decide +kernel

theorem nameW_at_M3 : ProofFile.Sk.Full.nameW ⟨1, none, 3, .K13⟩ = "M:3" := by
  decide +kernel

theorem nameW_at_F2_no : decide (ProofFile.Sk.Full.nameW ⟨1, none, 2, .K12⟩ = "M:3") = false := by
  decide +kernel

/-- **THE ROW, IN THE FORM "at the written name of its own place".** -/
theorem k12_row_named (Z : ProofFile.Pub) (G : ProofFile.Ground) (hV : H2U.p12OfMade Z.made = piLFull) :
    ∀ b ∈ (VerifiableInference.Desc.K12.lot Z).blocks G,
      b.rounds = Johnson.AtFull.Rounds.listAt (ProofFile.Sk.Full.nameW b.place) := by
  intro b hb
  obtain ⟨h1, h2⟩ := k12_blocks_rounds Z G hV b hb
  rw [h1, nameW_at_F2]
  exact h2

end H2K12

#print axioms H2K12.nameW_at_F2
#print axioms H2K12.nameW_at_M3
#print axioms H2K12.nameW_at_F2_no
#print axioms H2K12.k12_row_named
