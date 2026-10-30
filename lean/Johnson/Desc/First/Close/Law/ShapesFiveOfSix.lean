-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/ShapesFiveOfSix.lean (kind K10): AT LINK 0, "THE STATE's GROUP HOLDS
THE WRITTEN LIST's MEMBERS" (`ShapesAre`, LayoutOfShapes.lean) AT THE SIX MESSAGES' LIST GIVES THE
SAME AT THE FIVE-LIST, AND BACK. Statements and proofs.

Why. K10's typed group at link 0 is cut over `loFive` (LinkZeroFive.lean, beside this file). Other
sentences on a state at link 0 (the shapes at the plan's numbers; the run on the honest walk)
stand at the first written list `loSix`. `ShapesAre` reads a list only at its messages with a main
row: and these are the same in both lists (`five_entries`, `five_flags`: by the kernel).
  `shapesAre_move` (general in the two lists): the members' entries agree in order; so do their
    flags; so do their numbers: THEN `ShapesAre T G lo kb no` gives `ShapesAre T G lo' kb' no'`.
  `shapesAre_five_of_six`, `shapesAre_six_of_five`: at `loSix`, `kbSix` and `loFive`, `kbFive`, for
    two numberings that agree on the members in order (hno).
Limits. hno is a premise: a closed fact where the two numberings are closed terms. Nothing is shown
of any state. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.LinkZeroFive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G

/-- **The sentence reads a list at its members alone.** -/
theorem shapesAre_move {T : Statement} {G : Group} {lo lo' : List (OracleShape × ℕ)}
    {kb : Fin lo.length → Bool} {kb' : Fin lo'.length → Bool} {no : Fin lo.length → ℕ}
    {no' : Fin lo'.length → ℕ}
    (he : (membersOf lo').map (fun i => lo'.get i) = (membersOf lo).map fun i => lo.get i)
    (hf : (membersOf lo').map kb' = (membersOf lo).map kb)
    (hno : (membersOf lo').map no' = (membersOf lo).map no) (H : ShapesAre T G lo kb no) :
    ShapesAre T G lo' kb' no' := by
  refine ⟨H.members.trans hno.symm, H.kept.trans hf.symm, fun i hi => ?_⟩
  have hz : (membersOf lo').map (fun i => (no' i, lo'.get i)) =
      (membersOf lo).map fun j => (no j, lo.get j) :=
    (List.zip_map' (f := no') (g := fun i => lo'.get i) (l := membersOf lo')).symm.trans
      ((congrArg₂ List.zip hno he).trans
        (List.zip_map' (f := no) (g := fun j => lo.get j) (l := membersOf lo)))
  have hm : (no' i, lo'.get i) ∈ (membersOf lo).map fun j => (no j, lo.get j) :=
    hz ▸ List.mem_map_of_mem hi
  obtain ⟨j, hj, e⟩ := List.mem_map.1 hm
  have e1 : no j = no' i := congrArg Prod.fst e
  have e2 : lo.get j = lo'.get i := congrArg Prod.snd e
  rw [← e1, ← e2]
  exact H.shape j hj

theorem shapesAre_five_of_six {T : Statement} {G : Group} {no6 : Fin loSix.length → ℕ}
    {no5 : Fin loFive.length → ℕ}
    (hno : (membersOf loFive).map no5 = (membersOf loSix).map no6)
    (H : ShapesAre T G loSix kbSix no6) : ShapesAre T G loFive kbFive no5 :=
  shapesAre_move five_entries five_flags hno H

theorem shapesAre_six_of_five {T : Statement} {G : Group} {no6 : Fin loSix.length → ℕ}
    {no5 : Fin loFive.length → ℕ}
    (hno : (membersOf loFive).map no5 = (membersOf loSix).map no6)
    (H : ShapesAre T G loFive kbFive no5) : ShapesAre T G loSix kbSix no6 :=
  shapesAre_move five_entries.symm five_flags.symm hno.symm H

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.shapesAre_move
#print axioms VerifiableInference.Desc.First.Close.shapesAre_five_of_six
#print axioms VerifiableInference.Desc.First.Close.shapesAre_six_of_five
