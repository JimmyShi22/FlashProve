-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FillK13Laws.lean: EACH TEST OF THE LAYER's HALF WITH CODE
(Johnson/Desc/K13/PubK13.lean: the names that end in C) IS THE TEST OF WHICH THE KINDS' LAWS SPEAK.
Equations with their proofs, nearly all by the make. It stands BESIDE the layer: the layer does not
import it.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.PubK13
import Johnson.Desc.K13.Law.PileMasksIff
import Johnson.Desc.K1.Law.IndexBools
import Johnson.Desc.K13.Law.SitsAt
import Johnson.Desc.K13.Law.SeatMade
import Johnson.Desc.K13.Law.SitsDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes
open VerifiableInference.Desc.First (S Pub Numbers)

theorem noneSentC_eq (N : Numbers) (s : S) :
    noneSentC N s =
      (K1.noneSentB s && (s.st.groups.size == N.groupAt 0) && s.out.pending.isEmpty) := rfl
theorem indexIsC_eq (n : Nat) (s : S) : indexIsC n s = K1.indexIsB n s := rfl
theorem indexThereC_eq (s : S) : indexThereC s = K1.indexThereB s := rfl
theorem linAtC_eq (s : S) : linAtC s = linAt s := rfl
theorem claimMadeC_eq (c : LinClaim) : claimMadeC c = claimMadeB c := rfl
theorem tableSizeC_eq (St : Statement) (o : Nat) (part : OnBytes.Part) :
    tableSizeC St o part = OnBytes.Means.tableSize St o part := rfl
theorem frontOkC_eq (P : Where) (s : S) : frontOkC P s = frontOkB P s := rfl
theorem evalInC_eq (St : Statement) (w : Nat) (lay : VectorLay) (masks : MaskForm) :
    evalInC St w lay masks = evalInB St w lay masks := rfl
theorem evalLaidC_eq (P : Where) (s : S) : evalLaidC P s = evalLaidB P s := rfl
theorem wSeatC_eq (seat : Nat × Nat) (s : S) : wSeatC seat s = wSeatB seat s := rfl
theorem wSitsItem_eq : wSitsItem = Pub.more none "K13.wSits" := rfl

theorem wSitsLC_eq (cs : Codes) (P : Where) (s : S) : wSitsLC cs P s = wSitsL cs P s := by
  unfold wSitsLC wSitsL laidOf
  rw [evalLaidC_eq, linAtC_eq]
  cases linAt s with
  | none => rfl
  | some l =>
    simp only [Option.bind_some]
    cases linEvalRow P.lin l.claim l.w (linLayW s.st.codes P.lin) <;> rfl

theorem wSitsC_eq (cs : Codes) (P : Where) (s : S) : wSitsC cs P s = wSitsB cs P s := by
  unfold wSitsC wSitsB
  rw [wSitsLC_eq]

end VerifiableInference.Desc.K13.Law
