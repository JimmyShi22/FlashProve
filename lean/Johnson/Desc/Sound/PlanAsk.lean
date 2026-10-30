-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PlanAsk.lean: WHAT "ONE DECODER" ASKS OF THE PLAN, AS ONE TEST WITH CODE ON PUBLIC DATA; and the closed statements under that one test. One definition, four theorems.

  fullShapeB S: the shape's table has the code ⟨32, 402653184, 44040191⟩, 2^11 rows and one answer (its salt's bytes are not read); the matrix has 3076096 rows and kLo = 7.
  full_index, full_nums, full_cut: a yes gives the three premises of Johnson/Desc/Sound/DataAlong.lean | HeldAlong.lean: the equation on the table's shape · numsFull (Johnson/Flat/ClaimsSizes.lean) = ⟨matrixRows, kLo⟩ · matrixRows * 2 ^ kLo ≤ index.plain.
  heldTie_asked: **HeldTie at the release's configuration's own held, at numsFull, under that one test.**
A RUN, NO THEOREM (its print: not in this library): at the stored full-size set of record each conjunct says true, and three turned controls say false.

Limits. The full size alone. That a verifier asks this test is nobody's word yet: it is a test on the three public files' plan that only refuses more. NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.HeldAlong
import Johnson.Flat.ClaimsSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker OnBytes.Flat Desc.Plain

/-- **The one test on the plan**: the full size's table's shape and the matrix's two numbers. -/
def fullShapeB (S : LinShape) : Bool :=
  decide (S.fold.index = ⟨⟨32, 402653184, 44040191⟩, 11, 1, S.fold.index.saltBytes⟩) &&
    S.matrixRows == 3076096 && S.kLo == 7

/-- A yes gives the equation on the table's shape. -/
theorem full_index (S : LinShape) (h : fullShapeB S = true) :
    S.fold.index = ⟨⟨32, 402653184, 44040191⟩, 11, 1, S.fold.index.saltBytes⟩ := by
  unfold fullShapeB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact h.1.1

/-- A yes gives that the configuration's two numbers are the plan's. -/
theorem full_nums (S : LinShape) (h : fullShapeB S = true) : numsFull = ⟨S.matrixRows, S.kLo⟩ := by
  unfold fullShapeB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rw [h.1.2, h.2]
  rfl

/-- A yes gives that the matrix lies before the pads. -/
theorem full_cut (S : LinShape) (h : fullShapeB S = true) :
    S.matrixRows * 2 ^ S.kLo ≤ S.fold.index.plain := by
  have hi := full_index S h
  unfold fullShapeB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rw [h.1.2, h.2, hi]
  show 3076096 * 2 ^ 7 ≤ 402653184 - 3 * 1
  decide

/-- **"held" at the release's configuration's own held, under the one test.** -/
theorem heldTie_asked (p : Par) (err : Nat) (h : fullShapeB p.S = true) (pp : Inst.Model.ScalesAndPolicy)
    (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) numsFull pp)) :
    HeldTie p err 2852142980 (rankLib p.S.fold)
      (heldFull p err p.S.fold.index.saltBytes (full_index p.S h) numsFull pp E)
      (matN (frS.toDecR frZ 402653181) numsFull) :=
  heldTie_full p err p.S.fold.index.saltBytes (full_index p.S h) numsFull (full_nums p.S h) pp E
    (full_cut p.S h)

end Desc.K14.Law

#print axioms Desc.K14.Law.full_index
#print axioms Desc.K14.Law.full_nums
#print axioms Desc.K14.Law.full_cut
#print axioms Desc.K14.Law.heldTie_asked
