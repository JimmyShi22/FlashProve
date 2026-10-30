-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/DoorPlanOk.lean: THE PLAN's SHARE OF THE DOOR's PREMISES (DoorPlan,
Johnson/Prover/Link/DoorPay.lean) AS A PUBLIC TEST WITH CODE.

Main names (namespace Johnson.Prover.Link).
  doorPlanL   DoorPlan's twenty-one clauses as Booleans, each under its field's name.
  doorPlanOk   every clause says yes.
  doorPlan_of_ok   where the test says yes DoorPlan holds.

Limits. Nothing says here that the test says yes at any numbers: at a toy's:
Johnson/Prover/Link/DoorPlanToy.lean. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.DoorPay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- **DoorPlan's clauses, with code**, each under its field's name. The clause "one" says yes where
`layTrees` returns nothing. The clauses under the captions "freshRows" and "freshCode" are
`maskRows = 2 ^ cur.h` and `maskCode = i.2` of the shape of `foldMaskNotice (linkFoldShape S)`. -/
def doorPlanL (S : LinkShape) (K : Codes) (p : P12) (cur nxt : Fmt.M1.Stage) (i n : Nat × Nat) :
    List (String × Bool) :=
  [("ahead", S.masksAhead),
   ("idx0", decide (p.idx[0]? = some i)),
   ("idx1", decide (p.idx[1]? = some n)),
   ("code", decide (S.code = i.1)),
   ("maskCode", decide (S.maskCode = i.2)),
   ("base", decide (K.base[i.1]? = some ⟨cur.C.a, cur.C.l, cur.C.r⟩)),
   ("maskC", decide (K.mask[i.2]? = some ⟨cur.Z.a, cur.Z.l, cur.Z.r⟩)),
   ("base1", decide (K.base[n.1]? = some ⟨nxt.C.a, nxt.C.l, nxt.C.r⟩)),
   ("mask1", decide (K.mask[n.2]? = some ⟨nxt.Z.a, nxt.Z.l, nxt.Z.r⟩)),
   ("layK", decide (ceilLog2 S.rows + 1 = cur.k)),
   ("layH", decide (cur.h = 0)),
   ("freshRows", decide ((foldMaskNotice (linkFoldShape S)).shape.maskRows = 2 ^ cur.h)),
   ("freshCode", decide ((foldMaskNotice (linkFoldShape S)).shape.maskCode = i.2)),
   ("stage", K12.stageOk false cur),
   ("stage1", decide (nxt.Z.a ≤ nxt.C.a)),
   ("vars", decide (cur.k + ceilLog2 cur.C.l ≤ 63)),
   ("early", p.early),
   ("codes", codesFit p { codes := K }),
   ("pub", H2K.Pub.pubOk p K),
   ("free", decide (p.nums.free = 1)),
   ("one", match layTrees K (linkMessage S 1) with
     | some l => decide (l.shapes.size = 1)
     | none => true)]

/-- The test: every clause says yes. -/
def doorPlanOk (S : LinkShape) (K : Codes) (p : P12) (cur nxt : Fmt.M1.Stage) (i n : Nat × Nat) :
    Bool :=
  (doorPlanL S K p cur nxt i n).all (·.2)

/-- **Where the test says yes DoorPlan holds.** -/
theorem doorPlan_of_ok {S : LinkShape} {K : Codes} {p : P12} {cur nxt : Fmt.M1.Stage}
    {i n : Nat × Nat} (h : doorPlanOk S K p cur nxt i n = true) : DoorPlan S K p cur nxt i n := by
  unfold doorPlanOk doorPlanL at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21⟩ := h
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, fun l hl => ?_⟩
  rw [hl] at a21
  exact of_decide_eq_true a21

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.doorPlan_of_ok
