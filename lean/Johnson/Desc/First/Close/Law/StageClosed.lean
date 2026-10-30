-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/StageClosed.lean (kind K10): FOUR CLOSED FACTS ON K10's TYPED GROUP AT
A LETTER FOR THE CODES: what `OnLeft` (Johnson/Desc/First/Link/Law/OnOfShapes.lean)
asks under the names good, kL and h0, and the number of the fold's rounds. Statements and proofs:
calls.

  `stage_h0`: the stage of a written group in front has no variable for the mask rows: `(stageOf gs
    219).h = 0`. `stage_k`: its two numbers of variables add to the group's k.
  `kL_of`: so, where gs.k is the formula's number of row variables at the list and the flags: `kLay
    lo kb = (stageOf gs 219).h + (stageOf gs 219).g`.
  `good_cs`: where the corners fit (`Corners`), `groupLayK cs lo (stageOf gs 219) radFull kb hM hZ`
    is `Good`: by `sub_good_of_corners` (GroupSub.lean, beside this file), at cs = `codesFull2`.
General in the list (its entries stand on written lists): they serve the 25 written lists and link
0's five-list. WHO PAYS THE PREMISES: hk: `gsAt_front` at the written lists; `zero_gs`
with `five_kLay` at the five-list · hC: `linksFull_corners_all`; `five_corners_at` · `LayoutAgrees
lo kb` (that structure's field agrees): `linksFull_layout`; `five_layout`.
Limits. Closed facts. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.GroupSub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Params Johnson.Pack Johnson.Top.H Johnson.G Cb

theorem stage_h0 (gs : GroupSize) (hgs : gs ∈ frontFull) : (stageOf gs 219).h = 0 := by
  rw [← (frontFull_place gs hgs).2]
  rfl

theorem stage_k (gs : GroupSize) (hgs : gs ∈ frontFull) :
    (stageOf gs 219).h + (stageOf gs 219).g = gs.k := by
  rw [← (frontFull_place gs hgs).2]
  show 0 + gs.k = gs.k
  omega

theorem kL_of (gs : GroupSize) (hgs : gs ∈ frontFull) (lo : List (OracleShape × ℕ))
    (kb : Fin lo.length → Bool) (hk : gs.k = kLay lo kb) :
    kLay lo kb = (stageOf gs 219).h + (stageOf gs 219).g := by
  rw [stage_k gs hgs, hk]

/-- **The typed group at a letter for the codes is good.** -/
theorem good_cs (cs : OnBytes.Codes) (hcs : cs = codesFull2) (lo : List (OracleShape × ℕ))
    (hen : Written lo) (gs : GroupSize) (hgs : gs ∈ frontFull) (kb : Fin lo.length → Bool)
    (hM : ∀ i, memMain lo i → (lo.get i).1.mainRows ≠ 0 →
      cMain cs (lo.get i).1 = (stageOf gs 219).C)
    (hZ : ∀ i, memMain lo i → (lo.get i).1.maskRows ≠ 0 →
      cMask cs (lo.get i).1 = (stageOf gs 219).Z)
    (hC : Corners lo gs.k (fun i => layAt (sizesM lo kb) i.val)
      (fun i => layAt (sizesZ lo) i.val) kb) :
    (groupLayK cs lo (stageOf gs 219) radFull kb hM hZ).Good := by
  subst hcs
  exact sub_good_of_corners lo hen gs hgs _ _ kb hC

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.stage_h0
#print axioms VerifiableInference.Desc.First.Close.stage_k
#print axioms VerifiableInference.Desc.First.Close.kL_of
#print axioms VerifiableInference.Desc.First.Close.good_cs
