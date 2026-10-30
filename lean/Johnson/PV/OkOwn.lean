-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/OkOwn.lean: **okS AS A VALUE WITH CODE: THE FRONT SET's OWN TEST**, both sizes: «the
  reply of the request is 0: it is its own early part»: isOwn
  (Johnson/Flat/FrontSetOwnAt.lean:66) at enc := the subtype's value: what FrontSet.ownWords, at
  which the laws are proved (read, not shown here),
has for okS (beside «&& true»). IN THE PLACE OF okS := always. own‹S|F›_apart: on its
  yeses the request file's bytes tell the request (early_of_requestBytes). replyOne‹S|F›: a
  request that it refuses, for a control. IT IMPORTS FILES OF THE LIBRARY's BUILD ALONE.
WHY AN HONEST RUN PASSES IT: the proof file's first query holds the request's EARLY part (the
  carrier's early maps the instance by the object's early: «the reply laid 0»).


-/
import Johnson.Flat.FrontSetOwnAt
import Johnson.Flat.EarlyApart
import Johnson.Flat.FrontSetAtFiles
import Johnson.Flat.BigReqAt
import Johnson.Flat.SmallAtFiles

set_option autoImplicit false

namespace PV.OkOwn
open OnBytes.Flat VerifiableInference.OnPublicFiles

/-- **THE FRONT SET's OWN TEST, THE SMALL SIZE**: the reply of the request is 0. -/
def okOwnS (x : ReqAt sizesSmall) : Bool := decide (x.val.y = ⟨0, sizesSmall_V_pos⟩)

/-- It is isOwn (Johnson/Flat/FrontSetOwnAt.lean) at the subtype's value. -/
theorem okOwnS_is : okOwnS = OnBytes.K.Arm.ProofFront.isOwn sizesSmall_V_pos (fun x : ReqAt
    sizesSmall => x.val) := rfl

/-- On its yeses two requests with one request file are one. -/
theorem ownS_apart (x y : ReqAt sizesSmall) (hx : okOwnS x = true) (hy : okOwnS y = true)
    (e2 : requestBytesOf x.val = requestBytesOf y.val) : x = y := by
  have w : withoutReply sizesSmall_V_pos x.val = withoutReply sizesSmall_V_pos y.val :=
    early_of_requestBytes (P := sizesSmall) VerifiableInference.OnPublicFiles.sizesSmall_T
        VerifiableInference.OnPublicFiles.sizesSmall_V sizesSmall_V_pos e2
  have ox : withoutReply sizesSmall_V_pos x.val = x.val := by
    unfold withoutReply
    rw [← (of_decide_eq_true hx : x.val.y = ⟨0, sizesSmall_V_pos⟩)]
  have oy : withoutReply sizesSmall_V_pos y.val = y.val := by
    unfold withoutReply
    rw [← (of_decide_eq_true hy : y.val.y = ⟨0, sizesSmall_V_pos⟩)]
  exact Subtype.ext (ox.symm.trans (w.trans oy))

/-- A request with the reply 1 (T tokens 0; «the next token after these»): for a control. -/
def replyOneS : ReqAt sizesSmall :=
  ⟨Inst.Model.Instance.nextOf (fun _ => ⟨0, sizesSmall_V_pos⟩) ⟨1, by decide⟩, by decide, fun h =>
      absurd h (by decide)⟩

/-- **THE FRONT SET's OWN TEST, THE FULL SIZE**: the reply of the request is 0. -/
def okOwnF (x : ReqAt Inst.Model.ppref) : Bool := decide (x.val.y = ⟨0, ppref_V_pos⟩)

/-- It is isOwn (Johnson/Flat/FrontSetOwnAt.lean) at the subtype's value. -/
theorem okOwnF_is : okOwnF = OnBytes.K.Arm.ProofFront.isOwn ppref_V_pos (fun x : ReqAt
    Inst.Model.ppref => x.val) := rfl

/-- On its yeses two requests with one request file are one. -/
theorem ownF_apart (x y : ReqAt Inst.Model.ppref) (hx : okOwnF x = true) (hy : okOwnF y = true)
    (e2 : requestBytesOf x.val = requestBytesOf y.val) : x = y := by
  have w : withoutReply ppref_V_pos x.val = withoutReply ppref_V_pos y.val :=
    early_of_requestBytes (P := Inst.Model.ppref) VerifiableInference.OnPublicFiles.ppref_T
        VerifiableInference.OnPublicFiles.ppref_V ppref_V_pos e2
  have ox : withoutReply ppref_V_pos x.val = x.val := by
    unfold withoutReply
    rw [← (of_decide_eq_true hx : x.val.y = ⟨0, ppref_V_pos⟩)]
  have oy : withoutReply ppref_V_pos y.val = y.val := by
    unfold withoutReply
    rw [← (of_decide_eq_true hy : y.val.y = ⟨0, ppref_V_pos⟩)]
  exact Subtype.ext (ox.symm.trans (w.trans oy))

/-- A request with the reply 1 (T tokens 0; «the next token after these»): for a control. -/
def replyOneF : ReqAt Inst.Model.ppref :=
  ⟨Inst.Model.Instance.nextOf (fun _ => ⟨0, ppref_V_pos⟩) ⟨1, by decide⟩, by decide, fun h => absurd
      h (by decide)⟩

end PV.OkOwn

#print axioms PV.OkOwn.ownS_apart
#print axioms PV.OkOwn.ownF_apart
