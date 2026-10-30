-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/FirstCut.lean: the routine of a proof file's first chain, cut by the groups of
its links: if each piece goes from nothing open to nothing open (`Goes`,
Johnson/AtFull/Made/Goes.lean), so does the whole. General laws: no written value, no evaluation. A
law file; no running text imports it.

The frame (`reqPlanFrom`, OnBytes/Params/DeriveReq.lean) is a recursion on the groups. By the law
`reqPlanFrom_cons` (OnBytes/Tie/Pv/Req/Frame.lean) a group with a link is: the reply, the switch,
the link's sub-proof with its moments, the batching, the fold, and then the groups after; the group
without a link is: the reply, the switch, the last proximity test.

Definitions.
  `segOf`, `lastOf`: these two pieces, without what follows. `tailOf`: what follows the frame.
  `beforeAt z G l`: the group that was closed last before group number l of the list G.
  `segAt z sub G l`, `lastAt z G l`: the pieces at group number l of G.
Statements.
  `frP_segAt`, `frP_lastAt`, `frP_tailOf`: the pieces read no round, if the sub-proofs' routines
    read none.
  `goes_frame`: if `segAt` goes at every link's number and `lastAt` at the number behind, the frame
    goes.
  `goes_body`: with `tailOf` too, the whole routine (`bodyOf`, FirstReads.lean) goes.

Limits. It shows of no piece that it goes. Nothing says which rounds are added. Nothing on
soundness.

-/
import Johnson.AtFull.Made.Goes
import Johnson.AtFull.Made.FrameMore
import Johnson.AtFull.Made.FirstReads
import OnBytes.Tie.Pv.Req.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open OnBytes.Tie.Pv.Req (replyOf switchOf sendOf laterOf closedOf membersOf setScope battOf
  reqPlanFrom_cons)
open VerifiableInference.Desc.LinkJoin

/-- A group with a link, without the groups after. -/
def segOf (z : ProofSized) (sub : Subproofs) (l : Nat) (g : ReqGroup) (gs : List ReqGroup)
    (links : List ReqLink) (open_ : List Nat) (before : GroupSize) : Planning Unit :=
  replyOf links >>= fun _ => switchOf z l g links before >>= fun carried =>
    sub.plan l 0 >>= fun _ => setScope >>= fun _ => laterOf z sub l links >>= fun more =>
      planBat [closedOf z g gs] (open_.headD 0 + carried +
        sumT ((membersOf z l g links).map (·.shape.answers)) + more) >>= fun _ =>
      planFold (closedOf z g gs) 0

/-- The group without a link. -/
def lastOf (z : ProofSized) (l : Nat) (g : ReqGroup) (links : List ReqLink)
    (before : GroupSize) : Planning Unit :=
  replyOf links >>= fun _ => switchOf z l g links before >>= fun carried =>
    planIopp z.last.stages (carried + sumT ((membersOf z l g links).map (·.shape.answers))) 0
      z.request.choice.masksRide

/-- What follows the frame. -/
def tailOf (z : ProofSized) (sub : Subproofs) : Planning Unit :=
  sub.afterLinks >>= fun _ => setScope >>= fun _ =>
    battOf z sub >>= fun _ => linPlanFirst z.codes z.batch >>= fun _ => planSeal

/-- The group that was closed last before group number l. -/
def beforeAt (z : ProofSized) (G : List ReqGroup) : Nat → GroupSize
  | 0 => z.link.group
  | l + 1 =>
    match G.drop l with
    | g :: gs => closedOf z g gs
    | [] => z.link.group

/-- The piece at group number l, which has a link. -/
def segAt (z : ProofSized) (sub : Subproofs) (G : List ReqGroup) (l : Nat) : Planning Unit :=
  match G.drop l with
  | g :: gs =>
    segOf z sub l g gs (z.request.link.drop l) (sub.openRows.drop l) (beforeAt z G l)
  | [] => pure ()

/-- The piece at group number l, which has no link. -/
def lastAt (z : ProofSized) (G : List ReqGroup) (l : Nat) : Planning Unit :=
  match G.drop l with
  | g :: _ => lastOf z l g (z.request.link.drop l) (beforeAt z G l)
  | [] => pure ()

/-! ## The pieces read no round -/

theorem frP_replyOf (links : List ReqLink) : FrP (replyOf links) := by
  unfold replyOf
  frp

theorem frP_switchOf (z : ProofSized) (l : Nat) (g : ReqGroup) (links : List ReqLink)
    (before : GroupSize) : FrP (switchOf z l g links before) := by
  unfold switchOf sendOf
  frp

theorem frP_setScope : FrP setScope :=
  frP_modify _ (fun _ => rfl) (fun _ _ => rfl)

theorem frP_segOf (z : ProofSized) {sub : Subproofs} {l : Nat} (h : ∀ m, FrP (sub.plan l m))
    (g : ReqGroup) (gs : List ReqGroup) (links : List ReqLink) (open_ : List Nat)
    (before : GroupSize) : FrP (segOf z sub l g gs links open_ before) := by
  unfold segOf
  refine frP_bind (frP_replyOf _) fun _ => frP_bind (frP_switchOf _ _ _ _ _) fun _ =>
    frP_bind (h 0) fun _ => frP_bind frP_setScope fun _ =>
      frP_bind (frP_reqMoments z h _ _ _) fun _ => frP_bind (frP_planBat _ _) fun _ =>
        frP_planFold _ _

theorem frP_segAt (z : ProofSized) {sub : Subproofs} (h : ∀ l m, FrP (sub.plan l m))
    (G : List ReqGroup) (l : Nat) : FrP (segAt z sub G l) := by
  unfold segAt
  cases G.drop l with
  | nil => exact frP_pure _
  | cons g gs => exact frP_segOf z (h l) _ _ _ _ _

theorem frP_lastAt (z : ProofSized) (G : List ReqGroup) (l : Nat) : FrP (lastAt z G l) := by
  unfold lastAt
  cases G.drop l with
  | nil => exact frP_pure _
  | cons g gs =>
    exact frP_bind (frP_replyOf _) fun _ => frP_bind (frP_switchOf _ _ _ _ _) fun _ =>
      frP_planIopp _ _ _ _

theorem frP_tailOf (z : ProofSized) {sub : Subproofs} (h : FrP sub.afterLinks) :
    FrP (tailOf z sub) := by
  unfold tailOf
  refine frP_bind h fun _ => frP_bind frP_setScope fun _ => frP_bind ?_ fun _ =>
    frP_bind (frP_linPlanFirst _ _) fun _ => frP_planSeal
  unfold battOf
  exact frP_ite (frP_planBatt _ _) (frP_pure _)

/-! ## The pieces, joined -/

theorem drop_succ_of {α : Type} {G : List α} {l : Nat} {g : α} {gs : List α}
    (h : G.drop l = g :: gs) : G.drop (l + 1) = gs := by
  have e : G.drop (l + 1) = (G.drop l).drop 1 := by rw [List.drop_drop, Nat.add_comm]
  rw [e, h]
  rfl

/-- **The frame goes, if its pieces go.** -/
theorem goes_frame {z : ProofSized} {sub : Subproofs} {G : List ReqGroup}
    (hs : ∀ l, l < z.request.link.length → Goes z.set (segAt z sub G l) ())
    (hl : Goes z.set (lastAt z G z.request.link.length) ()) :
    ∀ k l, l + k = z.request.link.length →
      Goes z.set (reqPlanFrom z sub l (G.drop l) (z.request.link.drop l) (sub.openRows.drop l)
        (beforeAt z G l)) ()
  | 0, l, e => by
    have el : l = z.request.link.length := by omega
    have hl' := hl
    rw [← el] at hl'
    unfold lastAt at hl'
    cases hG : G.drop l with
    | nil =>
      unfold reqPlanFrom
      exact Goes.pure _ _
    | cons g gs =>
      rw [hG] at hl'
      have hd : z.request.link.drop l = [] := by
        rw [el]
        exact List.drop_length
      rw [reqPlanFrom_cons]
      rw [hd] at hl' ⊢
      exact hl'
  | k + 1, l, e => by
    have hlt : l < z.request.link.length := by omega
    have h1 := hs l hlt
    have ih := goes_frame hs hl k (l + 1) (by omega)
    unfold segAt at h1
    cases hG : G.drop l with
    | nil =>
      unfold reqPlanFrom
      exact Goes.pure _ _
    | cons g gs =>
      rw [hG] at h1
      have hh : (z.request.link.drop l).head?.isSome = true := by
        rw [List.drop_eq_getElem_cons hlt]
        rfl
      have d1 : (z.request.link.drop l).drop 1 = z.request.link.drop (l + 1) := by
        rw [List.drop_drop, Nat.add_comm]
      have d2 : (sub.openRows.drop l).drop 1 = sub.openRows.drop (l + 1) := by
        rw [List.drop_drop, Nat.add_comm]
      have d3 : beforeAt z G (l + 1) = closedOf z g gs := by
        show (match G.drop l with
          | g :: gs => closedOf z g gs
          | [] => z.link.group) = _
        rw [hG]
      rw [drop_succ_of hG, d3] at ih
      have eq : reqPlanFrom z sub l (g :: gs) (z.request.link.drop l) (sub.openRows.drop l)
          (beforeAt z G l) =
          (segOf z sub l g gs (z.request.link.drop l) (sub.openRows.drop l) (beforeAt z G l) >>=
            fun _ => reqPlanFrom z sub (l + 1) gs (z.request.link.drop (l + 1))
              (sub.openRows.drop (l + 1)) (closedOf z g gs)) := by
        rw [reqPlanFrom_cons]
        simp only [hh, if_true, d1, d2, segOf, bind_assoc]
      rw [eq]
      exact h1.bind ih

theorem bodyOf_eq (z : ProofSized) (sub : Subproofs) :
    bodyOf z sub = reqPlan z sub >>= fun _ => tailOf z sub := by
  unfold bodyOf tailOf battOf
  by_cases h : 1 < sub.pendingRows <;> simp only [h, if_true, if_false, pure_bind]

/-- **The whole routine goes, if its pieces go.** -/
theorem goes_body {z : ProofSized} {sub : Subproofs}
    (hs : ∀ l, l < z.request.link.length →
      Goes z.set (segAt z sub (reqGroups z.request).toList l) ())
    (hl : Goes z.set (lastAt z (reqGroups z.request).toList z.request.link.length) ())
    (ht : Goes z.set (tailOf z sub) ()) : Goes z.set (bodyOf z sub) () := by
  rw [bodyOf_eq]
  refine Goes.bind (a := ()) ?_ ht
  exact goes_frame hs hl z.request.link.length 0 (by omega)

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.frP_segOf
#print axioms Johnson.AtFull.Made.bodyOf_eq
#print axioms Johnson.AtFull.Made.frP_segAt
#print axioms Johnson.AtFull.Made.frP_lastAt
#print axioms Johnson.AtFull.Made.frP_tailOf
#print axioms Johnson.AtFull.Made.goes_frame
#print axioms Johnson.AtFull.Made.goes_body
