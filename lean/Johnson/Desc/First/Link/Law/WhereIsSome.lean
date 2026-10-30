-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/WhereIsSome.lean: WHEN THE RUNNING FRAME FINDS AN ORACLE MESSAGE
(`ReqFrame.whereIs`, OnBytes/Iop/Req.lean): on one frame. Theorems. No text already in the library turns.

  `idxOf_some`: a member of an array has a place in it, below its size.
  `whereIs_own`: a link is under way · i < f.own.size ⊢ (f.whereIs f.link i).isSome.
  `whereIs_kept`: **a link is under way · the frame's groups are `reqGroups` of its shape · it holds
    as many kept messages as the group's target has · born < f.link ≤ the number of links · message
    number i of link born has a life that reaches f.link ⊢ (f.whereIs born i).isSome** (by
    `born_at`, AliveAt.lean).
Limits. That a frame of a reached state is so is not said here. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.AliveAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes
open OnBytes.Params (ReqMessage ReqLink ReqShape)

theorem idxOf_some {α : Type} [BEq α] [LawfulBEq α] (xs : Array α) (x : α) (h : x ∈ xs.toList) :
    ∃ j, xs.idxOf? x = some j ∧ j < xs.size := by
  cases e : xs.idxOf? x with
  | none =>
    rw [Array.idxOf?_eq_none_iff] at e
    exact absurd (Array.mem_toList_iff.1 h) e
  | some j =>
    refine ⟨j, rfl, ?_⟩
    unfold Array.idxOf? at e
    obtain ⟨k, _, rfl⟩ := Option.map_eq_some_iff.1 e
    exact k.isLt

theorem whereIs_own (f : ReqFrame) (hn : f.next = .laterOrClose) {i : Nat}
    (hi : i < f.own.size) : (f.whereIs f.link i).isSome = true := by
  unfold ReqFrame.whereIs
  rw [hn]
  simp [hi]

theorem whereIs_kept (f : ReqFrame) (hn : f.next = .laterOrClose)
    (hg : f.groups = reqGroups f.shape)
    (hk : f.keptBefore.size = ((reqGroups f.shape).getD f.link {}).target.kept.size)
    {born i : Nat} {L : ReqLink} {m : ReqMessage} (hL : f.shape.link[born]? = some L)
    (hm : L.messages[i]? = some m) (hb : born < f.link) (hlife : f.link - born ≤ m.life)
    (hl : f.link ≤ f.shape.link.length) : (f.whereIs born i).isSome = true := by
  obtain ⟨h1, h2⟩ := born_at f.shape hL hm hb hlife hl
  obtain ⟨j, e, hj⟩ := idxOf_some _ _ h1
  unfold ReqFrame.whereIs
  rw [hn, hg, e]
  have hne : (born == f.link) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  have hj' : j < f.keptBefore.size := by omega
  simp [hne, hj']

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.idxOf_some
#print axioms VerifiableInference.Desc.LinkJoin.whereIs_own
#print axioms VerifiableInference.Desc.LinkJoin.whereIs_kept
