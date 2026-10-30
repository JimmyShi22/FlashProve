-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/FitCubes.lean: the cap FrameCap of FitPlans.lean (in this folder) on the frame of
a chain of links holds, where the request's shape has passed the program's own test, the codes'
messages are short, and groups, links and riders meet the premises of TreesReq.lean (the links'
oracle messages in the class of leaves 0 and under one code; the riders in one class, without main
rows).

FrameCap asks two things of each prover's message of the frame: the cube of every oracle message
with a sample has at most 2 ^ 32 variables; the messages lie in at most two trees. A cube's
variables are those of the rows and those of a row's entries, and one more where a message has main
rows and mask rows (Send.cube, OnBytes/Iop/Send.lean). The
program tests of every oracle message of a link, and of what rides at the start, that it has at most
2 ^ 20 rows (reqMessageOk, reqShapeOk, OnBytes/Iop/Req.lean). What a group keeps was a link's
message, and the carrying message has two rows (groups_all, TreesReq.lean in this folder). The trees
are the matter of TreesReq.lean.

Main names:
  CodesShort codes: under every number, in both lists, logEll ≤ 64: a message of at most 2 ^ 64
    entries.
  ceilLog2_le; cubeBits_le: few rows and CodesShort give a cube of at most 2 ^ 32 variables.
  RowsFew n: at most 2 ^ 128 main rows and mask rows.
  reqShapeOk_rows: the links' messages and what rides at the start have few rows, from the test.
  rows_members: so have the members of a group's first message that have a sample.
  TreesFrame, treesFrame_from: the half of FrameCap that is on trees, from TreesReq.lean's caps.
  frameCap_from, frameCap_of: FrameCap.
Limits. CodesShort and the premises on trees are premises here. The bounds are far from sharp.
The program does not import this file.


-/
import OnBytes.Params.Fit.FitPlans
import OnBytes.Params.Fit.TreesReq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

open OnBytes
open OnBytes.Plan (membersOf sentAtMoment)

/-! ## A cube's variables -/

/-- Under every number, in both lists: the logarithm of the message's length is at most 64. Beyond a
list's end stands the default code, whose message is empty. -/
def CodesShort (codes : Codes) : Prop :=
  ∀ i, (codes.base.getD i default).logEll ≤ 64 ∧ (codes.mask.getD i default).logEll ≤ 64

theorem ceilLog2_le {n a : Nat} (h : n ≤ 2 ^ a) : ceilLog2 n ≤ a := by
  unfold ceilLog2
  split
  · exact Nat.zero_le _
  · rename_i h1
    have h2 : n - 1 ≠ 0 := by omega
    have h3 : n - 1 < 2 ^ a := by omega
    have h4 := (Nat.log2_lt h2).2 h3
    omega

/-- At most 2 ^ 128 main rows and at most 2 ^ 128 mask rows. -/
def RowsFew (n : OracleNotice) : Prop :=
  n.shape.mainRows ≤ 2 ^ 128 ∧ n.shape.maskRows ≤ 2 ^ 128

theorem cubeBits_le {codes : Codes} {o : OracleShape} (hc : CodesShort codes)
    (h1 : o.mainRows ≤ 2 ^ 128) (h2 : o.maskRows ≤ 2 ^ 128) :
    cubeBitsOf codes o ≤ 2 ^ 32 := by
  have a1 := ceilLog2_le h1
  have a2 := ceilLog2_le h2
  have b1 := (hc o.code).1
  have b2 := (hc o.maskCode).2
  unfold cubeBitsOf Send.cube
  dsimp only
  repeat' split
  all_goals omega

/-! ## The rows, from the program's own test -/

theorem reqMessageOk_rows {m : ReqMessage} (h : reqMessageOk m = true) :
    RowsFew ⟨m.shape, m.leafClass⟩ := by
  unfold reqMessageOk at h
  simp only [Bool.and_eq_true] at h
  have r1 : m.shape.mainRows ≤ 2 ^ 20 := of_decide_eq_true h.1.1.1.1.2
  have r2 : m.shape.maskRows ≤ 2 ^ 20 := of_decide_eq_true h.1.1.1.2
  exact ⟨r1.trans (by omega), r2.trans (by omega)⟩

/-- The links' oracle messages and what rides at the start have few rows. -/
theorem reqShapeOk_rows {s : ReqShape} (h : reqShapeOk s = true) :
    (∀ L ∈ s.link, ∀ m ∈ L.messages, RowsFew ⟨m.shape, m.leafClass⟩) ∧
      ∀ n ∈ s.atStart, RowsFew n := by
  unfold reqShapeOk at h
  simp only [Bool.and_eq_true] at h
  refine ⟨fun L hL m hm => ?_, fun n hn => ?_⟩
  · obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hL
    have t := List.all_eq_true.1 h.1.1.1.1.1.1.2 (L, i) (List.mem_zipIdx_iff_getElem?.2 hi)
    rw [Bool.and_eq_true] at t
    have t1 : reqLinkOk L = true := t.1
    unfold reqLinkOk at t1
    rw [Bool.and_eq_true] at t1
    exact reqMessageOk_rows (List.all_eq_true.1 t1.2 m hm)
  · have t := List.all_eq_true.1 h.1.1.1.1.2 n hn
    simp only [Bool.and_eq_true, beq_iff_eq] at t
    have r1 : n.shape.mainRows = 0 := t.1.1.1.1.1
    have r2 : n.shape.maskRows ≤ 2 ^ 20 := of_decide_eq_true t.1.1.1.2
    exact ⟨by rw [r1]; exact Nat.zero_le _, r2.trans (by omega)⟩

/-- The members of a group's first message that have a sample have few rows. The fold's fresh mask
has no sample. -/
theorem rows_members {z : ProofSized} {g : ReqGroup}
    (hg : RowsFew ⟨g.target.shape, g.target.leafClass⟩ ∧
      ∀ k ∈ keptOf g, RowsFew ⟨k.shape, k.leafClass⟩)
    {msgs : List ReqMessage} (hm : ∀ m ∈ msgs, RowsFew ⟨m.shape, m.leafClass⟩) (l : Nat) :
    ∀ n ∈ membersOf z l g msgs, 0 < n.shape.answers → RowsFew n := by
  intro n hn ha
  unfold membersOf at hn
  rcases List.mem_append.1 hn with hn | hn
  · rcases List.mem_append.1 hn with hn | hn
    · rcases List.mem_append.1 hn with hn | hn
      · split at hn
        · rw [List.mem_singleton.1 hn]
          exact hg.1
        · exact absurd hn List.not_mem_nil
      · obtain ⟨k, hk, e⟩ := List.mem_map.1 hn
        rw [← e]
        exact hg.2 k hk
    · obtain ⟨m, hmm, e⟩ := List.mem_map.1 hn
      rw [← e]
      exact hm m (List.mem_filter.1 hmm).1
  · rw [List.mem_singleton.1 hn] at ha
    exact absurd ha (Nat.lt_irrefl 0)

/-! ## The frame's cap -/

/-- The messages of the first of some links are messages of one of them. -/
theorem head_messages {links : List ReqLink} {Pr : ReqMessage → Prop}
    (h : ∀ L ∈ links, ∀ m ∈ L.messages, Pr m) :
    ∀ m ∈ (links.head?.map (·.messages)).getD [], Pr m := by
  cases links with
  | nil => exact fun _ hm => absurd hm List.not_mem_nil
  | cons L t => exact fun m hm => h L List.mem_cons_self m hm

/-- The half of FrameCap that is on trees. It goes through groups and links as FrameCap does. -/
def TreesFrame (z : ProofSized) : Nat → List ReqGroup → List ReqLink → Prop
  | _, [], _ => True
  | l, g :: gs, links =>
    TreesCap z.codes (sentOf z l g ((links.head?.map (·.messages)).getD [])) ∧
      (∀ mo, TreesCap z.codes (sentAtMoment ((links.head?.map (·.messages)).getD []) mo)) ∧
      TreesFrame z (l + 1) gs (links.drop 1)

/-- It holds where groups, links and riders meet the premises of TreesReq.lean. -/
theorem treesFrame_from {z : ProofSized} {c : Nat} (hR : TreeRiderCap z.request.atStart) :
    ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink), (∀ g ∈ gs, TreeGroupCap c g) →
      (∀ L ∈ links, TreeLinkCap c L) → TreesFrame z l gs links
  | [], _, _, _, _ => by
    unfold TreesFrame
    trivial
  | g :: gs, l, links, hG, hL => by
    unfold TreesFrame
    have hm := head_messages (Pr := fun m => TreeNoticeCap c ⟨m.shape, m.leafClass⟩) hL
    refine ⟨?_, fun mo => treesCap_moment z.codes hm mo,
      treesFrame_from hR gs (l + 1) (links.drop 1)
        (fun g' hg' => hG g' (List.mem_cons_of_mem _ hg'))
        fun L hL' => hL L (List.mem_of_mem_drop hL')⟩
    unfold sentOf
    split
    · exact treesCap_notices z.codes
        (treeNoticeCap_members (hG g List.mem_cons_self) hm l
          ⟨z.request.code, z.request.maskCode, g.k, g.h⟩) hR
    · have q := treesCap_notices z.codes
        (treeNoticeCap_members (hG g List.mem_cons_self) hm l
          ⟨z.request.code, z.request.maskCode, g.k, g.h⟩) treeRiderCap_nil
      rw [List.append_nil] at q
      exact q

/-- FrameCap from group number l on: from few rows, and from its half on trees. -/
theorem frameCap_from {z : ProofSized} (hc : CodesShort z.codes)
    (hs : ∀ n ∈ z.request.atStart, RowsFew n) :
    ∀ (gs : List ReqGroup) (l : Nat) (links : List ReqLink),
      (∀ g ∈ gs, RowsFew ⟨g.target.shape, g.target.leafClass⟩ ∧
        ∀ k ∈ keptOf g, RowsFew ⟨k.shape, k.leafClass⟩) →
      (∀ L ∈ links, ∀ m ∈ L.messages, RowsFew ⟨m.shape, m.leafClass⟩) →
      TreesFrame z l gs links → FrameCap z l gs links
  | [], _, _, _, _, _ => by
    unfold FrameCap
    trivial
  | g :: gs, l, links, hG, hL, hF => by
    unfold TreesFrame at hF
    unfold FrameCap
    have hm := head_messages (Pr := fun m => RowsFew ⟨m.shape, m.leafClass⟩) hL
    refine ⟨⟨fun n hn ha => ?_, hF.1⟩, fun mo => ⟨fun n hn _ => ?_, hF.2.1 mo⟩,
      frameCap_from hc hs gs (l + 1) (links.drop 1)
        (fun g' hg' => hG g' (List.mem_cons_of_mem _ hg'))
        (fun L hL' => hL L (List.mem_of_mem_drop hL')) hF.2.2⟩
    · have r : RowsFew n := by
        unfold sentOf at hn
        split at hn
        · rcases List.mem_append.1 hn with hn | hn
          · exact rows_members (hG g List.mem_cons_self) hm l n hn ha
          · exact hs n hn
        · exact rows_members (hG g List.mem_cons_self) hm l n hn ha
      exact cubeBits_le hc r.1 r.2
    · unfold sentAtMoment at hn
      obtain ⟨m, hmm, e⟩ := List.mem_map.1 hn
      rw [← e]
      have r := hm m (List.mem_filter.1 hmm).1
      exact cubeBits_le hc r.1 r.2

/-- **FrameCap of the whole frame.** -/
theorem frameCap_of {z : ProofSized} (hok : reqShapeOk z.request = true)
    (hc : CodesShort z.codes) {c : Nat}
    (hG : ∀ g ∈ (reqGroups z.request).toList, TreeGroupCap c g)
    (hL : ∀ L ∈ z.request.link, TreeLinkCap c L) (hR : TreeRiderCap z.request.atStart) :
    FrameCap z 0 (reqGroups z.request).toList z.request.link :=
  frameCap_from hc (reqShapeOk_rows hok).2 _ 0 _
    (groups_all RowsFew (reqShapeOk_rows hok).1
      ⟨(by omega : (2 : Nat) ≤ 2 ^ 128), Nat.zero_le _⟩ ⟨Nat.zero_le _, Nat.zero_le _⟩)
    (reqShapeOk_rows hok).1 (treesFrame_from hR _ 0 _ hG hL)

end OnBytes.Params
