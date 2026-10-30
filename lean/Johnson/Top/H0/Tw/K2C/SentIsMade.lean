-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/SentIsMade.lean: the kind «the code switch»: THE SWITCH's HALF OF THE MAKING
OF THE PUBLIC ITEM «frame.sentIs»: behind a yes of the switch at a link m the four clauses that
the link's «opened» does not test itself hold of the chain's own state of the calls: checkSentB
(Johnson/Road/K4/Rec/MakerStatement.lean) says yes. NO BLOCK IMPORTS THIS FILE.
  born_size         in every group of a request's shape the switch's target has as many kept
                    shapes as the group has entries «born» (both are made of one list)
  cut_ids           a cut of the numbers of a sending: (sentIds n0 N).extract a (a + k) = n0 + a,
                    n0 + a + 1, … (k of them), where a + k ≤ N
  yes_link_checkSent   p.stands = .link · a yes at s · the frame's link number is m · the frame's
                       groups are the shape's (reqGroups): checkSentB (sentDataOf
                       s.check.frame.shape (fun _ => s.st.oracles.size) trees) m s'.check = true
THE LETTER base: the number of messages in front of the segment's first sending IS HERE the
statement's own number of messages in front of the switch: that it is the plan's number at that
place is the walk's, not said here.
LIMITS. Two premises on the record in front (link = m; groups = reqGroups shape): public; the
first follows from the seated block's yes (SitsLink.lean), the second is the walk's. (m is
not 0: the switch's own guard.) The head's link is opened by another text. No soundness is
claimed.
-/
import Johnson.Top.H0.Tw.K2C.LinkStays
import Johnson.Road.K4.Rec.MakerStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (sendByL8 firstFront switchNotices)
open OnBytes.Road.K4.Rec (checkSentB)
open VerifiableInference.Desc.First.FillSent (sentDataOf TreeLook)

theorem from_born_size (sh : Params.ReqShape) : ∀ (count l : Nat) (alive : List ReqAlive),
    ∀ G ∈ reqGroupsFrom sh count l alive, G.target.kept.size = G.born.size
  | 0, _, _, _, h => nomatch h
  | count + 1, l, alive, G, h => by
    rw [reqGroupsFrom] at h
    rcases List.mem_cons.1 h with rfl | h
    · simp [reqGroupAt]
    · exact from_born_size sh count (l + 1) _ G h

theorem born_size (sh : Params.ReqShape) {m : Nat} {G : ReqGroup}
    (h : (reqGroups sh)[m]? = some G) : G.target.kept.size = G.born.size := by
  rw [reqGroups_eq] at h
  refine from_born_size sh (sh.link.length + 1) 0 [] G ?_
  have := Array.mem_of_getElem? h
  simpa using this

theorem cut_ids (n0 N a k : Nat) (h : a + k ≤ N) :
    (sentIds n0 N).extract a (a + k) = (Array.range k).map (· + (n0 + a)) := by
  unfold sentIds
  apply Array.ext
  · simp
    omega
  · intro i h1 h2
    simp
    omega

theorem yes_link_checkSent {p : P2} {s : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {s' : S} (hp : p.stands = .link)
    (h : decideWith sendByL8 p s rs gs = .ok s') {m : Nat} (hm : s.check.frame.link = m)
    (hg : s.check.frame.groups = reqGroups s.check.frame.shape)
    (trees : Nat → List TreeLook) :
    checkSentB (sentDataOf s.check.frame.shape (fun _ => s.st.oracles.size) trees) m s'.check =
      true := by
  obtain ⟨e1, _, _, _⟩ := yes_link_next hp h
  obtain ⟨_, _, e4⟩ := yes_link_stays hp h
  obtain ⟨x, lay, hx, hown, _, _, _, k1, k2, _, _⟩ := yes_link_frame hp h
  obtain ⟨L, G, S0, g, a⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 hx
  have h0 : m ≠ 0 := hm ▸ a.later
  have hst : x.st.oracles.size = s.st.oracles.size := by
    rw [(firstFront_st hx).1]
    rfl
  have hG : (reqGroups s.check.frame.shape)[m]? = some G := by
    rw [← hg, ← hm]
    exact a.group
  have hT : x.T = G.target := by rw [a.out]
  have hb : x.T.kept.size = G.born.size := by rw [hT]; exact born_size _ hG
  have hGd : (reqGroups s.check.frame.shape).getD m {} = G := by
    rw [Array.getD_eq_getD_getElem?, hG]
    rfl
  have hN : (switchNotices x.T x.others).size = 1 + x.T.kept.size + x.others.size := by
    simp [switchNotices]
    omega
  have ho : x.others.size = x.own.length + 1 := by
    rw [a.out]
    simp [ReqFrame.notices]
  have hlen : x.own.length = (((s.check.frame.shape.link[m]?.map (·.messages)).getD []).filter
      fun y => y.moment == 0).length := by
    rw [hown, ← hm]
    rfl
  unfold checkSentB sentDataOf
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨e1, ?_⟩, ?_⟩, ?_⟩
  · rw [e4, hg]
  · rw [k2, hst, if_neg (by simpa using h0), hGd, ← hb, ← hlen]
    have c1 := cut_ids s.st.oracles.size (switchNotices x.T x.others).size (1 + x.T.kept.size)
      (x.others.size) (by omega)
    have e : 1 + x.T.kept.size + x.others.size = (switchNotices x.T x.others).size := hN.symm
    rw [e] at c1
    rw [c1]
    apply Array.ext
    · simp
      omega
    · intro i h1 h2
      simp
  · rw [k1, hst, if_neg (by simpa using h0), hGd, ← hb]
    exact cut_ids _ _ 1 x.T.kept.size (by omega)

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.born_size
#print axioms VerifiableInference.Desc.First.K2.cut_ids
#print axioms VerifiableInference.Desc.First.K2.yes_link_checkSent
