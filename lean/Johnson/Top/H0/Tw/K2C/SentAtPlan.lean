-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/SentAtPlan.lean: code switching: THE FIELD «sent» OF WHAT IS OWED ON THE
NUMBERS AT A SWITCH (LinkDebts, K2C/HandsLink.lean · SwitchDebts, K2C/HandsCore.lean) FROM ONE TEST
WITH CODE ON THE LIST OF ROUNDS AND TWO FACTS ON THE VERIFIER's STATE. NO SUB-PROTOCOL IMPORTS THIS
FILE. General in the numbers N. The test's definitions stand in a light file of their own
(K2C/SentFit.lean), so that they can be evaluated without these laws.
WHY. The field says: the tenants (tree, part) at which the book behind the switch has the sending's
messages, all but the fold's mask, are, as a set, N.sent m 0. Its left side reads the state in
front (how many trees the book has; the front's codes, target and further notices); its right side
is a number of the table of joints. Here the left side is carried to the list of rounds' own data.
  (sentFitB N m pIn codes sent  THE TEST, K2C/SentFit.lean: the program's layout of «sent» under
                                «codes» is there, and the tenants of all notices but the last, the
                                trees counted from N.treesAt pIn, are as a set N.sent m 0)
  sentFitB_some                 the test at a layout that is there
  others_of_front               the front that a switch takes off a state has one further notice
                                more than the link has own messages of moment 0 (the fold's mask)
  count_of_front · count_finish the number of the messages that join the group is the number of
                                the notices less one; at the finish the link's own are none
  sent_of_test                  THE RULE: the test accepts · bookAt N pIn s accepts · the front's
                                notices are «sent» · its codes are «codes» · lay is the layout at
                                the front · n is the number of the notices less one: the field
  sent_of_fence                 the same from the fence (Fence, K2C/SendsOn.lean) at a front of s
  linkDebts_of · switchDebts_of the two structures from the other five fields and the rule: so
                                the rule's end is the field to the letter
  sentFitOn_at · sentFitAll_at  the test at a list of switches (at all 25) accepts: it accepts at
                                each with the numbers that numsAt gives
                                (Johnson/Desc/ProofFile/Lot/K2OfPlan.lean)
LIMITS. THE TEST HAS BEEN EVALUATED AT NO LIST OF ROUNDS: whether it accepts at the release's own
parameters is not known here. The two facts on the state (the fence's first two clauses) are
premises: nobody shows them here, and they do not follow from the table's four fixed tests. That
the last notice is the fold's mask and the only one without an OOD sample is not said: the test
compares sets of tenants and asks nothing on samples. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.HandsCore
import Johnson.Top.H0.Tw.K2C.SendsOn
import Johnson.Top.H0.Tw.K2C.SentFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place)
open _root_.Tw.K2 (switchNotices firstFront)

theorem sentFitB_some (N : Numbers) (m : Nat) (pIn : Option Place) {codes : Codes}
    {sent : Array OracleNotice} {lay : TreeLay} (h : layTrees codes sent = some lay) :
    sentFitB N m pIn codes sent = sameMembers ((List.range (sent.size - 1)).map fun i =>
      (N.treesAt pIn + lay.tree.getD i 0, lay.part.getD i 0)) (N.sent m 0) := by
  unfold sentFitB
  rw [h]

/-- The further notices of a front: the link's own messages of moment 0, and the fold's mask. -/
theorem others_of_front {p : P2} {s : S} {x : _root_.Tw.K2.Front} (h : FrontOf p s x) :
    x.others.size = x.own.length + 1 := by
  rcases h with ⟨_, hx⟩ | ⟨_, a, G, _, _, rfl⟩ | ⟨_, a, G, _, _, rfl⟩
  · obtain ⟨L, Gq, S0, g, a⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 hx
    rw [a.out]
    simp [ReqFrame.notices]
  · simp [headFrontOf, ReqFrame.notices]
  · simp [finFrontOf]

/-- As many messages join the group as there are notices, less one. -/
theorem count_of_front {p : P2} {s : S} {x : _root_.Tw.K2.Front} (h : FrontOf p s x) :
    1 + x.T.kept.size + x.own.length = (switchNotices x.T x.others).size - 1 := by
  rw [notices_size, others_of_front h]
  omega

/-- At the finish the link's own messages are none. -/
theorem count_finish {p : P2} {s : S} {x : _root_.Tw.K2.Front} (hp : p.stands = .finish)
    (h : FrontOf p s x) : 1 + x.T.kept.size = (switchNotices x.T x.others).size - 1 := by
  have e : x.own.length = 0 := by
    rcases h with ⟨c, _⟩ | ⟨c, _⟩ | ⟨_, a, G, _, _, rfl⟩
    · rw [hp] at c; cases c
    · rw [hp] at c; cases c
    · rfl
  have k := count_of_front h
  omega

/-- **THE RULE.** s: the state whose book is counted. x: the front. -/
theorem sent_of_test {N : Numbers} {m : Nat} {pIn : Option Place} {codes : Codes}
    {sent : Array OracleNotice} (hT : sentFitB N m pIn codes sent = true) {s : S}
    (hb : bookAt N pIn s = true) {x : _root_.Tw.K2.Front}
    (hn : switchNotices x.T x.others = sent) (hc : x.st.codes = codes) {lay : TreeLay}
    (hl : layTrees x.st.codes (switchNotices x.T x.others) = some lay) {n : Nat}
    (hk : n = (switchNotices x.T x.others).size - 1) :
    sameMembers ((List.range n).map fun i =>
      (s.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0)) (N.sent m 0) = true := by
  have hs : s.book.trees.size = N.treesAt pIn := by
    unfold bookAt at hb
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    exact hb.1.1
  subst hn hc
  rw [sentFitB_some N m pIn hl] at hT
  rw [hk, hs]
  exact hT

/-- The rule from the fence, at a front of the state t; the book is counted at s. -/
theorem sent_of_fence {N : Numbers} {m : Nat} {pIn : Option Place} {codes : Codes}
    {sent : Array OracleNotice} (hT : sentFitB N m pIn codes sent = true) {s t : S}
    (hb : bookAt N pIn s = true) {p : P2} {n₀ : Nat} (hF : Fence p sent codes n₀ t)
    {x : _root_.Tw.K2.Front} (hx : FrontOf p t x) {lay : TreeLay}
    (hl : layTrees x.st.codes (switchNotices x.T x.others) = some lay) :
    sameMembers ((List.range (1 + x.T.kept.size + x.own.length)).map fun i =>
      (s.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0)) (N.sent m 0) = true :=
  sent_of_test hT hb (hF x hx).1 (hF x hx).2.1 hl (count_of_front hx)

/-- What is owed at a link's switch, from the other five fields and the rule. -/
theorem linkDebts_of {N : Numbers} {m : Nat} {pIn pOut : Option Place} {codes : Codes}
    {sent : Array OracleNotice} (hT : sentFitB N m pIn codes sent = true) {s : S}
    (hb : bookAt N pIn s = true) {p : P2} {n₀ : Nat} (hF : Fence p sent codes n₀ s)
    {x : _root_.Tw.K2.Front} (hx : FrontOf p s x) {lay : TreeLay}
    (hl : layTrees x.st.codes (switchNotices x.T x.others) = some lay) {d : Nat} {W : SwitchFrame}
    (keptPos : KeptPos x.T) (carried : N.rowsAt m .carried = (0, 1 + keptSamples x W))
    (position : N.rowsAt m .position = (1 + keptSamples x W, d * (1 + targetRows x.T + 2)))
    (trees : N.treesAt pOut = N.treesAt pIn + lay.shapes.size)
    (msgs : N.msgsAt pOut = N.msgsAt pIn + (switchNotices x.T x.others).size) :
    LinkDebts N m pIn pOut s d x W lay :=
  ⟨keptPos, carried, position, sent_of_fence hT hb hF hx hl, trees, msgs⟩

/-- What is owed at a switch of any sort, from the other five fields and the rule. t: the state
off which the front is taken (at the finish: behind the way in). -/
theorem switchDebts_of {N : Numbers} {m : Nat} {pIn pOut : Option Place} {codes : Codes}
    {sent : Array OracleNotice} (hT : sentFitB N m pIn codes sent = true) {s t : S}
    (hb : bookAt N pIn s = true) {p : P2} {n₀ : Nat} (hF : Fence p sent codes n₀ t)
    {x : _root_.Tw.K2.Front} (hx : FrontOf p t x) {lay : TreeLay}
    (hl : layTrees x.st.codes (switchNotices x.T x.others) = some lay) {d n : Nat}
    (hk : n = (switchNotices x.T x.others).size - 1) {W : SwitchFrame}
    (keptPos : KeptPos x.T) (carried : N.rowsAt m .carried = (0, 1 + keptSamples x W))
    (position : N.rowsAt m .position = (1 + keptSamples x W, d * (1 + targetRows x.T + 2)))
    (trees : N.treesAt pOut = N.treesAt pIn + lay.shapes.size)
    (msgs : N.msgsAt pOut = N.msgsAt pIn + (switchNotices x.T x.others).size) :
    SwitchDebts N m pIn pOut s.book.trees.size d n x W lay :=
  ⟨keptPos, carried, position, sent_of_test hT hb (hF x hx).1 (hF x hx).2.1 hl hk, trees, msgs⟩

/-! ## The test at all 25 places -/

theorem sentFitOn_at {spots : List (Nat × Option Nat × Nat)} {N : Numbers} {P : P1K2.Prep}
    {ps : List Place} (h : sentFitOn spots N P ps = true) {t : Nat × Option Nat × Nat}
    (ht : t ∈ spots) {n : P1K2.Nums} (hn : P1K2.numsAt P t.2.1 = some n) :
    sentFitB N t.1 ps[t.2.2]? n.codes n.sent = true := by
  have e := List.all_eq_true.1 h t ht
  rw [hn] at e
  exact e

theorem sentFitAll_at {N : Numbers} {P : P1K2.Prep} {ps : List Place}
    (h : sentFitAll N P ps = true) {t : Nat × Option Nat × Nat} (ht : t ∈ switchSpots)
    {n : P1K2.Nums} (hn : P1K2.numsAt P t.2.1 = some n) :
    sentFitB N t.1 ps[t.2.2]? n.codes n.sent = true :=
  sentFitOn_at h ht hn

theorem spot_link {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24) :
    (l, some l, 14 * l + 2) ∈ switchSpots := by
  unfold switchSpots
  refine List.mem_append_left _ (List.mem_map.2 ⟨l - 1, List.mem_range.2 (by omega), ?_⟩)
  have e : l - 1 + 1 = l := by omega
  rw [e]

theorem spot_head : (24, some 24, 339) ∈ switchSpots := by
  unfold switchSpots
  exact List.mem_append_right _ (List.mem_cons_self ..)

theorem spot_finish : (25, none, 353) ∈ switchSpots := by
  unfold switchSpots
  exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.sent_of_test
#print axioms VerifiableInference.Desc.First.K2.sent_of_fence
#print axioms VerifiableInference.Desc.First.K2.linkDebts_of
#print axioms VerifiableInference.Desc.First.K2.switchDebts_of
#print axioms VerifiableInference.Desc.First.K2.count_finish
#print axioms VerifiableInference.Desc.First.K2.sentFitAll_at
#print axioms VerifiableInference.Desc.First.K2.spot_link
