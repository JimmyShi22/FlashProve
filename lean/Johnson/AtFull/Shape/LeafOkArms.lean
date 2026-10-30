-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/LeafOkArms.lean: THE CODE SWITCH AT THE OUTPUT HEAD's PLACE (339) AND BEHIND
THE LAST SEGMENT (353) OF THE PROOF FILE's OWN FIRST CHAIN: AT EVERY STATE THAT IS REACHED THERE THE
TEST "WHAT SHARES A LEAF" (leafOk, Johnson/Top/H0/Tw/K2C/Asks.lean) ACCEPTS AT EACH TREE THAT THE
SWITCH OPENS, at the statement that the switch's front hands on. The counterpart of
LeafOkLinks.lean, which has the 23 links. At the proof file's seat, in the goals' scope, at an
opening; whoever plays.

How. AT 339: the sub-protocol at 338 pushes a group and leaves the messages (h1_front,
Johnson/IMR/HeadFront.lean; firstFront_st), and the head's own frame has the carried rows of the cut
338 (front_nums_head): so the law at the cut 338 = 14 (23 + 1) + 2 serves (leafOk_at_switch,
LeafOkReached.lean). AT 353: as at a link's switch (MarksReached.lean), with the last segment's
laws: the layout's members are those of the group 24 at the cut 347 (tail_rows_head,
Johnson/IMR/FinKept.lean), and once a member, always a member; they are numbered from the number of
messages at 339 on (members_behind_cleared, Johnson/Desc/K2/Honest/Returns/HeadSegment.lean); there
are 25 groups (count_fin, Johnson/IMR/FinCount.lean); the statement is shut below 24 since 339; the
fresh mask's message counts no answer (closed_behind_cleared, Returns/ClosedArms.lean). The quiet
front pushes a group and leaves the messages (finishFrontQ_st), and lays the walk's carried rows
into its own frame (finishFrontQ_rows, Returns/ClosedArms.lean).

  head_msgs: the states at the cuts 338 and 339 of one fold have the same messages.
  **head_leafOk**: s reached at 339.
  lists_at_finish, fresh_blank_fin, leafOk_at_finish: at the cut 353.
  **fin_leafOk**: s reached at 353, t behind the quiet front.

Limits. At 339 "here" and "group", at 353 the quiet front's yes and "here" are premises, as in
head_own_reached and fin_own_reached (Returns/OwnReached.lean, Returns/OwnFinish.lean). "Reached" is
over the list of the wrapped sub-protocols. At the statement in front of the switch's sending, not
behind it. It stands over another house's files (these two and what they import). Of a reached
state: that anything is reached is not said. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.LeafOkReached
import Johnson.Desc.K2.Honest.Returns.OwnFinish
import Johnson.IMR.FinKept
import Johnson.IMR.FinCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription foldBlocks)
open VerifiableInference.Desc.First (S HeadOwn FinOwn)
open VerifiableInference.Desc.First.K2 (headFrontOf finFrontOf finishFrontQ finishFrontQ_st
  firstFront_st frontAt_of)
open VerifiableInference.Desc.LinkJoin (closeFrame_reads)
open VerifiableInference.Desc.K2.Honest.Returns (inFront treesOf leafOk_same head_own_reached
  fin_own_reached members_behind_cleared closed_behind_cleared finishFrontQ_rows mem_shift placeQ)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Meaning.K2 (frontOf front_len fold_back fold_next fold_cut_le h1_front front_nums_head
  tail_rows_head count_fin)
open _root_.Tw.K2 (leafOk Par9 Sent Col)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-! ## 1 The output head's place -/

/-- The sub-protocol at 338 leaves the messages. -/
theorem head_msgs (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R Rm R₀ : List Fmt.RoundView} {C Cm C₀ : List VerifiableInference.Desc.OpenedColumn} {tm t₀ : S}
    (fm : foldBlocks 0 (c.blocksInOrder.take 338) (ProofFile.startS Z p) R C = .ok (tm, Rm, Cm))
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    t₀.st.oracles = tm.st.oracles := by
  obtain ⟨Lk, b0, eL, e0, hj, -⟩ := IM.k7_sits hS hR O
  have i0 : c.blocksInOrder[338]? = some b0 := by
    have k := IM.hear_at_flat eL e0
    rwa [(IM.flatIx_scope hS hR O (by decide : 24 ≤ 24) 0).trans (by omega : _ = 338)] at k
  obtain ⟨rs0, gs0, d0⟩ := fold_next i0 fm f₀
  have d0' := (IM.k7_sits_yes hS hR O hj d0).1
  obtain ⟨x, a, hx, -, -, es, -⟩ := h1_front d0'
  rw [es, (firstFront_st hx).1]
  rfl

/-- **"WHAT SHARES A LEAF" AT EACH TREE THAT THE OUTPUT HEAD's SWITCH OPENS.** -/
theorem head_leafOk (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) {a : HeadOwn}
    (here : s.here = .head a) {G : ReqGroup}
    (group : s.check.frame.groups[s.check.frame.link]? = some G) (T : SwitchTarget) (P9 : Par9)
    (y : Sent) (rL : Fmt.RoundView) (cols : List Col) :
    ∀ t ∈ treesOf (inFront P9 (headFrontOf s a T) s.book y rL cols), ∀ tree,
      (inFront P9 (headFrontOf s a T) s.book y rL cols).book.trees[t]? = some tree →
      leafOk (inFront P9 (headFrontOf s a T) s.book y rL cols).st tree = true := by
  intro t ht tree htree
  have hp := head_own_reached hS hR O hr here group T P9 y rL cols t ht tree htree
  obtain ⟨-, rs, cl, f⟩ := (reach_raw hr).fold
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 338) f
  have hrows : a.fr.rows = tm.check.frame.rows :=
    (front_nums_head hS hR O fm f (q := placeQ .head) rfl
      (frontAt_of (Or.inr (Or.inl ⟨rfl, a, G, here, group, rfl⟩)))).2.2.1
  have hp' : ∀ q ∈ tree.parts.toList, q ∈ (singleRowsOracles tm.check.frame.rows).toList := by
    intro q hq
    rw [← hrows]
    exact hp q hq
  have e : leafOk (inFront P9 (headFrontOf s a T) s.book y rL cols).st tree = leafOk tm.st tree :=
    leafOk_same fun q _ => by
      show s.st.oracles[q]? = tm.st.oracles[q]?
      rw [head_msgs hS hR O fm f]
  rw [e]
  exact leafOk_at_switch hS hR O (m := 23) (by omega) fm tree hp'

/-! ## 2 Behind the last segment -/

/-- **At the cut 353 each message of the carried rows' layout has the list [24].** In the proof f₀,
f₃, f₅ are the same fold's returns at the cuts 339, 342, 344 (members_behind_cleared's own); N is
the number of messages at 339, which lies behind the closing of link 23 (at 334). -/
theorem lists_at_finish (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₂ : List Fmt.RoundView} {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ : S}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    ∀ o ∈ t₂.check.frame.rows.layout.members, listAt t₂.st o = some [24] := by
  have hlen := front_len hS hR O
  have hk₂ : 353 ≤ (frontOf c).length := by omega
  obtain ⟨u, Ru, Cu, fu⟩ := fold_cut_le (by omega : 347 ≤ 353) f₂
  obtain ⟨L, G, -, -, -, hG, em, -⟩ := tail_rows_head hS hR O fu f₂
  obtain ⟨t₀, t₃, t₅, R₀, R₃, R₅, C₀, C₃, C₅, f₀, f₃, f₅, er⟩ :=
    members_behind_cleared hS hR O f₂
  have hT := tidy_fold O hk₂ f₂
  have hn : t₂.st.groups.size = 24 + 1 := count_fin hS hR O f₂
  have hS₀ := statement_shut_below hS hR O (m := 24) (by omega) (by omega) (by omega) f₀
  have hS₂ : Shut 24 t₀.st.oracles.size t₂.st :=
    plain_folds (plain_shut 24 _) O (by omega) hk₂ f₀ f₂ hS₀
  have b₃ : t₀.st.oracles.size ≤ t₃.st.oracles.size :=
    plain_folds (plain_big _) O (by omega) (by omega) f₀ f₃ (Nat.le_refl _)
  have b₅ : t₀.st.oracles.size ≤ t₅.st.oracles.size :=
    plain_folds (plain_big _) O (by omega) (by omega) f₀ f₅ (Nat.le_refl _)
  intro o ho
  have hN : t₀.st.oracles.size ≤ o := by
    have h := Array.mem_toList_iff.2 ho
    rw [er, Array.toList_append, List.mem_append, Array.toList_append, List.mem_append,
      Array.toList_append, List.mem_append, Array.toList_append, List.mem_append, mem_shift,
      mem_shift, mem_shift, mem_shift] at h
    have h1 : o ∈ (#[t₀.st.oracles.size] : Array Nat).toList → o = t₀.st.oracles.size := by
      intro k
      simpa using k
    rcases h with (h | h) | ((h | h) | h)
    · exact Nat.le_of_eq (h1 h).symm
    · omega
    · omega
    · omega
    · omega
  have hu : MemberOf 24 o u.st := by
    refine ⟨G.members, ?_, em ▸ ho⟩
    unfold membersAt
    rw [hG]
    rfl
  obtain ⟨M, hM, hoM⟩ := plain_folds (plain_member 24 o) O (by omega) hk₂ fu f₂ hu
  exact list_one hT hS₂ hn hM hoM hN

/-- The carried rows' fresh mask's message counts no answer. -/
theorem fresh_blank_fin (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₂ : List Fmt.RoundView} {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ : S}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    Blank t₂.check.frame.rows.fresh t₂.st := by
  obtain ⟨owed, f, T₀, es, rs, x, hx, hf, hg⟩ := closed_behind_cleared hS hR O f₂
  obtain ⟨id, e1, hb⟩ := closeFrame_blank hx
  obtain ⟨_, id', -, -, e2, e3⟩ := closeFrame_reads hx
  obtain rfl : id = id' := Option.some.inj (e1.symm.trans e2)
  rw [hf, e3]
  exact blank_grows hg hb

/-- The test accepts at every tree whose parts are among the carried rows' messages. -/
theorem leafOk_at_finish (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₂ : List Fmt.RoundView} {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ : S}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) (tree : Tree)
    (hp : ∀ q ∈ tree.parts.toList, q ∈ (singleRowsOracles t₂.check.frame.rows).toList) :
    leafOk t₂.st tree = true :=
  leafOk_of_rows (lists_at_finish hS hR O f₂) (fresh_blank_fin hS hR O f₂) tree hp

/-- **"WHAT SHARES A LEAF" AT EACH TREE THAT THE SWITCH BEHIND THE LAST SEGMENT OPENS.** t: the
state behind the quiet front. -/
theorem fin_leafOk (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s)) (hq : finishFrontQ s = .ok t)
    {a : FinOwn} (here : t.here = .fin a) (Q : ReqGroup) (P9 : Par9) (y : Sent) (rL : Fmt.RoundView)
    (cols : List Col) :
    ∀ τ ∈ treesOf (inFront P9 (finFrontOf t a Q) t.book y rL cols), ∀ tree,
      (inFront P9 (finFrontOf t a Q) t.book y rL cols).book.trees[τ]? = some tree →
      leafOk (inFront P9 (finFrontOf t a Q) t.book y rL cols).st tree = true := by
  intro τ hτ tree htree
  have hp := fin_own_reached hS hR O hr hq here Q P9 y rL cols τ hτ tree htree
  obtain ⟨-, rs, cl, f₂⟩ := (reach_raw hr).fold
  obtain ⟨a', ha', hrows⟩ := finishFrontQ_rows hq
  obtain rfl : a' = a := by
    have e : VerifiableInference.Desc.First.Here.fin a' = .fin a := ha'.symm.trans here
    cases e
    rfl
  have hp' : ∀ q ∈ tree.parts.toList, q ∈ (singleRowsOracles s.check.frame.rows).toList := by
    intro q hq'
    rw [← hrows]
    exact hp q hq'
  have e : leafOk (inFront P9 (finFrontOf t a' Q) t.book y rL cols).st tree = leafOk s.st tree :=
    leafOk_same fun q _ => by
      show t.st.oracles[q]? = s.st.oracles[q]?
      rw [finishFrontQ_st hq]
      rfl
  rw [e]
  exact leafOk_at_finish hS hR O f₂ tree hp'

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.head_msgs
#print axioms Johnson.AtFull.Shape.head_leafOk
#print axioms Johnson.AtFull.Shape.lists_at_finish
#print axioms Johnson.AtFull.Shape.fresh_blank_fin
#print axioms Johnson.AtFull.Shape.leafOk_at_finish
#print axioms Johnson.AtFull.Shape.fin_leafOk
