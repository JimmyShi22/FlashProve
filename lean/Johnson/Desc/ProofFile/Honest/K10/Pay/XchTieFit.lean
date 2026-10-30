-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchTieFit.lean: the closing of a segment (K10): the equation of the field tie of
`CarryOwed` (Honest/K10/Xch/CarryTop.lean), from two clauses on each member of the group, under the public test `rowsFit`
(Honest/K10/Job.lean) that the field itself hands:
  the job's rows for the member are `memberOf` of rows Rr that the shared text of a message's rows returned
  (`messageRows`, Honest/K2/Sending.lean), at the codes of the job's rows;
  the witness's table of the member is `K1.rowsMsg` of Rr.
The third clause of `tie_of_rowsMsg` (Pay/XchTieRows.lean), "Rr is 0 from the message length on", is a theorem here.

  `rowsFit_at`       what `rowsFit` says of member number i: the statement's shape; the shape names the group's code for its
                   main rows and the group's mask code for its mask rows; and the two codes' numbers are the rows' own
  `tie_of_tabs_in`   `tie_of_rowsMsg` with its third clause asked at real rows alone
  **`tie_of_made`**    the field tie's equation from the two clauses

Limits. The two clauses are premises, shown here of no witness and no job. No head, thread or prover is named.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchTieRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (Statement)
open OnBytes.Means (realRows)
open OnBytes.Slice (readE)
open VerifiableInference.Desc
open VerifiableInference.Desc.K2.Honest (GroupMember)
open VerifiableInference.Desc.Sound (MsgT wordsFirst tabAt seatBy noFirst)
open Johnson.Prover.Send (Rows)
open ProofFile.Honest.K2 (FreshTable Stretch messageRows)
open ProofFile.Honest.K10.YesFree (BaseData)

/-- What the public test says of member number i. -/
theorem rowsFit_at {S : Statement} {G : OnBytes.Group} {R : GroupData} (hf : rowsFit S G R = true) {o i : Nat}
    {x : MemberRows} (ho : G.members.toList[i]? = some o) (hx : R.members[i]? = some x) :
    G.code = R.code ∧ G.maskCode = R.maskCode ∧ (S.oracles[o]?).map (·.shape) = some x.shape ∧
      (x.shape.mainRows = 0 ∨ x.shape.code = G.code) ∧ (x.shape.maskRows = 0 ∨ x.shape.maskCode = G.maskCode) := by
  unfold rowsFit at hf
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, h1⟩, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hall⟩ := hf
  have hz : (G.members.toList.zipIdx)[i]? = some (o, i) := by
    rw [List.getElem?_zipIdx, ho]
    simp
  have hm : ((o, i), x) ∈ G.members.toList.zipIdx.zip R.members :=
    List.mem_iff_getElem?.2 ⟨i, List.getElem?_zip_eq_some.2 ⟨hz, hx⟩⟩
  obtain ⟨⟨⟨a1, -⟩, a3⟩, a4⟩ := hall _ hm
  exact ⟨h1, h2, a1, a3, a4⟩

/-- `tie_of_rowsMsg` with its third clause asked at real rows alone. -/
theorem tie_of_tabs_in {Cells Tok : Type} (arr : Nat → Nat → Nat) {s : First.S} {D : BaseData} {R : GroupData}
    {v : Wit Cells Tok MsgT}
    (hth : ∀ o ∈ D.G.members.toList, o < s.st.oracles.size)
    (hM : ∀ o ∈ D.G.members.toList, ∃ (i : Nat) (g : GroupMember) (Rr : Rows),
      D.G.members.idxOf? o = some i ∧ R.members[i]? = some (memberOf g Rr) ∧
      tabAt s.st.codes arr (seatBy noFirst s.book) s.st v o = K1.rowsMsg g.shape Rr ∧
      ∀ (part : OnBytes.Part) (b j : Nat), b < realRows s.st o part → ellAt R part ≤ j →
        K1.rowsMsg g.shape Rr (part == .mask) b j = 0) :
    OnBytes.Means.tablesOf (D.S1 (K9.recOf s)) (Own.layoutOf (K9.recOf s).st D.G) (wordsFirst arr s.st s.book v) =
      OnBytes.Means.tablesOf (D.S1 (K9.recOf s)) (Own.layoutOf (K9.recOf s).st D.G) (rowWords D (K9.recOf s) R) :=
  tie_of_tabAt arr hth fun o ho part b j hb => by
    obtain ⟨i, g, Rr, hi, hR, hT, h0⟩ := hM o ho
    rw [hT]
    by_cases c : j < ellAt R part
    · rw [if_pos c]
      unfold rowsAt
      rw [hi, Option.bind_some, hR]
      exact (readE_member g Rr part b j).symm
    · rw [if_neg c]
      exact h0 part b j hb (Nat.le_of_not_lt c)

/-- **The field tie's equation, from two clauses on each member, under `rowsFit`.** -/
theorem tie_of_made {Cells Tok : Type} (arr : Nat → Nat → Nat) {s : First.S} {D : BaseData} {R : GroupData}
    {v : Wit Cells Tok MsgT}
    (hth : ∀ o ∈ D.G.members.toList, o < s.st.oracles.size) (hfit : rowsFit s.st D.G R = true)
    (hM : ∀ o ∈ D.G.members.toList, ∃ (i : Nat) (g : GroupMember) (Rr : Rows) (table : FreshTable)
      (fold : Option Nat) (data : Nat → Nat → Cb.Gl.E) (k : Stretch),
      D.G.members.idxOf? o = some i ∧ R.members[i]? = some (memberOf g Rr) ∧
      messageRows table R.codes g.shape fold data k = .ok Rr ∧
      tabAt s.st.codes arr (seatBy noFirst s.book) s.st v o = K1.rowsMsg g.shape Rr) :
    OnBytes.Means.tablesOf (D.S1 (K9.recOf s)) (Own.layoutOf (K9.recOf s).st D.G) (wordsFirst arr s.st s.book v) =
      OnBytes.Means.tablesOf (D.S1 (K9.recOf s)) (Own.layoutOf (K9.recOf s).st D.G) (rowWords D (K9.recOf s) R) := by
  refine tie_of_tabs_in arr hth fun o ho => ?_
  obtain ⟨i, g, Rr, table, fold, data, k, hi, hR, hm, hT⟩ := hM o ho
  refine ⟨i, g, Rr, hi, hR, hT, fun part b j hb hj => ?_⟩
  obtain ⟨hlt, hget⟩ := OnBytes.Means.find_some
    (L := { (default : OnBytes.GroupLayout) with members := D.G.members }) hi
  have hlt' : i < D.G.members.size := hlt
  have hget' : D.G.members.getD i OnBytes.noId = o := hget
  have ho' : D.G.members.toList[i]? = some o := by
    rw [Array.getElem?_toList, ← hget', Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt']
    rfl
  obtain ⟨c1, c2, hs, hmn, hmk⟩ := rowsFit_at hfit ho' hR
  obtain ⟨y, hy, ey⟩ := Option.map_eq_some_iff.1 hs
  have ey' : y.shape = g.shape := ey
  have hrows : b < g.shape.rows part := by
    unfold realRows at hb
    rw [hy] at hb
    rw [← ey']
    exact hb
  refine rowsMsg_beyond hm part b j ?_
  cases part
  · have h0 : g.shape.mainRows ≠ 0 := Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le b) hrows)
    have hc : g.shape.code = D.G.code := hmn.resolve_left h0
    show (R.codes.base.getD g.shape.code default).ell ≤ j
    rw [hc, c1]
    exact hj
  · have h0 : g.shape.maskRows ≠ 0 := Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le b) hrows)
    have hc : g.shape.maskCode = D.G.maskCode := hmk.resolve_left h0
    show (R.codes.mask.getD g.shape.maskCode default).ell ≤ j
    rw [hc, c2]
    exact hj

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.rowsFit_at
#print axioms ProofFile.Honest.K10.tie_of_tabs_in
#print axioms ProofFile.Honest.K10.tie_of_made
