-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LOpensTable.lean: the table of a code switch's sending, as
a thread has it at hand, shows the sending's written column. General in the thread, the switch's
place and the tree's number among the chain's.

  `columnLength`, `length_col`   how many words a written column has: by the messages' shapes alone
  `canonW_col`              every word of a written column is the written form of a field element
  `widthTest`               a public test: tree number j of a sending is there, and its declared
                            width is the column's length
  `switchTable_shows`       where the switch's part is handed its coins and its rows are laid: table
                            number j of the switch's sending has the tree's depth, and its column at
                            every position is the written column over these rows
  `columnAtHand_is_sent`    so at a stand of a thread whose table at a source shows, at that stand,
                            what that table shows: the column at hand, below the tree's length

Limits.
- That the part is handed its coins (hHanded), that its rows are laid (hLaid), and what the thread's
  table shows at the stand (hSame) are premises.
- At the sender `coreSender freshTable` alone.
- Nothing on what a row holds. Nothing on completeness, on soundness or on hiding.
NOT IN FRONT OF A LAW OVER COINS: `switchTable_shows` and `columnAtHand_is_sent` bear this label;
the rule is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: hHanded
and hLaid tie the letters cK and V to a run's coins; the thread from `Thr` as a premise.
Terms: the head of LShapeTest.lean; Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.RowsTie
import Johnson.Desc.ProofFile.Honest.K12.TableCol
import Johnson.Desc.ProofFile.Honest.K12.PlanOpens
import Johnson.Desc.ProofFile.Honest.Thread.Sent
import Johnson.Desc.ProofFile.Honest.Thread.ThrRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open Johnson.Prover.Send (col mainSyms maskSyms shapeAt)
open Johnson.Prover.Link (words3)
open OnBytes.Slice (ofF toF toF_ofF ofE)
open ProofFile.Honest.K12 (CanonW colAt)

local notation "Rows" => Johnson.Prover.Send.Rows

/-- How many words the written column of tree number t has. -/
def columnLength (P : VerifiableInference.Desc.K1.Par) (t : ℕ) : ℕ :=
  let lay := (VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}
  let mine := (List.range P.sent.size).filter fun k => lay.tree[k]? == some t
  (mine.map fun k => (if (shapeAt P k).mainDeg == 3 then 3 else 1) * (shapeAt P k).mainRows).sum +
    (mine.map fun k => 3 * (shapeAt P k).maskRows).sum

theorem length_flatMap_const {α β : Type} (l : List α) (f : α → List β) (n : ℕ)
    (h : ∀ a ∈ l, (f a).length = n) : (l.flatMap f).length = n * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons, List.length_append, h a (List.mem_cons_self ..),
      ih fun b hb => h b (List.mem_cons_of_mem _ hb), List.length_cons, Nat.mul_succ, Nat.add_comm]

theorem length_flatMap_by {α β : Type} (l : List α) (f : α → List β) (g : α → ℕ)
    (h : ∀ a, (f a).length = g a) : (l.flatMap f).length = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.length_append, h, ih, List.map_cons, List.sum_cons]

theorem length_mainSyms (P : VerifiableInference.Desc.K1.Par) (V : ℕ → Rows) (k x : ℕ) :
    (mainSyms P V k x).length =
      (if (shapeAt P k).mainDeg == 3 then 3 else 1) * (shapeAt P k).mainRows := by
  unfold mainSyms
  dsimp only
  rw [length_flatMap_const _ _ (if (shapeAt P k).mainDeg == 3 then 3 else 1) fun r _ => by
    split <;> rfl, List.length_range]

theorem length_maskSyms (P : VerifiableInference.Desc.K1.Par) (V : ℕ → Rows) (k x : ℕ) :
    (maskSyms P V k x).length = 3 * (shapeAt P k).maskRows := by
  unfold maskSyms
  dsimp only
  rw [length_flatMap_const _ _ 3 fun r _ => rfl, List.length_range]

/-- **A written column's length hangs on the messages' shapes alone.** -/
theorem length_col (P : VerifiableInference.Desc.K1.Par) (V : ℕ → Rows) (t x : ℕ) :
    (col P V t x).length = columnLength P t := by
  unfold col columnLength
  dsimp only
  rw [List.length_append, length_flatMap_by _ _ _ fun k => length_mainSyms P V k x,
    length_flatMap_by _ _ _ fun k => length_maskSyms P V k x]

theorem canonW_words3 (y : OnBytes.Slice.GE) : CanonW (words3 (ofE y)) := fun w hw => by
  simp only [words3, ofE, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with h | h | h
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩

/-- **Every word of a written column is the written form of an element of the base field.** -/
theorem canonW_col (P : VerifiableInference.Desc.K1.Par) (V : ℕ → Rows) (t x : ℕ) :
    CanonW (col P V t x) := fun w hw => by
  unfold col at hw
  dsimp only at hw
  rcases List.mem_append.1 hw with h | h
  · obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 h
    unfold mainSyms at hk
    dsimp only at hk
    obtain ⟨r, -, hr⟩ := List.mem_flatMap.1 hk
    split at hr
    · exact canonW_words3 _ w hr
    · exact ⟨_, List.mem_singleton.1 hr⟩
  · obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 h
    unfold maskSyms at hk
    dsimp only at hk
    obtain ⟨r, -, hr⟩ := List.mem_flatMap.1 hk
    exact canonW_words3 _ w hr

/-- **A public test**: tree number j of the sending is there, and its declared width is the written
column's length. -/
def widthTest (P : VerifiableInference.Desc.K1.Par) (j : ℕ) : Bool :=
  (P.trees[j]?).any fun t => t.mainWidth + t.maskWidth == columnLength P j

variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- **The table of a switch's sending shows the written column over the rows that the switch
laid.** -/
theorem switchTable_shows (ch : ℕ) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : K2.Closing) (p : K2.SwitchPlace) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (hd : List Fmt.Drawn) (j : ℕ)
    {cK : K2.Law.SwitchCoins p.sizes p.others p.foldVars p.carries}
    (hHanded : K2.handed ch p k = some cK) {V : ℕ → Rows}
    (hLaid : K2.switchRowsLaid D readers closing p cK w hd = .ok V)
    (hw : widthTest (K2.sendingPar p.sizes.codes (K2.switchSent p.sizes p.others)) j = true) :
    ∃ t, (K2.sendingPar p.sizes.codes (K2.switchSent p.sizes p.others)).trees[j]? = some t ∧
      (K2.switchTableAt Bk ch (K2.coreSender K2.freshTable) D readers closing p k w hd
        j).logLength = t.logN ∧
      ∀ y, (K2.switchTableAt Bk ch (K2.coreSender K2.freshTable) D readers closing p k w hd j).col
        y = col (K2.sendingPar p.sizes.codes (K2.switchSent p.sizes p.others)) V j y := by
  unfold widthTest at hw
  cases ht : (K2.sendingPar p.sizes.codes (K2.switchSent p.sizes p.others)).trees[j]? with
  | none =>
    rw [ht] at hw
    cases hw
  | some t =>
    rw [ht, Option.any_some, beq_iff_eq] at hw
    have hj : j < (K2.sendingPar p.sizes.codes (K2.switchSent p.sizes p.others)).trees.length :=
      (List.getElem?_eq_some_iff.1 ht).1
    have hg : (K2.sendingPar p.sizes.codes (K2.switchSent p.sizes p.others)).trees[j] = t :=
      (List.getElem?_eq_some_iff.1 ht).2
    have e : K2.switchTableAt Bk ch (K2.coreSender K2.freshTable) D readers closing p k w hd j =
        { logLength := t.logN, words := t.mainWidth + t.maskWidth
          sym := fun pos i => toF ((col (K2.sendingPar p.sizes.codes
            (K2.switchSent p.sizes p.others)) V j pos).getD i.val 0) } := by
      rw [K2.Law.table_of_rows, hHanded, Option.bind_some, hLaid]
      show ((K1.treeTables _ V)[j]?).getD K2.noTable = _
      unfold K1.treeTables
      rw [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hj, hg]
      simp
    refine ⟨t, rfl, by rw [e], fun y => ?_⟩
    rw [e]
    have hlen := length_col (K2.sendingPar p.sizes.codes (K2.switchSent p.sizes p.others)) V j y
    rw [← hw] at hlen
    refine List.ext_getElem (by
      simp only [Table.col, List.length_ofFn]
      exact hlen.symm) fun i i1 i2 => ?_
    simp only [Table.col, List.getElem_ofFn]
    rw [List.getD_eq_getElem _ _ i2]
    obtain ⟨z, hz⟩ := canonW_col _ V j y _ (List.getElem_mem i2)
    rw [hz, toF_ofF]

variable {S Cl X Pb : Type}

/-- **So at a stand of a thread whose table at the source σ shows there what that table shows**: the
column at hand, below the tree's length. -/
theorem columnAtHand_is_sent
    (T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) {b : ℕ} {σ : Fmt.TreeSource}
    (hin : σ ∈ T.hand b) (ch : ℕ) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : K2.Closing) (p : K2.SwitchPlace) (j : ℕ)
    {k : Coins Bk} {s : S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : Thr T b k s m E)
    (hSame : (T.tableAt σ k m).2.same (K2.switchTableAt Bk ch (K2.coreSender K2.freshTable) D
      readers closing p k m.st.input (m.st.heard.take (T.fixed σ)) j) = true)
    {cK : K2.Law.SwitchCoins p.sizes p.others p.foldVars p.carries}
    (hHanded : K2.handed ch p k = some cK) {V : ℕ → Rows}
    (hLaid : K2.switchRowsLaid D readers closing p cK m.st.input
      (m.st.heard.take (T.fixed σ)) = .ok V)
    (hw : widthTest (K2.sendingPar p.sizes.codes (K2.switchSent p.sizes p.others)) j = true) :
    ∃ t, (K2.sendingPar p.sizes.codes (K2.switchSent p.sizes p.others)).trees[j]? = some t ∧
      ∀ y, y < 2 ^ t.logN → colAt E.tree σ y =
        col (K2.sendingPar p.sizes.codes (K2.switchSent p.sizes p.others)) V j y := by
  obtain ⟨t, ht, hlog, hcol⟩ := switchTable_shows ch D readers closing p k m.st.input
    (m.st.heard.take (T.fixed σ)) j hHanded hLaid hw
  obtain ⟨⟨-, hH⟩, -⟩ := hT
  obtain ⟨pt, hE, hc⟩ := T.col_of_handAt (hH _ hin)
  obtain ⟨hl, hs⟩ := Table.same_elim hSame
  refine ⟨t, ht, fun y hy => ?_⟩
  unfold colAt
  rw [hE]
  show pt.2.col y = _
  rw [hc y (by rw [hl, hlog]; exact hy), hs y (by rw [hl, hlog]; exact hy), hcol]

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.columnLength
#print axioms ProofFile.Honest.K12.AtProof.length_flatMap_const
#print axioms ProofFile.Honest.K12.AtProof.length_flatMap_by
#print axioms ProofFile.Honest.K12.AtProof.length_mainSyms
#print axioms ProofFile.Honest.K12.AtProof.length_maskSyms
#print axioms ProofFile.Honest.K12.AtProof.length_col
#print axioms ProofFile.Honest.K12.AtProof.canonW_words3
#print axioms ProofFile.Honest.K12.AtProof.canonW_col
#print axioms ProofFile.Honest.K12.AtProof.widthTest
#print axioms ProofFile.Honest.K12.AtProof.switchTable_shows
#print axioms ProofFile.Honest.K12.AtProof.columnAtHand_is_sent
