-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/Behind.lean: THE STEP BEHIND THE SENDING OF A CODE SWITCH BETWEEN TWO
SEGMENTS (`switchBehind`, Johnson/Top/H0/Tw/K2/Switch.lean) RETURNS, wherever premises on the make
of what it is handed hold; with what it returns. At all values: no premise speaks of an element of
the field but through a test with code on a tensor's written-out marks. Statements and proofs.

  `group_withRow`, `rowL_withRow`   the group behind one more open row; that row does not turn the
                    ground's test on a row
  `addRowsFrom_returns`, `addRowsG_returns`   rows that pass the test one by one are added, in order
  `BehindFits`      the premises, at the statement behind the joins
  `switchBehind_returns`   the step returns: the statement behind the joins with the made rows
                    appended to the group's open rows; the book and the columns that the reading
                    left; the numbers cut as the target says, with the positions

WHAT IS STILL A PREMISE IN THE FORM «… = .ok …»: that the reading of the old rows returns
(`readOld`) and that g and the copies join the group (`joinG`): each wants a law of this form of its
own.

Limits. Targets whose rest lies in g's main part alone: there g has no mask row and no ledger is
shut. The premises stand at the statement BEHIND the joins. Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Returns.MadeRows
import Johnson.Top.H0.Tw.K2C.Closed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.Slice (withRow withRows)
open VerifiableInference.Desc.Ground (rowL rowsL ok addRowP addRowsFrom addRowsP)
open _root_.Tw.K2 (SwIn SwOut readOld joinG addRowsG switchBehind dOf rowsCan)
open VerifiableInference.Desc.First.K2 (locOk outOf BehindIs switchBehind_of)

/-- The group behind one more open row. -/
theorem group_withRow (S : Statement) (g : Nat) (r' : OnBytes.Row) :
    (withRow S g r').groups[g]? =
      (S.groups[g]?).map fun G => { G with rows := G.rows.push r' } := by
  unfold withRow
  simp [Array.getElem?_modify]

/-- One more open row of the group does not turn the ground's test on a row. -/
theorem rowL_withRow (S : Statement) (g : Nat) (r' r : OnBytes.Row) :
    rowL (withRow S g r') g r = rowL S g r := by
  unfold rowL
  simp only [group_withRow]
  cases S.groups[g]? <;> rfl

/-- Rows that pass the test one by one are added, in order. -/
theorem addRowsFrom_returns {L : Type} (g : Nat) : ∀ (rows : List OnBytes.Row)
    (d : Desc.Plain.DState L), (∀ r ∈ rows, ok (rowL d.st g r) = true) →
    addRowsFrom g rows d = some { d with st := withRows d.st g rows }
  | [], _, _ => rfl
  | row :: l, d, h => by
    have h1 : addRowP d g row = some { d with st := withRow d.st g row } := by
      unfold addRowP
      rw [if_pos (h row (List.mem_cons_self ..))]
    show (addRowP d g row).bind (addRowsFrom g l) = _
    rw [h1]
    show addRowsFrom g l { d with st := withRow d.st g row } = _
    rw [addRowsFrom_returns g l _ fun r hr => by
      show ok (rowL (withRow d.st g row) g r) = true
      rw [rowL_withRow]
      exact h r (List.mem_cons_of_mem _ hr)]
    rfl

theorem addRowsG_returns (S : Statement) (g : Nat) (rows : List OnBytes.Row)
    (h0 : ok (rowsL S g) = true) (h : ∀ r ∈ rows, ok (rowL S g r) = true) :
    addRowsG S g rows = .ok (withRows S g rows) := by
  have e : addRowsP (dOf S) g rows = some { dOf S with st := withRows S g rows } := by
    unfold addRowsP
    rw [if_pos (show ok (rowsL (dOf S).st g) = true from h0)]
    exact addRowsFrom_returns g rows (dOf S) h
  unfold addRowsG
  rw [e]

/-- **The premises**, at S: the statement behind the joins. i: what the step is handed. c: the old
main code. y: the symbols that the reading gave. -/
structure BehindFits (i : SwIn) (c : Code) (y : Array E) (S : Statement) (G : Group) : Prop where
  check : switchTargetCheck S i.old i.T = true
  restMain : i.T.rest.part = .main
  fits : OldFits S i.old
  keptPos : ∀ k ∈ i.T.kept.toList, 0 < k.shape.mainRows
  seated : SeatedAt S i.old i.T (i.ids.getD 0 noId) (i.ids.extract 1 (1 + i.T.kept.size))
  lengths : S.codes.lengthsOk = true
  logC : (S.codes.base.getD i.old.code default).logN ≤ 32
  logZ : (S.codes.mask.getD i.old.maskCode default).logN ≤ 32
  inRange : ∀ x ∈ (Positions.ofDraws c.logN i.drawn.poss).all.toList,
    x < 2 ^ (S.codes.base.getD i.old.code default).logN
  stored : PadsStored S i.T (i.ids.getD 0 noId) (i.ids.extract 1 (1 + i.T.kept.size))
  group : S.groups[i.grp]? = some G
  noRun : G.inRun = false
  make : MakeFits S i.old i.T (i.ids.getD 0 noId) (i.ids.extract 1 (1 + i.T.kept.size)) G
  members : ∀ o ∈ G.members.toList, o = i.ids.getD 0 noId ∨
    ∃ a k, i.T.kept[a]? = some k ∧ o = (i.ids.extract 1 (1 + i.T.kept.size)).getD a noId
  can : rowsCan S i.old i.T (i.ids.extract 1 (1 + i.T.kept.size))
    (Positions.ofDraws c.logN i.drawn.poss) y = true

/-- **The step behind the sending returns.** -/
theorem switchBehind_returns (i : SwIn) (c : Code) (B : TreeBook)
    (left : List _root_.Tw.K2.Col) (y : Array E) (S2 S3 : Statement) (G : Group)
    (hCode : i.st.codes.base[i.old.code]? = some c) (hLoc : locOk i c.logN = true)
    (hRead : readOld i (Positions.ofDraws c.logN i.drawn.poss) = .ok (B, left, y))
    (hJoinG : joinG i.st i.grp (i.ids.getD 0 noId) false = .ok S2)
    (hJoinKept : ((i.ids.extract 1 (1 + i.T.kept.size)).zip i.T.kept).foldlM (fun S p =>
      joinG S i.grp p.1 p.2.keptAgain) S2 = .ok S3)
    (F : BehindFits i c y S3 G) :
    ∃ rows, Own.swRows S3 i.old i.T (i.ids.getD 0 noId) (i.ids.extract 1 (1 + i.T.kept.size))
        (Positions.ofDraws c.logN i.drawn.poss) y = some rows ∧
      switchBehind i = .ok ⟨withRows S3 i.grp rows, B, left,
        outOf i (Positions.ofDraws c.logN i.drawn.poss)⟩ := by
  obtain ⟨rows, hrows⟩ := Option.isSome_iff_exists.1
    (_root_.Tw.K2.rowsCan_someOwn (g := i.ids.getD 0 noId) F.can)
  have A := atPublic F.check F.restMain F.fits F.keptPos F.seated F.lengths
  have hbare : ¬ 0 < i.T.shape.maskRows := by
    rw [g_bare A]
    exact Nat.lt_irrefl 0
  have hGroup : ok (rowsL S3 i.grp) = true := by
    unfold ok rowsL VerifiableInference.Desc.Ground.has
    simp [F.group, F.noRun]
  have hpass := madeRows_pass S3 i.old i.T _ _ _ y rows F.check F.restMain F.fits F.keptPos
    F.seated F.lengths F.logC F.logZ F.inRange hrows F.stored i.grp G F.group F.noRun F.make
    F.members
  refine ⟨rows, hrows, switchBehind_of (c := c) (y := y) (S1 := i.st) (S2 := S2) (S3 := S3)
    (rows := rows) ⟨hCode, hLoc, hRead, by rw [if_neg hbare], hJoinG, hJoinKept, hGroup, F.can,
      hrows, addRowsG_returns S3 i.grp rows hGroup hpass, rfl⟩⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.addRowsG_returns
#print axioms VerifiableInference.Desc.K2.Honest.Returns.switchBehind_returns
