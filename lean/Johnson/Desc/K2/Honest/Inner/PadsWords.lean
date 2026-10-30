-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Inner/PadsWords.lean: THE ONE TEST ON VALUES THAT THE GROUND ASKS OF A NEW
OPEN ROW ("addRow: ON VALUES: no coefficient on a pad", `rowL`,
Johnson/Desc/First/Base/Ground.lean) SAYS YES AT EVERY ROW THAT A CODE SWITCH BETWEEN TWO SEGMENTS
LAYS: ON THE THREE WORDS of each coefficient. Statements and proofs.

  `fold_ok`, `coefficient_ok`   a row's coefficient has its three words below the prime, whatever
                    the row holds: it is 0 or a sum
  `allZero_coef`    so the test on words says yes just where the coefficient, read in the field,
                    is 0
  `PadsStored`      g and the copies stand in the statement with the pads of their shapes
  `padClause`       the clause, as a Bool, cut out of `rowL`; `padClause_is`: it is the eighth
  `padClause_made`  it says yes at every made row

By: Inner/PadsProof.lean (`padsUnread`); `isZeroE_iff` (OnBytes/Slice/ProgField.lean); `okE_add`
(Johnson/Top/H/P1Tie/Words.lean).

Limits. That the group's members are g and copies alone is a PREMISE. (At all three sorts of place
the switch's front opens the group anew: `firstFront` and `finishFront`,
Johnson/Top/H0/Tw/K2/First.lean; the head's front calls `firstFront`,
Johnson/Top/H0/Tw/K2C/Head.lean; the next segment's own messages join behind the rows,
`firstBehind`: by reading; no lemma here.) Nothing on any property.

-/
import Johnson.Desc.K2.Honest.Inner.PadsProof
import Johnson.Top.H.P1Tie.Words
import Johnson.Desc.Own.RowsAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE coefAt readE)
open VerifiableInference.Desc.Ground (rowL ok has)

/-- A sum that takes some of a list's entries has its words below the prime, if it began so. -/
theorem fold_ok {α : Type} (p : α → Bool) (f : α → E) : ∀ (l : List α) (s : E), okE s = true →
    okE (l.foldl (fun s t => if p t then addE s (f t) else s) s) = true
  | [], _, h => h
  | t :: l, s, h => by
    rw [List.foldl_cons]
    apply fold_ok p f l
    by_cases c : p t = true
    · rw [if_pos c]
      exact VerifiableInference.Desc.Part.MaskedSum.okE_add _ _
    · rw [if_neg c]
      exact h

/-- A row's coefficient has its three words below the prime. -/
theorem coefficient_ok (r : OnBytes.Row) (o : Nat) (part : Part) (i : Nat) :
    okE (r.coefficient o part i) = true := by
  unfold Row.coefficient
  simp only [← Array.foldl_toList]
  exact fold_ok (fun f : MainForm => f.oracle == o && part == .main) (fun f => f.c.entry i) _ _
    (fold_ok (fun w : OnBytes.Run => w.oracle == o && w.part == part && w.first ≤ i &&
        0 < w.step && (i - w.first) % w.step == 0 && (i - w.first) / w.step < w.coeffs.size)
      (fun w => w.coeffs.get ((i - w.first) / w.step)) _ _
      (fold_ok (fun u : Single => u.oracle == o && u.part == part && u.index == i)
        (fun u => u.coeff) _ _
        (fold_ok (fun t : Term => t.oracle == o && t.part == part) (fun t => t.v.entry i) _ _
          rfl)))

/-- The test on words says yes just where the coefficient, read in the field, is 0. -/
theorem allZero_coef (r : OnBytes.Row) (o : Nat) (part : Part) (i : Nat) :
    Own.allZero (r.coefficient o part i) = true ↔ coefAt r o part i = 0 := by
  rw [← Own.allZero_agrees]
  exact OnBytes.Slice.isZeroE_iff _ (coefficient_ok r o part i)

/-- g and the copies stand in the statement with the pads of their shapes. -/
structure PadsStored (S : Statement) (T : SwitchTarget) (g : Nat) (anew : Array Nat) : Prop where
  carrying : (S.oracles[g]?).map (·.pad) =
    some ((padPlaces S.codes T.shape).map fun p => (p.part, p.index))
  copies : ∀ (a : Nat) (k : KeptTarget), T.kept[a]? = some k →
    (S.oracles[anew.getD a noId]?).map (·.pad) =
      some ((padPlaces S.codes k.shape).map fun p => (p.part, p.index))

/-- The ground's clause on values, as a Bool. -/
def padClause (S : Statement) (grp : Nat) (row : OnBytes.Row) : Bool :=
  has S.groups[grp]? fun G =>
    G.members.all fun o =>
      ((S.oracles[o]?).map (·.pad)).getD [] |>.all fun q =>
        Own.allZero (row.coefficient o q.1 q.2)

/-- It is the eighth clause of `rowL`. -/
theorem padClause_is (S : Statement) (grp : Nat) (row : OnBytes.Row) :
    ((rowL S grp row).drop 7).map (·.2) = [padClause S grp row] := rfl

/-- **The clause says yes at every made row.** G: the group; its members: g and copies alone. -/
theorem padClause_made (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat)
    (anew : Array Nat) (pos : Positions) (y : Array E) (rows : List OnBytes.Row)
    (check : switchTargetCheck S old T = true) (restMain : T.rest.part = .main)
    (fits : OldFits S old) (keptPos : ∀ k ∈ T.kept.toList, 0 < k.shape.mainRows)
    (seated : SeatedAt S old T g anew) (lengths : S.codes.lengthsOk = true)
    (hlogC : (S.codes.base.getD old.code default).logN ≤ 32)
    (hlogZ : (S.codes.mask.getD old.maskCode default).logN ≤ 32)
    (hx : ∀ x ∈ pos.all.toList, x < 2 ^ (S.codes.base.getD old.code default).logN)
    (hrows : Own.swRows S old T g anew pos y = some rows)
    (stored : PadsStored S T g anew) (grp : Nat) (G : Group) (hG : S.groups[grp]? = some G)
    (hmem : ∀ o ∈ G.members.toList, o = g ∨ ∃ a k, T.kept[a]? = some k ∧ o = anew.getD a noId) :
    ∀ r ∈ rows, padClause S grp r = true := by
  intro r hr
  have sp := padsUnread S old T g anew pos y rows check restMain fits keptPos seated lengths hlogC
    hlogZ hx hrows r hr
  unfold padClause has
  rw [hG]
  show (G.members.all fun o => _) = true
  rw [Array.all_eq_true_iff_forall_mem]
  intro o ho
  rw [List.all_eq_true]
  intro q hq
  rw [allZero_coef]
  rcases hmem o (Array.mem_toList_iff.2 ho) with rfl | ⟨a, k, hk, rfl⟩
  · rw [stored.carrying] at hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact sp.1 p hp
  · rw [stored.copies a k hk] at hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
    exact sp.2 a k hk p hp

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.allZero_coef
#print axioms VerifiableInference.Desc.K2.Honest.padClause_made
