-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/RowSays.lean
(kind K9; row rows_law's half): THEOREMS: THE TIE, BY NAME, OF K9's OWN MEASURE OF
A ROW (rowSum, Law/AsRow.lean: a row's coefficients applied to the tables of the oracle messages
0, .., N - 1) TO THE MEANING OF A ROW THAT THE ROWS' OWN LAW SPEAKS OF (OnBytes.Means.value and
Says, Johnson/Desc/Means/Says.lean, landed).
  rowSum_value   rowSum ρ S N m row = value ρ S row m, at every N from the number of the statement's
                 oracle messages on, for a row that has no coefficient on a table that is not there
                 and none on a later oracle message. IT IS THE OTHER HOUSE's value_plain_le
                 (Johnson/Desc/Means/RowSumTie.lean), CALLED: rowSum's body is
                 its right-hand side to the letter [by Lean: the proof unfolds rowSum and no more].
                 (That file is compiled here with ONE IMPORT LINE TURNED, from the loose
                 LLP7L.Says to Johnson.Desc.Means.Says.)
  holds_says     so "the row holds on the tables" (rowSum .. = the target) IS Says.
  groupHolds_says   K9's relation "every open row of the segment's group holds on the tables"
                 (GroupHoldsAt, Law/Hout.lean) IS AllSay of the group's rows, under the two
                 conditions at each row.
THE TWO CONDITIONS (habs, hoff) ARE HYPOTHESES HERE. By that house's reading they follow for every
row that the ground's addRowP has let in (each summand's place is asked to be there). No lemma of
this file gives either condition.

-/
import Johnson.Desc.Means.RowSumTie
import Johnson.Desc.First.Batch.Law.Hout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Lens)

variable {T K : Type} [CommRing K] (ρ : Reading K)

/-- No coefficient on a table that is not there, and none on a later oracle message. -/
def NoneOff (S : Statement) (row : OnBytes.Row) : Prop :=
  (∀ o part, S.has o part = false → ∀ J, ρ.val (row.coefficient o part J) = 0) ∧
    ∀ o, S.oracles.size ≤ o → ∀ part J, ρ.val (row.coefficient o part J) = 0

/-- **K9's measure of a row is the rows' law's value.** -/
theorem rowSum_value (S : Statement) (N : Nat) (m : Nat → OnBytes.Part → Nat → K)
    (row : OnBytes.Row) (hN : S.oracles.size ≤ N) (h : NoneOff ρ S row) :
    rowSum ρ S N m row = OnBytes.Means.value ρ S row m := by
  unfold rowSum
  exact (OnBytes.Means.value_plain_le ρ S row m N hN h.1 h.2).symm

/-- "The row holds on the tables" is Says. -/
theorem holds_says (S : Statement) (N : Nat) (m : Nat → OnBytes.Part → Nat → K)
    (row : OnBytes.Row) (hN : S.oracles.size ≤ N) (h : NoneOff ρ S row) :
    rowSum ρ S N m row = ρ.val row.target ↔ OnBytes.Means.Says ρ S row m := by
  rw [rowSum_value ρ S N m row hN h]
  rfl

/-- **K9's relation on the group's open rows is AllSay.** -/
theorem groupHolds_says (X : Lens T) (N : Nat) (s : T) (m : Nat → OnBytes.Part → Nat → K)
    (a : K9.Part) (G : Group) (ha : X.get? s = some a)
    (hG : a.d.st.groups[a.L.check.group]? = some G) (hN : a.d.st.oracles.size ≤ N)
    (h : ∀ row ∈ G.rows.toList, NoneOff ρ a.d.st row) :
    GroupHoldsAt X ρ N s m ↔ OnBytes.Means.AllSay ρ a.d.st G.rows.toList m := by
  constructor
  · intro hh row hr
    exact (holds_says ρ a.d.st N m row hN (h row hr)).1 (hh a ha G hG row hr)
  · intro hh a' ha' G' hG' row hr
    have e : a' = a := Option.some.inj (ha'.symm.trans ha)
    subst e
    have e2 : G' = G := Option.some.inj (hG'.symm.trans hG)
    subst e2
    exact (holds_says ρ a'.d.st N m row hN (h row hr)).2 (hh row hr)

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.rowSum_value
#print axioms VerifiableInference.Desc.K9L.holds_says
#print axioms VerifiableInference.Desc.K9L.groupHolds_says
