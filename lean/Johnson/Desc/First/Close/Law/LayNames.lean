-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/LayNames.lean: when a row "names the group's members alone"
(`NamesMembers`, BatApply.lean, beside this file), at the layout that the verifier's own function
returns. Two definitions, statements and proofs.

`rowSumIn_eq` (BatApply.lean) says that a row, seen through the group, says what it says of the
oracle messages' own tables, if the row meets `NamesMembers`: a condition on the layout's weights,
on place bits and on the row's coefficients. Here it is taken apart into three plain facts (two on
the row, one on the statement), each of which belongs to somebody:
  `RowInGroup ρ S G r`: (off) the row has no coefficient on an oracle message that is no member of
    the group; (absent) it has none on a table that is not there; both are facts on the row, owed by
    whoever lays it. `off_of_contains`: (off) from the same fact said by `Array.contains`, part by
    part.
  `CodesAgree S G L`: a member's table that is there, and is not a kept main table, has as many
    place bits as the group's table: a fact on the statement, laid where a message joins a group.
  `namesMembers_of`: at `S.layout g = some L`, from these two: `NamesMembers ρ S L N r`, at every N.
  `rowSumIn_own`: so there `rowSumIn` is the row's coefficients applied to the two tables of each
    oracle message below N.

Limits. `RowInGroup` and `CodesAgree` are premises: shown here of no row and of no statement.
Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.LayWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.LayLaw

variable {K : Type} [CommRing K] (ρ : Model.Reading K)

/-- The row speaks of the group's members alone, and of tables that are there. -/
structure RowInGroup (S : Statement) (G : Group) (r : Row) : Prop where
  off : ∀ o, G.members.idxOf? o = none → ∀ part e, ρ.val (r.coefficient o part e) = 0
  absent : ∀ o part, S.has o part = false → ∀ e, ρ.val (r.coefficient o part e) = 0

/-- The clause `off`, from the same fact said by `Array.contains` and part by part. -/
theorem off_of_contains (G : Group) (r : Row)
    (h : ∀ o, G.members.contains o = false → ∀ e,
      ρ.val (r.coefficient o .main e) = 0 ∧ ρ.val (r.coefficient o .mask e) = 0) :
    ∀ o, G.members.idxOf? o = none → ∀ part e, ρ.val (r.coefficient o part e) = 0 := by
  intro o ho part e
  have hn : o ∉ G.members := Array.idxOf?_eq_none_iff.1 ho
  have hc : G.members.contains o = false := by
    cases hb : G.members.contains o with
    | false => rfl
    | true => exact absurd (Array.contains_iff_mem.1 hb) hn
  cases part
  · exact (h o hc e).1
  · exact (h o hc e).2

/-- A member's table that is laid on one of the group's tables has that table's place bits. -/
structure CodesAgree (S : Statement) (G : Group) (L : GroupLayout) : Prop where
  main : ∀ o i, G.members.idxOf? o = some i → S.has o .main = true →
    G.kept.getD i false = false → S.placeBits o .main = L.logEll
  mask : ∀ o i, G.members.idxOf? o = some i → S.has o .mask = true →
    S.placeBits o .mask = L.logEllZk

/-- **`NamesMembers` AT THE VERIFIER's OWN LAYOUT, FROM TWO PLAIN FACTS.** -/
theorem namesMembers_of (S : Statement) (g : Nat) (G : Group) (L : GroupLayout)
    (hG : S.groups[g]? = some G) (h : S.layout g = some L) (r : Row) (hr : RowInGroup ρ S G r)
    (hc : CodesAgree S G L) (N : Nat) : NamesMembers ρ S L N r := by
  have hm : L.members = G.members ∧ L.kept = G.kept := by
    rw [layout_eq S g G hG] at h
    obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl⟩
  have hfind : ∀ o, L.find o = G.members.idxOf? o := fun o => by
    unfold GroupLayout.find
    rw [hm.1]
  constructor
  · intro o _
    cases hf : L.find o with
    | none =>
      obtain ⟨a, b, -⟩ := weights_none (K := K) L o hf
      exact Or.inr (Or.inr ⟨b, a, hr.off o ((hfind o).symm.trans hf) .main⟩)
    | some i =>
      obtain ⟨a, b, -⟩ := weights_member (K := K) S g L h o i hf
      cases hk : L.kept.getD i false with
      | true =>
        rw [hk] at a b
        exact Or.inr (Or.inl ⟨by simpa using b, by simpa using a⟩)
      | false =>
        rw [hk] at a b
        cases hh : S.has o .main with
        | true =>
          rw [hh] at b
          refine Or.inl ⟨by simpa using b, by simpa using a, ?_⟩
          exact hc.main o i ((hfind o).symm.trans hf) hh (by rw [← hm.2]; exact hk)
        | false =>
          rw [hh] at b
          exact Or.inr (Or.inr ⟨by simpa using b, by simpa using a, hr.absent o .main hh⟩)
  · intro o _
    cases hf : L.find o with
    | none =>
      obtain ⟨-, -, c⟩ := weights_none (K := K) L o hf
      exact Or.inr ⟨c, hr.off o ((hfind o).symm.trans hf) .mask⟩
    | some i =>
      obtain ⟨-, -, c⟩ := weights_member (K := K) S g L h o i hf
      cases hh : S.has o .mask with
      | true =>
        rw [hh] at c
        exact Or.inl ⟨by simpa using c, hc.mask o i ((hfind o).symm.trans hf) hh⟩
      | false =>
        rw [hh] at c
        exact Or.inr ⟨by simpa using c, hr.absent o .mask hh⟩

/-- So, seen through the group, the row says what it says of the oracle messages' own tables. -/
theorem rowSumIn_own (S : Statement) (g : Nat) (G : Group) (L : GroupLayout)
    (hG : S.groups[g]? = some G) (h : S.layout g = some L) (r : Row) (hr : RowInGroup ρ S G r)
    (hc : CodesAgree S G L) (N : Nat) (tab : Nat → Part → Nat → K) :
    rowSumIn ρ S L N tab r =
      ∑ o ∈ Finset.range N,
        ((∑ J ∈ Finset.range (2 ^ (S.rowBits o .main + S.placeBits o .main)),
            ρ.val (r.coefficient o .main J) * tab o .main J) +
          ∑ j ∈ Finset.range (2 ^ (S.rowBits o .mask + S.placeBits o .mask)),
            ρ.val (r.coefficient o .mask j) * tab o .mask j) :=
  rowSumIn_eq ρ S L N tab r (namesMembers_of ρ S g G L hG h r hr hc N)

end OnBytes.LayLaw

#print axioms OnBytes.LayLaw.off_of_contains
#print axioms OnBytes.LayLaw.namesMembers_of
#print axioms OnBytes.LayLaw.rowSumIn_own
