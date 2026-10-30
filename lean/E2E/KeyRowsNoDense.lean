--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyRowsNoDense.lean: THE ROWS THAT THE KEY FILE's FIRST CHAIN LAYS ONTO THE RANGES' GROUP, AND
A SENDING's SAMPLE ROWS, HAVE NO WRITTEN-OUT FACTOR: at all values, WITH NO HYPOTHESIS. The makers'
own texts alone: `rowOfAff`, `rowOfPlane` (Johnson/Desc/First/Look/K3Key.lean) over `Wf.planesAt`
(OnBytes/Iop/Wf.lean), `rowsInOrder` (Johnson/Desc/Key/Link.lean), `sampleRow`
(Johnson/Desc/K1/Own.lean). Steps of the verifier's: NOTHING IS SHOWN OF ANY PROVER.

Why. The law on a proximity test's block from the shape in front (`k12_returns_one`,
Johnson/Desc/K12/Honest/Shape/TestReturnsOne.lean) asks that no row that the test takes in has a
written-out factor. The test on the ranges takes in the lookups' rows and the own message's sample
row.

  `NoDense`, `plainB_of`   no term's vector has a written-out factor, and the row has no form; it
      gives the mark's test on a row (`rowPlainB`, Johnson/Desc/Ground/Shape/Marks.lean).
  `noDense_add`, `noDense_ite`, `noDense_target`, `noDense_fold`   one term more; a choice of two;
      another target; a fold of steps that turn neither terms nor forms.
  ★ `aff_noDense`, ★ `plane_noDense`   the two makers of a lookup's rows.
  ★★ `rows_noDense`   all rows that the sub-protocol behind a lookup's rounds writes.
  ★★ `sample_noDense`   a sending's sample row.

By what. E2E/KeyRowsFit.lean: `addMasks_laws`, `planesAt_eq`, `addTerms_laws`, `termOf_laws` (its
second half: the vector that `Wf.planesAt` lays has no written-out factor, at every vector handed
in), `rowsInOrder_mem`. `LookupShapedRow` of that file is another notion: it asks that a term's vector is
in order, which allows a written-out factor.

Limits. ON THE MAKERS ALONE: that these rows lie in a statement, and that nothing else does, is not
here. FORM ALONE: that a row holds of anything is not touched. Nothing on completeness, on
soundness or on what a view shows.


-/
import E2E.KeyRowsFit
import Johnson.Desc.Ground.Shape.Marks
import Johnson.Desc.K1.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLookup
open OnBytes
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc.K3
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Ground.Sh (rowPlainB)

/-- No term's vector has a written-out factor, and the row has no form. -/
def NoDense (r : Row) : Prop := (∀ t ∈ r.terms.toList, t.v.denseVars = []) ∧ r.forms = #[]

theorem plainB_of {r : Row} (h : NoDense r) : rowPlainB r = true := by
  unfold rowPlainB
  rw [Bool.and_eq_true]
  refine ⟨List.all_eq_true.2 fun t ht => ?_, ?_⟩
  · rw [h.1 t ht]
    rfl
  · rw [h.2]
    rfl

theorem noDense_add {r : Row} (h : NoDense r) (o : ℕ) (part : Part) {v : Tensor}
    (hv : v.denseVars = []) : NoDense (r.add o part v) := by
  refine ⟨fun t ht => ?_, h.2⟩
  have ht' : t ∈ (r.terms.push ⟨o, part, v⟩).toList := ht
  rw [Array.toList_push, List.mem_append, List.mem_singleton] at ht'
  rcases ht' with c | rfl
  · exact h.1 t c
  · exact hv

theorem noDense_ite {c : Prop} [Decidable c] {a b : Row} (ha : NoDense a) (hb : NoDense b) :
    NoDense (if c then a else b) := by
  split
  · exact ha
  · exact hb

theorem noDense_target {r : Row} (h : NoDense r) (y : E) : NoDense { r with target := y } :=
  ⟨h.1, h.2⟩

theorem noDense_fold {α : Type} (f : Row → α → Row)
    (hf : ∀ r x, (f r x).terms = r.terms ∧ (f r x).forms = r.forms) :
    ∀ (l : List α) (r : Row), NoDense r → NoDense (l.foldl f r)
  | [], _, h => h
  | x :: l, r, h =>
    noDense_fold f hf l (f r x) ⟨by rw [(hf r x).1]; exact h.1, by rw [(hf r x).2]; exact h.2⟩

/-- ★ A claim on hidden values alone. -/
theorem aff_noDense {F : Fork} {home : Array Slot} {a : Aff} {r : Row}
    (h : rowOfAff F home a = some r) : rowPlainB r = true := by
  obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨-, a2, -, a4, -⟩ := addMasks_laws (negMasks y.1) { target := subE zeroE y.2 }
  refine plainB_of ⟨fun t ht => ?_, a4⟩
  rw [a2] at ht
  cases ht

/-- ★ A claim that reads the planes. -/
theorem plane_noDense {x : Params.WfPublic} {codes : Codes} {i : ℕ} {F : Fork}
    {home : Array Slot} {turned : Bool} {c : PlaneClaim} {r : Row}
    (h : rowOfPlane (Wf.planesAt x codes i) F home turned c = some r) : rowPlainB r = true := by
  obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 h
  have key : ∀ (tg sc : E) (m : MaskForm),
      rowPlainB ((Wf.planesAt x codes i { target := tg }
        { scalar := sc, pairs := c.pairs }).addMasks m) = true := by
    intro tg sc m
    obtain ⟨-, a2, -, a4, -⟩ := addMasks_laws m
      (Wf.planesAt x codes i { target := tg } { scalar := sc, pairs := c.pairs })
    rw [planesAt_eq] at a2 a4 ⊢
    obtain ⟨-, -, -, b4, -, b6⟩ := addTerms_laws x.messageId
      (termOf x codes i { scalar := sc, pairs := c.pairs }) (blocksOf x codes i) { target := tg }
    refine plainB_of ⟨fun t ht => ?_, a4.trans b4⟩
    rw [a2, b6] at ht
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 (by simpa using ht)
    exact (termOf_laws x codes i b (v := { scalar := sc, pairs := c.pairs })
      (v' := { scalar := sc, pairs := c.pairs }) rfl).2
  cases turned with
  | true => exact key _ _ _
  | false => exact key _ _ _

/-- ★★ **All rows that the sub-protocol behind a lookup's rounds writes.** -/
theorem rows_noDense {x : Params.WfPublic} {codes : Codes} {i : ℕ}
    {tab : List (Bool × ℕ × Bool)} {F : Fork} {home : Array Slot} {cls : List Claim}
    {rows : List OnBytes.Row}
    (h : rowsInOrder (Wf.planesAt x codes i) tab F home cls = some rows) :
    ∀ r ∈ rows, rowPlainB r = true := by
  intro r hr
  obtain ⟨c, -, turned, hrow⟩ := rowsInOrder_mem h r hr
  cases c with
  | inl a => exact aff_noDense hrow
  | inr c => exact plane_noDense hrow

/-- ★★ **A sending's sample row.** -/
theorem sample_noDense (m : VerifiableInference.Desc.K1.Msg) (o : ℕ) (z : List E) (β : E) (i : ℕ)
    (y : E) : rowPlainB (VerifiableInference.Desc.K1.sampleRow m o z β i y) = true := by
  have key : ∀ (r₀ : Row) (c1 c2 : Prop) [Decidable c1] [Decidable c2] (v1 v2 : Tensor),
      NoDense r₀ → v1.denseVars = [] → v2.denseVars = [] →
      rowPlainB { (if c2 then (if c1 then r₀.add o .main v1 else r₀).add o .mask v2
        else (if c1 then r₀.add o .main v1 else r₀)) with target := y } = true := by
    intro r₀ c1 c2 _ _ v1 v2 h0 h1 h2
    exact plainB_of (noDense_target
      (noDense_ite (noDense_add (noDense_ite (noDense_add h0 _ _ h1) h0) _ _ h2)
        (noDense_ite (noDense_add h0 _ _ h1) h0)) y)
  unfold VerifiableInference.Desc.K1.sampleRow
  refine key _ _ _ _ _ ?_ rfl rfl
  refine noDense_fold _ ?_ _ _ ?_
  · intro r x
    exact ⟨rfl, rfl⟩
  · exact ⟨fun t ht => absurd (show t ∈ ([] : List Term) from ht) List.not_mem_nil, rfl⟩

end AtPublicFiles.KeyLookup

#print axioms AtPublicFiles.KeyLookup.plainB_of
#print axioms AtPublicFiles.KeyLookup.noDense_add
#print axioms AtPublicFiles.KeyLookup.noDense_ite
#print axioms AtPublicFiles.KeyLookup.noDense_target
#print axioms AtPublicFiles.KeyLookup.noDense_fold
#print axioms AtPublicFiles.KeyLookup.aff_noDense
#print axioms AtPublicFiles.KeyLookup.plane_noDense
#print axioms AtPublicFiles.KeyLookup.rows_noDense
#print axioms AtPublicFiles.KeyLookup.sample_noDense
