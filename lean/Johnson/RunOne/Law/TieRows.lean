-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieRows.lean: THE TABLE'S
"A ROW HOLDS", IN MACHINE ELEMENTS, AGAINST Means.Says, FOR LISTS OF ROWS; AND THE ONE PREMISE OF
THAT IFF FOR THE ROWS THAT A LOOKUP'S LAYER MAKES. rowHolds_iff_says
(Johnson/Desc/Key/RowHoldsSays.lean) asks of a row OffTables: it reads 0 on every table that the
statement has not.

Main names:
  allSay_iff: for a list of rows with OffTables: all hold (RowHolds at "read alike") ⇔ AllSay at the
    words read.
  says_words, allSay_words: Says and AllSay at two families of words that agree on the statement's
    tables.
  off_bare, off_addMasks, off_planesAt: a bare row; mask entries inside the statement's mask tables
    added; a vector on the planes added, where the statement has the own message's main table.
  off_rowOfAff, off_rowOfPlane, off_group: the rows of a lookup's layer have OffTables.

Object: rowOfAff, rowOfPlane, groupRows (Johnson/Desc/First/Look/K3Key.lean); RowHolds; Means.Says.
User: TieEarly.lean calls allSay_iff; OffWalk.lean calls off_rowOfAff and off_rowOfPlane.
Letters: St, a statement · x, codes, i: the ranges' record, the codes, a lookup's number · F, homeA:
a ledger and a table of homes.

Limits. OffTables of the layer's rows is had where their making is in hand (groupRows' yes); that it
rides with the rows in a record through later blocks is not shown. Nothing on soundness.

-/
import Johnson.Desc.Key.RowHoldsSays
import Johnson.Desc.First.Look.KeyLaw.GroupSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.TieRows
open OnBytes OnBytes.Slice
open OnBytes.Model (Reading Fork Aff)
open OnBytes.Params (WfPublic)
open VerifiableInference.Desc.K3 VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (RowHolds OffTables rowHolds_iff_says)

/-- **For a list of rows: all hold ⇔ AllSay at the words read.** -/
theorem allSay_iff (St : Statement) (val : ℕ → Part → ℕ → E) (rs : List Row)
    (hoff : ∀ r ∈ rs, OffTables Reading.gl St r) :
    (∀ r ∈ rs, RowHolds (fun a b => readE a = readE b) St val r) ↔
      Means.AllSay Reading.gl St rs fun o pt i => readE (val o pt i) :=
  forall_congr' fun r => forall_congr' fun hr => rowHolds_iff_says Reading.gl St val r (hoff r hr)

/-- Says at two families of words that agree on the statement's tables. -/
theorem says_words (St : Statement) (r : Row) (w w' : Means.Words GE)
    (h : ∀ o < St.oracles.size, ∀ pt, ∀ i < Means.tableSize St o pt, w o pt i = w' o pt i) :
    Means.Says Reading.gl St r w ↔ Means.Says Reading.gl St r w' := by
  unfold Means.Says Means.value
  have e : ∀ o ∈ Finset.range St.oracles.size,
      Means.onTable Reading.gl St r w o .main + Means.onTable Reading.gl St r w o .mask =
      Means.onTable Reading.gl St r w' o .main + Means.onTable Reading.gl St r w' o .mask := by
    intro o ho
    have one : ∀ pt, Means.onTable Reading.gl St r w o pt = Means.onTable Reading.gl St r w' o pt :=
      fun pt => by
        unfold Means.onTable
        exact Finset.sum_congr rfl fun i hi => by
          rw [h o (Finset.mem_range.1 ho) pt i (Finset.mem_range.1 hi)]
    rw [one, one]
  rw [Finset.sum_congr rfl e]

theorem allSay_words (St : Statement) (rs : List Row) (w w' : Means.Words GE)
    (h : ∀ o < St.oracles.size, ∀ pt, ∀ i < Means.tableSize St o pt, w o pt i = w' o pt i) :
    Means.AllSay Reading.gl St rs w ↔ Means.AllSay Reading.gl St rs w' :=
  forall_congr' fun r => forall_congr' fun _ => says_words St r w w' h

variable {St : Statement}

theorem off_bare (t : E) : OffTables Reading.gl St ({ target := t } : Row) :=
  fun o pt i _ => Lk6.Mid.rd_bare t o pt i

/-- A table with an index inside it is a table that the statement has. -/
theorem has_of_lt {o : ℕ} {pt : Part} {i : ℕ} (h : i < Means.tableSize St o pt) :
    St.has o pt = true := by
  unfold Means.tableSize at h
  by_contra hc
  rw [if_neg hc] at h
  exact Nat.not_lt_zero _ h

theorem off_addMasks {R : Row} (hR : OffTables Reading.gl St R) (m : MaskForm)
    (hm : ∀ p ∈ m, p.1.index < Means.tableSize St p.1.oracle .mask) :
    OffTables Reading.gl St (R.addMasks m) := by
  intro o pt i hh
  show readE ((R.addMasks m).coefficient o pt i) = 0
  rw [Lk6.Mid.rd_addMasks, show readE (R.coefficient o pt i) = 0 from hR o pt i hh, zero_add]
  refine List.sum_eq_zero fun y hy => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
  refine if_neg fun hc => ?_
  have := has_of_lt (hm p hp)
  rw [hc.1, hc.2, hh] at this
  cases this

theorem off_planesAt (x : WfPublic) (codes : Codes) (i : ℕ) {R : Row}
    (hR : OffTables Reading.gl St R) (hx : St.has x.messageId .main = true) (v : Tensor) :
    OffTables Reading.gl St (Wf.planesAt x codes i R v) := by
  intro o pt idx hh
  rw [Planes.planesAt_coefficient Reading.gl, hR o pt idx hh, zero_add]
  refine if_neg fun hc => ?_
  rw [hc.1, hc.2, hh] at hx
  cases hx

variable {F : Fork} {homeA : Array Slot}
  (hIn : ∀ s ∈ homeA.toList, s.index < Means.tableSize St s.oracle .mask)
include hIn

theorem off_rowOfAff {a : Aff} {R : Row} (h : rowOfAff F homeA a = some R) :
    OffTables Reading.gl St R := by
  unfold rowOfAff at h
  cases hy : maskSide F homeA a with
  | none => rw [hy] at h; cases h
  | some y =>
    rw [hy] at h
    obtain rfl := Option.some.inj h
    exact off_addMasks (off_bare _) _ fun p hp =>
      hIn _ (negMasks_slots (maskSide_slots hy) p hp)

theorem off_rowOfPlane (x : WfPublic) (codes : Codes) (i : ℕ)
    (hx : St.has x.messageId .main = true) (turned : Bool) {c : PlaneClaim} {R : Row}
    (h : rowOfPlane (Wf.planesAt x codes i) F homeA turned c = some R) :
    OffTables Reading.gl St R := by
  unfold rowOfPlane at h
  cases hy : maskSide F homeA c.lead with
  | none => rw [hy] at h; cases h
  | some y =>
    rw [hy] at h
    obtain rfl := Option.some.inj h
    cases turned with
    | true =>
      exact off_addMasks (off_planesAt x codes i (off_bare _) hx _) _ fun p hp =>
        hIn _ (negMasks_slots (maskSide_slots hy) p hp)
    | false =>
      exact off_addMasks (off_planesAt x codes i (off_bare _) hx _) _ fun p hp =>
        hIn _ (maskSide_slots hy p hp)

omit hIn in
/-- Every member of a list made member by member comes of a member. -/
theorem mapM_mem {α β : Type} (f : α → Option β) : ∀ (os : List α) (fr : List β),
    os.mapM f = some fr → ∀ R ∈ fr, ∃ a ∈ os, f a = some R
  | [], fr, h, R, hR => by
    cases h
    cases hR
  | a :: os, fr, h, R, hR => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some Ra =>
      cases hos : os.mapM f with
      | none => simp [ha, hos] at h
      | some fr' =>
        simp only [ha, hos, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        rcases List.mem_cons.1 hR with rfl | hR'
        · exact ⟨a, List.mem_cons_self, ha⟩
        · obtain ⟨b, hb, e⟩ := mapM_mem f os fr' hos R hR'
          exact ⟨b, List.mem_cons_of_mem _ hb, e⟩

/-- **The rows of a lookup's layer have OffTables.** -/
theorem off_group (x : WfPublic) (codes : Codes) (i : ℕ) (hx : St.has x.messageId .main = true)
    {objects : List Aff} {planes : List PlaneClaim} {rows : List Row}
    (h : groupRows (Wf.planesAt x codes i) F homeA objects planes = some rows) :
    ∀ R ∈ rows, OffTables Reading.gl St R := by
  have aff := @off_rowOfAff St F homeA hIn
  have pln := @off_rowOfPlane St F homeA hIn x codes i hx
  unfold groupRows at h
  match planes, hg : objects.getLast?, h with
  | [leaves, value, counts], some bits, h =>
    simp only at h
    cases h0 : objects.dropLast.mapM (rowOfAff F homeA) with
    | none => simp [h0] at h
    | some front =>
      cases h1 : rowOfPlane (Wf.planesAt x codes i) F homeA true leaves with
      | none => simp [h0, h1] at h
      | some r1 =>
        cases h2 : rowOfAff F homeA bits with
        | none => simp [h0, h1, h2] at h
        | some r2 =>
          cases h3 : rowOfPlane (Wf.planesAt x codes i) F homeA false value with
          | none => simp [h0, h1, h2, h3] at h
          | some r3 =>
            cases h4 : rowOfPlane (Wf.planesAt x codes i) F homeA true counts with
            | none => simp [h0, h1, h2, h3, h4] at h
            | some r4 =>
              simp only [h0, h1, h2, h3, h4, Option.bind_eq_bind, Option.bind_some,
                Option.pure_def, Option.some.injEq] at h
              subst h
              intro R hR
              rcases List.mem_append.1 hR with hf | hl
              · obtain ⟨a, -, ha⟩ := mapM_mem _ _ _ h0 R hf
                exact aff ha
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
                rcases hl with rfl | rfl | rfl | rfl
                · exact pln true h1
                · exact aff h2
                · exact pln false h3
                · exact pln true h4

end Johnson.RunOne.Law.TieRows

#print axioms Johnson.RunOne.Law.TieRows.allSay_iff
#print axioms Johnson.RunOne.Law.TieRows.allSay_words
#print axioms Johnson.RunOne.Law.TieRows.off_group
