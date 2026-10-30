--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/RowsFit.lean: WHEN THE STEP THAT ADDS OPEN ROWS TO A GROUP ACCEPTS (`addRowP`, `addRowsP`,
Johnson/Desc/First/Base/Ground.lean): the general half. It names no file's protocol. Statements and
proofs; nothing is evaluated.

Why. Whoever shows that a verifier accepts an honest run has to pass that step wherever a
sub-protocol lays rows onto a group. Its test on a row (`rowL`) has eight clauses. The last is
headed «ON VALUES: no coefficient on a pad». For rows of the usual make it holds BY FORM, whatever
was sent: the row's summands do not lie where a member's pad lies.

What is shown.
  `rowL_withRow`: a further open row of the group turns no clause of the test on a row.
  **`addRows_of_fits`**: rows that each pass the test at the statement in front are all added.
  **`coefficient_zero`**: a row's coefficient (`Row.coefficient`, OnBytes/Iop/Ground.lean) on an
    entry is the element 0, as words, if the row has no term and no run on that table, no single
    entry at that index, and no form there (a form lies on a main table).
  **`noPad_of_zero`**: the eighth clause, from «the coefficient is 0 on every entry of every
    member's pad».
  `padFirst codes s`, **`pad_above`**: the pad of a message WITH MASK ROWS lies in its mask table,
    from the index `padFirst` on.
  `ShapeIs`, `take_below`, **`takes_below`**: under the library's `LedgerAt`
    (Johnson/Desc/K13/Law/LedgerWithin.lean): EVERY INDEX THAT A MESSAGE'S LEDGER OF MASK ENTRIES
    HANDS OUT LIES BELOW `padFirst`. By the library's `takenNo_eq` (OnBytes/Iop/LedgerPlaces.lean)
    and `freeAt_below_pad` (Fmt/PlacesLaws.lean).

So, for a member with mask rows: a row whose terms, runs and forms lie on main tables, and whose
single entries on that member's mask table are entries that its ledger handed out, has the
coefficient 0 on its pad.

Limits.
- A MEMBER WITHOUT MASK ROWS HAS ITS PAD IN ITS MAIN TABLE. There a term does add, and the clause is
  on values in earnest: that a vector ends in front of the pad is not treated here.
- The other seven clauses are not treated here.
- That a state's ledger has `LedgerAt` is a premise (E2E/KeyLedgers.lean carries it in the key
  file's first chain).
- Nothing on completeness as such, on soundness, or on what a view shows.


-/
import Johnson.Desc.First.Base.Ground
import Johnson.Desc.K13.Law.LedgerWithin

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.RowsFit
open OnBytes
open _root_.Desc.Plain (DState)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Own (placeFits allZero)

section
variable {L : Type}

/-! ## 1. A further open row turns no test on a row -/

theorem rowL_withRow (S : Statement) (g : ℕ) (r row : Row) :
    rowL (Slice.withRow S g r) g row = rowL S g row := by
  have hG : (Slice.withRow S g r).groups[g]? =
      (S.groups[g]?).map fun G => { G with rows := G.rows.push r } := by
    show (S.groups.modify g _)[g]? = _
    rw [Array.getElem?_modify, if_pos rfl]
  unfold rowL
  rw [hG]
  cases S.groups[g]? with
  | none => rfl
  | some G => rfl

theorem rowsFrom_of_fits (g : ℕ) : ∀ (rows : List Row) (d : DState L),
    (∀ row ∈ rows, ok (rowL d.st g row) = true) → (addRowsFrom g rows d).isSome = true
  | [], _, _ => rfl
  | row :: l, d, h => by
    unfold addRowsFrom addRowP
    rw [if_pos (h row (List.mem_cons_self ..))]
    exact rowsFrom_of_fits g l _ fun r hr => by
      show ok (rowL (Slice.withRow d.st g row) g r) = true
      rw [rowL_withRow]
      exact h r (List.mem_cons_of_mem _ hr)

/-- **Rows that each fit the statement in front are all added.** -/
theorem addRows_of_fits {d : DState L} {g : ℕ} {rows : List Row} {G : OnBytes.Group}
    (hG : d.st.groups[g]? = some G) (hr : G.inRun = false)
    (h : ∀ row ∈ rows, ok (rowL d.st g row) = true) : (addRowsP d g rows).isSome = true := by
  unfold addRowsP
  have h0 : ok (rowsL d.st g) = true := by simp [ok, rowsL, has, hG, hr]
  rw [if_pos h0]
  exact rowsFrom_of_fits g rows d h

/-! ## 2. A row's coefficient where nothing of it lies -/

theorem fold_keep {α : Type} (p : α → Bool) (f : E → α → E) : ∀ (l : List α) (s : E),
    (∀ a ∈ l, p a = false) → l.foldl (fun s a => if p a then f s a else s) s = s
  | [], _, _ => rfl
  | a :: l, s, h => by
    rw [List.foldl_cons, h a (List.mem_cons_self ..)]
    exact fold_keep p f l s fun b hb => h b (List.mem_cons_of_mem _ hb)

/-- **The coefficient is the element 0, as words, on an entry where no summand of the row lies**: no
term and no run on that table; no single entry at that index; no form, or the table is a mask table.
-/
theorem coefficient_zero {r : Row} {o : ℕ} {part : Part} {index : ℕ}
    (ht : ∀ t ∈ r.terms.toList, (t.oracle == o && t.part == part) = false)
    (hu : ∀ u ∈ r.units.toList, (u.oracle == o && u.part == part && u.index == index) = false)
    (hw : ∀ w ∈ r.runs.toList, (w.oracle == o && w.part == part) = false)
    (hf : ∀ f ∈ r.forms.toList, (f.oracle == o && part == .main) = false) :
    r.coefficient o part index = zeroE := by
  unfold Row.coefficient
  simp only [← Array.foldl_toList]
  rw [fold_keep (fun t : Term => t.oracle == o && t.part == part)
      (fun s t => addE s (t.v.entry index)) _ _ ht,
    fold_keep (fun u : Single => u.oracle == o && u.part == part && u.index == index)
      (fun s u => addE s u.coeff) _ _ hu,
    fold_keep (fun w : Run => w.oracle == o && w.part == part && decide (w.first ≤ index) &&
        decide (0 < w.step) && (index - w.first) % w.step == 0 &&
        decide ((index - w.first) / w.step < w.coeffs.size))
      (fun s w => addE s (w.coeffs.get ((index - w.first) / w.step))) _ _
      (fun w hw' => by
        beta_reduce
        rw [hw w hw']
        rfl),
    fold_keep (fun f : MainForm => f.oracle == o && part == .main)
      (fun s f => addE s (f.c.entry index)) _ _ hf]

/-- **The test «no coefficient on a pad»** holds where the row's coefficient is the element 0, as
words, on every entry of every member's pad. -/
theorem noPad_of_zero {S : Statement} {G : OnBytes.Group} {row : Row}
    (h : ∀ o ∈ G.members.toList, ∀ x, S.oracles[o]? = some x → ∀ q ∈ x.pad,
      row.coefficient o q.1 q.2 = zeroE) :
    (G.members.all fun o =>
      ((S.oracles[o]?).map (·.pad)).getD [] |>.all fun q =>
        allZero (row.coefficient o q.1 q.2)) = true := by
  rw [Array.all_eq_true_iff_forall_mem]
  intro o ho
  cases hx : S.oracles[o]? with
  | none => rfl
  | some x =>
    show (x.pad.all fun q => allZero (row.coefficient o q.1 q.2)) = true
    rw [List.all_eq_true]
    intro q hq
    rw [h o (Array.mem_toList_iff.2 ho) x hx q hq]
    rfl

/-! ## 3. What a ledger hands out lies below its message's pad -/

/-- The index of the first entry of the pad of a message with mask rows, in its mask table. -/
def padFirst (codes : Codes) (s : OracleShape) : ℕ :=
  (s.maskRows - 1) +
    ((codes.mask.getD s.maskCode default).ell - s.answers) * 2 ^ ceilLog2 s.maskRows

/-- **The pad of a message with mask rows lies in its mask table, from that index on.** -/
theorem pad_above {codes : Codes} {s : OracleShape} {places : List PadPlace} (hm : 0 < s.maskRows)
    (h : VerifiableInference.Desc.Own.padMade codes s = some places) :
    ∀ q ∈ places, q.part = Part.mask ∧ padFirst codes s ≤ q.index := by
  intro q hq
  unfold VerifiableInference.Desc.Own.padMade at h
  simp only [Send.cube, hm, decide_true, if_true, Bool.true_or, Nat.one_mul] at h
  split at h
  · cases h
  · obtain rfl := Option.some.inj h
    simp only [List.mem_flatMap, List.mem_map, List.mem_range] at hq
    obtain ⟨i, _, t, ht, rfl⟩ := hq
    refine ⟨rfl, ?_⟩
    show _ ≤ (s.maskRows - 1) + _ * 2 ^ ceilLog2 s.maskRows
    refine Nat.add_le_add_left (Nat.mul_le_mul_right _ ?_) _
    omega

open VerifiableInference.Desc.K13.Law (LedgerAt takenNo_at free_is takeMaskP_within)
open Fmt.Places (entryNo freeAt freeCount freeAt_below_pad)

/-- Message o is there, of the shape s, under the codes cs. -/
def ShapeIs (d : DState L) (o : ℕ) (cs : Codes) (s : OracleShape) : Prop :=
  d.st.codes = cs ∧ ∃ x, d.st.oracles[o]? = some x ∧ x.shape = s

theorem take_below {d d' : DState L} {o k n : ℕ} {cs : Codes} {s : OracleShape}
    (h : LedgerAt d.st o k) (hs : ShapeIs d o cs s) (e : takeMaskP d o = some (n, d')) :
    n < padFirst cs s ∧ ShapeIs d' o cs s := by
  obtain ⟨x, l, hx, hl, hm, ha, hr, hq, hleft, hnext⟩ := h
  obtain ⟨rfl, x', hx', rfl⟩ := hs
  obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
  unfold takeMaskP at e
  split at e
  · rename_i hok
    have h0 : 0 < l.left := by
      simp only [ok, takeMaskL, hx, hl, has, List.all_cons, List.all_nil, Bool.and_true,
        Bool.and_eq_true, Option.bind_some, Option.map_some, Option.getD_some,
        decide_eq_true_eq] at hok
      exact hok.2.2.2
    rw [hx] at e
    simp only [Option.bind_some, hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    let l₁ : Ledger :=
      { l with
        next := Blk.nextRealRow l.rows l.logRows (2 ^ l.logRows) l.next + 1
        left := l.left - 1 }
    refine ⟨?_, rfl, { x with ledger := some l₁ }, ?_, rfl⟩
    · rw [hr, hq, hnext]
      have e1 : Blk.nextRealRow x.shape.maskRows (ceilLog2 x.shape.maskRows)
          (2 ^ ceilLog2 x.shape.maskRows)
          (VerifiableInference.Desc.K13.Law.nextAt x.shape.maskRows k) =
          takenNo x.shape.maskRows k := takenNo_at x.shape.maskRows k
      rw [e1, takenNo_eq hm k]
      rw [free_is] at hleft
      have hk : k < freeCount x.shape.maskRows
          (d.st.codes.mask.getD x.shape.maskCode default).ell x.shape.answers := by omega
      have hse : x.shape.answers ≤ (d.st.codes.mask.getD x.shape.maskCode default).ell := by
        by_contra hn
        unfold freeCount at hk
        rw [if_pos (Or.inr (by omega))] at hk
        exact absurd hk (Nat.not_lt_zero _)
      have := (freeAt_below_pad hm hse k).2 hk
      unfold padFirst
      rw [Nat.mul_comm]
      exact this
    · show (d.st.oracles.modify o _)[o]? = _
      rw [Array.getElem?_modify, if_pos rfl, hx]
      rfl
  · cases e

theorem takeInto_below {o : ℕ} {cs : Codes} {s : OracleShape} : ∀ (n k : ℕ) (d d' : DState L)
    (acc : Array ℕ) (l : List ℕ), LedgerAt d.st o k → ShapeIs d o cs s →
    (∀ i ∈ acc.toList, i < padFirst cs s) → takeMasksInto o n d acc = some (l, d') →
    ∀ i ∈ l, i < padFirst cs s
  | 0, _, d, d', acc, l, _, _, ha, e => by
    have e' : some (acc.toList, d) = some (l, d') := e
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj e')
    exact ha
  | n + 1, k, d, d', acc, l, h, hs, ha, e => by
    unfold takeMasksInto at e
    cases ht : takeMaskP d o with
    | none => rw [ht] at e; cases e
    | some y =>
      obtain ⟨i, d₁⟩ := y
      rw [ht] at e
      obtain ⟨b1, s1⟩ := take_below h hs ht
      refine takeInto_below n (k + 1) d₁ d' (acc.push i) l (takeMaskP_within h ht).2.2 s1 ?_ e
      intro j hj
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hj
      rcases hj with hj | rfl
      · exact ha j hj
      · exact b1

/-- **Every index that a ledger hands out lies below the first entry of its message's pad.** -/
theorem takes_below {d d' : DState L} {o k n : ℕ} {cs : Codes} {s : OracleShape} {l : List ℕ}
    (h : LedgerAt d.st o k) (hs : ShapeIs d o cs s) (e : takeMasksP d o n = some (l, d')) :
    ∀ i ∈ l, i < padFirst cs s :=
  takeInto_below n k d d' #[] l h hs (fun _ hi => by cases hi) e

end

end AtPublicFiles.RowsFit

#print axioms AtPublicFiles.RowsFit.rowL_withRow
#print axioms AtPublicFiles.RowsFit.addRows_of_fits
#print axioms AtPublicFiles.RowsFit.coefficient_zero
#print axioms AtPublicFiles.RowsFit.noPad_of_zero
#print axioms AtPublicFiles.RowsFit.pad_above
#print axioms AtPublicFiles.RowsFit.takes_below
