--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyPadClear.lean: THE ROW (Dot) HAS THE COEFFICIENT 0, AS WORDS, ON EVERY ENTRY OF OMEGA's MAIN
TABLE THAT HOLDS A VECTOR ENTRY BEHIND THE MATRIX's ROWS: AT ALL WELL-FORMED ROW WEIGHTS, WITH OR
WITHOUT A WRITTEN-OUT FACTOR, AND ALL POINTS. So the
ground's one clause on values ("no coefficient on a pad") holds of that row at Omega's copy, whose
pad lies in its main table: in general where the pad lies behind the vector's end, and at the full
size's shapes and codes with no such premise. Statements and proofs; three closed lines by the
kernel. One test of the verifier's: NOTHING IS SHOWN OF ANY PROVER: no completeness.

How. The row's terms on Omega's copy are the row weights, each CUT at the matrix's rows and laid on
the table. The library has, of the values in the field: the summands of a cut add up to 0 at an
index from the length on (`tensorBelow_valG`, Johnson/Desc/K14/Law/TensorsDense.lean), and what a
laid vector has at the index of an entry (`onTable_entryG`, LayDense.lean): both for vectors that
may have a written-out factor. The clause asks for words that are
0, not for a value that is 0: a sum of the program has words below the prime, and on such words the
reading in the field is injective (`toE_inj`, OnBytes/Slice/Field.lean).

What is shown.
  `zeroE_of_val`: an element with words below the prime whose value is 0 is the element 0, as words.
  `sumOn_ok`, `sumOn_val`: a running sum over a row's terms: its words are below the prime; its
    value.
  `mapM_mem`, `sum_flatten_zero`: two small facts on lists.
  `cut_zero`: the summands of one cut, laid on the table, add up to 0 at the index of an entry j
    from the length on.
  **`dot_coefficient_zero`**: for every row that `linDotRow` returns, at row weights that are
    well-formed (the library's `Tensor.ok`), with W's number other than Omega's: the coefficient on
    Omega's main table at the index of entry j is the element 0, as words, for every j from the
    matrix's rows on.
  **`padsClear_of_behind`**: so `PadsClear` (E2E/KeyDotRow.lean) holds where every pad entry of
    every member lies in a mask table or is, on Omega's copy, the index of such an entry.
  **`omega_pad_behind`**: AT THE FULL SIZE's SHAPES AND CODES Omega's one pad entry is the index of
    the vector entry 3145727, which lies behind the matrix's 3076096 rows: by the kernel.
  **`dot_pad_zero_full`**: so there, AT ALL WELL-FORMED ROW WEIGHTS AND ALL POINTS:
    the coefficient on Omega's pad is 0 as words.

Limits.
- "Well-formed" is a premise on the row weights: at most 63 variables; the written-out values lie
  inside their vector; each written-out variable is there, has the pair (1, 1) and is named once.
  The key file's row weights have a written-out factor. That they are well-formed is not shown here
  (of the rows on the table, before the batching: the library's `pendingRow_ok`,
  Johnson/Desc/Key/KeyTensorOk.lean).
- It speaks of Omega's copy. That the other members' pads lie in mask tables is a premise of
  `padsClear_of_behind`.
- The rows (Fold) and SPLIT of the shared chain, which also have terms on Omega's main table, are
  not treated.


-/
import E2E.KeySecondMember
import Johnson.Desc.K14.Law.LayDense
import OnBytes.Tie.Pv.Lookup.PendOkKeys
import OnBytes.Slice.BlkLink

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params
open OnBytes.Model (Reading)

/-- The reading in the library's extension field. -/
local notation "val" => Reading.val Reading.gl

/-- An element with words below the prime whose value is 0 is the element 0, as words. -/
theorem zeroE_of_val (a : E) (ha : okE a = true) (h : val a = 0) : a = zeroE := by
  refine triple_inj (Slice.toE_inj _ _ (by rw [← okE_triple]; exact ha) rfl ?_)
  exact h.trans Reading.gl.zero.symm

/-- A running sum over a row's terms on one entry. -/
def sumOn (o : Nat) (part : Part) (index : Nat) (ts : List Term) (s : E) : E :=
  ts.foldl (fun s t => if t.oracle == o && t.part == part then addE s (t.v.entry index) else s) s

theorem sumOn_ok (o : Nat) (part : Part) (index : Nat) :
    ∀ (ts : List Term) (s : E), okE s = true → okE (sumOn o part index ts s) = true
  | [], _, h => h
  | t :: ts, s, h => by
    show okE (sumOn o part index ts
      (if t.oracle == o && t.part == part then addE s (t.v.entry index) else s)) = true
    refine sumOn_ok o part index ts _ ?_
    split
    · exact Wf.Proved.pendOkKeys_okE_add _ _
    · exact h

theorem sumOn_val (o : Nat) (part : Part) (index : Nat) :
    ∀ (ts : List Term) (s : E), val (sumOn o part index ts s) = val s +
      (ts.map fun t => if t.oracle == o && t.part == part then val (t.v.entry index) else 0).sum
  | [], s => by simp [sumOn]
  | t :: ts, s => by
    show val (sumOn o part index ts
      (if t.oracle == o && t.part == part then addE s (t.v.entry index) else s)) = _
    rw [sumOn_val o part index ts, List.map_cons, List.sum_cons]
    split
    · rw [Reading.gl.add]
      ring
    · ring

theorem mapM_mem {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : List β), l.mapM f = some r → ∀ y ∈ r, ∃ x ∈ l, f x = some y
  | [], r, h, y, hy => by
    rw [List.mapM_nil] at h
    obtain rfl := Option.some.inj h
    cases hy
  | a :: l, r, h, y, hy => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => rw [ha] at h; exact absurd h (by simp)
    | some b =>
      cases hl : l.mapM f with
      | none => rw [ha, hl] at h; exact absurd h (by simp)
      | some bs =>
        rw [ha, hl] at h
        obtain rfl : b :: bs = r := Option.some.inj h
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨a, List.mem_cons_self .., ha⟩
        · obtain ⟨x, hx, e⟩ := mapM_mem f l bs hl y hy
          exact ⟨x, List.mem_cons_of_mem _ hx, e⟩

theorem sum_flatten_zero {α K : Type} [AddCommMonoid K] (F : α → K) :
    ∀ L : List (List α), (∀ l ∈ L, (l.map F).sum = 0) → (L.flatten.map F).sum = 0
  | [], _ => rfl
  | l :: L, h => by
    rw [List.flatten_cons, List.map_append, List.sum_append, h l (List.mem_cons_self ..),
      sum_flatten_zero F L fun m hm => h m (List.mem_cons_of_mem _ hm), add_zero]

/-- **The summands of one cut, laid on the table, add up to 0 at the index of an entry from the
length on.** -/
theorem cut_zero (lay : VectorLay) (v : Tensor) (hd : v.ok = true) (len j : Nat)
    (l : List Tensor) (h : tensorBelow v 0 v.vars len = some l) (hv : v.vars ≤ lay.bits)
    (hj : j < 2 ^ lay.bits) (hlen : len ≤ j) :
    (l.map fun t => val ((lay.onTable t).entry (lay.index j))).sum = 0 := by
  obtain ⟨hin, hdist⟩ := _root_.Desc.K14.Law.dense_of_ok v hd
  have hm := _root_.Desc.K14.Law.tensorBelow_memG v 0 v.vars len l h
  have e : ∀ t ∈ l, val ((lay.onTable t).entry (lay.index j)) =
      if j < 2 ^ v.vars then val (t.entry j) else 0 := fun t ht => by
    rw [_root_.Desc.K14.Law.onTable_entryG Reading.gl lay t
      (by rw [(hm t ht).1, (hm t ht).2]; exact hin) (by rw [(hm t ht).2]; exact hv) j hj,
      (hm t ht).2]
  rw [List.map_congr_left e]
  by_cases c : j < 2 ^ v.vars
  · simp only [if_pos c]
    rw [_root_.Desc.K14.Law.tensorBelow_valG Reading.gl v hdist 0 v.vars len l h j, if_neg]
    rw [Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt c]
    omega
  · simp only [if_neg c]
    simp

/-- **The coefficient on Omega's main table at the index of an entry behind the matrix's rows is the
element 0, as words.** -/
theorem dot_coefficient_zero (S : LinShape) (g : List Tensor) (psi : List E) (omega : Nat)
    (omegaLay : VectorLay) (w : Nat) (wLay : VectorLay) (dot : OnBytes.Row)
    (h : linDotRow S g psi omega omegaLay w wLay = some dot) (hg : ∀ v ∈ g, v.ok = true)
    (hw : w ≠ omega) (hk : S.kRow ≤ omegaLay.bits) (j : Nat) (hj : j < 2 ^ omegaLay.bits)
    (hlen : S.matrixRows ≤ j) : dot.coefficient omega .main (omegaLay.index j) = zeroE := by
  have hf := dot_form S g psi omega omegaLay w wLay dot h
  have hc : dot.coefficient omega .main (omegaLay.index j) =
      sumOn omega .main (omegaLay.index j) dot.terms.toList zeroE := by
    unfold Row.coefficient sumOn
    simp only [hf.units, hf.runs, hf.forms, ← Array.foldl_toList, List.foldl_nil]
  rw [hc]
  refine zeroE_of_val _ (sumOn_ok _ _ _ _ _ rfl) ?_
  rw [sumOn_val, Reading.gl.zero, zero_add]
  unfold linDotRow at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨_, hgd, cut, hcut, hrow⟩ := h
  have hvars : ∀ v ∈ g, v.vars = S.kRow := by
    have t : (psi.length == S.kCol && g.all (·.vars == S.kRow)) = true := by
      by_contra c
      simp [guard, c] at hgd
    intro v hv
    exact beq_iff_eq.1 (List.all_eq_true.1 (Bool.and_eq_true_iff.1 t).2 v hv)
  rw [← hrow, (Slice.addLaid_terms _ _ _ _).1, (Slice.addLaid_terms _ _ _ _).1, List.map_append,
    List.sum_append, List.map_append, List.sum_append]
  have z1 : ((({} : OnBytes.Row).terms.toList).map fun t : Term =>
      if t.oracle == omega && t.part == Part.main then
        val (t.v.entry (omegaLay.index j)) else 0).sum = 0 := rfl
  have z3 : (([Tensor.eq psi (negE oneE)].map fun t => (⟨w, .main, wLay.onTable t⟩ : Term)).map
      fun t : Term => if t.oracle == omega && t.part == Part.main then
        val (t.v.entry (omegaLay.index j)) else 0).sum = 0 := by
    simp [hw]
  have z2 : ((cut.flatten.map fun t => (⟨omega, .main, omegaLay.onTable t⟩ : Term)).map
      fun t : Term => if t.oracle == omega && t.part == Part.main then
        val (t.v.entry (omegaLay.index j)) else 0).sum = 0 := by
    rw [List.map_map]
    have e : ((fun t : Term => if t.oracle == omega && t.part == Part.main then
        val (t.v.entry (omegaLay.index j)) else 0) ∘
        fun t => (⟨omega, .main, omegaLay.onTable t⟩ : Term)) =
        fun t => val ((omegaLay.onTable t).entry (omegaLay.index j)) := by
      funext t
      simp
    rw [e]
    refine sum_flatten_zero _ cut fun l hl => ?_
    obtain ⟨v, hv, hvl⟩ := mapM_mem _ g cut hcut l hl
    rw [← hvars v hv] at hvl
    exact cut_zero omegaLay v (hg v hv) S.matrixRows j l hvl (by rw [hvars v hv]; exact hk) hj hlen
  rw [z1, z2, z3]
  simp

/-- **`PadsClear`**, where every pad entry of every member lies in a mask table or is, on Omega's
copy, the index of a vector entry behind the matrix's rows. -/
theorem padsClear_of_behind (S : LinShape) (g : List Tensor) (psi : List E) (omega : Nat)
    (omegaLay : VectorLay) (w : Nat) (wLay : VectorLay) (dot : OnBytes.Row)
    (h : linDotRow S g psi omega omegaLay w wLay = some dot) (hg : ∀ v ∈ g, v.ok = true)
    (hw : w ≠ omega) (hk : S.kRow ≤ omegaLay.bits) (st : Statement) (G : OnBytes.Group)
    (hp : ∀ o ∈ G.members.toList, ∀ x : OnBytes.Oracle, st.oracles[o]? = some x → ∀ q ∈ x.pad,
      q.1 = .mask ∨ (o = omega ∧ q.1 = .main ∧
        ∃ j, q.2 = omegaLay.index j ∧ j < 2 ^ omegaLay.bits ∧ S.matrixRows ≤ j)) :
    PadsClear st G dot := by
  intro o ho x hx q hq
  rcases hp o ho x hx q hq with c | ⟨rfl, e1, j, e2, hj, hl⟩
  · exact Or.inl c
  · refine Or.inr ?_
    rw [e1, e2]
    exact dot_coefficient_zero S g psi o omegaLay w wLay dot h hg hw hk j hj hl

/-! ## At the full size's shapes and codes -/

/-- **Omega's one pad entry is the index of a vector entry behind the matrix's rows**: by the
kernel. -/
theorem omega_pad_behind : padF SF.omega = [(.main, (linLayOmega CF SF).index 3145727)] ∧
    3145727 < 2 ^ (linLayOmega CF SF).bits ∧ SF.matrixRows ≤ 3145727 ∧
    SF.kRow ≤ (linLayOmega CF SF).bits := by decide +kernel

/-- **At all well-formed row weights and all points, the coefficient on Omega's pad is 0 as
words.** -/
theorem dot_pad_zero_full (g : List Tensor) (psi : List E) (omega w : Nat) (wLay : VectorLay)
    (dot : OnBytes.Row) (h : linDotRow SF g psi omega (linLayOmega CF SF) w wLay = some dot)
    (hg : ∀ v ∈ g, v.ok = true) (hw : w ≠ omega) :
    ∀ q ∈ padF SF.omega, dot.coefficient omega q.1 q.2 = zeroE := by
  obtain ⟨e, h1, h2, h3⟩ := omega_pad_behind
  intro q hq
  rw [e] at hq
  obtain rfl := List.mem_singleton.1 hq
  exact dot_coefficient_zero SF g psi omega _ w wLay dot h hg hw h3 _ h1 h2

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.zeroE_of_val
#print axioms AtPublicFiles.AtFiles.sumOn_ok
#print axioms AtPublicFiles.AtFiles.sumOn_val
#print axioms AtPublicFiles.AtFiles.mapM_mem
#print axioms AtPublicFiles.AtFiles.sum_flatten_zero
#print axioms AtPublicFiles.AtFiles.cut_zero
#print axioms AtPublicFiles.AtFiles.dot_coefficient_zero
#print axioms AtPublicFiles.AtFiles.padsClear_of_behind
#print axioms AtPublicFiles.AtFiles.omega_pad_behind
#print axioms AtPublicFiles.AtFiles.dot_pad_zero_full
