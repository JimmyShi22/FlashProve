-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/SingleFormsLaw.lean: THE FORMS OF SingleForms.lean ARE rowsTail's SINGLE EQUATIONS: the
value of each form, in a world whose entry (array, row, index) is the cell A array row index, is the
gap (tieRow, readRow: OnBytes/Tie/Pv/Tail/EndRows.lean) at A.

Statements and proofs. No routine of `verify-on-bytes` is named. USED OF FILES IN OnBytes/ AND Alg/, ON RECORDS AND
PLAIN DATA ALONE: Reading, World, Aff.value, Ent.value; tieRow, readRow, rowsTail, rowsFrom, readsList, thOf, signOf,
uOf, posOf, tieGap, readGap, Alg.pack, Alg.lane; rowsLedger, rowsLedger_holds; sum_flatMap.
Main names:
  ownWorld A slot: the world whose entry (t, r, c) is the cell A t r c: an array's OWN row r, no virtual row.
  tieAff_value, readAff_value: a tie's form is worth tieRow's gap at A; a read's form readRow's gap.
  **rowsAff_values**: the forms' values, in order, are rowsTail's gaps at A, in order.
  rowsAff_length: as many forms as rowsTail has equations.
  rowsAff_zero_iff: so all forms are worth 0 just where rowsTail's single equations all hold at A.
  rowsAff_ledger: at the cells of a lay's entries m: just where rowsLedger holds on m.
  mem_rowsAff: the list's members are the ties' forms (matrix, row of symbols, combination) and the reads' forms
    (read, combination), and no other: so a test that walks these one by one is a test on the list's members.
  readsP_eq: the list of reads is readsList (rfl).
Limits. The forms carry no exponent: rowsTail's exponents are not said again. slot is free: no form names a
slot. Nothing says that any table A makes the forms 0.

-/
import Johnson.Desc.First.TailClaims.SingleForms
import OnBytes.Tie.Pv.Tail.EndsLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc.First.TailClaims
open OnBytes.Tie.Pv.Tail.Port Finset
open OnBytes.Tie.Pv.Tail (tieGap readGap)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The world of the arrays' own rows: entry (t, r, c) is the cell A t r c. -/
def ownWorld (A : Nat → Nat → Nat → K) (slot : Nat → K) : World K := ⟨slot, A⟩

theorem twoTo_val (n : Nat) : ρ.val (twoTo n) = (2 : K) ^ n := by
  unfold twoTo
  rw [ρ.pow, ρ.add, ρ.one]
  norm_num

theorem signE_val (x : Int) : ρ.val (signE x) = signOf (K := K) x := by
  unfold signE signOf
  split_ifs
  · exact ρ.zero
  · rw [ρ.sub, ρ.zero, ρ.one]; ring
  · exact ρ.one

theorem readsP_eq (tl : HTailF2) (funs : Array HFun) : readsP tl funs = readsList tl funs := rfl

theorem thE_val (tl : HTailF2) (mu k : Nat) (u : Fin tl.tau) (p : Fin k) :
    ρ.val (thE tl mu p u) = thOf (K := K) tl mu k u p := signE_val ρ _

/-! ## Sums over lists -/

theorem sum_range_list (f : ℕ → K) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem sum_filter3 (p : ℕ → Bool) (f : ℕ → K) :
    (((List.range 3).filter p).map f).sum =
      (if p 0 then f 0 else 0) + (if p 1 then f 1 else 0) + (if p 2 then f 2 else 0) := by
  have e : List.range 3 = [0, 1, 2] := rfl
  rw [e]
  cases h0 : p 0 <;> cases h1 : p 1 <;> cases h2 : p 2 <;> simp [List.filter, h0, h1, h2, add_assoc]

theorem foldl_addE {α : Type} (h : α → E) : ∀ (l : List α) (z : E),
    ρ.val (l.foldl (fun a x => addE a (h x)) z) = ρ.val z + (l.map fun x => ρ.val (h x)).sum
  | [], z => by simp
  | x :: l, z => by
    rw [List.foldl_cons, foldl_addE h l, ρ.add, List.map_cons, List.sum_cons]
    ring

variable (A : Nat → Nat → Nat → K) (slot : Nat → K)

theorem digitEnts_sum (tl : HTailF2) (u c0 c1 : Nat) (w : E) :
    ((digitEnts tl u c0 c1 w).map (Ent.value ρ (ownWorld A slot))).sum =
      ρ.val w * (A tl.ix.ZZ u c0 + (2 : K) ^ 10 * A tl.ix.ZZ u c1) := by
  simp only [digitEnts, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Ent.value, ownWorld,
    ρ.mul, twoTo_val]
  ring

/-- The entries under the drawn signs: k of them, in row r of array t, at the indices pos c. -/
theorem symEnts_sum (tl : HTailF2) (mu k t r : Nat) (pos : Nat → Nat) (u : Fin tl.tau) :
    (List.map (Ent.value ρ (ownWorld A slot) ∘ fun c =>
        ({ tree := t, row := r, idx := pos c, coef := subE zeroE (thE tl mu c u) } : Ent))
      (List.range k)).sum = -∑ x : Fin k, thOf tl mu k u x * A t r (pos x) := by
  rw [sum_range_list, ← Fin.sum_univ_eq_sum_range (fun c => (Ent.value ρ (ownWorld A slot) ∘ fun c =>
    ({ tree := t, row := r, idx := pos c, coef := subE zeroE (thE tl mu c u) } : Ent)) c) k,
    ← sum_neg_distrib]
  refine sum_congr rfl fun x _ => ?_
  simp only [Function.comp, Ent.value, ownWorld, ρ.sub, ρ.zero, thE_val ρ tl mu k u x]
  ring

/-- **A tie's form is the tie (tieRow).** -/
theorem tieAff_value (tl : HTailF2) (mu : Nat) (i' : Fin (Alg.symRows (tl.shp.getD mu {}).m))
    (u : Fin tl.tau) :
    (tieAff tl mu i' u).value ρ (ownWorld A slot) = tieRow tl mu i' u A := by
  unfold tieAff Aff.value tieRow tieGap Alg.pack Alg.lane
  simp only [List.map_append, List.sum_append, sum_flatMap, digitEnts_sum, List.map_map, ρ.sub, ρ.zero,
    ρ.mul, twoTo_val, foldl_addE, ρ.pow, sum_filter3, List.map_nil, List.sum_nil]
  rw [symEnts_sum ρ A slot tl mu (tl.shp.getD mu {}).k (tl.gtTree.getD mu 0) i' (fun c => c) u]
  simp only [decide_eq_true_eq, dite_eq_ite]
  push_cast
  split_ifs <;> ring

/-- **A read's form is the equation of the read (readRow).** -/
theorem readAff_value (tl : HTailF2) (x : HFun × Nat) (u : Fin tl.tau) :
    (readAff tl x u).value ρ (ownWorld A slot) = readRow ρ tl x u A := by
  unfold readAff Aff.value readRow readGap
  simp only [List.map_append, List.sum_append, sum_flatMap, digitEnts_sum, List.map_map, ρ.sub, ρ.zero,
    ρ.mul, twoTo_val, foldl_addE, List.map_nil, List.sum_nil]
  rw [symEnts_sum ρ A slot tl x.1.mat (tl.mats.getD x.1.mat {}).k ((tl.ix.U.getD x.1.tree none).getD 0) 0
    (fun d => (tl.tabAt x.1 d x.2).getD 0) u, sum_range_list, sum_range_list,
    ← Fin.sum_univ_eq_sum_range (fun j => ρ.val (x.1.phi.getD j zeroE) *
      (A tl.ix.ZZ u ((tl.zzCol x.1.mat 0 (x.2 * x.1.len)).getD 0 + j) +
        2 ^ 10 * A tl.ix.ZZ u ((tl.zzCol x.1.mat 1 (x.2 * x.1.len)).getD 0 + j))) x.1.len,
    ← Fin.sum_univ_eq_sum_range (fun j => ρ.val (x.1.phi.getD j zeroE)) x.1.len]
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, uOf, posOf]
  ring

/-! ## The lists -/

theorem range_map {β : Type} (n : ℕ) (f : ℕ → β) :
    (List.range n).map f = (List.finRange n).map fun i => f i.val := by
  rw [← List.map_coe_finRange_eq_range (n := n), List.map_map]
  rfl

theorem range_flatMap {β : Type} (n : ℕ) (f : ℕ → List β) :
    (List.range n).flatMap f = (List.finRange n).flatMap fun i => f i.val := by
  rw [← List.map_coe_finRange_eq_range (n := n), List.flatMap_map]

omit [CommRing K] in
theorem rowsFrom_gaps {tau : ℕ} (e : ℕ → ℕ → ℕ) (g : HFun × Nat → Fin tau → Gap K) :
    ∀ (l : List (HFun × Nat)) (q : ℕ), (rowsFrom e g q l).map (fun r => r.2 A) =
      l.flatMap fun x => (List.finRange tau).map fun u => g x u A
  | [], _ => rfl
  | x :: l, q => by
    rw [rowsFrom, List.map_append, rowsFrom_gaps e g l (q + 1), List.flatMap_cons, List.map_map]
    rfl

omit [CommRing K] in
/-- The members of the list: the ties' forms and the reads' forms, and no other. -/
theorem mem_rowsAff (tl : HTailF2) (funs : Array HFun) (a : Aff) :
    a ∈ rowsAff tl funs ↔
      (∃ mu, mu < tl.NM ∧ ∃ i, i < ((tl.shp.getD mu {}).m + 2) / 3 ∧ ∃ u, u < tl.tau ∧
        a = tieAff tl mu i u) ∨
      ∃ x ∈ readsP tl funs, ∃ u, u < tl.tau ∧ a = readAff tl x u := by
  unfold rowsAff
  simp only [List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨mu, hmu, i, hi, u, hu, rfl⟩ | ⟨x, hx, u, hu, rfl⟩)
    · exact Or.inl ⟨mu, hmu, i, hi, u, hu, rfl⟩
    · exact Or.inr ⟨x, hx, u, hu, rfl⟩
  · rintro (⟨mu, hmu, i, hi, u, hu, rfl⟩ | ⟨x, hx, u, hu, rfl⟩)
    · exact Or.inl ⟨mu, hmu, i, hi, u, hu, rfl⟩
    · exact Or.inr ⟨x, hx, u, hu, rfl⟩

/-- **The forms, in order, are rowsTail's single equations, in order**: value for gap. -/
theorem rowsAff_values (tl : HTailF2) (funs : Array HFun) (pc : Nat) :
    (rowsAff tl funs).map (fun a => a.value ρ (ownWorld A slot)) =
      (rowsTail ρ tl funs pc).map fun r => r.2 A := by
  unfold rowsAff rowsTail tieRows tieRowsAt readRowsFrom
  rw [List.map_append, List.map_append, rowsFrom_gaps, readsP_eq]
  congr 1
  · simp only [List.map_flatMap, List.map_map]
    refine congrArg (fun f => (List.range tl.NM).flatMap f) (funext fun mu => ?_)
    rw [range_flatMap]
    refine congrArg (fun f => (List.finRange (Alg.symRows (tl.shp.getD mu {}).m)).flatMap f)
      (funext fun i' => ?_)
    rw [range_map]
    exact List.map_congr_left fun u _ => tieAff_value ρ A slot tl mu i' u
  · simp only [List.map_flatMap, List.map_map]
    refine congrArg (fun f => (readsList tl funs).flatMap f) (funext fun x => ?_)
    rw [range_map]
    exact List.map_congr_left fun u _ => readAff_value ρ A slot tl x u

/-- As many forms as rowsTail has equations. -/
theorem rowsAff_length (tl : HTailF2) (funs : Array HFun) (pc : Nat) :
    (rowsAff tl funs).length = (rowsTail ρ tl funs pc).length := by
  have h := congrArg List.length (rowsAff_values ρ (fun _ _ _ => 0) (fun _ => 0) tl funs pc)
  simpa using h

/-- So: all forms are worth 0 in the world of own rows just where all rowsTail's equations hold. -/
theorem rowsAff_zero_iff (tl : HTailF2) (funs : Array HFun) (pc : Nat) :
    (∀ a ∈ rowsAff tl funs, a.value ρ (ownWorld A slot) = 0) ↔
      ∀ r ∈ rowsTail ρ tl funs pc, r.2 A = 0 := by
  have h := rowsAff_values ρ A slot tl funs pc
  constructor
  · intro H r hr
    have : r.2 A ∈ (rowsTail ρ tl funs pc).map fun r => r.2 A := List.mem_map.2 ⟨r, hr, rfl⟩
    rw [← h] at this
    obtain ⟨a, ha, e⟩ := List.mem_map.1 this
    rw [← e]
    exact H a ha
  · intro H a ha
    have : a.value ρ (ownWorld A slot) ∈ (rowsAff tl funs).map fun a => a.value ρ (ownWorld A slot) :=
      List.mem_map.2 ⟨a, ha, rfl⟩
    rw [h] at this
    obtain ⟨r, hr, e⟩ := List.mem_map.1 this
    rw [← e]
    exact H r hr

/-- At the cells of a lay's entries: just where the ledger rowsLedger of single equations holds. -/
theorem rowsAff_ledger {K J : Type} [Field K] [Fintype J] (ρ : Reading K) (Y : OnBytes.Road.Rows.Lay J)
    (slot : Nat → K) (tl : HTailF2) (funs : Array HFun) (pc : Nat) (m : J → K) :
    (∀ a ∈ rowsAff tl funs, a.value ρ (ownWorld (fun t r c => Y.cellAt m t r c) slot) = 0) ↔
      TWhole.Ledger.Holds (rowsLedger ρ Y tl funs pc) m :=
  (rowsAff_zero_iff ρ _ slot tl funs pc).trans (rowsLedger_holds ρ Y tl funs pc m).symm

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.mem_rowsAff
#print axioms VerifiableInference.Desc.First.TailClaims.Law.rowsAff_length
#print axioms VerifiableInference.Desc.First.TailClaims.Law.rowsAff_ledger
#print axioms VerifiableInference.Desc.First.TailClaims.Law.tieAff_value
#print axioms VerifiableInference.Desc.First.TailClaims.Law.readAff_value
#print axioms VerifiableInference.Desc.First.TailClaims.Law.rowsAff_values
#print axioms VerifiableInference.Desc.First.TailClaims.Law.rowsAff_zero_iff
