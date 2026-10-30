-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/EvalProofs.lean: the proofs of the statements of
Johnson/Desc/K13/Law/Eval.lean.

The coefficients of (Eval) in closed form are the library's (`read_eval`,
OnBytes/Slice/BlkLinRead.lean); that a layout's two functions undo each other too (`entryAt_index`,
`index_entryAt`, OnBytes/Slice/BlkCross.lean).
Main names: `single_sum`, `masks_sum`, `main_sum`, `eqW_rd`; `eval_value`, `eval_back`.
Used of `verify-on-bytes`: what Johnson/Desc/K13/Law/Eval.lean names.

What is not claimed. What Johnson/Desc/K13/Law/Eval.lean says is not claimed.

-/
import Johnson.Desc.K13.Law.Eval

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Params (LinShape)
open OnBytes.Means (Words Says value tableSize)
open Johnson.L5.Layers (rd)

/-- A coefficient on one mask entry that the statement has. -/
theorem single_sum (St : Statement) (m : Words GE) (o₀ i₀ : ℕ) (c : GE)
    (h1 : o₀ < St.oracles.size) (h2 : i₀ < tableSize St o₀ .mask) :
    ∑ o ∈ Finset.range St.oracles.size, ∑ i ∈ Finset.range (tableSize St o .mask),
      (if o₀ = o then (if i₀ = i then c else 0) else 0) * m o .mask i =
    c * m o₀ .mask i₀ := by
  rw [Finset.sum_eq_single o₀, Finset.sum_eq_single i₀]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · intro h
    exact absurd (Finset.mem_range.2 h2) h
  · intro o _ ho
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [Ne.symm ho]
  · intro h
    exact absurd (Finset.mem_range.2 h1) h

/-- A mask form whose entries the statement has. -/
theorem masks_sum (St : Statement) (m : Words GE) : ∀ M : MaskForm,
    (∀ t ∈ M, t.1.oracle < St.oracles.size ∧ t.1.index < tableSize St t.1.oracle .mask) →
    ∑ o ∈ Finset.range St.oracles.size, ∑ i ∈ Finset.range (tableSize St o .mask),
      ((readForm M).map fun e =>
        if e.1.oracle = o then (if e.1.index = i then e.2 else 0)
        else 0).sum * m o .mask i = formVal ρg (maskOf m) M
  | [], _ => by simp [readForm, formVal]
  | t :: M, h => by
    have ih := masks_sum St m M fun u hu => h u (List.mem_cons_of_mem _ hu)
    have h0 := h t List.mem_cons_self
    have e1 := single_sum St m t.1.oracle t.1.index (readE t.2) h0.1 h0.2
    simp only [readForm, List.map_cons, List.sum_cons, add_mul, Finset.sum_add_distrib, formVal]
      at ih e1 ⊢
    rw [e1, ih]
    rfl

/-- A vector that lies in the main table of one oracle message. -/
theorem main_sum (St : Statement) (m : Words GE) (w : ℕ) (lay : VectorLay) (f : ℕ → GE) (k : ℕ)
    (hk : k ≤ lay.bits) (hw : w < St.oracles.size) (hs : tableSize St w .main = 2 ^ lay.bits)
    (hf : ∀ e, 2 ^ k ≤ e → f e = 0) :
    ∑ o ∈ Finset.range St.oracles.size, ∑ i ∈ Finset.range (tableSize St o .main),
      (if (w == o && Part.main == Part.main) = true then laid lay f i else 0) * m o .main i =
    ∑ e ∈ Finset.range (2 ^ k), f e * m w .main (lay.index e) := by
  rw [Finset.sum_eq_single w]
  · rw [hs]
    have e1 : ∑ i ∈ Finset.range (2 ^ lay.bits),
        (if (w == w && Part.main == Part.main) = true then laid lay f i else 0) * m w .main i =
        ∑ e ∈ Finset.range (2 ^ lay.bits), f e * m w .main (lay.index e) := by
      refine Finset.sum_nbij' lay.entryAt lay.index ?_ ?_ ?_ ?_ ?_
      · intro i hi
        exact Finset.mem_range.2 (entryAt_lt lay i (Finset.mem_range.1 hi))
      · intro e he
        exact Finset.mem_range.2 (index_lt lay e (Finset.mem_range.1 he))
      · intro i hi
        exact index_entryAt lay i (Finset.mem_range.1 hi)
      · intro e he
        exact entryAt_index lay e (Finset.mem_range.1 he)
      · intro i hi
        have hi' := Finset.mem_range.1 hi
        simp only [beq_self_eq_true, Bool.and_self, if_true]
        unfold laid
        rw [Nat.mod_eq_of_lt hi', index_entryAt lay i hi']
    rw [e1]
    refine (Finset.sum_subset ?_ ?_).symm
    · intro e he
      exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 he)
        (Nat.pow_le_pow_right (by norm_num) hk))
    · intro e _ he
      rw [hf e (not_lt.1 fun h => he (Finset.mem_range.2 h)), zero_mul]
  · intro o _ ho
    refine Finset.sum_eq_zero fun i _ => ?_
    have : (w == o) = false := beq_false_of_ne (Ne.symm ho)
    simp [this]
  · intro h
    exact absurd (Finset.mem_range.2 hw) h

/-- The weight of a column at the claim's point, in the two ways of writing it. -/
theorem eqW_rd (k : ℕ) (psi : List E) (e : ℕ) :
    eqW k (fun t => (psi.map readE).getD t 0) e = Alg.eqk (rd ρg k psi) (lowBits k e) := by
  unfold eqW
  congr 1
  funext t
  show (psi.map ρg.val).getD t 0 = ρg.val (psi.getD t zeroE)
  rw [← ρg.zero, List.getD_map]

/-- What the row (Eval) is worth on words. -/
theorem eval_value : Spec.eval_value := by
  intro S row w lay r St m hb hr hin
  obtain ⟨_, hread⟩ := read_eval S row w lay r hb hr
  have hlen : (row.psi.map readE).length = S.kCol := by
    rw [List.length_map]
    exact (linEvalRow_inv S _ w lay r hr).1
  have hc : ∀ o part i, ρg.val (r.coefficient o part i) =
      (LinF.eval lay w (row.psi.map readE) (readForm row.masks) (readE row.target)).coef o part i :=
    fun o part i => congrArg (fun q : RowF => q.coef o part i) hread
  have hmain : ∀ o i, ρg.val (r.coefficient o .main i) =
      if (w == o && Part.main == Part.main) = true then
        laid lay (fun e => if e < 2 ^ S.kCol then
          eqW S.kCol (fun t => (row.psi.map readE).getD t 0) e else 0) i
      else 0 := by
    intro o i
    rw [hc]
    unfold LinF.eval RowF.ofMasks
    simp [hlen]
  have hmask : ∀ o i, ρg.val (r.coefficient o .mask i) =
      ((readForm row.masks).map fun e =>
        if e.1.oracle = o then (if e.1.index = i then e.2 else 0)
        else 0).sum := by
    intro o i
    rw [hc]
    unfold LinF.eval RowF.ofMasks
    simp
  unfold value OnBytes.Means.onTable
  rw [Finset.sum_add_distrib]
  simp only [hmain, hmask]
  rw [main_sum St m w lay _ S.kCol hb hin.there hin.size
    (fun e he => if_neg (not_lt.2 he)), masks_sum St m row.masks hin.masks]
  congr 1
  refine Finset.sum_congr rfl fun e he => ?_
  rw [if_pos (Finset.mem_range.1 he), eqW_rd]

/-- Where (Eval) says its claim and W's message holds g^T M, the claim's row is true, and back. -/
theorem eval_back : Spec.eval_back := by
  intro nR S row w lay r St m mat hb hr hin hW
  have ht : ρg.val r.target = ρg.val row.target :=
    congrArg RowF.target (read_eval S row w lay r hb hr).2
  unfold Says Holds lhs
  rw [eval_value S row w lay r St m hb hr hin, ht]
  have e1 : ∑ e ∈ Finset.range (2 ^ S.kCol),
      Alg.eqk (rd ρg S.kCol row.psi) (lowBits S.kCol e) * m w .main (lay.index e) =
      Alg.mle (colOf (witOf mat m) (weights ρg nR row.g)) (rd ρg S.kCol row.psi) := by
    unfold Alg.mle
    rw [← sum_lowBits S.kCol fun b => Alg.eqk (rd ρg S.kCol row.psi) b *
      colOf (witOf mat m) (weights ρg nR row.g) b]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [hW e (Finset.mem_range.1 he)]
    rfl
  rw [e1]
  rfl

end VerifiableInference.Desc.K13.Law
