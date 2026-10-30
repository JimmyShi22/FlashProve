--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/HonestRows.lean: the two premises of honest_tab
(Johnson/Desc/K14/Law/HonestTab.lean), which are typed, from equations by numbers.

  genMatrix_mulVec   the program's matrix applied to a full message is genK
                     (Johnson/Desc/K14/Law/NearRows.lean).
  numOf_lt           a vertex's number is below 2 ^ k.
  rowsOf             rows given by their numbers, typed: a row's full message, the tail first.
  htab_of_cols       the stored columns are the code's symbols of the rows.
  hrec_of_rows       the key's record holds the rows' true answers at the key's seeds.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K14.Law.HonestTab
import Johnson.Desc.K14.Law.NearRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Means (Words)

/-- The program's matrix applied to a full message is genK. -/
theorem genMatrix_mulVec {K : Type} [Field K] (ρ : OnBytes.Model.Reading K) (S : FoldeqShape)
    (x : Fin (2 ^ S.index.code.logN)) (U : Nat → K) :
    (genMatrix ρ S).mulVec (fullOf S U) x = genK ρ S x.val U := by
  have h : LocEq ρ S (generatorAt S.index.code x.val) (fun _ => 1) 1
      (fun _ => genK ρ S x.val U) U := by
    unfold LocEq genK
    simp
  have e := (mulVec_iff ρ S x (fun _ => 1) 1 (fun _ => genK ρ S x.val U) U).1 h
  rw [e]
  simp

theorem numOf_lt : ∀ (k : Nat) (b : Fin k → Bool), numOf k b < 2 ^ k
  | 0, _ => by simp [numOf]
  | k + 1, b => by
    have h := numOf_lt k (Fin.tail b)
    unfold numOf
    rw [Nat.pow_succ]
    split <;> omega

/-- The rows by their numbers, typed: row b's full message, the tail first. -/
def rowsOf (S : FoldeqShape) (Rw : Nat → Nat → GE) :
    (Fin S.index.v → Bool) → Fin (S.index.code.r + S.index.code.ell) → GE :=
  fun b => full2 S (Rw (numOf S.index.v b))

/-- **The stored columns are the code's symbols of the rows: typed.** -/
theorem htab_of_cols (p : Par) (tab : Nat → List UInt64) (Rw : Nat → Nat → GE)
    (ha : p.S.fold.index.code.logN ≤ 32)
    (hcol : ∀ x < 2 ^ p.S.fold.index.code.logN, ∀ n < 2 ^ p.S.fold.index.v,
      OnBytes.Model.Reading.gl.val (OnBytes.ofF ((tab x).toArray.getD n 0)) =
        genK OnBytes.Model.Reading.gl p.S.fold x (Rw n)) :
    tabF OnBytes.Model.Reading.gl p.S.fold.index tab =
      fun r => (genOf (codeOf p.S.fold.index.code)).mulVec (rowsOf p.S.fold Rw r) := by
  funext b x
  unfold tabF rowsOf
  rw [mulVec_tie p.S.fold ha, genMatrix_mulVec]
  exact hcol x.val x.isLt _ (numOf_lt _ b)

/-- **The key's record holds the rows' true answers at the key's seeds: typed**, from the equations
by numbers. -/
theorem hrec_of_rows (p : Par) (err eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (key : TableKey) (Rw : Nat → Nat → GE)
    (hp : p.S.fold.index.plain + 3 * p.S.fold.index.answers = p.S.fold.index.code.ell)
    (hz : ∀ a < p.S.fold.index.answers,
      (key.seeds.getD a default).z.length = p.S.fold.index.cubeBits)
    (h : ∀ n < 2 ^ p.S.fold.index.v, ∀ a < p.S.fold.index.answers,
      (∑ k ∈ Finset.range p.S.fold.index.plain,
          eqK ((key.seeds.getD a default).z.map OnBytes.Model.Reading.gl.val) k * Rw n k) +
        ∑ t ∈ Finset.range 3, OnBytes.Model.Reading.gl.val (key.seeds.getD a default).beta *
          OnBytes.Model.Reading.gl.val (thetaE t) * Rw n (p.S.fold.index.padPlace a t) =
      OnBytes.Model.Reading.gl.val
        (key.record.getD (n * p.S.fold.index.answers + a) zeroE)) :
    (recOf p.S.fold.index fun k =>
        OnBytes.Model.Reading.gl.val (key.record.getD k zeroE)) =
      (ixOf2 p.S.fold err eM rank).ZR.val (seedsFn OnBytes.Model.Reading.gl p.S.fold.index key)
        ((ixOf2 p.S.fold err eM rank).view (rowsOf p.S.fold Rw)) := by
  funext ⟨b, a⟩
  have e := h (numOf _ b) (numOf_lt _ b) a.val a.isLt
  rw [← rec_sum p.S.fold.index _ _ (fun t => OnBytes.Model.Reading.gl.val (thetaE t)) a.val
    (Rw (numOf _ b)) a.isLt hp, ← ofFn_ptFn OnBytes.Model.Reading.gl _ _ (hz a.val a.isLt)] at e
  refine Eq.trans e.symm ?_
  show _ = ∑ n : (Fin p.S.fold.index.v → Bool) × Fin p.S.fold.index.code.ell,
    (@ite _ (n.1 = b) (Classical.propDecidable _) (recMat p.S.fold.index
        (List.ofFn (seedsFn OnBytes.Model.Reading.gl p.S.fold.index key a).1)
        (seedsFn OnBytes.Model.Reading.gl p.S.fold.index key a).2
        (fun t => OnBytes.Model.Reading.gl.val (thetaE t)) a.val n.2.val) 0) *
      rowsOf p.S.fold Rw n.1 (Fin.natAdd p.S.fold.index.code.r n.2)
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · rw [← Fin.sum_univ_eq_sum_range (fun j => recMat p.S.fold.index _ _ _ a.val j *
      Rw (numOf _ b) j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_pos rfl]
    unfold rowsOf full2
    rw [Fin.addCases_right]
    rfl
  · intro b' _ hb
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg hb, zero_mul]
  · intro hb
    exact absurd (Finset.mem_univ b) hb

end Desc.K14.Law
