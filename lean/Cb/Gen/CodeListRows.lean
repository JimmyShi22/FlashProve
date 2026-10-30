-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/CodeListRows.lean: rows cost nothing for Reed-Solomon codes: if `BCHKS46` holds, its count
for two words holds for two tables of any finite number of rows.

The proof of Spec.rows_cost_nothing of Cb/Gen/CodeListRS.lean, and with it Spec.rs_prox and
Spec.rs_listProps, whose only hypothesis is the statement on codes BCHKS46 (stated in its source
with an outline of a proof: the head of Cb/Gen/CodeListRS.lean).
What the two conclude (`RsProx`, `RsListProps`, Cb/Gen/CodeListRS.lean) has premises of its own.

The argument. Let E be a finite field and u a table of r > 0 rows over E. Take an extension field K
of E of degree r (Mathlib: FiniteField.Extension) and a basis b of K over E, indexed by the rows.
 1. `pack`: the table becomes one word over K.
 2. For any generator matrix G over E and any set S of positions: all rows of a table agree on S
    with codewords of G over E if and only if the packed word agrees on S with a codeword of the
    same matrix over K (`on_iff`).
 3. The Reed-Solomon matrix over K at points of E is the Reed-Solomon matrix of E, read in K; so
    step 2 reads, for `OnRS`, as `rows_iff`.
 4. So a θ in E that is exceptional for the two tables is exceptional, read in K, for the two
    packed words; different θ stay different; and the count of `BCHKS46` for K is the same number,
    because it does not depend on the field.

What is used of the statement on codes (`Cb.BCHKS46`): that it holds for every finite field and
every set of distinct points (here: points in a subfield), with a count in n, k, e alone.
Nothing is assumed beyond the hypotheses of the statements: `BCHKS46` is a hypothesis in the Lean
text of each statement.
Terms: lean/GLOSSARY.md.
-/
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.LinearAlgebra.Dimension.Free
import Cb.Gen.CodeListRSProofs

set_option autoImplicit false

namespace Cb
open Prob Blocks

namespace CodeListRows
open CodeListRS

/-- An injective map that carries P into Q shows that P has at most as many elements as Q. -/
theorem cnt_le_cnt_of_injective {α β : Type} [Finite α] [Finite β] (g : α → β)
    (hg : Function.Injective g) {P : α → Prop} {Q : β → Prop} (h : ∀ a, P a → Q (g a)) :
    cnt P ≤ cnt Q :=
  Nat.card_le_card_of_injective (fun x : {a // P a} => (⟨g x.1, h x.1 x.2⟩ : {b // Q b}))
    fun _ _ hxy => Subtype.ext (hg (congrArg Subtype.val hxy))

section Pack
variable {E K ι κ R : Type} [Field E] [Field K] [Algebra E K] [Fintype κ] [Fintype R]

/-- A table over E as one word over K. -/
def pack (b : R → K) (f : R → ι → E) (j : ι) : K := ∑ a, f a j • b a

omit [Fintype κ] in
theorem pack_line (b : R → K) (f₀ f₁ : R → ι → E) (θ : E) (j : ι) :
    pack b (fun a j => f₀ a j + θ * f₁ a j) j = pack b f₀ j + algebraMap E K θ * pack b f₁ j := by
  unfold pack
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [add_smul, mul_smul, Algebra.smul_def θ]

theorem pack_mulVec (G : Matrix ι κ E) (b : R → K) (M : R → κ → E) (j : ι) :
    pack b (fun a => G.mulVec (M a)) j =
      (G.map (algebraMap E K)).mulVec (fun i => ∑ a, M a i • b a) j := by
  unfold pack
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  rw [mul_smul, Algebra.smul_def]

omit [Fintype κ] in
theorem coord_pack (b : Module.Basis R E K) (f : R → ι → E) (a : R) (j : ι) :
    b.coord a (pack b f j) = f a j := by
  unfold pack
  rw [Module.Basis.coord_apply, Module.Basis.repr_sum_self]

/-- Step 2. -/
theorem on_iff (G : Matrix ι κ E) (b : Module.Basis R E K) (f : R → ι → E) (S : Finset ι) :
    (∃ M : R → κ → E, ∀ j ∈ S, ∀ a, f a j = G.mulVec (M a) j) ↔
      ∃ v : κ → K, ∀ j ∈ S, pack b f j = (G.map (algebraMap E K)).mulVec v j := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨fun i => ∑ a, M a i • b a, fun j hj => ?_⟩
    rw [← pack_mulVec]
    unfold pack
    exact Finset.sum_congr rfl fun a _ => by rw [hM j hj a]
  · rintro ⟨v, hv⟩
    refine ⟨fun a i => b.coord a (v i), fun j hj a => ?_⟩
    rw [← Code.form_mulVec_map G (b.coord a) v j, ← hv j hj, coord_pack]

/-- Step 3. -/
theorem rows_iff {n : ℕ} (x : Fin n → E) (k : ℕ) (b : Module.Basis R E K)
    (f : R → Fin n → E) (A : Finset (Fin n)) :
    (∀ a, OnRS x k (f a) A) ↔ OnRS (fun j => algebraMap E K (x j)) k (pack b f) A := by
  have h1 : (∀ a, OnRS x k (f a) A) ↔
      ∃ M : R → Fin (k + 1) → E,
        ∀ j ∈ A, ∀ a, f a j = (Code.RS.code x (k + 1) 0 0 0 0).G.mulVec (M a) j := by
    constructor
    · intro h
      choose M hM using fun a => (onRS_iff x k (f a) A).mp (h a)
      exact ⟨M, fun j hj a =>
          (hM a j hj).trans (Code.RS.code_mulVec x (k + 1) 0 0 0 0 (M a) j).symm⟩
    · rintro ⟨M, hM⟩ a
      exact (onRS_iff x k (f a) A).mpr
        ⟨M a, fun j hj => (hM j hj a).trans (Code.RS.code_mulVec x (k + 1) 0 0 0 0 (M a) j)⟩
  have h2 : OnRS (fun j => algebraMap E K (x j)) k (pack b f) A ↔
      ∃ v : Fin (k + 1) → K, ∀ j ∈ A,
        pack b f j = ((Code.RS.code x (k + 1) 0 0 0 0).G.map (algebraMap E K)).mulVec v j := by
    rw [onRS_iff]
    refine exists_congr fun v => forall_congr' fun j => forall_congr' fun _ => ?_
    have e : ((Code.RS.code x (k + 1) 0 0 0 0).G.map (algebraMap E K)).mulVec v j =
        Code.RS.gen (fun j => algebraMap E K (x j)) (fun i : Fin (k + 1) => (i : ℕ)) v j :=
      code_GE_mulVec x (k + 1) 0 0 0 0 v j
    rw [e]
  rw [h1, h2]
  exact on_iff _ b f A

end Pack
end CodeListRows

open CodeListRows

-- Limit: the statement has the premise `Cb.BCHKS46`, a hypothesis; this file does not prove it.
theorem rows_cost_nothing : Spec.rows_cost_nothing := by
  intro H E _ _ n k e x hx hk he hJ R _ u₀ u₁
  rcases isEmpty_or_nonempty R with hR | hR
  · rw [cnt_false fun z ⟨A, _, _, h⟩ => h ⟨fun a => isEmptyElim a, fun a => isEmptyElim a⟩]
    exact le_trans (Nat.cast_le.mpr (Nat.zero_le _)) (H E n k e x hx hk he hJ 0 0)
  · cases nonempty_fintype R
    obtain ⟨p, hp⟩ := CharP.exists E
    haveI : Fact p.Prime := ⟨CharP.char_is_prime E p⟩
    haveI : NeZero (Fintype.card R) := ⟨Fintype.card_ne_zero⟩
    let K := FiniteField.Extension E p (Fintype.card R)
    let b : Module.Basis R E K :=
      (Module.finBasisOfFinrankEq E K (FiniteField.finrank_extension E p (Fintype.card R))).reindex
        (Fintype.equivFin R).symm
    have h := H K n k e (fun j => algebraMap E K (x j)) ((algebraMap E K).injective.comp hx)
      hk he hJ (pack b u₀) (pack b u₁)
    refine le_trans
      (Nat.cast_le.mpr (cnt_le_cnt_of_injective (algebraMap E K) (algebraMap E K).injective ?_)) h
    rintro θ ⟨A, hA, h1, h2⟩
    refine ⟨A, hA, ?_,
      fun h3 => h2 ⟨(rows_iff x k b u₀ A).mpr h3.1, (rows_iff x k b u₁ A).mpr h3.2⟩⟩
    have h4 := (rows_iff x k b (fun a j => u₀ a j + θ * u₁ a j) A).mp h1
    have e1 : pack b (fun a j => u₀ a j + θ * u₁ a j) =
        fun j => pack b u₀ j + algebraMap E K θ * pack b u₁ j :=
      funext fun j => pack_line b u₀ u₁ θ j
    rwa [e1] at h4

-- Limit: the statement has the premise `Cb.BCHKS46`, a hypothesis; this file does not prove it.
theorem rs_prox : Spec.rs_prox := fun H => rs_prox_of_rows (rows_cost_nothing H)

-- Limit: the statement has the premise `Cb.BCHKS46`, a hypothesis; this file does not prove it.
theorem rs_listProps : Spec.rs_listProps := fun H => rs_listProps_of_rows (rows_cost_nothing H)

end Cb
