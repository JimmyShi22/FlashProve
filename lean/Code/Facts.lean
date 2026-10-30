-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Code/Facts.lean: first lemmas on a code with encoder (`Code.Enc`, Code/Iface.lean).

Everything here follows from `Enc.Props`; nothing else is assumed of the code. F is the field of the
code and E an extension field of F.

 * Part 1: the full input `Enc.fm` of the generator.
 * Part 2: the two contributions to an encoding (`Enc.enc_eq`; `Enc.share` is that of the
   randomness); `Enc.hides_iff_ontoUpTo`: for a concrete code one proves that `Enc.share` is onto on
   every set of at most b positions and obtains the field `hides` of `Enc.Props`.
 * Part 3: encodings over E hide any b positions, with the same b, and so do tables of encodings
   with independent randomness, over F and over E.
 * Part 4: distance over E.

The step from "onto" to "uniform" is in Code/QueryUniform.lean.

Notation: `OntoUpTo φ b` (Code/QueryUniform.lean): a proposition: on every set of at most b
positions the words φ μ take all patterns of symbols; `cnt P` (`Prob.cnt`, Prob/Cnt.lean): a natural
number, the number of elements of a finite type with the property P.
-/
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dual.Lemmas
import Code.Iface
import Code.QueryUniform

set_option autoImplicit false

namespace Code

open Prob Function

/-! ## Part 1. The full input of the generator -/

section Fm

variable {F : Type} (C : Enc F) {K : Type}

/-- The message occupies the first coordinates. -/
theorem Enc.fm_msg [Zero K] (m : Fin C.msg → K) (ρ : Fin C.r → K)
    (s : Fin C.msg) (h : (s : ℕ) < C.k) : C.fm m ρ ⟨s, h⟩ = m s := by
  unfold Enc.fm
  dsimp only
  rw [dif_pos s.2]

/-- The randomness comes right after the message. -/
theorem Enc.fm_rand [Zero K] (m : Fin C.msg → K) (ρ : Fin C.r → K)
    (t : Fin C.r) (h : C.msg + (t : ℕ) < C.k) :
    C.fm m ρ ⟨C.msg + t, h⟩ = ρ t := by
  have h1 : ¬ (C.msg + (t : ℕ) < C.msg) := by omega
  have h2 : C.msg + (t : ℕ) - C.msg < C.r := by
    have := t.2
    omega
  unfold Enc.fm
  dsimp only
  rw [dif_neg h1, dif_pos h2]
  exact congrArg ρ (Fin.ext (by simp))

theorem Enc.fm_add [AddZeroClass K] (m m' : Fin C.msg → K) (ρ ρ' : Fin C.r → K) :
    C.fm (m + m') (ρ + ρ') = C.fm m ρ + C.fm m' ρ' := by
  funext i
  rw [Pi.add_apply]
  unfold Enc.fm
  split_ifs <;> simp

theorem Enc.fm_smul [MulZeroClass K] (c : K) (m : Fin C.msg → K) (ρ : Fin C.r → K) :
    C.fm (c • m) (c • ρ) = c • C.fm m ρ := by
  funext i
  rw [Pi.smul_apply]
  unfold Enc.fm
  split_ifs <;> simp

/-- A map f with f 0 = 0 may be applied before or after `fm`. -/
theorem Enc.fm_map {K' : Type} [Zero K] [Zero K'] (f : K → K') (hf : f 0 = 0) (m : Fin C.msg → K)
    (ρ : Fin C.r → K) (i : Fin C.k) :
    C.fm (fun s => f (m s)) (fun t => f (ρ t)) i = f (C.fm m ρ i) := by
  unfold Enc.fm
  split_ifs
  · rfl
  · rfl
  · exact hf.symm

/-- If msg + r ≤ k, the sum ∑ g_i · (fm 0 ρ)_i, where `fm 0 ρ` is the full input with message 0, is
a sum over the r coordinates of the randomness. -/
theorem Enc.sum_mul_fm_rand [Field K] (hp : C.msg + C.r ≤ C.k) (g : Fin C.k → K) (ρ : Fin C.r → K) :
    ∑ i, g i * C.fm 0 ρ i = ∑ t : Fin C.r, g ⟨C.msg + t, by have := t.2; omega⟩ * ρ t := by
  classical
  let emb : Fin C.r ↪ Fin C.k :=
    ⟨fun t => ⟨C.msg + t, by have := t.2; omega⟩, fun a b h => by
      have h' : C.msg + (a : ℕ) = C.msg + (b : ℕ) := congrArg Fin.val h
      exact Fin.ext (by omega)⟩
  have h1 : ∑ t : Fin C.r, g (emb t) * ρ t = ∑ i ∈ Finset.univ.map emb, g i * C.fm 0 ρ i := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [show C.fm 0 ρ (emb t) = ρ t from C.fm_rand 0 ρ t _]
  show _ = ∑ t : Fin C.r, g (emb t) * ρ t
  rw [h1]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
  have h0 : C.fm (0 : Fin C.msg → K) ρ i = 0 := by
    unfold Enc.fm
    split_ifs with ha hb
    · rfl
    · refine absurd (Finset.mem_map.2 ⟨⟨i - C.msg, hb⟩, Finset.mem_univ _, Fin.ext ?_⟩) hi
      show C.msg + ((i : ℕ) - C.msg) = i
      omega
    · rfl
  rw [h0, mul_zero]

/-- If msg + r ≤ k, the sum ∑ g_i · (fm m 0)_i, where `fm m 0` is the full input with randomness 0,
is a sum over the coordinates of the message. -/
theorem Enc.sum_mul_fm_msg [Field K] (hp : C.msg + C.r ≤ C.k)
    (g : Fin C.k → K) (m : Fin C.msg → K) :
    ∑ i, g i * C.fm m 0 i = ∑ s : Fin C.msg, g ⟨s, by have := s.2; omega⟩ * m s := by
  classical
  let emb : Fin C.msg ↪ Fin C.k :=
    ⟨fun s => ⟨s, by have := s.2; omega⟩, fun a b h => by
      have h' : (a : ℕ) = (b : ℕ) := congrArg (fun z : Fin C.k => (z : ℕ)) h
      exact Fin.ext h'⟩
  have h1 : ∑ s : Fin C.msg, g (emb s) * m s = ∑ i ∈ Finset.univ.map emb, g i * C.fm m 0 i := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show C.fm m 0 (emb s) = m s from C.fm_msg m 0 s _]
  show _ = ∑ s : Fin C.msg, g (emb s) * m s
  rw [h1]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
  have h0 : C.fm m (0 : Fin C.r → K) i = 0 := by
    unfold Enc.fm
    split_ifs with ha hb
    · exact absurd (Finset.mem_map.2 ⟨(⟨i, ha⟩ : Fin C.msg), Finset.mem_univ _, Fin.ext rfl⟩) hi
    · rfl
    · rfl
  rw [h0, mul_zero]

/-- The full input that holds the randomness ρ and nothing else, as a linear map. -/
def Enc.rnd (K : Type) [Field K] : (Fin C.r → K) →ₗ[K] (Fin C.k → K) where
  toFun ρ := C.fm 0 ρ
  map_add' ρ ρ' := by
    have h := C.fm_add (0 : Fin C.msg → K) 0 ρ ρ'
    rwa [add_zero] at h
  map_smul' c ρ := by
    have h := C.fm_smul c (0 : Fin C.msg → K) ρ
    rwa [smul_zero] at h

end Fm

variable {F : Type} [Field F]

/-! ## Part 2. The two contributions to an encoding -/

section Shares

variable (C : Enc F) (E : Type) [Field E] [Algebra F E]

/-- The contribution of the randomness to an encoding over F. -/
def Enc.share : (Fin C.r → F) →ₗ[F] (Fin C.n → F) := C.G.mulVecLin.comp (C.rnd F)

/-- The contribution of the randomness to an encoding over E. -/
def Enc.shareE : (Fin C.r → E) →ₗ[E] (Fin C.n → E) := (C.GE E).mulVecLin.comp (C.rnd E)

theorem Enc.share_apply (ρ : Fin C.r → F) : C.share ρ = C.G.mulVec (C.fm 0 ρ) := rfl

theorem Enc.shareE_apply (ρ : Fin C.r → E) : C.shareE E ρ = (C.GE E).mulVec (C.fm 0 ρ) := rfl

/-- An encoding is the encoding of the message under the randomness 0 plus the contribution of the
randomness. -/
theorem Enc.enc_eq (m : Fin C.msg → F) (ρ : Fin C.r → F) : C.enc m ρ = C.enc m 0 + C.share ρ := by
  rw [Enc.share_apply, Enc.enc, Enc.enc, ← Matrix.mulVec_add, ← Enc.fm_add, add_zero, zero_add]

theorem Enc.encE_eq (m : Fin C.msg → E) (ρ : Fin C.r → E) :
    C.encE E m ρ = C.encE E m 0 + C.shareE E ρ := by
  rw [Enc.shareE_apply, Enc.encE, Enc.encE, ← Matrix.mulVec_add, ← Enc.fm_add, add_zero, zero_add]

/-- On randomness with entries in F the contribution over E is the contribution over F. -/
theorem Enc.shareE_algebraMap (ρ : Fin C.r → F) (j : Fin C.n) :
    C.shareE E (fun t => algebraMap F E (ρ t)) j = algebraMap F E (C.share ρ j) := by
  rw [Enc.shareE_apply, Enc.share_apply]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := C.fm_map (algebraMap F E) (map_zero _) (0 : Fin C.msg → F) ρ i
  have h0 : (fun s : Fin C.msg => algebraMap F E ((0 : Fin C.msg → F) s)) = 0 := by
    funext s
    simp
  rw [h0] at h
  rw [h]
  rfl

/-- The field `hides` of `Enc.Props`, read as linear algebra: any b positions of an encoding are
uniform, for every message, if and only if the contribution of the randomness is onto on every set
of at most b positions. -/
theorem Enc.hides_iff_ontoUpTo [Fintype F] (b : ℕ) :
    (∀ S : Finset (Fin C.n), S.card ≤ b →
      ∀ m : Fin C.msg → F,
        (PMF.uniformOfFintype (Fin C.r → F)).map (fun ρ => fun j : S => C.enc m ρ j) =
          PMF.uniformOfFintype (S → F)) ↔
    OntoUpTo C.share b := by
  rw [← queryUniform_iff_ontoUpTo (fun m : Fin C.msg → F => C.enc m 0) C.share b]
  have e : (fun (m : Fin C.msg → F) (ρ : Fin C.r → F) (j : Fin C.n) => C.enc m 0 j + C.share ρ j)
      = fun m ρ j => C.enc m ρ j := by
    funext m ρ j
    exact (congrFun (C.enc_eq m ρ) j).symm
  rw [e]
  exact Iff.rfl

end Shares

/-! ## Part 3. What the encoder hides: over E, and for tables -/

section Hides

variable {C : Enc F} [Fintype F] {E : Type} [Field E] [Algebra F E]

theorem Enc.Props.ontoUpTo [Finite E] (h : C.Props E) : OntoUpTo C.share C.b :=
  (C.hides_iff_ontoUpTo C.b).1 h.hides

theorem Enc.Props.ontoUpToE [Finite E] (h : C.Props E) : OntoUpTo (C.shareE E) C.b :=
  h.ontoUpTo.of_algebraMap E (C.shareE E) (fun ρ t => algebraMap F E (ρ t)) (C.shareE_algebraMap E)

/-- Under `h` and `hS`, encodings over E hide the same positions. -/
theorem Enc.Props.hidesE [Fintype E] (h : C.Props E) (S : Finset (Fin C.n))
    (hS : S.card ≤ C.b) (m : Fin C.msg → E) :
    (PMF.uniformOfFintype (Fin C.r → E)).map (fun ρ => fun j : S => C.encE E m ρ j) =
      PMF.uniformOfFintype (S → E) := by
  have e : (fun (ρ : Fin C.r → E) (j : S) => C.encE E m ρ j) =
      fun (ρ : Fin C.r → E) (j : S) => C.encE E m 0 j + C.shareE E ρ j := by
    funext ρ j
    exact congrFun (C.encE_eq E m ρ) j
  rw [e]
  exact h.ontoUpToE.map_uniform hS _

variable {R : Type} [Fintype R] [DecidableEq R]

/-- Under `h`, a table of encodings hides any b positions, with the same b. The rows are
encodings of any messages m a under independent uniform randomness; a position holds a column. The
columns at any b positions are uniform, so their distribution does not depend on the messages. -/
theorem Enc.Props.hides_table
    [Finite E] (h : C.Props E) (S : Finset (Fin C.n)) (hS : S.card ≤ C.b) (m : R → Fin C.msg → F) :
    (PMF.uniformOfFintype (R → Fin C.r → F)).map
        (fun ρ => fun (j : S) (a : R) => C.enc (m a) (ρ a) j) =
      PMF.uniformOfFintype (S → R → F) := by
  have e : (fun (ρ : R → Fin C.r → F) (j : S) (a : R) => C.enc (m a) (ρ a) j)
      = fun (ρ : R → Fin C.r → F) (j : S) (a : R) => C.enc (m a) 0 j + C.share (ρ a) j := by
    funext ρ j a
    exact congrFun (C.enc_eq (m a) (ρ a)) j
  rw [e]
  exact h.ontoUpTo.map_uniform_table hS fun a => C.enc (m a) 0

/-- `Enc.Props.hides_table` over E. -/
theorem Enc.Props.hidesE_table
    [Fintype E] (h : C.Props E) (S : Finset (Fin C.n)) (hS : S.card ≤ C.b) (m : R → Fin C.msg → E) :
    (PMF.uniformOfFintype (R → Fin C.r → E)).map
        (fun ρ => fun (j : S) (a : R) => C.encE E (m a) (ρ a) j) =
      PMF.uniformOfFintype (S → R → E) := by
  have e : (fun (ρ : R → Fin C.r → E) (j : S) (a : R) => C.encE E (m a) (ρ a) j)
      = fun (ρ : R → Fin C.r → E) (j : S) (a : R) => C.encE E (m a) 0 j + C.shareE E (ρ a) j := by
    funext ρ j a
    exact congrFun (C.encE_eq E (m a) (ρ a)) j
  rw [e]
  exact h.ontoUpToE.map_uniform_table hS fun a => C.encE E (m a) 0

end Hides

/-! ## Part 4. The distance over E -/

section Dist

variable {C : Enc F} {E : Type} [Field E] [Algebra F E]

/-- An F-linear form on E, applied to every symbol, turns a word of the code over E into a word of
the code over F. -/
theorem Enc.form_mulVec (π : E →ₗ[F] F) (v : Fin C.k → E) (j : Fin C.n) :
    π ((C.GE E).mulVec v j) = C.G.mulVec (fun i => π (v i)) j := by
  simp only [Matrix.mulVec, dotProduct, map_sum, Enc.GE, Matrix.map_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

variable [Fintype F] [Finite E]

/-- Under `h`, every non-zero vector over E has an image of weight at least d. -/
theorem Enc.Props.distE (h : C.Props E) (v : Fin C.k → E) (hv : v ≠ 0) :
    C.d ≤ cnt (fun j => (C.GE E).mulVec v j ≠ 0) := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.1 hv
  obtain ⟨π, hπ⟩ : ∃ π : Module.Dual F E, π (v i) ≠ 0 := by
    by_contra hcon
    exact hi
      ((Module.forall_dual_apply_eq_zero_iff F (v i)).1 fun π => by_contra fun hπ => hcon ⟨π, hπ⟩)
  refine (h.dist (fun i => π (v i)) fun h0 => hπ (congrFun h0 i)).trans
    (cnt_mono fun j hj h0 => hj ?_)
  rw [← Enc.form_mulVec, h0, map_zero]

/-- Under `h`, interleaved words have the same distance: a table of codewords over E that is
not 0 has at least d columns that are not 0. -/
theorem Enc.Props.distE_table (h : C.Props E) {R : Type} (M : R → Fin C.k → E) (hM : M ≠ 0) :
    C.d ≤ cnt (fun j => ∃ a, (C.GE E).mulVec (M a) j ≠ 0) := by
  obtain ⟨a, ha⟩ : ∃ a, M a ≠ 0 := Function.ne_iff.1 hM
  exact (h.distE (M a) ha).trans (cnt_mono fun j hj => ⟨a, hj⟩)

/-- Under `h`, the distance d is positive. -/
theorem Enc.Props.d_pos (h : C.Props E) : 0 < C.d := lt_of_le_of_lt (Nat.zero_le _) h.unique

/-- Under `h`, the generator is injective over F. -/
theorem Enc.Props.mulVec_injective (h : C.Props E) : Injective C.G.mulVec := by
  intro u v huv
  by_contra hne
  have h1 := h.dist (u - v) (sub_ne_zero.2 hne)
  rw [cnt_false fun j hj => hj (by rw [Matrix.mulVec_sub, huv, sub_self]; rfl)] at h1
  exact absurd h.d_pos (by omega)

/-- Under `h`, the generator is injective over E. -/
theorem Enc.Props.mulVecE_injective (h : C.Props E) : Injective (C.GE E).mulVec := by
  intro u v huv
  by_contra hne
  have h1 := h.distE (u - v) (sub_ne_zero.2 hne)
  rw [cnt_false fun j hj => hj (by rw [Matrix.mulVec_sub, huv, sub_self]; rfl)] at h1
  exact absurd h.d_pos (by omega)

/-- Under `h`, two different codewords over E differ at d positions or more. -/
theorem Enc.Props.distE_sub (h : C.Props E) {u v : Fin C.k → E} (huv : u ≠ v) :
    C.d ≤ cnt (fun j => (C.GE E).mulVec u j ≠ (C.GE E).mulVec v j) := by
  refine (h.distE (u - v) (sub_ne_zero.2 huv)).trans (cnt_mono fun j hj h0 => hj ?_)
  rw [Matrix.mulVec_sub, Pi.sub_apply, h0, sub_self]

end Dist

end Code
