-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/LookupCalls.lean: the calls of a lookup argument, as ranges of trees of its forest.

Blocks/LookupRel.lean states the lookup argument for trees (batches of 2^D keys): key θ i, and a
table for each tree. Here a call is a range of 2^e trees (which share a table in
`LkPar.CallsOK.inTable_iff`); the forest need not be full. N_T is `LkPar.NT`; ~LEAF extends the
leaves `LkPar.leafK`; z, C_end: Blocks/LookupBlock.lean.

 * `LkCall` (e, pre): the call whose trees are θ = pre 2^e + τ, τ < 2^e; it has 2^(e + D) keys, and
   key number (τ | i) = τ 2^D + i of the call is key number i of the tree (pre | τ)
   (`LkPar.KeysOf`).
 * `LkPar.CallsOK`: e ≤ σ for each call, and the ranges of trees are below N_T, cover the trees
   below N_T, and do not overlap.
 * The numbering of z. The leaf (i | θ) has the number i 2^σ + θ, and coordinate 0 of a point
   belongs to the highest bit. So the end point of the key side is z = (z_in | z_tr): coordinates 0,
   .., D - 1 are z_in, coordinates D, .., D + σ - 1 are z_tr. `LkPar.wCall` c z = eq(the first σ - e
   coordinates of z_tr, pre). `LkPar.zCall` c z = (the last e coordinates of z_tr | z_in):
   coordinate t < e is z (D + (σ - e) + t), coordinate e + t is z t.
 * `LkPar.CallsOK.ext_leafK`: under `CallsOK`, N_T ≤ 2^σ and `LkPar.KeysOf`, ~LEAF(z) = ∑_c w_c (α -
   ~key_c(z_c)). With the end claim (under its premise) this gives val(C_end) = ∑_c w_c (α -
   ~key_c(z_c)). For one call with e = σ and pre = 0 it is `LkPar.ext_leafK_full` up to the order of
   the coordinates.
 * `LkPar.CallsOK.inTable_iff`: `InTable`, call by call.
-/
import Blocks.LookupRel

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks

open Finset

/-! ## 1. Equality factors at shifted points -/

section Eq

variable {E : Type} [Field E]

/-- The equality factor reads g coordinates of its point, from the offset on. -/
private theorem eqN_congr {g off off' : ℕ} {a a' : ℕ → E}
    (h : ∀ t < g, a (off + t) = a' (off' + t)) (X : ℕ) :
    eqN g off a X = eqN g off' a' X := by
  unfold eqN
  exact prod_congr rfl fun t ht => by rw [h t (mem_range.mp ht)]

/-- The extension of a vector with two-part indices (x | y), as a double sum. -/
theorem ext_two (g g' : ℕ) (v pt : ℕ → E) :
    ext (g + g') v pt =
        ∑ x ∈ range (2 ^ g),
          ∑ y ∈ range (2 ^ g'), eqN g 0 pt x * eqN g' g pt y * v (x * 2 ^ g' + y) := by
  unfold ext
  rw [pow_add, Alg.sum_range_mul_add]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y hy => ?_
  rw [eqN_append' g g' 0 pt x (mem_range.mp hy), Nat.zero_add]

end Eq

/-! ## 2. Calls -/

/-- A call, as a range of trees: the 2^e trees θ = (pre | τ) = pre 2^e + τ, τ < 2^e. With trees of
2^D keys the call has 2^(e + D) keys. -/
structure LkCall where
  e : ℕ
  pre : ℕ

/-- The tree θ belongs to the call. -/
def LkCall.Has (c : LkCall) (θ : ℕ) : Prop := θ / 2 ^ c.e = c.pre

instance (c : LkCall) (θ : ℕ) : Decidable (c.Has θ) := inferInstanceAs (Decidable (_ = _))

theorem LkCall.has_block (c : LkCall) {τ : ℕ} (hτ : τ < 2 ^ c.e) (h : ℕ) :
    LkCall.Has c (h * 2 ^ c.e + τ) ↔ h = c.pre := by
  unfold LkCall.Has
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hτ, Nat.zero_add]

namespace LkPar

variable {E : Type} [Field E] (P : LkPar E) {C : Type} [Fintype C] [DecidableEq C] (cl : C → LkCall)

/-- The calls make up the trees of the forest (the trees of call c are the indices θ = (pre_c | b)
with a fixed prefix; indices θ ≥ N_T are unused). -/
structure CallsOK : Prop where
  le : ∀ c, (cl c).e ≤ P.σ
  inNT : ∀ c, ((cl c).pre + 1) * 2 ^ (cl c).e ≤ P.NT
  cover : ∀ θ < P.NT, ∃ c, (cl c).Has θ
  disj : ∀ c c' θ, (cl c).Has θ → (cl c').Has θ → c = c'

/-- The weight of a call at the end point z = (z_in | z_tr) of the key side: eq(the first σ - e
coordinates of z_tr, pre). -/
def wCall (c : LkCall) (z : ℕ → E) : E := eqN (P.σ - c.e) P.D z c.pre

/-- The point of a call: z_c = (the last e coordinates of z_tr | z_in), e + D coordinates. -/
def zCall (c : LkCall) (z : ℕ → E) (t : ℕ) : E :=
  if t < c.e then z (P.D + (P.σ - c.e) + t) else z (t - c.e)

/-- The keys of the forest are those of the calls: key number i of the tree (pre | τ) is key number
(τ | i) of the call. -/
def KeysOf (key : ℕ → ℕ → E) (kc : C → ℕ → E) : Prop :=
  ∀ c, ∀ τ < 2 ^ (cl c).e,
    ∀ i < 2 ^ P.D, key ((cl c).pre * 2 ^ (cl c).e + τ) i = kc c (τ * 2 ^ P.D + i)

variable {P cl}

theorem CallsOK.pre_lt (h : P.CallsOK cl) (hnt : P.NT ≤ 2 ^ P.σ) (c : C) :
    (cl c).pre < 2 ^ (P.σ - (cl c).e) := by
  have h1 := (h.inNT c).trans hnt
  have h2 : 2 ^ P.σ = 2 ^ (P.σ - (cl c).e) * 2 ^ (cl c).e := by
    rw [← pow_add, Nat.sub_add_cancel (h.le c)]
  rw [h2] at h1
  exact Nat.lt_of_succ_le (Nat.le_of_mul_le_mul_right h1 (Nat.two_pow_pos _))

theorem CallsOK.lt_of_has (h : P.CallsOK cl) {c : C} {θ : ℕ} (hθ : (cl c).Has θ) : θ < P.NT := by
  refine lt_of_lt_of_le ?_ (h.inNT c)
  have h1 : θ / 2 ^ (cl c).e = (cl c).pre := hθ
  rw [← h1]
  have h2 := Nat.div_add_mod' θ (2 ^ (cl c).e)
  have h3 := Nat.mod_lt θ (Nat.two_pow_pos (cl c).e)
  calc θ = θ / 2 ^ (cl c).e * 2 ^ (cl c).e + θ % 2 ^ (cl c).e := h2.symm
    _ < θ / 2 ^ (cl c).e * 2 ^ (cl c).e + 2 ^ (cl c).e := by omega
    _ = (θ / 2 ^ (cl c).e + 1) * 2 ^ (cl c).e := by ring

end LkPar

namespace LkPar

variable {E : Type} [Field E] {P : LkPar E} {C : Type} [Fintype C] [DecidableEq C] {cl : C → LkCall}

/-- Under h, hnt, a sum over the trees that occur is the sum over the calls of the sums over their
ranges of trees. -/
theorem CallsOK.sum_trees (h : P.CallsOK cl) (hnt : P.NT ≤ 2 ^ P.σ) (F : ℕ → E) :
    ∑ θ ∈ range (2 ^ P.σ), (if θ < P.NT then F θ else 0) =
      ∑ c, ∑ τ ∈ range (2 ^ (cl c).e), F ((cl c).pre * 2 ^ (cl c).e + τ) := by
  have h1 : ∀ θ, (if θ < P.NT then F θ else 0) = ∑ c, if (cl c).Has θ then F θ else 0 := by
    intro θ
    by_cases hθ : θ < P.NT
    · obtain ⟨c, hc⟩ := h.cover θ hθ
      rw [if_pos hθ,
        sum_eq_single c (fun c' _ hne => if_neg fun hc' => hne (h.disj c' c θ hc' hc))
          (fun hn => absurd (mem_univ c) hn), if_pos hc]
    · rw [if_neg hθ]
      exact (sum_eq_zero fun c _ => if_neg fun hc => hθ (h.lt_of_has hc)).symm
  simp only [h1]
  rw [sum_comm]
  refine sum_congr rfl fun c _ => ?_
  have h2 : 2 ^ P.σ = 2 ^ (P.σ - (cl c).e) * 2 ^ (cl c).e := by
    rw [← pow_add, Nat.sub_add_cancel (h.le c)]
  rw [h2, Alg.sum_range_mul_add]
  have h3 : ∀ x ∈ range (2 ^ (P.σ - (cl c).e)),
      (∑ τ ∈ range (2 ^ (cl c).e), if (cl c).Has (x * 2 ^ (cl c).e + τ) then
            F (x * 2 ^ (cl c).e + τ)
          else 0) =
        if x = (cl c).pre then ∑ τ ∈ range (2 ^ (cl c).e), F (x * 2 ^ (cl c).e + τ) else 0 := by
    intro x _
    by_cases hx : x = (cl c).pre
    · rw [if_pos hx]
      exact sum_congr rfl fun τ hτ => if_pos (((cl c).has_block (mem_range.mp hτ) x).mpr hx)
    · rw [if_neg hx]
      exact sum_eq_zero fun τ hτ =>
        if_neg fun hh => hx (((cl c).has_block (mem_range.mp hτ) x).mp hh)
  rw [sum_congr rfl h3, sum_ite_eq' (range (2 ^ (P.σ - (cl c).e))) (cl c).pre,
    if_pos (mem_range.mpr (h.pre_lt hnt c))]

/-- The end of the key side, call by call, under h, hnt, hk: ~LEAF(z) = ∑_c w_c (α - ~key_c(z_c)).
Unused trees contribute 0. -/
theorem CallsOK.ext_leafK (h : P.CallsOK cl) (hnt : P.NT ≤ 2 ^ P.σ) {key : ℕ → ℕ → E}
    {kc : C → ℕ → E} (hk : P.KeysOf cl key kc) (al : E) (z : ℕ → E) :
    ext (P.D + P.σ) (P.leafK key al) z =
        ∑ c, P.wCall (cl c) z * (al - ext ((cl c).e + P.D) (kc c) (P.zCall (cl c) z)) := by
  -- the leaves, tree by tree
  have hleaf : ∀ i,
      ∀ θ < 2 ^ P.σ, P.leafK key al (i * 2 ^ P.σ + θ) = if θ < P.NT then al - key θ i else 0 := by
    intro i θ hθ
    unfold leafK
    have h1 : (i * 2 ^ P.σ + θ) % 2 ^ P.σ = θ := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hθ]
    have h2 : (i * 2 ^ P.σ + θ) / 2 ^ P.σ = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt hθ, Nat.zero_add]
    rw [h1, h2]
  rw [ext_two, sum_comm]
  have h1 : ∀ θ ∈ range (2 ^ P.σ),
      (∑ i ∈ range (2 ^ P.D), eqN P.D 0 z i * eqN P.σ P.D z θ * P.leafK key al (i * 2 ^ P.σ + θ)) =
        if θ < P.NT then eqN P.σ P.D z θ * ∑ i ∈ range (2 ^ P.D), eqN P.D 0 z i * (al - key θ i)
        else 0 := by
    intro θ hθ
    simp only [hleaf _ θ (mem_range.mp hθ)]
    split_ifs
    · rw [mul_sum]
      exact sum_congr rfl fun i _ => by ring
    · simp
  rw [sum_congr rfl h1, h.sum_trees hnt]
  refine sum_congr rfl fun c _ => ?_
  -- one call
  have h2 : al - ext ((cl c).e + P.D) (kc c) (P.zCall (cl c) z) =
      ext ((cl c).e + P.D) (fun k => al - kc c k) (P.zCall (cl c) z) := by
    rw [ext_sub, ext_const]
  rw [h2, ext_two, mul_sum]
  refine sum_congr rfl fun τ hτ => ?_
  have hσ : P.σ = (P.σ - (cl c).e) + (cl c).e := (Nat.sub_add_cancel (h.le c)).symm
  have h3 : eqN P.σ P.D z ((cl c).pre * 2 ^ (cl c).e + τ) =
      P.wCall (cl c) z * eqN (cl c).e (P.D + (P.σ - (cl c).e)) z τ := by
    conv_lhs => rw [hσ]
    exact eqN_append' _ _ _ z _ (mem_range.mp hτ)
  have h4 : eqN (cl c).e 0 (P.zCall (cl c) z) τ = eqN (cl c).e (P.D + (P.σ - (cl c).e)) z τ :=
    eqN_congr (fun t ht => by
      unfold zCall
      rw [Nat.zero_add, if_pos ht]) τ
  have h5 : ∀ i, eqN P.D (cl c).e (P.zCall (cl c) z) i = eqN P.D 0 z i := fun i =>
    eqN_congr (fun t _ => by
      unfold zCall
      rw [if_neg (by omega), Nat.add_sub_cancel_left, Nat.zero_add]) i
  rw [h3, mul_assoc, mul_sum, mul_sum, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [hk c τ (mem_range.mp hτ) i (mem_range.mp hi), h4, h5]
  ring

/-- Under h, hk: every key of every tree is a value of its table if and only if every key of every
call c is a value of tbc c, the table of all trees of c. -/
theorem CallsOK.inTable_iff (h : P.CallsOK cl) {key : ℕ → ℕ → E} {kc : C → ℕ → E}
    (hk : P.KeysOf cl key kc) {tbc : C → ℕ → E}
    (htb : ∀ c, ∀ τ < 2 ^ (cl c).e, P.tb ((cl c).pre * 2 ^ (cl c).e + τ) = tbc c) :
    P.InTable key ↔ ∀ c, ∀ k < 2 ^ ((cl c).e + P.D), ∃ t < 2 ^ P.r, kc c k = tbc c t := by
  constructor
  · intro hin c k hk'
    have h1 : k / 2 ^ P.D < 2 ^ (cl c).e := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
      exact hk'
    have h2 : k % 2 ^ P.D < 2 ^ P.D := Nat.mod_lt _ (Nat.two_pow_pos _)
    have hθ : (cl c).pre * 2 ^ (cl c).e + k / 2 ^ P.D < P.NT :=
      h.lt_of_has (((cl c).has_block h1 _).mpr rfl)
    obtain ⟨t, ht, he⟩ := hin _ hθ _ h2
    rw [hk c _ h1 _ h2, Nat.div_add_mod', htb c _ h1] at he
    exact ⟨t, ht, he⟩
  · intro hc θ hθ i hi
    obtain ⟨c, hcθ⟩ := h.cover θ hθ
    have h1 : θ % 2 ^ (cl c).e < 2 ^ (cl c).e := Nat.mod_lt _ (Nat.two_pow_pos _)
    have h2 : (cl c).pre * 2 ^ (cl c).e + θ % 2 ^ (cl c).e = θ := by
      have h3 : θ / 2 ^ (cl c).e = (cl c).pre := hcθ
      rw [← h3]
      exact Nat.div_add_mod' θ _
    have h4 : θ % 2 ^ (cl c).e * 2 ^ P.D + i < 2 ^ ((cl c).e + P.D) := by
      rw [pow_add]
      calc θ % 2 ^ (cl c).e * 2 ^ P.D + i < θ % 2 ^ (cl c).e * 2 ^ P.D + 2 ^ P.D := by omega
        _ = (θ % 2 ^ (cl c).e + 1) * 2 ^ P.D := by ring
        _ ≤ 2 ^ (cl c).e * 2 ^ P.D := Nat.mul_le_mul_right _ h1
    obtain ⟨t, ht, he⟩ := hc c _ h4
    refine ⟨t, ht, ?_⟩
    rw [← h2, hk c _ h1 i hi, htb c _ h1]
    exact he

end LkPar

end Blocks
