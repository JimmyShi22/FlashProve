-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/ChalK.lean: how many scalars a plain part holds and how large a verifier message is, as small
numbers that the kernel can evaluate; and the challenge sampler of a verifier message. (Words of
this library: lean/GLOSSARY.md.)

The compiler serializes the plain part of a round, and makes a verifier message from hash blocks of
λ bits: with the universal sampler ⌈log₂ (number of its values)⌉ / λ + 2 blocks (Iop/Univ.lean:
`Round.blocks`), with `draw` (below) `nb` blocks. The numbers of values are easy to compute by hand
(powers of the number of elements of E, times powers of 2 for positions and bits), but Lean finds
`Fintype.card` or `FinEnum.card` of such a type by listing its elements, which does not end in
feasible time. So the data of a round (Blocks/StageData.lean: `RNum.plainK`, `chalE`, `chalB`) carry
three small numbers, which come from two classes:
 * class `IdxK ι`: the index type ι has n elements (the plain part K → E of a round holds `IdxK.n K`
   scalars);
 * class `ChalK E C`: C has at most |E|^kE · 2^kb values.
There are instances for the types from which the library builds index types and verifier messages
(the instance of last resort: see Limits).
The numbers are data and involve no choice (`FinEnum.card`, `FinEnum.toList`, `Fintype.card`,
`Nat.clog`); the conditions are propositions about `Nat.card`, so that they do not depend on an
instance.
The class `ChalK` also says how a verifier message is sampled from hash blocks, coordinate by
coordinate (Iop/Draw.lean, Iop/DrawOf.lean), because its instances have the coordinates of which the
message of a round consists:
 * `draw lam bE sl`: the challenge sampler of C, from a sampler bE of E and the slack sl of
   positions; none where this file has no coordinates of C or no rule of the implementation for
   them: the instance of last resort; functions on an index type without enumeration; Fin n for n no
   power of two; a single Bool; a table of coefficients with more than lam combinations.
 * `draw_good`, `draw_b`: its bias condition (`Iop.BS.Good` with (1 + 2^-sl)^(number of blocks)) if
   bE has it and 0 < lam (`DrawBase`), and that nb is the number of its blocks.
 * `draw_rule`: it is built by the rules and by nothing else (Iop/DrawRule.lean: `BS.Rule`).
Unit: no block. E: bE. Fin (2^L): a position (`Iop.BS.pos`). C × C': the blocks of C, then those of
C'. Fin n → C: coordinate i reads the blocks i · b, .., i · b + b − 1. ι → C and ∀ i, C i on an
enumerated ι: in the order of the enumeration.
The coefficients of a range proof, Fin n → ι → Bool × Bool (combination u, column c; support bit,
sign bit), have a separate instance (`coefs`), after the implementation's rule: for each column two
blocks, the first for the signs, the second for the supports; bit u of each, u < n ≤ λ, belongs to
combination u; the other bits of the two blocks are discarded. Its numbers kE, kb are those that the
general instances give.

Notation: `BS lam C` (Iop/Draw.lean): a challenge sampler for the type C: the element of C is φ of b
uniform blocks of lam bits; `draw : (lam : ℕ) → BS lam E → ℕ → Option (BS lam C)`: the challenge
sampler of C, coordinate by coordinate; `nb : ℕ → ℕ → ℕ → ℕ`: the number of its blocks, for a
sampler of E with t blocks: arguments lam, t, sl.

Limits: in each class a last instance, of low priority, serves every other enumerated, or finite,
type: `IdxK.ofFinEnum` (`FinEnum.card`, also for subtypes and Σ-types) and `ChalK.ofFintype` (kb is
the logarithm of the number of elements). It keeps every file compiling; where it is used, the
number cannot be evaluated if the type is large. Lean takes it without a warning, also in these two
cases: where a definition with a variable type omits the binder [IdxK K] or [ChalK E C]; and where
an instance `FinEnum` of the index type of a dependent function is not in scope (FinEnum Bool is in
Iop/Num.lean).
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Mathlib.Data.FinEnum
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring
import Mathlib.Data.FinEnum.Option
import Iop.DrawRule

set_option autoImplicit false

namespace Blocks
open Iop

/-- The index type ι has n elements, n a number that the kernel can evaluate. (`FinEnum.card` of a
sum or a product of types Fin n is the length of a list from which duplicates are removed: quadratic
in the number of elements.) -/
class IdxK (ι : Type) where
  n : ℕ
  eq : Nat.card ι = n

namespace IdxK

instance empty : IdxK Empty := ⟨0, by simp⟩
instance unit : IdxK Unit := ⟨1, by simp⟩
instance bool : IdxK Bool := ⟨2, by simp⟩
instance fin (n : ℕ) : IdxK (Fin n) := ⟨n, by simp⟩
instance sum {α β : Type} [Finite α] [Finite β] [a : IdxK α] [b : IdxK β] : IdxK (α ⊕ β) :=
  ⟨a.n + b.n, by rw [Nat.card_sum, a.eq, b.eq]⟩
instance prod {α β : Type} [a : IdxK α] [b : IdxK β] : IdxK (α × β) :=
  ⟨a.n * b.n, by rw [Nat.card_prod, a.eq, b.eq]⟩
instance option {α : Type} [Finite α] [a : IdxK α] : IdxK (Option α) :=
  ⟨a.n + 1, by
    haveI := Fintype.ofFinite α
    rw [Nat.card_eq_fintype_card, Fintype.card_option, ← Nat.card_eq_fintype_card, a.eq]⟩

/-- every other enumerated type: the number of its enumeration -/
instance (priority := low) ofFinEnum {ι : Type} [FinEnum ι] : IdxK ι where
  n := FinEnum.card ι
  eq := by
    letI : Fintype ι := FinEnum.instFintype
    rw [Nat.card_eq_fintype_card, FinEnum.card_eq_fintypeCard]

end IdxK

/-- C has at most |E|^kE · 2^kb values; and how an element of C is sampled from hash blocks. -/
class ChalK (E C : Type) where
  kE : ℕ
  kb : ℕ
  le : Nat.card C ≤ Nat.card E ^ kE * 2 ^ kb
  /-- the challenge sampler of C, coordinate by coordinate -/
  draw : (lam : ℕ) → BS lam E → ℕ → Option (BS lam C)
  /-- the number of its blocks, for a sampler of E with t blocks: arguments lam, t, sl -/
  nb : ℕ → ℕ → ℕ → ℕ
  draw_good : ∀ (lam : ℕ) (bE : BS lam E) (sl : ℕ) [DrawBase bE sl] (s : BS lam C),
    draw lam bE sl = some s → s.Good (kapSl sl ^ s.b)
  draw_b : ∀ (lam : ℕ) (bE : BS lam E) (sl : ℕ) (s : BS lam C),
    draw lam bE sl = some s → s.b = nb lam bE.b sl
  draw_rule : ∀ (lam : ℕ) (bE : BS lam E) (sl : ℕ) (s : BS lam C),
    draw lam bE sl = some s → BS.Rule bE sl s

namespace ChalK
variable {E : Type}

theorem good_zero {lam : ℕ} {C : Type} {s : BS lam C} {κ : ENNReal} (h : s.Good 1) (hb : s.b = 0) :
    s.Good (κ ^ s.b) := by
  rw [hb, pow_zero]; exact h

instance unit : ChalK E Unit where
  kE := 0
  kb := 0
  le := by simp
  draw := fun _ _ _ => some BS.unit
  nb := fun _ _ _ => 0
  draw_good := fun _ _ _ _ s h => by cases h; exact good_zero BS.unit_good rfl
  draw_b := fun _ _ _ s h => by cases h; rfl
  draw_rule := fun _ _ _ s h => by cases h; exact .unit

instance bool : ChalK E Bool where
  kE := 0
  kb := 1
  le := by simp
  draw := fun _ _ _ => none
  nb := fun _ _ _ => 0
  draw_good := fun _ _ _ _ _ h => by cases h
  draw_b := fun _ _ _ _ h => by cases h
  draw_rule := fun _ _ _ _ h => by cases h

instance (priority := high + 4) self : ChalK E E where
  kE := 1
  kb := 0
  le := by simp
  draw := fun _ bE _ => some bE
  nb := fun _ t _ => t
  draw_good := fun _ _ _ B s h => by cases h; exact B.good
  draw_b := fun _ _ _ s h => by cases h; rfl
  draw_rule := fun _ _ _ s h => by cases h; exact .el

instance fin (n : ℕ) : ChalK E (Fin n) where
  kE := 0
  kb := Nat.clog 2 n
  le := by simpa using Nat.le_pow_clog (by decide) n
  draw := fun lam _ sl =>
    if h : n = 2 ^ Nat.log 2 n then
      some (BS.pos lam sl n (lt_of_lt_of_eq (Nat.two_pow_pos _) h.symm))
    else none
  nb := fun lam _ sl => BS.posK lam sl n
  draw_good := fun _ _ sl B s h => by
    by_cases hn : n = 2 ^ Nat.log 2 n
    · rw [dif_pos hn] at h; cases h; exact BS.pos_good B.lam_pos sl n _
    · rw [dif_neg hn] at h; cases h
  draw_b := fun _ _ _ s h => by
    by_cases hn : n = 2 ^ Nat.log 2 n
    · rw [dif_pos hn] at h; cases h; rfl
    · rw [dif_neg hn] at h; cases h
  draw_rule := fun _ _ _ s h => by
    by_cases hn : n = 2 ^ Nat.log 2 n
    · rw [dif_pos hn] at h; cases h; exact .pos n _ _ hn
    · rw [dif_neg hn] at h; cases h

instance prod {C C' : Type} [a : ChalK E C] [b : ChalK E C'] : ChalK E (C × C') where
  kE := a.kE + b.kE
  kb := a.kb + b.kb
  le := by
    rw [Nat.card_prod, pow_add, pow_add]
    calc
      Nat.card C * Nat.card C' ≤ (Nat.card E ^ a.kE * 2 ^ a.kb) * (Nat.card E ^ b.kE * 2 ^ b.kb) :=
        Nat.mul_le_mul a.le b.le
      _ = _ := by ring
  draw := fun lam bE sl => match a.draw lam bE sl, b.draw lam bE sl with
    | some s, some t => some (s.prod t)
    | _, _ => none
  nb := fun lam t sl => a.nb lam t sl + b.nb lam t sl
  draw_good := fun lam bE sl _ s h => by
    cases ha : a.draw lam bE sl with
    | none => simp [ha] at h
    | some x =>
      cases hb : b.draw lam bE sl with
      | none => simp [ha, hb] at h
      | some y =>
        simp only [ha, hb, Option.some.injEq] at h
        subst h
        have := BS.prod_good (a.draw_good lam bE sl x ha) (b.draw_good lam bE sl y hb)
        rwa [← pow_add] at this
  draw_b := fun lam bE sl s h => by
    cases ha : a.draw lam bE sl with
    | none => simp [ha] at h
    | some x =>
      cases hb : b.draw lam bE sl with
      | none => simp [ha, hb] at h
      | some y =>
        simp only [ha, hb, Option.some.injEq] at h
        subst h
        show x.b + y.b = _
        rw [a.draw_b lam bE sl x ha, b.draw_b lam bE sl y hb]
  draw_rule := fun lam bE sl s h => by
    cases ha : a.draw lam bE sl with
    | none => simp [ha] at h
    | some x =>
      cases hb : b.draw lam bE sl with
      | none => simp [ha, hb] at h
      | some y =>
        simp only [ha, hb, Option.some.injEq] at h
        subst h
        exact .prod (a.draw_rule lam bE sl x ha) (b.draw_rule lam bE sl y hb)

theorem prod_list_le {ι : Type} (l : List ι) (c kE kb : ι → ℕ)
    (q : ℕ) (h : ∀ i, c i ≤ q ^ kE i * 2 ^ kb i) :
    (l.map c).prod ≤ q ^ (l.map kE).sum * 2 ^ (l.map kb).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add]
    calc
      c i * (l.map c).prod ≤ (q ^ kE i * 2 ^ kb i) * (q ^ (l.map kE).sum * 2 ^ (l.map kb).sum) :=
        Nat.mul_le_mul (h i) ih
      _ = _ := by ring

theorem piE_b' {lam : ℕ} {ι : Type} [FinEnum ι] [Fintype ι] {C : ι → Type} (s : ∀ i, BS lam (C i)) :
    (BS.piE s).b = ∑ i, (s i).b :=
  Equiv.sum_comp (FinEnum.equiv (α := ι)).symm fun i => (s i).b

/-- dependent functions on an enumerated type: the sums over the enumeration. (It fits constant
families too; for these "fn" below has the higher priority.) -/
instance pi {ι : Type} [FinEnum ι] {C : ι → Type} [a : ∀ i, ChalK E (C i)] :
    ChalK E (∀ i, C i) where
  kE := ((FinEnum.toList ι).map fun i => (a i).kE).sum
  kb := ((FinEnum.toList ι).map fun i => (a i).kb).sum
  le := by
    classical
    letI : Fintype ι := FinEnum.instFintype
    rw [Nat.card_pi]
    have e : ∏ i, Nat.card (C i) = ((FinEnum.toList ι).map fun i => Nat.card (C i)).prod := by
      rw [← List.prod_toFinset _ FinEnum.nodup_toList]
      exact Finset.prod_congr (Finset.ext fun i => by simp) fun _ _ => rfl
    rw [e]
    exact prod_list_le _ _ _ _ _ fun i => (a i).le
  draw := fun lam bE sl =>
    letI : Fintype ι := FinEnum.instFintype
    if h : ∀ i, ((a i).draw lam bE sl).isSome = true then
        some (BS.piE fun i => ((a i).draw lam bE sl).get (h i))
      else none
  nb := fun lam t sl => ((FinEnum.toList ι).map fun i => (a i).nb lam t sl).sum
  draw_good := fun lam bE sl _ s h => by
    letI : Fintype ι := FinEnum.instFintype
    by_cases hs : ∀ i, ((a i).draw lam bE sl).isSome = true
    · rw [dif_pos hs] at h
      cases h
      exact BS.piE_good fun i => (a i).draw_good lam bE sl _ (Option.some_get (hs i)).symm
    · rw [dif_neg hs] at h
      cases h
  draw_b := fun lam bE sl s h => by
    classical
    letI : Fintype ι := FinEnum.instFintype
    by_cases hs : ∀ i, ((a i).draw lam bE sl).isSome = true
    · rw [dif_pos hs] at h
      cases h
      rw [piE_b']
      have e : ∑ i, (((a i).draw lam bE sl).get (hs i)).b = ∑ i, (a i).nb lam bE.b sl :=
        Finset.sum_congr rfl fun i _ => (a i).draw_b lam bE sl _ (Option.some_get (hs i)).symm
      rw [e, ← List.sum_toFinset _ FinEnum.nodup_toList]
      exact Finset.sum_congr (Finset.ext fun i => by simp) fun _ _ => rfl
    · rw [dif_neg hs] at h
      cases h
  draw_rule := fun lam bE sl s h => by
    letI : Fintype ι := FinEnum.instFintype
    by_cases hs : ∀ i, ((a i).draw lam bE sl).isSome = true
    · rw [dif_pos hs] at h
      cases h
      exact .piE fun i => (a i).draw_rule lam bE sl _ (Option.some_get (hs i)).symm
    · rw [dif_neg hs] at h
      cases h

theorem pow_le_of {c q kE kb : ℕ} (h : c ≤ q ^ kE * 2 ^ kb) (n : ℕ) :
    c ^ n ≤ q ^ (n * kE) * 2 ^ (n * kb) := by
  calc c ^ n ≤ (q ^ kE * 2 ^ kb) ^ n := Nat.pow_le_pow_left h n
    _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm kE, Nat.mul_comm kb]

/-- functions on a finite index type into one type: the two numbers are n · kE and n · kb, so that
the kernel need not go through an enumeration -/
instance (priority := high) fn {ι C : Type} [Finite ι] [i : IdxK ι] [a : ChalK E C] :
    ChalK E (ι → C) where
  kE := i.n * a.kE
  kb := i.n * a.kb
  le := by
    rw [Nat.card_fun, i.eq]
    exact pow_le_of a.le _
  draw := fun _ _ _ => none
  nb := fun _ _ _ => 0
  draw_good := fun _ _ _ _ _ h => by cases h
  draw_b := fun _ _ _ _ h => by cases h
  draw_rule := fun _ _ _ _ h => by cases h

/-- `fn` on an enumerated index type: the numbers are the same, and the coordinates are sampled in
the order of the enumeration -/
instance (priority := high + 1) fnE {ι C : Type} [FinEnum ι] [i : IdxK ι] [a : ChalK E C] :
    ChalK E (ι → C) where
  kE := i.n * a.kE
  kb := i.n * a.kb
  le := by
    haveI : Finite ι := Finite.of_equiv _ (FinEnum.equiv (α := ι)).symm
    rw [Nat.card_fun, i.eq]
    exact pow_le_of a.le _
  draw := fun lam bE sl => (a.draw lam bE sl).map BS.fnE
  nb := fun lam t sl => i.n * a.nb lam t sl
  draw_good := fun lam bE sl _ s h => by
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    exact BS.fnE_good (a.draw_good lam bE sl x hx)
  draw_b := fun lam bE sl s h => by
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    show FinEnum.card ι * x.b = _
    letI : Fintype ι := FinEnum.instFintype
    rw [a.draw_b lam bE sl x hx, ← i.eq, Nat.card_eq_fintype_card, FinEnum.card_eq_fintypeCard]
  draw_rule := fun lam bE sl s h => by
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .fnE (a.draw_rule lam bE sl x hx)

/-- vectors: coordinate i reads the blocks i · b, .., i · b + b − 1 -/
instance (priority := high + 2) vec (n : ℕ) {C : Type} [a : ChalK E C] : ChalK E (Fin n → C) where
  kE := n * a.kE
  kb := n * a.kb
  le := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
    exact pow_le_of a.le _
  draw := fun lam bE sl => (a.draw lam bE sl).map (BS.vec n)
  nb := fun lam t sl => n * a.nb lam t sl
  draw_good := fun lam bE sl _ s h => by
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    have := BS.vec_good n (a.draw_good lam bE sl x hx)
    rwa [← pow_mul, Nat.mul_comm] at this
  draw_b := fun lam bE sl s h => by
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    show n * x.b = _
    rw [a.draw_b lam bE sl x hx]
  draw_rule := fun lam bE sl s h => by
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .vec n (a.draw_rule lam bE sl x hx)

/-- The coefficients of a range proof: for each column two blocks, signs then supports; bit u of
each belongs to combination u. -/
instance (priority := high + 3) coefs (n : ℕ) {ι : Type} [FinEnum ι] [i : IdxK ι] :
    ChalK E (Fin n → ι → Bool × Bool) where
  kE := n * (i.n * (0 + 0))
  kb := n * (i.n * (1 + 1))
  le := (vec (E := E) n (C := ι → Bool × Bool)).le
  draw := fun lam _ _ => if h : n ≤ lam then some (BS.coefs n h ι) else none
  nb := fun _ _ _ => i.n * (1 + 1)
  draw_good := fun lam _ sl _ s h => by
    by_cases hn : n ≤ lam
    · rw [dif_pos hn] at h
      cases h
      exact BS.coefs_good n hn ι (one_le_kapSl sl)
    · rw [dif_neg hn] at h
      cases h
  draw_b := fun lam _ _ s h => by
    by_cases hn : n ≤ lam
    · rw [dif_pos hn] at h
      cases h
      show FinEnum.card ι * (1 + 1) = _
      letI : Fintype ι := FinEnum.instFintype
      rw [← i.eq, Nat.card_eq_fintype_card, FinEnum.card_eq_fintypeCard]
    · rw [dif_neg hn] at h
      cases h
  draw_rule := fun lam _ _ s h => by
    by_cases hn : n ≤ lam
    · rw [dif_pos hn] at h
      cases h
      exact .coefs n hn ι
    · rw [dif_neg hn] at h
      cases h

/-- every other finite type: the logarithm of its number of elements -/
instance (priority := low) ofFintype {C : Type} [Fintype C] : ChalK E C where
  kE := 0
  kb := Nat.clog 2 (Fintype.card C)
  le := by
    rw [Nat.card_eq_fintype_card, pow_zero, Nat.one_mul]
    exact Nat.le_pow_clog (by decide) _
  draw := fun _ _ _ => none
  nb := fun _ _ _ => 0
  draw_good := fun _ _ _ _ _ h => by cases h
  draw_b := fun _ _ _ _ h => by cases h
  draw_rule := fun _ _ _ _ h => by cases h

end ChalK

/-! The kernel evaluates these numbers. (ℕ stands for E: only the numbers are tested, not the
conditions.) -/
example : (inferInstance : IdxK (Fin 15040 ⊕ Fin 15040 × Fin (2 ^ 5))).n = 496320 := by
  decide +kernel
example : (inferInstance : ChalK ℕ (Fin 7 → ℕ)).kE = 7 := by decide +kernel
example : (inferInstance : ChalK ℕ (Fin 3 ⊕ Fin 4 ⊕ Fin 5 → ℕ)).kE = 12 := by decide +kernel
example : (inferInstance : ChalK ℕ (∀ _ : Fin 2, Fin 5 → Fin 3 → Bool × Bool)).kb = 60 := by
  decide +kernel
example : (inferInstance : ChalK ℕ (∀ b : Fin 2, Fin (b.val + 2) → ℕ)).kE = 5 := by decide +kernel
example : (inferInstance : ChalK ℕ (Fin 8 × Fin 7 → ℕ)).kE = 56 := by decide +kernel
example : (inferInstance : ChalK ℕ (Unit → ℕ)).kE = 1 := by decide +kernel
example :
    (inferInstance : ChalK ℕ (∀ _ : Fin 8, Fin 160 → Fin 4816 → Bool × Bool)).kb = 12328960 := by
  decide +kernel
example (E : Type) : (inferInstance : ChalK E E).kE = 1 := rfl
/-! Which instance is taken, as the number of blocks shows (256 bits, 3 blocks for an element of E,
slack 115): a table of coefficients needs two blocks for a column, not a block for a bit; a vector 3
for a coordinate; a position one. -/
example : (inferInstance : ChalK ℕ (Fin 160 → Fin 4816 → Bool × Bool)).nb 256 3 115 = 9632 := by
  decide +kernel
example :
    (inferInstance : ChalK ℕ (∀ _ : Fin 8, Fin 160 → Fin 4816 → Bool × Bool)).nb 256 3 115 =
      77056 := by decide +kernel
example :
    (inferInstance : ChalK ℕ (∀ b : Fin 2, Fin 160 → Fin (b.val + 2) → Bool × Bool)).nb 256 3 115 =
      10 := by decide +kernel
example : (inferInstance : ChalK ℕ (Fin 7 → ℕ)).nb 256 3 115 = 21 := by decide +kernel
example : (inferInstance : ChalK ℕ (Fin 8 × Fin 7 → ℕ)).nb 256 3 115 = 168 := by decide +kernel
example : (inferInstance : ChalK ℕ (Fin 41 → Fin (2 ^ 33))).nb 256 3 115 = 41 := by decide +kernel
example (E : Type) (lam : ℕ) (bE : BS lam E) (sl : ℕ) :
    (inferInstance : ChalK E E).draw lam bE sl = some bE := rfl
example (E : Type) (lam : ℕ) (bE : BS lam E) (sl n : ℕ) :
    (inferInstance : ChalK E (Fin n → E)).draw lam bE sl = some (bE.vec n) := rfl

end Blocks
