-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/DrawProofs.lean: proofs of the condition `BS.Good` for the samplers of Iop/Draw.lean (for
`three` only the bound on the fibres), each under the hypotheses of its statement, and a proof of
`Spec.drawsGood`. Among the hypotheses: a composed sampler: from `BS.Good` of its parts; `modN`:
with κ = 1 + 2^-e, if m · 2^e ≤ 2^(λ k). (Words of this library: lean/GLOSSARY.md.)
A sampler (`BS lam C`) computes an element of C from b hash blocks (below: blocks); `BS.Good s κ`
says that every fibre has at most w elements and that w · |C| ≤ κ · 2^(λ b).
The bounds on the fibres are proved by counting: a string of blocks is split into the parts that the
coordinates read, and independent conditions on the parts multiply (Prob/Count.lean).

Notation: `cnt P : ℕ` (Prob/Cnt.lean): the number of elements of a finite type with the property P;
`A R T : ℕ` in `three_fib`: arguments of `BS.three` (Iop/Draw.lean), numbers of blocks; what is
asked of them: `hA`, `hR`, `hT`.
-/
import Iop.Draw
import Iop.PullProofs

namespace Iop
open Prob
open scoped ENNReal

namespace BS
variable {lam : ℕ} {C D : Type}

theorem cardS (lam k : ℕ) : (Fintype.card (Fin k → Dig lam) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ (lam * k) := by
  rw [card_blocks]; push_cast; rfl

theorem Good.mono {s : BS lam C} {κ κ' : ℝ≥0∞} (h : s.Good κ) (hk : κ ≤ κ') : s.Good κ' :=
  ⟨h.fib, h.ratio.trans (by gcongr)⟩

theorem unit_good : (BS.unit (lam := lam)).Good 1 where
  fib := fun c => by
    show cnt (fun _ : Fin 0 → Dig lam => () = c) ≤ 1
    exact cnt_le_one fun a b _ _ => Subsingleton.elim a b
  ratio := by
    show ((1 : ℕ) : ℝ≥0∞) * (Nat.card Unit : ℝ≥0∞) ≤ 1 * (Fintype.card (Fin 0 → Dig lam) : ℝ≥0∞)
    simp

theorem map_good (e : C ≃ D) {s : BS lam C} {κ : ℝ≥0∞} (h : s.Good κ) : (s.map e).Good κ where
  fib := fun d => by
    refine le_trans (le_of_eq (cnt_congr fun a => ?_)) (h.fib (e.symm d))
    show e (s.φ a) = d ↔ s.φ a = e.symm d
    exact e.apply_eq_iff_eq_symm_apply
  ratio := by
    rw [← Nat.card_congr e]
    exact h.ratio

theorem prod_good {s : BS lam C} {t : BS lam D} {κ κ' : ℝ≥0∞} (hs : s.Good κ) (ht : t.Good κ') :
    (s.prod t).Good (κ * κ') where
  fib := fun c => by
    show cnt (fun u : Fin (s.b + t.b) → Dig lam =>
        (s.φ (fun i => u (Fin.castAdd t.b i)), t.φ fun i => u (Fin.natAdd s.b i)) = c) ≤ s.w * t.w
    rw [← cnt_equiv
        (Fin.appendEquiv s.b t.b :
          (Fin s.b → Dig lam) × (Fin t.b → Dig lam) ≃ (Fin (s.b + t.b) → Dig lam))
        (fun u => (s.φ (fun i => u (Fin.castAdd t.b i)), t.φ fun i => u (Fin.natAdd s.b i)) = c)]
    have e : ∀ p : (Fin s.b → Dig lam) × (Fin t.b → Dig lam),
        ((s.φ (fun i => (Fin.appendEquiv s.b t.b p) (Fin.castAdd t.b i)),
            t.φ fun i => (Fin.appendEquiv s.b t.b p) (Fin.natAdd s.b i)) = c) ↔
        (s.φ p.1 = c.1 ∧ t.φ p.2 = c.2) := by
      intro p
      have h1 : (fun i => (Fin.appendEquiv s.b t.b p) (Fin.castAdd t.b i)) = p.1 :=
        funext fun i => Fin.append_left p.1 p.2 i
      have h2 : (fun i => (Fin.appendEquiv s.b t.b p) (Fin.natAdd s.b i)) = p.2 :=
        funext fun i => Fin.append_right p.1 p.2 i
      rw [h1, h2]
      exact Prod.ext_iff
    rw [cnt_congr e,
      cnt_and_prod (fun x : Fin s.b → Dig lam => s.φ x = c.1)
        (fun y : Fin t.b → Dig lam => t.φ y = c.2)]
    exact Nat.mul_le_mul (hs.fib _) (ht.fib _)
  ratio := by
    show ((s.w * t.w : ℕ) : ℝ≥0∞) * (Nat.card (C × D) : ℝ≥0∞) ≤
      κ * κ' * (Fintype.card (Fin (s.b + t.b) → Dig lam) : ℝ≥0∞)
    have h1 := hs.ratio
    have h2 := ht.ratio
    rw [cardS] at h1 h2 ⊢
    rw [Nat.card_prod, Nat.mul_add, pow_add]
    push_cast
    calc
      (s.w : ℝ≥0∞) * t.w * ((Nat.card C : ℝ≥0∞) * Nat.card D) =
          (s.w * Nat.card C) * (t.w * Nat.card D) := by ring
      _ ≤ (κ * 2 ^ (lam * s.b)) * (κ' * 2 ^ (lam * t.b)) := mul_le_mul' h1 h2
      _ = κ * κ' * (2 ^ (lam * s.b) * 2 ^ (lam * t.b)) := by ring

/-- a string of blocks, split into the parts of the coordinates -/
def cutPi {n : ℕ} (b : Fin n → ℕ) (lam : ℕ) :
    (∀ j, Fin (b j) → Dig lam) ≃ (Fin (∑ j, b j) → Dig lam) :=
  (Equiv.piCurry (fun (_ : Fin n) (_ : Fin (b _)) => Dig lam)).symm.trans
    (Equiv.arrowCongr finSigmaFinEquiv (Equiv.refl _))

theorem cutPi_apply {n : ℕ} (b : Fin n → ℕ) (f : ∀ j, Fin (b j) → Dig lam)
    (j : Fin n) (t : Fin (b j)) :
    cutPi b lam f (finSigmaFinEquiv ⟨j, t⟩) = f j t := by
  show Sigma.uncurry f (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨j, t⟩)) = f j t
  rw [Equiv.symm_apply_apply]
  rfl

theorem pi_good {n : ℕ} {C : Fin n → Type} {s : ∀ j, BS lam (C j)}
    {κ : Fin n → ℝ≥0∞} (h : ∀ j, (s j).Good (κ j)) : (BS.pi s).Good (∏ j, κ j) where
  fib := fun c => by
    show cnt (fun u : Fin (∑ j, (s j).b) → Dig lam =>
        (fun j => (s j).φ fun t => u (finSigmaFinEquiv ⟨j, t⟩)) = c) ≤ ∏ j, (s j).w
    rw [← cnt_equiv (cutPi (fun j => (s j).b) lam)
        (fun u => (fun j => (s j).φ fun t => u (finSigmaFinEquiv ⟨j, t⟩)) = c)]
    have e : ∀ f : ∀ j, Fin (s j).b → Dig lam,
        ((fun j => (s j).φ fun t => cutPi (fun j => (s j).b) lam f (finSigmaFinEquiv ⟨j, t⟩)) = c) ↔
        ∀ j, (s j).φ (f j) = c j := by
      intro f
      simp only [cutPi_apply]
      exact funext_iff
    rw [cnt_congr e, cnt_forall_pi (fun j (x : Fin (s j).b → Dig lam) => (s j).φ x = c j)]
    exact Finset.prod_le_prod' fun j _ => (h j).fib _
  ratio := by
    show ((∏ j, (s j).w : ℕ) : ℝ≥0∞) * (Nat.card (∀ j, C j) : ℝ≥0∞) ≤
      (∏ j, κ j) * (Fintype.card (Fin (∑ j, (s j).b) → Dig lam) : ℝ≥0∞)
    rw [cardS, Nat.card_pi, Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum]
    push_cast
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod' fun j _ => ?_
    have := (h j).ratio
    rwa [cardS] at this

/-- `cutPi` for parts of one length b -/
def cutVec (n b lam : ℕ) : (Fin n → Fin b → Dig lam) ≃ (Fin (n * b) → Dig lam) :=
  (Equiv.curry (Fin n) (Fin b) (Dig lam)).symm.trans
    (Equiv.arrowCongr finProdFinEquiv (Equiv.refl _))

theorem cutVec_apply (n b : ℕ) (f : Fin n → Fin b → Dig lam) (i : Fin n) (t : Fin b) :
    cutVec n b lam f (finProdFinEquiv (i, t)) = f i t := by
  simp [cutVec, Equiv.arrowCongr, Equiv.curry]

theorem vec_good (n : ℕ) {s : BS lam C} {κ : ℝ≥0∞} (h : s.Good κ) : (s.vec n).Good (κ ^ n) where
  fib := fun c => by
    show cnt (fun u : Fin (n * s.b) → Dig lam =>
        (fun i => s.φ fun t => u (finProdFinEquiv (i, t))) = c) ≤ s.w ^ n
    rw [← cnt_equiv (cutVec n s.b lam)
        (fun u => (fun i => s.φ fun t => u (finProdFinEquiv (i, t))) = c)]
    have e : ∀ f : Fin n → Fin s.b → Dig lam,
        ((fun i => s.φ fun t => cutVec n s.b lam f (finProdFinEquiv (i, t))) = c) ↔
        ∀ i, s.φ (f i) = c i := by
      intro f
      simp only [cutVec_apply]
      exact funext_iff
    rw [cnt_congr e, cnt_forall_pi (fun i (x : Fin s.b → Dig lam) => s.φ x = c i)]
    calc
      ∏ i : Fin n, cnt (fun x : Fin s.b → Dig lam => s.φ x = c i) ≤ ∏ _i : Fin n, s.w :=
        Finset.prod_le_prod' fun i _ => h.fib _
      _ = s.w ^ n := by simp
  ratio := by
    show ((s.w ^ n : ℕ) : ℝ≥0∞) * (Nat.card (Fin n → C) : ℝ≥0∞) ≤
      κ ^ n * (Fintype.card (Fin (n * s.b) → Dig lam) : ℝ≥0∞)
    have h1 := h.ratio
    rw [cardS] at h1 ⊢
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin,
      show lam * (n * s.b) = (lam * s.b) * n by ring, pow_mul]
    push_cast
    rw [← mul_pow, ← mul_pow]
    exact pow_le_pow_left' h1 n

/-- Bits at distinct places (a is injective): at most 2^(|J| − |A|) strings on J have given bits at
the places a x. -/
theorem cnt_restrict_le {A J : Type} [Fintype A] [Fintype J] [DecidableEq J] (a : A → J)
    (ha : Function.Injective a) (s : A → Bool) :
    cnt (fun d : J → Bool => ∀ x, d (a x) = s x) ≤ 2 ^ (Fintype.card J - Fintype.card A) := by
  classical
  have e : ∀ d : J → Bool,
      (∀ x, d (a x) = s x) ↔ ∀ j, (fun (j : J) (b : Bool) => ∀ x, a x = j → b = s x) j (d j) :=
    fun d => ⟨fun h j x hx => hx ▸ h x, fun h x => h (a x) x rfl⟩
  rw [cnt_congr e,
    cnt_forall_pi (A := fun _ : J => Bool) (fun (j : J) (b : Bool) => ∀ x, a x = j → b = s x)]
  have h1 : ∀ j : J,
      cnt (fun b : Bool => ∀ x, a x = j → b = s x) ≤ if j ∈ Finset.univ.image a then 1 else 2 := by
    intro j
    split_ifs with hj
    · obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hj
      exact cnt_le_one fun b b' hb hb' => (hb x hx).trans (hb' x hx).symm
    · exact le_trans (cnt_le_card _) (le_of_eq Fintype.card_bool)
  refine le_trans (Finset.prod_le_prod' fun j _ => h1 j) (le_of_eq ?_)
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ]
  congr 1
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.card_image_of_injective _ ha, Finset.card_univ]

theorem bits_good (n : ℕ) (h : n ≤ lam) : (bits n h).Good 1 where
  fib := fun c => by
    show cnt
        (fun u : Fin 1 → Dig lam => (fun i : Fin n => u 0 ⟨i.val, lt_of_lt_of_le i.isLt h⟩) = c) ≤
      2 ^ (lam - n)
    rw [← cnt_equiv (Equiv.funUnique (Fin 1) (Dig lam)).symm
        (fun u : Fin 1 → Dig lam => (fun i : Fin n => u 0 ⟨i.val, lt_of_lt_of_le i.isLt h⟩) = c)]
    have e : ∀ d : Dig lam,
        ((fun i : Fin n =>
            ((Equiv.funUnique (Fin 1) (Dig lam)).symm d) 0 ⟨i.val, lt_of_lt_of_le i.isLt h⟩) = c) ↔
        ∀ i : Fin n, d (Fin.castLE h i) = c i :=
      fun d => funext_iff
    rw [cnt_congr e]
    refine le_trans (cnt_restrict_le (Fin.castLE h) (Fin.castLE_injective h) c) (le_of_eq ?_)
    rw [Fintype.card_fin, Fintype.card_fin]
  ratio := by
    show ((2 ^ (lam - n) : ℕ) : ℝ≥0∞) * (Nat.card (Fin n → Bool) : ℝ≥0∞) ≤
      1 * (Fintype.card (Fin 1 → Dig lam) : ℝ≥0∞)
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      card_blocks, one_mul, Nat.mul_one, ← Nat.cast_mul, ← pow_add, Nat.sub_add_cancel h]

/-! ## A number below m -/

theorem modN_fib (lam m k : ℕ) (h : 0 < m) (c : Fin m) :
    cnt (fun a : Fin (modN lam m k h).b → Dig lam => (modN lam m k h).φ a = c) ≤
      (modN lam m k h).w := by
  have h1 : cnt (fun a : Fin k → Dig lam => (modN lam m k h).φ a = c)
      = cnt (fun i : Fin (Fintype.card (Fin k → Dig lam)) => (i : ℕ) ≡ (c : ℕ) [MOD m]) := by
    rw [← cnt_equiv (Num.blocks lam k) (fun i => (i : ℕ) ≡ (c : ℕ) [MOD m])]
    refine cnt_congr fun a => ?_
    show (⟨_ % m, _⟩ : Fin m) = c ↔ _
    rw [Fin.ext_iff]
    show _ % _ = _ ↔ _ % _ = _ % _
    rw [Nat.mod_eq_of_lt c.isLt]
  show cnt (fun a : Fin k → Dig lam => (modN lam m k h).φ a = c) ≤ (2 ^ (lam * k) + (m - 1)) / m
  rw [h1, cnt_fin_modEq _ h, card_blocks, Nat.le_div_iff_mul_le h]
  have h3 := Nat.div_add_mod (2 ^ (lam * k)) m
  have h4 : m * (2 ^ (lam * k) / m) = 2 ^ (lam * k) / m * m := Nat.mul_comm _ _
  split_ifs with hc
  · have : 1 ≤ 2 ^ (lam * k) % m := by omega
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · rw [Nat.add_zero]
    omega

theorem modN_exact (lam m k : ℕ) (h : 0 < m) (hd : m ∣ 2 ^ (lam * k)) :
    (modN lam m k h).Good 1 where
  fib := modN_fib lam m k h
  ratio := by
    show (((2 ^ (lam * k) + (m - 1)) / m : ℕ) : ℝ≥0∞) * (Nat.card (Fin m) : ℝ≥0∞) ≤
      1 * (Fintype.card (Fin k → Dig lam) : ℝ≥0∞)
    obtain ⟨q, hq⟩ := hd
    have e : (2 ^ (lam * k) + (m - 1)) / m = q := by
      rw [hq, Nat.mul_add_div h, Nat.div_eq_of_lt (by omega), Nat.add_zero]
    rw [e, Nat.card_eq_fintype_card, Fintype.card_fin, card_blocks, hq, one_mul]
    push_cast
    rw [mul_comm]

theorem modN_good (lam m k : ℕ) (h : 0 < m) (e : ℕ) (he : m * 2 ^ e ≤ 2 ^ (lam * k)) :
    (modN lam m k h).Good (1 + (2 ^ e : ℝ≥0∞)⁻¹) where
  fib := modN_fib lam m k h
  ratio := by
    show (((2 ^ (lam * k) + (m - 1)) / m : ℕ) : ℝ≥0∞) * (Nat.card (Fin m) : ℝ≥0∞) ≤
      (1 + (2 ^ e : ℝ≥0∞)⁻¹) * (Fintype.card (Fin k → Dig lam) : ℝ≥0∞)
    rw [Nat.card_eq_fintype_card, Fintype.card_fin, card_blocks]
    generalize 2 ^ (lam * k) = S at he ⊢
    have hn : (S + (m - 1)) / m * m ≤ S + m := le_trans (Nat.div_mul_le_self _ _) (by omega)
    have h2 : (2 ^ e : ℝ≥0∞) ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2t : (2 ^ e : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
    have hle' : ((m * 2 ^ e : ℕ) : ℝ≥0∞) ≤ (S : ℝ≥0∞) := by exact_mod_cast he
    have hC : (m : ℝ≥0∞) ≤ (2 ^ e : ℝ≥0∞)⁻¹ * S := by
      calc
        (m : ℝ≥0∞) = (2 ^ e : ℝ≥0∞)⁻¹ * 2 ^ e * m := by rw [ENNReal.inv_mul_cancel h2 h2t, one_mul]
        _ = (2 ^ e : ℝ≥0∞)⁻¹ * ((m * 2 ^ e : ℕ) : ℝ≥0∞) := by push_cast; ring
        _ ≤ (2 ^ e : ℝ≥0∞)⁻¹ * S := by gcongr
    calc
      (((S + (m - 1)) / m : ℕ) : ℝ≥0∞) * (m : ℝ≥0∞) = (((S + (m - 1)) / m * m : ℕ) : ℝ≥0∞) := by
        push_cast; ring
      _ ≤ ((S + m : ℕ) : ℝ≥0∞) := by exact_mod_cast hn
      _ = (S : ℝ≥0∞) + m := by push_cast; rfl
      _ ≤ (S : ℝ≥0∞) + (2 ^ e : ℝ≥0∞)⁻¹ * S := by gcongr
      _ = (1 + (2 ^ e : ℝ≥0∞)⁻¹) * (S : ℝ≥0∞) := by ring

/-! ## Three attempts -/

theorem cnt3 {Dg : Type} [Fintype Dg] (P0 P1 P2 : Dg → Prop) :
    cnt (fun u : Fin 3 → Dg => P0 (u 0) ∧ P1 (u 1) ∧ P2 (u 2)) = cnt P0 * cnt P1 * cnt P2 := by
  have h :=
    cnt_forall_pi (ι := Fin 3) (A := fun _ => Dg) (fun i => (![P0, P1, P2] : Fin 3 → Dg → Prop) i)
  rw [Fin.prod_univ_three] at h
  rw [show cnt P0 * cnt P1 * cnt P2 =
          cnt ((![P0, P1, P2] : Fin 3 → Dg → Prop) 0) *
            cnt ((![P0, P1, P2] : Fin 3 → Dg → Prop) 1) *
            cnt ((![P0, P1, P2] : Fin 3 → Dg → Prop) 2) from rfl, ← h]
  refine cnt_congr fun u => ?_
  rw [Fin.forall_fin_succ, Fin.forall_fin_succ, Fin.forall_fin_succ]
  simp

theorem card_dig (lam : ℕ) : Fintype.card (Dig lam) = 2 ^ lam := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

theorem three_fib (ok : Dig lam → Bool) (el : Dig lam → C) (A R T : ℕ) (z : C → Bool) (nz : ℕ)
    (hA : ∀ c, cnt (fun d : Dig lam => ok d = true ∧ el d = c) ≤ A)
    (hR : cnt (fun d : Dig lam => ok d = false) ≤ R)
    (hT : ∀ c, cnt (fun d : Dig lam => el d = c) ≤ T) (c : C) :
    cnt (fun a : Fin (three ok el A R T z nz).b → Dig lam => (three ok el A R T z nz).φ a = c) ≤
      (three ok el A R T z nz).w := by
  show cnt (fun u : Fin 3 → Dig lam =>
      (if ok (u 0) then el (u 0) else if ok (u 1) then el (u 1) else el (u 2)) = c) ≤
    A * 2 ^ lam * 2 ^ lam + R * A * 2 ^ lam + R * R * T
  have hsplit : ∀ u : Fin 3 → Dig lam,
      (if ok (u 0) then el (u 0) else if ok (u 1) then el (u 1) else el (u 2)) = c →
      (((ok (u 0) = true ∧ el (u 0) = c) ∧ True ∧ True) ∨
        (ok (u 0) = false ∧ (ok (u 1) = true ∧ el (u 1) = c) ∧ True)) ∨
      (ok (u 0) = false ∧ ok (u 1) = false ∧ el (u 2) = c) := by
    intro u hu
    cases h0 : ok (u 0) with
    | true => rw [h0] at hu; exact Or.inl (Or.inl ⟨⟨rfl, by simpa using hu⟩, trivial, trivial⟩)
    | false =>
      rw [h0] at hu
      cases h1 : ok (u 1) with
      | true => rw [h1] at hu; exact Or.inl (Or.inr ⟨rfl, ⟨rfl, by simpa using hu⟩, trivial⟩)
      | false => rw [h1] at hu; exact Or.inr ⟨rfl, rfl, by simpa using hu⟩
  refine le_trans (cnt_le_add hsplit)
    (Nat.add_le_add (le_trans (cnt_or_le _ _) (Nat.add_le_add ?_ ?_)) ?_)
  · rw [cnt3 (fun d => ok d = true ∧ el d = c) (fun _ => True) (fun _ => True), cnt_true, card_dig]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (hA c))
  · rw [cnt3 (fun d => ok d = false) (fun d => ok d = true ∧ el d = c) (fun _ => True), cnt_true,
      card_dig]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul hR (hA c))
  · rw [cnt3 (fun d => ok d = false) (fun d => ok d = false) (fun d => el d = c)]
    exact Nat.mul_le_mul (Nat.mul_le_mul hR hR) (hT c)

/-! ## `Spec.drawsGood` -/

end BS


theorem drawsGood_aux {lam : ℕ} {κ₀ : ℝ≥0∞} (h1 : 1 ≤ κ₀) :
    ∀ (s : Shape) (ds : s.Draws lam), ds.Good κ₀ s →
      ∀ κ : ℝ≥0∞,
        κ₀ ^ Shape.Draws.maxB s ds ≤ κ → (Samplers.ofDraws s ds).Good κ (κ₀ ^ Shape.Draws.totB s ds)
  | [], _, _, _, _ => le_of_eq (pow_zero _).symm
  | r :: s, (d, ds), h, κ, hκ => by
    have hd : κ₀ ^ d.b ≤ κ := le_trans (pow_le_pow_right₀ h1 (le_max_left _ _)) hκ
    have hr := h.1.ratio
    rw [Nat.card_eq_fintype_card] at hr
    refine ⟨h.1.fib, hr.trans (mul_le_mul' hd le_rfl), _,
      drawsGood_aux h1 s ds h.2 κ (le_trans (pow_le_pow_right₀ h1 (le_max_right _ _)) hκ), ?_⟩
    show (d.w : ℝ≥0∞) * (Fintype.card r.Chal : ℝ≥0∞) * κ₀ ^ Shape.Draws.totB s ds ≤
      κ₀ ^ (d.b + Shape.Draws.totB s ds) * (Fintype.card (Fin d.b → Dig lam) : ℝ≥0∞)
    calc
      (d.w : ℝ≥0∞) * (Fintype.card r.Chal : ℝ≥0∞) * κ₀ ^ Shape.Draws.totB s ds ≤
          κ₀ ^ d.b * (Fintype.card (Fin d.b → Dig lam) : ℝ≥0∞) * κ₀ ^ Shape.Draws.totB s ds :=
        mul_le_mul' hr le_rfl
      _ = _ := by rw [pow_add]; ring

theorem drawsGood : Spec.drawsGood := fun _ _ h1 s ds h _ _ ha hc =>
  (drawsGood_aux h1 s ds h _ (pow_le_pow_right₀ h1 ha)).mono (pow_le_pow_right₀ h1 hc)

end Iop
