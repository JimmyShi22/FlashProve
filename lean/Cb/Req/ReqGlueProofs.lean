-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req/ReqGlueProofs.lean: the proofs of the statements of Cb/Req/ReqGlue.lean on families (more
variables, `Fam.to`, the first of the four steps of gluing; the glued family) and of
`Spec.vtx_shift`, `Spec.ext_low`; the laws of the other three steps are stated and proved here.

The statements on segments and partitions are proved in Cb/Req/ReqGlueProofsSeg.lean. Nothing is
defined here that a statement reads, but `pick`, an abbreviation inside the induction
(`glueFrom_val`).

Terms: lean/GLOSSARY.md.
-/
import Cb.Req.ReqGlue
import Cb.Req.ReqSpecProofs

set_option autoImplicit false

namespace Cb
open Blocks Hiop Finset

theorem vtx_shift : Spec.vtx_shift := by
  intro E _ _ N v b hv
  funext t
  unfold shiftPt vtx
  by_cases ht : t < v
  · have h1 : N - v + t < N := by omega
    have h2 : N - 1 - (N - v + t) = v - 1 - t := by omega
    have h3 : v - 1 - t < v := by omega
    simp only [h1, ht, h2, true_and, Nat.testBit_mod_two_pow, h3, decide_true, Bool.true_and]
  · have h1 : ¬ N - v + t < N := by omega
    simp only [h1, ht, false_and, if_false]

theorem eqN_shift {E : Type} [Field E] (v k : ℕ) (pt : ℕ → E) (c : ℕ) :
    eqN v k pt c = eqN v 0 (shiftPt k pt) c := by
  unfold eqN shiftPt
  simp only [Nat.zero_add]

theorem ext_low : Spec.ext_low := by
  intro E _ N v h pt hv
  obtain ⟨k, rfl⟩ : ∃ k, N = k + v := ⟨N - v, by omega⟩
  rw [Nat.add_sub_cancel]
  have h1 : ∑ a ∈ range (2 ^ k), eqN k 0 pt a = 1 := by
    have := ext_const k (1 : E) pt
    unfold Blocks.ext at this
    simpa using this
  unfold Blocks.ext
  rw [pow_add, Alg.sum_range_mul_add]
  have h2 : ∀ a ∈ range (2 ^ k), ∑ c ∈ range (2 ^ v),
        eqN (k + v) 0 pt (a * 2 ^ v + c) * h ((a * 2 ^ v + c) % 2 ^ v) =
      eqN k 0 pt a * ∑ c ∈ range (2 ^ v), eqN v 0 (shiftPt k pt) c * h c := by
    intro a _
    rw [mul_sum]
    refine sum_congr rfl fun c hc => ?_
    have hc' := mem_range.1 hc
    rw [eqN_append' k v 0 pt a hc', Nat.zero_add, eqN_shift v k pt c,
      Nat.mul_add_mod_of_lt hc', mul_assoc]
  rw [sum_congr rfl h2, ← sum_mul, h1, one_mul]

/-- For j < 2^w, the low v + w bits of the vertex (b, j) are (the low v bits of b, j). -/
theorem mod_pow_add (b v w j : ℕ) (hj : j < 2 ^ w) :
    (b * 2 ^ w + j) % 2 ^ (v + w) = b % 2 ^ v * 2 ^ w + j := by
  have hpos : 0 < 2 ^ w := Nat.two_pow_pos _
  rw [pow_add, Nat.mul_comm (2 ^ v) (2 ^ w), Nat.mod_mul, Nat.mul_add_mod_of_lt hj,
    Nat.add_comm (b * 2 ^ w) j, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hj, Nat.zero_add]
  ring

section
variable {X F E : Type} [Field F] [Field E] [Algebra F E]

/-! ## More variables -/

theorem Atom0.to_val (a : Atom0 E) (Φ : IdxFmt F) {N v : ℕ} (hv : v ≤ N) (W : ℕ → ℕ → F)
    (A : ℕ → ℕ → ℕ → E) (b : ℕ) :
    (a.to N v).val Φ N W A b = a.val Φ v W A (b % 2 ^ v) := by
  cases a with
  | cell f => rfl
  | idx a =>
    show Φ.form (a.g (shiftPt (N - v) (vtx N b))) (a.ψ (shiftPt (N - v) (vtx N b))) W =
      Φ.form (a.g (vtx v (b % 2 ^ v))) (a.ψ (vtx v (b % 2 ^ v))) W
    rw [vtx_shift E N v b hv]

theorem Term.low_val (t : Term X E) (v : ℕ) (x : X) (b : ℕ)
    {Y Y' : ℕ → E} (h : ∀ j ∈ t.atoms, Y j = Y' j) :
    (t.low v).val x b Y = t.val x (b % 2 ^ v) Y' := by
  show t.coef x (b % 2 ^ v) * (t.atoms.map Y).prod = t.coef x (b % 2 ^ v) * (t.atoms.map Y').prod
  rw [List.map_congr_left h]

theorem Poly0.to_val (P : Poly0 X E) (Φ : IdxFmt F) {N : ℕ} (hv : P.v ≤ N) (x : X) (W : ℕ → ℕ → F)
    (A : ℕ → ℕ → ℕ → E) (b : ℕ) :
    (P.to N).val Φ x W A b = P.val Φ x W A (b % 2 ^ P.v) := by
  show ((P.terms.map (Term.low P.v)).map fun t =>
      t.val x b fun j => ((P.atom j).to N P.v).val Φ N W A b).sum = _
  rw [List.map_map]
  unfold Poly0.val
  exact congrArg List.sum
    (List.map_congr_left fun t _ =>
      Term.low_val t P.v x b fun j _ => Atom0.to_val (P.atom j) Φ hv W A b)

theorem Atom.to_val (a : Atom X E) (Φ : IdxFmt F) {N v : ℕ} (hw : a.WF Φ v) (hv : v ≤ N) (x : X)
    (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) (b : ℕ) :
    (a.to N v).val Φ N x W A b = a.val Φ v x W A (b % 2 ^ v) := by
  cases a with
  | base a => exact Atom0.to_val a Φ hv W A b
  | sum w P =>
    show ∑ j ∈ range (2 ^ w), (P.to (N + w)).val Φ x W A (b * 2 ^ w + j) =
      ∑ j ∈ range (2 ^ w), P.val Φ x W A (b % 2 ^ v * 2 ^ w + j)
    refine sum_congr rfl fun j hj => ?_
    rw [Poly0.to_val P Φ (by rw [hw.1]; omega), hw.1, mod_pow_add b v w j (mem_range.1 hj)]

end

theorem to_val : Spec.to_val := by
  intro X F E _ _ _ f Φ N x W A hw hv b
  show ((f.terms.map (Term.low f.v)).map fun t =>
      t.val x b fun j => ((f.atom j).to N f.v).val Φ N x W A b).sum = _
  rw [List.map_map]
  unfold Fam.val
  exact congrArg List.sum
    (List.map_congr_left fun t ht =>
      Term.low_val t f.v x b fun j hj =>
        Atom.to_val (f.atom j) Φ (hw.2 j (hw.1 t ht j hj)) hv x W A b)

section
variable {X F E : Type} [Field F] [Field E] [Algebra F E]

theorem IdxAtom.up_ok (a : IdxAtom E) (Φ : IdxFmt F) {N v : ℕ} (h : a.OK Φ v) (hv : v ≤ N) :
    (a.up (N - v)).OK Φ N := by
  intro W pt
  have h1 : (fun b => (a.up (N - v)).at Φ W (vtx N b)) =
      fun b => (fun b' => a.at Φ W (vtx v b')) (b % 2 ^ v) := by
    funext b
    show Φ.form (a.g (shiftPt (N - v) (vtx N b))) (a.ψ (shiftPt (N - v) (vtx N b))) W =
      Φ.form (a.g (vtx v (b % 2 ^ v))) (a.ψ (vtx v (b % 2 ^ v))) W
    rw [vtx_shift E N v b hv]
  rw [h1, ext_low E N v (fun b' => a.at Φ W (vtx v b')) pt hv, h W (shiftPt (N - v) pt)]
  rfl

theorem Atom0.to_wf (a : Atom0 E) (Φ : IdxFmt F) {N v : ℕ} (h : a.WF Φ v) (hv : v ≤ N) :
    (a.to N v).WF Φ N := by
  cases a with
  | cell f => trivial
  | idx a => exact IdxAtom.up_ok a Φ h hv

omit [Field E] in
theorem mem_low {t : Term X E} {v : ℕ} {l : List (Term X E)} (h : t ∈ l.map (Term.low v)) :
    ∃ t' ∈ l, t.atoms = t'.atoms := by
  obtain ⟨t', ht', rfl⟩ := List.mem_map.1 h
  exact ⟨t', ht', rfl⟩

theorem Poly0.to_wf (P : Poly0 X E) (Φ : IdxFmt F) {N : ℕ} (h : P.WF Φ) (hv : P.v ≤ N) :
    (P.to N).WF Φ := by
  refine ⟨fun t ht j hj => ?_, fun j hj => Atom0.to_wf (P.atom j) Φ (h.2 j hj) hv⟩
  obtain ⟨t', ht', he⟩ := mem_low ht
  exact h.1 t' ht' j (he ▸ hj)

theorem Atom.to_wf (a : Atom X E) (Φ : IdxFmt F) {N v : ℕ} (h : a.WF Φ v) (hv : v ≤ N) :
    (a.to N v).WF Φ N := by
  cases a with
  | base a => exact Atom0.to_wf a Φ h hv
  | sum w P => exact ⟨rfl, Poly0.to_wf P Φ h.2 (by rw [h.1]; omega)⟩

omit [Field E] in
theorem Atom0.to_places (a : Atom0 E) {N v : ℕ} (hv : v ≤ N) :
    (a.to N v).places N = a.places v := by
  cases a with
  | cell f =>
    ext p
    constructor
    · rintro ⟨b, _, t, ht, rfl⟩
      exact ⟨b % 2 ^ v, Nat.mod_lt _ (Nat.two_pow_pos _), t, ht, rfl⟩
    · rintro ⟨b, hb, t, ht, rfl⟩
      refine ⟨b, lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hv), t, ?_, rfl⟩
      show t ∈ (f (b % 2 ^ v)).terms
      rwa [Nat.mod_eq_of_lt hb]
  | idx a => rfl

omit [Field E] in
theorem Poly0.to_places (P : Poly0 X E) {N : ℕ} (hv : P.v ≤ N) : (P.to N).places = P.places := by
  ext p
  show (∃ j < P.na, p ∈ ((P.atom j).to N P.v).places N) ↔ ∃ j < P.na, p ∈ (P.atom j).places P.v
  simp only [Atom0.to_places _ hv]

theorem Atom.to_places (a : Atom X E) (Φ : IdxFmt F) {N v : ℕ} (h : a.WF Φ v) (hv : v ≤ N) :
    (a.to N v).places N = a.places v := by
  cases a with
  | base a => exact Atom0.to_places a hv
  | sum w P => exact Poly0.to_places P (by rw [h.1]; omega)

end

theorem to_wf : Spec.to_wf := by
  intro X F E _ _ _ f Φ N h hv
  refine ⟨fun t ht j hj => ?_, fun j hj => Atom.to_wf (f.atom j) Φ (h.2 j hj) hv⟩
  obtain ⟨t', ht', he⟩ := mem_low ht
  exact h.1 t' ht' j (he ▸ hj)

theorem to_places : Spec.to_places := by
  intro X F E _ _ _ f Φ N h hv
  ext p
  show (∃ j < f.na, p ∈ ((f.atom j).to N f.v).places N) ↔ ∃ j < f.na, p ∈ (f.atom j).places f.v
  constructor
  · rintro ⟨j, hj, hp⟩
    exact ⟨j, hj, by rwa [Atom.to_places _ Φ (h.2 j hj) hv] at hp⟩
  · rintro ⟨j, hj, hp⟩
    exact ⟨j, hj, by rwa [Atom.to_places _ Φ (h.2 j hj) hv]⟩

/-! ## The steps -/

section
variable {X F E : Type} [Field F] [Field E] [Algebra F E] (Φ : IdxFmt F) (x : X)
  (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E)

theorem mask_val (c : X → ℕ → E) (f : Fam X E) (b : ℕ) :
    (f.mask c).val Φ x W A b = c x b * f.val Φ x W A b := by
  show ((f.terms.map fun t => (⟨fun x b => c x b * t.coef x b, t.atoms⟩ : Term X E)).map
      fun t => t.val x b fun j => (f.atom j).val Φ f.v x W A b).sum = _
  unfold Fam.val
  rw [List.map_map, ← List.sum_map_mul_left]
  exact congrArg List.sum (List.map_congr_left fun t _ => mul_assoc _ _ _)

theorem mask_wf (c : X → ℕ → E) {f : Fam X E} (h : f.WF Φ) : (f.mask c).WF Φ := by
  refine ⟨fun t ht j hj => ?_, h.2⟩
  obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
  exact h.1 t' ht' j hj

theorem pub_val (v : ℕ) (c : X → ℕ → E) (b : ℕ) : (Fam.pub v c).val Φ x W A b = c x b := by
  simp [Fam.pub, Fam.val, Term.val]

theorem pub_wf (v : ℕ) (c : X → ℕ → E) : (Fam.pub v c).WF Φ := by
  refine ⟨fun t ht j hj => ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  obtain rfl := List.mem_singleton.1 ht
  exact absurd hj List.not_mem_nil

theorem add_val {f g : Fam X E} (hf : ∀ t ∈ f.terms, ∀ j ∈ t.atoms, j < f.na)
    (hv : g.v = f.v) (b : ℕ) :
    (f.add g).val Φ x W A b = f.val Φ x W A b + g.val Φ x W A b := by
  show ((f.terms ++ g.terms.map fun t => (⟨t.coef, t.atoms.map (· + f.na)⟩ : Term X E)).map fun t =>
      t.val x b fun n => (if n < f.na then f.atom n else g.atom (n - f.na)).val Φ f.v x W A b).sum =
    _
  rw [List.map_append, List.sum_append, List.map_map]
  unfold Fam.val
  congr 1
  · exact congrArg List.sum
      (List.map_congr_left fun t ht =>
        Term.val_congr t x b fun j hj => by rw [if_pos (hf t ht j hj)])
  · refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
    show t.coef x b *
        ((t.atoms.map (· + f.na)).map fun n =>
          (if n < f.na then f.atom n else g.atom (n - f.na)).val Φ f.v x W A b).prod =
      t.coef x b * (t.atoms.map fun j => (g.atom j).val Φ g.v x W A b).prod
    rw [List.map_map, hv]
    refine congrArg (fun l => t.coef x b * List.prod l) (List.map_congr_left fun j _ => ?_)
    show (if j + f.na < f.na then f.atom (j + f.na) else g.atom (j + f.na - f.na)).val
        Φ f.v x W A b = _
    rw [if_neg (by omega), Nat.add_sub_cancel]

theorem add_wf {f g : Fam X E} (hf : f.WF Φ) (hg : g.WF Φ) (hv : g.v = f.v) : (f.add g).WF Φ := by
  refine ⟨fun t ht j hj => ?_, fun n hn => ?_⟩
  · rcases List.mem_append.1 ht with h | h
    · exact lt_of_lt_of_le (hf.1 t h j hj) (Nat.le_add_right _ _)
    · obtain ⟨t', ht', rfl⟩ := List.mem_map.1 h
      obtain ⟨j', hj', rfl⟩ := List.mem_map.1 hj
      have := hg.1 t' ht' j' hj'
      show j' + f.na < f.na + g.na
      omega
  · show (if n < f.na then f.atom n else g.atom (n - f.na)).WF Φ f.v
    by_cases h : n < f.na
    · rw [if_pos h]
      exact hf.2 n h
    · rw [if_neg h, ← hv]
      have hn' : n < f.na + g.na := hn
      exact hg.2 _ (by omega)

omit [Field F] [Field E] [Algebra F E] in
theorem add_places {f g : Fam X E} (hv : g.v = f.v) (p : Place) :
    p ∈ (f.add g).places ↔ p ∈ f.places ∨ p ∈ g.places := by
  show (∃ n < f.na + g.na, p ∈ (if n < f.na then f.atom n else g.atom (n - f.na)).places f.v) ↔
    (∃ j < f.na, p ∈ (f.atom j).places f.v) ∨ ∃ j < g.na, p ∈ (g.atom j).places g.v
  rw [hv]
  constructor
  · rintro ⟨n, hn, hp⟩
    by_cases h : n < f.na
    · rw [if_pos h] at hp
      exact Or.inl ⟨n, h, hp⟩
    · rw [if_neg h] at hp
      exact Or.inr ⟨n - f.na, by omega, hp⟩
  · rintro (⟨j, hj, hp⟩ | ⟨j, hj, hp⟩)
    · exact ⟨j, by omega, by rwa [if_pos hj]⟩
    · exact ⟨j + f.na, by omega, by rwa [if_neg (by omega), Nat.add_sub_cancel]⟩

/-! ## The glued family -/

omit [Field F] [Field E] [Algebra F E] in
theorem le_maxV {L : List (Fam X E)} {f : Fam X E} (h : f ∈ L) : f.v ≤ maxV L := by
  induction L with
  | nil => exact absurd h List.not_mem_nil
  | cons g L ih =>
    show f.v ≤ max g.v (maxV L)
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

omit [Field F] [Algebra F E] in
theorem glueFrom_v (N V i : ℕ) (L : List (Fam X E)) : (glueFrom N V i L).v = N := by
  cases L <;> rfl

/-- family number n at r, or 0 -/
def pick (L : List (Fam X E)) (val : Fam X E → ℕ → E) (n r : ℕ) : E :=
  match L[n]? with
  | some f => if r < 2 ^ f.v then val f r else 0
  | none => 0

omit [Field F] [Algebra F E] in
theorem pick_step (f : Fam X E) (L : List (Fam X E)) (val : Fam X E → ℕ → E) (i n r : ℕ)
    (y : E) (hy : r < 2 ^ f.v → y = val f r) :
    (if n = i ∧ r < 2 ^ f.v then 1 else 0) * y +
        (if i + 1 ≤ n then pick L val (n - (i + 1)) r else 0) =
      if i ≤ n then pick (f :: L) val (n - i) r else 0 := by
  rcases lt_trichotomy n i with hlt | heq | hgt
  · rw [if_neg (fun hc => absurd hc.1 (by omega)), if_neg (show ¬ i + 1 ≤ n by omega),
      if_neg (show ¬ i ≤ n by omega), zero_mul, add_zero]
  · subst heq
    rw [if_neg (show ¬ n + 1 ≤ n by omega), if_pos (le_refl n), add_zero, Nat.sub_self]
    show _ = if r < 2 ^ f.v then val f r else 0
    by_cases hr : r < 2 ^ f.v
    · rw [if_pos ⟨rfl, hr⟩, if_pos hr, one_mul, hy hr]
    · rw [if_neg (fun hc => hr hc.2), if_neg hr, zero_mul]
  · rw [if_neg (fun hc => absurd hc.1 (by omega)), if_pos (show i + 1 ≤ n by omega),
      if_pos (show i ≤ n by omega), zero_mul, zero_add]
    obtain ⟨k, hk⟩ : ∃ k, n - i = k + 1 := ⟨n - i - 1, by omega⟩
    have hk' : n - (i + 1) = k := by omega
    rw [hk, hk']
    rfl

theorem glueFrom_val {N V : ℕ} (hN : V ≤ N) :
    ∀ (L : List (Fam X E)) (i : ℕ), (∀ f ∈ L, f.WF Φ ∧ f.v ≤ V) →
      ∀ b, (glueFrom N V i L).val Φ x W A b =
        if i ≤ b / 2 ^ V then pick L (fun f b' => f.val Φ x W A b') (b / 2 ^ V - i) (b % 2 ^ V)
        else 0
  | [], i, _, b => by
    show (Fam.pub N fun _ _ => (0 : E)).val Φ x W A b = _
    rw [pub_val]
    split_ifs <;> rfl
  | f :: L, i, h, b => by
    have hf := h f List.mem_cons_self
    show (Fam.add
          (Fam.mask (fun _ b => if b / 2 ^ V = i ∧ b % 2 ^ V < 2 ^ f.v then 1 else 0) (f.to N))
          (glueFrom N V (i + 1) L)).val
        Φ x W A b = _
    rw [add_val Φ x W A (mask_wf Φ _ (to_wf X F E f Φ N hf.1 (le_trans hf.2 hN))).1
          (glueFrom_v N V (i + 1) L),
      mask_val, to_val X F E f Φ N x W A hf.1 (le_trans hf.2 hN),
      glueFrom_val hN L (i + 1) (fun g hg => h g (List.mem_cons_of_mem _ hg)) b]
    refine pick_step f L (fun f b' => f.val Φ x W A b') i (b / 2 ^ V) (b % 2 ^ V) _ fun hr => ?_
    rw [← Nat.mod_mod_of_dvd b (pow_dvd_pow 2 hf.2), Nat.mod_eq_of_lt hr]

theorem glueFrom_wf {N V : ℕ} (hN : V ≤ N) :
    ∀ (L : List (Fam X E)) (i : ℕ), (∀ f ∈ L, f.WF Φ ∧ f.v ≤ V) → (glueFrom N V i L).WF Φ
  | [], _, _ => pub_wf Φ N _
  | f :: L, i, h => by
    have hf := h f List.mem_cons_self
    exact add_wf Φ (mask_wf Φ _ (to_wf X F E f Φ N hf.1 (le_trans hf.2 hN)))
      (glueFrom_wf hN L (i + 1) fun g hg => h g (List.mem_cons_of_mem _ hg))
      (glueFrom_v N V (i + 1) L)

theorem glueFrom_places {N V : ℕ} (hN : V ≤ N) :
    ∀ (L : List (Fam X E)) (i : ℕ),
      (∀ f ∈ L, f.WF Φ ∧ f.v ≤ V) → ∀ p, p ∈ (glueFrom N V i L).places ↔ ∃ f ∈ L, p ∈ f.places
  | [], _, _, p => by
    constructor
    · rintro ⟨j, hj, -⟩
      exact absurd hj (Nat.not_lt_zero j)
    · rintro ⟨f, hf, -⟩
      exact absurd hf List.not_mem_nil
  | f :: L, i, h, p => by
    have hf := h f List.mem_cons_self
    show p ∈ (Fam.add
          (Fam.mask (fun _ b => if b / 2 ^ V = i ∧ b % 2 ^ V < 2 ^ f.v then 1 else 0) (f.to N))
          (glueFrom N V (i + 1) L)).places ↔
      _
    rw [add_places (glueFrom_v N V (i + 1) L),
      glueFrom_places hN L (i + 1) (fun g hg => h g (List.mem_cons_of_mem _ hg)) p]
    have h1 : (Fam.mask
          (fun (_ : X) b => if b / 2 ^ V = i ∧ b % 2 ^ V < 2 ^ f.v then (1 : E) else 0)
          (f.to N)).places = f.places :=
      to_places X F E f Φ N hf.1 (le_trans hf.2 hN)
    rw [h1, List.exists_mem_cons_iff]

end

theorem maxV_le_glueN {X E : Type} (L : List (Fam X E)) : maxV L ≤ glueN L := Nat.le_add_left _ _

theorem glue_hyp {X F E : Type} [Field F] [Field E] [Algebra F E] {L : List (Fam X E)}
    {Φ : IdxFmt F} (h : ∀ f ∈ L, f.WF Φ) :
    ∀ f ∈ L, f.WF Φ ∧ f.v ≤ maxV L :=
  fun f hf => ⟨h f hf, le_maxV hf⟩

theorem glue_val : Spec.glue_val := by
  intro X F E _ _ _ L pad Φ x W A h b
  show (Fam.add (Fam.pub (glueN L) fun _ b => if liveAt (maxV L) L b then 0 else pad)
        (glueFrom (glueN L) (maxV L) 0 L)).val
      Φ x W A b = _
  rw [add_val Φ x W A (f := Fam.pub (glueN L) fun _ b => if liveAt (maxV L) L b then 0 else pad)
        (g := glueFrom (glueN L) (maxV L) 0 L) (pub_wf Φ _ _).1 (glueFrom_v _ _ _ _),
    pub_val, glueFrom_val Φ x W A (maxV_le_glueN L) L 0 (glue_hyp h) b,
    if_pos (Nat.zero_le _), Nat.sub_zero]
  unfold liveAt pick glueVal
  cases L[b / 2 ^ maxV L]? with
  | none => simp
  | some f =>
    by_cases hr : b % 2 ^ maxV L < 2 ^ f.v
    · simp [hr]
    · simp [hr]

theorem glue_wf : Spec.glue_wf := by
  intro X F E _ _ _ L pad Φ h
  exact add_wf Φ (pub_wf Φ _ _)
    (glueFrom_wf Φ (maxV_le_glueN L) L 0 (glue_hyp h)) (glueFrom_v _ _ _ _)

theorem glue_places : Spec.glue_places := by
  intro X F E _ _ _ L pad Φ h p
  show p ∈ (Fam.add (Fam.pub (glueN L) fun _ b => if liveAt (maxV L) L b then 0 else pad)
        (glueFrom (glueN L) (maxV L) 0 L)).places ↔
    _
  rw [add_places (f := Fam.pub (glueN L) fun _ b => if liveAt (maxV L) L b then 0 else pad)
        (g := glueFrom (glueN L) (maxV L) 0 L) (glueFrom_v _ _ _ _),
    glueFrom_places Φ (maxV_le_glueN L) L 0 (glue_hyp h) p]
  constructor
  · rintro (⟨j, hj, -⟩ | h1)
    · exact absurd hj (Nat.not_lt_zero j)
    · exact h1
  · exact Or.inr

/-- A property of all values `glueVal` of the glued family: if it holds of pad, then it holds at all
vertices iff it holds of all values of all families. -/
theorem forall_glueVal {X E : Type} (L : List (Fam X E)) (val : Fam X E → ℕ → E) (pad : E)
    (Pr : E → Prop) (hpad : Pr pad) :
    (∀ b < 2 ^ glueN L, Pr (glueVal (maxV L) L val pad b)) ↔
    ∀ f ∈ L, ∀ b < 2 ^ f.v, Pr (val f b) := by
  constructor
  · intro h f hf b' hb'
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hf
    have hV : b' < 2 ^ maxV L :=
      lt_of_lt_of_le hb' (Nat.pow_le_pow_right (by norm_num) (le_maxV hf))
    have hdiv : (n * 2 ^ maxV L + b') / 2 ^ maxV L = n := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _),
        Nat.div_eq_of_lt hV, Nat.zero_add]
    have hmod : (n * 2 ^ maxV L + b') % 2 ^ maxV L = b' := Nat.mul_add_mod_of_lt hV
    have hlt : n * 2 ^ maxV L + b' < 2 ^ glueN L := by
      unfold glueN
      rw [pow_add]
      calc n * 2 ^ maxV L + b' < n * 2 ^ maxV L + 2 ^ maxV L := Nat.add_lt_add_left hV _
        _ = (n + 1) * 2 ^ maxV L := by ring
        _ ≤ 2 ^ Nat.clog 2 L.length * 2 ^ maxV L :=
          Nat.mul_le_mul_right _ (le_trans hn (Nat.le_pow_clog (by norm_num) _))
    have h1 := h _ hlt
    unfold glueVal at h1
    rw [hdiv, hmod, List.getElem?_eq_getElem hn] at h1
    simpa [hb'] using h1
  · intro h b _
    unfold glueVal
    cases hL : L[b / 2 ^ maxV L]? with
    | none => exact hpad
    | some f =>
      show Pr (if b % 2 ^ maxV L < 2 ^ f.v then val f (b % 2 ^ maxV L) else pad)
      by_cases hr : b % 2 ^ maxV L < 2 ^ f.v
      · rw [if_pos hr]
        exact h f (List.mem_of_getElem? hL) _ hr
      · rw [if_neg hr]
        exact hpad

theorem glue_zero_iff : Spec.glue_zero_iff := by
  intro X F E _ _ _ L Φ x W A h
  simp only [glue_val X F E L 0 Φ x W A h]
  exact forall_glueVal L (fun f b' => f.val Φ x W A b') 0 (fun e => e = 0) rfl

theorem glue_key_iff : Spec.glue_key_iff := by
  intro X F E _ _ _ L T Φ x W A h
  simp only [glue_val X F E L _ Φ x W A h]
  exact forall_glueVal L (fun f b' => f.val Φ x W A b') _
    (fun e => ∃ u ∈ T.set, e = algebraMap F E u) ⟨T.t 0, ⟨0, Nat.two_pow_pos _, rfl⟩, rfl⟩

end Cb
