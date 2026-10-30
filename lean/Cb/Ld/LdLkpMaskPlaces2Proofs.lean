-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMaskPlaces2Proofs.lean: the proofs of the statements of Cb/Ld/LdLkpMaskPlaces2.lean (the
conditions on the places of the masks of the assembled lookup `LkAsm2` (Cb/Ld/LdLkpAsm2.lean), from
four plain ones; the number of own masks).

The generic parts (own places of a tie's step and of a tree's level; the conditions of a tree in the
data's own fields) are those of Cb/Ld/LdLkpMaskPlacesProofs.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMaskPlaces2
import Cb.Ld.LdLkpMaskPlacesProofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp Cb.Lkp

section
variable (E : Type) [Field E] [Fintype E]

variable {E}
variable (A : LkAsm2 E)

/-- The own places of the parts, as places of names. -/
theorem LdLkp.LkAsm2.nm_tie {l : ℕ} (hl : l ≤ A.n) {j : A.J} (h : A.H.tie.ownAt l j) :
    (l = 0 ∧ ∃ i, j = A.plN (.s i)) ∨ ∃ l' h' i, l = l' + 1 ∧ j = A.plN (.t l' h' i) := by
  cases l with
  | zero => exact Or.inl ⟨rfl, h⟩
  | succ l' =>
      obtain ⟨i, hi⟩ := h
      exact Or.inr ⟨l', hl, i, rfl, hi⟩

theorem LdLkp.LkAsm2.nm_k {l : ℕ} (hl : l ≤ A.v') {j : A.J}
    (h : (A.IK.setV (A.v' + 1)).DK.ownAt l j) : ∃ i, j = A.plN (.k l hl i) :=
  (ldLkpPlaces_treeOwn E (A.IK.setV (A.v' + 1)).DK l j).1 h

theorem LdLkp.LkAsm2.nm_f {l : ℕ} (hl : l < A.d) {j : A.J} (h : A.D.ownAt l j) :
    ∃ i, j = A.plN (.f l hl i) :=
  (ldLkpPlaces_treeOwn E A.D l j).1 h

theorem LdLkp.LkAsm2.nm_swTie {j : A.J} (h : A.swTie j) :
    (∃ i, j = A.plN (.s i)) ∨ ∃ l h' i, j = A.plN (.t l h' i) := by
  obtain ⟨l, hl, h⟩ := h
  rcases A.nm_tie hl h with ⟨_, i, hi⟩ | ⟨l', h', i, _, hi⟩
  · exact Or.inl ⟨i, hi⟩
  · exact Or.inr ⟨l', h', i, hi⟩

variable (E)

theorem ldLkpPlaces2_sw : Spec.ldLkpPlaces2_sw E := by
  intro A j
  constructor
  · rintro (h | ⟨l, hl, h⟩ | ⟨l, hl, h⟩ | h | h)
    · rcases A.nm_swTie h with ⟨i, hi⟩ | ⟨l, h', i, hi⟩
      · exact ⟨_, hi⟩
      · exact ⟨_, hi⟩
    · exact ⟨_, (A.nm_k hl h).choose_spec⟩
    · exact ⟨_, (A.nm_f hl h).choose_spec⟩
    · obtain ⟨i, hi⟩ := h
      exact ⟨.e i, hi⟩
    · obtain ⟨i, hi⟩ := h
      exact ⟨.b i, hi⟩
  · rintro ⟨a, rfl⟩
    cases a with
    | s i => exact Or.inl ⟨0, Nat.zero_le _, i, rfl⟩
    | t l h i => exact Or.inl ⟨l + 1, h, i, rfl⟩
    | k l h i => exact Or.inr (Or.inl ⟨l, h, (ldLkpPlaces_treeOwn E (A.IK.setV (A.v' + 1)).DK l _).2 ⟨i, rfl⟩⟩)
    | f l h i => exact Or.inr (Or.inr (Or.inl ⟨l, h, (ldLkpPlaces_treeOwn E A.D l _).2 ⟨i, rfl⟩⟩))
    | e i => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, rfl⟩)))
    | b i => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)))

theorem ldLkpPlaces2_ok : Spec.ldLkpPlaces2_ok E := by
  classical
  intro A Dt h
  have hbit : ∀ m m' : A.J → E,
      (∀ j, Dt j → m j = m' j) → (fun u j => m (A.bAt u j)) = fun u j => m' (A.bAt u j) :=
    fun m m' hm => funext fun u => funext fun j => hm _ (h.bits u j)
  have hbitOn : ∀ m m' : A.J → E, (∀ j, Dt j → m j = m' j) →
      A.IT.bitOn A.n m = A.IT.bitOn A.n m' := fun m m' hm => funext fun u => funext fun j => by
    show (if j < A.n + 1 then m (A.bAt u j) else 0) = if j < A.n + 1 then m' (A.bAt u j) else 0
    rw [hm _ (h.bits u j)]
  -- the incoming forms read masks of the tie only
  have hfK : ∀ x j, ¬ A.swTie j → A.fK x j = 0 := fun x j hj =>
    if_neg fun e => hj ⟨0, Nat.zero_le _, .inr false, e⟩
  have hfT : ∀ x θ j, ¬ A.swTie j → A.formT x θ j = 0 := by
    intro x θ j hj
    unfold LkAsm2.formT
    split_ifs with h1 h2
    · exact if_neg fun e => hj ⟨numLE θ + 1, h1, .inr true, e⟩
    · refine Finset.sum_eq_zero fun j' _ => ?_
      by_cases h3 : (A.H.tie.lv (A.n + 1)).toJ j' = j
      · refine (if_pos h3).trans ?_
        refine if_neg fun e => hj ⟨A.n, le_refl _, .inr (A.H.tie.lv A.n).nx, ?_⟩
        rw [← h3, e]
        rfl
      · exact if_neg h3
    · rfl
  have tie : A.H.tie.MaskOK A.n Dt :=
    { inj := fun l hl => by
        cases l with
        | zero => exact fun a b e => LkAsm2.Nm.s.inj (h.inj (a₁ := .s a) (a₂ := .s b) e)
        | succ l =>
          exact fun a b e => (LkAsm2.Nm.t.inj (h.inj (a₁ := .t l hl a) (a₂ := .t l hl b) e)).2
      disj := fun l l' hll hl' j hj hj' => by
        rcases A.nm_tie (le_trans (le_of_lt hll) hl') hj with ⟨rfl, i, hi⟩ | ⟨l₁, h₁, i, rfl, hi⟩
          <;> rcases A.nm_tie hl' hj' with ⟨rfl, i', hi'⟩ | ⟨l₂, h₂, i', rfl, hi'⟩
        · exact absurd hll (lt_irrefl _)
        · exact absurd (h.inj (hi.symm.trans hi')) (fun e => by cases e)
        · exact absurd hll (Nat.not_lt_zero _)
        · have e := (LkAsm2.Nm.t.inj (h.inj (hi.symm.trans hi'))).1
          subst e
          exact absurd hll (lt_irrefl _)
      rd := fun st m m' hm => by
        have hk := h.keys st.1 m m' hm
        have hP : A.H.PT st m = A.H.PT st m' := funext fun j => by
          show tabProd A.d (A.tab st.1) (fun u j => m (A.bAt u j)) st.2 j =
            tabProd A.d (A.tab st.1) (fun u j => m' (A.bAt u j)) st.2 j
          rw [hbit m m' hm]
        refine ⟨?_, hP, funext fun j => ?_⟩
        · show keyProd (A.v' + 1) (A.key st.1 m) st.2 = keyProd (A.v' + 1) (A.key st.1 m') st.2
          rw [hk]
        · show Lkp.hU (A.n + 1) (A.H.PT st m) j = Lkp.hU (A.n + 1) (A.H.PT st m') j
          rw [hP]
      dt := fun l hl j hd hj => by
        rcases A.nm_tie hl hj with ⟨_, i, hi⟩ | ⟨l₁, h₁, i, _, hi⟩
        · exact h.out _ (hi ▸ hd)
        · exact h.out _ (hi ▸ hd) }
  -- a place of a name of another kind is no mask of the tie
  have notTie : ∀ a : A.Nm, (∀ i, a ≠ .s i) → (∀ l h' i, a ≠ .t l h' i) → ¬ A.swTie (A.plN a) := by
    intro a h1 h2 hs
    rcases A.nm_swTie hs with ⟨i, hi⟩ | ⟨l, h', i, hi⟩
    · exact h1 i (h.inj hi)
    · exact h2 l h' i (h.inj hi)
  have keyT : (A.IK.setV (A.v' + 1)).DK.MaskOK A.v' Dt A.swTie :=
    ldLkpPlaces_tree E (A.IK.setV (A.v' + 1)).DK A.v' Dt A.swTie
      (fun l hl a b e =>
        eq_of_heq (LkAsm2.Nm.k.inj (h.inj (a₁ := .k l hl a) (a₂ := .k l hl b) e)).2)
      (fun l l' hll hl' i i' e =>
        absurd (LkAsm2.Nm.k.inj
            (h.inj (a₁ := .k l (le_trans (le_of_lt hll) hl') i) (a₂ := .k l' hl' i') e)).1
          (ne_of_lt hll))
      (fun st m m' hm => by
        show (fun l =>
            cubeLvl 0 (A.v' + 1) (facK (A.key (A.b2 (A.oR st)).1 m) (A.b2 (A.oR st)).2) l) =
          fun l => cubeLvl 0 (A.v' + 1) (facK (A.key (A.b2 (A.oR st)).1 m') (A.b2 (A.oR st)).2) l
        rw [h.keys _ m m' hm])
      (fun l hl i => h.out (.k l hl i))
      (fun st _ j hj => hfK (A.oR st) j hj)
      (fun l hl i => notTie (.k l hl i) (fun _ e => by cases e) fun _ _ _ e => by cases e)
  have lev : ∀ l < A.d, A.D.MaskOK l Dt A.swTie := fun l hl =>
    ldLkpPlaces_tree E A.D l Dt A.swTie
      (fun l' hl' a b e =>
        eq_of_heq (LkAsm2.Nm.f.inj
            (h.inj (a₁ := .f l' (lt_of_le_of_lt hl' hl) a)
              (a₂ := .f l' (lt_of_le_of_lt hl' hl) b) e)).2)
      (fun l₁ l₂ hll hl₂ i i' e =>
        absurd (LkAsm2.Nm.f.inj
            (h.inj (a₁ := .f l₁ (lt_of_le_of_lt (le_trans (le_of_lt hll) hl₂) hl) i)
              (a₂ := .f l₂ (lt_of_le_of_lt hl₂ hl) i') e)).1 (ne_of_lt hll))
      (fun st m m' hm => by
        show (fun l =>
            cubeLvl A.w A.d
              (facT A.w (A.tab (A.b2 (A.oR (A.o4 st))).1)
                (A.IT.bitOn A.n m) (A.b2 (A.oR (A.o4 st))).2) l) =
          fun l =>
            cubeLvl A.w A.d
              (facT A.w (A.tab (A.b2 (A.oR (A.o4 st))).1)
                (A.IT.bitOn A.n m') (A.b2 (A.oR (A.o4 st))).2) l
        rw [hbitOn m m' hm])
      (fun l' hl' i => h.out (.f l' (lt_of_le_of_lt hl' hl) i))
      (fun st ϱ j hj =>
        Finset.sum_eq_zero fun θ _ =>
          (congrArg (fun z => Alg.eqk ϱ θ * z) (hfT (A.oR (A.o4 st)) θ j hj)).trans (mul_zero _))
      (fun l' hl' i =>
        notTie (.f l' (lt_of_le_of_lt hl' hl) i) (fun _ e => by cases e) fun _ _ _ e => by cases e)
  refine
    { tie := tie
      keyT := keyT
      lev := lev
      inc := fun st ϱ j hj =>
        Finset.sum_eq_zero fun θ _ =>
          (congrArg (fun z => Alg.eqk ϱ θ * z) (hfT (A.oR (A.o4 st)) θ j hj)).trans (mul_zero _)
      bits := h.bits
      injE := fun a b e => LkAsm2.Nm.e.inj (h.inj (a₁ := .e a) (a₂ := .e b) e)
      injB := fun a b e => LkAsm2.Nm.b.inj (h.inj (a₁ := .b a) (a₂ := .b b) e)
      dtE := fun j hd ⟨i, hi⟩ => by
        have hi2 : j = A.plN (.e i) := hi
        exact h.out (.e i) (hi2 ▸ hd)
      dtB := fun j hd ⟨i, hi⟩ => by
        have hi2 : j = A.plN (.b i) := hi
        exact h.out (.b i) (hi2 ▸ hd)
      inE := fun j hs ⟨i, hi⟩ => by
        have hi2 : j = A.plN (.e i) := hi
        exact notTie (.e i) (fun _ e => by cases e) (fun _ _ _ e => by cases e) (hi2 ▸ hs)
      inB := fun j hs ⟨i, hi⟩ => by
        have hi2 : j = A.plN (.b i) := hi
        exact notTie (.b i) (fun _ e => by cases e) (fun _ _ _ e => by cases e) (hi2 ▸ hs)
      fE := fun j ⟨l, hl, hf⟩ ⟨i, hi⟩ => by
        obtain ⟨i', hi'⟩ := A.nm_f hl hf
        have hi2 : j = A.plN (.e i) := hi
        exact absurd (h.inj (hi'.symm.trans hi2)) (fun e => by cases e)
      fB := fun j ⟨l, hl, hf⟩ ⟨i, hi⟩ => by
        obtain ⟨i', hi'⟩ := A.nm_f hl hf
        have hi2 : j = A.plN (.b i) := hi
        exact absurd (h.inj (hi'.symm.trans hi2)) (fun e => by cases e)
      eB := fun j ⟨i, hi⟩ ⟨i', hi'⟩ =>
        absurd (h.inj (a₁ := .e i) (a₂ := .b i') (hi.symm.trans hi')) (fun e => by cases e)
      kT := ?_ }
  rintro j ⟨l, hl, hk⟩ hT
  obtain ⟨i, hi⟩ := A.nm_k hl hk
  rcases hT with ⟨l', hl', hf⟩ | ⟨i', hi'⟩ | ⟨i', hi'⟩
  · obtain ⟨i', hi'⟩ := A.nm_f hl' hf
    exact absurd (h.inj (hi.symm.trans hi')) (fun e => by cases e)
  · exact absurd (h.inj (a₂ := .e i') (hi.symm.trans hi')) (fun e => by cases e)
  · exact absurd (h.inj (a₂ := .b i') (hi.symm.trans hi')) (fun e => by cases e)

/-! ### The number of own masks -/

/-- The names, as a sum of finite types. -/
def LdLkp.LkAsm2.nmEquiv (A : LkAsm2 E) :
    A.Nm ≃ ((PIdx (([] : List (PFmt E)) ++ [pDummy E 1]) ⊕ Bool)
          ⊕ (Fin A.n × (PIdx (([] : List (PFmt E)) ++ [pDummy E 3]) ⊕ Bool)))
        ⊕ (((Σ l : Fin (A.v' + 1),
              PIdx (List.replicate (0 + (l : ℕ)) (pfCube E 2) ++ [pDummy E 2]) ⊕ Bool)
            ⊕ (Σ l : Fin A.d,
              PIdx (List.replicate (A.w + (l : ℕ)) (pfCube E 2) ++ [pDummy E 2]) ⊕ Bool))
          ⊕ (PIdx (List.replicate (A.w + A.d) (pfCube E 2)) ⊕
            (PIdx (List.replicate (A.w + A.d) (pfCube E 2) ++ [pDummy E 2]) ⊕ Unit))) where
  toFun
    | .s i => .inl (.inl i)
    | .t l h i => .inl (.inr (⟨l, h⟩, i))
    | .k l h i => .inr (.inl (.inl ⟨⟨l, Nat.lt_succ_of_le h⟩, i⟩))
    | .f l h i => .inr (.inl (.inr ⟨⟨l, h⟩, i⟩))
    | .e i => .inr (.inr (.inl i))
    | .b i => .inr (.inr (.inr i))
  invFun
    | .inl (.inl i) => .s i
    | .inl (.inr (l, i)) => .t l.1 l.2 i
    | .inr (.inl (.inl ⟨l, i⟩)) => .k l.1 (Nat.le_of_lt_succ l.2) i
    | .inr (.inl (.inr ⟨l, i⟩)) => .f l.1 l.2 i
    | .inr (.inr (.inl i)) => .e i
    | .inr (.inr (.inr i)) => .b i
  left_inv := by rintro (i | ⟨l, h, i⟩ | ⟨l, h, i⟩ | ⟨l, h, i⟩ | i | i) <;> rfl
  right_inv := by rintro ((i | ⟨l, i⟩) | ((⟨l, i⟩ | ⟨l, i⟩) | (i | i))) <;> rfl

theorem card_pidx (k D : ℕ) :
    Fintype.card (PIdx (List.replicate k (pfCube E 2) ++ [pDummy E D])) = 1 + 2 * k + D := by
  rw [psc_own_card E]
  simp [pfCube, pDummy]
  ring

theorem card_pidx0 (k : ℕ) : Fintype.card (PIdx (List.replicate k (pfCube E 2))) = 1 + 2 * k := by
  rw [psc_own_card E]
  simp [pfCube]
  ring

theorem card_pidxN (D : ℕ) :
    Fintype.card (PIdx (([] : List (PFmt E)) ++ [pDummy E D])) = 1 + D := by
  rw [psc_own_card E]
  simp [pDummy]

/-- The sum of 2 l + c over l < n. -/
theorem sum_two_add (c : ℕ) : ∀ n, ∑ l ∈ Finset.range n, (2 * l + c) + n = n ^ 2 + c * n
  | 0 => by simp
  | n + 1 => by
    have ih := sum_two_add c n
    rw [Finset.sum_range_succ]
    nlinarith [ih]

theorem ldLkpPlaces2_card : Spec.ldLkpPlaces2_card E := by
  intro A
  rw [Nat.card_congr (A.nmEquiv E), Nat.card_eq_fintype_card]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_sigma, Fintype.card_fin,
    Fintype.card_bool, Fintype.card_unit, card_pidx E, card_pidx0 E, card_pidxN E]
  have hK : ∑ l : Fin (A.v' + 1), (1 + 2 * (0 + (l : ℕ)) + 2 + 2) =
      ∑ l ∈ Finset.range (A.v' + 1), (2 * l + 5) :=
    (Finset.sum_congr rfl fun l _ => by omega).trans
      (Fin.sum_univ_eq_sum_range (fun l => 2 * l + 5) (A.v' + 1))
  have hF : ∑ l : Fin A.d, (1 + 2 * (A.w + (l : ℕ)) + 2 + 2) =
      ∑ l ∈ Finset.range A.d, (2 * l + (2 * A.w + 5)) :=
    (Finset.sum_congr rfl fun l _ => by omega).trans
      (Fin.sum_univ_eq_sum_range (fun l => 2 * l + (2 * A.w + 5)) A.d)
  rw [hK, hF]
  have h1 := sum_two_add 5 (A.v' + 1)
  have h2 := sum_two_add (2 * A.w + 5) A.d
  nlinarith [h1, h2]

end
end Cb
