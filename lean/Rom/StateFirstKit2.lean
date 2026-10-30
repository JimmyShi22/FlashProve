-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstKit2.lean: the step that expands a long answer of a random oracle from a state
(Rom/StateFirst.lean): composition of mixed programs (Rom/StateFirstMix.lean); query bounds;
programs in which no raw query follows a typed one (`RawFirst`), and `mixClose_rawFirst` for them.

The step leads from a family S of typed oracles, the first family, to the second, `stSpec S lam C`.
There a chain oracle returns only a state: the chaining value and the last block, hid, of its old
answer; the other hash blocks are answers of an added oracle dr to expansion queries (state,
counter). (`Link`, `stSpec`: Rom/StateFirst.lean.) A mixed program (over `mixSpec`) makes typed
queries (the honest side's, to the first family) and raw queries (an adversary's, to the second).
The ideal interpretations (`ideal`) are programs over the first family, in which a reduction answers
the raw expansion queries from a table (`Book`). `MixBound C c t r`: at most t typed queries at
chain oracles and r raw queries.

In `shadow` (the reduction's table bF, a shadow table bT, a flag for a disagreement) the flag is not
raised by a program with `RawFirst`, under the start conditions of `shadow_rawFirst`.
-/
import Rom.StateFirstColl2

set_option autoImplicit false

namespace Rom
open Prob
open scoped ENNReal

variable {S : OSpec} {lam : ℕ} (C : ∀ o, Link lam (S.Rng o)) {α β : Type}

theorem stateFirst_bind (c : OComp S α) (g : α → OComp S β) :
    (c.bind g).stateFirst C = (c.stateFirst C).bind fun a => (g a).stateFirst C := by
  induction c with
  | pure a => rfl
  | sample n k ih => simp only [OComp.bind, OComp.stateFirst, ih]
  | query o q k ih => simp only [OComp.bind, OComp.stateFirst, ih, OComp.bind_assoc]

theorem liftT_bind (c : OComp S α) (g : α → OComp S β) :
    liftT C (c.bind g) = (liftT C c).bind fun a => liftT C (g a) := by
  induction c with
  | pure a => rfl
  | sample n k ih => simp only [OComp.bind, liftT, ih]
  | query o q k ih => simp only [OComp.bind, liftT, ih]

theorem liftR_bind (c : OComp (stSpec S lam C) α) (g : α → OComp (stSpec S lam C) β) :
    liftR C (c.bind g) = (liftR C c).bind fun a => liftR C (g a) := by
  induction c with
  | pure a => rfl
  | sample n k ih => simp only [OComp.bind, liftR, ih]
  | query o q k ih => simp only [OComp.bind, liftR, ih]

variable {C}

theorem MixBound.mono {c : OComp (mixSpec C) α} :
    ∀ {t r t' r' : ℕ}, MixBound C c t r → t ≤ t' → r ≤ r' → MixBound C c t' r' := by
  induction c with
  | pure a => exact fun _ _ _ => trivial
  | sample n k ih => exact fun h ht hr x => ih x (h x) ht hr
  | query x q k ih =>
    intro t r t' r' h ht hr
    match x, q, k, ih, h with
    | .inl o, q, k, ih, h =>
      have h' : if (C o).isPlain = true then
        ∀ x, MixBound C (k x) t r else ∃ t0, t = t0 + 1 ∧ ∀ x, MixBound C (k x) t0 r := h
      show if (C o).isPlain = true then
        ∀ x, MixBound C (k x) t' r' else ∃ t0, t' = t0 + 1 ∧ ∀ x, MixBound C (k x) t0 r'
      by_cases hp : (C o).isPlain = true
      · rw [if_pos hp] at h' ⊢
        exact fun x => ih x (h' x) ht hr
      · rw [if_neg hp] at h' ⊢
        obtain ⟨t0, rfl, h0⟩ := h'
        exact ⟨t' - 1, by omega, fun x => ih x (h0 x) (by omega) hr⟩
    | .inr y, q, k, ih, h =>
      cases r with
      | zero => exact absurd h (by simp [MixBound])
      | succ r0 =>
        obtain ⟨r1, rfl⟩ : ∃ r1, r' = r1 + 1 := ⟨r' - 1, by omega⟩
        have h' : ∀ x, MixBound C (k x) t r0 := h
        exact fun x => ih x (h' x) ht (by omega)

theorem MixBound.bind {c : OComp (mixSpec C) α} {g : α → OComp (mixSpec C) β}
    {t' r' : ℕ} (hg : ∀ a, MixBound C (g a) t' r') :
    ∀ {t r : ℕ}, MixBound C c t r → MixBound C (c.bind g) (t + t') (r + r') := by
  induction c with
  | pure a => exact fun _ => (hg a).mono (by omega) (by omega)
  | sample n k ih => exact fun h x => ih x (h x)
  | query x q k ih =>
    intro t r h
    match x, q, k, ih, h with
    | .inl o, q, k, ih, h =>
      have h' : if (C o).isPlain = true then
        ∀ x, MixBound C (k x) t r else ∃ t0, t = t0 + 1 ∧ ∀ x, MixBound C (k x) t0 r := h
      show if (C o).isPlain = true then
        ∀ x, MixBound C ((k x).bind g) (t + t') (r + r')
          else ∃ t0, t + t' = t0 + 1 ∧ ∀ x, MixBound C ((k x).bind g) t0 (r + r')
      by_cases hp : (C o).isPlain = true
      · rw [if_pos hp] at h' ⊢
        exact fun x => ih x (h' x)
      · rw [if_neg hp] at h' ⊢
        obtain ⟨t0, rfl, h0⟩ := h'
        exact ⟨t0 + t', by omega, fun x => ih x (h0 x)⟩
    | .inr y, q, k, ih, h =>
      cases r with
      | zero => exact absurd h (by simp [MixBound])
      | succ r0 =>
        have h' : ∀ x, MixBound C (k x) t r0 := h
        rw [show r0 + 1 + r' = r0 + r' + 1 by omega]
        exact fun x => ih x (h' x)

theorem mixBound_liftT (c : OComp S α) :
    ∀ n, c.CostBoundAt (wCh C) n → MixBound C (liftT C c) n 0 := by
  induction c with
  | pure a => exact fun _ _ => trivial
  | sample n k ih => exact fun m h x => ih x m (h x)
  | query o q k ih =>
    rintro n ⟨n', rfl, h⟩
    show if (C o).isPlain = true then
      ∀ x, MixBound C (liftT C (k x)) (wCh C o q + n') 0
        else ∃ t0, wCh C o q + n' = t0 + 1 ∧ ∀ x, MixBound C (liftT C (k x)) t0 0
    by_cases hp : (C o).isPlain = true
    · rw [if_pos hp]
      exact fun x => (ih x n' (h x)).mono (by omega) le_rfl
    · rw [if_neg hp]
      refine ⟨n', ?_, fun x => ih x n' (h x)⟩
      unfold wCh
      rw [if_neg hp]
      omega

theorem mixBound_liftR (c : OComp (stSpec S lam C) α) :
    ∀ n, c.QueryBound n → MixBound C (liftR C c) 0 n := by
  induction c with
  | pure a => exact fun _ _ => trivial
  | sample n k ih => exact fun m h x => ih x m (h x)
  | query y q k ih =>
    intro n h
    cases n with
    | zero => exact h.elim
    | succ n => exact fun x => ih x n (h x)

/-! ## No raw query after a typed one -/

variable (C)

/-- no raw query -/
def TypedOnly : OComp (mixSpec C) α → Prop
  | .pure _ => True
  | .sample _ k => ∀ x, TypedOnly (k x)
  | .query (.inl _) _ k => ∀ x, TypedOnly (k x)
  | .query (.inr _) _ _ => False

/-- no raw query after a typed one -/
def RawFirst : OComp (mixSpec C) α → Prop
  | .pure _ => True
  | .sample _ k => ∀ x, RawFirst (k x)
  | .query (.inl _) _ k => ∀ x, TypedOnly C (k x)
  | .query (.inr _) _ k => ∀ x, RawFirst (k x)

variable {C}

theorem TypedOnly.bind {c : OComp (mixSpec C) α} {g : α → OComp (mixSpec C) β}
    (hg : ∀ a, TypedOnly C (g a)) (h : TypedOnly C c) : TypedOnly C (c.bind g) := by
  induction c with
  | pure a => exact hg a
  | sample n k ih => exact fun x => ih x (h x)
  | query x q k ih =>
    match x, q, k, ih, h with
    | .inl o, q, k, ih, h => exact fun x => ih x (h x)
    | .inr y, q, k, ih, h => exact h.elim

theorem typedOnly_liftT (c : OComp S α) : TypedOnly C (liftT C c) := by
  induction c with
  | pure a => trivial
  | sample n k ih => exact ih
  | query o q k ih => exact ih

theorem TypedOnly.rawFirst {c : OComp (mixSpec C) α} (h : TypedOnly C c) : RawFirst C c := by
  induction c with
  | pure a => trivial
  | sample n k ih => exact fun x => ih x (h x)
  | query x q k ih =>
    match x, q, k, ih, h with
    | .inl o, q, k, ih, h => exact h
    | .inr y, q, k, ih, h => exact h.elim

theorem rawFirst_liftR_bind (c : OComp (stSpec S lam C) α)
    {g : α → OComp (mixSpec C) β} (hg : ∀ a, RawFirst C (g a)) :
    RawFirst C ((liftR C c).bind g) := by
  induction c with
  | pure a => exact hg a
  | sample n k ih => exact ih
  | query y q k ih => exact ih

/-- a program without raw queries does not change the flag -/
theorem shadow_typedOnly (c : OComp (mixSpec C) α) :
    ∀ (s : Sh S lam) (T : Table S),
      TypedOnly C c → ∀ x ∈ ((shadow C c s).runLazy T).support, x.1.2.fl = s.fl := by
  induction c with
  | pure a =>
    intro s T _ x hx
    simp only [shadow, OComp.runLazy, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
  | sample n k ih =>
    intro s T h x hx
    simp only [shadow, OComp.runLazy, PMF.mem_support_bind_iff] at hx
    obtain ⟨r, -, hr⟩ := hx
    exact ih r s T (h r) x hr
  | query y q k ih =>
    intro s T h x hx
    match y, q, k, ih, h, hx with
    | .inl o, q, k, ih, h, hx =>
      simp only [shadow, OComp.runLazy] at hx
      cases hT : T o q with
      | some r => rw [hT] at hx; exact ih r { s with bT := s.bT.note C o q r } T (h r) x hx
      | none =>
        rw [hT] at hx
        obtain ⟨r, -, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
        exact ih r { s with bT := s.bT.note C o q r } _ (h r) x hr
    | .inr y, q, k, ih, h, hx => exact h.elim

/-- Under `RawFirst`, with equal tables and the flag down at the start, the flag of `shadow` is
never raised. -/
theorem shadow_rawFirst (c : OComp (mixSpec C) α) :
    ∀ (s : Sh S lam) (T : Table S), RawFirst C c → s.bT = s.bF → s.fl = false →
      ∀ x ∈ ((shadow C c s).runLazy T).support, x.1.2.fl = false := by
  induction c with
  | pure a =>
    intro s T _ _ hf x hx
    simp only [shadow, OComp.runLazy, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
    exact hf
  | sample n k ih =>
    intro s T h hb hf x hx
    simp only [shadow, OComp.runLazy, PMF.mem_support_bind_iff] at hx
    obtain ⟨r, -, hr⟩ := hx
    exact ih r s T (h r) hb hf x hr
  | query y q k ih =>
    intro s T h hb hf x hx
    match y, q, k, ih, h, hx with
    | .inl o, q, k, ih, h, hx =>
      have h' : ∀ x, TypedOnly C (k x) := h
      simp only [shadow, OComp.runLazy] at hx
      cases hT : T o q with
      | some r => rw [hT] at hx; exact (shadow_typedOnly (k r) { s with bT := s.bT.note C o q r } T (h' r) x hx).trans hf
      | none =>
        rw [hT] at hx
        obtain ⟨r, -, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
        exact (shadow_typedOnly (k r) { s with bT := s.bT.note C o q r } _ (h' r) x hr).trans hf
    | .inr (.inl o), q, k, ih, h, hx =>
      have h' : ∀ x, RawFirst C (k x) := h
      simp only [shadow, OComp.runLazy] at hx
      cases hT : T o q with
      | some r => rw [hT] at hx; exact ih _ { s with bT := s.bT.note C o q r, bF := s.bF.note C o q r } T (h' _) (by show s.bT.note C o q r = s.bF.note C o q r; rw [hb]) hf x hx
      | none =>
        rw [hT] at hx
        obtain ⟨r, -, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
        exact ih _ { s with bT := s.bT.note C o q r, bF := s.bF.note C o q r } _ (h' _)
          (by show s.bT.note C o q r = s.bF.note C o q r; rw [hb]) hf x hr
    | .inr (.inr u), p, k, ih, h, hx =>
      have h' : ∀ x, RawFirst C (k x) := h
      have hfl : (s.fl || s.dis C p) = false := by simp [Sh.dis, hb, hf]
      simp only [shadow] at hx
      cases hv : drVal C s.bF p with
      | some v =>
        rw [hv, hfl] at hx
        exact ih v { s with fl := false } T (h' v) hb rfl x hx
      | none =>
        rw [hv, hfl] at hx
        simp only [OComp.runLazy] at hx
        obtain ⟨r, -, hr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
        exact ih _ ⟨{ s.bT with loose := (p, digE lam r) :: s.bT.loose }, { s.bF with loose := (p, digE lam r) :: s.bF.loose }, false⟩ T (h' _) (by
          show ({ s.bT with loose := (p, digE lam r) :: s.bT.loose } : Book S lam) =
            { s.bF with loose := (p, digE lam r) :: s.bF.loose }
          rw [hb]) rfl x hr

/-- Under `RawFirst` and `MixBound C c t r`: Pr[real ∈ E] ≤ Pr[the reduction's interpretation ∈ E] +
(t + r)² / 2^(2 lam). -/
theorem mixClose_rawFirst (c : OComp (mixSpec C) α) (t r : ℕ) (hB : MixBound C c t r)
    (hR : RawFirst C c) (E : Set α) :
    Pr (real C c) (fun _ => E) ≤
      Pr (ideal C false c ⟨[], []⟩) (fun _ => {x | x.1 ∈ E}) + collP lam (t + r) (t + r) := by
  refine le_trans (mixColl c t r hB E) (add_le_add_left ?_ _)
  rw [← shadow_forget C c ⟨⟨[], []⟩, ⟨[], []⟩, false⟩, Pr_bind_pure, Pr_eq_law, Pr_eq_law]
  unfold OComp.law
  rw [pr_map, pr_map]
  refine pr_mono_support _ fun x hx h => ?_
  rcases h with h | h
  · exact h
  · rw [shadow_rawFirst c _ _ hR rfl rfl x hx] at h
    cases h

end Rom
