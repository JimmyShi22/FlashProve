-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstDr.lean: the step that expands a long answer of a random oracle from a state
(Rom/StateFirst.lean): the expansion queries of a state under lazy sampling.

After the step a chain oracle returns only a state: the chaining value and the last block, hid, of
its old answer; the other hash blocks are answers of an added oracle dr to expansion queries (state,
counter). (`Link`, `stSpec`: Rom/StateFirst.lean.) `askDr` makes the queries dr (σ, off), .., dr (σ,
off + K − 1) of a state σ.

  `runLazy_askDr_old`   If the table holds all the entries, `askDr` returns them and leaves the
      table unchanged.
  `runLazy_askDr_new`   If the table holds none of the entries, `askDr` returns uniform hash blocks
      and writes them.

Notation:
  `Dg lam`: a hash block, `Fin lam → Bool` (Rom/NeedA.lean)
  `C`: for each oracle o of S, a `Link lam (S.Rng o)` (Rom/StateFirst.lean): how an oracle with
      answers in R is treated (`plain` or `chain K e`)
  `Table S` (Rom/OSpec.lean): a partial table: what lazy sampling has fixed so far
  `.inl o` of `stSpec S lam C` (Rom/StateFirst.lean): the oracle o of S, with answers in `(C o).Ans`
  dr: the added oracle of the second family: `.inr ()` of `stSpec S lam C` (Rom/StateFirst.lean); a
      query to it is an expansion query (state, counter), of type `(Dg lam × Dg lam) × ℕ`; an answer
      is a hash block
  σ, off, K, bl (in `putDr`): a state, of type `Dg lam × Dg lam`; two natural numbers; K hash
      blocks, of type `Fin K → Dg lam`

Limits: a table that holds some but not all of the entries is not treated.
-/
import Rom.StateFirstMix
import Prob.Count

set_option autoImplicit false

namespace Rom
open Prob

variable {S : OSpec} {lam : ℕ} (C : ∀ o, Link lam (S.Rng o))

/-- the table with hash blocks written at the expansion queries of a state -/
def putDr (T : Table (stSpec S lam C)) (σ : Dg lam × Dg lam) (off K : ℕ) (bl : Fin K → Dg lam) :
    Table (stSpec S lam C) :=
  fun x => match x with
    | .inl o => T (.inl o)
    | .inr u =>
      fun p =>
        if h : p.1 = σ ∧ off ≤ p.2 ∧ p.2 < off + K then some (bl ⟨p.2 - off, by omega⟩)
        else T (.inr u) p

theorem putDr_inl (T : Table (stSpec S lam C)) (σ : Dg lam × Dg lam) (off K : ℕ)
    (bl : Fin K → Dg lam) (o : S.ι) :
    putDr C T σ off K bl (.inl o) = T (.inl o) := rfl

theorem putDr_zero (T : Table (stSpec S lam C)) (σ : Dg lam × Dg lam)
    (off : ℕ) (bl : Fin 0 → Dg lam) : putDr C T σ off 0 bl = T := by
  funext x
  match x with
  | .inl o => rfl
  | .inr u =>
    funext p
    show (if h : p.1 = σ ∧ off ≤ p.2 ∧ p.2 < off + 0 then _ else T (.inr u) p) = _
    rw [dif_neg (by omega)]

theorem set_dr_ne (T : Table (stSpec S lam C)) (p p' : (Dg lam × Dg lam) × ℕ)
    (r : Dg lam) (h : p' ≠ p) :
    (T.set (S := stSpec S lam C) (.inr ()) p r) (.inr ()) p' = T (.inr ()) p' := by
  unfold Table.set
  rw [Function.update_self]
  exact @Function.update_of_ne _ _ ((stSpec S lam C).decDom (.inr ())) _ _ h _ _

theorem set_dr_self (T : Table (stSpec S lam C)) (p : (Dg lam × Dg lam) × ℕ) (r : Dg lam) :
    (T.set (S := stSpec S lam C) (.inr ()) p r) (.inr ()) p = some r :=
  Table.set_self (S := stSpec S lam C) T (.inr ()) p r

theorem set_dr_inl (T : Table (stSpec S lam C)) (p : (Dg lam × Dg lam) × ℕ) (r : Dg lam) (o : S.ι) :
    (T.set (S := stSpec S lam C) (.inr ()) p r) (.inl o) = T (.inl o) := by
  unfold Table.set
  rw [Function.update_of_ne (by simp)]

theorem putDr_succ (T : Table (stSpec S lam C)) (σ : Dg lam × Dg lam) (off K : ℕ)
    (r : Dg lam) (bl : Fin K → Dg lam) :
    putDr C (T.set (S := stSpec S lam C) (.inr ()) (σ, off) r) σ (off + 1) K bl =
      putDr C T σ off (K + 1) (Fin.cons (α := fun _ => Dg lam) r bl) := by
  funext x
  match x with
  | .inl o => exact set_dr_inl C T _ r o
  | .inr () =>
    funext p
    show (if h : p.1 = σ ∧ off + 1 ≤ p.2 ∧ p.2 < off + 1 + K then
          some (bl ⟨p.2 - (off + 1), by omega⟩)
        else (T.set (S := stSpec S lam C) (.inr ()) (σ, off) r) (.inr ()) p) =
      if h : p.1 = σ ∧ off ≤ p.2 ∧ p.2 < off + (K + 1) then
        some ((Fin.cons (α := fun _ => Dg lam) r bl : Fin (K + 1) → Dg lam) ⟨p.2 - off, by omega⟩)
      else T (.inr ()) p
    by_cases h1 : p.1 = σ ∧ off + 1 ≤ p.2 ∧ p.2 < off + 1 + K
    · rw [dif_pos h1, dif_pos ⟨h1.1, by omega, by omega⟩]
      have e : (⟨p.2 - off, by omega⟩ : Fin (K + 1)) = Fin.succ ⟨p.2 - (off + 1), by omega⟩ :=
        Fin.ext (by simp only [Fin.val_succ]; omega)
      rw [e, Fin.cons_succ]
    · rw [dif_neg h1]
      by_cases h2 : p = (σ, off)
      · subst h2
        rw [set_dr_self, dif_pos ⟨rfl, le_refl _, by simp⟩]
        have e : (⟨(σ, off).2 - off, by simp⟩ : Fin (K + 1)) = 0 := Fin.ext (by simp)
        rw [e, Fin.cons_zero]
      · rw [set_dr_ne C T _ _ r h2, dif_neg]
        rintro ⟨a, b, c⟩
        by_cases h3 : p.2 = off
        · exact h2 (Prod.ext a h3)
        · exact h1 ⟨a, by omega, by omega⟩

/-- If the table holds all the entries, `askDr` returns them and leaves the table unchanged. -/
theorem runLazy_askDr_old (σ : Dg lam × Dg lam) :
    ∀ (K off : ℕ) (T : Table (stSpec S lam C)) (bl : Fin K → Dg lam),
      (∀ j : Fin K, T (.inr ()) (σ, off + j.val) = some (bl j)) →
      (askDr C σ off K).runLazy T = PMF.pure (bl, T)
  | 0, _, T, bl, _ => by
    have e : bl = fun i => i.elim0 := funext fun i => i.elim0
    rw [e]
    rfl
  | K + 1, off, T, bl, h => by
    have h0 : T (.inr ()) (σ, off) = some (bl 0) := h 0
    have ih := runLazy_askDr_old σ K (off + 1) T (fun j => bl j.succ) fun j => by
      have := h j.succ
      rwa [Fin.val_succ, show off + (j.val + 1) = off + 1 + j.val by omega] at this
    show (OComp.query (S := stSpec S lam C) (.inr ()) (σ, off) fun r =>
        (askDr C σ (off + 1) K).bind fun rest =>
          .pure (Fin.cons (α := fun _ => Dg lam) r rest)).runLazy T = _
    simp only [OComp.runLazy, h0]
    rw [OComp.runLazy_bind, ih, PMF.pure_bind]
    simp only [OComp.runLazy]
    congr 2
    exact Fin.cons_self_tail bl

/-- uniform hash blocks, one after the other, are a uniform tuple -/
theorem unif_cons_blocks (K : ℕ) :
    (unif (Dg lam)).bind (fun r =>
        (unif (Fin K → Dg lam)).map fun bl =>
          (Fin.cons (α := fun _ => Dg lam) r bl : Fin (K + 1) → Dg lam)) =
      unif (Fin (K + 1) → Dg lam) := by
  have h := map_unif_equiv (Fin.consEquiv fun _ : Fin (K + 1) => Dg lam)
  rw [← h, unif_prod]
  unfold Prob.prod
  rw [PMF.map_bind]
  congr 1
  funext r
  rw [PMF.map_comp]
  rfl

/-- If the table holds none of the entries, `askDr` returns uniform hash blocks and writes them. -/
theorem runLazy_askDr_new (σ : Dg lam × Dg lam) :
    ∀ (K off : ℕ) (T : Table (stSpec S lam C)), (∀ j < K, T (.inr ()) (σ, off + j) = none) →
      (askDr C σ off K).runLazy T = (unif (Fin K → Dg lam)).map fun bl => (bl, putDr C T σ off K bl)
  | 0, off, T, _ => by
    have e : unif (Fin 0 → Dg lam) = PMF.pure fun i => i.elim0 := by
      refine PMF.ext fun x => ?_
      have hx : x = fun i => i.elim0 := funext fun i => i.elim0
      subst hx
      simp [unif, PMF.uniformOfFintype_apply]
    rw [e, PMF.pure_map, putDr_zero]
    rfl
  | K + 1, off, T, h => by
    have h0 : T (.inr ()) (σ, off) = none := h 0 (Nat.succ_pos K)
    show (OComp.query (S := stSpec S lam C) (.inr ()) (σ, off) fun r =>
        (askDr C σ (off + 1) K).bind fun rest =>
          .pure (Fin.cons (α := fun _ => Dg lam) r rest)).runLazy T = _
    simp only [OComp.runLazy, h0]
    rw [← unif_cons_blocks, PMF.map_bind]
    refine congrArg _ (funext fun r => ?_)
    have ih := runLazy_askDr_new σ K (off + 1) (T.set (S := stSpec S lam C) (.inr ()) (σ, off) r) fun j hj => by
      rw [set_dr_ne C T _ _ r (by intro e; have := congrArg Prod.snd e; simp at this; omega)]
      have := h (j + 1) (by omega)
      rwa [show off + (j + 1) = off + 1 + j by omega] at this
    rw [OComp.runLazy_bind, ih, PMF.bind_map, PMF.map_comp]
    refine congrArg _ (funext fun bl => ?_)
    show PMF.pure
        ((Fin.cons (α := fun _ => Dg lam) r bl : Fin (K + 1) → Dg lam),
          putDr C (T.set (S := stSpec S lam C) (.inr ()) (σ, off) r) σ (off + 1) K bl) = PMF.pure _
    rw [putDr_succ]
    rfl

end Rom
