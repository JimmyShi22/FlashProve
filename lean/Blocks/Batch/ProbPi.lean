-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Batch/ProbPi.lean: independent samples, one for each element of a finite set.

Lemmas of section 1 are used in Ior/LinkVRules.lean (`exactV_local`) and Ior/OnlineHonKit.lean
(`law_split`). All types from which a uniform value is taken are finite and non-empty.

 * `Prob.Indep.pis p`: see its docstring.
 * `Prob.Indep.map_unif_pis`: if, for each k, a function g k is applied to the k-th coordinate of a
   uniform family, the results have the distribution `pis` of the single distributions.
 * `Prob.Indep.map_unif_shared`: the same for a subset J of the coordinates, and with a shared
   uniform part on which all functions may depend: sample the shared part; given it, the samples are
   independent.
 * `Prob.Indep.map_unif_two`, `Prob.Indep.map_unif_three`: see their docstrings.

Notation: in section 2: `s` (`Γ → Sg`; `A → Γ → Sg`): the symbols; `vB : Γ → CB → VB`,
`vC : A → Γ → CC → VC`: the view; `pl : A → Pl`: the plain parts; `SimP : PMF Pl`,
`KB : Sg → PMF VB`, `KC : Pl → Sg → PMF VC`: the distributions that stand in `h1`, `h3`, `h4`;
`Φ : Pl → Sg → VC → Out`: a function of the three parts.
-/
import Prob.Linear
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Basic
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Prob.Indep

/-! ## 1. Independent samples -/

/-- Independent samples y_0 from p 0, .., y_(n-1) from p (n-1). -/
def piFin {Y : Type} : (n : ℕ) → (Fin n → PMF Y) → PMF (Fin n → Y)
  | 0, _ => PMF.pure Fin.elim0
  | n + 1, p =>
    (p 0).bind fun y => (piFin n fun i => p i.succ).map fun f => (Fin.cons y f : Fin (n + 1) → Y)

/-- A family on n + 1 indices is a first entry and a family on n indices. -/
def consE (Ω : Type) (n : ℕ) : Ω × (Fin n → Ω) ≃ (Fin (n + 1) → Ω) where
  toFun p := Fin.cons p.1 p.2
  invFun f := (f 0, fun i => f i.succ)
  left_inv p := by simp
  right_inv f := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp

/-- A function of a uniform pair: sample the first part, then the second. -/
theorem map_unif_fst_then {C D β : Type} [Fintype C] [Nonempty C] [Fintype D]
    [Nonempty D] (f : C × D → β) :
    (unif (C × D)).map f = (unif C).bind fun c => (unif D).map fun d => f (c, d) := by
  rw [unif_prod]
  unfold Prob.prod
  rw [PMF.map_bind]
  refine congrArg _ (funext fun c => ?_)
  rw [PMF.map_comp]
  rfl

theorem map_unif_piFin {Ω Y : Type} [Fintype Ω] [Nonempty Ω] : ∀ (n : ℕ) (g : Fin n → Ω → Y),
    (unif (Fin n → Ω)).map (fun ω i => g i (ω i)) = piFin n fun i => (unif Ω).map (g i)
  | 0, g => by
      have h : (fun (ω : Fin 0 → Ω) i => g i (ω i)) = fun _ => Fin.elim0 :=
        funext fun _ => funext fun i => i.elim0
      rw [h]
      exact PMF.map_const _ _
  | n + 1, g => by
      have ih := map_unif_piFin n fun i => g i.succ
      show _ = ((unif Ω).map (g 0)).bind fun y =>
          (piFin n fun i => (unif Ω).map (g i.succ)).map fun f => (Fin.cons y f : Fin (n + 1) → Y)
      rw [← ih, PMF.bind_map, ← map_unif_equiv (consE Ω n), PMF.map_comp, map_unif_fst_then]
      refine congrArg _ (funext fun a => ?_)
      show _ = ((unif (Fin n → Ω)).map fun ω i => g i.succ (ω i)).map fun f =>
          (Fin.cons (g 0 a) f : Fin (n + 1) → Y)
      rw [PMF.map_comp]
      refine congrArg (fun φ => (unif (Fin n → Ω)).map φ) (funext fun ω => funext fun i => ?_)
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [consE]
      · simp [consE]

/-- Independent samples, y_k from p k for each k in the finite set κ. -/
def pis {κ Y : Type} [Fintype κ] (p : κ → PMF Y) : PMF (κ → Y) :=
  (piFin (Fintype.card κ) fun i => p ((Fintype.equivFin κ).symm i)).map fun f k =>
    f (Fintype.equivFin κ k)

/-- Functions of the single coordinates of a uniform family are independent. -/
theorem map_unif_pis {κ Ω Y : Type} [Fintype κ] [DecidableEq κ] [Fintype Ω]
    [Nonempty Ω] (g : κ → Ω → Y) :
    (unif (κ → Ω)).map (fun ω k => g k (ω k)) = pis fun k => (unif Ω).map (g k) := by
  unfold pis
  rw [← map_unif_piFin, PMF.map_comp,
    ← map_unif_equiv (Equiv.arrowCongr (Fintype.equivFin κ) (Equiv.refl Ω)), PMF.map_comp]
  refine congrArg (fun φ => (unif (κ → Ω)).map φ) (funext fun ω => funext fun k => ?_)
  show g k (ω k) =
    g ((Fintype.equivFin κ).symm (Fintype.equivFin κ k))
      (ω ((Fintype.equivFin κ).symm (Fintype.equivFin κ k)))
  rw [Equiv.symm_apply_apply]

/-- The coordinates in a subset of a uniform family are a uniform family. -/
theorem map_unif_restrict {ι Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    [Nonempty Ω] (J : Finset ι) :
    (unif (ι → Ω)).map (fun ω (j : J) => ω j.1) = unif (J → Ω) := by
  have h := map_unif_equiv (Equiv.piEquivPiSubtypeProd (fun i => i ∈ J) fun _ : ι => Ω)
  rw [← map_fst_unif (C := J → Ω) (D := {i // ¬ i ∈ J} → Ω), ← h, PMF.map_comp]
  rfl

/-- A shared part and independent slots. Each function G j sees the shared part and the coordinate
j. -/
theorem map_unif_shared {ι C0 Ω Y : Type} [Fintype ι] [DecidableEq ι] [Fintype C0] [Nonempty C0]
    [Fintype Ω] [Nonempty Ω] (J : Finset ι) (G : J → C0 → Ω → Y) :
    (unif (C0 × (ι → Ω))).map (fun c (j : J) => G j c.1 (c.2 j.1)) =
      (unif C0).bind fun c0 => pis fun j : J => (unif Ω).map (G j c0) := by
  rw [map_unif_fst_then]
  refine congrArg _ (funext fun c0 => ?_)
  rw [← map_unif_pis, ← map_unif_restrict J, PMF.map_comp]
  rfl

/-! ## 2. Values that are composed of parts sampled one after the other -/

/-- Two parts: uniform symbols, then a view whose distribution depends on them. -/
theorem map_unif_two {Γ CB Sg VB : Type} [Fintype Γ] [Nonempty Γ] [Fintype CB] [Nonempty CB]
    [Fintype Sg] [Nonempty Sg] (s : Γ → Sg) (vB : Γ → CB → VB) (KB : Sg → PMF VB)
    (h2 : (unif Γ).map s = unif Sg) (h3 : ∀ γ, (unif CB).map (vB γ) = KB (s γ)) :
    (unif (Γ × CB)).map (fun c => (s c.1, vB c.1 c.2)) =
      (unif Sg).bind fun σ => (KB σ).map fun b => (σ, b) := by
  rw [← h2, PMF.bind_map, map_unif_fst_then]
  refine congrArg _ (funext fun γ => ?_)
  show _ = (KB (s γ)).map fun b => (s γ, b)
  rw [← h3 γ, PMF.map_comp]
  rfl

/-- Three parts: plain parts (`pl`) with a given distribution (`SimP`; `h1`); symbols (`s`) that are
uniform for each of their coins (for each a; `h2`); then a view (`vC`) whose distribution (`KC`)
depends on both (`h4`). -/
theorem map_unif_three {A Γ CC Pl Sg VC Out : Type} [Fintype A] [Nonempty A] [Fintype Γ]
    [Nonempty Γ] [Fintype CC] [Nonempty CC] [Fintype Sg] [Nonempty Sg] (pl : A → Pl)
    (s : A → Γ → Sg) (vC : A → Γ → CC → VC) (Φ : Pl → Sg → VC → Out) (SimP : PMF Pl)
    (KC : Pl → Sg → PMF VC) (h1 : (unif A).map pl = SimP) (h2 : ∀ a, (unif Γ).map (s a) = unif Sg)
    (h4 : ∀ a γ, (unif CC).map (vC a γ) = KC (pl a) (s a γ)) :
    (unif (A × Γ × CC)).map (fun c => Φ (pl c.1) (s c.1 c.2.1) (vC c.1 c.2.1 c.2.2)) =
      SimP.bind fun p => (unif Sg).bind fun σ => (KC p σ).map fun c => Φ p σ c := by
  rw [← h1, PMF.bind_map, map_unif_fst_then]
  refine congrArg _ (funext fun a => ?_)
  show _ = (unif Sg).bind fun σ => (KC (pl a) σ).map fun c => Φ (pl a) σ c
  rw [← h2 a, PMF.bind_map, map_unif_fst_then]
  refine congrArg _ (funext fun γ => ?_)
  show _ = (KC (pl a) (s a γ)).map fun c => Φ (pl a) (s a γ) c
  rw [← h4 a γ, PMF.map_comp]
  rfl

end Prob.Indep
