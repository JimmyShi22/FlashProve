-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdHideShort.lean: round polynomials of a sumcheck without the coefficient that the round
equation fixes: the bijection between short messages and consistent long messages, under the
hypotheses below.

Definitions, statements (in `Cb.Spec`) and proofs. Algebra only: no protocol occurs here.
Cb/Ld/LdHide.lean writes the messages of a sumcheck as all coefficients of each round polynomial
(`RIdx`), and says which tuples are consistent for a claimed sum (`HCons`: each round polynomial
"sums" to the value of the one before at its challenge). The description's prover does not send, in
each round, the coefficient of one fixed power of the variable: both parties set it by the round
equation. This file has the two forms of the messages: long (all coefficients) and short (without
the one that is left out). The "sum" over a variable is a weighted sum of values at nodes (`HVar`,
Cb/Ld/LdHide.lean).

Main names:
  `v.mon a`: the "sum" of the power X^a.
  `HFixs l`, `HFixs.OK l F`: for each variable: which power is left out, and an inverse of the "sum"
    of that power; that it is an inverse is what `HFixs.OK` says.
  `SIdx`: the names of the entries of the short messages: n, not n + 1, for a variable of degree n.
  `hFill v fx σ q'`: one round: the polynomial with the sent coefficients q' whose "sum" is σ (if
    `fx.2` is an inverse of the "sum" of the power `fx.1`: `phi_fill`).
  `hComp l F σ q' γ`: the long messages that the short messages q' stand for, at the claimed sum σ
    and the challenges γ: a round's completion reads the earlier rounds' messages and challenges
    only (beside `l`, σ, `F` and its own sent coefficients).
  `hDrop l F q`: the long messages without the coefficients that are left out.
  `Spec.short_cons`: under `HFixs.OK l F`, what is completed is consistent, for all short messages:
    no check is left (of the round equations in `HCons`).
  `Spec.short_drop`: drop (`hDrop`) after completion (`hComp`) gives the short messages again (no
    hypothesis).
  `Spec.short_comp`: under `HFixs.OK l F`, completion after drop gives a tuple of long messages
    again if it is consistent (`HCons l σ q γ`).
  `Spec.short_exists`: over a field, a variable with the one condition of Cb/Ld/LdHide.lean (the
    "sum" of its public polynomial is 1) has a power that occurs in that polynomial and whose "sum"
    is not 0: the description's choice exists.

Limits: this file does not say which power the description leaves out for which kind of variable.
Nothing on protocols.
Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdHide

set_option autoImplicit false

namespace Cb

section Defs
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

/-- The "sum" of a power of the variable. -/
def HVar.mon (v : HVar R) (a : Fin (v.n + 1)) : R := ∑ s, v.wt s * v.node s ^ (a : ℕ)

/-- For each variable: the power that is left out, and an inverse of its "sum" (by type any element
of R; that it is an inverse is what `HFixs.OK` says). -/
def HFixs : List (HVar R) → Type
  | [] => Unit
  | v :: l => (Fin (v.n + 1) × R) × HFixs l

def HFixs.OK : (l : List (HVar R)) → HFixs l → Prop
  | [], _ => True
  | v :: l, F => F.1.2 * v.mon F.1.1 = 1 ∧ HFixs.OK l F.2

/-- The names of the entries of the short messages. -/
def SIdx : List (HVar R) → Type
  | [] => Empty
  | v :: l => Fin v.n ⊕ SIdx l

/-- One round: the polynomial with the sent coefficients whose "sum" is σ (if `fx.2` is an inverse
of the "sum" of the power `fx.1`: `phi_fill`). -/
def hFill (v : HVar R) (fx : Fin (v.n + 1) × R) (σ : M) (q' : Fin v.n → M) : Fin (v.n + 1) → M :=
  fx.1.insertNth (α := fun _ => M) (fx.2 • (σ - v.phi (fx.1.insertNth (α := fun _ => M) 0 q'))) q'

/-- The long messages that short messages stand for. -/
def hComp : (l : List (HVar R)) → HFixs l → M → (SIdx l → M) → HPt l → RIdx l → M
  | [], _, _, _, _, i => i.elim
  | v :: _, F, σ, q', _, .inl t => hFill v F.1 σ (fun t => q' (.inl t)) t
  | v :: l, F, σ, q', γ, .inr i =>
    hComp l F.2 (hev (hFill v F.1 σ fun t => q' (.inl t)) γ.1) (fun i => q' (.inr i)) γ.2 i

/-- The long messages without the coefficients that are left out. -/
def hDrop : (l : List (HVar R)) → HFixs l → (RIdx l → M) → SIdx l → M
  | [], _, _, i => i.elim
  | _ :: _, F, q, .inl t => q (.inl (F.1.1.succAbove t))
  | _ :: l, F, q, .inr i => hDrop l F.2 (fun i => q (.inr i)) i

end Defs

namespace Spec
section
variable (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]

def short_cons : Prop :=
  ∀ (l : List (HVar R)) (F : HFixs l),
    HFixs.OK l F → ∀ (σ : M) (q' : SIdx l → M) (γ : HPt l), HCons l σ (hComp l F σ q' γ) γ
def short_drop : Prop :=
  ∀ (l : List (HVar R)) (F : HFixs l) (σ : M) (q' : SIdx l → M) (γ : HPt l),
    hDrop l F (hComp l F σ q' γ) = q'
def short_comp : Prop :=
  ∀ (l : List (HVar R)) (F : HFixs l), HFixs.OK l F →
    ∀ (σ : M) (q : RIdx l → M) (γ : HPt l), HCons l σ q γ → hComp l F σ (hDrop l F q) γ = q

end

def short_exists : Prop :=
  ∀ (R : Type) [Field R] (v : HVar R), v.OK → ∃ a : Fin (v.n + 1), v.psi a ≠ 0 ∧ v.mon a ≠ 0

end Spec

section Proofs
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

theorem hev_split {n : ℕ} (a : Fin (n + 1)) (x : M) (q' : Fin n → M) (y : R) :
    hev (a.insertNth (α := fun _ => M) x q') y =
      hev (a.insertNth (α := fun _ => M) 0 q') y + y ^ (a : ℕ) • x := by
  unfold hev
  rw [Fin.sum_univ_succAbove _ a, Fin.sum_univ_succAbove _ a]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, smul_zero, zero_add]
  exact add_comm _ _

theorem phi_split (v : HVar R) (a : Fin (v.n + 1)) (x : M) (q' : Fin v.n → M) :
    v.phi (a.insertNth (α := fun _ => M) x q') =
      v.phi (a.insertNth (α := fun _ => M) 0 q') + v.mon a • x := by
  unfold HVar.phi HVar.sum HVar.mon
  simp only [hev_split a x q', smul_add, Finset.sum_add_distrib, Finset.sum_smul, mul_smul]

theorem phi_fill (v : HVar R) (fx : Fin (v.n + 1) × R) (h : fx.2 * v.mon fx.1 = 1)
    (σ : M) (q' : Fin v.n → M) :
    v.phi (hFill v fx σ q') = σ := by
  unfold hFill
  rw [phi_split, ← mul_smul, mul_comm, h, one_smul, add_sub_cancel]

theorem fill_drop (v : HVar R) (fx : Fin (v.n + 1) × R)
    (h : fx.2 * v.mon fx.1 = 1) (c : Fin (v.n + 1) → M) :
    hFill v fx (v.phi c) (fun t => c (fx.1.succAbove t)) = c := by
  have e : c = fx.1.insertNth (α := fun _ => M) (c fx.1) fun t => c (fx.1.succAbove t) :=
    (Fin.insertNth_self_removeNth fx.1 c).symm
  have e2 : v.phi c - v.phi (fx.1.insertNth (α := fun _ => M) 0 fun t => c (fx.1.succAbove t)) =
      v.mon fx.1 • c fx.1 := by
    have e3 := phi_split v fx.1 (c fx.1) fun t => c (fx.1.succAbove t)
    rw [← e] at e3
    rw [e3, add_sub_cancel_left]
  unfold hFill
  rw [e2, ← mul_smul, h, one_smul]
  exact e.symm

end Proofs

theorem short_cons (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] :
    Spec.short_cons R M := by
  intro l
  induction l with
  | nil => exact fun _ _ _ _ _ => trivial
  | cons v l ih => exact fun F hF σ q' γ => ⟨phi_fill v F.1 hF.1 σ _, ih F.2 hF.2 _ _ γ.2⟩

theorem short_drop (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] :
    Spec.short_drop R M := by
  intro l
  induction l with
  | nil => exact fun _ _ _ _ => funext fun i => i.elim
  | cons v l ih =>
      intro F σ q' γ
      funext i
      rcases i with t | i
      · show hFill v F.1 σ (fun t => q' (.inl t)) (F.1.1.succAbove t) = _
        unfold hFill
        rw [Fin.insertNth_apply_succAbove]
      · exact congrFun (ih F.2 _ (fun i => q' (.inr i)) γ.2) i

theorem short_comp (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M] :
    Spec.short_comp R M := by
  intro l
  induction l with
  | nil => exact fun _ _ _ _ _ _ => funext fun i => i.elim
  | cons v l ih =>
      intro F hF σ q γ hq
      have e1 : hFill v F.1 σ (fun t => q (.inl (F.1.1.succAbove t))) = fun t => q (.inl t) := by
        rw [← hq.1]
        exact fill_drop v F.1 hF.1 fun t => q (.inl t)
      funext i
      rcases i with t | i
      · exact congrFun e1 t
      · show hComp l F.2 (hev (hFill v F.1 σ fun t => q (.inl (F.1.1.succAbove t))) γ.1)
            (hDrop l F.2 fun i => q (.inr i)) γ.2 i = _
        rw [e1]
        exact congrFun (ih F.2 hF.2 _ (fun i => q (.inr i)) γ.2 hq.2) i

theorem short_exists : Spec.short_exists := by
  intro R _ v hv
  by_contra hc0
  have hc : ∀ a, v.psi a ≠ 0 → v.mon a = 0 := fun a ha => by_contra fun hm => hc0 ⟨a, ha, hm⟩
  have h0 : v.phi v.psi = 0 := by
    unfold HVar.phi HVar.sum hev
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases ha : v.psi a = 0
    · simp [ha]
    · have hm := hc a ha
      unfold HVar.mon at hm
      calc
        ∑ s, v.wt s * (v.node s ^ (a : ℕ) * v.psi a) =
            (∑ s, v.wt s * v.node s ^ (a : ℕ)) * v.psi a := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun s _ => (mul_assoc _ _ _).symm
        _ = 0 := by rw [hm, zero_mul]
  exact one_ne_zero (hv.symm.trans h0)

end Cb
