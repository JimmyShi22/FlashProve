-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumZk.lean: proof of `Spec.ld_sum_exact` (Cb/Ld/LdSum.lean): under `2 ≤ Y.n` and `Y.Cw.Zk t`
(`Y : SumPar E P`, t : ℕ; Cb/Ld/LdSum.lean), the zero-knowledge sumcheck is honest-verifier zero
knowledge, in the exact form (`IOR.Honest.Exact`, Ior/Honest.lean); and the same with the simulator
named in the statement (`Spec.ld_sum_exactWith`: `Y.sim`), as the code switch's and the base case's
are (Cb/Ld/LdSwitch.lean, Cb/Ld/LdBase.lean).

`H.ExactWith Ri bud S`: for every (x, y, w) in Ri, every ρ outside `H.Hid w x` and every T with
`bud ρ T`, the distribution `H.output w x ρ T` equals `S x ρ T a`, where a gives the symbols of y at
the positions `R.given ρ T` and `none` at the others. `Exact` says that some S does. Here
`ExactWith`, of `Y.hon`, at S = `Y.sim`, is the conclusion of `Spec.ld_sum_exactWith`, and `Exact`
that of `Spec.ld_sum_exact`, each under `2 ≤ Y.n` and `Y.Cw.Zk t`, at Ri =
`Con Y.Cin.N Y.slIn.Holds` and bud = `Y.bud t`.

The simulator (`SumPar.sim`): it draws coefficients W and encoding randomness r as the honest prover
does; it shows
  the sum of the hiding polynomial of W,
  the round polynomials of that polynomial plus those of (target) ε ψ_1 .. ψ_k (ψ_j: `HVar.psi`,
    Cb/Ld/LdHide.lean), which is a summand with the claimed sum that needs no witness,
  and the symbols of an encoding of the message 0.

The proof. (1) The honest round polynomials are those of the hiding polynomial plus a tuple that is
consistent with the sum ε (target); so is the simulator's; two such tuples differ by the messages of
a hiding polynomial with sum 0 (Cb/Ld/LdHide.lean), and a shift of the uniform coefficients by its
coefficients carries one to the other. (2) Under `Y.Cw.Zk t`: for each value of the coefficients,
the symbols of the mask oracle within the budget (`SumPar.bud`, Cb/Ld/LdSum.lean) have a law that
does not depend on the message.

Notation:
  ε: `Y.eps ρ`, the coefficient that the verifier reads off a transcript (Cb/Ld/LdSum.lean);
  target: `x.1`: a statement is (target, state) (`LdCode.rels`, Cb/Ld/LdRel.lean);
  `Y.n`: the largest degree of a round polynomial (Cb/Ld/LdSum.lean);
  `hMu`: the sum of the hiding polynomial; `hTr`: the round polynomials of Λ ψ_1 .. ψ_k + U at the
    challenges γ;
  `HCons`: consistent messages for the claimed sum σ: each round polynomial sums to the value of the
    one before at its challenge (all three: Cb/Ld/LdHide.lean).

Limits: this file says nothing on a verifier that departs from the protocol, and nothing on further
positions outside the budget. It does not say that any code has `LdCode.Zk`.
-/
import Cb.Ld.LdSumAcc
import Prob.LawKit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

section General
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

theorem sCons_smul :
    ∀ (l : List (HVar R)) {σ : M} {q : RIdx l → M} {γ : HPt l} (a : R),
      HCons l σ q γ → HCons l (a • σ) (fun i => a • q i) γ := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _; trivial
  | cons v l ih =>
      intro σ q γ a h
      refine ⟨?_, ?_⟩
      · show v.sum (hev fun t => a • q (.inl t)) = _
        rw [funext (hev_smul a fun t => q (.inl t)), HVar.sum_smul]
        exact congrArg _ h.1
      · show HCons l (hev (fun t => a • q (.inl t)) γ.1) (fun i => a • q (.inr i)) γ.2
        rw [hev_smul]
        exact ih a h.2

theorem sMu_zero (l : List (HVar R)) : hMu l (0 : HIdx l → M) = 0 := by
  have h := hMu_add l (0 : HIdx l → M) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

/-- Under `hOK`: two tuples consistent with one sum differ by the messages of a hiding polynomial
with sum 0. -/
theorem hide_shift (l : List (HVar R)) (hOK : ∀ v ∈ l, v.OK) (γ : HPt l) (σ : M) (u u' : RIdx l → M)
    (hu : HCons l σ u γ) (hu' : HCons l σ u' γ) :
    ∃ W₀ : HIdx l → M,
      ∀ W, hMu l W = hMu l (W + W₀) ∧ hTr l 0 W γ + u = hTr l 0 (W + W₀) γ + u' := by
  have h0 : HCons l (0 + 0) (u - u') γ := by
    have := HCons.sub l hu hu'
    rwa [sub_self, ← add_zero (0 : M)] at this
  obtain ⟨i1, i2⟩ := hide_inv_right R M l hOK 0 0 (u - u') γ h0
  refine ⟨hInv l 0 0 (u - u') γ, fun W => ?_⟩
  have ht := hTr_add l 0 0 W (hInv l 0 0 (u - u') γ) γ
  rw [add_zero] at ht
  rw [hMu_add, ht, i1, i2, add_zero]
  exact ⟨rfl, by abel⟩

end General

section Rounds
variable {E Ch : Type} [Field E] [Fintype Ch] [Nonempty Ch] (val : Ch → E) (n : ℕ)

/-- the transcript of the k rounds with given round polynomials -/
def sMk :
    (k : ℕ) → (RIdx (sVars E n k) → E) → Rho (List.replicate k (sRound E Ch n)) →
    Tr (List.replicate k (sRound E Ch n))
  | 0, _, _ => ()
  | k + 1, q, ρ => (((), fun t => q (.inl t)), ρ.1, sMk k (fun i => q (.inr i)) ρ.2)

theorem sStrat_tr {β : Type} :
    ∀ (k : ℕ) (q : HPt (sVars E n k) → RIdx (sVars E n k) → E) (res : HPt (sVars E n k) → β),
      SCausal n k q →
      ∀ ρ : Rho (List.replicate k (sRound E Ch n)),
        ((sStrat val n k q res).run ρ).1 = sMk n k (q (sG val n k ρ)) ρ := by
  intro k
  induction k with
  | zero => intro _ _ _ _; rfl
  | succ k ih =>
      intro q res hq ρ
      exact Prod.ext (Prod.ext rfl (funext fun t => hq.1 _ _ t))
        (Prod.ext rfl
          (ih (fun γ i => q (val ρ.1, γ) (.inr i)) (fun γ => res (val ρ.1, γ)) (hq.2 _) ρ.2))

theorem sOPos_empty : ∀ k : ℕ, OPos (List.replicate k (sRound E Ch n)) → False
  | 0, p => p.elim
  | _ + 1, .inl p => p.elim
  | k + 1, .inr p => sOPos_empty k p

end Rounds

namespace SumPar
variable {E P : Type} [Field E] [Fintype E] (Y : SumPar E P)

/-- a transcript from its parts -/
def mkTr (f : Y.Cw.Word) (μ : E) (q : RIdx Y.vars → E) (ρ : Rho Y.shape) : Tr Y.shape :=
  ((f, μ), ρ.1, sMk Y.n Y.k q ρ.2)

theorem run_eq (w : Y.Cin.N.Wit) (x : Y.Xi) (c : Y.Coin) (ρ : Rho Y.shape) :
    ((Y.hon.strat w x c).run ρ).1 =
      Y.mkTr (Y.Cw.enc (Y.pk c.1) c.2) (hMu Y.vars c.1) (Y.honQ w x c.1 (Y.eps ρ) (Y.gam ρ)) ρ :=
  Prod.ext rfl (Prod.ext rfl (sStrat_tr Y.val Y.n Y.k _ _ (Y.honQ_causal w x c.1 _) ρ.2))

/-- the native positions of the mask oracle in a set of further positions -/
def posOf (T : Finset (OPos Y.ior.shape)) : Finset Y.Cw.nat.Pos :=
  (show Finset (Y.Cw.NP ⊕ OPos Y.rounds) from T).toLeft

/-- the native symbol at p, out of a symbol σ that carries its position -/
def take (σ : Y.Cw.nat.Sym) (p : Y.Cw.NP) : Option (Y.Cw.NS p → E) :=
  if h : σ.1 = p then some (h ▸ σ.2) else none

/-- what a run shows, from the symbols of the mask oracle at the further positions -/
def gv (T : Finset (OPos Y.ior.shape)) (ρ : Rho Y.shape) (μ : E)
    (q : RIdx Y.vars → E) (g : Y.posOf T → Y.Cw.nat.Sym) : Option (IOR.View Y.ior) :=
  some { plains := (μ, (sMk Y.n Y.k q ρ.2).plains)
         orc := fun p => match p with
           | .inl p₀ => if h : p₀ ∈ Y.posOf T then Y.take (g ⟨p₀, h⟩) p₀ else none
           | .inr p' => (sOPos_empty Y.n Y.k p').elim }

omit [Fintype E] in
theorem view_mk (T : Finset (OPos Y.ior.shape)) (ρ : Rho Y.shape) (μ : E)
    (q : RIdx Y.vars → E) (f : Y.Cw.Word) :
    some (Y.ior.view T (Y.mkTr f μ q ρ)) = Y.gv T ρ μ q fun p => ⟨p.1, f p.1⟩ := by
  unfold gv IOR.view
  refine congrArg some ?_
  refine congrArg (IOR.View.mk _) (funext fun p => ?_)
  rcases p with p₀ | p'
  · have hc : (Sum.inl p₀ ∈ Y.ior.reads (Y.mkTr f μ q ρ).rho ∨
          Sum.inl p₀ ∈ T ∨
          Y.ior.blinded (Sum.inl p₀) = false) ↔
        p₀ ∈ Y.posOf T := by
      constructor
      · rintro (h | h | h)
        · exact absurd h (Finset.notMem_empty _)
        · exact Finset.mem_toLeft.2 h
        · exact absurd h (by simp [SumPar.ior])
      · intro h
        exact Or.inr (Or.inl (Finset.mem_toLeft.1 h))
    by_cases h : p₀ ∈ Y.posOf T
    · refine (if_pos (hc.2 h)).trans ?_
      show _ = if h : p₀ ∈ Y.posOf T then Y.take ⟨p₀, f p₀⟩ p₀ else none
      rw [dif_pos h]
      unfold take
      rw [dif_pos rfl]
      rfl
    · refine (if_neg fun h' => h (hc.1 h')).trans ?_
      show _ = if h : p₀ ∈ Y.posOf T then Y.take ⟨p₀, f p₀⟩ p₀ else none
      rw [dif_neg h]
      rfl
  · exact (sOPos_empty Y.n Y.k p').elim

/-- The simulator (see the head). -/
def sim : IOR.Honest.Sim Y.ior := fun x ρ T _ =>
  (unif Y.Coin).map fun c =>
    some (Y.ior.view T
        (Y.mkTr (Y.Cw.enc 0 c.2) (hMu Y.vars c.1)
          (hTr Y.vars 0 c.1 (Y.gam ρ) +
            fun i => Y.eps ρ • hTr Y.vars x.1 (0 : HIdx Y.vars → E) (Y.gam ρ) i) ρ))

end SumPar

/-- The same with the simulator named: under `2 ≤ Y.n` and `Y.Cw.Zk t`, for x, y, w in
`Con Y.Cin.N Y.slIn.Holds`, `Y.sim` is exact at every ρ, for every set of further positions within
the budget. -/
def Spec.ld_sum_exactWith (E P : Type) [Field E] [Fintype E] : Prop :=
  ∀ (Y : SumPar E P) (t : ℕ),
    2 ≤ Y.n → Y.Cw.Zk t → Y.hon.ExactWith (Con Y.Cin.N Y.slIn.Holds) (Y.bud t) Y.sim

theorem ld_sum_exactWith (E P : Type) [Field E] [Fintype E] : Spec.ld_sum_exactWith E P := by
  intro Y t hn hZk x y w hR ρ _ T hT
  have hOK := sVars_ok (E := E) Y.n (by omega : 1 ≤ Y.n) Y.k
  have hcl : ∑ j, Y.slIn x.2 j * w.1 j = x.1 := hR.2
  -- the two tuples, consistent with one sum
  have hu : HCons Y.vars (Y.eps ρ • x.1)
      (fun i => Y.eps ρ • sTr Y.n Y.k (Y.tabL x) (Y.tabM w.1) (Y.gam ρ) i) (Y.gam ρ) := by
    have h1 :=
      (hRounds_cons Y.vars _ _ _ (sTr_rounds Y.n hn Y.k (Y.tabL x) (Y.tabM w.1) (Y.gam ρ))).1
    rw [sCl_sum, Y.sBl_tab, hcl] at h1
    exact sCons_smul Y.vars _ h1
  have hu' : HCons Y.vars (Y.eps ρ • x.1)
      (fun i => Y.eps ρ • hTr Y.vars x.1 (0 : HIdx Y.vars → E) (Y.gam ρ) i) (Y.gam ρ) := by
    have h1 := hide_cons E E Y.vars hOK x.1 0 (Y.gam ρ)
    rw [sMu_zero, add_zero] at h1
    exact sCons_smul Y.vars _ h1
  obtain ⟨W₀, hW₀⟩ := hide_shift Y.vars hOK (Y.gam ρ) _ _ _ hu hu'
  -- the budget
  have hS : Y.Cw.budT t (Y.posOf T) := by
    obtain ⟨X, hX, hXT⟩ := hT
    refine ⟨X, hX, fun p hp => ?_⟩
    obtain ⟨q, hq, e⟩ := hXT (Sum.inl p) (Finset.mem_toLeft.1 hp)
    rw [Sum.inl.inj e]
    exact hq
  have hout : Y.hon.output w x ρ T =
      (unif Y.Coin).map fun c => some (Y.ior.view T ((Y.hon.strat w x c).run ρ).1) := by
    unfold IOR.Honest.output
    rw [if_neg (by rintro (h | h) <;> exact h)]
    rfl
  rw [hout]
  show _ = (unif Y.Coin).map _
  refine map_unif_prod_congr (Equiv.addRight W₀) _ _ fun W => ?_
  obtain ⟨e1, e2⟩ := hW₀ W
  have hl : ∀ r : Y.Cw.Q → E, some (Y.ior.view T ((Y.hon.strat w x (W, r)).run ρ).1) =
      Y.gv T ρ (hMu Y.vars W) (Y.honQ w x W (Y.eps ρ) (Y.gam ρ))
        (Y.Cw.Nn.shows (Y.posOf T) (Y.pk W) r) := by
    intro r
    rw [Y.run_eq w x (W, r) ρ, Y.view_mk]
    rfl
  have hr : ∀ r : Y.Cw.Q → E,
      some (Y.ior.view T
            (Y.mkTr (Y.Cw.enc 0 r) (hMu Y.vars (W + W₀))
              (hTr Y.vars 0 (W + W₀) (Y.gam ρ) +
                fun i => Y.eps ρ • hTr Y.vars x.1 (0 : HIdx Y.vars → E) (Y.gam ρ) i) ρ)) =
        Y.gv T ρ (hMu Y.vars W) (Y.honQ w x W (Y.eps ρ) (Y.gam ρ))
          (Y.Cw.Nn.shows (Y.posOf T) 0 r) := by
    intro r
    rw [Y.view_mk, ← e1, ← e2]
    rfl
  show (unif (Y.Cw.Q → E)).map (fun r => some (Y.ior.view T ((Y.hon.strat w x (W, r)).run ρ).1)) =
    (unif (Y.Cw.Q → E)).map fun r =>
      some (Y.ior.view T
          (Y.mkTr (Y.Cw.enc 0 r) (hMu Y.vars (W + W₀))
            (hTr Y.vars 0 (W + W₀) (Y.gam ρ) +
              fun i => Y.eps ρ • hTr Y.vars x.1 (0 : HIdx Y.vars → E) (Y.gam ρ) i) ρ))
  rw [funext hl, funext hr]
  have hh := hZk (Y.posOf T) hS (Y.pk W) 0
  have := congrArg (fun p => p.map (Y.gv T ρ (hMu Y.vars W) (Y.honQ w x W (Y.eps ρ) (Y.gam ρ)))) hh
  simpa only [PMF.map_comp] using this

theorem ld_sum_exact (E P : Type) [Field E] [Fintype E] : Spec.ld_sum_exact E P := fun Y t hn hZk =>
  ⟨Y.sim, ld_sum_exactWith E P Y t hn hZk⟩

end Cb
