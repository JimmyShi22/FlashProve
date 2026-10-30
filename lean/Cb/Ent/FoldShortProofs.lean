-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ent/FoldShortProofs.lean: the proofs of the statements of Cb/Ent/FoldShort.lean: the fold with
short rounds.

By recursion on the number of rounds: the image of a transcript, its verifier messages, the round
equations on the completed polynomials (`phi_fill`, Cb/Ld/LdHideShort.lean), the last running claim.
Knowledge soundness: `ld_sum_know` (Cb/Ld/LdSumKnowProofs.lean), then `know_pullC_ior`
(Ior/PullCProofs.lean).

Main names: one theorem for each statement, of the same name.

Limits: those in the head of Cb/Ent/FoldShort.lean.

Terms: lean/GLOSSARY.md.

-/
import Cb.Ent.FoldShort
import Cb.Ld.LdSumKnowProofs
import Ior.PullCProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

section Rounds
variable {E Ch : Type} [Field E] [Fintype Ch] [Nonempty Ch] (val : Ch → E) (n : ℕ)
  (fx : Fin (n + 1) × E)

/-- the image of a transcript of k short rounds -/
theorem sCar_tr : ∀ (k : ℕ) (σ : E) (τ : Tr (List.replicate k (sRoundS E Ch n))),
    (sCar val n fx k σ).tr τ = some (sUp val n fx k σ τ)
  | 0, _, _ => rfl
  | k + 1, σ, (m, c, τ) => by
      show (some c).bind (fun c' =>
        ((sCar val n fx k (hev (sFill n fx σ m.2) (val c))).tr τ).map fun τ' =>
          (((), sFill n fx σ m.2), c', τ')) = _
      rw [sCar_tr k _ τ]
      rfl

/-- one verifier message goes to one -/
theorem sCar_fib : ∀ (k : ℕ) (σ : E), (sCar val n fx k σ).Fib (Err.ones _)
  | 0, _ => trivial
  | k + 1, _ =>
      ⟨fun _ _ => cnt_le_one fun _ _ ha hb => Option.some.inj (ha.trans hb.symm),
        fun _ _ => sCar_fib k _⟩

/-- the verifier messages of the image -/
theorem sUp_rho : ∀ (k : ℕ) (σ : E) (τ : Tr (List.replicate k (sRoundS E Ch n))),
    (sUp val n fx k σ τ).rho = sUpRho n k τ.rho
  | 0, _, _ => rfl
  | k + 1, σ, (m, c, τ) => by
      show (c, (sUp val n fx k _ τ).rho) = (c, sUpRho n k τ.rho)
      rw [sUp_rho k _ τ]

/-- the round equations hold of the image -/
theorem sUp_cons (h : fx.2 * (HVar.plain E n).mon fx.1 = 1) :
    ∀ (k : ℕ) (σ : E) (τ : Tr (List.replicate k (sRoundS E Ch n))),
      HCons (sVars E n k) σ (sQ n k (sUp val n fx k σ τ).plains)
        (sG val n k (sUp val n fx k σ τ).rho)
  | 0, _, _ => trivial
  | k + 1, σ, (m, _, τ) =>
      ⟨phi_fill (HVar.plain E n) fx h σ m.2, sUp_cons h k _ τ⟩

/-- the value with which the block's verifier ends on the image -/
theorem sUp_fin : ∀ (k : ℕ) (σ : E) (τ : Tr (List.replicate k (sRoundS E Ch n))),
    hFin (sVars E n k) σ (sQ n k (sUp val n fx k σ τ).plains)
      (sG val n k (sUp val n fx k σ τ).rho) = sClaim val n fx k σ τ
  | 0, _, _ => rfl
  | k + 1, _, (_, _, τ) => sUp_fin k _ τ

/-- k short rounds have as many verifier messages as k rounds -/
theorem sRoundS_chal : ∀ k : ℕ,
    Shape.chalList (List.replicate k (sRoundS E Ch n)) =
      Shape.chalList (List.replicate k (sRound E Ch n))
  | 0 => rfl
  | k + 1 => congrArg (List.cons (Fintype.card Ch)) (sRoundS_chal k)

end Rounds

theorem ldEnt_foldS_tr : Spec.ldEnt_foldS_tr := by
  intro E P _ Y fx t₀ τ
  obtain ⟨m, c, τ⟩ := τ
  show (some c).bind (fun c' =>
    ((sCar Y.val Y.n fx Y.k (m.2 + t₀ * Y.val c)).tr τ).map fun τ' => (m, c', τ')) = _
  rw [sCar_tr]
  rfl

theorem ldEnt_foldS_fib : Spec.ldEnt_foldS_fib := fun _ _ _ Y fx _ =>
  ⟨fun _ _ => cnt_le_one fun _ _ ha hb => Option.some.inj (ha.trans hb.symm),
    fun _ _ => sCar_fib Y.val Y.n fx Y.k _⟩

/-- the verifier messages of the image of a transcript of the fold -/
theorem SumPar.upS_rho {E P : Type} [Field E] (Y : SumPar E P) (fx : Fin (Y.n + 1) × E) (t₀ : E)
    (τ : Tr Y.shapeS) : (Y.upS fx t₀ τ).rho = Y.upRho τ.rho := by
  obtain ⟨m, c, τ⟩ := τ
  show (c, (sUp Y.val Y.n fx Y.k _ τ).rho) = (c, sUpRho Y.n Y.k τ.rho)
  rw [sUp_rho]

theorem ldEnt_foldS_imp : Spec.ldEnt_foldS_imp := by
  intro E P _ Y fx t₀ y τ
  unfold SumPar.impS SumPar.imp
  rw [Y.upS_rho fx t₀ τ]
  rfl

theorem ldEnt_foldS_know : Spec.ldEnt_foldS_know := by
  intro E P _ _ _ Y fx d e Lst mC mS mW d₀ hC hE hv hn hQ
  refine know_pullC_ior _ _ _ _ Y.ior Y.shapeS (fun a => Y.carS fx a.1.1) Y.impS Y.declS
    (Err.ones Y.shapeS) _ _ _ _ _ (Y.ext d) (Y.err Lst mC mS mW) d₀ ?_
    (ld_sum_know E P Y d e Lst mC mS mW hC hE hv hn hQ)
    fun a _ => ldEnt_foldS_fib E P Y fx a.1.1
  intro a τ τ' hτ
  have hτ' : some (Y.upS fx a.1.1 τ) = some τ' := (ldEnt_foldS_tr E P Y fx a.1.1 τ).symm.trans hτ
  rw [← Option.some.inj hτ']
  exact ldEnt_foldS_imp E P Y fx a.1.1 a.2 τ

theorem ldEnt_foldS_err : Spec.ldEnt_foldS_err := by
  intro E P _ _ Y Lst mC mS mW
  exact mulErr_ones_toList _ _ (Y.carS (0, 0) 0) _

theorem ldEnt_foldS_chal : Spec.ldEnt_foldS_chal := fun E _ _ Y =>
  congrArg (List.cons (Fintype.card Y.Ch)) (sRoundS_chal (E := E) (Ch := Y.Ch) Y.n Y.k)

theorem ldEnt_foldS_out : Spec.ldEnt_foldS_out := by
  intro E P _ Y fx h x y τ
  show ((Y.carS fx x.1).tr τ).bind (Y.out x) = _
  rw [ldEnt_foldS_tr E P Y fx x.1 τ]
  obtain ⟨m, c, τ⟩ := τ
  show Y.out x (Y.upS fx x.1 (m, c, τ)) = _
  have hc : HCons Y.vars (Y.mu (Y.upS fx x.1 (m, c, τ)).plains +
      x.1 * Y.eps (Y.upS fx x.1 (m, c, τ)).rho) (Y.qs (Y.upS fx x.1 (m, c, τ)).plains)
      (Y.gam (Y.upS fx x.1 (m, c, τ)).rho) :=
    sUp_cons Y.val Y.n fx h Y.k (m.2 + x.1 * Y.val c) τ
  have hf : hFin Y.vars (Y.mu (Y.upS fx x.1 (m, c, τ)).plains +
      x.1 * Y.eps (Y.upS fx x.1 (m, c, τ)).rho) (Y.qs (Y.upS fx x.1 (m, c, τ)).plains)
      (Y.gam (Y.upS fx x.1 (m, c, τ)).rho) =
        sClaim Y.val Y.n fx Y.k (m.2 + x.1 * Y.val c) τ :=
    sUp_fin Y.val Y.n fx Y.k (m.2 + x.1 * Y.val c) τ
  unfold SumPar.out
  rw [if_pos hc, hf, Y.upS_rho fx x.1 (m, c, τ)]

theorem ldEnt_foldS_lin : Spec.ldEnt_foldS_lin := by
  intro E _ n
  show (1 : E) * ∑ s : Bool, (1 : E) * (if s then (1 : E) else 0) ^ ((1 : Fin (n + 1 + 1)) : ℕ) = 1
  rw [Fintype.sum_bool]
  simp

end Cb
