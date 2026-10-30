-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/PullProofs.lean: a protocol whose challenges are computed from other uniform strings keeps all
its properties, up to the samplers' bias. (Words of this library: lean/GLOSSARY.md.)
`InteractiveOracleProof.pull` (Iop/Pull.lean) pulls a protocol back along one sampler φ : Src → Chal for each round:
the verifier sends a uniform element of Src, and everything else uses its image under φ.
The bias is measured multiplicatively. The samplers are good (`Samplers.Good`, Iop/Pull.lean) with
numbers κ and K if in each round every fibre of φ has at most w elements and w |Chal| ≤ κ |Src|, and
K bounds the product of these ratios over all rounds. Then a count e of bad values becomes `e * w`,
a round's error grows by at most the factor κ, and the probability of a set of values of the whole
verifier randomness by at most the factor K.

This file proves `univGood`, the statement on the universal samplers (Iop/Univ.lean), and the
lemmas of `Spec.pullPropsB` (Iop/BatchPull.lean).
-/
import Iop.Pull
import Iop.Univ
import Iop.State
import Prob.Bias

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. The push (`Tr.push`, Iop/Pull.lean) commutes with everything -/

theorem Tr.rho_push :
    ∀ {s : Shape} (σ : Samplers s) (τ : Tr (s.pull σ)), (Tr.push σ τ).rho = Rho.push σ τ.rho
  | [], _, _ => rfl
  | _ :: _, (σ, σs), (_, c, τ) => by
      show (σ.φ c, (Tr.push σs τ).rho) = (σ.φ c, Rho.push σs τ.rho)
      rw [Tr.rho_push σs τ]

theorem Tr.plains_push :
    ∀ {s : Shape} (σ : Samplers s) (τ : Tr (s.pull σ)),
      (Tr.push σ τ).plains = Plains.push σ τ.plains
  | [], _, _ => rfl
  | _ :: _, (_, σs), (m, _, τ) => by
      show (m.2, (Tr.push σs τ).plains) = (m.2, Plains.push σs τ.plains)
      rw [Tr.plains_push σs τ]

/-- Plain parts do not change: the map in the other direction. -/
def Plains.pull : {s : Shape} → (σ : Samplers s) → Plains s → Plains (s.pull σ)
  | [], _, _ => ()
  | _ :: _, (_, σs), (a, pl) => (a, Plains.pull σs pl)

theorem Plains.pull_push :
    ∀ {s : Shape} (σ : Samplers s) (pl : Plains (s.pull σ)), Plains.pull σ (Plains.push σ pl) = pl
  | [], _, _ => rfl
  | _ :: _, (_, σs), (a, pl) => by
      show (a, Plains.pull σs (Plains.push σs pl)) = (a, pl)
      rw [Plains.pull_push σs pl]

/-- The alphabet at a position does not change. -/
def OSym.push :
    {s : Shape} → (σ : Samplers s) → (p : OPos (s.pull σ)) →
    OSym (s.pull σ) p → OSym s (OPos.pushEquiv σ p)
  | _ :: _, (_, _), .inl _, a => a
  | _ :: _, (_, σs), .inr p, a => OSym.push σs p a

/-- The alphabet at a position does not change: the map in the other direction. -/
def OSym.pull :
    {s : Shape} → (σ : Samplers s) → (p : OPos (s.pull σ)) →
    OSym s (OPos.pushEquiv σ p) → OSym (s.pull σ) p
  | _ :: _, (_, _), .inl _, a => a
  | _ :: _, (_, σs), .inr p, a => OSym.pull σs p a

theorem OSym.pull_push :
    ∀ {s : Shape} (σ : Samplers s) (p : OPos (s.pull σ)) (a : OSym (s.pull σ) p),
      OSym.pull σ p (OSym.push σ p a) = a
  | _ :: _, (_, _), .inl _, _ => rfl
  | _ :: _, (_, σs), .inr p, a => OSym.pull_push σs p a

/-- The answers of the prover's oracles do not change. -/
theorem Tr.read_push : ∀ {s : Shape} (σ : Samplers s) (τ : Tr (s.pull σ)) (p : OPos (s.pull σ)),
    (Tr.push σ τ).read (OPos.pushEquiv σ p) = OSym.push σ p (τ.read p)
  | _ :: _, (_, _), (_, _, _), .inl _ => rfl
  | _ :: _, (_, σs), (_, _, τ), .inr p => Tr.read_push σs τ p

/-- The transcript of a run of the pulled-back strategy, pushed forward, is that of the run of the
strategy at the pushed randomness. -/
theorem Strat.run_pull :
    ∀ {s : Shape} {β : Type} (σ : Samplers s) (S : Strat s β) (ρ : Rho (s.pull σ)),
      Tr.push σ ((Strat.pull σ S).run ρ).1 = (S.run (Rho.push σ ρ)).1
  | [], _, _, _, _ => rfl
  | _ :: _, _, (σ, σs), (m, k), (c, ρ) => by
      show (m, σ.φ c, Tr.push σs ((Strat.pull σs (k (σ.φ c))).run ρ).1) =
        (m, σ.φ c, ((k (σ.φ c)).run (Rho.push σs ρ)).1)
      rw [Strat.run_pull σs]

/-! ## 2. Counting -/

/-- All fibres of all samplers are within their bounds w. -/
def Samplers.Fib : {s : Shape} → Samplers s → Prop
  | [], _ => True
  | r :: _, (σ, σs) => (∀ c : r.Chal, cnt (fun a : σ.Src => σ.φ a = c) ≤ σ.w) ∧ Samplers.Fib σs

theorem Samplers.Good.fib : ∀ {s : Shape} {σ : Samplers s} {κ K : ℝ≥0∞}, σ.Good κ K → σ.Fib
  | [], _, _, _, _ => trivial
  | _ :: _, (_, _), _, _, h => ⟨h.1, let ⟨_, h', _⟩ := h.2.2; Samplers.Good.fib h'⟩

/-- A larger K is good too. -/
theorem Samplers.Good.mono :
    ∀ {s : Shape} {σ : Samplers s} {κ K K' : ℝ≥0∞}, σ.Good κ K → K ≤ K' → σ.Good κ K'
  | [], _, _, _, _, h, hK => le_trans h hK
  | _ :: _, (_, _), _, _, _, h, hK =>
      ⟨h.1, h.2.1, let ⟨K₀, h₀, h₁⟩ := h.2.2; ⟨K₀, h₀, h₁.trans (by gcongr)⟩⟩

/-- The product of the bounds on the fibres. -/
def Samplers.W : {s : Shape} → Samplers s → ℕ
  | [], _ => 1
  | _ :: _, (σ, σs) => σ.w * Samplers.W σs

/-- Under `σ.Fib`: a value of the whole verifier randomness has at most W preimages. -/
theorem Samplers.Fib.cnt_push_le : ∀ {s : Shape} {σ : Samplers s}, σ.Fib → ∀ ρ : Rho s,
    cnt (fun ρ' : Rho (s.pull σ) => Rho.push σ ρ' = ρ) ≤ σ.W
  | [], _, _, _ =>
    (cnt_le_card _).trans
      (le_of_eq (Fintype.card_eq_nat_card.trans (Nat.card_unique : Nat.card Unit = 1)))
  | r :: s, (σ, σs), h, (c, ρ) => by
      have h1 : cnt (fun x : σ.Src × Rho (Shape.pull s σs) => σ.φ x.1 = c ∧ Rho.push σs x.2 = ρ) =
          cnt (fun a : σ.Src => σ.φ a = c) *
            cnt (fun ρ' : Rho (Shape.pull s σs) => Rho.push σs ρ' = ρ) :=
        cnt_and_prod (fun a : σ.Src => σ.φ a = c)
          (fun ρ' : Rho (Shape.pull s σs) => Rho.push σs ρ' = ρ)
      have h2 : cnt (fun ρ' : Rho (Shape.pull (r :: s) (σ, σs)) =>
            Rho.push (s := r :: s) (σ, σs) ρ' = (c, ρ)) =
          cnt (fun x : σ.Src × Rho (Shape.pull s σs) => σ.φ x.1 = c ∧ Rho.push σs x.2 = ρ) :=
        cnt_congr (C := σ.Src × Rho (Shape.pull s σs)) fun x => Prod.mk.injEq _ _ _ _ ▸ Iff.rfl
      rw [h2, h1]
      exact Nat.mul_le_mul (h.1 c) (Samplers.Fib.cnt_push_le h.2 ρ)

/-- For good samplers, the product of the bounds, times the number of values, is at most K times the
number of sources. -/
theorem Samplers.Good.W_mul_card_le : ∀ {s : Shape} {σ : Samplers s} {κ K : ℝ≥0∞}, σ.Good κ K →
    (σ.W : ℝ≥0∞) * Fintype.card (Rho s) ≤ K * Fintype.card (Rho (s.pull σ))
  | [], _, _, K, h => by
      have e : Fintype.card (Rho []) = 1 :=
        Fintype.card_eq_nat_card.trans (Nat.card_unique : Nat.card Unit = 1)
      show ((1 : ℕ) : ℝ≥0∞) * Fintype.card (Rho []) ≤ K * Fintype.card (Rho [])
      rw [e]
      simpa using h
  | r :: s, (σ, σs), κ, K, h => by
      obtain ⟨K', h', hK⟩ := h.2.2
      have ih := Samplers.Good.W_mul_card_le h'
      have e1 : Fintype.card (Rho (r :: s)) = Fintype.card r.Chal * Fintype.card (Rho s) :=
        card_rho_cons r s
      have e2 : Fintype.card (Rho (Shape.pull (r :: s) (σ, σs))) =
          Fintype.card σ.Src * Fintype.card (Rho (Shape.pull s σs)) :=
        card_rho_cons (r.pull σ) (Shape.pull s σs)
      rw [e1, e2]
      show ((σ.w * σs.W : ℕ) : ℝ≥0∞) * _ ≤ _
      push_cast
      calc (σ.w : ℝ≥0∞) * σs.W * (Fintype.card r.Chal * Fintype.card (Rho s))
          = σ.w * Fintype.card r.Chal * (σs.W * Fintype.card (Rho s)) := by ring
        _ ≤ σ.w * Fintype.card r.Chal * (K' * Fintype.card (Rho (Shape.pull s σs))) :=
          mul_le_mul' le_rfl ih
        _ = σ.w * Fintype.card r.Chal * K' * Fintype.card (Rho (Shape.pull s σs)) := by ring
        _ ≤ K * Fintype.card σ.Src * Fintype.card (Rho (Shape.pull s σs)) := mul_le_mul' hK le_rfl
        _ = K * (Fintype.card σ.Src * Fintype.card (Rho (Shape.pull s σs))) := by ring

/-- For good samplers, the preimage of a set of values of the verifier randomness has at most K
times its probability. -/
theorem prRho_preimage_le {s : Shape} {σ : Samplers s} {κ K : ℝ≥0∞}
    (h : σ.Good κ K) (S : Set (Rho s)) :
    prRho {ρ : Rho (s.pull σ) | Rho.push σ ρ ∈ S} ≤ K * prRho S :=
  pr_preimage_le_mul (Rho.push σ) h.fib.cnt_push_le h.W_mul_card_le S

/-! ## 3. Soundness -/

/-- Under `σ.Fib`: a doomed prover stays doomed, with each count multiplied by the bound on the
fibres. -/
theorem Doomed.pull : ∀ {s : Shape} {σ : Samplers s}, σ.Fib → ∀ (ε : Err s) (bad : Tr s → Prop),
    Doomed s ε bad → Doomed (s.pull σ) (Err.pull σ ε) (fun τ => bad (Tr.push σ τ))
  | [], _, _, _, _, h => h
  | r :: s, (σ, σs), hσ, (e, ε), bad, h => fun m => by
      have h1 : cnt (fun c : σ.Src =>
            ¬ Doomed (Shape.pull s σs) (Err.pull σs ε) (fun τ => bad (m, σ.φ c, Tr.push σs τ))) ≤
          cnt (fun c : σ.Src => ¬ Doomed s ε (fun τ => bad (m, σ.φ c, τ))) :=
        cnt_mono fun c hc hd => hc (Doomed.pull hσ.2 ε (fun τ => bad (m, σ.φ c, τ)) hd)
      have h2 : cnt (fun c : σ.Src => ¬ Doomed s ε (fun τ => bad (m, σ.φ c, τ)))
          ≤ cnt (fun c : r.Chal => ¬ Doomed s ε (fun τ => bad (m, c, τ))) * σ.w :=
        cnt_comp_le σ.φ hσ.1 fun c => ¬ Doomed s ε (fun τ => bad (m, c, τ))
      exact h1.trans (h2.trans (Nat.mul_le_mul_right _ (h m)))

theorem InteractiveOracleProof.Sound.pull {X : Type} {E : ExtSpec} {Q : InteractiveOracleProof X E} {σ : Samplers Q.shape}
    (hσ : σ.Fib) {L : X → E.Str → Prop} {ε : Err Q.shape} (h : Q.Sound L ε) :
    (Q.pull σ).Sound L (Err.pull σ ε) :=
  fun x y hL => Doomed.pull hσ ε _ (h x y hL)

/-- For good samplers: if every error of the list, as a probability, is at most c, then after the
pull-back every error is at most κ * c. -/
theorem Err.Below.pull :
    ∀ {s : Shape} {σ : Samplers s} {κ K : ℝ≥0∞},
      σ.Good κ K → ∀ {ε : Err s} {c : ℝ≥0∞}, Err.Below ε c → Err.Below (Err.pull σ ε) (κ * c)
  | [], _, _, _, _, _, _, _ => trivial
  | r :: _, (σ, _), κ, _, h, (e, _), c, hb => by
      obtain ⟨_, h', _⟩ := h.2.2
      refine ⟨?_, Err.Below.pull h' hb.2⟩
      show ((e * σ.w : ℕ) : ℝ≥0∞) ≤ κ * c * (Fintype.card σ.Src : ℝ≥0∞)
      push_cast
      calc (e : ℝ≥0∞) * σ.w ≤ c * Fintype.card r.Chal * σ.w := mul_le_mul' hb.1 le_rfl
        _ = c * (σ.w * Fintype.card r.Chal) := by ring
        _ ≤ c * (κ * Fintype.card σ.Src) := mul_le_mul' le_rfl h.2.1
        _ = κ * c * Fintype.card σ.Src := by ring

/-! ## 4. Locality, acceptance, abort sets (`Honest.withheld`) -/

section OneProtocol

variable {X : Type} {E : ExtSpec} {Q : InteractiveOracleProof X E} {Wt : Type}

theorem InteractiveOracleProof.mem_reads_pull (σ : Samplers Q.shape) (x : X) (ρ : Rho (Q.shape.pull σ))
    (pl : Plains (Q.shape.pull σ)) (p : OPos (Q.shape.pull σ)) :
    p ∈ (Q.pull σ).reads x ρ pl ↔
    OPos.pushEquiv σ p ∈ Q.reads x (Rho.push σ ρ) (Plains.push σ pl) := by
  show p ∈ (Q.reads x (Rho.push σ ρ) (Plains.push σ pl)).map (OPos.pushEquiv σ).symm.toEmbedding ↔ _
  rw [Finset.mem_map_equiv, Equiv.symm_symm]

theorem InteractiveOracleProof.IsLocal.pull (h : Q.IsLocal) (σ : Samplers Q.shape) : (Q.pull σ).IsLocal := by
  intro x y y' τ τ' hρ hpl hext hrd
  refine h x y y' (Tr.push σ τ) (Tr.push σ τ') ?_ ?_ ?_ ?_
  · rw [Tr.rho_push, Tr.rho_push]
    exact congrArg (Rho.push σ) hρ
  · rw [Tr.plains_push, Tr.plains_push]
    exact congrArg (Plains.push σ) hpl
  · intro p hp
    rw [Tr.rho_push] at hp
    exact hext p hp
  · intro p hp
    rw [Tr.rho_push, Tr.plains_push] at hp
    obtain ⟨p', rfl⟩ := (OPos.pushEquiv σ).surjective p
    rw [Tr.read_push, Tr.read_push]
    exact congrArg (OSym.push σ p') (hrd p' ((InteractiveOracleProof.mem_reads_pull σ x _ _ p').2 hp))

theorem Honest.mem_withheld_pull
    (H : Honest Q Wt) (σ : Samplers Q.shape) (w : Wt) (x : X) (ρ : Rho (Q.shape.pull σ)) :
    ρ ∈ (H.pull σ).withheld w x ↔ Rho.push σ ρ ∈ H.withheld w x := Iff.rfl

theorem Honest.Acc.pull {H : Honest Q Wt} {valid : Wt → X → Prop}
    (h : H.Acc valid) (σ : Samplers Q.shape) : (H.pull σ).Acc valid := by
  intro w x c ρ hv hρ
  show Q.accept x (H.ext w) (Tr.push σ ((Strat.pull σ (H.strat w x c)).run ρ).1) = true
  rw [Strat.run_pull]
  exact h w x c (Rho.push σ ρ) hv hρ

theorem Honest.prRho_withheld_pull (H : Honest Q Wt) {σ : Samplers Q.shape} {κ K : ℝ≥0∞}
    (hσ : σ.Good κ K) (w : Wt) (x : X) {p : ℝ≥0∞} (h : prRho (H.withheld w x) ≤ p) :
    prRho ((H.pull σ).withheld w x) ≤ K * p :=
  (prRho_preimage_le hσ (H.withheld w x)).trans (by gcongr)

/-! ## 5. Honest-verifier zero knowledge -/

/-- A disclosed view of the protocol, as a disclosed view of the pulled-back protocol. -/
def DView.pull (σ : Samplers Q.shape) (v : DView Q) : DView (Q.pull σ) where
  plains := Plains.pull σ v.plains
  ext := v.ext
  orc := fun p => (v.orc (OPos.pushEquiv σ p)).map (OSym.pull σ p)

theorem InteractiveOracleProof.extAns_pull (σ : Samplers Q.shape) (x : X) (ρ : Rho (Q.shape.pull σ)) (y : E.Str) :
    (Q.pull σ).extAns x ρ y = Q.extAns x (Rho.push σ ρ) y := rfl

/-- The disclosed view of a transcript is the image of the disclosed view of the pushed transcript.
-/
theorem InteractiveOracleProof.dview_pull (σ : Samplers Q.shape) (x : X) (y : E.Str) (τ : Tr (Q.shape.pull σ)) :
    (Q.pull σ).dview x y τ = DView.pull σ (Q.dview x y (Tr.push σ τ)) := by
  have h1 : τ.plains = Plains.pull σ (Tr.push σ τ).plains := by
    rw [Tr.plains_push, Plains.pull_push]
  have h2 : (Q.pull σ).extAns x τ.rho y = Q.extAns x (Tr.push σ τ).rho y := by
    rw [Tr.rho_push, InteractiveOracleProof.extAns_pull]
  have h3 : ((Q.pull σ).dview x y τ).orc = (DView.pull σ (Q.dview x y (Tr.push σ τ))).orc := by
    funext p
    have hiff : (p ∈ (Q.pull σ).reads x τ.rho τ.plains ∨ (Q.pull σ).blinded p = false) ↔
        (OPos.pushEquiv σ p ∈ Q.reads x (Tr.push σ τ).rho (Tr.push σ τ).plains ∨
          Q.blinded (OPos.pushEquiv σ p) = false) := by
      refine or_congr ?_ Iff.rfl
      rw [Tr.rho_push, Tr.plains_push]
      exact InteractiveOracleProof.mem_reads_pull σ x τ.rho τ.plains p
    dsimp only [InteractiveOracleProof.dview, DView.pull]
    split_ifs with ha hb hb
    · exact congrArg some
        ((OSym.pull_push σ p (τ.read p)).symm.trans
          (congrArg (OSym.pull σ p) (Tr.read_push σ τ p).symm))
    · exact absurd (hiff.1 ha) hb
    · exact absurd (hiff.2 hb) ha
    · rfl
  show DView.mk τ.plains ((Q.pull σ).extAns x τ.rho y) ((Q.pull σ).dview x y τ).orc
    = DView.mk (Plains.pull σ (Tr.push σ τ).plains) (Q.extAns x (Tr.push σ τ).rho y)
        (DView.pull σ (Q.dview x y (Tr.push σ τ))).orc
  rw [← h1, ← h2, ← h3]

/-- The honest output at ρ is the image of the honest output at the pushed ρ. -/
theorem Honest.output_pull (H : Honest Q Wt) (σ : Samplers Q.shape) (w : Wt)
    (x : X) (ρ : Rho (Q.shape.pull σ)) :
    (H.pull σ).output w x ρ = (H.output w x (Rho.push σ ρ)).map (Option.map (DView.pull σ)) := by
  by_cases h : Rho.push σ ρ ∈ H.withheld w x
  · have e1 : (H.pull σ).output w x ρ = PMF.pure none := if_pos h
    have e2 : H.output w x (Rho.push σ ρ) = PMF.pure none := if_pos h
    rw [e1, e2, PMF.pure_map]
    rfl
  · have e1 : (H.pull σ).output w x ρ
        = (unif H.Coin).map fun c =>
          some ((Q.pull σ).dview x (H.ext w) ((Strat.pull σ (H.strat w x c)).run ρ).1) := if_neg h
    have e2 : H.output w x (Rho.push σ ρ) =
        (unif H.Coin).map fun c =>
          some (Q.dview x (H.ext w) ((H.strat w x c).run (Rho.push σ ρ)).1) := if_neg h
    rw [e1, e2, PMF.map_comp]
    congr 1
    funext c
    show some ((Q.pull σ).dview x (H.ext w) ((Strat.pull σ (H.strat w x c)).run ρ).1)
      = some (DView.pull σ (Q.dview x (H.ext w) ((H.strat w x c).run (Rho.push σ ρ)).1))
    rw [InteractiveOracleProof.dview_pull, Strat.run_pull]

/-- For good samplers, honest-verifier zero knowledge in the exact form (`Honest.HVZK`) is
preserved, with the error K * z: the simulator is the image of the old one, and the exceptional set
is contained in the preimage of the old one. -/
theorem Honest.HVZK.pull {H : Honest Q Wt} {valid : Wt → X → Prop} {z : ℝ≥0∞} (h : H.HVZK valid z)
    {σ : Samplers Q.shape} {κ K : ℝ≥0∞} (hσ : σ.Good κ K) : (H.pull σ).HVZK valid (K * z) := by
  obtain ⟨Sim, hS⟩ := h
  refine ⟨fun x ρ a => (Sim x (Rho.push σ ρ) a).map (Option.map (DView.pull σ)), fun w x hv => ?_⟩
  refine le_trans (pr_mono _ ?_) ((prRho_preimage_le hσ _).trans (by gcongr; exact hS w x hv))
  intro ρ hρ heq
  apply hρ
  rw [Honest.output_pull, heq]
  rfl

end OneProtocol

/-- A round whose oracle is a string stays one. -/
def Round.IsPoint.pull {r : Round} (h : r.IsPoint) (σ : Sampler r) : (r.pull σ).IsPoint :=
  ⟨h.finPos, h.decPos, h.ofSyms, h.rd_ofSyms, h.ofSyms_rd, h.zero⟩

def Shape.IsPoint.pull : {s : Shape} → (σ : Samplers s) → s.IsPoint → (s.pull σ).IsPoint
  | [], _, _ => ()
  | _ :: _, (σ, σs), (h, hs) => (h.pull σ, Shape.IsPoint.pull σs hs)

/-! ## 7. The universal sampler -/

/-- The number of tuples of k hash blocks of λ bits. -/
theorem card_blocks (lam k : ℕ) : Fintype.card (Fin k → Dig lam) = 2 ^ (lam * k) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Fintype.card_fin, ← pow_mul]

/-- If 0 < λ, there are at least 2^λ times as many tuples of hash blocks as values of the challenge.
-/
theorem Round.card_mul_le (lam : ℕ) (hlam : 0 < lam) (r : Round) :
    Fintype.card r.Chal * 2 ^ lam ≤ Fintype.card (Fin (r.blocks lam) → Dig lam) := by
  rw [card_blocks]
  have h1 : Fintype.card r.Chal ≤ 2 ^ Nat.clog 2 (Fintype.card r.Chal) :=
    Nat.le_pow_clog (by norm_num) _
  have h2 : Nat.clog 2 (Fintype.card r.Chal) + lam ≤ lam * r.blocks lam := by
    unfold Round.blocks
    have h3 := Nat.div_add_mod (Nat.clog 2 (Fintype.card r.Chal)) lam
    have h4 := Nat.mod_lt (Nat.clog 2 (Fintype.card r.Chal)) hlam
    have h5 : lam * (Nat.clog 2 (Fintype.card r.Chal) / lam + 2) =
        lam * (Nat.clog 2 (Fintype.card r.Chal) / lam) + 2 * lam := by
      ring
    omega
  calc
    Fintype.card r.Chal * 2 ^ lam ≤ 2 ^ Nat.clog 2 (Fintype.card r.Chal) * 2 ^ lam :=
      Nat.mul_le_mul_right _ h1
    _ = 2 ^ (Nat.clog 2 (Fintype.card r.Chal) + lam) := (pow_add _ _ _).symm
    _ ≤ 2 ^ (lam * r.blocks lam) := Nat.pow_le_pow_right (by norm_num) h2

/-- Every value of the challenge has at most w preimages. -/
theorem Sampler.univ_fib (lam : ℕ) (r : Round)
    (nc : r.Chal ≃ Fin (Fintype.card r.Chal)) (c : r.Chal) :
    cnt (fun a : (Sampler.univ lam r nc).Src => (Sampler.univ lam r nc).φ a = c) ≤
      (Sampler.univ lam r nc).w := by
  have hpos : 0 < Fintype.card r.Chal := Fintype.card_pos
  have h1 : cnt (fun a : Fin (r.blocks lam) → Dig lam => (Sampler.univ lam r nc).φ a = c)
      = cnt (fun i : Fin (Fintype.card (Fin (r.blocks lam) → Dig lam)) =>
          (i : ℕ) ≡ (nc c : ℕ) [MOD Fintype.card r.Chal]) := by
    rw [← cnt_equiv (Num.blocks lam (r.blocks lam))
      (fun i => (i : ℕ) ≡ (nc c : ℕ) [MOD Fintype.card r.Chal])]
    refine cnt_congr fun a => ?_
    show nc.symm ⟨_ % Fintype.card r.Chal, _⟩ = c ↔ _
    rw [Equiv.symm_apply_eq, Fin.ext_iff]
    show _ % _ = _ ↔ _ % _ = _ % _
    rw [Nat.mod_eq_of_lt (nc c).isLt]
  show cnt (fun a : Fin (r.blocks lam) → Dig lam => (Sampler.univ lam r nc).φ a = c)
    ≤ Fintype.card (Fin (r.blocks lam) → Dig lam) / Fintype.card r.Chal + 1
  rw [h1, cnt_fin_modEq _ hpos]
  split_ifs <;> omega

theorem ratio_aux (S C lam : ℕ) (hle : C * 2 ^ lam ≤ S) :
    ((S / C + 1 : ℕ) : ℝ≥0∞) * (C : ℝ≥0∞) ≤ (1 + (2 ^ lam : ℝ≥0∞)⁻¹) * (S : ℝ≥0∞) := by
  have hn : (S / C + 1) * C ≤ S + C := by
    rw [add_mul, one_mul]
    exact Nat.add_le_add_right (Nat.div_mul_le_self S C) C
  have h2 : (2 ^ lam : ℝ≥0∞) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2t : (2 ^ lam : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have hle' : ((C * 2 ^ lam : ℕ) : ℝ≥0∞) ≤ (S : ℝ≥0∞) := by exact_mod_cast hle
  have hC : (C : ℝ≥0∞) ≤ (2 ^ lam : ℝ≥0∞)⁻¹ * S := by
    calc
      (C : ℝ≥0∞) = (2 ^ lam : ℝ≥0∞)⁻¹ * 2 ^ lam * C := by
        rw [ENNReal.inv_mul_cancel h2 h2t, one_mul]
      _ = (2 ^ lam : ℝ≥0∞)⁻¹ * ((C * 2 ^ lam : ℕ) : ℝ≥0∞) := by push_cast; ring
      _ ≤ (2 ^ lam : ℝ≥0∞)⁻¹ * S := by gcongr
  calc ((S / C + 1 : ℕ) : ℝ≥0∞) * (C : ℝ≥0∞) = (((S / C + 1) * C : ℕ) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ((S + C : ℕ) : ℝ≥0∞) := by exact_mod_cast hn
    _ = (S : ℝ≥0∞) + C := by push_cast; rfl
    _ ≤ (S : ℝ≥0∞) + (2 ^ lam : ℝ≥0∞)⁻¹ * S := by gcongr
    _ = (1 + (2 ^ lam : ℝ≥0∞)⁻¹) * (S : ℝ≥0∞) := by ring

/-- The ratio of one round, if 0 < λ: w |Chal| ≤ (1 + 2^-λ) |Src|. -/
theorem Sampler.univ_ratio (lam : ℕ) (hlam : 0 < lam) (r : Round)
    (nc : r.Chal ≃ Fin (Fintype.card r.Chal)) :
    ((Sampler.univ lam r nc).w : ℝ≥0∞) * (Fintype.card r.Chal : ℝ≥0∞) ≤
      (1 + (2 ^ lam : ℝ≥0∞)⁻¹) * (Fintype.card (Sampler.univ lam r nc).Src : ℝ≥0∞) :=
  ratio_aux _ _ lam (Round.card_mul_le lam hlam r)

/-- If 0 < λ, the universal samplers are good, with κ = 1 + 2^-λ for each round and K = κ^(number of
rounds). -/
theorem univGood : Spec.univGood := by
  intro lam hlam s
  induction s with
  | nil => intro _; exact le_of_eq (pow_zero _).symm
  | cons r s ih =>
    rintro ⟨nc, pts⟩
    refine ⟨Sampler.univ_fib lam r nc, Sampler.univ_ratio lam hlam r nc, _, ih pts, ?_⟩
    calc
      ((Sampler.univ lam r nc).w : ℝ≥0∞) * (Fintype.card r.Chal : ℝ≥0∞) *
            (1 + (2 ^ lam : ℝ≥0∞)⁻¹) ^ s.length ≤
          (1 + (2 ^ lam : ℝ≥0∞)⁻¹) * (Fintype.card (Sampler.univ lam r nc).Src : ℝ≥0∞) *
            (1 + (2 ^ lam : ℝ≥0∞)⁻¹) ^ s.length := by
          exact mul_le_mul' (Sampler.univ_ratio lam hlam r nc) le_rfl
      _ = (1 + (2 ^ lam : ℝ≥0∞)⁻¹) ^ (r :: s).length *
            (Fintype.card (Sampler.univ lam r nc).Src : ℝ≥0∞) := by
          rw [List.length_cons, pow_succ]
          ring

end Iop
