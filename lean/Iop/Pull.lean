-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/Pull.lean: protocols whose challenges are computed from other uniform strings.

The file has definitions; lemmas on them are in Iop/PullProofs.lean. The protocols of Blocks/ have
challenges in fields, sets of positions and so on. The compiler (Compile/) takes protocols whose
challenges are computed from tuples of hash blocks so that uniform blocks give a uniform challenge.
Between them is this one construction: pull a protocol back along a sampler φ : Src → Chal for each
round (`InteractiveOracleProof.pull`). The bias is measured multiplicatively, by the size of the largest fibre: if
every value of Chal has at most w preimages and w · |Chal| ≤ κ · |Src|, then every error count e
becomes e · w, every round error grows by at most the factor κ, and the probability of a set of
verifier randomness by at most K, a bound on the product of the ratios w · |Chal| / |Src| over the
rounds (`prRho_preimage_le`, Iop/PullProofs.lean).
-/
import Iop.InteractiveOracleProof
noncomputable section -- Lean tags what it cannot compile

namespace Iop
open Prob
open scoped ENNReal

/-- A sampler for one round: the challenge is φ of a uniform element of Src. w: the bound on the
fibres that `Samplers.Good` asks for (by type any number). -/
structure Sampler (r : Round) where
  Src : Type
  finSrcT : Unit → Fintype Src := by lazy_instance
  [neSrc  : Nonempty Src]
  φ : Src → r.Chal
  w : ℕ

/-- The instance of the sampler. -/
@[reducible] def Sampler.finSrc {r : Round} (σ : Sampler r) : Fintype σ.Src := σ.finSrcT ()

attribute [instance] Sampler.finSrc Sampler.neSrc

/-- The same round with an element of the sampler's source Src as challenge. -/
def Round.pull (r : Round) (σ : Sampler r) : Round :=
  { Orc := r.Orc, Pos := r.Pos, Sym := r.Sym, rd := r.rd, Plain := r.Plain, Chal := σ.Src,
    dOrc := r.dOrc, dPlain := r.dPlain }

/-- One sampler for each round. -/
def Samplers : Shape → Type 1
  | [] => PUnit
  | r :: s => Sampler r × Samplers s

def Shape.pull : (s : Shape) → Samplers s → Shape
  | [], _ => []
  | r :: s, (σ, σs) => r.pull σ :: Shape.pull s σs

def Rho.push : {s : Shape} → (σ : Samplers s) → Rho (s.pull σ) → Rho s
  | [], _, _ => ()
  | _ :: _, (σ, σs), (c, ρ) => (σ.φ c, Rho.push σs ρ)

def Tr.push : {s : Shape} → (σ : Samplers s) → Tr (s.pull σ) → Tr s
  | [], _, _ => ()
  | _ :: _, (σ, σs), (m, c, τ) => (m, σ.φ c, Tr.push σs τ)

def Plains.push : {s : Shape} → (σ : Samplers s) → Plains (s.pull σ) → Plains s
  | [], _, _ => ()
  | _ :: _, (_, σs), (a, pl) => (a, Plains.push σs pl)

/-- Positions do not change. -/
def OPos.pushEquiv : {s : Shape} → (σ : Samplers s) → OPos (s.pull σ) ≃ OPos s
  | [], _ => Equiv.refl Empty
  | _ :: _, (_, σs) => Equiv.sumCongr (Equiv.refl _) (OPos.pushEquiv σs)

def Strat.pull : {s : Shape} → {β : Type} → (σ : Samplers s) → Strat s β → Strat (s.pull σ) β
  | [], _, _, b => b
  | _ :: _, _, (σ, σs), (m, k) => (m, fun c => Strat.pull σs (k (σ.φ c)))

/-- Errors: each count is multiplied by the bound on the fibres. -/
def Err.pull : {s : Shape} → (σ : Samplers s) → Err s → Err (s.pull σ)
  | [], _, _ => ()
  | _ :: _, (σ, σs), (e, ε) => (e * σ.w, Err.pull σs ε)

variable {X : Type} {E : ExtSpec}

/-- The protocol pulled back along the samplers. -/
def InteractiveOracleProof.pull (Q : InteractiveOracleProof X E) (σ : Samplers Q.shape) : InteractiveOracleProof X E where
  shape    := Q.shape.pull σ
  blinded  := fun p => Q.blinded (OPos.pushEquiv σ p)
  extReads := fun x ρ => Q.extReads x (Rho.push σ ρ)
  reads    := fun x ρ pl =>
    (Q.reads x (Rho.push σ ρ) (Plains.push σ pl)).map (OPos.pushEquiv σ).symm.toEmbedding
  accept   := fun x y τ => Q.accept x y (Tr.push σ τ)

def Honest.pull {Q : InteractiveOracleProof X E} {Wt : Type} (H : Honest Q Wt) (σ : Samplers Q.shape) :
    Honest (Q.pull σ) Wt where
  Coin  := H.Coin
  ext   := H.ext
  strat := fun w x c => Strat.pull σ (H.strat w x c)
  Bad   := {ρ | Rho.push σ ρ ∈ H.Bad}
  Hid   := fun w x => {ρ | Rho.push σ ρ ∈ H.Hid w x}

/-- The samplers are good: every fibre has at most w elements; for each round w * card Chal ≤ κ *
card Src;
and the product of these ratios over all rounds is at most K. -/
def Samplers.Good : {s : Shape} → Samplers s → (κ K : ℝ≥0∞) → Prop
  | [], _, _, K => 1 ≤ K
  | r :: _, (σ, σs), κ, K =>
      (∀ c : r.Chal, cnt (fun a : σ.Src => σ.φ a = c) ≤ σ.w) ∧
      (σ.w : ℝ≥0∞) * (Fintype.card r.Chal : ℝ≥0∞) ≤ κ * (Fintype.card σ.Src : ℝ≥0∞) ∧
      ∃ K' : ℝ≥0∞, Samplers.Good σs κ K' ∧
        (σ.w : ℝ≥0∞) * (Fintype.card r.Chal : ℝ≥0∞) * K' ≤ K * (Fintype.card σ.Src : ℝ≥0∞)

/-- The numbers after the pull-back. -/
def LH.Nums.pull (N : LH.Nums) (κ K : ℝ≥0∞) : LH.Nums :=
  { N with
    εs := κ * N.εs, zT := K * N.zT, zL := K * N.zL, zO := K * N.zO, pT := K * N.pT,
    pL := K * N.pL, pO := K * N.pO }

end Iop
