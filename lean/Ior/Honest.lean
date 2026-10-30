-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/Honest.lean: the honest side of an IOR: pointwise completeness, and honest-verifier
zero knowledge in the exact form, with further reads.

Definitions, and the statements of the composition rules. `Spec.acc_seq` is proved in
Ior/SeqProofs.lean, `Spec.exact_seq` in Ior/ExactSeq.lean, `Spec.stat_of_exact` in Ior/Stat.lean.
An IOR (`IOR`, Ior/Ior.lean) is an interactive oracle reduction: a protocol after whose rounds the
verifier rejects or outputs a new statement.
`R.tie ρ p` is a finite set of positions of the implicit instance, for each ρ and each position p of
the prover's oracles; it enters `R.given`.

Completeness (`Acc`), as in Iop/InteractiveOracleProof.lean: for every input in the relation, at every value ρ of the
verifier's randomness outside the withheld set Bad ∪ Hid w x, for all coins, the verifier outputs
the explicit part with which the honest prover ends, and the output statement with the prover's new
witness is in the output relation. The completeness error is the probability of the withheld set.
Bad is public (no argument but ρ); Hid may read the witness.

Zero knowledge (`Exact`). The notion of a print of this protocol's technical report
(lean/CREDITS.md) compares two random variables up to a statistical distance, for distinguishers
that read every oracle at further uniform positions.
Here: one simulator;
   it is given x, ρ, a set T of further positions in the prover's oracles, and the symbols of the
     implicit instance at the positions `given ρ T`, and nothing else (a fact about its type);
   for every input in the relation, at every ρ outside Hid w x and every T within the budget, its
     output has exactly the law (over the prover's coins) of what the honest run shows (`view`) at
     the verifier's positions and at T, or the notice (`none`) if ρ is withheld.
   The zero-knowledge error is the probability of Hid w x.
Reasons:
   (1) the compiler (Compile/) takes this form (`Iop.Honest.HVZK`, `Iop.BatchHonestProver.HVZK`);
   (2) under the hypotheses of `Spec.exact_seq`, at the composed budget, it composes by function
     composition, with no classes of distinguishers: the further reads of a later verifier, of a
     simulator or of a distinguisher are all "a set T";
   (3) it implies the statistical notion for every way of choosing T from ρ and coins of its own,
     within the budget, that does not depend on the prover's coins (`Spec.stat_of_exact`). It is the
     stronger demand on a block.
"bud ρ T": the budget: which sets T (together with the verifier's own positions at ρ) the encodings
of the prover's oracles bear. It is a parameter of the property.
The honest prover ends with (xo, wo): the explicit part that it expects the verifier to output, and
its witness for the output statement. What it sends on the withheld set is not constrained in this
file.
Terms: lean/GLOSSARY.md.
-/
import Ior.Ior
import Iop.ViewKit
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {X₁ X₂ X₃ Xi Xo X : Type} {E₁ E₂ E₃ Ei Eo E : ExtSpec}

/-- The honest side of an IOR: the data. Wi, Wo are the witnesses of the input and of the output
relation. -/
structure Honest (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) where
  Coin  : Type
  [finCoin : Fintype Coin]
  [neCoin  : Nonempty Coin]
  strat : Wi → Xi → Coin → Strat R.shape (Xo × Wo)
  /-- the public bad set -/
  Bad   : Set (Rho R.shape)
  /-- the rest of the withheld set; it may read the witness -/
  Hid   : Wi → Xi → Set (Rho R.shape)

attribute [instance] Honest.finCoin Honest.neCoin

/-- What a run shows: the plain parts, and symbols of the prover's oracles. -/
structure View (R : IOR Xi Ei Xo Eo) where
  plains : Plains R.shape
  orc    : (p : OPos R.shape) → Option (OSym R.shape p)

open Classical in
/-- The plain parts, the symbols at the verifier's positions and at T, and every unblinded oracle in
full. -/
def view (R : IOR Xi Ei Xo Eo) (T : Finset (OPos R.shape)) (τ : Tr R.shape) :
    View R where
  plains := τ.plains
  orc := fun p => if p ∈ R.reads τ.rho ∨ p ∈ T ∨ R.blinded p = false then some (τ.read p) else none

open Classical in
/-- The positions of the implicit instance whose symbols the simulator is given: the verifier's, and
those tied to the verifier's positions in the prover's oracles and to T. -/
def given (R : IOR Xi Ei Xo Eo) (ρ : Rho R.shape) (T : Finset (OPos R.shape)) :
    Finset Ei.Pos :=
  R.extReads ρ ∪ (R.reads ρ ∪ T).biUnion (R.tie ρ)

namespace Honest
variable {R : IOR Xi Ei Xo Eo} {Wi Wo : Type}

def withheld (H : R.Honest Wi Wo) (w : Wi) (x : Xi) : Set (Rho R.shape) := H.Bad ∪ H.Hid w x

/-- Pointwise completeness from the relation Ri to the relation Ro. -/
def Acc (H : R.Honest Wi Wo) (Ri : Xi → Ei.Str → Wi → Prop) (Ro : Xo → Eo.Str → Wo → Prop) : Prop :=
  ∀ x y w c ρ, Ri x y w → ρ ∉ H.withheld w x →
    R.out x y ((H.strat w x c).run ρ).1 = some ((H.strat w x c).run ρ).2.1 ∧
    Ro ((H.strat w x c).run ρ).2.1 (R.imp y ((H.strat w x c).run ρ).1) ((H.strat w x c).run ρ).2.2

open Classical in
/-- The output at ρ with the further positions T: what the run shows, or the notice (`none`) if ρ is
withheld. A random variable over the prover's coins. -/
def output (H : R.Honest Wi Wo) (w : Wi) (x : Xi)
    (ρ : Rho R.shape) (T : Finset (OPos R.shape)) : PMF (Option (View R)) :=
  if ρ ∈ H.withheld w x then PMF.pure none
  else (unif H.Coin).map fun c => some (R.view T ((H.strat w x c).run ρ).1)

/-- The type of a simulator. -/
abbrev Sim (R : IOR Xi Ei Xo Eo) : Type :=
  Xi → (ρ : Rho R.shape) → Finset (OPos R.shape) → (Ei.Pos → Option Ei.Sym) → PMF (Option (View R))

/-- Honest-verifier zero knowledge, exact form, with the simulator named. -/
def ExactWith (H : R.Honest Wi Wo) (Ri : Xi → Ei.Str → Wi → Prop)
    (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (S : Sim R) : Prop :=
  ∀ x y w, Ri x y w →
    ∀ ρ, ρ ∉ H.Hid w x → ∀ T, bud ρ T → H.output w x ρ T = S x ρ T (Ei.ans (R.given ρ T) y)

def Exact (H : R.Honest Wi Wo) (Ri : Xi → Ei.Str → Wi → Prop)
    (bud : Rho R.shape → Finset (OPos R.shape) → Prop) : Prop :=
  ∃ S : Sim R, H.ExactWith Ri bud S

end Honest

/-! ### Composition -/

/-- The honest side of a composition. The coins are independent. The withheld set: ρ₁ is withheld by
the first, or ρ₂ is withheld by the second on what the first hands on, for some coins of the first.
In Hid the second half counts only where ρ₁ is outside the first's public bad set: there the whole
is withheld anyway, and what the first hands on is not constrained in this file. -/
def Honest.seq {R₁ : IOR X₁ E₁ X₂ E₂} {R₂ : IOR X₂ E₂ X₃ E₃} {W₁ W₂ W₃ : Type}
    (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) : (R₁.seq R₂).Honest W₁ W₃ where
  Coin := H₁.Coin × H₂.Coin
  strat := fun w x c => Strat.bind (H₁.strat w x c.1) fun o => H₂.strat o.2 o.1 c.2
  Bad := Rho.cylFst R₂.shape H₁.Bad ∪ Rho.cylSnd R₁.shape H₂.Bad
  Hid := fun w x => Rho.cylFst R₂.shape (H₁.Hid w x) ∪
    {ρ : Rho (R₁.shape ++ R₂.shape) | Rho.fst ρ ∉ H₁.Bad ∧ ∃ c, Rho.snd (s := R₁.shape) ρ ∈ H₂.Hid ((H₁.strat w x c).run (Rho.fst ρ)).2.2 ((H₁.strat w x c).run (Rho.fst ρ)).2.1}


open Classical in
/-- The budget of a composition. T₁, T₂ are the parts of T in the two protocols. The second bears
T₂; the first bears T₁ together with all that the second verifier reads of the first's oracles and
all that is tied to the second verifier's positions in the prover's oracles and to T₂. -/
def budSeq (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
    (b₁ : Rho R₁.shape → Finset (OPos R₁.shape) → Prop)
    (b₂ : Rho R₂.shape → Finset (OPos R₂.shape) → Prop) :
    Rho (R₁.shape ++ R₂.shape) → Finset (OPos (R₁.shape ++ R₂.shape)) → Prop := fun ρ T =>
  ∀ (T₁ : Finset (OPos R₁.shape)) (T₂ : Finset (OPos R₂.shape)),
    (∀ p, p ∈ T₁ ↔ OPos.left p ∈ T) → (∀ p, p ∈ T₂ ↔ OPos.right (s := R₁.shape) p ∈ T) →
    b₂ (Rho.snd (s := R₁.shape) ρ) T₂ ∧ b₁ (Rho.fst ρ) (T₁ ∪ (R₂.given (Rho.snd (s := R₁.shape) ρ) T₂).biUnion (R₁.srcO (Rho.fst ρ)))

end IOR

namespace Spec
open IOR

/-- States: completeness composes. -/
def acc_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (Ra : X₁ → E₁.Str → W₁ → Prop)
      (Rb : X₂ → E₂.Str → W₂ → Prop) (Rc : X₃ → E₃.Str → W₃ → Prop),
    H₁.Acc Ra Rb → H₂.Acc Rb Rc → (H₁.seq H₂).Acc Ra Rc

/-- States: honest-verifier zero knowledge composes: exact simulation of both, completeness and
locality of the first, give exact simulation of the composition at the composed budget. Locality
(`IOR.IsLocal`, Ior/Ior.lean): the verifier's output and the symbols of the new implicit instance
depend on the oracles only at the positions declared. -/
def exact_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃) (Ra : X₁ → E₁.Str → W₁ → Prop)
      (Rb : X₂ → E₂.Str → W₂ → Prop) (b₁ : Rho R₁.shape → Finset (OPos R₁.shape) → Prop)
      (b₂ : Rho R₂.shape → Finset (OPos R₂.shape) → Prop),
    R₁.IsLocal → H₁.Acc Ra Rb → H₁.Exact Ra b₁ → H₂.Exact Rb b₂ →
    (H₁.seq H₂).Exact Ra (budSeq R₁ R₂ b₁ b₂)

/-- States, under the hypotheses below: the exact form gives the statistical form: for every law of
(ρ uniform, T chosen from ρ and coins of its own, within the budget), the pair (ρ, T, output) of the
honest run and that of the simulator are within the probability of Hid. -/
def stat_of_exact : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (Wi Wo : Type) (H : R.Honest Wi Wo)
      (Ri : Xi → Ei.Str → Wi → Prop) (bud : Rho R.shape → Finset (OPos R.shape) → Prop)
      (S : Honest.Sim R) (z : ℝ≥0∞),
    H.ExactWith Ri bud S →
    ∀ x y w, Ri x y w → prRho (H.Hid w x) ≤ z →
      ∀ D : Rho R.shape → PMF (Finset (OPos R.shape)), (∀ ρ T, T ∈ (D ρ).support → bud ρ T) →
        tv ((unif (Rho R.shape)).bind fun ρ =>
              (D ρ).bind fun T => (H.output w x ρ T).map fun o => (ρ, T, o))
            ((unif (Rho R.shape)).bind fun ρ =>
              (D ρ).bind fun T => (S x ρ T (Ei.ans (R.given ρ T) y)).map fun o => (ρ, T, o)) ≤ z

end Spec
end Iop
