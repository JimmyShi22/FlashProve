-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/Sub.lean: a transformation of interactive oracle reductions (IORs): the verifier draws from a
subset.

Definitions and statements; the proofs are in Ior/SubProofs.lean.
An IOR (`IOR`, Ior/Ior.lean) is an interactive oracle reduction: a protocol after whose rounds the
verifier rejects or outputs a new statement.

Why: the blocks of the vector floor draw challenges from all of a field, and their verifiers reject
a drawn 0 where somebody divides by the challenge; the honest side lists these values in its public
withheld set. A print of this protocol's technical report (lean/CREDITS.md) draws such
challenges from the field WITHOUT 0. Here: the passage from the one to the other, for any reduction,
all rounds at once; no block is touched.
The terms on shapes are those of Iop/Pull.lean, which pulls a shape back along one map φ : Src →
Chal for each round (`Samplers`, by recursion on the shape): `Shape.pull`, `Rho.push`, `Tr.push`,
`Plains.push`, `OPos.pushEquiv`, `Strat.pull` (`Plains.pull`, `OSym.pull`: Iop/PullProofs.lean). A
subset is the case "φ injective" (`Samplers.Inj`).

Main names:
  `Orcs.push` (Ior/OrcsPush.lean): the oracles of the new shape are those of the old one.
  `R.sub σ`, `H.sub σ`, `P.sub σ pBad pHid`: the reduction, its honest side, its numbers. The
    withheld sets are the preimages.
  `Spec.doomed_sub`: under `σ.Inj`, if the prover has lost in the old shape, it has lost in the new
    one, towards the same goal, with the same counts.
  `Spec.know_sub`: so, under the hypotheses of its statement, round-by-round knowledge soundness is
    kept: same relations, same extractor, same counts. (As fractions the errors grow: the same count
    over a smaller set.)
  `Spec.isLocal_sub`, `Spec.point_sub`, `Spec.acc_sub`, `Spec.exact_sub`, under the hypotheses of
    their statements: locality; strings; completeness and honest-verifier exact zero knowledge: both
    are statements for each value of the verifier's randomness, so they are kept for any maps φ; the
    simulator is that of R at the randomness pushed forward, the budget is read through the
    positions' bijection.
  `Spec.good_sub`: under `σ.Inj`, the bundle of Ior/Chain.lean is kept, with the two probabilities
    as new numbers: bounds on the probabilities of the preimages of the public withheld set and of
    the covers.
  `Spec.pr_sub_empty`: a set that no pushed value meets has a preimage of probability 0: if the
    public withheld set holds only values outside the subsets, nothing is withheld in public any
    more.
  `Spec.pr_sub_fst`, `Spec.pr_sub_snd`: an event on the first (second) of two shapes in a row has,
    after restriction of both, the probability that it has after restriction of its own shape alone:
    so, with `Spec.pr_sub_bij` and `Spec.bij_keep`, an event whose rounds are not restricted keeps
    its probability [no theorem here].

Limits: the verifier's test "reject this value" stays in the term `R.out`; `Spec.pr_sub_empty` says
when it never fires in this sense: a set that no pushed value meets has a preimage of probability 0
(the statement names no `R.out`). This file says nothing on how the verifier's message is made from
uniform bits (Iop/Pull.lean, Iop/Univ.lean: a further pull). It says nothing on batches.
Terms: lean/GLOSSARY.md: budget, bundle, cover, error, honest side, IOR, numbers (of a reduction),
round-by-round knowledge soundness, shape, string, the prover has lost, vector floor, withheld,
zero knowledge.
-/
import Ior.Chain
import Ior.OrcsPush
import Iop.PullProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-- The whole set of verifier messages. -/
def Sampler.all (r : Round) : Sampler r := ⟨r.Chal, by lazy_instance, id, 1⟩

/-- A nonempty subset of the verifier messages. -/
def Sampler.sub {r : Round} (P : r.Chal → Prop) [Fintype {c // P c}] [Nonempty {c // P c}] :
    Sampler r :=
  ⟨{c // P c}, by lazy_instance, Subtype.val, 1⟩

namespace Samplers

/-- Nothing is restricted. -/
def keep : (s : Shape) → Samplers s
  | [] => PUnit.unit
  | r :: s => (Sampler.all r, keep s)

/-- Two shapes in a row. -/
def app : {s t : Shape} → Samplers s → Samplers t → Samplers (s ++ t)
  | [], _, _, τ => τ
  | _ :: _, _, (a, σ), τ => (a, app σ τ)

/-- Every map is injective: the verifier draws from subsets. -/
def Inj : {s : Shape} → Samplers s → Prop
  | [], _ => True
  | _ :: _, (a, σ) => Function.Injective a.φ ∧ Inj σ

/-- Every map is bijective. -/
def Bij : {s : Shape} → Samplers s → Prop
  | [], _ => True
  | _ :: _, (a, σ) => Function.Bijective a.φ ∧ Bij σ

end Samplers

/-- The error list of the new shape: the same counts. -/
def Err.same : {s : Shape} → (σ : Samplers s) → Err s → Err (s.pull σ)
  | [], _, _ => ()
  | _ :: _, (_, σ), (e, ε) => (e, Err.same σ ε)

namespace IOR
variable {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type}

/-- R with its verifier messages drawn through σ. The verifier does what it did, on the transcript
pushed forward. -/
def sub (R : IOR Xi Ei Xo Eo) (σ : Samplers R.shape) : IOR Xi Ei Xo Eo where
  shape := R.shape.pull σ
  blinded p := R.blinded (OPos.pushEquiv σ p)
  extReads ρ := R.extReads (Rho.push σ ρ)
  reads ρ := (R.reads (Rho.push σ ρ)).map (OPos.pushEquiv σ).symm.toEmbedding
  out x y τ := R.out x y (Tr.push σ τ)
  imp y τ := R.imp y (Tr.push σ τ)
  srcE ρ q := R.srcE (Rho.push σ ρ) q
  srcO ρ q := (R.srcO (Rho.push σ ρ) q).map (OPos.pushEquiv σ).symm.toEmbedding
  tie ρ p := R.tie (Rho.push σ ρ) (OPos.pushEquiv σ p)

/-- Its honest side: same coins, same messages; the withheld sets are the preimages. -/
def Honest.sub {R : IOR Xi Ei Xo Eo} (H : R.Honest Wi Wo) (σ : Samplers R.shape) :
    (R.sub σ).Honest Wi Wo where
  Coin := H.Coin
  strat w x c := Strat.pull σ (H.strat w x c)
  Bad := {ρ | Rho.push σ ρ ∈ H.Bad}
  Hid w x := {ρ | Rho.push σ ρ ∈ H.Hid w x}

/-- Its numbers: the same counts; two new probabilities; budget and cover read through σ. -/
def Nums.sub {R : IOR Xi Ei Xo Eo} (P : Nums K R) (σ : Samplers R.shape) (pBad pHid : ℝ≥0∞) :
    Nums K (R.sub σ) where
  err  := Err.same σ P.err
  pBad := pBad
  pHid := pHid
  bud  := fun ρ T => P.bud (Rho.push σ ρ) (T.map (OPos.pushEquiv σ).toEmbedding)
  cov  := fun k => {ρ | Rho.push σ ρ ∈ P.cov k}

/-- What a run of R shows, written for the new shape. -/
def View.sub {R : IOR Xi Ei Xo Eo} (σ : Samplers R.shape) (V : View R) : View (R.sub σ) where
  plains := Plains.pull σ V.plains
  orc := fun p => (V.orc (OPos.pushEquiv σ p)).map (OSym.pull σ p)

/-- The simulator: that of R, at the verifier's randomness pushed forward. -/
def simSub {R : IOR Xi Ei Xo Eo} (σ : Samplers R.shape) (S : Honest.Sim R) :
    Honest.Sim (R.sub σ) :=
  fun x ρ T a =>
    (S x (Rho.push σ ρ) (T.map (OPos.pushEquiv σ).toEmbedding) a).map (Option.map (View.sub σ))

end IOR

namespace Spec
open IOR

/-- The bad values in a subset are among the bad values. -/
def doomed_sub : Prop :=
  ∀ (s : Shape) (σ : Samplers s) (ε : Err s) (bad : Tr s → Prop),
    σ.Inj → Doomed s ε bad → Doomed (s.pull σ) (Err.same σ ε) fun τ => bad (Tr.push σ τ)

/-- Under the hypotheses below, round-by-round knowledge soundness is kept, with the same counts. -/
def know_sub : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (σ : Samplers R.shape) (Wi Wo : Type)
      (on : Xi × Ei.Str → Prop) (RA : Xi × Ei.Str → Wi → Prop) (RB : Xo × Eo.Str → Wo → Prop)
      (ext : Ei.Str → Orcs R.shape → Wo → Wi) (ε : Err R.shape),
    σ.Inj → R.red.Know on RA RB (fun a τ w => ext a.2 τ.read w) ε →
    (R.sub σ).red.Know on RA RB (fun a τ w => ext a.2 (Orcs.push σ τ.read) w) (Err.same σ ε)

def isLocal_sub : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (σ : Samplers R.shape),
    R.IsLocal → (R.sub σ).IsLocal

def point_sub : Prop :=
  ∀ (s : Shape) (σ : Samplers s), Nonempty s.IsPoint → Nonempty (s.pull σ).IsPoint

def acc_sub : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (σ : Samplers R.shape) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (Ri : Xi → Ei.Str → Wi → Prop) (Ro : Xo → Eo.Str → Wo → Prop),
    H.Acc Ri Ro → (H.sub σ).Acc Ri Ro

/-- Under the hypotheses below, honest-verifier exact zero knowledge is kept, with the simulator
named. -/
def exact_sub : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (σ : Samplers R.shape) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (Ri : Xi → Ei.Str → Wi → Prop)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (S : Honest.Sim R),
    H.ExactWith Ri bud S →
    (H.sub σ).ExactWith Ri
      (fun ρ T => bud (Rho.push σ ρ) (T.map (OPos.pushEquiv σ).toEmbedding)) (simSub σ S)

/-- Under the hypotheses below, the bundle is kept. -/
def good_sub : Prop :=
  ∀ (K Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (σ : Samplers R.shape) (Wi Wo : Type)
      (H : R.Honest Wi Wo) (A : Rels K Xi Ei Wi) (B : Rels K Xo Eo Wo)
      (ext : Ei.Str → Orcs R.shape → Wo → Wi) (P : Nums K R) (pBad pHid : ℝ≥0∞),
    σ.Inj → prRho {ρ : Rho (R.shape.pull σ) | Rho.push σ ρ ∈ H.Bad} ≤ pBad →
    (∀ k, prRho {ρ : Rho (R.shape.pull σ) | Rho.push σ ρ ∈ P.cov k} ≤ pHid) → Good R H A B ext P →
    Good (R.sub σ) (H.sub σ) A B (fun y o w => ext y (Orcs.push σ o) w) (P.sub σ pBad pHid)

/-- A set that no pushed value meets. -/
def pr_sub_empty : Prop :=
  ∀ (s : Shape) (σ : Samplers s) (S : Set (Rho s)),
    (∀ ρ, Rho.push σ ρ ∉ S) → prRho {ρ : Rho (s.pull σ) | Rho.push σ ρ ∈ S} = 0

/-- Where every map is bijective, probabilities do not change. -/
def pr_sub_bij : Prop :=
  ∀ (s : Shape) (σ : Samplers s) (S : Set (Rho s)),
    σ.Bij → prRho {ρ : Rho (s.pull σ) | Rho.push σ ρ ∈ S} = prRho S

/-- An event on the first of two shapes in a row. -/
def pr_sub_fst : Prop :=
  ∀ (s t : Shape) (σ : Samplers s) (τ : Samplers t) (S : Set (Rho s)),
    prRho {ρ : Rho ((s ++ t).pull (σ.app τ)) | Rho.push (σ.app τ) ρ ∈ Rho.cylFst t S} =
      prRho {ρ : Rho (s.pull σ) | Rho.push σ ρ ∈ S}

/-- An event on the second. -/
def pr_sub_snd : Prop :=
  ∀ (s t : Shape) (σ : Samplers s) (τ : Samplers t) (S : Set (Rho t)),
    prRho {ρ : Rho ((s ++ t).pull (σ.app τ)) | Rho.push (σ.app τ) ρ ∈ Rho.cylSnd s S} =
      prRho {ρ : Rho (t.pull τ) | Rho.push τ ρ ∈ S}

def inj_app : Prop :=
  ∀ (s t : Shape) (σ : Samplers s) (τ : Samplers t), σ.Inj → τ.Inj → (σ.app τ).Inj
def inj_keep : Prop := ∀ s : Shape, (Samplers.keep s).Inj
def bij_keep : Prop := ∀ s : Shape, (Samplers.keep s).Bij

end Spec
end Iop
