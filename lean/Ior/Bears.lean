-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/Bears.lean: what a chain of IORs needs of its oracles: which positions of the input's implicit
part have to be known, and which budgets have to be borne, so that the whole chain is simulated.
The file is about the sequential composition of many interactive oracle reductions (IORs):
book-keeping of oracle positions.

Definitions and statements; the proofs are in Ior/BearsProofs.lean.
An IOR (`IOR`, Ior/Ior.lean) is an interactive oracle reduction: a protocol after whose rounds the
verifier rejects or outputs a new statement. A statement has an explicit part, held by the verifier,
and an implicit part: oracles that it queries.
`R.tie ρ p` is a finite set of positions of the implicit instance, for each ρ and each position p of
the prover's oracles; it enters `R.given`. `R.given ρ T` is the set of positions of the implicit
instance that the verifier reads at ρ, together with `R.tie ρ p` for every p that the verifier reads
in the prover's oracles or that is in T.

Why: the budget of a composition (`budSeq`, Ior/Honest.lean) is nested: the first bears
 (1) what the second verifier reads of its oracles and
 (2) what is tied to the second verifier's positions in the prover's oracles and to T₂ (the part, in
     the second protocol, of the set T of further positions),
and so on. For a chain of many IORs one wants one invariant for each link.

Main names:
  `need`: let what follows R need the symbols of R's new implicit instance at the set U of
    positions. `R.need ρ U` is the set of positions of R's old implicit instance that are then
    needed: what R's own simulator is given when it also has to show the sources of U in R's
    oracles, and the sources of U in the old implicit instance. For a composition, need is the
    composition of the two (`Spec.need_seq`): an equation, no inclusion.
  `Bears`: `R.Bears bud qi qo`: whenever the set U is within qo, R's budget bears the sources of U
    in R's oracles, and `R.need ρ U` is within qi. (qi, qo: predicates on sets of positions; say "at
    most q a positions in component a".)
    It composes (`Spec.bears_seq`), with the composed budget.
    Under the hypotheses of its statement, at the end of a chain, at U = ∅: the budget holds at no
    further reads, and what the simulator is given is within qi (`Spec.bears_end`).
  Also here, for chains, kept by composition:
    nothing hidden is withheld (`noHid_seq`);
    no oracle gives anything away in this sense: `∀ ρ p, R.tie ρ p = ∅` (`noTie_seq`) (data: see
      `given`, Ior/Honest.lean);
    the verifier reads all that is tied to its positions (`IOR.Tied`, `tied_seq`: the first ties
      nothing);
    the last two also for a step without rounds before R (`noTie_pre`, `tied_pre`).

Notation:
  `ρ : Rho R.shape`: "the verifier's randomness of a whole execution" (`Rho`, Iop/Shape.lean).
  `bud : Rho R.shape → Finset (OPos R.shape) → Prop`: a predicate on the verifier's randomness ρ and
    a set T of further positions.
  `R.srcO ρ q`, `R.srcE ρ q` (Ior/Ior.lean), the sources of q: the positions of the prover's
    oracles, and of the old implicit instance, from whose symbols the symbol at q of the new
    implicit instance is computed (data; the condition: `IOR.IsLocal`, Ior/Ior.lean).
  `H.Hid : Wi → Xi → Set (Rho R.shape)`: a field of `IOR.Honest` (Ior/Honest.lean).

Limits: further reads by a distinguisher (a set T beside the sources of U) are not in `Bears`.
Terms: lean/GLOSSARY.md.
-/
import Ior.Frame
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {Xi Xo : Type} {Ei Eo : ExtSpec}

open Classical in
/-- The positions of the old implicit instance that are needed when what follows needs the new one
at U. -/
def need (R : IOR Xi Ei Xo Eo) (ρ : Rho R.shape) (U : Finset Eo.Pos) :
    Finset Ei.Pos :=
  R.given ρ (U.biUnion (R.srcO ρ)) ∪ U.biUnion (R.srcE ρ)

open Classical in
/-- R bears what follows: for U within qo the budget bears the sources of U, and what is needed of
the old implicit instance is within qi. -/
def Bears (R : IOR Xi Ei Xo Eo) (bud : Rho R.shape → Finset (OPos R.shape) → Prop)
    (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop) : Prop :=
  ∀ ρ U, qo U → bud ρ (U.biUnion (R.srcO ρ)) ∧ qi (R.need ρ U)

end IOR

namespace Spec
open IOR

open Classical in
/-- `need` of a composition is the composition of the needs. -/
def need_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (ρ : Rho (R₁.shape ++ R₂.shape)) (U : Finset E₃.Pos),
    (R₁.seq R₂).need ρ U = R₁.need (Rho.fst ρ) (R₂.need (Rho.snd (s := R₁.shape) ρ) U)

/-- Bearing composes, at the composed budget. -/
def bears_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (b₁ : Rho R₁.shape → Finset (OPos R₁.shape) → Prop)
      (b₂ : Rho R₂.shape → Finset (OPos R₂.shape) → Prop) (qa : Finset E₁.Pos → Prop)
      (qb : Finset E₂.Pos → Prop) (qc : Finset E₃.Pos → Prop),
    R₁.Bears b₁ qa qb → R₂.Bears b₂ qb qc → (R₁.seq R₂).Bears (budSeq R₁ R₂ b₁ b₂) qa qc

/-- Weaker demands. -/
def bears_mono : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo)
      (bud bud' : Rho R.shape → Finset (OPos R.shape) → Prop)
      (qi qi' : Finset Ei.Pos → Prop) (qo qo' : Finset Eo.Pos → Prop),
    R.Bears bud qi qo → (∀ ρ T, bud ρ T → bud' ρ T) → (∀ S, qi S → qi' S) →
    (∀ U, qo' U → qo U) → R.Bears bud' qi' qo'

open Classical in
/-- A step without rounds before R: the needed positions are the sources, under the step's map, of
those that R needs. -/
def bears_pre : Prop :=
  ∀ (Xi Xi' Xo : Type) (Ei Ei' Eo : ExtSpec) (R : IOR Xi Ei Xo Eo) (f : Xi' → Option Xi)
      (g : ExtMap Ei' Ei) (bud : Rho R.shape → Finset (OPos R.shape) → Prop)
      (qi : Finset Ei.Pos → Prop) (qi' : Finset Ei'.Pos → Prop) (qo : Finset Eo.Pos → Prop),
    R.Bears bud qi qo → (∀ S, qi S → qi' (S.biUnion g.src)) → (R.pre f g).Bears bud qi' qo

/-- Under the hypotheses below, at the end of a chain: the budget holds at no further reads, and
what the simulator is given is within qi. -/
def bears_end : Prop :=
  ∀ (Xi Xo : Type) (Ei Eo : ExtSpec) (R : IOR Xi Ei Xo Eo)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop)
      (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop),
    R.Bears bud qi qo → qo ∅ → ∀ ρ, bud ρ ∅ ∧ qi (R.given ρ ∅)

/-- Nothing hidden is withheld: kept by composition. -/
def noHid_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (W₁ W₂ W₃ : Type) (H₁ : R₁.Honest W₁ W₂) (H₂ : R₂.Honest W₂ W₃),
    (∀ w x, H₁.Hid w x = ∅) → (∀ w x, H₂.Hid w x = ∅) → ∀ w x, (H₁.seq H₂).Hid w x = ∅

/-- No oracle gives anything away in this sense: `∀ ρ p, R.tie ρ p = ∅`: kept by composition and by
a step before R. (data: see `given`, Ior/Honest.lean) -/
def noTie_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃),
    (∀ ρ p, R₁.tie ρ p = ∅) → (∀ ρ p, R₂.tie ρ p = ∅) → ∀ ρ p, (R₁.seq R₂).tie ρ p = ∅

def noTie_pre : Prop :=
  ∀ (Xi Xi' Xo : Type) (Ei Ei' Eo : ExtSpec) (R : IOR Xi Ei Xo Eo)
      (f : Xi' → Option Xi) (g : ExtMap Ei' Ei),
    (∀ ρ p, R.tie ρ p = ∅) → ∀ ρ p, (R.pre f g).tie ρ p = ∅

/-- The verifier reads all that is tied to its positions: kept if an IOR that ties nothing comes
first, and by a step before R. -/
def tied_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃),
    (∀ ρ p, R₁.tie ρ p = ∅) → R₂.Tied → (R₁.seq R₂).Tied

def tied_pre : Prop :=
  ∀ (Xi Xi' Xo : Type) (Ei Ei' Eo : ExtSpec) (R : IOR Xi Ei Xo Eo)
      (f : Xi' → Option Xi) (g : ExtMap Ei' Ei),
    R.Tied → (R.pre f g).Tied

end Spec
end Iop
