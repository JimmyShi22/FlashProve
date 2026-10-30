-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/ToProto.lean: an interactive oracle reduction (IOR) to the trivial statement, read as an
interactive oracle proof (IOP; `IOR.toInteractiveOracleProof`, Ior/Ior.lean), and its honest side, read as an
honest side of Iop/InteractiveOracleProof.lean. An IOP with such an honest side is what the interface to the
compiler (`Iop.BatchProtocol`) holds as `offline` with `honestOfflineProver` and as `link` with `honestLinkProver`.

Definitions and statements; the proofs are in Ior/ToProtoProofs.lean.

An IOR (`IOR`, Ior/Ior.lean) is an interactive oracle reduction: a protocol after whose rounds the
verifier rejects or outputs a new statement.

Notions of Ior/Honest.lean, for an IOR R and its honest side H:
  `H.Bad`, `H.Hid`: fields of `IOR.Honest`, Ior/Honest.lean.
  Further positions T: `IOR.view`, Ior/Honest.lean.
  `H.ExactWith Ri bud S`: for every (x, y, w) in Ri, every ρ outside `H.Hid w x` and every T with
    `bud ρ T`, the distribution `H.output w x ρ T` equals `S x ρ T a`, where a gives the symbols
    of y at the positions `R.given ρ T` and `none` at the others. `Exact` says that some S does.
    Here `H.Exact Ri bud` is a premise, of `Spec.hvzk_toProto` ("the exact form" in its doc
    comment). The conclusion, `Honest.HVZK` (Iop/InteractiveOracleProof.lean; "the compiler's form"), is of a
    `InteractiveOracleProof`: what stands above is not said of it.

Main names:
  `Spec.sound_toProto`: from knowledge soundness of the IOR to round-by-round soundness of the
    IOP: see its doc comment.
  `Spec.acc_toProto`: states: if the IOR's honest side is pointwise complete (`Acc`, to the
    relation `triv`), and `valid w x` implies that x, `ext w` and `inp w x` are in the IOR's
    relation, then the IOP's honest side is pointwise complete on `valid`.
  `Spec.hvzk_toProto`: see its statement.

Terms: lean/GLOSSARY.md.
-/
import Ior.Honest
import Ior.Know

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {X Wt Wi : Type} {E : ExtSpec}

/-- The honest side of the IOP. Wt is the private input of the interface. `ext w`: the external
oracles that belong to it. `inp w x`: the witness that the honest prover uses for x. -/
def Honest.toProto {R : IOR X E Unit extNone} (H : R.Honest Wi Unit)
    (ext : Wt → E.Str) (inp : Wt → X → Wi) : Iop.Honest R.toInteractiveOracleProof Wt where
  Coin := H.Coin
  ext := ext
  strat := fun w x c => Strat.map (fun _ => ()) (H.strat (inp w x) x c)
  Bad := H.Bad
  Hid := fun w x => H.Hid (inp w x) x

/-- the trivial relation on the trivial statement -/
def triv : Unit → extNone.Str → Unit → Prop := fun _ _ _ => True

end IOR

namespace Spec
open IOR

/-- States: knowledge soundness of an IOR to the trivial statement gives round-by-round soundness
of the IOP for the language of the relation, together with all statements outside `on`. -/
def sound_toProto : Prop :=
  ∀ (X W : Type) (E : ExtSpec) (R : IOR X E Unit extNone) (on : X × E.Str → Prop)
      (RA : X × E.Str → W → Prop) (ext : X × E.Str → Tr R.shape → Unit → W) (ε : Err R.shape),
    R.red.Know on RA (fun _ _ => True) ext ε →
    R.toInteractiveOracleProof.Sound (fun x y => ¬ on (x, y) ∨ ∃ w, RA (x, y) w) ε

def acc_toProto : Prop :=
  ∀ (X Wt Wi : Type) (E : ExtSpec) (R : IOR X E Unit extNone) (H : R.Honest Wi Unit)
      (ext : Wt → E.Str) (inp : Wt → X → Wi) (valid : Wt → X → Prop) (Ri : X → E.Str → Wi → Prop),
    H.Acc Ri triv → (∀ w x, valid w x → Ri x (ext w) (inp w x)) → (H.toProto ext inp).Acc valid

open Classical in
/-- States, under the hypotheses below: if the verifier itself reads all that is tied to its
positions, and the budget bears its positions (`bud ρ ∅` for every ρ), then the exact form of the
IOR's honest side (`H.Exact Ri bud`; `Honest.Exact`, Ior/Honest.lean) gives the compiler's form of
the IOP's honest side (`HVZK valid z`; `Honest.HVZK`, Iop/InteractiveOracleProof.lean). Not all hypotheses are
named here: see the statement below. -/
def hvzk_toProto : Prop :=
  ∀ (X Wt Wi : Type) (E : ExtSpec) (R : IOR X E Unit extNone) (H : R.Honest Wi Unit)
      (ext : Wt → E.Str) (inp : Wt → X → Wi) (valid : Wt → X → Prop) (Ri : X → E.Str → Wi → Prop)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop) (z : ℝ≥0∞),
    H.Exact Ri bud → (∀ ρ, bud ρ ∅) → (∀ ρ, (R.reads ρ).biUnion (R.tie ρ) ⊆ R.extReads ρ) →
    (∀ w x, valid w x → Ri x (ext w) (inp w x)) →
    (∀ w x, valid w x → prRho (H.Hid (inp w x) x) ≤ z) → (H.toProto ext inp).HVZK valid z

end Spec
end Iop
