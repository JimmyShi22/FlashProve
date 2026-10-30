-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/Ior.lean: interactive oracle reductions (IORs) of fixed shape: the data, locality, sequential
composition, conversion to the IOPs of Iop/InteractiveOracleProof.lean.

Terms and definitions only. The three statements in `Iop.Spec` are proved in Ior/SeqProofs.lean.

A shape (`Shape`, Iop/Shape.lean) is the list of a protocol's rounds: in each a prover message (an
oracle part and a plain part), then a verifier message.
What an IOR is here: a statement has an explicit part x : Xi, which the verifier holds, and an
implicit part y : Ei.Str, oracles that it reads by queries (`ExtSpec`). After the rounds of the
shape the verifier reads y and the prover's oracles at positions that are a function of its own
randomness alone (`extReads`, `reads`), and rejects or outputs a new explicit part (`out`). The new
implicit part (`imp`) is given in terms of y and the prover's oracles: its symbol at the position q
is computed from the symbols of y at srcE ρ q and of the prover's oracles at srcO ρ q (a copy: one
position; a fold: several); that `out` and `imp` read the oracles only at the positions declared is
the property `IsLocal`, which lets both depend on ρ and the plain parts too.
"tie ρ p": the positions of y whose symbols a symbol of the prover's oracle at p gives away together
with the plain parts (a mask row that is sent as an oracle while the masked combination is sent in
full) (data: see `given`, Ior/Honest.lean). It is read by zero knowledge alone (Ior/Honest.lean).
The structure `IOR` holds data only; the properties are separate (as in Iop/InteractiveOracleProof.lean).

Limits: running times and the succinctness of anything are not modelled in this file.
Terms: lean/GLOSSARY.md.
-/
import Iop.Compose
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob

/-- No oracle. -/
abbrev extNone : ExtSpec := ⟨Unit, Empty, Unit, fun _ _ => ()⟩

/-- Two kinds of oracles side by side. -/
abbrev ExtSpec.prod (E₁ E₂ : ExtSpec) : ExtSpec :=
  ⟨E₁.Str × E₂.Str, E₁.Pos ⊕ E₂.Pos, E₁.Sym ⊕ E₂.Sym, fun y p => match p with
    | .inl p => .inl (E₁.rd y.1 p)
    | .inr p => .inr (E₂.rd y.2 p)⟩

open Classical in
/-- What oracles hold on a set of positions, and nothing else. -/
def ExtSpec.ans (E : ExtSpec) (U : Finset E.Pos) (y : E.Str) : E.Pos → Option E.Sym :=
  fun p => if p ∈ U then some (E.rd y p) else none

/-- An interactive oracle reduction of fixed shape: the data. -/
structure IOR (Xi : Type) (Ei : ExtSpec) (Xo : Type) (Eo : ExtSpec) where
  shape    : Shape
  /-- is the oracle at this position blinded (never shown in full) (by type any map
  `OPos shape → Bool`; it enters `view`, Ior/Honest.lean) -/
  blinded  : OPos shape → Bool
  /-- the positions that the verifier reads in the implicit instance, and in the prover's oracles -/
  extReads : Rho shape → Finset Ei.Pos
  reads    : Rho shape → Finset (OPos shape)
  /-- the verifier: none = reject -/
  out      : Xi → Ei.Str → Tr shape → Option Xo
  /-- the new implicit instance -/
  imp      : Ei.Str → Tr shape → Eo.Str
  /-- from which symbols a symbol of the new implicit instance is computed -/
  srcE     : Rho shape → Eo.Pos → Finset Ei.Pos
  srcO     : Rho shape → Eo.Pos → Finset (OPos shape)
  /-- which symbols of the implicit instance a symbol of a prover's oracle gives away (by type any
  map from ρ and a position to a finite set of positions; it enters `given`, Ior/Honest.lean) -/
  tie      : Rho shape → OPos shape → Finset Ei.Pos

namespace IOR
variable {X₁ X₂ X₃ Xi Xo X : Type} {E₁ E₂ E₃ Ei Eo E : ExtSpec}

/-- The verifier's output and the symbols of the new implicit instance depend on the oracles only at
the positions declared. -/
structure IsLocal (R : IOR Xi Ei Xo Eo) : Prop where
  out : ∀ x y y' (τ τ' : Tr R.shape), τ.rho = τ'.rho → τ.plains = τ'.plains → (∀ p ∈ R.extReads τ.rho, Ei.rd y p = Ei.rd y' p) →
      (∀ p ∈ R.reads τ.rho, τ.read p = τ'.read p) → R.out x y τ = R.out x y' τ'
  imp : ∀ y y' (τ τ' : Tr R.shape) q, τ.rho = τ'.rho → τ.plains = τ'.plains → (∀ p ∈ R.srcE τ.rho q, Ei.rd y p = Ei.rd y' p) →
      (∀ p ∈ R.srcO τ.rho q, τ.read p = τ'.read p) → Eo.rd (R.imp y τ) q = Eo.rd (R.imp y' τ') q

/-- An IOR as a reduction between statements (x, y): what soundness and knowledge soundness speak
of. -/
@[reducible] def red (R : IOR Xi Ei Xo Eo) : Reduction (Xi × Ei.Str) (Xo × Eo.Str) where
  shape := R.shape
  out a τ := (R.out a.1 a.2 τ).map fun xo => (xo, R.imp a.2 τ)

open Classical in
/-- The first IOR, then the second on its output. If the first verifier rejects, the rounds of the
second are still played. -/
def seq (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃) : IOR X₁ E₁ X₃ E₃ where
  shape := R₁.shape ++ R₂.shape
  blinded p := match OPos.split (s := R₁.shape) p with
    | .inl p => R₁.blinded p
    | .inr p => R₂.blinded p
  extReads ρ := R₁.extReads (Rho.fst ρ) ∪
    (R₂.extReads (Rho.snd (s := R₁.shape) ρ)).biUnion (R₁.srcE (Rho.fst ρ))
  reads ρ := (R₁.reads (Rho.fst ρ) ∪
        (R₂.extReads (Rho.snd (s := R₁.shape) ρ)).biUnion (R₁.srcO (Rho.fst ρ))).image OPos.left ∪
    (R₂.reads (Rho.snd (s := R₁.shape) ρ)).image (OPos.right (s := R₁.shape))
  out x y τ := (R₁.out x y (Tr.fst τ)).bind fun x₂ =>
    R₂.out x₂ (R₁.imp y (Tr.fst τ)) (Tr.snd (s := R₁.shape) τ)
  imp y τ := R₂.imp (R₁.imp y (Tr.fst τ)) (Tr.snd (s := R₁.shape) τ)
  srcE ρ q := (R₂.srcE (Rho.snd (s := R₁.shape) ρ) q).biUnion (R₁.srcE (Rho.fst ρ))
  srcO ρ q := ((R₂.srcE (Rho.snd (s := R₁.shape) ρ) q).biUnion (R₁.srcO (Rho.fst ρ))).image
      OPos.left ∪
    (R₂.srcO (Rho.snd (s := R₁.shape) ρ) q).image (OPos.right (s := R₁.shape))
  tie ρ p := match OPos.split (s := R₁.shape) p with
    | .inl p => R₁.tie (Rho.fst ρ) p
    | .inr p => (R₂.tie (Rho.snd (s := R₁.shape) ρ) p).biUnion (R₁.srcE (Rho.fst ρ))
        ∪ ((R₂.tie (Rho.snd (s := R₁.shape) ρ) p).biUnion (R₁.srcO (Rho.fst ρ))).biUnion (R₁.tie (Rho.fst ρ))

/-- An IOR to the trivial statement is an IOP in the sense of Iop/InteractiveOracleProof.lean. -/
def toInteractiveOracleProof (R : IOR X E Unit extNone) : InteractiveOracleProof X E where
  shape := R.shape
  blinded := R.blinded
  extReads := fun _ ρ => R.extReads ρ
  reads := fun _ ρ _ => R.reads ρ
  accept := fun x y τ => (R.out x y τ).isSome

end IOR

namespace Spec

/-- States: locality is kept by composition. -/
def isLocal_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃),
    R₁.IsLocal → R₂.IsLocal → (R₁.seq R₂).IsLocal

/-- States: an IOR that is local gives an IOP that is local. -/
def isLocal_toProto : Prop :=
  ∀ (X : Type) (E : ExtSpec) (R : IOR X E Unit extNone), R.IsLocal → R.toInteractiveOracleProof.IsLocal

/-- States: the reduction of a composition is the composition of the reductions. -/
def red_seq : Prop :=
  ∀ (X₁ X₂ X₃ : Type) (E₁ E₂ E₃ : ExtSpec) (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
      (a : X₁ × E₁.Str) (τ : Tr (R₁.shape ++ R₂.shape)),
    (R₁.seq R₂).red.out a τ = (R₁.red.seq R₂.red).out a τ

end Spec
end Iop
