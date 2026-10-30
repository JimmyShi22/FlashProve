-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tower/Seal.lean: the kind of block SEAL (in a plan of rounds: "SEAL", one round at the end of
a chain): the prover sends nothing, the verifier draws nothing, nothing is checked, the statement
and its oracles stay. General in the statement, its oracles and the joint.

The typed reduction is the library's one-round reduction `IOR.draw` (Ior/Draw.lean) at a set of one
value. Both joints are the same joint A, any; the extractor is the identity; the error is 0.

Main names:
  `sealR X Ex`: the reduction. `sealExt`, `sealErr`: the identity; the error 0.
  `SealKnow A`: the statement: round-by-round knowledge soundness from A to A, and nothing else.
  `seal_know`: it holds without any premise.
  Beside it, without any premise: `seal_point`, `seal_local`, `seal_onOut`; `seal_out` (the verifier
  never rejects and hands the statement on), `seal_imp` (the oracles stay); `seal_shape`,
  `seal_rounds`, `sealErr_toList`, `seal_vals`: one round, the error 0, one value.

Limits: the block says nothing on what the round's hash binds in the compiled scheme: it is a round
without content. Nothing on an honest prover.


Terms: lean/GLOSSARY.md.
-/
import Ior.Draw
import Ior.KnowCollRulesChainErr

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tower
open Iop Prob IOR

section
variable (X : Type) (Ex : ExtSpec)

/-- SEAL. -/
def sealR : IOR X Ex X Ex := IOR.draw Unit (fun x _ => x) Ex

/-- its one round: nothing | nothing -/
theorem seal_shape : (sealR X Ex).shape = [Blocks.plainRound Unit Unit ()] := rfl

/-- the verifier never rejects and hands the statement on -/
theorem seal_out (x : X) (y : Ex.Str) (τ : Tr (sealR X Ex).shape) :
    (sealR X Ex).out x y τ = some x := rfl

/-- the oracles stay -/
theorem seal_imp (y : Ex.Str) (τ : Tr (sealR X Ex).shape) : (sealR X Ex).imp y τ = y := rfl

/-- the error, as a count of verifier's messages -/
def sealErr : Err (sealR X Ex).shape := ((0, ()) : ℕ × Unit)

theorem sealErr_toList : Err.toList (sealErr X Ex) = [0] := rfl

theorem seal_rounds : (sealR X Ex).shape.length = 1 := rfl

/-- the verifier's one message has one value -/
theorem seal_vals : (sealR X Ex).shape.chalList = [1] := rfl

theorem seal_point : Nonempty (sealR X Ex).shape.IsPoint :=
  ⟨((Blocks.plainPoint Unit Unit (), ()) : (drawRound Unit).IsPoint × Unit)⟩

theorem seal_local : (sealR X Ex).IsLocal :=
  ⟨fun _ _ _ _ _ _ _ _ _ => rfl,
    fun _ _ _ _ p _ _ hE _ => hE p (Finset.mem_singleton_self p)⟩

end

section
variable {K X W : Type} {Ex : ExtSpec}

/-- the extractor: the identity -/
def sealExt : X × Ex.Str → Tr (sealR X Ex).shape → W → W := fun _ _ w => w

/-- Round-by-round knowledge soundness of SEAL, from a joint to itself. -/
def SealKnow (A : Rels K X Ex W) : Prop :=
  (sealR X Ex).red.Know A.on A.relR A.relR sealExt (sealErr X Ex)

theorem seal_red_out (a b : X × Ex.Str) (τ : Tr (sealR X Ex).shape)
    (h : (sealR X Ex).red.out a τ = some b) : b = a :=
  (Option.some.inj h).symm

theorem seal_know (A : Rels K X Ex W) : SealKnow A := fun a _ =>
  Doomed.of_forall _ _ fun τ b w hb hw => by
    rw [seal_red_out a b τ hb] at hw
    exact hw

theorem seal_onOut (A : Rels K X Ex W) :
    ∀ a τ b, A.on a → (sealR X Ex).red.out a τ = some b → A.on b := fun a τ b ha hb => by
  rw [seal_red_out a b τ hb]
  exact ha

end

#print axioms seal_know
#print axioms seal_local

end Cb.Pv.Tower
