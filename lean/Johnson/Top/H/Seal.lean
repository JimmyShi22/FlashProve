-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Seal.lean: the kind of block SEAL (one round without content at the end of a chain) as
a value of `Kind` (Johnson/Top/Kind.lean), at any written list of callers, with the kind's
hypothesis and the three facts beside it.

Nothing new is proved: every line is a call of Cb/Pv/Tower/Seal.lean. A size is a caller: the joint
at which the chain stands, which is the block's joint on both sides: data alone.
Main names:
  `SealCaller`: the types of a joint, and the joint. `kSeal L`: the kind.
  `kSeal_know`, `_point`, `_local`, `_onOut`, `_good`: without any premise.
  `HSeal`: closed: for every list of callers the kind is knowledge sound. `hSeal`: it holds.
Limits: no list of callers is written here. The block is the identity on statement and oracles, at
the error 0: it says nothing on what the round's hash binds in the compiled scheme. Nothing on an
honest prover.

-/
import Johnson.Top.Kind
import Cb.Pv.Tower.Seal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR Cb.Pv.Tower

/-- Who calls SEAL: the joint at which the chain stands. Data alone. -/
structure SealCaller : Type 1 where
  K : Type
  X : Type
  W : Type
  Ex : ExtSpec
  A : Rels K X Ex W

/-- SEAL, at a written list of callers. -/
@[reducible] def kSeal (L : List SealCaller) : Kind.{1} where
  Size := SealCaller
  sizes := L
  src := fun c => jOf c.A
  dst := fun c => jOf c.A
  block := fun c => ⟨sealR c.X c.Ex, sealExt, sealErr c.X c.Ex⟩

variable (L : List SealCaller)

theorem kSeal_know : (kSeal L).Know := fun c _ => seal_know c.A

theorem kSeal_point : (kSeal L).Point := fun c _ => seal_point c.X c.Ex

theorem kSeal_local : (kSeal L).Local := fun c _ => seal_local c.X c.Ex

theorem kSeal_onOut : (kSeal L).OnOut := fun c _ a τ b hb ha => seal_onOut c.A a τ b ha hb

theorem kSeal_good : ∀ c ∈ L, ((kSeal L).block c).Good :=
  Kind.good (kSeal_know L) (kSeal_point L) (kSeal_local L) (kSeal_onOut L)

/-- The hypothesis of the kind, closed: knowledge soundness alone, for every list of callers. -/
def HSeal : Prop := ∀ L : List SealCaller, (kSeal L).Know

theorem hSeal : HSeal := kSeal_know

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hSeal
#print axioms VerifiableInference.OnPublicFiles.kSeal_good
