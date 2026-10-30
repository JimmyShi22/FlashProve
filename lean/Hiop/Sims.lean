-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/Sims.lean: the simulator of an IOP from that of an IOR (`IOR.simProto`): no further reads; the
answers of the external oracle that it was given are laid into the view.

Definition; the statement on it, `IOR.simProto_good`, is in Hiop/SimsProof.lean.

Terms: lean/GLOSSARY.md.
-/
import Hiop.ListNums
import Ior.ExactSeq
import Ior.ToProtoProofs
import Ior.OnlineHon
import Compile.Batch.SpecLife
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-- The simulator of the IOP from that of the IOR: no further reads; the external answers given are
laid into the view. -/
def IOR.simProto
    {X : Type} {E : ExtSpec} {R : IOR X E Unit extNone} (S : IOR.Honest.Sim R) :
    Compile.Lifetime.SimOf R.toInteractiveOracleProof :=
  fun x ρ a => (S x ρ ∅ a).map (Option.map (IOR.View.toD a))

end Iop
