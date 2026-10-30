-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/WholeSharpProof.lean: `simP`, the simulator of an IOP from that of an IOR, and `simP_exact`: under
the hypotheses of its statement it is exact outside the withheld set.

Terms: lean/GLOSSARY.md.
-/
import Hiop.WholeTrue
import Hiop.ListNums
import Hiop.Whole
import Ior.More
import Hiop.WholeTrueProof
import Hiop.WholeProof
import Hiop.OfflineProof
import Hiop.InterfaceProofs
import Ior.OnlineK
import Ior.OnlineHon
import Hiop.ProofKit
import Iop.BatchOne
import Blocks.Basic
import Blocks.Batch.Kit
import Ior.MoreProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open Prob Compile.Lifetime Compile.BatchLife

section
variable {X Wt Wi : Type} {E : ExtSpec}

/-- The simulator of the IOP from that of the IOR: no further reads; the external answers given are
laid into the view. -/
def simP {R : IOR X E Unit extNone} (S : IOR.Honest.Sim R) : SimOf R.toInteractiveOracleProof :=
  fun x ρ a => (S x ρ ∅ a).map (Option.map (IOR.View.toD a))

open Classical in
theorem simP_exact {R : IOR X E Unit extNone} (H : R.Honest Wi Unit) (ext : Wt → E.Str)
    (inp : Wt → X → Wi) {Ri : X → E.Str → Wi → Prop}
    {bud : Rho R.shape → Finset (OPos R.shape) → Prop} {S : IOR.Honest.Sim R}
    (hS : H.ExactWith Ri bud S) (hb : ∀ ρ, bud ρ ∅)
    (ht : ∀ ρ, (R.reads ρ).biUnion (R.tie ρ) ⊆ R.extReads ρ) (w : Wt) (x : X)
    (hR : Ri x (ext w) (inp w x)) (ρ : Rho R.shape) (hρ : ρ ∉ H.Hid (inp w x) x) :
    (H.toProto ext inp).output w x ρ = simP S x ρ (R.toInteractiveOracleProof.extAns x ρ (ext w)) := by
  rw [IOR.Honest.output_toProto, hS x (ext w) (inp w x) hR ρ hρ ∅ (hb ρ),
    IOR.given_empty R ρ (ht ρ), IOR.ans_extReads R x ρ (ext w)]
  rfl

end
end Iop
