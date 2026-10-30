-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/SimsProof.lean: `IOR.simProto_good`: from an exact simulator of an IOR, a bound on the chance
that the output of the honest side of its IOP differs from that of `IOR.simProto`.

Terms: lean/GLOSSARY.md.
-/
import Hiop.Sims
import Hiop.OfflineProof
import Hiop.ListNums
import Hiop.InterfaceProofs
import Ior.OnlineK
import Ior.OnlineHon
import Hiop.ProofKit
import Iop.BatchOne
import Blocks.Basic
import Blocks.Batch.Kit

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-- Under `hR`: the simulator of the IOP is exact outside the secret-dependent withheld set, if the
IOR's simulator is exact (`hS`), the budget bears the verifier's own positions (`hb`), and the
verifier itself reads all that is tied to its positions (`ht`); in this sense: the set of ρ at which
the output of the IOP's honest side differs from that of `IOR.simProto S` has at most the
probability of the secret-dependent withheld set `H.Hid (inp w x) x`. -/
theorem IOR.simProto_good {X Wt Wi : Type} {E : ExtSpec} {R : IOR X E Unit extNone}
    (H : R.Honest Wi Unit) (ext : Wt → E.Str) (inp : Wt → X → Wi)
    {Ri : X → E.Str → Wi → Prop} {bud : Rho R.shape → Finset (OPos R.shape) → Prop}
    {S : IOR.Honest.Sim R} (hS : H.ExactWith Ri bud S) (hb : ∀ ρ, bud ρ ∅) (ht : R.Tied)
    (w : Wt) (x : X) (hR : Ri x (ext w) (inp w x)) :
    prRho
        {ρ | (H.toProto ext inp).output w x ρ ≠ IOR.simProto S x ρ (R.toInteractiveOracleProof.extAns x ρ (ext w))} ≤
      prRho (H.Hid (inp w x) x) := by
  classical
  refine pr_mono _ fun ρ hρ => ?_
  by_contra hn
  apply hρ
  rw [IOR.Honest.output_toProto, hS x (ext w) (inp w x) hR ρ hn ∅ (hb ρ),
    IOR.given_empty R ρ (Finset.biUnion_subset.2 (ht ρ)), IOR.ans_extReads R x ρ (ext w)]
  rfl

end Iop
