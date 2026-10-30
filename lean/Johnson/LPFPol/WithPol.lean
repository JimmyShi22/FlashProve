-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/WithPol.lean: the proof file's public part, and the segments' records, with the three
numbers C, theta, cap of the acceptance policy replaced. Definitions alone.
  `wpP`, `wpM`, `wpZ`, `wpG`: the planner's record, the maker's record, the public part (with
  another parameter file's bytes) and the segments' records, each with `Public.withPol`
  (OnBytes/Tie/PlanAtPolicy.lean) at its public record; every other field stays.
Limits. Nothing is proved here. Nothing on soundness.

-/
import OnBytes.Tie.PlanAtPolicy
import Johnson.Desc.ProofFile.OnlineDescription

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFPol
open OnBytes OnBytes.Model

def wpP (p : Verify.Planned) (C theta cap : Nat) : Verify.Planned :=
  { p with X := p.X.withPol C theta cap }

def wpM (m : Johnson.G.OfPlan.Made) (C theta cap : Nat) : Johnson.G.OfPlan.Made :=
  { m with p := wpP m.p C theta cap }

def wpZ (Z : ProofFile.Pub) (pol' : ByteArray) (C theta cap : Nat) : ProofFile.Pub :=
  { Z with pol := pol', made := wpM Z.made C theta cap }

def wpG (G : ProofFile.Ground) (C theta cap : Nat) : ProofFile.Ground :=
  { G with W := G.W.withPol C theta cap }

end LPFPol
