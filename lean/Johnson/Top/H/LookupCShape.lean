-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/LookupCShape.lean: the lookup inside a sub-proof, at the records of public numbers
that the verifier itself makes.

The verifier's routine Forest.pad makes its record of public numbers from the calls, the cap on a
tree's depth and the numbers of padding keys: it takes h₀ from Forest.shape, tests pub by
Forest.pubAsk, and goes on with { h₀ with pub := pub }.
 - MadeLookupC L: every caller's record in the list L is made so, both routines returning a value.
 - HLookupCMade, a closed proposition: for every such list, round-by-round knowledge soundness of
   each block of the kind kLookupC L (Johnson/Top/H/LookupC.lean), for every tuple of committed
   messages, at the block's own errors. hLookupCMade proves it. No list of sizes is written and no
   test on numbers is left as a premise: Cb.Fo.shape_ok pays FoNums.ok from the two successes.
 - lookupC_good_made: all four facts of a block, over the caller's signature.

What ties MadeLookupC to that routine. MadeLookupC restates the first three lines of Forest.pad's
body (OnBytes/Model/Look.lean). Its clause on one caller is Fo.ShapeOf
(OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean) at that caller's record, for some calls, cap and numbers
of padding keys. Fo.hcOut2V (OnBytes/Tie/Pv/Lookup/Forest/FoPadAll.lean) says of every run of
Forest.pad that returns, from a sized fork and a context on a view with no message open, that
ShapeOf holds of the record with which the run went on. This file imports neither of the two and
does not state the step from the one to the other.

What the file does not say: that a caller exists whose data are a sub-proof's own, or how its joints
meet a neighbour's. An empty list of callers meets MadeLookupC for nothing. How small the block's
own errors are is not said here: lookupC_small (Johnson/Top/H/LookupC.lean) says that each round's
number of bad challenges is below the number of its challenges.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Top.H.LookupC
import OnBytes.Tie.Pv.Lookup.Port.FoShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open Cb.Fo
open OnBytes.Model (Forest.Shape Forest.shape Forest.pubAsk Call)

/-- Every caller's record of public numbers is one with which Forest.pad goes on. -/
def MadeLookupC (L : List LookupCCaller) : Prop :=
  ∀ c ∈ L, ∃ (calls : Array Call) (lid : Nat) (h₀ : Forest.Shape) (pub : Array Nat),
    Forest.shape calls lid = .ok h₀ ∧ Forest.pubAsk h₀ pub = .ok () ∧ c.h = { h₀ with pub := pub }

/-- The verifier's own two tests give the test on public numbers. -/
theorem okLookupC_of_made {L : List LookupCCaller} (hL : MadeLookupC L) : OkLookupC L :=
  fun c hc => by
    obtain ⟨calls, lid, h₀, pub, hs, hp, e⟩ := hL c hc
    rw [e]
    exact shape_ok hs hp

/-- Knowledge soundness of the lookup of a sub-proof, whoever calls it, at every record of public
numbers that the verifier makes. -/
def HLookupCMade : Prop := ∀ L : List LookupCCaller, MadeLookupC L → (kLookupC L).Know

theorem hLookupCMade : HLookupCMade := fun L hL => hLookupCEvery L (okLookupC_of_made hL)

/-- Over its caller's signature every such block has the property of a block. -/
theorem lookupC_good_made (L : List LookupCCaller) (hL : MadeLookupC L) :
    ∀ c ∈ L, ((kLookupC L).toKind.block c).Good :=
  lookupC_good L (okLookupC_of_made hL)

#print axioms VerifiableInference.OnPublicFiles.hLookupCMade
#print axioms VerifiableInference.OnPublicFiles.lookupC_good_made

end VerifiableInference.OnPublicFiles
