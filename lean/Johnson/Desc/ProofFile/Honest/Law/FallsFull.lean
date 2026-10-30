-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/FallsFull.lean: the first chain's list of falls at the full size,
at K8's authors' three stated numbers. `fallsHead` (Honest/Law/FallsHead.lean) leaves five arguments
open. K8's authors have given three of them as functions with code of the public part, the ground
and the segment's number (Honest/K8/FallNumbers.lean). Here the list is laid at these three. Every
lemma on `fallsHead` is general in the three, so it holds of this list by unfolding; two are
restated.

  1  `fallsFull`   the definition
  2  `fallsFull_87`, `fallsFull_seats`   under the library's `P5J.AtMgA`: the list has 87 records;
     every record stands at a fall's seat

Limits.
  * `notGood` and `r0` stay open (see `fallsHead`).
  * No test reads the three numbers. Nothing here holds a stated number against its test. K8's
    authors' lemmas on the three numbers lie in other files, which are not imported here.
  * By K8's authors' word their number for `k8ShareFall` is held under a condition on the state
    before the batching. The chance that an earlier challenge leaves a state that fails that
    condition is not in it. So the sum of the stated numbers over this list is not yet a bound on
    all that can go wrong at these places.
  * Where a look-up does not return, the three functions return 0, 0 and 0 of 1: fillers.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.FallsHeadFull
import Johnson.Desc.ProofFile.Honest.K8.FallNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- The first chain's list of falls at the full size, at K8's authors' three terms: `fallsHead` at
`cols := K8.k8ColsAt G₀`, `tau := K8.k8TauAt G₀` and `share := P1K8.k8ShareAt Zp G₀`
(Honest/K8/FallNumbers.lean). `notGood` and `r0` stay open, as at `fallsHead`. -/
def fallsFull (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) (notGood : Nat → Odds) (r0 : Nat → Nat) :
    List (Fall S) :=
  fallsHead Zp G₀ (K8.k8ColsAt G₀) (K8.k8TauAt G₀) (P1K8.k8ShareAt Zp G₀) notGood r0

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {notGood : Nat → Odds} {r0 : Nat → Nat}

/-- Under `P5J.AtMgA` the list has 87 records. -/
theorem fallsFull_87 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    (fallsFull Zp Bs.G₀ notGood r0).length = 87 :=
  fallsHead_87 h hB

/-- Under `P5J.AtMgA` every record stands at a fall's seat. -/
theorem fallsFull_seats (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G₀ : ProofFile.Ground) :
    ∀ f ∈ fallsFull Zp G₀ notGood r0, fallSeat P5J.At.links f.place = true :=
  fallsHead_seats_full h G₀

end ProofFile.Honest

#print axioms ProofFile.Honest.fallsFull_87
#print axioms ProofFile.Honest.fallsFull_seats
