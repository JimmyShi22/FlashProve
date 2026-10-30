-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P4SR/K6StatesAtChain.lean: K6States AT THE DESCRIPTION's OWN FIRST CHAIN: link 24, hearing block number 3.
A joining of two laws: IM.k6_of (IMR/K6Seat.lean: at an opening of onlineDescription's value, in the goals' scope,
link 24's fourth hearing block is the seated block, alone, in the seat's dress) · P4SR/K6StatesAtSeat.lean's
k6States_of_laid.

What is said. **k6States_at_seat**: in the goals' scope, at an opening O of the description's value at `secondHashFunction`:
there are Lk and iU3 with c.links[24]? = some Lk, Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3 and
K6States Bs.G₀.W.hS iU3 (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) 24 4 (K9.statesOfLink Lk) 3; and Bs.G₀.built.size = 25.

The letters. Lk and iU3 stand under "there is", EACH TIED BY THE EQUATION THAT MAKES IT. c is the opening's own chain.
What it does not give. That an opening is there (IM.seat_open gives one wherever onlineDescription returns). At
`secondHashFunction` alone, as k6_of is. The full size alone: 24 is a literal. Nothing on the way back. Nothing on soundness.

-/
import Johnson.IMR.K6Seat
import Johnson.P4SR.K6StatesAtSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P4
open Inst.Model (ScalesAndPolicy)
open VerifiableInference.Desc (Block Chain Link FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (workAtW K6States)
open ProofFile (Cl)

/-- **K6States at link 24's fourth hearing block of the description's first chain.** -/
theorem k6States_at_seat {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (Lk : Link S Cl) (iU3 : Nat), c.links[24]? = some Lk ∧
      Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3 ∧
      K6States Bs.G₀.W.hS iU3 (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) 24 4
        (VerifiableInference.Desc.K9.statesOfLink Lk) 3 ∧ Bs.G₀.built.size = 25 := by
  obtain ⟨Lk, b, b', ms, e1, e2, _, hs, hla, sz, _, _⟩ := IM.k6_of hS hR O
  obtain ⟨iU3, hU, K⟩ := k6States_of_laid hs hla e2
  exact ⟨Lk, iU3, e1, hU, K, sz⟩

end P4

#print axioms P4.k6States_at_seat
