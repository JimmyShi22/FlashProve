-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P4SR/SixClosed.lean: THE SIX AT SEGMENT 24 OF THE IOP AS WRITTEN IN LEAN, WITH NO NAMED
PREMISE LEFT: `objectsBack_at_seat` (ObjectsBackAtSeat.lean) with its three premises hK, hKo, hKg
paid by `k03_planes_of`, `k03_objects_of`, `k03_guests_of` (Johnson/Desc/First/Look/K03States.lean)
at l := 24. A JOINING: the closing that is meant (a file of this project that does
not ship, not compiled), with the conclusion written out, which a theorem's text must have: it is
`objectsBack_at_seat`'s, to the letter. One theorem with its proof.

Limits. Nothing on soundness. In the goals' scope alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P4SR.ObjectsBackAtSeat
import Johnson.Desc.First.Look.K03States

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P4
open Inst.Model (ScalesAndPolicy)
open VerifiableInference.Desc (Block Claim Chain Link FileDescription named)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (workAtW K6States K6Back PlanesStates PlanesBack)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (ObjectsStates ObjectsBack)
open VerifiableInference.OnPublicFiles (k03_planes_of k03_objects_of k03_guests_of)
open ProofFile (Cl)

/-- **The six at segment 24, from the scope and the opening alone.** -/
theorem six_at_seat {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ (Lk : Link S Cl) (iU3 : Nat), c.links[24]? = some Lk ∧
      Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3 ∧
      K6States Bs.G₀.W.hS iU3 (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) 24 4
        (VerifiableInference.Desc.K9.statesOfLink Lk) 3 ∧
      K6Back Bs.G₀.W.hS iU3 (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) 24 4
        (VerifiableInference.Desc.K9.statesOfLink Lk) 3 ∧
      PlanesStates iU3 Bs.G₀.W.hS.lmbH (VerifiableInference.Desc.K9.statesOfLink Lk) 2 ∧
      PlanesBack iU3 Bs.G₀.W.hS.lmbH (VerifiableInference.Desc.K9.statesOfLink Lk) 2 ∧
      ObjectsStates (VerifiableInference.Desc.K9.statesOfLink Lk) 2 ∧
      ObjectsBack (VerifiableInference.Desc.K9.statesOfLink Lk) 2 :=
  objectsBack_at_seat hS hR O (fun r hr => k03_planes_of hS hR O 24 (by norm_num) r hr)
    (k03_objects_of hS hR O 24 (by norm_num) false) (k03_guests_of hS hR O 24 (by norm_num) false)

end P4

#print axioms P4.six_at_seat
