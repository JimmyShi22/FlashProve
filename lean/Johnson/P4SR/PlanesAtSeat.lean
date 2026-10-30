-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P4SR/PlanesAtSeat.lean: THE NAMED PREMISE PlanesStates
(Johnson/Desc/Kinds/Law/PlanesRoad.lean: which run of claims sub-protocol number b of a segment
states under the name "planes") AT THE IOP AS WRITTEN IN LEAN, segment 24 (the output head's),
sub-protocol number 2 (the lookup argument on the head's calls). Theorems.

What is proved.
  ofForm_eq       the lookup's maker of claims K3Lot.ofForm is the head's asClaim.
  readers_head    at the head's segment K3Lot.readersAt gives the head's own readers callerReaders
                  (planesAt iU3), where iU3 is the third entry of the head's list of arrays.
  lm_head         the lookup's parameter lm at the head's segment is W.hS.lmbH.
  head_24         in the goals' scope segment 24 is the head's.
  planesStates_of_find   where find? under "planes" gives the guarded run at these readers,
                  PlanesStates holds: the guard on the heard reply only adds rejections.
  **planesStates_at_seat**   in the goals' scope, at an opening O of the IOP's value at our second,
                  non-standard hash (built on BLAKE2b's compression function): UNDER ONE NAMED
                  PREMISE hK there are Lk and iU3 with c.links[24]? = some Lk, iU3's equation,
                  K6States and K6Back at sub-protocol 3, and PlanesStates iU3 Bs.G₀.W.hS.lmbH
                  (K9.statesOfLink Lk) 2. ONE Lk AND ONE iU3 SERVE ALL THREE.

THE NAMED PREMISE hK is, word for word, the conclusion of the theorem k03_planes_of
(Johnson/Desc/First/Look/K03States.lean) at l := 24: whoever has that file and this one
in one build closes it by "fun r hr => k03_planes_of hS hR O 24 (by norm_num) r hr". The two files
have not met in one build.

Existential quantifiers. Lk and iU3, each fixed by the equation that gives it.
Not proved here. hK. That an opening exists. Only at that hash, at the full size, in scope. The
converse direction (PlanesStates asks one direction only). Nothing on soundness.

-/
import Johnson.P4SR.K6BackAtSeat
import Johnson.Desc.Kinds.Law.PlanesRoad
import Johnson.Desc.ProofFile.Lot.K3
import Johnson.Desc.First.Look.K3CallerAtPlan
import Johnson.Goal.Meaning.PlanShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P4
open Inst.Model (ScalesAndPolicy)
open VerifiableInference.Desc (Block Claim Chain Link FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (workAtW K6States K6Back PlanesStates)
open ProofFile (Cl)

/-- The lookup's maker of claims is the head's. -/
theorem ofForm_eq : K3Lot.ofForm = asClaim := rfl

/-- At the head's segment the lookup is handed the head's own readers. -/
theorem readers_head {W : OnBytes.Model.Verify.Public} {l iU3 : Nat}
    (hH : VerifiableInference.Desc.K3.isHead W l = true)
    (hU : W.H.tl.ix.U.getD 2 none = some iU3) :
    K3Lot.readersAt W l = some (callerReaders (planesAt iU3)) := by
  unfold K3Lot.readersAt
  dsimp only
  rw [if_pos hH, hU]
  rfl

/-- The lookup's parameter lm at the head's segment. -/
theorem lm_head {W : OnBytes.Model.Verify.Public} {l : Nat}
    {p : VerifiableInference.Desc.First.Look.P}
    (hH : VerifiableInference.Desc.K3.isHead W l = true)
    (hp : VerifiableInference.Desc.First.Look.placeAt W l false = some p) :
    p.lm = W.hS.lmbH := by
  have hl : l = (if W.p4 then 2 else 1) * W.NGr := eq_of_beq hH
  obtain ⟨pl, hpl, rfl⟩ := Option.map_eq_some_iff.mp hp
  rw [hl] at hpl
  exact (VerifiableInference.Desc.First.Look.lookAt_head hpl).2.2.1

/-- Where find? gives the guarded run at the head's readers, PlanesStates holds. -/
theorem planesStates_of_find {Lk : Link S Claim} {iU3 lm i : Nat}
    (hf : (VerifiableInference.Desc.K9.statesOfLink Lk i).find? (fun x => x.1 == "planes") =
      some ("planes", IM.guardRun ProofFile.sameReply
        (VerifiableInference.Desc.K3.planesRun
          (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm) lm
          (callerReaders (planesAt iU3))))) :
    PlanesStates iU3 lm (VerifiableInference.Desc.K9.statesOfLink Lk) i :=
  ⟨_, hf, fun k t y h => ((IM.guardRun_yes _ k t y).1 h).1⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- In the goals' scope segment 24 is the head's. -/
theorem head_24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    VerifiableInference.Desc.K3.isHead Bs.G₀.W 24 = true := by
  obtain ⟨h4, hN, -, -⟩ := Meaning.scope_plans hS hR O.public
  unfold VerifiableInference.Desc.K3.isHead
  rw [h4, hN]
  rfl

/-- **K6States, K6Back and PlanesStates at segment 24 of the IOP as written in Lean.** -/
theorem planesStates_at_seat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hK : ∀ r, K3Lot.readersAt Bs.G₀.W 24 = some r →
      ∃ (Lk : Link S Cl) (p : VerifiableInference.Desc.First.Look.P), c.links[24]? = some Lk ∧
        VerifiableInference.Desc.First.Look.placeAt Bs.G₀.W 24 false = some p ∧
        (VerifiableInference.Desc.K9.statesOfLink Lk 2).find? (fun x => x.1 == "planes") =
          some ("planes", IM.guardRun ProofFile.sameReply
            (VerifiableInference.Desc.K3.planesRun
              (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm) p.lm r))) :
    ∃ (Lk : Link S Cl) (iU3 : Nat), c.links[24]? = some Lk ∧
      Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3 ∧
      K6States Bs.G₀.W.hS iU3 (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) 24 4
        (VerifiableInference.Desc.K9.statesOfLink Lk) 3 ∧
      K6Back Bs.G₀.W.hS iU3 (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) 24 4
        (VerifiableInference.Desc.K9.statesOfLink Lk) 3 ∧
      PlanesStates iU3 Bs.G₀.W.hS.lmbH (VerifiableInference.Desc.K9.statesOfLink Lk) 2 := by
  obtain ⟨Lk, iU3, e1, hU, KS, KB⟩ := k6Back_at_seat hS hR O
  have hH := head_24 hS hR O
  obtain ⟨Lk', p, e1', hp, hf⟩ := hK _ (readers_head hH hU)
  obtain rfl : Lk' = Lk := Option.some.inj (e1'.symm.trans e1)
  rw [lm_head hH hp] at hf
  exact ⟨Lk', iU3, e1, hU, KS, KB, planesStates_of_find hf⟩

end

end P4

#print axioms P4.readers_head
#print axioms P4.lm_head
#print axioms P4.planesStates_at_seat
