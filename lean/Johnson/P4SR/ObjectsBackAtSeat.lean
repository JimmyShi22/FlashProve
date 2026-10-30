-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P4SR/ObjectsBackAtSeat.lean: THE NAMED PREMISE ObjectsBack
(Johnson/Desc/Kinds/Law/ObjectsBack.lean: an accept of the runs K9.objectsCalls and
K9.guestsNone is an accept of what sub-protocol number b of a segment states under "objects" and
under "guests") AT THE IOP AS WRITTEN IN LEAN, segment 24 (the output head's), sub-protocol number 2
(the lookup argument on the head's calls). Theorems.

What is proved.
  objectsBack_of_find   where find? under "objects" and under "guests" gives the two guarded runs,
                  ObjectsBack holds: the first run lays a ledger alone, the second leaves the state:
                  so the heard reply is as it was, and the guard accepts.
  **objectsBack_at_seat**   P4SR/ObjectsAtSeat.lean's objectsStates_at_seat, with one conjunct
                  more: UNDER ITS THREE NAMED PREMISES hK, hKo, hKg there are Lk and iU3 with
                  c.links[24]? = some Lk, iU3's equation, K6States and K6Back at sub-protocol 3,
                  PlanesStates, PlanesBack, ObjectsStates and ObjectsBack at sub-protocol 2. ONE Lk
                  AND ONE iU3 SERVE ALL SIX.

The named premises, the existential quantifiers and what is not proved: as in
P4SR/ObjectsAtSeat.lean, word for word: hK, hKo, hKg are another file's theorems' conclusions, with
three of its terms written out; the files have not met in one build; only at our second,
non-standard hash, at the full size, in scope. Nothing on soundness.

-/
import Johnson.P4SR.ObjectsAtSeat
import Johnson.Desc.Kinds.Law.ObjectsBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P4
open Inst.Model (ScalesAndPolicy)
open VerifiableInference.Desc (Block Claim Chain Link FileDescription named)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (workAtW K6States K6Back PlanesStates PlanesBack)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (ObjectsStates ObjectsBack objectsCalls_putFork
  guestsNone_same)
open ProofFile (Cl)

/-- Where find? gives the two guarded runs, ObjectsBack holds. -/
theorem objectsBack_of_find {Lk : Link S Claim} {i : Nat}
    (ho : (VerifiableInference.Desc.K9.statesOfLink Lk i).find? (fun r => r.1 == "objects") =
      some ("objects", IM.guardRun ProofFile.sameReply
        (VerifiableInference.OnPublicFiles.objectsRun
          (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm))))
    (hg : (VerifiableInference.Desc.K9.statesOfLink Lk i).find? (fun r => r.1 == "guests") =
      some ("guests", IM.guardRun ProofFile.sameReply fun _ s =>
        named "K3 guests: a guest refuses"
          ((([] : List (VerifiableInference.Desc.First.Look.Guest S Cl)).mapM
            fun (g : VerifiableInference.Desc.First.Look.Guest S Cl) => g.form s).map
              fun l => (l, s)))) :
    ObjectsBack (VerifiableInference.Desc.K9.statesOfLink Lk) i := by
  refine ⟨fun run hrun k t y hy => ?_, fun run hrun k t y hy => ?_⟩
  · obtain rfl := congrArg Prod.snd (Option.some.inj (ho.symm.trans hrun))
    obtain ⟨G, e⟩ := objectsCalls_putFork k t y hy
    exact (IM.guardRun_yes _ k t y).2 ⟨hy, same_of_eq (by rw [e, S.out_putFork])⟩
  · obtain rfl := congrArg Prod.snd (Option.some.inj (hg.symm.trans hrun))
    exact (IM.guardRun_yes _ k t y).2 ⟨hy, same_of_eq (by rw [guestsNone_same k t y hy])⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **The six at segment 24 of the IOP as written in Lean.** -/
theorem objectsBack_at_seat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hK : ∀ r, K3Lot.readersAt Bs.G₀.W 24 = some r →
      ∃ (Lk : Link S Cl) (p : VerifiableInference.Desc.First.Look.P), c.links[24]? = some Lk ∧
        VerifiableInference.Desc.First.Look.placeAt Bs.G₀.W 24 false = some p ∧
        (VerifiableInference.Desc.K9.statesOfLink Lk 2).find? (fun x => x.1 == "planes") =
          some ("planes", IM.guardRun ProofFile.sameReply
            (VerifiableInference.Desc.K3.planesRun
              (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm) p.lm r)))
    (hKo : ∃ Lk : Link S Cl, c.links[24]? = some Lk ∧
      (VerifiableInference.Desc.K9.statesOfLink Lk 2).find? (fun r => r.1 == "objects") =
        some ("objects", IM.guardRun ProofFile.sameReply
          (VerifiableInference.OnPublicFiles.objectsRun
            (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm))))
    (hKg : ∃ Lk : Link S Cl, c.links[24]? = some Lk ∧
      (VerifiableInference.Desc.K9.statesOfLink Lk 2).find? (fun r => r.1 == "guests") =
        some ("guests", IM.guardRun ProofFile.sameReply fun _ s =>
          named "K3 guests: a guest refuses"
            ((([] : List (VerifiableInference.Desc.First.Look.Guest S Cl)).mapM
              fun (g : VerifiableInference.Desc.First.Look.Guest S Cl) => g.form s).map
                fun l => (l, s)))) :
    ∃ (Lk : Link S Cl) (iU3 : Nat), c.links[24]? = some Lk ∧
      Bs.G₀.W.H.tl.ix.U.getD 2 none = some iU3 ∧
      K6States Bs.G₀.W.hS iU3 (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) 24 4
        (VerifiableInference.Desc.K9.statesOfLink Lk) 3 ∧
      K6Back Bs.G₀.W.hS iU3 (parOf Bs.G₀.W.hS (workAtW Bs.G₀.W)) 24 4
        (VerifiableInference.Desc.K9.statesOfLink Lk) 3 ∧
      PlanesStates iU3 Bs.G₀.W.hS.lmbH (VerifiableInference.Desc.K9.statesOfLink Lk) 2 ∧
      PlanesBack iU3 Bs.G₀.W.hS.lmbH (VerifiableInference.Desc.K9.statesOfLink Lk) 2 ∧
      ObjectsStates (VerifiableInference.Desc.K9.statesOfLink Lk) 2 ∧
      ObjectsBack (VerifiableInference.Desc.K9.statesOfLink Lk) 2 := by
  obtain ⟨Lk, iU3, e1, hU, KS, KB, PSt, PB, OS⟩ := objectsStates_at_seat hS hR O hK hKo hKg
  obtain ⟨Lo, eo, fo⟩ := hKo
  obtain ⟨Lg, eg, fg⟩ := hKg
  obtain rfl : Lo = Lk := Option.some.inj (eo.symm.trans e1)
  obtain rfl : Lg = Lo := Option.some.inj (eg.symm.trans e1)
  exact ⟨Lg, iU3, e1, hU, KS, KB, PSt, PB, OS, objectsBack_of_find fo fg⟩

end

end P4

#print axioms P4.objectsBack_of_find
#print axioms P4.objectsBack_at_seat
