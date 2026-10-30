-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P4SR/ObjectsAtSeat.lean: TWO NAMED PREMISES AT THE IOP AS WRITTEN IN LEAN, segment 24
(the output head's), sub-protocol number 2 (the lookup argument on the head's calls): ObjectsStates
(Johnson/Desc/Kinds/Law/ObjectsStates.lean: which runs of claims that sub-protocol states under the
names "objects" and "guests") and PlanesBack (Johnson/Desc/Kinds/Law/SilentAll.lean: an accept of
the lookup's own run "planes" is an accept of the run that is stated under that name). Theorems.

What is proved.
  objectsRun_calls   the lookup's run "objects" at the calls, with the lookup's maker of claims
                  K3Lot.ofForm, is K9.objectsCalls: by rfl.
  objectsStates_of_find   where find? under "objects" and under "guests" gives the two guarded runs,
                  ObjectsStates holds: the guard on the heard reply only adds rejects.
  planesRun_putFork   an accept of the run "planes" at the calls turns the verifier's state by
                  laying a ledger alone.
  planesBack_of_find   where find? under "planes" gives the guarded run at the head's readers,
                  PlanesBack holds: laying a ledger leaves the heard reply, so the guard accepts.
  **objectsStates_at_seat**   in the goals' scope, at an opening O of the IOP's value at our second,
                  non-standard hash (built on BLAKE2b's compression function): UNDER THREE NAMED
                  PREMISES hK, hKo, hKg there are Lk and iU3 with c.links[24]? = some Lk, iU3's
                  equation, K6States and K6Back at sub-protocol 3, PlanesStates, PlanesBack and
                  ObjectsStates at sub-protocol 2. ONE Lk AND ONE iU3 SERVE ALL FIVE.

THE NAMED PREMISES. hK: P4SR/PlanesAtSeat.lean's own, unturned. hKo, hKg are the conclusions of
the theorems k03_objects_of and k03_guests_of (Johnson/Desc/First/Look/K03States.lean)
at l := 24, d := false, WITH THREE OF THAT FILE'S TERMS WRITTEN OUT: 2 for
IM.k3Ix 24 false; the calls' seat for seatOf K3Lot.ofForm false (that definition stands in that file
itself); the body of guestsRun [] (its file lies beneath neither ground). Whoever has that file and
this one in one build is meant to close them by "k03_objects_of hS hR O 24 (by norm_num) false" and
the like. THE FILES HAVE NOT MET IN ONE BUILD: that the written-out terms are theirs by definition
is read, not compiled.

Existential quantifiers. Lk and iU3, each fixed by the equation that gives it; in hK, hKo and hKg:
Lk, fixed by c.links[24]?; in hK: p, fixed by placeAt's equation.
Not proved here. hK, hKo, hKg. That an opening exists. Only at that hash, at the full size, in
scope. For "objects" and "guests" the converse direction (ObjectsStates asks one direction only).
Nothing on soundness.

-/
import Johnson.P4SR.PlanesAtSeat
import Johnson.Desc.Kinds.Law.ObjectsStates
import Johnson.Desc.Kinds.Law.SilentAll
import Johnson.Top.H.K3RunsLaw
import Johnson.Desc.First.StateOut

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P4
open Inst.Model (ScalesAndPolicy)
open VerifiableInference.Desc (Block Claim Chain Link FileDescription named)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (workAtW K6States K6Back PlanesStates PlanesBack)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (ObjectsStates objectsStates_of_guarded)
open ProofFile (Cl)

/-- The lookup's run "objects" at the calls is K9.objectsCalls. -/
theorem objectsRun_calls :
    VerifiableInference.OnPublicFiles.objectsRun (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm) =
      VerifiableInference.Desc.K9.objectsCalls := rfl

/-- Where find? gives the two guarded runs, ObjectsStates holds. -/
theorem objectsStates_of_find {Lk : Link S Claim} {i : Nat}
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
    ObjectsStates (VerifiableInference.Desc.K9.statesOfLink Lk) i :=
  objectsStates_of_guarded (IM.guardRun ProofFile.sameReply)
    (fun r k t y h => ((IM.guardRun_yes r k t y).1 h).1) ho hg

/-- An accept of the run "planes" at the calls turns the state by laying a ledger alone. -/
theorem planesRun_putFork (cl : OnBytes.Model.Aff → Claim) (lm : Nat)
    (rd : VerifiableInference.Desc.K3.Readers S) (k : Nat) (t : S) (y : List Claim × S)
    (h : VerifiableInference.Desc.K3.planesRun (VerifiableInference.Desc.K3.seatCalls cl) lm rd k
      t = .ok y) : ∃ G, y.2 = t.putFork G := by
  unfold VerifiableInference.Desc.K3.planesRun at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals (cases h; try exact ⟨_, rfl⟩)

/-- Where find? gives the guarded run at the head's readers, PlanesBack holds. -/
theorem planesBack_of_find {Lk : Link S Claim} {iU3 lm i : Nat}
    (hf : (VerifiableInference.Desc.K9.statesOfLink Lk i).find? (fun x => x.1 == "planes") =
      some ("planes", IM.guardRun ProofFile.sameReply
        (VerifiableInference.Desc.K3.planesRun
          (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm) lm
          (callerReaders (planesAt iU3))))) :
    PlanesBack iU3 lm (VerifiableInference.Desc.K9.statesOfLink Lk) i := by
  intro run hrun k t y hy
  obtain rfl := congrArg Prod.snd (Option.some.inj (hf.symm.trans hrun))
  obtain ⟨G, e⟩ := planesRun_putFork _ _ _ k t y hy
  exact (IM.guardRun_yes _ k t y).2 ⟨hy, same_of_eq (by rw [e, S.out_putFork])⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **K6States, K6Back, PlanesStates, PlanesBack and ObjectsStates at segment 24 of the IOP as
written in Lean.** -/
theorem objectsStates_at_seat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
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
      ObjectsStates (VerifiableInference.Desc.K9.statesOfLink Lk) 2 := by
  obtain ⟨Lk, iU3, e1, hU, KS, KB, PSt⟩ := planesStates_at_seat hS hR O hK
  have hH := head_24 hS hR O
  obtain ⟨Lp, p, ep, hp, fp⟩ := hK _ (readers_head hH hU)
  obtain ⟨Lo, eo, fo⟩ := hKo
  obtain ⟨Lg, eg, fg⟩ := hKg
  obtain rfl : Lp = Lk := Option.some.inj (ep.symm.trans e1)
  obtain rfl : Lo = Lp := Option.some.inj (eo.symm.trans e1)
  obtain rfl : Lg = Lo := Option.some.inj (eg.symm.trans e1)
  rw [lm_head hH hp] at fp
  exact ⟨Lg, iU3, e1, hU, KS, KB, PSt, planesBack_of_find fp, objectsStates_of_find fo fg⟩

end

end P4

#print axioms P4.objectsRun_calls
#print axioms P4.objectsStates_of_find
#print axioms P4.planesRun_putFork
#print axioms P4.planesBack_of_find
#print axioms P4.objectsStates_at_seat
