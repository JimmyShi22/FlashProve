-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/LeftAtBatch.lean: AT THE 24 SEGMENTS IN FRONT OF THE HEAD's, IN FRONT OF THE BATCHING,
TWO MORE OF THE FORMS THAT THE LOOKUP ON THE CALLS HAS HEARD (cEnd, leaves.start) NAME NO ENTRY. AT
STATES THAT THE FIRST CHAIN's OWN BLOCKS REACH; UNDER THE SCOPE, THE FILES READ, IM.Open AND THE
DESCRIPTION's TEST ON ITS PLAN. Lemmas; none of the library's goals. No prover stands in them;
nothing on completeness, soundness or hiding. A joining.

  `bare_of_leftAt`   the second and the fourth of the seven tests of FillBare.leftAtB;
      FillBare.namedB begins with "names no entry" (Johnson/Desc/First/FillBare.lean)
  `callsLeft_behind`   behind the lookup on the calls: OnPublicFiles.leftAt_reached
      (Johnson/Desc/First/Look/K03LeftQ.lean), carried from the fold over the blocks to "reached" by
      reach_fold (Johnson/Top/H0/Walk/Reach.lean)
  **`callsLeft_att`**   in front of an attention segment's batching, by `look_back_att`
      (Johnson/P1K8R/LookAtBatchAll.lean): the fields cEnd and leaves of `StillAtt`
      (BehindAtReach.lean)
  `callsLeft_layers`   the like at a layers' segment, by `look_back_layers` (LookAtBatch.lean).
      User: nobody yet
The like, at the states that the wrapped blocks reach, behind the lookup, at attention alone:
OnPublicFiles.reached_leftAt (Johnson/Desc/First/Look/K03ReachedAt.lean).
Limits. Nothing on the head's segment. Nothing on what the lookup on the digits has heard. Nothing
on whether any state is reached.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P1K8R.LookAtBatchAll
import Johnson.Desc.First.Look.K03LeftQ
import Johnson.Desc.First.FillBare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

/-- What the test on what a lookup has left (FillBare.leftAtB, Johnson/Desc/First/FillBare.lean)
says of two of the forms that were heard: they name no entry. -/
theorem bare_of_leftAt {g : Forest.Heard} {G : Fork} (h : FillBare.leftAtB g G = true) :
    g.cEnd.ents = #[] ∧ g.leaves.start.ents = #[] := by
  simp only [FillBare.leftAtB, FillBare.namedB, Bool.and_eq_true] at h
  exact ⟨Array.isEmpty_iff.mp h.1.1.1.1.1.2.1, Array.isEmpty_iff.mp h.1.1.1.2.1⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Behind the lookup on the calls, at the 24 segments in front of the head's: it has heard
something, and the two forms name no entry.** -/
theorem callsLeft_behind (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 4) (z, s)) :
    ∃ g, s.lookHeard? = some g ∧ g.cEnd.ents = #[] ∧ g.leaves.start.ents = #[] := by
  obtain ⟨-, rs, cols, f⟩ := Johnson.Desc.First.Walk.Tied.reach_fold.1 h
  have e : 14 * l + 2 + IM.k3Ix l false + 1 = 14 * l + 4 := by
    show 14 * l + 2 + ((if false = true then 6 else 1) + (if l = 24 then 1 else 0)) + 1 = _
    rw [if_neg (by decide), if_neg (by omega)]
  obtain ⟨g, G, hg, -, hb⟩ := OnPublicFiles.leftAt_reached hS hR O hOk l hl (by rw [e]; exact f)
  exact ⟨g, hg, bare_of_leftAt hb⟩

/-- **So, at an attention segment, in front of the batching.** -/
theorem callsLeft_att (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (z, s)) :
    ∃ k, s.lookHeard? = some k ∧ k.cEnd.ents = #[] ∧ k.leaves.start.ents = #[] := by
  obtain ⟨s4, r4, e⟩ := look_back_att hS hR O hOk hg h
  obtain ⟨k, hk, hb⟩ := callsLeft_behind hS hR O hOk (l := 2 * g + 1) (by omega) r4
  exact ⟨k, e k hk, hb⟩

/-- **The like at a layers' segment.** -/
theorem callsLeft_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {g : ℕ} (hg : g < 12) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (28 * g + 9) (z, s)) :
    ∃ k, s.lookHeard? = some k ∧ k.cEnd.ents = #[] ∧ k.leaves.start.ents = #[] := by
  obtain ⟨s4, r4, e⟩ := look_back_layers hS hR O hOk hg h
  have r4' : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g) + 4) (z, s4) := by
    rw [show 14 * (2 * g) + 4 = 28 * g + 4 by omega]
    exact r4
  obtain ⟨k, hk, hb⟩ := callsLeft_behind hS hR O hOk (l := 2 * g) (by omega) r4'
  exact ⟨k, e k hk, hb⟩

end

end P1K8

#print axioms P1K8.bare_of_leftAt
#print axioms P1K8.callsLeft_behind
#print axioms P1K8.callsLeft_att
#print axioms P1K8.callsLeft_layers
