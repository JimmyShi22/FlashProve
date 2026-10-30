-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupMemberWrittenOut.lean: AT ANY FILLING. The kind "lookup"
(K3): a member of the side that is seated over the lookup's row (`rowPairs`, Honest/K3/LotRow.lean),
written out. It is the masked sumcheck's part, lifted, beside `sumSim`, or the part that sends
nothing, lifted, beside `quietSim`. There is no third sort. Three theorems; no definition. General
in the filling, the site, the list of sub-protocols and the falls.

  `lookupMemberHasStage`          every member has a stage at its own number, with a call or without
  `lookupMemberAtSumcheckStage`   a member at a stage with a call, written out
  `lookupMemberAtQuietStage`      a member at a stage without a call, written out

Each is conditional on the side being seated. By `member_k3` (Honest/K3/Law/Good/K3Members.lean).

The sites of a public part (`lookSites`) are PLACES OF THE PROOF FILE ALONE (fifty under the
library's hypothesis at the full size): THE KEY FILE'S TWO LOOKUPS ARE NOT SPOKEN OF.

Limits. Equations between definitions. Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Good.K3Members
import Johnson.Desc.ProofFile.Honest.K3.RowQuietIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Part.MaskedSum (Call)
open ProofFile.Honest.K3.Law

variable {S Cl V W X Pb : Type}

/-- **Every member of the side has a stage at its own number**, with a call or without. -/
theorem lookupMemberHasStage (A : Fill W) (s : Site) (bs : List (Block S Cl)) (fs : List (Fall S))
    (σ : Side S Cl V W X Pb) (seated : Side.seated bs s.at_.place (rowPairs A s) fs = some σ)
    (u : Member V W X Pb) (member : u ∈ σ.members) :
    ∃ stage, (stages s.at_.face)[u.number]? = some stage ∧
      ((∃ call, stage.call s.at_.face = some call) ∨ stage.call s.at_.face = none) := by
  obtain ⟨stage, hstage, _⟩ := member_k3 A s bs fs σ seated u member
  refine ⟨stage, hstage, ?_⟩
  cases hcall : stage.call s.at_.face with
  | none => exact Or.inr rfl
  | some call => exact Or.inl ⟨call, rfl⟩

/-- **A member at a stage that has a sumcheck, written out.** The simulator is at the job's own
shape. -/
theorem lookupMemberAtSumcheckStage (A : Fill W) (s : Site) (bs : List (Block S Cl))
    (fs : List (Fall S)) (σ : Side S Cl V W X Pb)
    (seated : Side.seated bs s.at_.place (rowPairs A s) fs = some σ) (u : Member V W X Pb)
    (member : u ∈ σ.members) (stage : Stage) (call : Call)
    (atNumber : (stages s.at_.face)[u.number]? = some stage)
    (hasCall : stage.call s.at_.face = some call) :
    u = ⟨u.number, u.rounds,
      (sumPart (V := Unit) (sumName s.at_.place u.number) (endName s.at_.place u.number)
        (jobOf theReads (A.jobs s).asked s.at_ stage call)).lift (fun _ => ()) (A.wit s)
        (fun _ => ()) (fun y _ => y),
      sumSim ⟨s.at_.place, u.number⟩ (jobOf theReads (A.jobs s).asked s.at_ stage call).shape⟩ := by
  obtain ⟨stage', hstage', _, hp, hs⟩ := member_k3 A s bs fs σ seated u member
  obtain rfl : stage' = stage := Option.some.inj (hstage'.symm.trans atNumber)
  obtain ⟨j, rs, p, sm⟩ := u
  have hp' : p = (partOf (V := Unit) theReads (A.jobs s).asked s.at_ stage' j).lift (fun _ => ())
      (A.wit s) (fun _ => ()) (fun y _ => y) := hp
  have hs' : sm = simOf s.at_ stage' j := hs
  subst hp' hs'
  unfold partOf simOf
  simp only [hasCall]
  rfl

/-- **A member at a stage that sends nothing, written out.** -/
theorem lookupMemberAtQuietStage (A : Fill W) (s : Site) (bs : List (Block S Cl))
    (fs : List (Fall S)) (σ : Side S Cl V W X Pb)
    (seated : Side.seated bs s.at_.place (rowPairs A s) fs = some σ) (u : Member V W X Pb)
    (member : u ∈ σ.members) (stage : Stage)
    (atNumber : (stages s.at_.face)[u.number]? = some stage)
    (noCall : stage.call s.at_.face = none) :
    u = ⟨u.number, u.rounds,
      (ProofFile.Honest.quietPart 1 : Part Unit Ask Unit).lift (fun _ => ()) (A.wit s) (fun _ => ())
        (fun y _ => y), ProofFile.Honest.quietSim ⟨s.at_.place, u.number⟩ 1⟩ := by
  obtain ⟨stage', hstage', _, hp, hs⟩ := member_k3 A s bs fs σ seated u member
  obtain rfl : stage' = stage := Option.some.inj (hstage'.symm.trans atNumber)
  obtain ⟨j, rs, p, sm⟩ := u
  have hp' : p = (partOf (V := Unit) theReads (A.jobs s).asked s.at_ stage' j).lift (fun _ => ())
      (A.wit s) (fun _ => ()) (fun y _ => y) := hp
  have hs' : sm = simOf s.at_ stage' j := hs
  subst hp' hs'
  unfold partOf simOf
  simp only [noCall]
  rfl

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupMemberHasStage
#print axioms ProofFile.Honest.K3.Term.lookupMemberAtSumcheckStage
#print axioms ProofFile.Honest.K3.Term.lookupMemberAtQuietStage
