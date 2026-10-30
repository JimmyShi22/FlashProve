-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/FiveReach.lean: CONDITIONAL: the five facts on a state of the verifier
that `doorYes_narrow` spends (`FiveAt`, Johnson/Desc/K5/Honest/Law/DoorNarrow.lean) hold at every
state without a mark that the first chain's OWN sub-protocols reach (`Reach`,
Johnson/Top/H0/Walk/Reach.lean, over the chain's flat list as it stands).

Why this file. The library's structure of facts along the run (`FoldFacts`,
Johnson/Desc/First/FoldFacts.lean) is had at the states that the WRAPPED sub-protocols reach (each
refuses a shown word that is not below the prime). What is reached by the wrapped ones is reached
by their own, not the other way round. But the library's five lemmas under these five fields
(`IM.seatsCarried_field`, `IM.msgShapes_field`, Johnson/IMR/SeatsField.lean; `codes_field`,
`liveShape_field`, `liveLayout_field`, Johnson/IMR/AtReach.lean) are stated over the own
sub-protocols' family, or over the fold that it gives. They are called here at that family.

Main names:
  `fiveAt_of_reach`: in scope, at an opening of the maker whose description passes its test on the
    plan, under one test on public data and where the list of seats can be laid: `Reach 0 c.blocksInOrder
    (ProofFile.startS Z) k (z, s)` and "s bears no mark" give `FiveAt Ld (msgsOfChain ..) (sentAt Z) s`.

Limits. Conditional on all of these. At the function `OnBytes.secondHashFunction`, as the lemmas that are
called have it; nothing is asked of it here. That a state of an honest run is reached in this sense
is not shown here.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.DoorNarrow
import Johnson.IMR.AtReachFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc VerifiableInference.Desc.First
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- **The five facts at every state without a mark that the first chain's own sub-protocols
reach.** Conditional: hS: the public input is in scope; hR: the public files are read; O: an
opening of the maker; hF: the description passes its test on the plan; hB: a test with code: the
planner's sendings, in the order of their entries, are those of the sub-protocols numbered below
358 in the flat list's order (the number is the called lemmas' own); hLd: the list of seats can be
laid; h: the state is reached; hu: no mark. -/
theorem fiveAt_of_reach {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (hB : K12.Door.sendsAreB Z.made.proof.1 358 (K12.Door.snAt Z Bs.G₀ IM.placesW) = true)
    {Ld : K12.Door.Laid} (hLd : K12.Door.laidAtCodes Z.first.codes Z.made.proof.1 = some Ld)
    {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s))
    (hu : s.failed = none) :
    FiveAt Ld (K12.Door.msgsOfChain Z.made.proof.1) (Meaning.K2.sentAt Z) s := by
  have hp := Meaning.K2.flat_planOk O.desc hF
  have raw : ∀ (k : ℕ) (a : ProofFile.InstPub × S), Reach 0 c.blocksInOrder (ProofFile.startS Z) k a →
      Reach 0 c.blocksInOrder (ProofFile.startS Z) k (id a) := fun _ _ h => h
  have fold := Meaning.K2.fold_of_rch raw
  exact
    { seats := IM.seatsCarried_field hS hR O _ id fold hF hB hLd k (z, s) h hu
      shapes := IM.msgShapes_field hS hR O _ id fold hF hB k (z, s) h hu
      liveShape := Meaning.K2.liveShape_field hS hR O hp _ id raw k (z, s) h hu
      liveLayout := Meaning.K2.liveLayout_field hS hR O hp _ id raw k (z, s) h hu
      codes := Meaning.K2.codes_field hS hR O hp _ id raw k (z, s) h hu }

end H2K5.Honest

#print axioms H2K5.Honest.fiveAt_of_reach
