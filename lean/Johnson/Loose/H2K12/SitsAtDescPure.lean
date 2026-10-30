-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Loose.H2K12.SitsInPure
import Johnson.Desc.ProofFile.Law.MakerPublic
/-
Johnson/Loose/H2K12/SitsAtDescPure.lean: K12_sits AT THE SEATED
TEXT's OWN CONSTANT: ProofFile.onlineDescription o pol lay KL (OnlineDescription.lean): the two premises of pureZ_sits on
the seat PAID AT THAT TEXT's OWN SEAT onlineFirstChainBlockTables, and an accepting run of the proof file's IOP as
written in Lean carried to the four places. Over SitsInPure.lean.

k12_sits ends in FirstJ (pL N) J, that is J = firstCore (pL N) nm;
k12_instance's FirstOut ProofFile.sameReply (pL N) J leave
says J = firstCore (pL N) nm and leave = outCore ProofFile.sameReply (H2K12/FirstSeatForm.lean).
NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. NO NEW MATHEMATICS.
WHAT STANDS AGAINST IT, FIRST: NO EXAMPLE: at no files is onlineDescription shown in Lean to return, and
nothing has run. pre, l, nm stand under «there is» at the first chain. o, THE SECOND HASH FUNCTION,
IS A LETTER THROUGHOUT.
  (onlineDescription's text read back is the seat's files' own lemma:
      Johnson/Desc/ProofFile/Law/MakerPublic.lean: descPure_made: called.)
  thePure_k12          the kind's lot stands in onlineFirstChainBlockTables's list.
  k9_face · thePure_noFace     NoFaceAt at onlineFirstChainBlockTables: of its fifteen lots K9's alone gives a
      maker (the others' field «batch» is the default, by rfl), and that maker's sub-protocol stands
      inside a link, whatever the gatherer.
  k12_sits             onlineDescription o pol lay KL = .ok F ⇒ ∃ Z N c: pubPlain o … = .ok Z ·
      placesOfMade Z.made = .ok N · F = descN o pureRoad.links guardedProximityTestParts Z N c · c.blocksInOrder = pre ++
      firstEntry sameReply J :: l · no other entry of c.blocksInOrder bears the kind K12 · FirstJ (pL N) J.
      (The two later flat lists: descN_shared | descN_second; no other entry there: descN_only.)
  k12_instance         THE INSTANCE: the same, and for every instance and three views: where F
      accepts: AtCut at all four places (at G_omega's where the plan has that test).
LIMITS. X (the law's letters) is free. WHAT AN ACCEPTING RUN GIVES, NOT AN ERROR BOUND. The key
file's IOP as written in Lean is not looked at.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn)
open H2K.Pub (Letters)

theorem thePure_k12 (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) : K12.lot Z ∈ (ProofFile.pureSeat o Z).lots := by
  simp [ProofFile.pureSeat, ProofFile.onlineFirstChainBlockTables]

/-- K9's lot's maker's sub-protocol stands inside a link. -/
theorem k9_face (Z : ProofFile.Pub) (G : ProofFile.Ground) (a : Place)
    (mk : ProofFile.Gatherer → Block First.S ProofFile.Cl) (g : ProofFile.Gatherer)
    (h : (ProofFile.k9Ninth Z).batch G a = some mk) : (mk g).place ≠ a12 := by
  unfold ProofFile.k9Ninth at h
  dsimp only at h
  split at h
  · obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · cases h
      intro e
      have := congrArg Place.link e
      cases this
    · cases h
  · cases h

/-- AT ProofFile's OWN SEAT no batching's maker's sub-protocol claims the proximity test's place. -/
theorem thePure_noFace (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    NoFaceAt (ProofFile.pureSeat o Z) G := by
  intro L hL a mk g h
  have hL' : L = ProofFile.k9Ninth Z ∨ L.batch = fun _ _ => none := by
    simp only [ProofFile.pureSeat, ProofFile.onlineFirstChainBlockTables, ProofFile.p4Pure, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hL
    rcases hL with (h | h | h | h | h | h | h | h | h | h | h | h | h) | (h | h) <;> subst h <;>
      first
        | exact Or.inl rfl
        | exact Or.inr rfl
  rcases hL' with rfl | hn
  · exact k9_face Z G a mk g h
  · rw [hn] at h
    cases h

/-- **K12_sits, at the proof file's IOP as written in Lean.** -/
theorem k12_sits (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription ProofFile.Inst)
    (hF : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ Z N c B, ProofFile.pubPlain o pol lay KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      F = descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c ∧ ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B ∧
      ∃ pre l J, c.blocksInOrder = pre ++ firstEntry ProofFile.sameReply J :: l ∧
        (∀ E ∈ c.blocksInOrder, E.place.kind = .K12 → E = firstEntry ProofFile.sameReply J) ∧
        FirstJ (pL N) J := by
  obtain ⟨Z, hZ, hF⟩ := ProofFile.Law.descPure_made hF
  obtain ⟨N, c, B, hN, e, hB, h⟩ := pureZ_sits Z (ProofFile.pureSeat o Z) F hF (thePure_k12 o Z)
    (fun B _ => thePure_noFace o Z B.G₀) rfl rfl
  exact ⟨Z, N, c, B, hZ, hN, e, hB, h⟩

/-- **THE INSTANCE**: what an accepting run of the proof file's IOP as written in Lean gives at
all four places of the proximity test: AtCut (the kind's sub-protocol's own step accepts at the
state that the door lays of the run's state; YesAll; GivenAt) at the written cuts. NO PREMISE BUT
onlineDescription's VALUE AND THAT ITS RUN ACCEPTS. -/
theorem k12_instance (X : Letters) (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray)
    (F : FileDescription ProofFile.Inst) (hF : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ Z N c, ProofFile.pubPlain o pol lay KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      F = descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c ∧
      ∀ (x : ProofFile.Inst) (v₁ v₂ v₃ : Fmt.View)
        (e : (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).S₁ ×
          (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).S₂ ×
          (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).S₃),
        (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).runEnd x v₁ v₂ v₃ = .ok e →
        (∃ pre l J leave, c.blocksInOrder = pre ++ firstEntry ProofFile.sameReply J :: l ∧
          FirstOut ProofFile.sameReply (pL N) J leave ∧
          AtCut X (pL N) 0 pre (firstEntry ProofFile.sameReply J) l enterFinish leave
            ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).start₁
              ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).pub x)) e.1 (withEmptySealRound v₁)) ∧
        AtCut X (pGu N) 0 (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N) (guEntry ProofFile.Cl N)
          ((N.O.toList.map fun nO => omegaEntry ProofFile.Cl nO) ++ [sharedEnd ProofFile.Cl (p14N Z N) N])
          (Seat.enter (·.gU) (·.firstMask)) Seat.leave
          ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).start₂
            ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).pub x)) e.2.1 v₂ ∧
        (∀ nO, N.O = some nO →
          AtCut X (pGomega nO) 0
            (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N])
            (omegaEntry ProofFile.Cl nO) [sharedEnd ProofFile.Cl (p14N Z N) N]
            (Seat.enter (·.gOmega) fun _ => none) Seat.leave
            ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).start₂
              ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).pub x)) e.2.1 v₂) ∧
        ∃ s₃, (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).start₃
            ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).pub x) e.1 e.2.1 = .ok s₃ ∧
          AtCut X (pOwn N) (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).lastChainFirstTreeNumber
            (secondPre ProofFile.Cl (p₁₄N Z) (proximityTestKind guardedProximityTestParts (pOwn N) : Blk'))
            (ownEntry ProofFile.Cl (proximityTestKind guardedProximityTestParts (pOwn N) : Blk'))
            [secondEnd ProofFile.Cl (p₁₄N Z) (proximityTestKind guardedProximityTestParts (pOwn N) : Blk')] enterOwn leaveOwn s₃
            e.2.2 v₃ := by
  obtain ⟨Z, N, c, B, hZ, hN, e, _, pre, l, J, hb, _, hJ⟩ := k12_sits o pol lay KL F hF
  refine ⟨Z, N, c, hZ, hN, e, fun x v₁ v₂ v₃ e' h => ⟨?_, ?_, ?_, ?_⟩⟩
  · obtain ⟨leave, a, ho⟩ :=
      descN_atL X o ProofFile.pureRoad.links Z N c ProofFile.sameReply pre l J hb hJ x v₁ v₂ v₃ e' h
    exact ⟨pre, l, J, leave, hb, ho, a⟩
  · exact descN_atU X o ProofFile.pureRoad.links Z N c x v₁ v₂ v₃ e' h
  · exact fun nO hO => descN_atO X o ProofFile.pureRoad.links Z N nO hO c x v₁ v₂ v₃ e' h
  · exact descN_atW X o ProofFile.pureRoad.links Z N c x v₁ v₂ v₃ e' h

end H2K.JointK

#print axioms H2K.JointK.k12_instance
#print axioms H2K.JointK.thePure_noFace
#print axioms H2K.JointK.k12_sits
