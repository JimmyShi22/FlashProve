-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.FirstSeatForm
import Johnson.Desc.K12.Law.SitsBats
import Johnson.Desc.RunLaws
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Loose.H2K12.PlainParts
/-
Johnson/Loose/H2K12/FreeAtSeats.lean: AT THE PROOF FILE's DESCRIPTION, WHERE ITS TESTS ON THE PLAN
PASS: THE PLACE's NUMBER «free» IS THE COUNT OF ROOTS THAT THE BLOCKS IN FRONT OF THE SEAT DECLARE,
AND ITS «start» THE NUMBER OF ROUNDS THAT THEY DECLARE: at the three seats on the two later chains.
An assembly: free_seat (Johnson/Desc/K12/Law/StartOfMade.lean) · the counts of "BAT"
at the written cuts (Law/SitsBats.lean) · «the blocks' rounds in a row are the plan's» (the lemma
FileDescription.planOk_ok: Johnson/Desc/RunLaws.lean) · the description's field «plans» is the public
part's D. BOOK-KEEPING. NO SOUNDNESS IS CLAIMED. NOTHING
ON HIDING.
descN_free's PREMISES PlanLike Z.made AND declPOf Z.made = .ok Z.D ARE PAID WHERE Z IS THE PLAIN
ROAD's (pub_D · pubBy_made | madeOf_planned (MakerPublic.lean) · planLike_of_plain:
H2K12/PlainParts.lean): plain_free: OF THE DESCRIPTION's TESTS ON THE PLAN ALONE, AT EVERY o (the
format's second hash function, a letter throughout). THE FIRST CHAIN's SEAT IS NOT HERE. TWO SMALL
TOOLS HERE HAVE FELLOWS IN OTHER FILES ON K12 (flat_rounds: Law/FileWord.lean's · k12_head: seat_bat
of Law/SeatFree.lean, which is not in this library).
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Made (batsR PlanLike free_seat)

/-- The kind's block's declared rounds begin with a round named "BAT". -/
theorem k12_head {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) :
    ∃ r R, (proximityTestKind X p : Block T Cl).rounds = r :: R ∧ (r.entry.name == "BAT") = true := by
  obtain ⟨_, _, _, R, _, _, e⟩ :=
    H2K.Made.rounds_top p.nums _ (VerifiableInference.Desc.K12.k12_rounds X p hp)
  exact ⟨_, R, e, rfl⟩

theorem flat_rounds {S Cl : Type} (pre : List (Block S Cl)) (B : Block S Cl)
    (l : List (Block S Cl)) :
    (pre ++ B :: l).flatMap (·.rounds) =
      pre.flatMap (·.rounds) ++ (B.rounds ++ l.flatMap (·.rounds)) := by
  rw [List.flatMap_append, List.flatMap_cons]

/-- «free» and «start» at the three later seats. -/
theorem descN_free (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl)
    (hN : H2U.placesOfMade Z.made = .ok N) (hD : Johnson.G.OfPlan.declPOf Z.made = .ok Z.D)
    (hT : PlanLike Z.made) (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true) :
    (((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).flatMap (·.rounds)).length = N.U.start ∧
      N.U.nums.free =
        Johnson.G.OfPlan.rootsOf ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).flatMap (·.rounds))) ∧
    (∀ nO, N.O = some nO →
      ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).flatMap
          (·.rounds)).length = nO.start ∧
        nO.nums.free = Johnson.G.OfPlan.rootsOf
          ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).flatMap (·.rounds))) ∧
    (N.W.start = 0 ∧ N.W.nums.free = Johnson.G.OfPlan.rootsOf []) := by
  have hd := (FileDescription.planOk_ok _).1 hp
  obtain ⟨_, b2, b3⟩ := Keeps.planOk_blocks _ hp
  obtain ⟨fU, fO, fW⟩ := free_seat Z.made N Z.D hT hN hD
  have mU : guEntry ProofFile.Cl N ∈ (descN o mk guardedProximityTestParts Z N c).shared.blocksInOrder :=
    (descN_shared o mk guardedProximityTestParts Z N c) ▸ List.mem_append_right _ List.mem_cons_self
  have pU : (proximityTestKind guardedProximityTestParts (pGu N) : Blk').planOk = true := (guEntry_sits ProofFile.Cl N).plan (b2 _ mU)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨r, R, e, hr⟩ := k12_head guardedProximityTestParts (pGu N) pU
    have e2 : Z.D.2.1 = (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).flatMap (·.rounds) ++
        ((guEntry ProofFile.Cl N).rounds ++ ((N.O.toList.map fun nO => omegaEntry ProofFile.Cl nO) ++
                [sharedEnd ProofFile.Cl (p14N Z N) N]).flatMap (·.rounds)) := by
      rw [← flat_rounds, ← descN_shared o mk guardedProximityTestParts Z N c]
      exact hd.decl₂.symm
    rw [(guEntry_sits ProofFile.Cl N).rounds, e] at e2
    exact fU _ r (R ++ _) e2 hr (sharedPre_bats ProofFile.Cl _ _ N)
  · intro nO hO
    have hc := shared_cut_omega ProofFile.Cl Z.p.chains (p14N Z N) N nO hO
    have mO : omegaEntry ProofFile.Cl nO ∈ (descN o mk guardedProximityTestParts Z N c).shared.blocksInOrder :=
      hc ▸ List.mem_append_right _ List.mem_cons_self
    have pO : (proximityTestKind guardedProximityTestParts (pGomega nO) : Blk').planOk = true :=
      (omegaEntry_sits ProofFile.Cl nO).plan (b2 _ mO)
    obtain ⟨r, R, e, hr⟩ := k12_head guardedProximityTestParts (pGomega nO) pO
    have e2 : Z.D.2.1 =
        (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).flatMap (·.rounds) ++
        ((omegaEntry ProofFile.Cl nO).rounds ++
          [sharedEnd ProofFile.Cl (p14N Z N) N].flatMap (·.rounds)) := by
      rw [← flat_rounds, ← hc]
      exact hd.decl₂.symm
    rw [(omegaEntry_sits ProofFile.Cl nO).rounds, e] at e2
    exact fO nO hO _ r (R ++ _) e2 hr (sharedPreO_bats ProofFile.Cl _ _ N pU)
  · have mW : ownEntry ProofFile.Cl (proximityTestKind guardedProximityTestParts (pOwn N) : Blk') ∈
        (descN o mk guardedProximityTestParts Z N c).second.blocksInOrder :=
      (descN_second o mk guardedProximityTestParts Z N c) ▸ List.mem_append_right _ List.mem_cons_self
    have pW : (proximityTestKind guardedProximityTestParts (pOwn N) : Blk').planOk = true :=
      (ownEntry_sits ProofFile.Cl _).plan (b3 _ mW)
    obtain ⟨r, R, e, hr⟩ := k12_head guardedProximityTestParts (pOwn N) pW
    have e3 : Z.D.2.2 =
        (secondPre ProofFile.Cl (p₁₄N Z) (proximityTestKind guardedProximityTestParts (pOwn N) : Blk')).flatMap (·.rounds) ++
        ((ownEntry ProofFile.Cl (proximityTestKind guardedProximityTestParts (pOwn N) : Blk')).rounds ++
          [secondEnd ProofFile.Cl (p₁₄N Z) (proximityTestKind guardedProximityTestParts (pOwn N) : Blk')].flatMap (·.rounds)) := by
      rw [← flat_rounds, ← descN_second o mk guardedProximityTestParts Z N c]
      exact hd.decl₃.symm
    rw [secondPre_rounds, (ownEntry_sits ProofFile.Cl _).rounds, e] at e3
    have := fW [] r (R ++ _) e3 hr rfl
    exact ⟨this.1.symm, this.2⟩

/-- Where the public part is the plain road's: its D is the plan's declared rounds. -/
theorem pub_D (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (h : ProofFile.pubPlain o pol lay KL = .ok Z) :
    Johnson.G.OfPlan.declPOf Z.made = .ok Z.D := by
  unfold ProofFile.pubPlain ProofFile.pubBy at h
  obtain ⟨m, _, h⟩ := ebind_ok h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨_, _, h⟩ := ebind_ok h
    obtain ⟨D, hD, h⟩ := ebind_ok h
    obtain ⟨_, _, h⟩ := ebind_ok h
    obtain ⟨_, _, h⟩ := ebind_ok h
    obtain ⟨_, _, h⟩ := ebind_ok h
    obtain ⟨_, _, h⟩ := ebind_ok h
    cases h
    exact ProofFile.Law.atCall_ok hD

/-- Where the public part is the plain road's, at every o: the plans as read back are like the
made plans' entries. -/
theorem pub_planLike (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) : PlanLike Z.made :=
  H2K.Made.planLike_of_plain (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
          (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Z from hZ)))

/-- Where onlineDescription is made, at every o: the plans as read back are like the made plans' entries.
-/
theorem descPure_planLike (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription ProofFile.Inst)
    (hF : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ Z, ProofFile.pubPlain o pol lay KL = .ok Z ∧ ProofFile.onlineDescriptionFromPublicPart Z (ProofFile.pureSeat o Z) = .ok F ∧
      PlanLike Z.made := by
  obtain ⟨Z, hZ, h⟩ := ProofFile.Law.descPure_made hF
  exact ⟨Z, hZ, h, pub_planLike o pol lay KL Z hZ⟩

/-- ON THE PLAIN ROAD: «free» and «start» at the three later seats OF THE TESTS ON THE PLAN
ALONE. -/
theorem plain_free (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (Z : ProofFile.Pub)
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z)
    (mk : ProofFile.LinksBy) (N : H2U.Places4) (c : Chain First.S ProofFile.Cl)
    (hN : H2U.placesOfMade Z.made = .ok N) (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true) :
    (((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).flatMap (·.rounds)).length = N.U.start ∧
      N.U.nums.free =
        Johnson.G.OfPlan.rootsOf ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).flatMap (·.rounds))) ∧
    (∀ nO, N.O = some nO →
      ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).flatMap
          (·.rounds)).length = nO.start ∧
        nO.nums.free = Johnson.G.OfPlan.rootsOf
          ((sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N ++ [guEntry ProofFile.Cl N]).flatMap (·.rounds))) ∧
    (N.W.start = 0 ∧ N.W.nums.free = Johnson.G.OfPlan.rootsOf []) :=
  descN_free o mk Z N c hN (pub_D o pol lay KL Z hZ) (pub_planLike o pol lay KL Z hZ) hp

end H2K.JointK

#print axioms H2K.JointK.pub_planLike
#print axioms H2K.JointK.descPure_planLike
#print axioms H2K.JointK.plain_free
#print axioms H2K.JointK.pub_D
#print axioms H2K.JointK.descN_free
