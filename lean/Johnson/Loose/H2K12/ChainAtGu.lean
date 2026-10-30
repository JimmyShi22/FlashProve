-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.Laid.ProofFullScope
import Johnson.Loose.H2K12.ClosedAtSeats
import Johnson.Loose.H2K12.SitsAtDescPure
import Johnson.Desc.K12.Law.AtCutWith
import Johnson.Desc.K12.Law.PubOfStep
/-
Johnson/Loose/H2K12/ChainAtGu.lean: «THE CHAIN AT G_u»: THE PROXIMITY TEST AT ⟨2, none, 9, .K12⟩, AT THE FULL SIZE, AT EVERY THREE PUBLIC FILES IN THE GOALS' SCOPE, FROM THE VALUE THAT IS LAID FOR THE PROOF FILE: A JOIN OF WHAT LIES: no new mathematics. Statements and proofs. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  atCut_pub: AtCut, and the kind's block's test on the plan ⇒ AtCutWith at Φ := «the plan's count of roots in front is the record's ∧ pubOk at the record's codes»: guards (f) and (p) AT THE RUN's OWN RECORD, inside AtCut's own «there is».
  run_at_Gu: onlineDescription's yes and the description's test on the plan ⇒ the letters Z N c, each a return's, and at every yes of the description's run: that AtCutWith at G_u's seat.
  chain_at_Gu: InScope S · LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r) ⇒ ∃ F Z N c, ‹eight equations: five pin them; D is F's own data; F's test on the plan says yes; the seat's pin says yes (the forms with these two are chain_at_Gu_pins | chain_at_Gu_run_pins; chain_at_Gu | chain_at_Gu_run stand to the letter, six equations, as corollaries)› ∧ (PUBLIC) ∧ (THE RUN).
    (PUBLIC; no run, no record, no codes): ClosedL (pGu N) rUFull 1 0 0 TUFull · rUFull is the planner's radius at each stage · at all t₁ t₂ a more key: SeatGameVAt (the game at every seat, nothing promised of the record) · at every num: CountsAre (the chain is there) and the two comparisons at 2⁻¹ ^ 128.
    (THE RUN): run_at_Gu's.
  chain_at_Gu_run: the same with (THE RUN) AT THE LAID DECISION ITSELF: r z v₁ v₂ v₃ = true ⇒ the description's run returns its ends at instanceAsPlainRecord z, and AtCutWith … there (FileDescription.pull_run; runEnd_of_run: run is runEnd's isOk: by cases; another kind's law file has the like in general: K1/Law/When.lean's isOk_iff: not imported for five lines).
WHERE: links 1 | 2: laidPOf_ok · asks_written (Johnson/Desc/Laid/ProofFullLaw.lean · ProofAsksLaw.lean) · the letters and AtCut: k12_instance (H2K12/SitsAtDescPure.lean) and AtCutWith (Law/AtCutWith.lean) · (PUBLIC), WHOLE: closedL_in_scope_U · gameV_in_scope_U · numbers_in_scope_U · plan_at_seat_U (H2K12/ClosedAtSeats.lean), over ClosedL and k12_gameSeatV · pub_of_step (Law/PubOfStep.lean) over k12_guards.
WHAT IT IS NOT: A CONJUNCTION OF A LAW AND A RUN's FACTS AT ONE PLACE: NOT A BOUND ON ANYTHING THAT THE FILE's GAME COUNTS: (a) the law is said of the piece pieceOf … ((proximityTestKind …).inside enter leave) at letters t₁ t₂ a more key: that the file's own piece is alike to it, with its base, rounds and counts, is shown by nobody: D, the data that the file's game reads, is tied to F by one equation and to the law's letters by nothing · (b) the game's conclusion numbers the book's places by their trees' labels: it reaches the file's oracles only where the book is in order at the record behind the door in (qn_places_of_labels): not shown here · one round's share each, no sum · G_u's seat alone · no member: nothing here shows that proofDataAndDecisionOfPublicFiles says yes at any files in scope.
ALSO: (PUBLIC)'s third conjunct, SeatGameVAt, CONCLUDES IN «Leads»: the form for ONE statement; the file's rule asks of the shared chain the form with a key (LeadsK | LeadsBN): its heir is Coin/ReadsKey.lean's gameK_… and H2K12/GameKAtGu.lean · X : Letters is free and stands in AtCutWith's YesAll alone.

-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin (ClosedL SeatGameVAt CountsAre εAt)
open VerifiableInference.Desc.K12.Coin.At (TUFull)
open H2K.Member (rUFull dBAt)
open H2K.Pub (Letters radBy sgOf batV0 pubOk)
open OnBytes.Maker (LeftT WholeD)
open scoped ENNReal

/-- What guards (f) and (p) say of the record behind the door in. -/
def PubAt (p : P12) {S : Type} : S → T12 → Prop :=
  fun _ t0 => p.nums.free = t0.roots ∧ pubOk p t0.st.codes = true

/-- **Guards (f) and (p) at the run's own record.** -/
theorem atCut_pub {X : Letters} {p : P12} {ft : ℕ} {S Cl : Type} {pre : List (Block S Cl)}
    {B : Block S Cl} {l : List (Block S Cl)} {enter : S → Except String T12}
    {leave : S → T12 → Except String S} {s s' : S} {v : Fmt.View}
    (hp : (proximityTestKind guardedProximityTestParts p : Blk').planOk = true)
    (h : AtCut X p ft pre B l enter leave s s' v) :
    AtCutWith X p ft pre B l enter leave s s' v (PubAt p) :=
  atCutWith_of h fun _ t0 _ _ cols tE n _ _ _ hstep => pub_of_step p hp ft t0 tE _ cols n hstep

/-- What a yes of the description's run gives at G_u's seat. -/
def RunAtGu (X : Letters) (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) : Prop :=
  ∀ (x : ProofFile.Inst) (v₁ v₂ v₃ : Fmt.View)
    (e : (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).S₁ ×
      (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).S₂ ×
      (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).S₃),
    (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).runEnd x v₁ v₂ v₃ = .ok e →
    AtCutWith X (pGu N) 0 (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N) (guEntry ProofFile.Cl N)
      ((N.O.toList.map fun nO => omegaEntry ProofFile.Cl nO) ++ [sharedEnd ProofFile.Cl (p14N Z N) N])
      (Seat.enter (·.gU) (·.firstMask)) Seat.leave
      ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).start₂
        ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).pub x)) e.2.1 v₂ (PubAt (pGu N))

theorem run_at_Gu (X : Letters) (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray)
    (F : FileDescription ProofFile.Inst) (hF : ProofFile.onlineDescription o pol lay KL = .ok F) (hp : F.planOk = true) :
    ∃ Z N c, ProofFile.pubPlain o pol lay KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      F = descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c ∧ RunAtGu X o Z N c := by
  obtain ⟨Z, N, c, hZ, hN, e, h⟩ := k12_instance X o pol lay KL F hF
  subst e
  exact ⟨Z, N, c, hZ, hN, rfl, fun x v₁ v₂ v₃ e' he =>
    atCut_pub (plan_at_seat_U o Z _ N c hp) (h x v₁ v₂ v₃ e' he).2.1⟩

/-- The public half at G_u's seat. -/
def PublicAtGu (Z : ProofFile.Pub) (N : H2U.Places4) : Prop :=
  ClosedL (pGu N) rUFull 1 0 0 TUFull ∧
  (∀ a ∈ N.U.nums.stages, radBy Z.made.p.chains.made.sized.proof.set
    Z.made.p.chains.made.sized.proof.batch.folded.stages (sgOf a) = rUFull a) ∧
  (∀ (t₁ t₂ a : ℕ) (more : List LeftT) (key : ℕ → ℕ),
    SeatGameVAt (pGu N) rUFull 1 TUFull t₁ t₂ a more key) ∧
  ∀ num : Fmt.TreeSource → ℕ,
    CountsAre num (pGu N) rUFull ∧ Iop.Err.Below (εAt num (pGu N) rUFull) ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧
      OnBytes.Slice.RoundBelow (batV0 (pGu N) rUFull) (OnBytes.Flat.toRD (dBAt num (pGu N)))
        ((2 : ℝ≥0∞)⁻¹ ^ 128)

/-- **THE CHAIN AT G_u.** -/
theorem chain_at_Gu_pins (X : Letters) (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true)
    (o : ProofFile.SecondHashFunctionArgument) (D : WholeD) (r : _)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) :
    ∃ F Z N c, ProofFile.onlineDescription o S.pol S.lay S.KL = .ok F ∧ r = (F.pull LPFD.Full.instanceAsPlainRecord).run ∧
      F.data "proof file" = .ok D ∧ F.planOk = true ∧
      VerifiableInference.PlanWritten.seatPinnedProof S.pol F = true ∧
      ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      F = descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c ∧ PublicAtGu Z N ∧ RunAtGu X o Z N c := by
  obtain ⟨F, hF, hp, hD, hs, hr⟩ := LPFD.Full.laidPOf_ok hL
  have hpin := LPFD.asks_written hs
  obtain ⟨Z, N, c, hZ, hN, e, hrun⟩ := run_at_Gu X o S.pol S.lay S.KL F hF hp
  subst e
  obtain ⟨c1, c2⟩ := closedL_in_scope_U hS Z hZ _ N c hN hp hpin
  exact ⟨_, Z, N, c, hF, hr, hD, hp, hpin, hZ, hN, rfl,
    ⟨c1, c2, fun t₁ t₂ a more key => gameV_in_scope_U hS Z hZ _ N c hN hp hpin t₁ t₂ a more key,
      fun num => numbers_in_scope_U hS Z hZ _ N c hN hp hpin num⟩, hrun⟩

/-- A yes of a description's decision is a return of its run. -/
theorem runEnd_of_run {Xi : Type} (F : FileDescription Xi) (x : Xi) (v₁ v₂ v₃ : Fmt.View)
    (h : F.run x v₁ v₂ v₃ = true) : ∃ e, F.runEnd x v₁ v₂ v₃ = .ok e := by
  unfold FileDescription.run at h
  cases he : F.runEnd x v₁ v₂ v₃ with
  | ok e => exact ⟨e, rfl⟩
  | error _ =>
    rw [he] at h
    cases h

/-- **THE CHAIN AT G_u, AT THE LAID DECISION ITSELF**: (THE RUN) from «r z v₁ v₂ v₃ = true». -/
theorem chain_at_Gu_run_pins (X : Letters) (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true)
    (o : ProofFile.SecondHashFunctionArgument) (D : WholeD) (r : _)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) :
    ∃ Z N c, ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) ∧
      (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).data "proof file" = .ok D ∧
      (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).planOk = true ∧
      VerifiableInference.PlanWritten.seatPinnedProof S.pol
        (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) = true ∧ PublicAtGu Z N ∧
      ∀ z (v₁ v₂ v₃ : Fmt.View), r z v₁ v₂ v₃ = true →
        ∃ e, (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).runEnd (LPFD.Full.instanceAsPlainRecord z) v₁ v₂ v₃ =
            .ok e ∧
          AtCutWith X (pGu N) 0 (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N) (guEntry ProofFile.Cl N)
            ((N.O.toList.map fun nO => omegaEntry ProofFile.Cl nO) ++ [sharedEnd ProofFile.Cl (p14N Z N) N])
            (Seat.enter (·.gU) (·.firstMask)) Seat.leave
            ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).start₂
              ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).pub (LPFD.Full.instanceAsPlainRecord z))) e.2.1 v₂
            (PubAt (pGu N)) := by
  obtain ⟨F, Z, N, c, hF, hr, hD, hp, hpin, hZ, hN, e, hP, hR⟩ := chain_at_Gu_pins X S hS o D r hL
  subst e
  subst hr
  refine ⟨Z, N, c, hZ, hN, hF, hD, hp, hpin, hP, fun z v₁ v₂ v₃ hy => ?_⟩
  obtain ⟨e, he⟩ := runEnd_of_run _ (LPFD.Full.instanceAsPlainRecord z) v₁ v₂ v₃
    ((FileDescription.pull_run LPFD.Full.instanceAsPlainRecord _ z v₁ v₂ v₃).symm.trans hy)
  exact ⟨e, he, hR _ v₁ v₂ v₃ e he⟩

/-- **THE CHAIN AT G_u.** -/
theorem chain_at_Gu (X : Letters) (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true)
    (o : ProofFile.SecondHashFunctionArgument) (D : WholeD) (r : _)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) :
    ∃ F Z N c, ProofFile.onlineDescription o S.pol S.lay S.KL = .ok F ∧ r = (F.pull LPFD.Full.instanceAsPlainRecord).run ∧
      F.data "proof file" = .ok D ∧ ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      F = descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c ∧ PublicAtGu Z N ∧ RunAtGu X o Z N c := by
  obtain ⟨F, Z, N, c, hF, hr, hD, _, _, hZ, hN, e, hP, hR⟩ := chain_at_Gu_pins X S hS o D r hL
  exact ⟨F, Z, N, c, hF, hr, hD, hZ, hN, e, hP, hR⟩

/-- **THE CHAIN AT G_u, AT THE LAID DECISION ITSELF**: (THE RUN) from «r z v₁ v₂ v₃ = true». -/
theorem chain_at_Gu_run (X : Letters) (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true)
    (o : ProofFile.SecondHashFunctionArgument) (D : WholeD) (r : _)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) :
    ∃ Z N c, ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) ∧
      (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).data "proof file" = .ok D ∧ PublicAtGu Z N ∧
      ∀ z (v₁ v₂ v₃ : Fmt.View), r z v₁ v₂ v₃ = true →
        ∃ e, (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).runEnd (LPFD.Full.instanceAsPlainRecord z) v₁ v₂ v₃ =
            .ok e ∧
          AtCutWith X (pGu N) 0 (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N) (guEntry ProofFile.Cl N)
            ((N.O.toList.map fun nO => omegaEntry ProofFile.Cl nO) ++ [sharedEnd ProofFile.Cl (p14N Z N) N])
            (Seat.enter (·.gU) (·.firstMask)) Seat.leave
            ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).start₂
              ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).pub (LPFD.Full.instanceAsPlainRecord z))) e.2.1 v₂
            (PubAt (pGu N)) := by
  obtain ⟨Z, N, c, hZ, hN, hF, hD, _, _, hP, hR⟩ := chain_at_Gu_run_pins X S hS o D r hL
  exact ⟨Z, N, c, hZ, hN, hF, hD, hP, hR⟩

end H2K.JointK

#print axioms H2K.JointK.atCut_pub
#print axioms H2K.JointK.run_at_Gu
#print axioms H2K.JointK.chain_at_Gu
#print axioms H2K.JointK.chain_at_Gu_run
#print axioms H2K.JointK.chain_at_Gu_pins
#print axioms H2K.JointK.chain_at_Gu_run_pins
