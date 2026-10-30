-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.SeamPlanAtSeats
import Johnson.Desc.K1.Law.Port6
import Johnson.Desc.K1.Law.RowsOn
import Johnson.Desc.K14.Law.Run
import Johnson.Desc.K14.Law.SharesGiven
import Johnson.Desc.K14.Law.SplitGiven
import Johnson.Desc.Sound.FenceK14Named
import Johnson.Desc.PlanPasses
/-
H2K12/TiesAtSeats.lean: `K1.Tie` (Johnson/Desc/K1/Law/Port2.lean) at the codes and at
the shapes of the three oracle messages of the proof file's shared chain (the folded row's, Omega's,
the split's): general, off three of the shared chain's own tests on the list of rounds; at the proof
file's IOP as written in Lean; and at the return of `LPFD.Full.proofDataAndDecisionOfPublicFiles`. Statements and proofs; no
definition.

Why. The seam's joined call at the two shared proximity tests (`tupleNine_sh`, `tupleTen_sh`,
Johnson/Desc/Sound/SeamAtSh.lean [not in the base; not imported here]) takes `K1.Tie` at these
shapes as premises, and they are the three fields that `Second.Seam.Facts`
(Johnson/Second/Seam/PlanFacts.lean [not in the base; not imported here]) has beyond the seven of
`SeamPlan` (H2K12/SeamPlanAtSeats.lean).
Tie's four clauses and what pays each. One answer: `ShapesFull`'s uAns, oAns, sAns
(Johnson/Desc/K12/Law/Sizes/ShapesAtScope.lean). Every code's message length is a power of two: the
test on the list of rounds of the kind's first sub-protocol, "LIN point", asks it (`point_given`,
Johnson/Desc/K14/Law/SharesGiven.lean). The shape is admitted, and the pad fits: the two sendings'
own tests ask them (`plan_shape`, Johnson/Desc/K1/Law/Port6.lean; `plan_msg`, Law/RowsOn.lean).
Main names.
  `planOwn_of_sendAt`, `tie_at`: general, at a sending.
  `ties_of_blocks`: general in P: the kind's eight sub-protocols are there; the first, second and
    fifth pass; a split is needed; one answer at each of the three.
  `blocks_pass_of_pre`: where all that stands in front of the test on G_u passes, the eight are
    there and these three pass.
  `ties_at_desc`: the files are in scope; pubPlain's return; the IOP as written in Lean passes its
    test on the list of rounds: the three at `p14N Z N`.
  `ties_laid`: the files are in scope; proofDataAndDecisionOfPublicFiles … = .ok (D, r): there are Z, N, nO, c with four
    returns and the three. No test is left in front.
  `nine_ten_ties_laid`: the same two premises: `nine_ten_plan_laid`'s conclusion
    (H2K12/SeamPlanAtSeats.lean) and the three, under one «there are». OF THE TEN THE SEVEN STAND IN
    SCOPE ALONE; THE THREE AT THE LAID VALUE ONLY. `facts_laid` (H2K12/SeamPlanFits.lean) lays the
    ten into `Second.Seam.Facts`.
Nearest kin. `cond_tie` (Johnson/Desc/K1/Law/Port6.lean) has Tie off `condPort`, which asks a radius
besides; its proof is the pattern of `tie_at`. `Second.Seam.Facts` is had in its own file from a
test with code, evaluated at stored files: no theorem.
What it is not. THE THREE ARE NOT HAD IN SCOPE ALONE: they spend the test on the list of rounds. It
pays no other premise of the call; it pays no law and closes no row.
NO EXAMPLE: at no files does Lean show that they are in scope and that proofDataAndDecisionOfPublicFiles returns: whether the
premises can be met together is not said here.
No soundness and no level is claimed. Nothing on hiding. No sorry, no axiom of ours;
what each theorem rests on is printed at the file's end.

-/
set_option autoImplicit false
namespace H2K.JointK
open OnBytes OnBytes.Params
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K1 (Tie planOkOwn shapesOf shapeAt sampledAt msgAt plan_shape
  plan_msg)
open _root_.Desc.K14 (St P14 withU withOmega blocks sendAt parK1)
open Johnson.G (writtenPFull)

/-- Where a sending's sub-protocol on the shared chain passes its test on the list of rounds, so
does the sending's own test with the pads. -/
theorem planOwn_of_sendAt (P : P14) (n : String) (Q : VerifiableInference.Desc.K1.Par)
    (inFront : Option Fmt.Entry) (groups : List (List Nat))
    (behind : St → Array Nat → Option St)
    (h : (sendAt P n Q inFront groups behind).planOk = true) : planOkOwn Q = true := by
  simp only [sendAt, VerifiableInference.Desc.Block.inside, VerifiableInference.Desc.K1.sendOwn,
    Bool.and_eq_true] at h
  exact h.1.1.1.1

/-- General, at a sending: the sending's own test, the codes' lengths, and one answer at a message
that it sends. `cond_tie`'s pattern (Johnson/Desc/K1/Law/Port6.lean) without `condPort`. -/
theorem tie_at (Q : VerifiableInference.Desc.K1.Par) (hB : planOkOwn Q = true)
    (hl : Q.codes.lengthsOk = true) (k : ℕ) (n : OracleNotice) (hn : Q.sent[k]? = some n)
    (h1 : n.shape.answers = 1) : Tie Q.codes n.shape := by
  have hs : (shapesOf Q)[k]? = some n.shape := by
    unfold shapesOf
    rw [List.getElem?_map, Array.getElem?_toList, hn]
    rfl
  obtain ⟨hk, e⟩ := List.getElem?_eq_some_iff.1 hs
  have e' : shapeAt Q ⟨k, hk⟩ = n.shape := e
  have hsm : sampledAt Q ⟨k, hk⟩ := by
    show (VerifiableInference.Desc.K1.Msg.of Q.codes (shapesOf Q)[k]).answers ≠ 0
    rw [e]
    show n.shape.answers ≠ 0
    omega
  have a := plan_shape Q hB ⟨k, hk⟩
  have b := (plan_msg Q hB ⟨k, hk⟩ hsm).2
  rw [e'] at a
  have b' : (VerifiableInference.Desc.K1.Msg.of Q.codes n.shape).padFits = true := by
    have : msgAt Q ⟨k, hk⟩ = VerifiableInference.Desc.K1.Msg.of Q.codes n.shape := by
      show VerifiableInference.Desc.K1.Msg.of Q.codes (shapesOf Q)[k] = _
      rw [e]
    rw [← this]
    exact b
  exact ⟨h1, hl, a, b'⟩

/-- ★ **The three, off three of the kind's eight tests on the list of rounds**, general in P. -/
theorem ties_of_blocks (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (h1 : b1.planOk = true)
    (h2 : b2.planOk = true) (h5 : b5.planOk = true) (hS : P.S.sharedSplitNeeded = true)
    (aU : P.S.fold.u.answers = 1) (aO : P.S.omega.answers = 1)
    (aS : P.S.sharedSplit.answers = 1) :
    Tie P.codes P.S.fold.u ∧ Tie P.codes P.S.omega ∧ Tie P.codes P.S.sharedSplit := by
  have hl : P.codes.lengthsOk = true := by
    have p := (_root_.Desc.K14.Law.point_given P b1 b2 b3 b4 b5 b6 b7 b8 hbl h1).1
    unfold VerifiableInference.OnPublicFiles.OkD.At.linPoint at p
    simp only [Bool.and_eq_true] at p
    exact p.1.1.1.2
  obtain ⟨sentU, hU, e2, e5⟩ := _root_.Desc.K14.Law.Fence.blocks_two P b1 b2 b3 b4 b5 b6 b7 b8 hbl
  rw [e2] at h2
  rw [e5] at h5
  have B2 := planOwn_of_sendAt P _ _ _ _ _ h2
  have B5 := planOwn_of_sendAt P _ _ _ _ _ h5
  obtain ⟨nU, hnU, sU⟩ := _root_.Desc.K14.Law.withU_first P.S sentU hU
  have hO : withOmega P.S =
      #[⟨P.S.omega, P.S.omegaLeafClass⟩, ⟨P.S.sharedSplit, P.S.sharedSplitLeafClass⟩] := by
    unfold withOmega linMessageOmega
    simp [hS]
  refine ⟨?_, ?_, ?_⟩
  · have t := tie_at (parK1 P 2 "o_u and the first mask" sentU) B2 hl 0 nU
      (by rw [_root_.Desc.K14.Law.parK1_sent]; exact hnU) (by rw [sU]; exact aU)
    rw [sU] at t
    exact t
  · exact tie_at (parK1 P 5 "o_omega and o_sp" (withOmega P.S)) B5 hl 0
      ⟨P.S.omega, P.S.omegaLeafClass⟩ (by rw [_root_.Desc.K14.Law.parK1_sent, hO]; rfl) aO
  · exact tie_at (parK1 P 5 "o_omega and o_sp" (withOmega P.S)) B5 hl 1
      ⟨P.S.sharedSplit, P.S.sharedSplitLeafClass⟩
      (by rw [_root_.Desc.K14.Law.parK1_sent, hO]; rfl) aS

/-- Where all that stands in front of the test on G_u passes its test on the list of rounds, the
kind's eight sub-protocols are there and the first, the second and the fifth pass theirs. -/
theorem blocks_pass_of_pre (Cl' : Type) (c : OnBytes.Model.Verify.Chains) (P : P14)
    (N : H2U.Places4) (h : ∀ b ∈ sharedPre Cl' c P N, b.planOk = true) :
    ∃ b1 b2 b3 b4 b5 b6 b7 b8, blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8] ∧
      b1.planOk = true ∧ b2.planOk = true ∧ b5.planOk = true := by
  have own : ∀ b ∈ _root_.Desc.K14.blocksOr P, b.planOk = true := by
    intro b hb
    have m : (b.retype (Cl' := Cl')).asBare ∈ sharedPre Cl' c P N :=
      List.mem_cons_of_mem _ (List.mem_map_of_mem hb)
    have k : ((b.planOk && b.claims.isEmpty) && (b.retype (Cl' := Cl')).hasNoClaimsAndNothingAfter) = true := h _ m
    simp only [Bool.and_eq_true] at k
    exact k.1.1
  cases hb : blocks P with
  | none =>
    unfold _root_.Desc.K14.blocksOr at own
    rw [hb] at own
    have k : false = true := own _ (List.mem_singleton.2 rfl)
    cases k
  | some l =>
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := _root_.Desc.K14.Law.eight P l hb
    unfold _root_.Desc.K14.blocksOr at own
    rw [hb] at own
    exact ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl, own b1 (by simp), own b2 (by simp),
      own b5 (by simp)⟩

/-- ★★ At the proof file's IOP as written in Lean, in the goals' scope, where it passes its test on
the list of rounds. -/
theorem ties_at_desc {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope S = true)
    (Z : ProofFile.Pub) (hZ : ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z) (mk : ProofFile.LinksBy)
    (N : H2U.Places4) (c : VerifiableInference.Desc.Chain First.S ProofFile.Cl)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true) :
    Tie (p14N Z N).codes (p14N Z N).S.fold.u ∧ Tie (p14N Z N).codes (p14N Z N).S.omega ∧
      Tie (p14N Z N).codes (p14N Z N).S.sharedSplit := by
  obtain ⟨_, h2, _⟩ := VerifiableInference.Desc.Keeps.planOk_blocks _ hp
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hbl, p1, p2, p5⟩ :=
    blocks_pass_of_pre ProofFile.Cl Z.p.chains (p14N Z N) N fun b hb =>
      h2 b ((descN_shared o mk guardedProximityTestParts Z N c) ▸ List.mem_append_left _ hb)
  have F := H2K.Sizes.shapes_in_scope hS hZ
  exact ties_of_blocks (p14N Z N) b1 b2 b3 b4 b5 b6 b7 b8 hbl p1 p2 p5 F.split F.uAns F.oAns
    F.sAns

/-- ★★★ At proofDataAndDecisionOfPublicFiles's return: the letters and the four returns are firstTie_laid's. -/
theorem ties_laid (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true) (o : ProofFile.SecondHashFunctionArgument)
    (D : WholeD) (r : LPFD.Full.RunPF)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) :
    ∃ Z N nO c, ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      N.O = some nO ∧
      ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) ∧
      Tie (p14N Z N).codes (p14N Z N).S.fold.u ∧ Tie (p14N Z N).codes (p14N Z N).S.omega ∧
      Tie (p14N Z N).codes (p14N Z N).S.sharedSplit := by
  obtain ⟨F, hF, hp, _, hs, _⟩ := LPFD.Full.laidPOf_ok hL
  have hpin := LPFD.asks_written hs
  obtain ⟨Z, N, c, _, hZ, hN, rfl, _⟩ := k12_sits o S.pol S.lay S.KL F hF
  obtain ⟨nO, hO⟩ := omega_some_in_scope hS Z _ N c hp hpin
  exact ⟨Z, N, nO, c, hZ, hN, hO, hF, ties_at_desc hS Z hZ _ N c hp⟩

/-- ★★★ At proofDataAndDecisionOfPublicFiles's return, under one «there are»: what the shared chain's ledger asks of the list
of rounds and of the piece at the two tests, the seven of `SeamPlan`, and the three. -/
theorem nine_ten_ties_laid (W : Type) (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true)
    (o : ProofFile.SecondHashFunctionArgument) (D : WholeD) (r : LPFD.Full.RunPF)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) :
    ∃ Z N nO c, ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      N.O = some nO ∧
      ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) ∧
      D = writtenPFull ∧ dField = writtenPFull ∧
      r = (seatedAt o ProofFile.pureRoad.links Z N c LPFD.Full.instanceAsPlainRecord).run ∧
      NineAtGu W o ProofFile.pureRoad.links Z N c LPFD.Full.instanceAsPlainRecord ∧
      TenAtGomega W o ProofFile.pureRoad.links Z N nO c LPFD.Full.instanceAsPlainRecord ∧
      (∃ sentU layU layO, SeamPlan (p14N Z N) sentU layU layO) ∧
      Tie (p14N Z N).codes (p14N Z N).S.fold.u ∧ Tie (p14N Z N).codes (p14N Z N).S.omega ∧
      Tie (p14N Z N).codes (p14N Z N).S.sharedSplit := by
  obtain ⟨F, hF, hp, hD, hs, hr⟩ := LPFD.Full.laidPOf_ok hL
  have hpin := LPFD.asks_written hs
  obtain ⟨Z, N, c, _, hZ, hN, rfl, _⟩ := k12_sits o S.pol S.lay S.KL F hF
  obtain ⟨nO, hO⟩ := omega_some_in_scope hS Z _ N c hp hpin
  obtain ⟨ha, hD'⟩ := Coin.depth_in_scope _ S hS hpin
  obtain ⟨sentU, layU, layO, h⟩ := seamPlan_in_scope hS hZ
  exact ⟨Z, N, nO, c, hZ, hN, hO, hF, Except.ok.inj (hD.symm.trans hD'),
    Coin.at_of_depth _ _ (ha.trans (Coin.data_depth _ _ _ hD').symm), hr,
    nine_facts_at_Gu W o S hS Z hZ _ N c hN hp hpin _,
    ten_facts_at_Gomega W o S hS Z hZ _ N nO hO c hN hp hpin _, ⟨sentU, layU, layO, h N⟩,
    ties_at_desc hS Z hZ _ N c hp⟩
end H2K.JointK

#print axioms H2K.JointK.planOwn_of_sendAt
#print axioms H2K.JointK.tie_at
#print axioms H2K.JointK.ties_of_blocks
#print axioms H2K.JointK.blocks_pass_of_pre
#print axioms H2K.JointK.ties_at_desc
#print axioms H2K.JointK.ties_laid
#print axioms H2K.JointK.nine_ten_ties_laid
