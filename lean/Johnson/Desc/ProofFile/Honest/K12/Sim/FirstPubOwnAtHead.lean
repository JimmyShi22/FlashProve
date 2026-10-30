-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/FirstPubOwnAtHead.lean: under the library's head (`P5J.AtMg`,
Johnson/P5J/AtMg.lean), at the job `jobAtOmega` (JobShared.lean) at the proof file's own plan and
the seated place of the proximity test on G_omega, whose first fold sends its own fresh table: the
public premise `FirstPubOwn` (Sim/ExactFirstOwn.lean) of the sentence `exact_first_own` holds; the
side that is taken off the shared list of the proof file's own description (`testSide`,
Sim/Row.lean, at `(P5J.F0T o Zp Np cF).shared.blocksInOrder`) is there, passes the frame's test on sides, and
has the two members that are written out; and at the first of them the sentence `ExactMember` holds
at the side's own `testOn` and `testBud`. It is Sim/FirstPubAtHead.lean and Sim/FirstSeatAtHead.lean
at the other test. It imports Mathlib.

  `formPubB_O`, `enough_O`, `tabB_O`, `points_O`, `count_OFull`   five facts on the written place
                 `piOFull` (Johnson/Desc/K12/Law/PlacesFull.lean), evaluated by Lean's kernel;
                 `tabB` at the flag "the first fold sends its own table"
  `exact_bud`, `budBoth_of_testBud`   the sentence goes over to a bound that asks at least as much
                 at the member's number; at the first member `testBud` asks what `budBoth` asks
  `row_at_head`, `omega_of_four`, `omega_head`   the description is `descN`; the place that `fourOf`
                 (AtProof/Places.lean) gives is the library's `pGomega`; there is one
  `nums_head_O`, `planOk_head_O`, `thin_head_O`, `count_head_O`   the seated place has the written
                 place's seven numbers; its block passes its test on the plan
  `firstPubOwn_head`, `exact_first_own_head`   the public premise; the sentence at every face, side
                 and On, at the bound `budBoth`
  `find_at_O`, `find_gomega`, `seat_head_O`, `seated_head_O`   the side off the description's own
                 list: it is there at every list of falls; `fits`; the two members; the sentence

By what. The library's `k12_sits_row` (Johnson/Loose/H2K12/SitsRow.lean), `omega_some_in_scope`
(OmegaIsSome.lean), `nums_in_scope_O` and `plan_at_seat_O` (ClosedAtSeats.lean), `closed_OFull`
(Johnson/Desc/K12/Coin/LawAtFull.lean), `guEntry_place`, `omegaEntry_place`
(Johnson/Desc/K12/Law/SharedPlaces.lean). Of Johnson/Desc/ProofFile/Honest/K12/: `thin_of_planOk`,
`formPubB_congr`, `length_congr`, `tabB_congr` (Sim/FirstPubAtHead.lean) and `fits_of`
(Sim/FirstSeatAtHead.lean), which are general in the place; `members_of_seat` (Sim/ExactSide.lean);
`zip_laid` (PlaysK12.lean); one call of `exact_first_own`. `formPubB_O` and `tabB_O` are evaluated
under `set_option maxRecDepth 100000`, as their likes in Sim/FirstPubAtHead.lean are.

The 0 in `⟨K1.qAt Zp Np, 0⟩` is the field `atPoint` of `SendPub`
(Johnson/Desc/ProofFile/Honest/K14/Sendings.lean): the number, among the shared chain's rounds, of
"LIN point", by which a sender's vector is computed; `jobAtOmega` hands that record to `jobOmega`
(there), of which both members' rows are made. It is compared with nothing here, and nothing here
says that 0 is that number at this plan.

Limits.
- One member of a side's two: it is not the frame's field `exact` at that side, which speaks of
  every member. No sentence is shown at the side's second member.
- The state on entry is any function here, and nothing says that it is the verifier's state. At this
  test that weighs more than at the test on G_u: a part is handed no opened column, and the blocks
  in front of this test have read columns that the test on G_u opened; so `doorOf` (JobShared.lean,
  Limits) returns its fall-back there at every honest run. With such a state function the statement
  is a law on this text, at a state that is made of the plan's public part and is not shown to be
  the verifier's. The law beneath (`own_law`, Sim/ExactFirstOwnLaw.lean) holds at every claim's row.
- It is shown at no job that is played: that a job which somebody lays is this one is up to whoever
  lays it.
- It speaks of the parts of `proverSideOfProximityTest` (Parts.lean), not of halves with a guard in front.
- The parts and their random values are defined in Test.lean, Parts.lean and Coins.lean of
  Johnson/Desc/ProofFile/Honest/K12/. What the parts send is that folder's own `testAll`; how far it
  is tied to the library's `bodyAll` (Johnson/Prover/Link/BodyAll.lean) is said in the limits of
  Test.lean.
- `testOn` asks nothing at the first member. `testBud` does ask here: its first clause, `budFirst`
  (Sim/Row.lean): the positions asked of the fold's own tree are in range and at most Z.r different
  ones. In this arm that bound is a premise that is spent, and it is shown at no list of positions
  that the frame lays: not for the test's own first reading round, and not for the rest of the file:
  that no other round reads that tree is shown by nobody.
- By the book the coefficients and the tails that this member samples are meant to be carried by the
  test's second part. No theorem says that a book deals them so, and nothing here joins the two
  members.
- At Z.r different positions as many field elements are shown as are sampled. That is a count; that
  fewer random values would not do is no theorem here.
- No stand, front, challenges or positions at which the sentence's own hypotheses hold are written
  here; Sim/MeetsOwnAtHead.lean has them at this size, under the head, at written letters
  (`meets_head_O`).
- The full size alone. No example of the head is shown here.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactFirstOwn
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstSeatAtHead
import Johnson.Loose.H2K12.OmegaIsSome

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (Block Place K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St)
open H2K.Member (piOFull)
open H2K.JointK (descN laidOf guEntry omegaEntry pGomega)
open ProofFile.Honest.Small (ExactMember)
open ProofFile.Honest.K12.AtProof (fourOf)

/-! ## 1 At the written place -/

set_option maxRecDepth 100000 in
theorem formPubB_O : formPubB piOFull = true := by decide +kernel

theorem enough_O : firstLen piOFull.nums.stages ≤ (laidOf piOFull).length := by decide +kernel

set_option maxRecDepth 100000 in
theorem tabB_O : tabB piOFull true = true := by decide +kernel

theorem points_O : (piOFull.nums.stages.headD default).Z.a ≤ 32 := by decide +kernel

theorem count_OFull : (laidOf piOFull).length =
    firstLen piOFull.nums.stages + restLen piOFull.nums.stages := by decide +kernel

/-! ## 2 A bound that asks more -/

variable {S Cl V W X Pb : Type}

/-- The sentence goes over to a bound that, at the member's number, asks at least as much. -/
theorem exact_bud {φ : Face V W Pb} {σ : Side S Cl V W X Pb} {chain firstTree : ℕ}
    {On : (u : Member V W X Pb) → CsAll u.part.carries → ProofFile.Honest.Mid W X → Before → Prop}
    {bud bud' : ℕ → List Fmt.Drawn → List (List (List ℕ)) → Prop} {u : Member V W X Pb}
    (hb : ∀ ds asks, bud' u.number ds asks → bud u.number ds asks)
    (H : ExactMember φ σ chain firstTree On bud u) : ExactMember φ σ chain firstTree On bud' u :=
  fun ca m front ds asks h1 h2 h3 h4 => H ca m front ds asks h1 h2 h3 (hb ds asks h4)

/-- At the first member `testBud` (Sim/Row.lean) asks what `budBoth` (Sim/ExactFirstOwn.lean) asks.
-/
theorem budBoth_of_testBud (Js : SimJob Pb) (ds : List Fmt.Drawn) (asks : List (List (List ℕ)))
    (h : testBud Js 0 ds asks) : budBoth Js 0 ds asks :=
  ⟨h.1, fun e => absurd e (by decide)⟩

/-! ## 3 Under the head: the place -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- Under the head the proof file's description is `descN`, with the library's facts on where the
proximity tests sit, its test on the plan, and its test on the written list. -/
theorem row_at_head (h : P5J.AtMg o Z D r Zp Np cF) :
    ∃ c', P5J.F0T o Zp Np cF = descN o ProofFile.pureRoad.links guardedProximityTestParts Zp Np c' ∧
      H2K.JointK.RowK12 o ProofFile.pureRoad.links Zp Np c' ∧
      (descN o ProofFile.pureRoad.links guardedProximityTestParts Zp Np c').planOk = true ∧
      VerifiableInference.PlanWritten.seatPinnedProof Z.pol
        (descN o ProofFile.pureRoad.links guardedProximityTestParts Zp Np c') = true := by
  obtain ⟨Z', N', c', hZ', hN', e, R⟩ :=
    H2K.JointK.k12_sits_row o Z.pol Z.lay Z.KL _ h.laid.value
  have eZ : Z' = Zp := Except.ok.inj (hZ'.symm.trans h.laid.pub)
  subst eZ
  have eN : N' = Np := Except.ok.inj (hN'.symm.trans h.laid.places)
  subst eN
  refine ⟨c', e, R, ?_, ?_⟩
  · rw [← e]
    exact h.laid.planOk
  · rw [← e]
    exact LPFD.asks_written h.laid.asks

/-- The place that `fourOf` gives for the test on G_omega is the library's `pGomega`. -/
theorem omega_of_four {N : H2U.Places4} {pO : P12} (hO : (fourOf N).O = some pO) :
    ∃ nO, N.O = some nO ∧ pO = pGomega nO := by
  obtain ⟨nO, h1, h2⟩ := Option.map_eq_some_iff.1 hO
  exact ⟨nO, h1, h2.symm⟩

/-- Under the head there is such a place. -/
theorem omega_head (h : P5J.AtMg o Z D r Zp Np cF) : ∃ pO, (fourOf Np).O = some pO := by
  obtain ⟨c', _, _, hp, hpin⟩ := row_at_head h
  obtain ⟨nO, hO⟩ := H2K.JointK.omega_some_in_scope h.scope Zp ProofFile.pureRoad.links Np c' hp hpin
  exact ⟨pGomega nO, by
    show Np.O.map _ = _
    rw [hO]
    rfl⟩

variable {pO : P12}

/-- **Under the head all seven numbers of the seated place of the test on G_omega are the written
place's.** -/
theorem nums_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    pO.nums = piOFull.nums := by
  obtain ⟨c', _, _, hp, hpin⟩ := row_at_head h
  obtain ⟨nO, h1, rfl⟩ := omega_of_four hO
  exact H2K.JointK.nums_in_scope_O h.scope Zp h.laid.pub ProofFile.pureRoad.links Np nO h1 c'
    h.laid.places hp hpin

/-- Under the head the block of the test on G_omega passes its test on the plan. -/
theorem planOk_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).planOk = true := by
  obtain ⟨c', _, _, hp, _⟩ := row_at_head h
  obtain ⟨nO, h1, rfl⟩ := omega_of_four hO
  exact H2K.JointK.plan_at_seat_O o Zp ProofFile.pureRoad.links Np nO h1 c' hp

theorem thin_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    thinOf pO = thinOf piOFull :=
  thin_of_planOk guardedProximityTestParts (nums_head_O h hO) (planOk_head_O h hO)
    VerifiableInference.Desc.K12.Coin.At.closed_OFull.plan

theorem count_head_O (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    (laidOf pO).length = firstLen pO.nums.stages + restLen pO.nums.stages := by
  rw [length_congr (thin_head_O h hO), nums_head_O h hO]
  exact count_OFull

/-! ## 4 Under the head: the public premise, and the sentence -/

/-- **The public premise of `exact_first_own` at `jobAtOmega`, under the head.** -/
theorem firstPubOwn_head (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (door : W → Front X → T12) (weights : W → Weights) (rand : W → TableRand)
    (omega? : Option (W → Front X → ℕ → OnBytes.E)) (Js : SimJob Pb) (hJ : Js.p = pO)
    (ho : Js.own = true) :
    FirstPubOwn (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js := by
  have hn := nums_head_O h hO
  have hT := thin_head_O h hO
  refine ⟨hJ, ho, ?_, ?_, ?_, ?_⟩
  · show formPubB pO = true
    rw [formPubB_congr hn hT]
    exact formPubB_O
  · show firstLen pO.nums.stages ≤ (laidOf pO).length
    rw [hn, length_congr hT]
    exact enough_O
  · rw [tablesFitB_eq]
    show tabB pO true = true
    rw [tabB_congr hn hT]
    exact tabB_O
  · show (pO.nums.stages.headD default).Z.a ≤ 32
    rw [hn]
    exact points_O

/-- **The sentence at the first member of that job, under the head**: at every face, side and On, at
the bound `budBoth`. -/
theorem exact_first_own_head (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO)
    (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (door : W → Front X → T12) (weights : W → Weights)
    (rand : W → TableRand) (omega? : Option (W → Front X → ℕ → OnBytes.E)) (Js : SimJob Pb)
    (hJ : Js.p = pO) (ho : Js.own = true) (chain firstTree : ℕ)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → ProofFile.Honest.Mid W X → Before → Prop) :
    ExactMember φ σ chain firstTree On (budBoth Js)
      (firstMember (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js) :=
  exact_first_own φ σ _ Js chain firstTree On rfl
    (firstPubOwn_head h hO door weights rand omega? Js hJ ho)

/-! ## 5 Under the head: the side off the description's own shared list -/

/-- At a description that is `descN`: the first block of its shared list at the place of the test on
G_omega stands at that place and has the rounds and oracle messages of the test's own block. F is a
letter, so that the blocks' types can follow it. -/
theorem find_at_O {mk : ProofFile.LinksBy} {N : H2U.Places4}
    {c : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl}
    (F : VerifiableInference.Desc.FileDescription ProofFile.Inst) (hF : F = descN o mk guardedProximityTestParts Zp N c)
    (R : H2K.JointK.RowK12 o mk Zp N c) (nO : H2U.PlaceNums) (hO : N.O = some nO) :
    ∃ b, (F.shared.blocksInOrder.find? fun b => b.place == (⟨2, none, 10, .K12⟩ : Place)) = some b ∧
      b.place = ⟨2, none, 10, .K12⟩ ∧
      b.rounds = (proximityTestKind guardedProximityTestParts (pGomega nO) : Block T12 Unit).rounds ∧
      b.oracles = (proximityTestKind guardedProximityTestParts (pGomega nO) : Block T12 Unit).oracles := by
  subst hF
  cases hf : (descN o mk guardedProximityTestParts Zp N c).shared.blocksInOrder.find?
      fun b => b.place == (⟨2, none, 10, .K12⟩ : Place) with
  | none =>
    have := List.find?_eq_none.1 hf _ (R.omega nO hO).1
    rw [H2K.JointK.omegaEntry_place] at this
    simp at this
  | some b =>
    have hb : b.place = ⟨2, none, 10, .K12⟩ := by simpa using List.find?_some hf
    rcases R.sharedOnly b (List.mem_of_find?_eq_some hf) (by rw [hb]) with rfl | ⟨nO', hO', rfl⟩
    · rw [H2K.JointK.guEntry_place] at hb
      cases hb
    · obtain rfl : nO' = nO := Option.some.inj (hO'.symm.trans hO)
      exact ⟨_, rfl, hb, rfl, rfl⟩

/-- **The first block of the description's shared list at the place of the test on G_omega.** -/
theorem find_gomega (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) :
    ∃ b : Block St ProofFile.Cl,
      ((P5J.F0T o Zp Np cF).shared.blocksInOrder.find? fun b => b.place == pO.place) = some b ∧
      b.place = pO.place ∧
      b.rounds = (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).rounds ∧
      b.oracles = (proximityTestKind guardedProximityTestParts pO : Block T12 Unit).oracles := by
  obtain ⟨c', e, R, _, _⟩ := row_at_head h
  obtain ⟨nO, h1, rfl⟩ := omega_of_four hO
  have hpl : (pGomega nO).place = ⟨2, none, 10, .K12⟩ := H2K.JointK.place_of_p12At _ _
  rw [hpl]
  exact find_at_O (P5J.F0T o Zp Np cF) e R nO h1

section Side
variable (h : P5J.AtMg o Z D r Zp Np cF) (hO : (fourOf Np).O = some pO) (door : W → Front X → T12)
  (weights : W → Weights) (rand : W → TableRand) (omega? : Option (W → Front X → ℕ → OnBytes.E))
  (Js : SimJob Pb) (fs : List (Fall St))

include h hO in
/-- **The side is there.** -/
theorem seat_head_O : ∃ σ : Side St ProofFile.Cl V W X Pb,
    testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder
      (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js fs = some σ := by
  obtain ⟨b, hf, _, _, _⟩ := find_gomega h hO
  unfold testSide Side.seated
  exact ⟨_, by
    show Option.map _ ((P5J.F0T o Zp Np cF).shared.blocksInOrder.find? fun b => b.place == pO.place) = _
    rw [hf]
    rfl⟩

include h hO in
/-- **Whatever side `testSide` returns there**: it passes the frame's test on sides; its members are
the two that are written out; and the sentence holds at the first, at the side's own On and bud. -/
theorem seated_head_O (hJ : Js.p = pO) (ho : Js.own = true) (σ : Side St ProofFile.Cl V W X Pb)
    (hσ : testSide (P5J.F0T o Zp Np cF).shared.blocksInOrder
      (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js fs = some σ) :
    σ.fits = true ∧
    σ.members =
      [firstMember (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js,
        restMember (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js] ∧
    ∀ (φ : Face V W Pb) (chain firstTree : ℕ), ExactMember φ σ chain firstTree
      (testOn φ (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js)
      (testBud Js)
      (firstMember (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest Js) := by
  have hk := planOk_head_O h hO
  have hst : pO.nums.stages = piOFull.nums.stages := congrArg (·.stages) (nums_head_O h hO)
  obtain ⟨s, t, rest, hlit⟩ : ∃ s t rest, piOFull.nums.stages = s :: t :: rest := ⟨_, _, _, rfl⟩
  obtain ⟨b, hf, hp, hr, hor⟩ := find_gomega h hO
  have hσ' := hσ
  unfold testSide Side.seated at hσ'
  have hf' : ((P5J.F0T o Zp Np cF).shared.blocksInOrder.find? fun b => b.place ==
      (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ pO door weights rand omega?).toRun.toTest.p.place) =
      some b := hf
  rw [hf'] at hσ'
  obtain rfl := Option.some.inj hσ'
  refine ⟨?_, ?_, fun φ chain firstTree => ?_⟩
  · exact fits_of _ Js hJ b _ hp hk hr hor s t rest (hst.trans hlit) (count_head_O h hO)
  · refine members_of_seat _ _ Js fs _ hσ ?_ s t rest (hst.trans hlit) (count_head_O h hO)
    show b.rounds.zip b.oracles = _
    rw [hr, hor]
    exact zip_laid pO hk
  · exact exact_bud (fun ds asks hb => budBoth_of_testBud Js ds asks hb)
      (exact_first_own_head h hO φ _ door weights rand omega? Js hJ ho chain firstTree _)

end Side

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.formPubB_O
#print axioms ProofFile.Honest.K12.Light.enough_O
#print axioms ProofFile.Honest.K12.Light.tabB_O
#print axioms ProofFile.Honest.K12.Light.points_O
#print axioms ProofFile.Honest.K12.Light.count_OFull
#print axioms ProofFile.Honest.K12.Light.exact_bud
#print axioms ProofFile.Honest.K12.Light.budBoth_of_testBud
#print axioms ProofFile.Honest.K12.Light.row_at_head
#print axioms ProofFile.Honest.K12.Light.omega_of_four
#print axioms ProofFile.Honest.K12.Light.omega_head
#print axioms ProofFile.Honest.K12.Light.nums_head_O
#print axioms ProofFile.Honest.K12.Light.planOk_head_O
#print axioms ProofFile.Honest.K12.Light.thin_head_O
#print axioms ProofFile.Honest.K12.Light.count_head_O
#print axioms ProofFile.Honest.K12.Light.firstPubOwn_head
#print axioms ProofFile.Honest.K12.Light.exact_first_own_head
#print axioms ProofFile.Honest.K12.Light.find_at_O
#print axioms ProofFile.Honest.K12.Light.find_gomega
#print axioms ProofFile.Honest.K12.Light.seat_head_O
#print axioms ProofFile.Honest.K12.Light.seated_head_O
