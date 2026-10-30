-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/OnFreeTAtHeadU.lean

A conditional with no known member: the head has members at the goals' two named sets of files
(headMember_named, AtFullSide/Top/HeadMemberAtGap.lean); that at a prover and a book ready and runC
return with it, and that the part is called, is shown by nothing that we know.

What it proves. What is left of the condition at the second part's entry (OnFreeT,
Sim/TreesExact.lean) at the proximity test on G_u of the proof file's shared chain, under the head
P5J.AtMg, at a run of the frame's walking prover (runC): one statement, its premises sorted. The
jobs are jobLocU and simLocU (JobsLocU.lean) at the plan's letters; the list of first trees is the
place's own. The conclusion has the letters of the second half of the frame's debt at a part, but
for one step: there are the blocks that the part is handed as carried and the stand that
midSharedAtW returns, and the condition holds at them and at the run's own front. The step: the debt
(Owed, ProofFile/Honest/Owed.lean) names the stand by orRefused of midSharedAtW's term; the frame's
orRefused_some (Law/WalkMid.lean) leads there from this conclusion's equation and is not called
here.

Paid here. le, leS, heardFit, heard, fold (five_at_run, FiveAtRun.lean); door (door_clause_any,
JobsLocU.lean); asks, down to the sentence on values (asks_heard, AsksWhole.lean).

Left, not paid by these files: two premises on values, at the run's stand and carried blocks:
hSays (SaysAt: the rows that the test takes in say true things of the words that the job's own rows
make) and hTrees (OnFreeT's clause trees, to the letter); and the run: hR, hrun, hc.

Asked here; the like stands elsewhere at other letters, and is not drawn at this J: till it is,
these are asked, not paid. Public at the place: hlaid (own_at_place's road), hk and T's fields
stages, enough, sorts, tables (the like stands in facts_head_U, pubTiesT_head_U:
Sim/FirstAnyAtHeadU.lean, Sim/RestTiesAtHeadU.lean). On the challenges: hfit and T's fields len, own
(of Draws.due). On the filling: S (stands_rest, Sim/FrameAtRun.lean), h9, hg. On the book: hT
(tiesB: a test with code on its entries).

Names.
  jobHeadU, simHeadU   the two jobs at the plan's letters.
  onFreeT_head_U       the statement.

Limits.
- hSays and hTrees are clauses of the condition, taken as premises on a run: that bars a count, not
  the law. No later law may take the condition as a hypothesis on a run and then speak of the random
  values as uniform.
- It holds at doorUF's fall-back too, where SaysAt holds for nothing (SaysAtFall.lean): that the
  state on entry is what the seat's way in makes of the verifier's is door_at_run's sentence
  (DoorAtRun.lean), which asks besides that the prover's key is the instance's.
- The simulators' job is given the stored table's columns opened at "LOC"'s positions: these are
  computed from the weights and count against the committed tables' budget of columns
  (DoorSimAtRun.lean's head).
- Of the walk (runC), not of play (run).
- It moves no count. The test on G_u alone; the arm of the test on G_omega has no like.
- What MarksBehind.lean stands over are files of this library.
  Also beneath this file: K12/LiveField.lean and, of the frame's authors (ProofFile/Honest/): Blind,
  Field, FieldGood, FieldLaw, Gap, GapAt, GapSame, MidW, WalkHeard, WalkLive, WalkOpened,
  Law/WalkMid, Law/Rule/FaithOwnFile, Law/Rule/OpenedAt, Law/Rule/OpenedStep.
- The stand is the state that midSharedAtW (Honest/MidW.lean) returns. That runC's own walk goes
  through that state is not said here.
- Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.FiveAtRun
import Johnson.Desc.ProofFile.Honest.K12.JobsLocU
import Johnson.Desc.ProofFile.Honest.K12.AsksWhole
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactFirstAtU

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (TableKey)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc (K1.qAt)
open Johnson.G (codesFull2)
open Desc.K14 (St blocks)
open Desc.K14.Honest (flatOf_carried)
open H2K.Pub (sgOf)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Common StandsAt Face ready runC
  midSharedAtW carriedAt storedShown drawsFit)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- The prover's job at the test on G_u of the proof file's shared chain: jobLocU (JobsLocU.lean) at
the plan's letters. st: the function that makes the stored tables' columns (at a prover P:
P.storedWords). -/
abbrev jobHeadU {W₀ Rc X : Type} (Zp : ProofFile.Pub) (Np : H2U.Places4) (bs : List (Block St Unit))
    (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (u? : Option (Common W₀ Rc TableKey → Front X → ℕ → OnBytes.E)) :
    ManyJob (Common W₀ Rc TableKey) X :=
  jobLocU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U (sentOf (K1.qAt Zp Np).S) bs st weights rand u?

/-- The simulators' job there: simLocU at the plan's letters and the shared chain's number 1, given
the stored table's columns opened at "LOC"'s positions. -/
abbrev simHeadU (Zp : ProofFile.Pub) (Np : H2U.Places4) (bs : List (Block St Unit)) : SimJob TableKey :=
  simLocU (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) bs (fourOf Np).U 1

/-- **What is left of the condition at the second part's entry (OnFreeT, Sim/TreesExact.lean) at the
test on G_u, under the head, at a run: one statement, its premises sorted.** F := P5J.F0T o Zp Np
cF. J: the test's job of jobHeadU at the prover's own stored columns. Js := simHeadU. At every book
and every prover: where ready and runC return and the test's second part is called, there are the
blocks ca that the part is handed as carried and the stand m that midSharedAtW returns, and OnFreeT
holds at J, Js, codesFull2, the chain's number 1, the place's own list of first trees, the input's
public part, ca's stretches, m and the run's own front.
Paid here: le, leS, heardFit, heard, fold; door; asks down to the sentence on values.
Left, as premises on values, at the run's stand and carried blocks: hSays (SaysAt) and hTrees
(OnFreeT's clause trees, to the letter).
Public at the place: hb, hlaid, hk, and T's fields stages, enough, sorts, tables. On the challenges:
hfit, and T's fields len, own. On the filling and the book: hR, S, h9, hg, hT. On the run: hrun, hc.
A conditional with no known member. It holds at doorUF's fall-back too: that the state on entry is
what the seat's way in makes of the verifier's is door_at_run's sentence, under hα besides. The
simulators' job is given the stored table's columns opened at "LOC"'s positions. Of the walk (runC),
not of play (run). It moves no count. -/
theorem onFreeT_head_U {W₀ Rc Tr X₀ Y : Type} (h : P5J.AtMg o Z D r₀ Zp Np cF)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst TableKey Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)}
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (u? : Option (Common W₀ Rc TableKey → Front X₀ → ℕ → OnBytes.E))
    (J : TestJob (Common W₀ Rc TableKey) X₀) (hJ : J = (jobHeadU Zp Np
        [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand u?).toRun.toTest)
    (Js : SimJob TableKey) (hJs : Js = (simHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8]))
    (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side St ProofFile.Cl Empty (Common W₀ Rc TableKey) X₀ TableKey)
    (pre t : List (Block St ProofFile.Cl))
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ (restMember J Js) pre t
      (firstLen J.p.nums.stages))
    (h9 : pre = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9)
    (hg : (P.shared.find? fun g => g.place == σ.block.place) = some (proverSideOfProximityTest J))
    (hlaid : σ.block.rounds.zip σ.block.oracles = J.laid)
    (hT : tiesB Bk J.p.place J.members.length = true)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (Dr : ℕ → Fmt.Drawn)
    (T : FirstTies J s next rest Dr
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)))
    (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hfit : drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
      ((ρ.shared.drop (pre.flatMap (·.rounds)).length).take (firstLen J.p.nums.stages)) = true)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = true)
    (hSays : ∀ m ca, midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ
        ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = .ok (some m) →
      carriedAt Bk k 1 ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩
          (restMember (V := Empty) J Js).part = .ok ca →
      SaysAt (jobHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand u?)
          m.st.input (restFront J m) (carriedCoins J (stretches _ ca)))
    (hTrees : ∀ m ca, midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ
        ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = .ok (some m) →
      carriedAt Bk k 1 ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩
          (restMember (V := Empty) J Js).part = .ok ca →
      (J.trees₀ m.st.input (restFront J m) (stretches _ ca) (rowsAt J (stretches _ ca) m)).map
          (·.1) = (fourOf Np).U.nums.first.map (·.1.a) ∧
        ∀ (i : ℕ) (o' : Fmt.Shape × Fmt.TreeSource) (Tr' : Tree), (fourOf Np).U.nums.first[i]?
            = some o' →
          (J.trees₀ m.st.input (restFront J m) (stretches _ ca)
            (rowsAt J (stretches _ ca) m))[i]? = some Tr' →
          ∃ cols, (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
              ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩).treeCols (ProofFile.Honest.srcOf 1
                  o'.2).1 (ProofFile.Honest.srcOf 1 o'.2).2 = some cols ∧
            ∀ q ∈ cols, q.2 = Tr'.2 q.1) :
    ∃ ca m, carriedAt Bk k 1 ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩
        (restMember (V := Empty) J Js).part = .ok ca ∧
      midSharedAtW (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ
          ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩ = .ok (some m) ∧
      OnFreeT J Js codesFull2 1 (fourOf Np).U.nums.first (Face.shared.pub m.st.input)
          (stretches _ ca) m
        (r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
            ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩) := by
  have hp : J.p = (fourOf Np).U := by rw [hJ]; rfl
  have hfr : J.fresh = some (⟨ProofFile.Honest.K14.sendPlace 2, 0⟩, 1) := by rw [hJ]; rfl
  have hrows : ∀ (w : Common W₀ Rc TableKey) (fr : Front X₀) (mem mem' : ℕ → Stretch),
      (∀ t, t < J.members.length → mem t = mem' t) →
      Johnson.Prover.Link.μOf (sgOf s) (J.rows₀ w fr mem) =
        Johnson.Prover.Link.μOf (sgOf s) (J.rows₀ w fr mem') := by
    rw [hJ]
    exact fun w fr mem mem' hh => rowsMu_many _ s w fr mem mem' hh
  obtain ⟨c, m, hm, hca, -, le, leS, hF, hH, hFold⟩ := five_at_run (F := P5J.F0T o Zp Np cF)
    h.laid.planOk J _ hfr Js hR σ pre t S hg hlaid hT s next rest Dr T hk hrows hfit hrun hc
    (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
  -- the rounds in front
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, eF, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :=
    flatOf_carried (Cl := ProofFile.Cl) Zp.p.chains (K1.qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last hb
  have eF' : (P5J.F0T o Zp Np cF).shared.blocksInOrder =
      x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl := eF
  have epre : pre = [x0, x1, x2, x3, x4, x5, x6, x7, x8] := by
    rw [h9, eF']
    rfl
  have eR : pre.flatMap (·.rounds) = [b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds) := by
    rw [epre]
    simp only [List.flatMap_cons, List.flatMap_nil, l0.rounds, l1.rounds, l2.rounds, l3.rounds,
      l4.rounds, l5.rounds, l6.rounds, l7.rounds, l8.rounds]
    rfl
  obtain ⟨d0, d1, d2, e, post, q0, q1, q2, eq⟩ := rounds_eight (K1.qAt Zp Np)
    (sentOf (K1.qAt Zp Np).S) b1 b2 b3 b4 b5 b6 b7 b8 hb (facts_at_head h).2.2
  -- the clause door
  have S' := S
  rw [hp] at S'
  obtain ⟨m', hm', -, hdoor⟩ := door_clause_any (F := P5J.F0T o Zp Np cF) h.laid.planOk
    ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U (sentOf (K1.qAt Zp Np).S) [b1, b2, b3, b4, b5, b6, b7, b8]
        weights rand u? 1 hR σ
    (restMember J Js) pre t S' d0 d1 d2 e post q0 q1 q2 (eR.trans eq) hrun hc
  obtain rfl : m' = m := Option.some.inj (Except.ok.inj (hm'.symm.trans hm))
  have hdoor' : J.rec₀ m'.st.input (restFront J m') = Js.rec₀ (Face.shared.pub m'.st.input)
      ((r.run.beforeAt (storedShown (P.storedWords w₀ rc) r.run.storedAsked)
        ⟨σ.block.place, (restMember (V := Empty) J Js).number⟩).cut (firstLen J.p.nums.stages)) :=
            by
    rw [hJ, hJs]
    exact hdoor
  -- the clause asks
  have hgen : ∀ (mem : ℕ → Stretch) (m : ProofFile.Honest.Mid (Common W₀ Rc TableKey) X₀),
      drawsFit (((H2K.JointK.laidOf J.p).take (firstLen J.p.nums.stages)).map (·.1))
        (m.st.lately (firstLen J.p.nums.stages)) = true →
      SaysAt (jobHeadU Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] P.storedWords weights rand u?)
          m.st.input (restFront J m) (carriedCoins J mem) →
      ∃ Dp cc Rr, Dp.ts.length = 2 ∧
        ShapeAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) codesFull2 Dp ∧
        DataAsks J m.st.input (restFront J m) (carriedCoins J mem) (heardIn J m) Dp cc Rr := by
    rw [hJ]
    unfold jobHeadU jobLocU
    dsimp only
    intro mem m a b
    exact asks_heard (W := Common W₀ Rc TableKey) (X := X₀) h _ hb _ _ _ _ _ mem m a b
  have hasks := hgen _ m' hF (hSays m' _ hm hca)
  obtain ⟨Dp, cc, Rr, hts, hSh, hDa⟩ := hasks
  have hos : (fourOf Np).U.nums.first.length = 2 := by
    rw [nums_head_U h]
    rfl
  exact ⟨c.2.1.2.2, m', hca, hm, ⟨le, leS, hF, hH, hdoor', hFold,
    ⟨Dp, cc, Rr, hts.trans hos.symm, hSh, hDa⟩, hTrees m' _ hm hca⟩⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.onFreeT_head_U
#print axioms ProofFile.Honest.K12.Light.jobHeadU
#print axioms ProofFile.Honest.K12.Light.simHeadU
