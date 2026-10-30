-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Hears.lean: CONDITIONAL. Five definitions (four hypotheses'
forms, one test with code), and six statements with their proofs.

What is here. THE HYPOTHESIS `K4Hears` (Law/Accepted.lean: the decision
of K4, the sub-protocol of the feed-forward layers' own rounds, accepts the rounds as played)
BROUGHT DOWN TO: tests on the plan alone; facts on the verifier's state in front; two named
hypotheses on the rounds as a tape; and that the fall says nothing.

THE HYPOTHESES, EACH WITH WHERE IT IS SHOWN OR WHO IS MEANT TO PROVE IT.
  `K4TapeFits T b p`   the sub-protocol's two tests on the stretch accept the rounds as the member's
      half has played them, without the sealed digest. K4's writers: the tape's half
      (Law/TapeAccepts.lean, `k4_played_fits`).
  `K4TapeCoin T b Q p`   where the honest side's test on one sampled element (`k4CoinZero`,
      Honest/K4/Part.lean) says nothing of the challenges, the element that joins the second token
      sumcheck's hiding polynomial to its claim is not 0 on the tape of the rounds as played. K4's
      writers: the tape's half (`k4_coin_tape`, there).
  `k4PlanB p`   THREE TESTS WITH CODE ON THE PLAN ALONE: the sub-protocol covers the plan; ten
      comparisons of its numbers; the pure functions that the hearing calls return. An evaluation
      gives no term of `k4PlanB p = true`. Under h, the hypothesis on the public files
      (`P5J.AtMgA`), and `LaidK4` the proof of `k4_accepted_one` (Law/PublicOne.lean) has it at the
      member's parameters from `covers_head` and the test `k4PublicX`, which Law/DearX.lean has
      under h (`publicX_head`).
  `K4Ready p s`   the state in front, in the very terms of `hearAt_returns`. That a layers' segment
      is open there (the lifted decision's own first test) is in it: else `seatS.look` answers
      nothing.
  `K4ReadyP p s`   `K4Ready` with the third test of `k4PlanB` in the stead of the readings of pure
      functions, AND FOUR FACTS ON THE STATE THAT COME IN WITH IT (zk · planes · join · tokens).
      CLAUSE BY CLAUSE (mark and owed are fields; the rest are the clauses of the field more, named
      by what they hold: hands: `K3Hands` · merged: ends.all (· == Z)): mark: the thread's form ·
      owed, room: the promise in front (`room_of_items` for the second) · look, and the last clause
      of hands: the promise's item on the lookup (Law/ReadyOfPromise.lean) · shape, the rest of
      hands, zk, planes, merged: sizes and one equation on what the lookup's hearing lays: the head
      of Law/HearsShape.lean (handed in with this file) says of each where it is shown · join:
      another writer's `join_pay` has it from two tests on the plan and FOUR MORE FACTS ON WHAT THE
      LOOKUP HAS HEARD (the number of its shape's calls · of its weights
      · its shape's number of trees · its padding counts): Law/HearsShape.lean · tokens: under h and
      `LaidK4`, wherever the first chain's thread stands in front of the member
      (Law/TokensHead.lean): their number and bound alone.
  The fall: `∀ s ds, fall b s ds = none → k4CoinZero Q ds = none`: whoever lays the chain's falls.

  `room_of_items`   room in the ledger from three public items' tests and one comparison of public
      numbers.
  `blockAtS_returns`   the decision at the first chain's state accepts, under the premises of
      `hearAt_returns` in the terms of the seat at that state.
  `behind_of_kept`   where `KeptAtS` holds of s and s' (what an accept leaves) and s bears no mark:
      s' bears none, and the reply is as it was.
  `k4Ready_of_P`   K4Ready from K4ReadyP and the test.
  `k4Hears_of_ready`   **K4Hears**, from K4Ready.
  `k4Hears_of_plan`   **K4Hears**, from `k4PlanB` and K4ReadyP.

Called. The road is one call of another writer's statement that the sub-protocol's hearing returns
(`hearAt_returns`, Johnson/Desc/First/K4/Returns/Seat.lean). Besides: `planNums_of_B`
(Returns/Needs.lean beside it), `hearPub_of_PB` (Returns/Pub/JoinPoints.lean), `kept_atS`
(Johnson/Road/K4/KeptAtS.lean), `ledgerB_iff` (Johnson/Road/K4/K4KeepKeeper.lean), `sized_iff`
(Johnson/Road/K4/LookOutKept.lean), `seatS_owed`, `seatS_look`, `seatS_fork`
(Johnson/Desc/First/K4/SeatS.lean).

Kin. `behind_of_kept` takes `Rest` out of `KeptAtS` within its proof, as `rest_of_kept`
(Law/PromiseConds.lean (handed in with this file)) states it; neither file imports the other.
`sameOut_all` (Johnson/Desc/First/Att/Door/Law/K5RestOpen.lean, of other writers) has the step of
its second half: where the field out is the same, `sameReply` is true; it is not called.
`takes_slotsOf` (Returns/Needs.lean) counts a layers' sub-proof's slots as the lookup's, K4's and
the smallness test's together, under two equations on the plan; it is not called. The comparison hn
of `room_of_items` is asked as it stands: in the proof of `k4_accepted_one` (Law/PublicOne.lean) the
comparison of slots at the member's parameters comes out of the fourth test of `k4PublicB`
(Law/PublicX.lean).

Not shown here. THAT THE DECISION ACCEPTS ANYWHERE. This file gives no example of its hypotheses
together; the list above says of each where it is shown. Q AND p ARE TIED BY NOTHING HERE: the field
own of `K4SeatedA` (Law/SeatedA.lean) ties them. `hearAt_returns` asks nothing of what the prover
has sent but its shape: no worth, no tie to the witness, no `k4Fits`: SO THE DECISION TESTS NO SENT
VALUE: it accepts every play of the right shape, a false one too. Following import lines, and
stopping unopened at every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/
and at every module whose name begins Cb.Bridge, its imports reach 2 modules under Johnson/Bridge/
and none of the others; what lies behind the two is not counted; one of the modules that it reaches
has RecCompile in its name (Johnson.TypedOracleCompiler.RecCompile.Bcs, with the library's
Johnson/Road/K4/K4KeepKeeper.lean), which is not RecCompile's Honest*, Both or PassH*. Nothing on
soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Accepted
import Johnson.Desc.First.K4.Returns.Seat
import Johnson.Desc.First.K4.Returns.Needs
import Johnson.Desc.First.K4.Returns.Pub.JoinPoints
import Johnson.Road.K4.K4KeepKeeper
import Johnson.Desc.First.FillK4
import Johnson.Road.K4.LookOutKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E isZeroE)
open OnBytes.K.Kc (paired)
open D6.Ret (Room)
open OnBytes.Model (Forest.Heard RoundName Fork lastOf)
open OnBytes.Model.Layer (TableAt TableAsk)
open OnBytes.Desc.First.K4 (Par blockAtS seatS rounds entries rowsTabled covers shapeFits)
open OnBytes.Desc.First.K4.Rt (TapeOf rowsNorms k4Takes PlanNums planNumsB K3Hands HearPub JoinPub
  hearAt_returns planNums_of_B)
open OnBytes.Desc.First.K4.RtPub (hearPB hearPub_of_PB zkFits tokensFit tablesAt)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Road.K4 (KeptAtS kept_atS)
open VerifiableInference.Desc (Block Claim First.S noDigest)
open VerifiableInference.Desc.First (ledgerB freeAboveB)
open VerifiableInference.Desc.First.FillK4 (callerInLayB)

/-! ## 1 The hypotheses -/

section
variable {Bk : ProverCoinCounts} {V W X Pb : Type}

/-- **The sub-protocol's two tests on the stretch accept the rounds as played.** This defines a
hypothesis; the definition claims nothing. -/
def K4TapeFits (T : Thread Bk First.S Claim V W X Pb) (b : Nat) (p : Par) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k m E ds y cols, T.Moved blk k m E ds y cols →
    drawsFit blk.rounds ds = true →
    OnBytes.Desc.First.K4.fitsAll (rounds p.P p.hp p.g) (entries p.P p.hp p.g)
        ((roundsOf y.1).map noDigest) = true ∧
      OnBytes.Desc.First.Kit.plainStretchWith rowsTabled (entries p.P p.hp p.g)
        ((roundsOf y.1).map noDigest) = true

/-- **The honest side's test on the sampled element, read on the tape of the rounds as played.**
This defines a hypothesis; the definition claims nothing. -/
def K4TapeCoin (T : Thread Bk First.S Claim V W X Pb) (b : Nat) (Q : K4Pub) (p : Par) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k m E ds y cols, T.Moved blk k m E ds y cols →
    k4CoinZero Q ds = none →
    ∀ t₁ s0 eps t₂, TapeOf (rowsNorms p.P p.g) t₁ →
      paired ((roundsOf y.1).map noDigest) (entries p.P p.hp p.g) =
        t₁ ++ ⟨some RoundName.pscEpsilon.name, 0, 0, s0, [eps]⟩ :: t₂ → isZeroE eps = false

end

/-- **Three tests on the plan alone.** -/
def k4PlanB (p : Par) : Bool :=
  covers p.P && planNumsB p.P p.hp p.g && hearPB p.P p.hp p.g

/-- **What is asked of the verifier's state in front of the member**, in the terms of
`hearAt_returns`. This defines a hypothesis; the definition claims nothing. -/
structure K4Ready (p : Par) (s : First.S) : Prop where
  mark : s.failed = none
  owed : (seatS.owed s).isNone = true
  more : ∃ (fo : Forest.Heard) (k : Nat) (Z ztF : Array E) (ends : Array (Array E)) (iU3 : Nat)
    (tab : List TableAt) (laid : List (TableAsk × List (Nat × Nat))),
    seatS.look s = some fo ∧ shapeFits p.P fo = true ∧
      Room (seatS.fork s) (k4Takes p.P p.hp p.g + k) ∧ K3Hands p.P fo (seatS.fork s) Z ztF ends ∧
      HearPub { p.P with tokv := seatS.tokv s } p.hp p.g fo ztF iU3 tab laid ∧
      ends.all (· == Z) = true

/-- **The same, with a test on the plan in the stead of the readings of pure functions.** This
defines a hypothesis; the definition claims nothing. -/
structure K4ReadyP (p : Par) (s : First.S) : Prop where
  mark : s.failed = none
  owed : (seatS.owed s).isNone = true
  more : ∃ (fo : Forest.Heard) (k : Nat) (Z ztF : Array E) (ends : Array (Array E)),
    seatS.look s = some fo ∧ shapeFits p.P fo = true ∧
      Room (seatS.fork s) (k4Takes p.P p.hp p.g + k) ∧ K3Hands p.P fo (seatS.fork s) Z ztF ends ∧
      zkFits p.P fo.zk = true ∧
      (OnBytes.Model.Forest.planeCols fo.shape p.P.y.h.lmb).toBool = true ∧
      (∀ iU3 tab laid n, p.hp.tl.ix.U.getD 2 none = some iU3 →
        tablesAt p.P p.g = some (tab, laid, n) →
        JoinPub (OnBytes.Desc.First.K4.Rt.envOf { p.P with tokv := seatS.tokv s } p.hp p.g fo iU3
          tab) fo) ∧
      ends.all (· == Z) = true ∧ tokensFit { p.P with tokv := seatS.tokv s } p.g = true

/-! ## 2 The state's half -/

/-- **Room in the ledger**, from the tests of three public items that are open in front of the
member (ledger · freeAbove · callerIn) and one comparison of public numbers. nu: the plan's next
free slot in front; ns: its number of slots; n: how many slots are asked. -/
theorem room_of_items {s : First.S} {nu ns n : Nat} (hl : ledgerB s = true)
    (hf : freeAboveB ns s = true) (hc : callerInLayB nu s = true) (hn : nu + n ≤ ns) :
    Room (seatS.fork s) n := by
  obtain ⟨F, e, hz⟩ := (OnBytes.Road.K4.ledgerB_iff s).mp hl
  have hS : OnBytes.PscRun.Sized F := (OnBytes.Road.K4.sized_iff F).mp hz
  unfold callerInLayB at hc
  cases ha : s.here with
  | lay a =>
    rw [ha] at hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    have eF : s.fork? = some a.F := by simp only [First.S.fork?, ha]
    obtain rfl : a.F = F := Option.some.inj (eF.symm.trans e)
    rw [OnBytes.Desc.First.K4.seatS_fork ha]
    unfold freeAboveB at hf
    rw [eF] at hf
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
      Bool.not_eq_true'] at hf
    obtain ⟨hfree, hns⟩ := hf
    refine ⟨hS, by rw [hc.2, hns]; exact hn, fun j hj hF => ?_⟩
    unfold OnBytes.PscRun.Filled at hF
    by_cases hlt : j < a.F.ns
    · have h1 := hfree (j - a.F.next) (by omega)
      rw [show a.F.next + (j - a.F.next) = j by omega] at h1
      have hsz : j < a.F.gotF.size := by rw [hS.2.2]; exact hlt
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hsz, Option.getD_some] at h1 hF
      rw [h1] at hF
      cases hF
    · have hsz : a.F.gotF.size ≤ j := by rw [hS.2.2]; omega
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hsz, Option.getD_none] at hF
      cases hF
  | _ =>
    rw [ha] at hc
    cases hc

/-- **The sub-protocol's decision at the first chain's state accepts**, under the premises of
`hearAt_returns` in the terms of the seat at that state. The decision is the sub-protocol's at its
own part of the state, lifted (`blockAtS`, Johnson/Desc/First/K4/AtS.lean): so the statement on the
hearing is called at that part's seat. -/
theorem blockAtS_returns {p : Par} {s : First.S} {rs : List Fmt.RoundView}
    (gs : List (List (Nat × List UInt64))) {fo : Forest.Heard} {k : Nat} {Z ztF : Array E}
    {ends : Array (Array E)} {iU3 : Nat} {tab : List TableAt}
    {laid : List (TableAsk × List (Nat × Nat))} (h0 : (seatS.owed s).isNone = true)
    (h1 : OnBytes.Desc.First.K4.fitsAll (rounds p.P p.hp p.g) (entries p.P p.hp p.g) rs = true)
    (h2 : OnBytes.Desc.First.Kit.plainStretchWith rowsTabled (entries p.P p.hp p.g) rs = true)
    (h3 : seatS.look s = some fo) (hc : covers p.P = true) (hs : shapeFits p.P fo = true)
    (hR : Room (seatS.fork s) (k4Takes p.P p.hp p.g + k)) (hN : PlanNums p.P p.hp p.g)
    (hK : K3Hands p.P fo (seatS.fork s) Z ztF ends)
    (hP : HearPub { p.P with tokv := seatS.tokv s } p.hp p.g fo ztF iU3 tab laid)
    (vM : ends.all (· == Z) = true)
    (vE : ∀ t₁ s0 eps t₂, TapeOf (rowsNorms p.P p.g) t₁ →
      paired rs (entries p.P p.hp p.g) =
        t₁ ++ ⟨some RoundName.pscEpsilon.name, 0, 0, s0, [eps]⟩ :: t₂ → isZeroE eps = false) :
    ∃ s', (blockAtS p).decide s rs gs = .ok s' := by
  cases ha : s.here with
  | lay a =>
    rw [OnBytes.Desc.First.K4.seatS_owed ha] at h0
    rw [OnBytes.Desc.First.K4.seatS_look ha] at h3
    rw [OnBytes.Desc.First.K4.seatS_fork ha] at hR hK
    obtain ⟨o, G, e, -⟩ := hearAt_returns OnBytes.Desc.First.K4.seatOwn p
      (a, (if s.noneWaits then none else s.rowsOwed), s.tokv) rs h0 h1 h2 h3 hc hs hR hN hK hP vM vE
    have hq : OnBytes.Desc.First.K4.part? s =
        some (a, (if s.noneWaits then none else s.rowsOwed), s.tokv) := by
      simp only [OnBytes.Desc.First.K4.part?, ha]
    refine ⟨OnBytes.Desc.First.K4.setPart s (OnBytes.Desc.First.K4.seatOwn.setOwed
      (OnBytes.Desc.First.K4.seatOwn.setOwn (OnBytes.Desc.First.K4.seatOwn.setFork
        (a, (if s.noneWaits then none else s.rowsOwed), s.tokv) G) o) none), ?_⟩
    show ((VerifiableInference.Desc.named "the part is not there"
      (OnBytes.Desc.First.K4.part? s)).bind fun q =>
        ((OnBytes.Desc.First.K4.block OnBytes.Desc.First.K4.seatOwn p).decide q rs gs).map
          (OnBytes.Desc.First.K4.setPart s)) = _
    rw [hq]
    show (((OnBytes.Desc.First.K4.hearAt OnBytes.Desc.First.K4.seatOwn p
      (a, (if s.noneWaits then none else s.rowsOwed), s.tokv) rs)).map
        (OnBytes.Desc.First.K4.setPart s)) = _
    rw [e]
    rfl
  | between => simp [seatS, ha] at h3
  | att _ => simp [seatS, ha] at h3
  | head _ => simp [seatS, ha] at h3
  | fin _ => simp [seatS, ha] at h3
  | mem _ => simp [seatS, ha] at h3

/-- **Behind what an accept leaves (`KeptAtS`), where there is no mark in front, there is none, and
the reply is as it was.** -/
theorem behind_of_kept {p : Par} {s s' : First.S} (K : KeptAtS p s s') (hm : s.failed = none) :
    s'.failed = none ∧ ProofFile.sameReply s s' = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hR, _⟩ := K
  refine ⟨by rw [hR.failed, hm], ?_⟩
  unfold ProofFile.sameReply
  rw [hR.out]
  exact beq_self_eq_true _

/-- **The readings of pure functions, from the test on the plan.** -/
theorem k4Ready_of_P {p : Par} {s : First.S} (hB : hearPB p.P p.hp p.g = true)
    (R : K4ReadyP p s) : K4Ready p s := by
  obtain ⟨hm, h0, fo, k, Z, ztF, ends, h3, hs, hR, hK, hz, hpc, hj, vM, hk⟩ := R
  obtain ⟨iU3, tab, laid, n, hu, ht, h⟩ :=
    hearPub_of_PB (P := { p.P with tokv := seatS.tokv s }) (hp := p.hp) (g := p.g) hB
  exact ⟨hm, h0, fo, k, Z, ztF, ends, iU3, tab, laid, h3, hs, hR, hK,
    h fo Z ztF hz hk hK.z hK.ztSize hpc (hj iU3 tab laid n hu ht), vM⟩

/-! ## 3 The decision accepts -/

variable {Bk : ProverCoinCounts} {V W X Pb : Type} {T : Thread Bk First.S Claim V W X Pb} {b : Nat}
  {Q : K4Pub} {p : Par} {fall : Nat → First.S → List Fmt.Drawn → Option String}
  {At : Coins Bk → First.S → Mid W X → Env → Prop}

/-- **THE SUB-PROTOCOL's OWN DECISION ACCEPTS THE ROUNDS AS PLAYED.** CONDITIONAL. -/
theorem k4Hears_of_ready (hTF : K4TapeFits T b p) (hTC : K4TapeCoin T b Q p)
    (hc : covers p.P = true) (hN : PlanNums p.P p.hp p.g)
    (hRd : ∀ k s m E, At k s m E → K4Ready p s)
    (hf : ∀ s ds, fall b s ds = none → k4CoinZero Q ds = none) : K4Hears T At fall b p := by
  intro blk hblk k s m E ds y cols hAt hd _ hfall hM gs
  obtain ⟨h1, h2⟩ := hTF blk hblk k m E ds y cols hM hd
  obtain ⟨hm, h0, fo, k', Z, ztF, ends, iU3, tab, laid, h3, hs, hR, hK, hP, vM⟩ :=
    hRd k s m E hAt
  obtain ⟨s', hdec⟩ := blockAtS_returns gs h0 h1 h2 h3 hc hs hR hN hK hP vM
    (hTC blk hblk k m E ds y cols hM (hf s ds hfall))
  obtain ⟨b1, b2⟩ := behind_of_kept (kept_atS hdec) hm
  exact ⟨s', hdec, b1, b2⟩

/-- **The same, from the three tests on the plan.** CONDITIONAL. -/
theorem k4Hears_of_plan (hTF : K4TapeFits T b p) (hTC : K4TapeCoin T b Q p)
    (hPl : k4PlanB p = true) (hRd : ∀ k s m E, At k s m E → K4ReadyP p s)
    (hf : ∀ s ds, fall b s ds = none → k4CoinZero Q ds = none) : K4Hears T At fall b p := by
  unfold k4PlanB at hPl
  simp only [Bool.and_eq_true] at hPl
  exact k4Hears_of_ready hTF hTC hPl.1.1 (planNums_of_B hPl.1.2)
    (fun k s m E h => k4Ready_of_P hPl.2 (hRd k s m E h)) hf

end ProofFile.Honest.K4


#print axioms ProofFile.Honest.K4.K4TapeFits
#print axioms ProofFile.Honest.K4.K4TapeCoin
#print axioms ProofFile.Honest.K4.k4PlanB
#print axioms ProofFile.Honest.K4.K4Ready
#print axioms ProofFile.Honest.K4.K4ReadyP
#print axioms ProofFile.Honest.K4.room_of_items
#print axioms ProofFile.Honest.K4.blockAtS_returns
#print axioms ProofFile.Honest.K4.behind_of_kept
#print axioms ProofFile.Honest.K4.k4Ready_of_P
#print axioms ProofFile.Honest.K4.k4Hears_of_ready
#print axioms ProofFile.Honest.K4.k4Hears_of_plan
