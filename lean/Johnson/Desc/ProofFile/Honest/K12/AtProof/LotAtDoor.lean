-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/LotAtDoor.lean: the honest side of the first chain's lot
of the kind K12 (`lotL`, LotL.lean in this folder) with its state on entry filled: `doorL`
(Blind/DoorL.lean) at the chain's own list of blocks, at the description's own start and at the
test's place, each a term off the public part. And, under the head at the concrete earlier hash, at
a called part of a run of the frame's walking prover: the state on entry is at hand; it agrees, but
for the rows' targets, with the record T that the way in returns at the state which the
description's own fold reaches at the run's own rounds and columns; and each move of both parts says
what it says at the job that is handed T.

  `flatL`        the first chain's own list, off the public part (the library's `ProofFile.onlineFirstChainAt`,
                 Johnson/Desc/ProofFile/LinkAt.lean)
  `startL`       the start: one term for all inputs
  `doorAtL`, `atHandAtL`   the state on entry; the test that says whether a default was taken
  `lotAtDoor`    the lot. The main rows' data, the readers and the closing stay letters
  `flatL_at_head`, `atHand_no_chain`, `startL_own`, `numbersL_at_head`, `halves_lotAtDoor`,
  `restFront_seen`   small lemmas
  `door_moves_at_L`   the statement above; `door_moves_at_lot`: the same with the side seated in
                 `flatL Zp`
  `agree_at_rest`   at the second member's own front (`restFront`, Sim/Row.lean)

By what. `atHandL_at_seat` (Blind/AtHandAtFinish.lean), `say_zero_at_first` (Blind/DoorL.lean),
`theSteps` (Blind/All.lean), `keepsInFront_L` (Blind/KeepsAtFinish.lean); `P5J.LaidAt.chain`
(Johnson/P5J/ChainFree.lean); `four_L` (Places.lean in this folder). Against these laws four
hypotheses are gone: the five equations `Steps`; that the start is the description's own at the
run's input; that the job's numbers are the planner's record's; that the side stands at the test's
place.

TWO SILENT DEFAULTS. `flatL` is the empty list where the library gives no chain; there no block
stands at any place and `atHandAtL` is false (`atHand_no_chain`). `doorAtL` is `idleT12`
(Doors.lean) where the fold or the way in refuses; `atHandAtL` is the test that says so. At the
stands spoken of in `door_moves_at_L` it is true, so neither default is taken there. Of any other
input and front nothing is said.

Limits.
- T is what the way in returns at the state s of the clause on `foldBlocks`. `doorAtL`'s value is
  not T and is not the verifier's state: it agrees with T but for the rows' targets.
- The job that is handed T is a term of comparison: no prover's side can make it.
- THE LOT GIVES A HALF ONLY WHERE THE PLAN HAS THE FINISH AND `fitsL` SAYS YES (`halves_lotAtDoor`:
  hf, hfit). Both are public tests. These files do not pay them under the head: `fitsL_head_L` and
  `halves_head_L` (AtFullSide/K12/FitsAtHeadL.lean) do, at the blank ground.
- hi of `agree_at_rest`, that the rounds of the side's parts in front of the member are the first
  part's, is a hypothesis: `StandsAt` has no field that gives it. The frame's `PartsStand`
  (ProofFile/Honest/Law/OwedRule.lean) states `StandsAt` at `σ.roundsTo u.number`, which by reading
  is that number at the second member: not typed here.
- What is left as hypotheses: the head, which has members at the goals' two named sets of files
  (`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean); on the filling and the book (hR, St);
  on the run (hrun, hc); that `testSide` seats the side (hσ). Nothing on whether `ready` or `runC`
  returns or a part is called. That these hold together with the head is shown by nothing that we
  know. At the concrete earlier hash alone.
- AT ONE LIST OF GROUPS, as all of Blind/: this is no law on a fold at made-up columns through the
  test's own block.
- All limits of LotL.lean and JobL.lean stand: where the sender's text refuses the job lays zeros
  without a warning; wanted beside it, wherever `jobL` is laid: the closing's refusals hang on
  public fields alone. Nothing here shows it.
- The stand is the state that `midAtW` (Honest/MidW.lean) returns. That `runC`'s own walk goes
  through that state is not said here.
- It moves no count. Nothing on completeness, soundness or hiding.
Over what it stands. This folder's files and Blind/'s, and beneath these the kind K10's authors'
(Johnson/Desc/ProofFile/Honest/K10/).
Also beneath this file: K12/LiveField.lean and, of the frame's authors
(Johnson/Desc/ProofFile/Honest/): Blind, Field, FieldGood, FieldLaw, Gap, GapAt, GapSame, MidW,
WalkHeard, WalkLive, WalkOpened, Law/WalkMid, Law/Rule/FaithOwnFile, Law/Rule/OpenedAt,
Law/Rule/OpenedStep.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Blind.All
import Johnson.Desc.ProofFile.Honest.K12.Blind.AtHandAtFinish
import Johnson.Desc.ProofFile.Honest.K12.AtProof.LotL
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Places
import Johnson.P5J.ChainFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Block Chain Place OpenedColumn FileDescription foldBlocks)
open VerifiableInference.Desc.K12 (P12 T12 enterFinish)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest
open ProofFile.Honest.K10 (Keeps wipeS)
open ProofFile.Honest.K12.Blind (Agree doorL atHandL doorZ)

variable {V W₀ Rc Tr X : Type}

/-! ## 1 The definitions -/

/-- **The first chain's own list of blocks, off the public part.** A SILENT DEFAULT: the empty list
where the library's `onlineFirstChainAt` refuses (`atHand_no_chain`). -/
def flatL (Z : ProofFile.Pub) : List (Block S ProofFile.Cl) :=
  ((ProofFile.onlineFirstChainAt Z).toOption.map (·.blocksInOrder)).getD []

/-- **The start, one term for all inputs**: the description's own start at the public part of the
input's instance. -/
def startL (Z : ProofFile.Pub) (w : Local W₀ Rc ProofFile.Inst Tr) : S := ProofFile.startS Z w.x.pub

/-- **The state on entry at the first chain's proximity test.** `idleT12`: its silent default. -/
def doorAtL (Z : ProofFile.Pub) : Local W₀ Rc ProofFile.Inst Tr → Front X → T12 :=
  doorL (flatL Z) (startL Z) placeL idleT12

/-- The test that says whether `doorAtL`'s default was taken. -/
def atHandAtL (Z : ProofFile.Pub) : Local W₀ Rc ProofFile.Inst Tr → Front X → Bool :=
  atHandL (flatL Z) (startL Z) placeL

/-- **The lot, its door filled.** The ground is not read by the door. -/
def lotAtDoor (D : ProofFile.Pub → Ground → RowDataOf ProofFile.Inst)
    (readers : ProofFile.Pub → Ground → Local W₀ Rc ProofFile.Inst Tr → Readers)
    (closing : ProofFile.Pub → Ground → K2.Closing) : HLot V (Local W₀ Rc ProofFile.Inst Tr) X :=
  lotL (fun Z _ => doorAtL Z) D readers closing

/-! ## 2 The small lemmas -/

theorem flatL_at_head {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) : flatL Zp = cF.blocksInOrder := by
  unfold flatL
  rw [h.laid.chain]
  rfl

/-- Where the library gives no chain the state on entry is not at hand. -/
theorem atHand_no_chain (Z : ProofFile.Pub) (e : String) (h : ProofFile.onlineFirstChainAt Z = .error e)
    (w : Local W₀ Rc ProofFile.Inst Tr) (fr : Front X) : atHandAtL Z w fr = false := by
  unfold atHandAtL flatL
  rw [h]
  rfl

/-- `startL` is the description's own start at every input. -/
theorem startL_own (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain S ProofFile.Cl)
    (w : Local W₀ Rc ProofFile.Inst Tr) :
    startL Zp w = (P5J.F0T o Zp Np cF).start₁ ((P5J.F0T o Zp Np cF).pub w.x) := rfl

/-- The numbers at which the lot lays its job are the planner's record's. -/
theorem numbersL_at_head {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD}
    {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg o Z D₀ r₀ Zp Np cF) : H2U.p12OfMade Zp.made = (fourOf Np).L :=
  (four_L Zp (fourOf Np) (by unfold four; rw [h.laid.places])).symm

/-- Where the plan has the finish and the public test says yes, the lot's halves are the one pair of
the job at the filled door. -/
theorem halves_lotAtDoor (D : ProofFile.Pub → Ground → RowDataOf ProofFile.Inst)
    (readers : ProofFile.Pub → Ground → Local W₀ Rc ProofFile.Inst Tr → Readers)
    (closing : ProofFile.Pub → Ground → K2.Closing) (Z : ProofFile.Pub) (G : Ground) (pl : K2.SwitchPlace)
    (hf : finishAt Z G = some pl) (hfit : fitsL (H2U.p12OfMade Z.made) pl = true) :
    (lotAtDoor D readers closing : HLot V (Local W₀ Rc ProofFile.Inst Tr) X).halves Z G =
      [proverSideOfProximityTest (jobL (H2U.p12OfMade Z.made) (doorAtL Z) (D Z G) (readers Z G) (closing Z G)
                         pl)] := by
  unfold lotAtDoor lotL lotOf
  simp only [hf, Option.bind_some, hfit, if_true, Option.toList_some, List.map_cons, List.map_nil]

/-- The front of the second member's stand shows just the rounds in front. -/
theorem restFront_seen {W : Type} (J : TestJob W X) (m : Mid W X) (n : ℕ)
    (h : m.seen.length = n + firstLen J.p.nums.stages) :
    (restFront J m).seen.rounds = m.seen.take n := by
  show m.seen.take (m.seen.length - firstLen J.p.nums.stages) = m.seen.take n
  rw [h, Nat.add_sub_cancel]

/-! ## 3 At a called part, under the head -/

/-- **At a called part of the side that `testSide` seats, in the chain's own list, for the lot's job
at the filled door.** With all eight clauses of `called_at_first` (CalledAtFirst.lean) on m, s and
cs: the way in returns a record T at s; at every front that shows just the rounds of the blocks in
front the state on entry is at hand and agrees with T but for the rows' targets; and the move of the
test's round number j says what the move of the job that is handed T says, for every j, where what
is shown begins with these rounds and has j rounds more, at every value of the columns handed. -/
theorem door_moves_at_L {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Ky X₀ Y Pb : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side S ProofFile.Cl V (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (u : Member V (Local W₀ Rc ProofFile.Inst Tr) Y Pb) (pre t : List (Block S ProofFile.Cl)) (i : ℕ)
    (St : StandsAt cF.blocksInOrder R.first σ u pre t i)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (D : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing) (pl : K2.SwitchPlace)
    (Js : SimJob Pb) (fs : List (Fall S))
    (hσ : testSide cF.blocksInOrder
      (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) Js fs = some σ) :
    ∃ (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y) (s : S) (cs more : List OpenedColumn) (rest : List Fmt.RoundView)
      (tr : Tr),
      midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ =
        .ok (some m) ∧
      P.trace w₀ x = some tr ∧ m.st.input = ⟨w₀, rc, x, tr⟩ ∧
      r.run.views.1.rounds = m.seen ++ rest ∧
      m.seen.length = (pre.flatMap (·.rounds)).length + i ∧
      r.run.views.1.opened = cs ++ more ∧
      foldBlocks 0 pre
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₁ ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).pub x))
        (m.seen.take (pre.flatMap (·.rounds)).length) cs = .ok (s, [], []) ∧
      fillCols (readsOf 0 0 (P.storedWords w₀ rc)
        (treeOwn (r.run.played.1.take (pre.flatMap (·.rounds)).length))
        (pre.flatMap (·.rounds))
        ((m.seen.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cs ∧
      ∃ T : T12, enterFinish s = .ok T ∧
        (∀ fr : Front Y, fr.seen.rounds = m.seen.take (pre.flatMap (·.rounds)).length →
          atHandAtL Zp m.st.input fr = true ∧ Agree (doorAtL Zp m.st.input fr) T) ∧
        ∀ (C : Type) (rd : C → TestCoins) (j : ℕ) (c : C) (sn : Seen)
          (st : State (Local W₀ Rc ProofFile.Inst Tr) Y), st.input = m.st.input →
          sn.rounds.length = (pre.flatMap (·.rounds)).length + j →
          sn.rounds.take (pre.flatMap (·.rounds)).length =
            m.seen.take (pre.flatMap (·.rounds)).length →
          (moveAt (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) rd j).say c
              sn st =
            (moveAt { (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) with
              rec₀ := fun _ _ => T } rd j).say c sn st := by
  have hp : (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl :
      TestJob (Local W₀ Rc ProofFile.Inst Tr) Y).p = (fourOf Np).L := numbersL_at_head h
  have hpl : σ.block.place = placeL :=
    (Blind.testSide_place hσ).trans (hp ▸ Blind.placeL_of_four Np)
  obtain ⟨m, s, cs, more, rest, tr, a1, a2, a3, a4, a5, a6, a7, a8, T, hT, b⟩ :=
    Blind.atHandL_at_seat h hR σ u pre t i St hrun hc _ Js fs hσ hp
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hn := (places_nodup (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).planOk_ok).1 h.laid.planOk).places).1
  have hcut : cF.blocksInOrder = pre ++ σ.block :: t := St.cut
  have hn' : ((pre ++ σ.block :: t).map (·.place)).Nodup := hcut ▸ hn
  have hk : ∀ y ∈ pre, Keeps wipeS 0 y := by
    have k0 := Blind.keepsInFront_L h.scope h.reads O
    unfold Blind.KeepsInFront at k0
    rw [← hpl, hcut, Blind.takeWhile_cut pre t σ.block (Blind.apart_of_nodup hn')] at k0
    exact k0
  obtain ⟨m', s', cs', -, -, -, c1, -, -, -, -, -, c7, c8, say⟩ :=
    Blind.say_zero_at_first Blind.theSteps (F := (P5J.F0T OnBytes.secondHashFunction Zp Np cF)) h.laid.planOk
      hR σ u pre t i St hrun hc wipeS enterFinish hk Blind.enterFinish_alike
  obtain rfl : m' = m := Option.some.inj (Except.ok.inj (c1.symm.trans a1))
  obtain rfl : cs' = cs := Except.ok.inj (c8.symm.trans a8)
  obtain rfl : s' = s := (Prod.mk.inj (Except.ok.inj (c7.symm.trans a7))).1
  have hs : startL Zp m'.st.input =
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₁ ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).pub x) := by
    rw [a3]
    rfl
  have hfl := flatL_at_head h
  refine ⟨m', s', cs', more, rest, tr, a1, a2, a3, a4, a5, a6, a7, a8, T, hT, fun fr hf => ?_,
    fun C rd j c sn st h1 h2 h3 => ?_⟩
  · obtain ⟨d1, -, d3⟩ := b (startL Zp) fr hs hf
    unfold atHandAtL doorAtL
    rw [hfl, ← hpl]
    exact ⟨d1, d3 idleT12⟩
  · refine say T hT (startL Zp) idleT12 _ hs ?_ C rd j c sn st h1 h2 h3
    show doorAtL Zp = doorZ enterFinish cF.blocksInOrder (startL Zp) σ.block.place idleT12
    unfold doorAtL
    rw [hfl, hpl]
    rfl

/-- The same, at every value of the columns handed too, with the side seated in `flatL Zp`, the list
that the lot's own text names. -/
theorem door_moves_at_lot {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Ky X₀ Y Pb : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side S ProofFile.Cl V (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (u : Member V (Local W₀ Rc ProofFile.Inst Tr) Y Pb) (pre t : List (Block S ProofFile.Cl)) (i : ℕ)
    (St : StandsAt cF.blocksInOrder R.first σ u pre t i)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (D : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing) (pl : K2.SwitchPlace)
    (Js : SimJob Pb) (fs : List (Fall S))
    (hσ : testSide (flatL Zp)
      (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) Js fs = some σ) :
    ∃ (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y) (s : S) (cs more : List OpenedColumn) (rest : List Fmt.RoundView)
      (tr : Tr),
      midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ =
        .ok (some m) ∧
      P.trace w₀ x = some tr ∧ m.st.input = ⟨w₀, rc, x, tr⟩ ∧
      r.run.views.1.rounds = m.seen ++ rest ∧
      m.seen.length = (pre.flatMap (·.rounds)).length + i ∧
      r.run.views.1.opened = cs ++ more ∧
      foldBlocks 0 pre
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₁ ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).pub x))
        (m.seen.take (pre.flatMap (·.rounds)).length) cs = .ok (s, [], []) ∧
      fillCols (readsOf 0 0 (P.storedWords w₀ rc)
        (treeOwn (r.run.played.1.take (pre.flatMap (·.rounds)).length))
        (pre.flatMap (·.rounds))
        ((m.seen.take (pre.flatMap (·.rounds)).length).map (·.drawn))) [] = .ok cs ∧
      ∃ T : T12, enterFinish s = .ok T ∧
        (∀ fr : Front Y, fr.seen.rounds = m.seen.take (pre.flatMap (·.rounds)).length →
          atHandAtL Zp m.st.input fr = true ∧ Agree (doorAtL Zp m.st.input fr) T) ∧
        ∀ (C : Type) (rd : C → TestCoins) (j : ℕ) (c : C) (sn : Seen)
          (st : State (Local W₀ Rc ProofFile.Inst Tr) Y), st.input = m.st.input →
          sn.rounds.length = (pre.flatMap (·.rounds)).length + j →
          sn.rounds.take (pre.flatMap (·.rounds)).length =
            m.seen.take (pre.flatMap (·.rounds)).length →
          (moveAt (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) rd j).say c
              sn st =
            (moveAt { (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) with
              rec₀ := fun _ _ => T } rd j).say c sn st :=
  door_moves_at_L h hR σ u pre t i St hrun hc D readers closing pl Js fs (flatL_at_head h ▸ hσ)

/-- **At the second member's stand, at its own front**: the state on entry is at hand and agrees,
but for the rows' targets, with what the way in returns at the state that the description's own fold
reaches. hi: the rounds of the side's parts in front of the member are the first part's. -/
theorem agree_at_rest {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) {Ky X₀ Y Pb : Type} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst} {k : Coins Bk}
    {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ Y} {r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)}
    (hR : ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k = .ok R)
    (σ : Side S ProofFile.Cl V (Local W₀ Rc ProofFile.Inst Tr) Y Pb)
    (u : Member V (Local W₀ Rc ProofFile.Inst Tr) Y Pb) (pre t : List (Block S ProofFile.Cl)) (i : ℕ)
    (St : StandsAt cF.blocksInOrder R.first σ u pre t i)
    (hrun : runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (D : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (closing : K2.Closing) (pl : K2.SwitchPlace)
    (Js : SimJob Pb) (fs : List (Fall S))
    (hσ : testSide cF.blocksInOrder
      (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) Js fs = some σ)
    (hi : i = firstLen (H2U.p12OfMade Zp.made).nums.stages) :
    ∃ (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Y) (s : S) (cs : List OpenedColumn) (T : T12),
      midAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Bk P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ =
        .ok (some m) ∧
      foldBlocks 0 pre
        ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).start₁ ((P5J.F0T OnBytes.secondHashFunction Zp Np cF).pub x))
        (m.seen.take (pre.flatMap (·.rounds)).length) cs = .ok (s, [], []) ∧
      enterFinish s = .ok T ∧
      atHandAtL Zp m.st.input
        (restFront (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) m) = true ∧
      Agree (doorAtL Zp m.st.input
        (restFront (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) m)) T := by
  obtain ⟨m, s, cs, -, -, -, a1, -, -, -, a5, -, a7, -, T, hT, b, -⟩ :=
    door_moves_at_L h hR σ u pre t i St hrun hc D readers closing pl Js fs hσ
  obtain ⟨e1, e2⟩ := b
    (restFront (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) m)
    (restFront_seen _ m _ (by rw [a5, hi]; rfl))
  exact ⟨m, s, cs, T, a1, a7, hT, e1, e2⟩

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.flatL
#print axioms ProofFile.Honest.K12.AtProof.startL
#print axioms ProofFile.Honest.K12.AtProof.doorAtL
#print axioms ProofFile.Honest.K12.AtProof.atHandAtL
#print axioms ProofFile.Honest.K12.AtProof.lotAtDoor
#print axioms ProofFile.Honest.K12.AtProof.flatL_at_head
#print axioms ProofFile.Honest.K12.AtProof.atHand_no_chain
#print axioms ProofFile.Honest.K12.AtProof.startL_own
#print axioms ProofFile.Honest.K12.AtProof.numbersL_at_head
#print axioms ProofFile.Honest.K12.AtProof.halves_lotAtDoor
#print axioms ProofFile.Honest.K12.AtProof.restFront_seen
#print axioms ProofFile.Honest.K12.AtProof.door_moves_at_L
#print axioms ProofFile.Honest.K12.AtProof.door_moves_at_lot
#print axioms ProofFile.Honest.K12.AtProof.agree_at_rest
