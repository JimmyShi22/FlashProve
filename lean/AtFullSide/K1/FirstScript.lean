-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/FirstScript.lean: the first chain's Script at the base prover of the online proof, as one
closed term.

The base prover is A.H, where onlineProverFromPublicFiles returns A at the filling onlineProverPartsInUse I secondHashFunction S Op
(AtFullSide/K1/RecordAtBase.lean). A Script says what the honest prover's oracle messages, pads and trees
are, as functions of a run's coins, the input and the challenges heard. Three kinds send oracle messages in
the first chain: the shared sending (K1), the code switch (K2) and the proximity test (K12).

  1  readersB, closingB, noTree, cellsB, tokB   the small parameters
  2  testJobAt, testOk, shapeAtSeat, testShareOf, testShareAt   the proximity test's share
  3  otherSendersAt   the code switch's share and the proximity test's, summed
  4  firstScriptAt   the Script: scriptAt at cellsB, tokB and otherSendersAt
  5  testJob_six, finish_at_base, otherSenders_at_head   under the head the test's job has six stages, the
     code switch's finish is found, and so the sum is the sum of the two written shares
  6  othersApart_first   what K1 asks of the other senders' record holds of otherSendersAt
  7  joinFit_first   the joined list is fit (JoinFit, Honest/Thread/JoinFit.lean). Its fields whole, owned
     and trees say: every seat that the first chain's flat list declares has a lot of messages and a lot
     of pads in this list, and every member that declares a tree is one of K1's 52, the code switch's 25
     or number 354. So no fourth kind sends an oracle message in the first chain
  8  k1Seated_first   K1's record at each of its 52 members, at firstScriptAt
  9  tie_k1_first   each message and pad of each of K1's 52 members is, in the Script's witness, the job's
     own text
     ownTrees_first, with its three readings at 2, at K1.noL l d and at 356   the thread's table of each tree
     of each of K1's 52 members is that member's job's own table, fixed right behind the rounds in front
 10  switch_in_first, ownMsgs_switch_first   the code switch's share lies in the record, and each message
     of which a switch is the first sender is, in the Script's witness, that switch's own text
 11  shapeAtSeat_at_head, finish_codes   under the head the plan's list has the test's ten seats, so
     shapeAtSeat's default is not read there; the finish's codes are the written plan's

Which values are whose.
  * readersB, closingB and the data widerRows S are the terms that the filling hands the kinds K2 and K12
    (widerFillOwn, Honest/AtPureWiderAt.lean; proxLotOf, Honest/AtPureWiderK12.lean).
  * testJobAt is the job of the one side that the filling's list for K12 lays
    (halves_head_L, AtFullSide/K12/FitsAtHeadL.lean).
  * cellsB is the matrix of cells of the index's reader. It is the only value that the hypothesis
    CellsAreIndex (Honest/K13/CellsAreIndex.lean) allows.
  * testOk, the parameter ok of the proximity test's texts, is "yes" everywhere: its authors' pick. Every law
    of this file holds at every value of that parameter.
  * tokB, shapeAtSeat and the codes pl.sizes.codes are this file's reading of what the authors of K7 and K12
    say these parameters are meant to be. No law of theirs has been called at them. The law that tokB is to
    meet is asked_of_instOf (Johnson/Desc/ProofFile/InstOf.lean).

Limits.
  * Three fallback values. testShareAt is the empty record where the code switch has no finish: under the
    head that is never so (finish_at_base). shapeAtSeat is the default shape where the plan has no such
    seat: under the head the ten seats are there (shapeAtSeat_at_head). noTree is read at no member that
    declares a tree
    (tl_reads_no_rest, Honest/Thread/Join.lean, with joinFit_first's field trees).
  * "Fit" speaks of numbers, seats, places, counts and of lots that agree. A lot whose text answers nothing
    counts like any other, and where no lot answers the Script holds 0. That the texts answer is their
    authors' laws, under public tests and where the book lends the part its coins.
  * Nothing here says that the prover's sides of the kinds K2 and K12 play these texts.
  * The head h and the return hA are hypotheses. The numbers 77 and 354 are written by hand.
  * The first chain alone. The full size alone.
  * This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.K1.RecordAtBase
import AtFullSide.K2.JoinFitFull
import AtFullSide.K12.FitsAtHeadL
import AtFullSide.K12.RestTiesAtHeadL
import Johnson.Desc.ProofFile.Honest.K12.ScriptLotsAtL
import Johnson.Bind.ForProver.CellsInField
import AtFullSide.K1.MomentZeroWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles (numsRef)
open OnBytes.Maker (WholeD)
open OnBytes.Slice (frS frZ)
open Bind.ForProver (cellsOfF)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2 (switchShareAt)

variable {W₀ : Type}

/-! ## 1 The small parameters -/

/-- The readers that the filling hands the kinds K2 and K12, at the public part Zq. -/
def readersB (I : WiderIn W₀) (Zq : ProofFile.Pub) : LocB W₀ → Readers :=
  fun v => ⟨v.trace, I.weights Zq v.w₀, v.rc⟩

/-- The code switch's closing, as its authors' law names it. -/
def closingB (Zq : ProofFile.Pub) (G : ProofFile.Ground) : K2.Closing :=
  K2.lotClosingAt G.first.layout (K2.segmentsOf Zq G)

/-- The lot of trees for a member that declares no tree: the table without a word. -/
def noTree {Bk : ProverCoinCounts} {W : Type} : Nat → TreeLot Bk W :=
  fun _ => ⟨fun _ _ _ _ => (default, wordlessTable), fun _ => 0⟩

/-- **The witness's cells**: the matrix of cells of the index's reader. -/
def cellsB (I : WiderIn W₀) (Zq : ProofFile.Pub) : LocB W₀ → CellsM OnBytes.Flat.numsFull :=
  fun v => cellsOfF frS frZ 402653181 numsRef (I.weights Zq v.w₀).entry

/-- **The witness's token**: the number of the reply that the instance asks about. -/
def tokB : LocB W₀ → P5J.At.Tok :=
  fun v => OnBytes.Desc.Reply.tokOf v.x.asked

/-! ## 2 The proximity test's share -/

/-- The job of the proximity test's side, at the code switch's finish pl. -/
def testJobAt (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Zq : ProofFile.Pub) (G : ProofFile.Ground)
    (pl : K2.SwitchPlace) : K12.TestJob (LocB W₀) Unit :=
  K12.AtProof.jobL (H2U.p12OfMade Zq.made) (K12.AtProof.doorAtL Zq) (widerRows S Zq G) (readersB I Zq)
    (closingB Zq G) pl

/-- **The proximity test's lots never refuse of themselves**: the parameter ok of its authors' texts, at
"yes". So the Script's tables and messages at the test's place are what the job's side plays at every stand,
also where the carrying message's rows are not there and the job's first stage goes on with zeros (rowsL,
Honest/K12/AtProof/JobL.lean). The pick of the proximity test's authors. -/
def testOk : LocB W₀ → List Fmt.Drawn → (Nat → K12.Stretch) → Bool :=
  fun _ _ _ => true

/-- The shape of the message at tenant t of tree j, off the plan's list of seats; the default shape
where the list has no such seat. -/
def shapeAtSeat (Zq : ProofFile.Pub) (j t : Nat) : OnBytes.OracleShape :=
  (((P5J.At.pseatsAll Zq).find? fun q => q.j == j && q.t == t).map (·.shape)).getD default

/-- The proximity test's share at the finish pl. -/
def testShareOf (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit)
    (cF : Chain TS ProofFile.Cl) (pl : K2.SwitchPlace) : Others A.B (LocB W₀) :=
  K12.k12Share 0 (testJobAt I S A.Z A.G pl) () (roundsTo cF.blocksInOrder 354) 77 (P5J.At.arr A.Z)
    testOk pl.sizes.codes (fun τ => shapeAtSeat A.Z (77 + τ) 0)
    (fun τ => shapeAtSeat A.Z (77 + τ) 1) 354 noTree

/-- **The proximity test's share.** The empty record where the code switch has no finish. -/
def testShareAt (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit)
    (cF : Chain TS ProofFile.Cl) : Others A.B (LocB W₀) :=
  ((K12.AtProof.finishAt A.Z A.G).map (testShareOf I S A cF)).getD ⟨[], [], noTree, []⟩

/-! ## 3 The other senders, and the Script -/

/-- The code switch's share at the base prover. -/
def switchShareB (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit)
    (cF : Chain TS ProofFile.Cl) : Others A.B (LocB W₀) :=
  switchShareAt A.B cF.blocksInOrder 0 A.Z A.G (widerRows S A.Z A.G) (readersB I A.Z) noTree

/-- **The record of the senders beside K1**: the code switch's share, then the proximity test's. -/
def otherSendersAt (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit)
    (cF : Chain TS ProofFile.Cl) : Others A.B (LocB W₀) :=
  (switchShareB I S A cF).add (testShareAt I S A cF)

/-- **THE FIRST CHAIN's SCRIPT AT THE BASE PROVER.** -/
def firstScriptAt (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (Op : OnlineProverArguments)
    (A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit) (cF : Chain TS ProofFile.Cl) :
    Script A.B (LocB W₀) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT :=
  scriptAt I S Op A cF (cellsB I A.Z) tokB (otherSendersAt I S A cF)

/-! ## 4 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Where the finish is found, the share is the share at it. -/
theorem testShareAt_some {pl : K2.SwitchPlace} (hf : K12.AtProof.finishAt A.Z A.G = some pl) :
    testShareAt I S A cF = testShareOf I S A cF pl :=
  congrArg (fun o : Option K2.SwitchPlace =>
    (o.map (testShareOf I S A cF)).getD ⟨[], [], noTree, []⟩) hf

/-- **Under the head the test's job has six stages**, at every place pl. -/
theorem testJob_six (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x) (pl : K2.SwitchPlace) :
    (testJobAt I S A.Z A.G pl).p.nums.stages.length = 6 := by
  show (H2U.p12OfMade A.Z.made).nums.stages.length = 6
  rw [K12.AtProof.numbersL_at_head h.toAtMg, K12.Light.nums_head_L h.toAtMg]
  exact K12.stages_LFull

/-- **Under the head, where the maker returns, the code switch's finish is found.** -/
theorem finish_at_base (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) :
    ∃ pl, K12.AtProof.finishAt A.Z A.G = some pl := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  obtain ⟨pl, hf, -⟩ := K12.AtProof.fitsL_head_L h.toAtMg (G := A.G) (by rw [eG]; exact O.blank)
  exact ⟨pl, hf⟩

/-- **So the record is the sum of the two written shares.** -/
theorem otherSenders_at_head (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) :
    ∃ pl, K12.AtProof.finishAt A.Z A.G = some pl ∧
      otherSendersAt I S A cF = (switchShareB I S A cF).add (testShareOf I S A cF pl) := by
  obtain ⟨pl, hf⟩ := finish_at_base h hA
  exact ⟨pl, hf, congrArg (switchShareB I S A cF).add (testShareAt_some hf)⟩

/-- **What K1 asks of the other senders' record holds of it.** Under the head and the maker's return
alone. -/
theorem othersApart_first (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) :
    OthersApart A (otherSendersAt I S A cF) := by
  obtain ⟨pl, -, e⟩ := otherSenders_at_head h hA
  rw [e]
  exact othersApart_at_shares h hA (widerRows S A.Z A.G) (readersB I A.Z) noTree 0
    (testJobAt I S A.Z A.G pl) (testJob_six h pl) () (roundsTo cF.blocksInOrder 354) testOk
    pl.sizes.codes (fun τ => shapeAtSeat A.Z (77 + τ) 0) (fun τ => shapeAtSeat A.Z (77 + τ) 1) noTree

/-- **THE JOINED LIST OF ALL THREE SENDERS IS FIT.** Under the head and the maker's return alone. Its
fields whole, owned and trees: no fourth kind sends an oracle message in the first chain. -/
theorem joinFit_first (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) :
    JoinFit cF.blocksInOrder 0 (P5J.At.arr A.Z) (P5J.At.seats A.Z) (witB I A.Z) ()
      (k1MembersW (jobTwoAt S A.Z A.G) (jobLaterAt S A.Z A.G) (jobWAt Op A.Z A.G))
      (otherSendersAt I S A cF) := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  obtain ⟨pl, -, e⟩ := otherSenders_at_head h hA
  have F := K2.Law.joinFit_full h O hA (lotNo OnBytes.secondHashFunction A.Z) (lotData S)
    (K13.wDataAt Op.pile) 0 (witB I A.Z) () (widerRows S A.Z A.G) (readersB I A.Z) noTree 0
    (testJobAt I S A.Z A.G pl) (testJob_six h pl) () (roundsTo cF.blocksInOrder 354) testOk
    pl.sizes.codes (fun τ => shapeAtSeat A.Z (77 + τ) 0) (fun τ => shapeAtSeat A.Z (77 + τ) 1) noTree
  rw [byNo_at_head h O, ← eG] at F
  rw [e]
  exact F

/-- **K1Seated, all twenty fields, at each of the 52 members, at the closed Script.** Under the head and
the maker's return alone; the other ten parameters of lettersHead are bound by "for all". -/
theorem k1Seated_first (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀) :
    (∃ blk, K1Seated (lettersHead h A.H (firstScriptAt I S Op A cF)
        test carryX item n₁ n₂ b₀ Vd Rd Kp w)
      2 blk (witB I A.Z) (jobTwoAt S A.Z A.G) () .opening (P5J.At.arr A.Z) (P5J.At.seats A.Z)
      (P5J.At.ms A.Z Z.lay) (K1.radRec 0 (jobTwoAt S A.Z A.G).P)) ∧
    (∀ l, l < 25 → ∀ d : Bool, ∃ blk, K1Seated (lettersHead h A.H
        (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w)
      (K1.noL l d) blk (witB I A.Z) (jobLaterAt S A.Z A.G l d) () (cond d (.digits l) (.reads l))
      (P5J.At.arr A.Z) (P5J.At.seats A.Z) (P5J.At.ms A.Z Z.lay)
      (K1.radRec (3 * l + (if d then 2 else 1)) (jobLaterAt S A.Z A.G l d).P)) ∧
    (∃ blk, K1Seated (lettersHead h A.H (firstScriptAt I S Op A cF)
        test carryX item n₁ n₂ b₀ Vd Rd Kp w)
      356 blk (witB I A.Z) (jobWAt Op A.Z A.G) () .w (P5J.At.arr A.Z) (P5J.At.seats A.Z)
      (P5J.At.ms A.Z Z.lay) (K1.radRec 81 (jobWAt Op A.Z A.G).P)) :=
  k1Seated_at_base h hA (cellsB I A.Z) tokB (otherSendersAt I S A cF) (othersApart_first h hA)
    test carryX item n₁ n₂ b₀ Vd Rd Kp w

/-! ## 5 K1's messages, pads and trees -/

/-- **EACH MESSAGE AND EACH PAD OF EACH OF K1's 52 MEMBERS IS, IN THE SCRIPT's WITNESS, THAT MEMBER's JOB's
OWN TEXT.** Under the head and the maker's return alone, at every Vd. Where a text answers nothing this
says nothing: K1's messages' texts
answer at every entry at this book (k1_answers, Honest/Thread/Join.lean, from joinFit_first's field
coins). -/
theorem tie_k1_first (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (Vd : LocB W₀ → Prop) {y : Nat × SendJob (PlaceIn ProofFile.Inst) Unit}
    (hy : y ∈ k1MembersW (jobTwoAt S A.Z A.G) (jobLaterAt S A.Z A.G) (jobWAt Op A.Z A.G)) :
    (∀ n, n < y.2.P.sent.size →
      OwnMsgs (firstScriptAt I S Op A cF) Vd (0 + roundsTo cF.blocksInOrder y.1)
        (P5J.At.arr A.Z (seatAtMember cF.blocksInOrder y.1 y.2.P n).1 (seatAtMember cF.blocksInOrder y.1 y.2.P n).2)
        (0 + roundsTo cF.blocksInOrder y.1) (msgTxt 0 (witB I A.Z) y.2 () n)) ∧
    ∀ n, n < y.2.P.sent.size →
      OwnPads (firstScriptAt I S Op A cF) Vd (seatAtMember cF.blocksInOrder y.1 y.2.P n).1
        (seatAtMember cF.blocksInOrder y.1 y.2.P n).2 (fun k _ => padTxt 0 y.2 n k) :=
  join_tie_k1_fit (joinFit_first h hA) (cellsB I A.Z) tokB Vd hy


/-- **THE THREAD's TABLE OF EACH TREE OF EACH OF K1's 52 MEMBERS IS THE JOB's OWN**, and it is fixed right
behind the rounds in front of the member. Under the head and the maker's return alone; the other ten
parameters of lettersHead are bound by "for all". At a job whose plan has no tree it says nothing. -/
theorem ownTrees_first (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀) {y : Nat × SendJob (PlaceIn ProofFile.Inst) Unit}
    (hy : y ∈ k1MembersW (jobTwoAt S A.Z A.G) (jobLaterAt S A.Z A.G) (jobWAt Op A.Z A.G)) :
    OwnTrees (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      y.1 y.2.P.trees.length (treeTbl 0 (witB I A.Z) y.2 ()) fun _ => 0 := by
  have F := joinFit_first h hA
  obtain ⟨blk, hb, -⟩ := F.found y hy
  rw [← F.fits y hy blk hb]
  exact join_trees_k1 (front := 0) (arr := P5J.At.arr A.Z) (O := otherSendersAt I S A cF)
    (cellsB I A.Z) tokB _ rfl rfl rfl rfl (k1MembersW_nodup _ _ _) hy hb

/-- At number 2. -/
theorem ownTrees_first_two (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀) :
    OwnTrees (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      2 (jobTwoAt S A.Z A.G).P.trees.length (treeTbl 0 (witB I A.Z) (jobTwoAt S A.Z A.G) ()) fun _ => 0 :=
  ownTrees_first h hA test carryX item n₁ n₂ b₀ Vd Rd Kp w
    (mem_k1MembersW.2 (.inl (mem_k1Members.2 (.inl rfl))))

/-- At each of the fifty. -/
theorem ownTrees_first_later (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀) {l : Nat} (hl : l < 25) (d : Bool) :
    OwnTrees (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (K1.noL l d) (jobLaterAt S A.Z A.G l d).P.trees.length
      (treeTbl 0 (witB I A.Z) (jobLaterAt S A.Z A.G l d) ()) fun _ => 0 :=
  ownTrees_first h hA test carryX item n₁ n₂ b₀ Vd Rd Kp w
    (mem_k1MembersW.2 (.inl (mem_k1Members.2 (.inr ⟨l, hl, d, rfl⟩))))

/-- At number 356. -/
theorem ownTrees_first_w (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀) :
    OwnTrees (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      356 (jobWAt Op A.Z A.G).P.trees.length (treeTbl 0 (witB I A.Z) (jobWAt Op A.Z A.G) ()) fun _ => 0 :=
  ownTrees_first h hA test carryX item n₁ n₂ b₀ Vd Rd Kp w (mem_k1MembersW.2 (.inr rfl))

/-! ## 6 What the spenders of a switch's message can call -/

/-- The code switch's share lies in the record. No hypothesis. -/
theorem switch_in_first : K2.Law.ShareIn (switchShareB I S A cF) (otherSendersAt I S A cF) :=
  K2.Law.shareIn_add_left _ _

/-- **A MESSAGE OF WHICH A SWITCH IS THE FIRST SENDER IS, IN THE SCRIPT's WITNESS, THAT SWITCH's OWN
TEXT**: at each place of the code switch, at the carrying message and at every message behind the kept
copies: the next segment's own messages of moment 0, the one with the segment's mask row among them
where it is of that moment, and the next fold's fresh mask. Where the text answers nothing this says
nothing: that it answers is msgTxt_isSome (Honest/K2/Law/LotsAnswer.lean), under a public test and where
the book lends the part its own cut and every stretch that it carries. -/
theorem ownMsgs_switch_first (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (Vd : LocB W₀ → Prop) (N : Nat) {p : K2.SwitchPlace} (hp : p ∈ K2.switchPlaces A.Z A.G) {n : Nat}
    (hn : n < (K2.switchSent p.sizes p.others).size) (h1 : K2.firstSender p n = true) :
    OwnMsgs (firstScriptAt I S Op A cF) Vd N (K2.switchNum A.Z p n)
      (0 + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder p.place))
      (K2.switchMsgTxt 0 (widerRows S A.Z A.G) (readersB I A.Z) (closingB A.Z A.G) p n) :=
  K2.Law.share_msgs_fit 0 (K2.coreSender K2.freshTable) (widerRows S A.Z A.G) (readersB I A.Z)
    (closingB A.Z A.G) _ _ _ _ _ _ noTree (joinFit_first h hA) (switch_in_first (I := I) (S := S))
    (cellsB I A.Z) tokB Vd N hp hn h1

/-! ## 7 The two parameters of the pads' places -/

/-- **Under the head the plan's list has the proximity test's ten seats**: shapeAtSeat's default is not
read there. -/
theorem shapeAtSeat_at_head (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x) {τ t : Nat} (hτ : τ < 5)
    (ht : t < 2) :
    ∃ q ∈ P5J.At.pseatsAll A.Z, q.j = 77 + τ ∧ q.t = t ∧ shapeAtSeat A.Z (77 + τ) t = q.shape := by
  have hs : ((P5J.At.pseatsAll A.Z).find? fun q => q.j == 77 + τ && q.t == t).isSome = true := by
    rw [K2.Law.pseatsAll_at_head h.toAtMg]
    exact List.all_eq_true.1 (List.all_eq_true.1 testSeatsW.1 τ (List.mem_range.2 hτ)) t
      (List.mem_range.2 ht)
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hs
  have hp : (q.j == 77 + τ && q.t == t) = true := by
    have hp' := List.find?_some hq
    exact hp'
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hp
  exact ⟨q, List.mem_of_find?_eq_some hq, hp.1, hp.2,
    congrArg (fun o : Option P5T.PSeat =>
      (o.map fun s : P5T.PSeat => s.shape).getD (default : OnBytes.OracleShape)) hq⟩

/-- **Under the head the finish's codes are the written plan's.** -/
theorem finish_codes (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    {pl : K2.SwitchPlace} (hf : K12.AtProof.finishAt A.Z A.G = some pl) :
    pl.sizes.codes = Johnson.G.proofSends0.codes := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have hp : pl ∈ K2.switchPlaces A.Z A.G := List.mem_of_find?_eq_some hf
  rw [K12.AtProof.places_head h.toAtMg (G := A.G) (by rw [eG]; exact O.blank)] at hp
  exact of_decide_eq_true (List.all_eq_true.1 K2.Law.sentMeetsW.2 pl hp)

end ProofFile.Honest.K1

end

#print axioms ProofFile.Honest.K1.firstScriptAt
#print axioms ProofFile.Honest.K1.testJob_six
#print axioms ProofFile.Honest.K1.finish_at_base
#print axioms ProofFile.Honest.K1.otherSenders_at_head
#print axioms ProofFile.Honest.K1.othersApart_first
#print axioms ProofFile.Honest.K1.joinFit_first
#print axioms ProofFile.Honest.K1.k1Seated_first
#print axioms ProofFile.Honest.K1.tie_k1_first
#print axioms ProofFile.Honest.K1.ownTrees_first
#print axioms ProofFile.Honest.K1.ownTrees_first_two
#print axioms ProofFile.Honest.K1.ownTrees_first_later
#print axioms ProofFile.Honest.K1.ownTrees_first_w
#print axioms ProofFile.Honest.K1.shapeAtSeat_at_head
#print axioms ProofFile.Honest.K1.finish_codes
#print axioms ProofFile.Honest.K1.switch_in_first
#print axioms ProofFile.Honest.K1.ownMsgs_switch_first
