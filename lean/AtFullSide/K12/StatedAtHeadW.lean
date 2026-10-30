-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/StatedAtHeadW.lean: THE REQUEST's OWN PROXIMITY TEST (the place W, the last chain),
THE FULL SIZE: THE MEMBERS BY POSITION AGAINST THE MAKER's PROPERTY, BY NAME AND COUNT. WHAT THE
BARE JOB `bareW`'s TWO PARTS STATE AS CARRIED IS WHAT THE MAKER's BOOK CARRIES TO THEM. PUBLIC DATA
ALONE: names, addresses, counts. Four definitions of rows, one test, and the theorems below.

Why. The frame lends a part its coins only where the part states just the names and counts that the
book has for it. At this test the job's list (`membersW`, `freshW`,
Johnson/Desc/ProofFile/Honest/K12/AtProof/MembersW.lean) picks its messages BY POSITION: the last of
the first sending; W's sending's but its last; message 0 of Omega's. The book's maker picks them BY
A PROPERTY (`bookRaw`, Honest/BookWhole.lean). MembersW.lean's head: «nothing here shows that they
agree». Until now only their number was held (`hT_head_W`, TiesAtHeadW.lean in this folder).

  `omegaDueB`, `omegaDue_real`, `omegaDue_head`   message 0 of Omega's sending, by the sending's own
                 reckoning: 42853 coins
  `rowIF`, `rowWF`, `rowOF`, `membersWF`   the three members at the written plans
  `statedW_W`, `statedW_W_bite`   these, and W's fresh table, ARE THE WRITTEN ENTRIES
                 `rawCarriesWW` (AtFullSide/K14/RawSmallWritten.lean); a control
  `membersW_head`, `freshW_head`, `firstRide_head`   under the head the job's lists are these
  `carryE_at_W`   at the maker's book the part at the test's place carries those written entries
  `carried_stated_W`   THE LAW

By what. The library's `eG_atAll`, `pin1_atAll`, `hs_atAll`; K1's authors' `msg_w_head`,
`parW_written`; `stages_at_head`, `written_at_head`, `qAt_written`
(Johnson/Desc/ProofFile/Honest/K12/); the shared rounds' authors' `bookWhole_returns_written_ahead`
and `rawCarriesWW`; the frame's authors' `segmentCarries_filter` and `BookRow`'s lemmas.

Limits.
- NAMES AND COUNTS ALONE. Where a run begins among its owner's coins is compared with nothing here.
- The job is the bare one: `bareW` has public numbers alone; its rows and trees are idle. No job
  with rows stands at this test. That a filling holds these parts is said nowhere here.
- That `bareW` returns a job is a premise (hJ): that `sendPub` returns under the head is not shown
  here: the law may be idle.
- IN `statedW_W` OMEGA's COUNT IS A LITERAL, THE WRITTEN ENTRY's NUMBER: there only its name is
  tried. The sender's reckoning meets that number in `omegaDue_real`, spent in `membersW_head`.
- The control tries a position, an order and a count. W's message and Omega's name have none.
- The ground of the law is the head's own (`Bs.G₀`).
- WHAT THE PARTS SPEND, AND THAT THE FRAME LENDS, IS NOT HERE.
- The written facts' own limits bind: WP's values were printed by Lean's evaluator; evaluations in
  Lean's kernel, which no independent checker has replayed.
- All limits of MembersW.lean and of AtProof/Bare.lean stand. The full size alone.
- What may be said of this pair on hiding stands in the head of
  Johnson/Desc/ProofFile/Honest/K12/AtProof/HalfW.lean.
- It moves no count. Nothing on completeness, soundness or hiding.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.TiesAtHeadW
import AtFullSide.K14.BookWholeWritten
import AtFullSide.K14.RawSmallWritten
import Johnson.Desc.ProofFile.Honest.BookCarryKit
import Johnson.Desc.ProofFile.Honest.BookWritten.SentFirst
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsAtW
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsWritten
import Johnson.Desc.ProofFile.Honest.K12.AtProof.MembersW
import Johnson.Desc.ProofFile.Honest.K12.FitAtHead
import Johnson.Desc.ProofFile.Honest.K12.StagesAtHead
import Johnson.Desc.ProofFile.Honest.K14.AtFilling

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain Block)
open ProofFile.Honest (ProverCoinCounts Addr Due Ahead bookWhole mergesByName carryE carriedName segmentCarries
  segmentCarries_filter segmentCarriesAt)
open ProofFile.Honest.K12 (TestJob dueFresh memberRuns freshRun freshFrom)
open ProofFile.Honest.K12.AtProof (placeW senderW senderI senderO msgK1 msgOf membersW freshW parI parWAt
  sendPub bareW bareJob four fourOf p12At_place)
open H2K.Member (piWFull)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull codesFull2)
open AtFullSide.K14 (rawAheadW rawWantsW rawSegW rawSeg_returns rawCarriesFoldedW rawCarriesOmegaW
  rawCarriesWW rawOwnCarryW foldsFirstW foldsSharedW bookWhole_returns_written_ahead)
open P5J (TS)

/-! ## 1 At the written values -/

/-- Message 0 of Omega's sending takes 42853 coins, by the sending's own reckoning. -/
def omegaDueB (A : ProofFile.Honest.K14.SendPub) : Bool :=
  ProofFile.Honest.K14.dueOf (ProofFile.Honest.K14.jobOmega A).Q.codes
    ((ProofFile.Honest.K14.jobOmega A).Q.sent.getD 0 default).shape
    ((ProofFile.Honest.K14.jobOmega A).sort 0) == 42853

/-- The test reads of the public data the codes and the shape alone. -/
theorem omegaDueB_plan (A : ProofFile.Honest.K14.SendPub) :
    omegaDueB A = omegaDueB (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S) := rfl

/-- It accepts at the typed sizes over a proof file's own codes. An evaluation in Lean's kernel. -/
theorem omegaDue_real : (VerifiableInference.Desc.K1.realSized.all fun q =>
    omegaDueB (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)) = true := by decide +kernel

/-- The index-mask message: the last of the first sending, at the written plan. -/
def rowIF : Addr × Nat × Due :=
  msgK1 senderI VerifiableInference.Desc.K1.parGF
    (ProofFile.Honest.K1.firstRide VerifiableInference.Desc.K1.qFull)
    (VerifiableInference.Desc.K1.parGF.sent.size - 1)

/-- W: message 0 of its sending, at the written plan. -/
def rowWF : Addr × Nat × Due := msgK1 senderW VerifiableInference.Desc.K1.parWF (fun _ => none) 0

/-- Omega: message 0 of its sending. ITS COUNT IS THE WRITTEN ENTRY's NUMBER, A LITERAL: the
sender's reckoning meets it in `omegaDue_real`. -/
def rowOF : Addr × Nat × Due := (senderO, 0, ⟨0, 42853⟩)

/-- The group at the written plans, in the job's order. -/
def membersWF : List (Addr × Nat × Due) := [rowIF, rowWF, rowOF]

set_option maxRecDepth 1000000 in
/-- **THE MEMBERS BY POSITION, AND W's FRESH TABLE, ARE THE WRITTEN ENTRIES**, names and counts, in
order, at both parts. Left: the texts of `memberRuns` and `freshRun` at the written rows; of Omega's
the name alone is tried here (`rowOF`). Right: the entries that the frame's maker lays by its
property, written out. -/
theorem statedW_W :
    membersWF.map (fun m => (carriedName m.1 m.2.1 ⟨placeW, 0⟩, m.2.2)) =
        (rawCarriesWW.filter fun e => e.spender == ⟨placeW, 0⟩).map Ahead.named ∧
      membersWF.map (fun m => (carriedName m.1 m.2.1 ⟨placeW, 1⟩, m.2.2)) ++
          [(carriedName senderW 1 ⟨placeW, 1⟩,
            ⟨0, dueFresh (piWFull.nums.stages.headD default)⟩)] =
        (rawCarriesWW.filter fun e => e.spender == ⟨placeW, 1⟩).map Ahead.named := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The evaluation can fail, and it feels a position, an order and a count: with the first sending's
message 3 in the place of its last, with the first two members swapped, and with the fresh table's
count greater by one, the comparison says no. -/
theorem statedW_W_bite :
    decide ((msgK1 senderI VerifiableInference.Desc.K1.parGF
        (ProofFile.Honest.K1.firstRide VerifiableInference.Desc.K1.qFull) 3 :: [rowWF, rowOF]).map
          (fun m => (carriedName m.1 m.2.1 ⟨placeW, 0⟩, m.2.2)) =
        (rawCarriesWW.filter fun e => e.spender == ⟨placeW, 0⟩).map Ahead.named) = false ∧
      decide ([rowWF, rowIF, rowOF].map (fun m => (carriedName m.1 m.2.1 ⟨placeW, 0⟩, m.2.2)) =
        (rawCarriesWW.filter fun e => e.spender == ⟨placeW, 0⟩).map Ahead.named) = false ∧
      decide (membersWF.map (fun m => (carriedName m.1 m.2.1 ⟨placeW, 1⟩, m.2.2)) ++
          [(carriedName senderW 1 ⟨placeW, 1⟩,
            ⟨0, dueFresh (piWFull.nums.stages.headD default) + 1⟩)] =
        (rawCarriesWW.filter fun e => e.spender == ⟨placeW, 1⟩).map Ahead.named) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The written entries are no spending entries. -/
theorem rawCarriesWW_kept : ∀ e ∈ rawCarriesWW, e.once = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The entries of the two chains' folds are spent once. -/
theorem folds_once : ((foldsFirstW ++ foldsSharedW).all fun e => e.once) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The other written carrying entries name no part at the test's place. -/
theorem others_off : ((rawCarriesFoldedW ++ rawCarriesOmegaW ++ rawOwnCarryW).all fun e =>
    e.spender.place != placeW) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The chain of segments carries nothing to the test's two parts. -/
theorem seg_off : (segmentCarriesAt (ProofFile.Honest.planOf WP.first.blocksInOrder) ProofFile.Honest.sentFirstW
      ⟨placeW, 0⟩).isEmpty = true ∧
    (segmentCarriesAt (ProofFile.Honest.planOf WP.first.blocksInOrder) ProofFile.Honest.sentFirstW
      ⟨placeW, 1⟩).isEmpty = true := by
  unfold segmentCarriesAt ProofFile.Honest.linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-! ## 2 On the book -/

/-- hB is a premise. **AT THE MAKER's BOOK THE TWO PARTS OF THE TEST CARRY THE WRITTEN ENTRIES.** -/
theorem carryE_at_W {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) {a : Addr} (ha : a = ⟨placeW, 0⟩ ∨ a = ⟨placeW, 1⟩) :
    carryE B a = rawCarriesWW.filter fun e => e.spender == a := by
  obtain ⟨B', h', e'⟩ := bookWhole_returns_written_ahead
  obtain rfl : B' = B := Except.ok.inj (h'.symm.trans hB)
  have hp : a.place = placeW := by rcases ha with rfl | rfl <;> rfl
  have s0 : ∀ e ∈ rawWantsW.map (·.entry), e.once = true := by
    intro e he
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 he
    rfl
  have s1 : ∀ e ∈ foldsFirstW ++ foldsSharedW, e.once = true := fun e he =>
    List.all_eq_true.1 folds_once e he
  have s2 : ∀ e ∈ [ProofFile.Honest.K14.splitEntryWritten], e.once = true := by
    intro e he
    rw [List.mem_singleton.1 he]
    rfl
  have s3 : ∀ e ∈ rawCarriesFoldedW ++ rawCarriesOmegaW ++ rawOwnCarryW, e.spender ≠ a := by
    intro e he q
    have k := List.all_eq_true.1 others_off e he
    rw [q, hp] at k
    simp at k
  have s4 : rawSegW.filter (fun e => e.spender == a) = [] := by
    rw [segmentCarries_filter rawSeg_returns a]
    have k := seg_off
    rcases ha with rfl | rfl
    · exact List.isEmpty_iff.1 k.1
    · exact List.isEmpty_iff.1 k.2
  have c1 := ProofFile.Honest.BookRow.carry_spent (a := a) s0
  have c2 := ProofFile.Honest.BookRow.carry_spent (a := a) s1
  have c3 := ProofFile.Honest.BookRow.carry_spent (a := a) s2
  have c4 := ProofFile.Honest.BookRow.carry_other (a := a) s3
  have c5 := ProofFile.Honest.BookRow.carry_kept (a := a) rawCarriesWW_kept
  simp only [List.filter_append] at c2 c4
  simp only [List.append_eq_nil_iff] at c2 c4
  unfold carryE
  rw [e']
  unfold AtFullSide.K14.rawAheadW
  simp only [List.filter_append, List.filter_nil, s4]
  rw [c1, c2.1, c2.2, c3, c4.1.1, c4.1.2, c4.2, c5]
  simp

/-! ## 3 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The test on Omega's message accepts at the shared chain's own plan, under the head. -/
theorem omegaDue_head (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF) (a : Nat) :
    omegaDueB ⟨VerifiableInference.Desc.K1.qAt Zp Np, a⟩ = true := by
  obtain ⟨y, hy, Wr⟩ := ProofFile.Honest.K12.Light.written_at_head h
  have k := omegaDue_real
  rw [hy] at k
  have k' : omegaDueB (ProofFile.Honest.K12.Light.planOf codesFull2 y.shape) = true := k
  rw [omegaDueB_plan, ProofFile.Honest.K12.Light.qAt_written Wr Np]
  exact k'

variable (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x) {Bs : ProofFile.PureBase}
  {base : List (Block TS ProofFile.Cl)}
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
    (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
include h O

/-- Under the head the first sending's ride is the written one. -/
theorem firstRide_head :
    ProofFile.Honest.K1.firstRide Bs.G₀.first =
      ProofFile.Honest.K1.firstRide VerifiableInference.Desc.K1.qFull := by
  have hs : Bs.G₀.first.shape = VerifiableInference.Desc.K1.qFull.shape :=
    (VerifiableInference.Desc.K1.hs_atAll h O (VerifiableInference.Desc.K1.pin1_atAll h)).trans rfl
  funext k
  unfold ProofFile.Honest.K1.firstRide VerifiableInference.Desc.K1.frame₀
  rw [hs]

/-- Under the head W's fresh table is the second message of W's sending. -/
theorem freshW_head : freshW Zp = some (senderW, 1) := by
  unfold freshW parWAt
  rw [ProofFile.Honest.K1.msg_w_head h O]
  show some (senderW, (VerifiableInference.Desc.K1.parW Zp.first (ProofFile.Honest.K1.wGp Zp) 4
    VerifiableInference.Desc.K13.Law.wMsgFull).sent.size - 1) = _
  have e : VerifiableInference.Desc.K1.parWF.sent.size - 1 = 1 := by decide +kernel
  rw [ProofFile.Honest.K1.parW_written h O, e]

/-- **Under the head, at the head's ground, the job's list is the written one.** -/
theorem membersW_head {ms : List (Addr × Nat × Due)} (hm : membersW Zp Bs.G₀ = some ms) :
    ms = membersWF := by
  unfold membersW at hm
  obtain ⟨P, hP, hm⟩ := Option.bind_eq_some_iff.1 hm
  obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.1 hm
  have eP : P = VerifiableInference.Desc.K1.parWF := by
    unfold parWAt at hP
    rw [ProofFile.Honest.K1.msg_w_head h O] at hP
    exact (Option.some.inj hP).symm.trans (ProofFile.Honest.K1.parW_written h O)
  subst eP
  have eA : A.P = VerifiableInference.Desc.K1.qAt Zp Np := by
    unfold sendPub at hA
    rw [(ProofFile.Honest.K14.readers_at Zp Np h.laid.places).1] at hA
    change Option.map _ _ = some A at hA
    obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.1 hA
    rfl
  have ho : omegaDueB A = true := by
    have k := omegaDue_head h.toAtMg A.atPoint
    rw [← eA] at k
    exact k
  have eO : msgOf senderO (ProofFile.Honest.K14.jobOmega A) 0 = rowOF := by
    unfold omegaDueB at ho
    have e := beq_iff_eq.1 ho
    unfold msgOf rowOF
    rw [e]
  have er : List.range (VerifiableInference.Desc.K1.parWF.sent.size - 1) = [0] := by decide +kernel
  unfold parI
  rw [VerifiableInference.Desc.K1.eG_atAll h O (VerifiableInference.Desc.K1.pin1_atAll h),
    firstRide_head h O, er, eO]
  rfl

/-- hB and hJ are premises. **AT THE MAKER's BOOK WHAT IT CARRIES TO THE TWO PARTS OF THE TEST IS
WHAT THEY STATE**, names and counts, in order, at the bare job at the head's ground. The parts state
it at the job's own place: the first clause says that that is `placeW`. -/
theorem carried_stated_W {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) {W X : Type} {J : TestJob W X}
    (hJ : bareW Zp Bs.G₀ = some J) :
    J.p.place = placeW ∧ (carryE B ⟨placeW, 0⟩).map Ahead.named = memberRuns J ⟨placeW, 0⟩ ∧
      (carryE B ⟨placeW, 1⟩).map Ahead.named = memberRuns J ⟨placeW, 1⟩ ++ [freshRun J] := by
  unfold bareW at hJ
  obtain ⟨F, hF, hJ⟩ := Option.bind_eq_some_iff.1 hJ
  obtain ⟨ms, hms, rfl⟩ := Option.map_eq_some_iff.1 hJ
  obtain ⟨hf, -, -, hW, -⟩ := ProofFile.Honest.K12.Light.stages_at_head h.toAtMg
  obtain rfl : F = fourOf Np := Option.some.inj (hF.symm.trans hf)
  obtain rfl := membersW_head h O hms
  obtain ⟨s0, s1⟩ := statedW_W
  rw [carryE_at_W hB (Or.inl rfl), carryE_at_W hB (Or.inr rfl)]
  refine ⟨p12At_place _ _, s0.symm, ?_⟩
  have ef : freshRun (bareJob (fourOf Np).W membersWF (freshW Zp) : TestJob W X) =
      (carriedName senderW 1 ⟨placeW, 1⟩,
        ⟨0, dueFresh (piWFull.nums.stages.headD default)⟩) := by
    have hq : (fourOf Np).W.place = placeW := p12At_place _ _
    show (carriedName ((freshW Zp).getD (⟨(fourOf Np).W.place, 0⟩, 0)).1
        ((freshW Zp).getD (⟨(fourOf Np).W.place, 0⟩, 0)).2 ⟨(fourOf Np).W.place, 1⟩,
      (⟨0, dueFresh ((fourOf Np).W.nums.stages.headD default)⟩ : Due)) = _
    rw [freshW_head h O, hq, hW]
    rfl
  rw [ef]
  exact s1.symm

end AtFullSide.K12

#print axioms AtFullSide.K12.omegaDueB
#print axioms AtFullSide.K12.omegaDueB_plan
#print axioms AtFullSide.K12.omegaDue_real
#print axioms AtFullSide.K12.rowIF
#print axioms AtFullSide.K12.rowWF
#print axioms AtFullSide.K12.rowOF
#print axioms AtFullSide.K12.membersWF
#print axioms AtFullSide.K12.statedW_W
#print axioms AtFullSide.K12.statedW_W_bite
#print axioms AtFullSide.K12.rawCarriesWW_kept
#print axioms AtFullSide.K12.folds_once
#print axioms AtFullSide.K12.others_off
#print axioms AtFullSide.K12.seg_off
#print axioms AtFullSide.K12.carryE_at_W
#print axioms AtFullSide.K12.omegaDue_head
#print axioms AtFullSide.K12.firstRide_head
#print axioms AtFullSide.K12.freshW_head
#print axioms AtFullSide.K12.membersW_head
#print axioms AtFullSide.K12.carried_stated_W
