-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/BookBehindStep.lean: the kind "the code switch" (K2): THE TWO
PUBLIC PREMISES ON THE VERIFIER's BOOK BEHIND THE MEMBER's STEP that three of the kind's four laws
ask beside the record (hFits, hNum; the second and third limb of `SwitchPaid`,
Honest/K2/Law/ExchangeByKind.lean), IN THEIR OWN TEXT, AT THE FIRST THREAD's LETTERS AT THE
LIBRARY's HEAD, AT EACH SWITCH OF THE PLAN: behind the step each message's place in the book names a
tree and a part that hold it, and a tree's number is its place. No definition; nothing is evaluated;
calls.

THE ROAD. In front of the member the state is reached (`reach_of_made`), so both hold there, by the
library's own laws on reached states (`bookFits_reached`, `bookInOrder_reached`). The place's step
in front leaves book and roots; a yes of the kind's own decision hands both on (`yes_fits`,
`yes_numbered`); the step behind leaves the book.

  `arm_before_book`   the step in front leaves the book and the count of roots
  `number_le`       a switch's number is at most 353
  `book_behind_step`   THE END: both premises

By, sealed, of other authors: the names told (Honest/Thread/MadeLaw.lean · Johnson/IMR/AtReach.lean,
RootsWhole.lean · Johnson/Top/H0/Tw/K2C/FitsRide.lean, SentTrees.lean, BookKept.lean) ·
`step_ok_iff` (Johnson/Desc/Sound/RunIsDecide.lean) · `gpOf_in_scope`. Ours: `k2_block_at_head`,
`SwitchArm` (Honest/K2/Law/BlockAtHead.lean) · `arm_after` (SendsAtThread.lean).

Limits. BEHIND A STEP IN WHICH THE MEMBER SAID YES: that there is one is not said. ON THE BOOK
ALONE. A run's coins and the prover's state stand under "for all", inside the thread's stand, of
which the clause on how the state was made alone is read, and inside the step, of which the member's
own step alone is read. The full size and the format's second hash function alone. The head and the opening
are premises. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SendsAtThread
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw
import Johnson.IMR.AtReach
import Johnson.Top.H0.Tw.K2C.FitsRide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Wit Place Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 decideWith par9 FrontOf headOpenQ finishFrontQ
  finishBehindQ sendByL8_iff sendOpen_iff yes_seated yes_size headOpenQ_book finishBehindQ_book
  finishBehindQ_st finishFrontQ_book yes_fits yes_numbered)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.K2.Honest.Returns (switchPlaceAt headPlaceAt)
open VerifiableInference.Desc.K12.Coin (placesOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread
open P1K2 (guards leaveOpened)
open IM (k2P k2PlaceF)
open _root_.Tw.K2 (sendByL8 switchNotices)
open _root_.Desc.Plain (DState)
open _root_.Desc.K14.Law (secondAt seatZ)

section
variable {Zp : ProofFile.Pub} {G : ProofFile.Ground} {p : SwitchPlace} {st : First.K2.At}
  {before : S → Except String S} {after : S → S → Except String S} {s s₁ : S}

/-- The step in front leaves the book and the count of roots. -/
theorem arm_before_book (hA : SwitchArm Zp G p st before after) (hb : before s = .ok s₁) :
    s₁.book = s.book ∧ s₁.roots = s.roots := by
  rcases hA with ⟨-, -, -, -, -, rfl, -⟩ | ⟨-, -, -, rfl, -⟩ | ⟨-, -, -, rfl, -⟩
  · obtain rfl : s = s₁ := Except.ok.inj hb
    exact ⟨rfl, rfl⟩
  · obtain rfl : s = s₁ := Except.ok.inj hb
    exact ⟨rfl, rfl⟩
  · exact finishFrontQ_book hb

/-- A switch's number is at most 353. -/
theorem number_le (hA : SwitchArm Zp G p st before after) :
    P5J.At.ps.findIdx (· == p.place) ≤ 353 := by
  rcases hA with ⟨-, -, -, h24, ei, -⟩ | ⟨-, -, ei, -⟩ | ⟨-, -, ei, -⟩
  · omega
  · omega
  · omega

end

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  {blk : Block TS ProofFile.Cl} {p : SwitchPlace} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **hFits AND hNum, IN THEIR OWN TEXT, AT lettersHead, AT A SWITCH OF THE PLAN.** member: the
record's field. -/
theorem book_behind_step
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀)
    (member : L.bs[P5J.At.ps.findIdx (· == p.place)]? = some blk)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    (∀ k s m E ds y cols s', ThrS L.thread Said (P5J.At.ps.findIdx (· == p.place)) k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      VerifiableInference.Desc.Book.BookFits s'.book) ∧
    (∀ k s m E ds y cols s', ThrS L.thread Said (P5J.At.ps.findIdx (· == p.place)) k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      ∀ (z : ℕ) (T : OnBytes.Tree), s'.book.trees[z]? = some T → T.number = z) := by
  obtain ⟨Pp, n, nm, st, before, after, hP, hn, hA, -, -, hdown⟩ :=
    k2_block_at_head h O hp (by rw [hL] at member; exact member)
  have hft : (k2P Zp p.place nm st n).firstTree = 0 :=
    congrArg (·.firstTree) (K13.Law.gpOf_in_scope h.scope h.laid.pub (K1.pin1_atAll h))
  have hk : P5J.At.ps.findIdx (· == p.place) ≤ (Meaning.K2.frontOf cF).length := by
    rw [Meaning.Carry.front_len h.scope h.reads O]
    exact number_le hA
  have key : ∀ (k : Coins Bk) (s : TS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env)
      (ds : List Fmt.Drawn) (y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X) (cols : List OpenedColumn)
      (s' : TS), ThrS L.thread Said (P5J.At.ps.findIdx (· == p.place)) k s m E →
      L.thread.Stepped blk k s m E ds y cols s' →
      VerifiableInference.Desc.Book.BookFits s'.book ∧
        ∀ (z : ℕ) (T : OnBytes.Tree), s'.book.trees[z]? = some T → T.number = z := by
    intro k s m E ds y cols s' hT hS
    have hy := ((VerifiableInference.Desc.Sound.step_ok_iff _ _ _ _ _ _ _).1 hS.2).2.2.2
    obtain ⟨s₁, u, hb, hd, ha⟩ := hdown s _ _ s' hy
    have hreach : Johnson.Desc.First.Walk.Tied.Reach 0 cF.blocksInOrder (ProofFile.startS Zp)
        (P5J.At.ps.findIdx (· == p.place)) (m.st.input.x.pub, s) := by
      subst hL
      exact reach_of_made _ (ProofFile.startS Zp) m.st.input.x.pub
        (Nat.le_of_lt (List.getElem?_eq_some_iff.1 member).1) (fun _ e => e) hT.1.2.2.2.2.1
    obtain ⟨e1, e2⟩ := arm_before_book hA hb
    have eb := (arm_after hA ha).2
    have F := Meaning.K2.bookFits_reached O hreach hk
    have N := Meaning.K2.bookInOrder_reached O hreach hk
    refine ⟨?_, ?_⟩
    · rw [eb]
      exact yes_fits hd (by rw [e1]; exact F)
    · have N' := yes_numbered hd (by
        rw [e1, e2, hft]
        exact N)
      intro z T hT'
      rw [eb] at hT'
      have := (N'.2 z T hT').1
      rw [hft] at this
      omega
  exact ⟨fun k s m E ds y cols s' hT _ hS => (key k s m E ds y cols s' hT hS).1,
    fun k s m E ds y cols s' hT _ hS => (key k s m E ds y cols s' hT hS).2⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.arm_before_book
#print axioms ProofFile.Honest.K2.Law.number_le
#print axioms ProofFile.Honest.K2.Law.book_behind_step
