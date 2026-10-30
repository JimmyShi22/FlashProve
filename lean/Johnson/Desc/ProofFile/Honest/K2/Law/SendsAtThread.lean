-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SendsAtThread.lean: the kind "the code switch" (K2): TWO FIELDS
OF THE RECORD `K2SeatedL` (Honest/K2/SeatedL.lean), sends AND books, IN THE RECORD's OWN TEXT, AT
THE FIRST THREAD's LETTERS AT THE LIBRARY's HEAD, AT EACH SWITCH OF THE PLAN: at a state of the
thread in front of the member, a yes of the member holds a yes of the shared sending's decision at
the plan's own sending, at the second round cut to the sending's answers, leaves the messages, and
does to the verifier's book what a sending does. No definition; nothing is evaluated here; lemmas:
calls.

THE ROAD. The kind's decision takes what it sends off the state. (1) The thread's clause on how the
state was made holds the verifier's own fold over the members in front (`fold_of_thr`). (2) At such
a fold's state the library has, on the soundness side, that whatever front the switch takes off the
state announces just the plan's messages (`fence1_link`, `fence1_head`, `fence1_finish`), and that
the state's codes are the public part's (`open_recAll`): `fence_at_fold`. (3) A yes of the member
holds a yes of the kind's own decision (the way down, `k2_block_at_head`). (4) Inside that yes
stands a yes of the sending over the verifier program's own functions (`yes_msgs`, `sendByL8_iff`,
`sendOpen_iff`), and that is a yes of the shared sending's decision at the cut round
(`decide_of_sendP`): `sends_of_yes`; for the book: `yes_seated`, `yes_size`: `books_of_yes`. (5) The
place's own steps in front and behind leave the messages and the book (`arm_before`, `arm_after`).

  `sends_of_yes`, `books_of_yes`   at a yes of the kind's own decision, under the fence
  `arm_before`, `arm_after`   the place's own steps, by `SwitchArm`
  `fold_of_thr`     the thread's stand holds the fold
  `fence_at_fold`   the fence and the codes behind the place's step in front
  `sends_books_at_head`   THE END: both fields

By, sealed, of other authors: the names told above (Johnson/IMR/MsgsBehind.lean, ListsEnds.lean,
RootsWhole.lean, SendsK2.lean, SendsArms.lean · Johnson/Top/H0/Tw/K2C/SendsOpen.lean, SeatedAt.lean,
StillKeeps.lean, BookKept.lean, SendsOn.lean · Johnson/Desc/K1/Law/SendP5.lean, GoodSendAtS.lean ·
Johnson/P1K2R/SitsDoor.lean · Johnson/Top/H0/Walk/FrameOpened.lean) · `gpOf_in_scope`. Ours:
`k2_block_at_head`, `SwitchArm` (Honest/K2/Law/BlockAtHead.lean) · `yes_msgs`, `headOpenQ_msgs`
(MsgsBehindYes.lean) · `codes_switch`, `port_switch` (PublicMoreAtHead.lean) · `place_nums`
(SentIsBlocks.lean) · `sendingPar_sent` (Counts.lean).

Limits. ONE DIRECTION: BEHIND A YES OF THE MEMBER. THAT THE MEMBER SAYS YES ANYWHERE IS NOT SAID.
The start d of the sending's decision stands under "there is" and in no equation with the state (the
proof lays the front's statement, the state's book and its count of roots). A RUN's COINS AND THE
PROVER's STATE STAND UNDER "FOR ALL", inside the thread's stand, of which the fold alone is read.
The full size and the format's second hash function alone. The head and the opening are premises; that they
can be met is not said. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.BlockAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.MsgsBehindYes
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicMoreAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.Counts
import Johnson.IMR.MsgsBehind
import Johnson.IMR.SendsK2
import Johnson.Desc.K1.Law.SendP5
import Johnson.Desc.K1.Law.GoodSendAtS
import Johnson.P1K2R.SitsDoor
import Johnson.Top.H0.Tw.K2C.SendsOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Wit Place Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 decideWith par9 FrontOf headOpenQ finishFrontQ
  finishBehindQ sendByL8_iff sendOpen_iff yes_seated yes_size headOpenQ_book finishBehindQ_book
  finishBehindQ_st)
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

/-! ## 1 At a yes of the kind's own decision, under the fence -/

section
variable {q : P2} {P : K1.Par} {s₁ t : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}

/-- **A yes of the kind's own decision holds a yes of the sending's, at the cut round.** hF: the
fence: whatever front the switch takes off the state announces just P's messages. -/
theorem sends_of_yes (hy : decideWith sendByL8 q s₁ [r₁, r₂] gs = .ok t)
    (hF : ∀ x, FrontOf q s₁ x → switchNotices x.T x.others = P.sent)
    (hc : s₁.st.codes = P.codes) (hft : q.firstTree = P.gp.firstTree)
    (hB : K1.planOkOwn P = true) (hl : P.codes.lengthsOk = true) :
    ∃ (d d' : DState Unit) (ids : Array Nat),
      K1.decideSend P none d [r₁, K1.cutTo P r₂] = .ok (ids, d') ∧ K1.SameMsgs d'.st t.st ∧
        t.st.oracles.size = d'.st.oracles.size := by
  obtain ⟨x, y, hx, hs, hm⟩ := yes_msgs hy
  obtain ⟨ids, took, d, ho, rfl⟩ := (sendByL8_iff _ _ _ _ _ _ _ _ _).1 hs
  obtain ⟨-, -, sd, an, hp⟩ := (sendOpen_iff _ _ _ _ _ _ _ _ _ _ _).1 ho
  rw [hF x hx] at hp
  have h' := K1.decide_of_sendP { P with gp := ⟨(par9 q).samples, P.gp.firstTree⟩ } false
    (⟨x.st, s₁.book, s₁.roots, [], ()⟩ : DState Unit) d r₁ r₂ ids sd an took hB hl (by
      show x.st.codes = P.codes
      rw [IM.frontOf_codes hx, hc]) (by
      rw [← hft]
      exact hp)
  exact ⟨_, d, ids, h'.1, hm, K1.size_of_same hm⟩

/-- **And does to the book what a sending does.** -/
theorem books_of_yes (hy : decideWith sendByL8 q s₁ [r₁, r₂] gs = .ok t)
    (hF : ∀ x, FrontOf q s₁ x → switchNotices x.T x.others = P.sent)
    (hc : s₁.st.codes = P.codes) :
    K1.Booked P s₁.book s₁.st.oracles.size t.book t.st.oracles.size := by
  obtain ⟨x, lay, hx, hl', -, St⟩ := yes_seated hy
  rw [hF x hx, IM.frontOf_codes hx, hc] at hl'
  rw [hF x hx] at St
  obtain ⟨x', hx', z1, -, z3, -⟩ := yes_size hy
  rw [hF x' hx'] at z3
  have hlay : K1.layOf P = lay := by
    unfold K1.layOf
    rw [hl']
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hlay]
    apply Array.toList_inj.1
    rw [IM.places_of_seatedBut St, Array.toList_append, Array.toList_map, Array.toList_range]
    rfl
  · rw [hlay]
    exact St.size
  · rw [z3, z1]

end

/-! ## 2 The place's own steps -/

section
variable {Zp : ProofFile.Pub} {G : ProofFile.Ground} {p : SwitchPlace} {st : First.K2.At}
  {before : S → Except String S} {after : S → S → Except String S} {s s₁ u t : S}

/-- The step in front leaves the codes, the number of messages and the book. -/
theorem arm_before (hA : SwitchArm Zp G p st before after) (hb : before s = .ok s₁) :
    IM.Calm s s₁ := by
  rcases hA with ⟨-, -, -, -, -, rfl, -⟩ | ⟨-, -, -, rfl, -⟩ | ⟨-, -, -, rfl, -⟩
  · obtain rfl : s = s₁ := Except.ok.inj hb
    exact ⟨rfl, rfl, rfl⟩
  · obtain rfl : s = s₁ := Except.ok.inj hb
    exact ⟨rfl, rfl, rfl⟩
  · exact IM.finishFrontQ_calm hb

/-- The step behind leaves every message and the book. -/
theorem arm_after (hA : SwitchArm Zp G p st before after) (ha : after s₁ u = .ok t) :
    K1.SameMsgs u.st t.st ∧ t.book = u.book := by
  rcases hA with ⟨-, -, -, -, -, -, fs, f, hfs, hff, -, rfl⟩ | ⟨-, -, -, -, HP, -, rfl⟩ |
    ⟨-, -, -, -, rfl⟩
  · have k := Johnson.Desc.First.Walk.Tied.opened_keeps hfs hff (P1K2.leaveOpened_is ha)
    exact ⟨by rw [k.1]; exact msgs_refl _, k.2.1⟩
  · obtain ⟨m, h1, h2⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 ha
    obtain rfl : t = m := P1K2.guards_same h2
    exact ⟨headOpenQ_msgs h1, (headOpenQ_book h1).1⟩
  · obtain ⟨m, h1, h2⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 ha
    obtain rfl : t = m := P1K2.guards_same h2
    exact ⟨by rw [finishBehindQ_st h1]; exact msgs_refl _, (finishBehindQ_book h1).1⟩

end

/-! ## 3 Under the head -/

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

/-- **The thread's stand in front of a member holds the verifier's own fold over the members in
front**, from the description's own first state at the input's public part. -/
theorem fold_of_thr
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) {b : Nat} {k : Coins Bk}
    {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} (hT : Thr L.thread b k s m E) :
    ∃ (R : List Fmt.RoundView) (C : List OpenedColumn),
      foldBlocks 0 (cF.blocksInOrder.take b) (ProofFile.startS Zp m.st.input.x.pub) R C = .ok (s, [], []) := by
  subst hL
  obtain ⟨-, -, -, -, s₀, cols, hbeg, -, hf⟩ := hT.2.2.2.2.1
  have e0 : s₀ = ProofFile.startS Zp m.st.input.x.pub := hbeg
  rw [e0] at hf
  exact ⟨_, _, hf⟩

/-- **The fence and the codes, behind the place's step in front, at a fold's state.** -/
theorem fence_at_fold (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Pp : P1K2.Prep} {n : P1K2.Nums} (hP : P1K2.prepOf Zp Bs.G₀ = some Pp)
    (hn : P1K2.numsAt Pp p.place.link = some n) {st : First.K2.At}
    {before : TS → Except String TS}
    {after : TS → TS → Except String TS} (hA : SwitchArm Zp Bs.G₀ p st before after)
    {z : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List OpenedColumn} {s s₁ : TS}
    (hf : foldBlocks 0 (cF.blocksInOrder.take (P5J.At.ps.findIdx (· == p.place))) (ProofFile.startS Zp z) R C =
      .ok (s, [], [])) (hb : before s = .ok s₁) (nm : String) :
    (∀ x, FrontOf (k2P Zp p.place nm st n) s₁ x → switchNotices x.T x.others = n.sent) ∧
      s₁.st.codes = Zp.first.codes := by
  rcases hA with ⟨rfl, ep, h1, h24, ei, rfl, -⟩ | ⟨rfl, ep, ei, rfl, -⟩ | ⟨rfl, ep, ei, rfl, -⟩
  · obtain rfl : s = s₁ := Except.ok.inj hb
    rw [ei] at hf
    rw [ep] at hn
    exact ⟨Meaning.Carry.fence1_link h.scope h.reads O (by omega) hf hP hn _ nm .link
        (by intro e; cases e),
      (Meaning.K2.open_recAll h.scope h.reads O (by omega)
        (by rw [Meaning.Carry.front_len h.scope h.reads O]; omega) hf).codes⟩
  · obtain rfl : s = s₁ := Except.ok.inj hb
    rw [ei] at hf
    rw [ep] at hn
    exact ⟨Meaning.Carry.fence1_head h.scope h.reads O hf hP hn _ nm .head (by intro e; cases e),
      (Meaning.K2.open_recAll h.scope h.reads O (by decide)
        (by rw [Meaning.Carry.front_len h.scope h.reads O]; decide) hf).codes⟩
  · rw [ei] at hf
    rw [ep] at hn
    exact ⟨Meaning.Carry.fence1_finish h.scope h.reads O hf hP hn _ nm hb,
      (IM.finishFrontQ_calm hb).1.trans (Meaning.K2.open_recAll h.scope h.reads O (by decide)
        (by rw [Meaning.Carry.front_len h.scope h.reads O]) hf).codes⟩

/-- **sends AND books, IN THE RECORD's OWN TEXT, AT lettersHead, AT A SWITCH OF THE PLAN.** member:
the record's field. -/
theorem sends_books_at_head
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀)
    (member : L.bs[P5J.At.ps.findIdx (· == p.place)]? = some blk) :
    (∀ k s m E s' r₁ r₂ gs, Thr L.thread (P5J.At.ps.findIdx (· == p.place)) k s m E → blk.decide s
        [r₁, r₂] gs = .ok s' → ∃ (Lt : Type) (d d' : DState Lt) (owed : Option Nat) (ids : Array
        Nat), K1.decideSend (switchPar p) owed d [r₁, K1.cutTo (switchPar p) r₂] = .ok (ids, d') ∧
        K1.SameMsgs d'.st s'.st ∧ s'.st.oracles.size = d'.st.oracles.size) ∧
      ∀ k s m E s' r₁ r₂ gs, Thr L.thread (P5J.At.ps.findIdx (· == p.place)) k s m E → blk.decide s
        [r₁, r₂] gs = .ok s' → K1.Booked (switchPar p) s.book s.st.oracles.size s'.book
        s'.st.oracles.size := by
  obtain ⟨Pp, n, nm, st, before, after, hP, hn, hA, -, -, hdown⟩ :=
    k2_block_at_head h O hp (by rw [hL] at member; exact member)
  have hsent : n.sent = (switchPar p).sent := by
    rw [place_nums hP hp hn]
    exact (sendingPar_sent _ _).symm
  have hcod : Zp.first.codes = (switchPar p).codes := (codes_switch h O hp).symm
  have hport := port_switch h O hp
  unfold K1.condPort at hport
  rw [Bool.and_eq_true, Bool.and_eq_true] at hport
  have hft : (k2P Zp p.place nm st n).firstTree = (switchPar p).gp.firstTree :=
    congrArg (·.firstTree) (K13.Law.gpOf_in_scope h.scope h.laid.pub (K1.pin1_atAll h))
  have key : ∀ (k : Coins Bk) (s : TS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X) (E : Env) (s' : TS)
      (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
      Thr L.thread (P5J.At.ps.findIdx (· == p.place)) k s m E →
      blk.decide s [r₁, r₂] gs = .ok s' → ∃ s₁ u gs', IM.Calm s s₁ ∧
        decideWith sendByL8 (k2P Zp p.place nm st n) s₁ [r₁, r₂] gs' = .ok u ∧
        (∀ x, FrontOf (k2P Zp p.place nm st n) s₁ x →
          switchNotices x.T x.others = (switchPar p).sent) ∧
        s₁.st.codes = (switchPar p).codes ∧ K1.SameMsgs u.st s'.st ∧ s'.book = u.book := by
    intro k s m E s' r₁ r₂ gs hT hy
    obtain ⟨s₁, u, hb, hd, ha⟩ := hdown s [r₁, r₂] gs s' hy
    obtain ⟨R, C, hf⟩ := fold_of_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hL hT
    obtain ⟨F1, F2⟩ := fence_at_fold h O hP hn hA hf hb nm
    obtain ⟨A1, A2⟩ := arm_after hA ha
    exact ⟨s₁, u, _, arm_before hA hb, hd, by rw [← hsent]; exact F1, F2.trans hcod, A1, A2⟩
  constructor
  · intro k s m E s' r₁ r₂ gs hT hy
    obtain ⟨s₁, u, gs', -, hd, F1, F2, A1, -⟩ := key k s m E s' r₁ r₂ gs hT hy
    obtain ⟨d, d', ids, e1, e2, e3⟩ := sends_of_yes hd F1 F2 hft hport.1.1 hport.1.2
    exact ⟨Unit, d, d', none, ids, e1, e2.trans A1, by rw [K1.size_of_same A1, e3]⟩
  · intro k s m E s' r₁ r₂ gs hT hy
    obtain ⟨s₁, u, gs', C1, hd, F1, F2, A1, A2⟩ := key k s m E s' r₁ r₂ gs hT hy
    have B := books_of_yes hd F1 F2
    rw [C1.2.2, C1.2.1] at B
    rw [A2, K1.size_of_same A1]
    exact B

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.sends_of_yes
#print axioms ProofFile.Honest.K2.Law.books_of_yes
#print axioms ProofFile.Honest.K2.Law.arm_before
#print axioms ProofFile.Honest.K2.Law.arm_after
#print axioms ProofFile.Honest.K2.Law.fold_of_thr
#print axioms ProofFile.Honest.K2.Law.fence_at_fold
#print axioms ProofFile.Honest.K2.Law.sends_books_at_head
