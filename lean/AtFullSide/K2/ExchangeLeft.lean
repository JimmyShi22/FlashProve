-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/ExchangeLeft.lean: the kind "the code switch" (K2): `k2_exchange_step`
(ExchangeStep.lean of this folder) WITH WHAT THE HOUSE HAS LAID IN: y₀ and hD1 are gone from its
premises, and of the record `OpenerAsks` there stand the later senders alone. A
definition: a premise's form. Statements with their proofs: calls.

WHICH SLOT IT IS FOR. The same: the hypothesis hXk of the frame's gather at the kind K2.

  `frontSwitchW`, `frontSwitchW_can_fail`   BY LEAN's KERNEL: a switch in front of each but the
                    first
  `JoinAsks`        under `StepAsks`' binders: that the input is typed · `FirstAsks` at p.link = 1
                    · beyond it, at the switch p₀ in front: HL, the two later senders' asks ·
                    `SymbolsAre`
  `stepAsks_of_join`   `JoinAsks` ⊢ `StepAsks`, at the joined Script
  `k2_exchange_left`   THE TOP

By: `opener_at_join` (OpenerAtJoin.lean) · `handed_at_book` (HandedAtTheBook.lean) ·
`book_tests_at_head` (BookTestsAtHead.lean) · `rows_isSome` (Honest/K2/Law/LotsAnswer.lean),
`closing_at_head`, `serves_at_head`, `roomy_at_head`, `fits_at_head`, `publicOk_of_reads` ·
`anyStrings` (Honest/K2/Law/AnyStrings.lean) · `heard_at_switches` (HeardAtSwitches.lean), of other
authors · `k2_exchange_step` · `drawsFit_length`.

WHAT IS LEFT, BY THE TOP's OWN BINDERS. h, O, hA · hOk, hst · hex, ho · hR4 · hI · hJ · hO · left:
`JoinAsks`.

Limits. AN IMPLICATION: `JoinAsks` IS SHOWN OF NO PROVER AND NO SCRIPT. It binds a run's coins k and
c; cs stands under "there is"; CLOSED FACTS BY LEAN's KERNEL, REPLAYED BY NO INDEPENDENT CHECKER;
entries that hold coins: equations between two texts' values. The full size; the format's second hash function. One run's coins: never quoted for a law.
NOT IN FRONT OF A LAW OVER COINS (the rule: Johnson/Bind/ForProver/FiveFieldsAt.lean). Nothing on any property.
-/
import AtFullSide.K2.OpenerAtJoin
import Johnson.Desc.ProofFile.Honest.K2.Law.AnyStrings
import AtFullSide.K2.HandedAtTheBook
import AtFullSide.K2.BookTestsAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.LotsAnswerAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block KindName Strs)
open VerifiableInference.Desc.K2.Honest (carryExact Left)
open VerifiableInference.Desc.Sound (MsgT allOf EAll)
open OnBytes (Positions)
open OnBytes.HonestTrace (Sz)
open OnBytes.SendSim.Seat (wJobs)
open OnBytes.Maker (WholeD)
open Johnson.G (proofSendsFull)
open P5J (AtMgA CellsM TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.K1 (seatAtMember)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (sizesAt SymbolsAre)
open VerifiableInference.Desc.First.K2 (AtYes)
open _root_.Desc.K14.Law (shownGroups)

set_option maxRecDepth 1000000 in
/-- BY LEAN's KERNEL: past the first, each written switch has one with the link in front. -/
theorem frontSwitchW : (placesW.all fun p => decide (p.link ≤ 1) ||
    placesW.any fun p₀ => decide (p₀.link + 1 = p.link)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: some written switch has none. -/
theorem frontSwitchW_can_fail : (placesW.all fun p =>
    placesW.any fun p₀ => decide (p₀.link + 1 = p.link)) = false := by decide +kernel

/-- **WHAT STANDS IN `StepAsks`' STEAD, AT ONE PLACE.** A definition: the form of a premise. Nothing
here proves that it can be met. NOT IN FRONT OF A LAW OVER COINS. -/
def JoinAsks {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type} (Wj Xj : Type)
    (L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (Zp : ProofFile.Pub) (Bs :
                  ProofFile.PureBase)
    (cF : Chain TS ProofFile.Cl)
    (D : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (p : SwitchPlace) : Prop :=
  ∀ (blk : Block TS ProofFile.Cl) (Pp : P1K2.Prep) (n : P1K2.Nums) (nm : String)
    (st : VerifiableInference.Desc.First.K2.At) (before : TS → Except String TS)
    (after : TS → TS → Except String TS), L.bs[switchNo p]? = some blk →
    P1K2.prepOf Zp Bs.G₀ = some Pp → P1K2.numsAt Pp p.place.link = some n →
    SwitchArm Zp Bs.G₀ p st before after →
    ∀ k s m E ds y cols s', ThrS L.thread Said (switchNo p) k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      ∀ c V Wl r₁ r₂ s₁ t x z S3 Y rows Gr cd, handed 0 p k = some c →
        switchRowsLaid D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p c m.st.input m.st.heard
          =
          .ok V →
        lotClosingAt lay (segmentsOf Zp Bs.G₀) p (D m.st.input.x) (readers m.st.input)
          (m.st.heard.take (m.st.heard.length - 0)) (Stretch.carried p.carries c.2.2) = .ok Wl →
        (roundsOf y.1).map noDigest = [r₁, r₂] → before s = .ok s₁ →
        AtYes (IM.k2P Zp p.place nm st n) s₁ t r₁ r₂
          (shownGroups L.thread.ft blk (roundsOf y.1) cols) x z S3 Y rows Gr cd →
        after s₁ t = .ok s' →
        (∃ z : LPFD.Full.XF × OnBytes.Flat.RecFull, m.st.input.x.pub = (LPFD.Full.instanceAsPlainRecord z).pub) ∧
        (p.link = 1 → ∃ N, FirstAsks (W := Wj) (X := Xj) Zp Bs cF 0 p k c
          (lotOwn segsW p (D m.st.input.x) (readers m.st.input) m.st.heard) L.Q L.valid N
          m.st.input m.st.heard ds) ∧
        (∀ p₀ ∈ switchPlaces Zp Bs.G₀, p₀.link + 1 = p.link → 1 ≤ p₀.link →
          ∀ (y' : Option (Left × List OnBytes.OracleShape) × Nat) (Sg : SegmentPub),
            closingFrom freshTable (lotOwn (segmentsOf Zp Bs.G₀) p (D m.st.input.x)
              (readers m.st.input) m.st.heard) m.st.heard (Stretch.carried p.carries c.2.2)
              ((segmentsOf Zp Bs.G₀).take (p.link - 1)) 0 0 none = .ok y' →
            (segmentsOf Zp Bs.G₀)[p.link - 1]? = some Sg →
            ∀ q, q < 2 → ∃ (wit' : Local W₀ Rc ProofFile.Inst Tr → Wj) (J : K1.SendJob Wj Xj) (own' : Xj)
              (cs : Cs (K1.dueR J.P J.ride)) (e : Ahead)
              (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (front : Nat),
              SharedAsks Zp cF.blocksInOrder (VerifiableInference.Desc.K1.parL Zp Bs.G₀ (p.link - 1) (q ==
                         1))
                (K1.rideOf none) (VerifiableInference.Desc.K1.noL (p.link - 1) (q == 1)) 0
                (y'.2 + ((Sg.sent.headD #[]).size - 1) + 1 + q) 0 p k
                (lotOwn (segmentsOf Zp Bs.G₀) p (D m.st.input.x) (readers m.st.input) m.st.heard
                  (0 + (p.link - 1)) ((Sg.sent.headD #[]).size - 1 -
                    (if (y'.1.map (·.1)).isSome then 1 + Sg.sizes.kept.length else 0) + q))
                L.Q L.valid (0 + roundsTo cF.blocksInOrder (switchNo p₀)) m.st.input
                (m.st.heard ++ ds) wit' J own' cs e dataK front) ∧
        SymbolsAre (sizesAt S3 x.f.rows x.T) x.f.rows Wl (Positions.ofDraws (IM.k2P Zp p.place nm
          st n).logN r₂.drawn.poss) Y

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {W₀ Rc Tr X₀ X Y X₂ : Type} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- h, O, hA, hR4, hI, hO, hJ, hp AND hV ARE PREMISES; the rest are letters. **`StepAsks` AT THE
JOINED SCRIPT.** NOT IN FRONT OF A LAW OVER COINS. -/
theorem stepAsks_of_join {Wj Xj : Type} (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (no : VerifiableInference.Desc.Place → Nat) (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tokQ : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst) (own₀ : Y)
    (rest : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr)) (ch : Nat)
    (Jt : K12.TestJob (Local W₀ Rc ProofFile.Inst Tr) X₂) (hJ : Jt.p.nums.stages.length = 6)
    (own₂ : X₂) (n₀ : Nat)
    (ok : Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → (Nat → K12.Stretch) → Bool)
    (codes : OnBytes.Codes) (sh sh₁ : Nat → OnBytes.OracleShape)
    (rest₂ : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr))
    (Oth : Others A.B (Local W₀ Rc ProofFile.Inst Tr))
    (hO : Oth = (switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀ (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp
               Bs.G₀)
      (fun v => (wit v).R) rest).add
        (K12.k12Share ch Jt own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂))
    (test : Nat → TS → Option String) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
        (hR4 : ∀ v, (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).valid v →
      ReadsLight Zp Bs.G₀ v.x)
    (hI : ∀ v, (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).valid v → (wit v).x = v.x)
    {p : SwitchPlace} (hp : p ∈ placesW)
    (hV : JoinAsks Wj Xj (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w) Said Zp Bs cF (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀)
      (fun v => (wit v).R) Bs.G₀.first.layout p) :
    StepAsks Wj Xj (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w) Said Zp Bs cF (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀)
      (fun v => (wit v).R) Bs.G₀.first.layout p := by
  have hpS : p ∈ switchPlaces Zp Bs.G₀ := by
    rw [places_at_head h.toAtMg O]
    exact hp
  have hB := pure_book_written h hA
  intro blk Pp n nm st before after hb hP hn hArm k s m E ds y cols s' hT hd hS c V Wl r₁ r₂ s₁ t x
    z S3 Y rows Gr cd hc hL hW hr hbf Ay ha
  obtain ⟨hty, hF, hLt, hsym⟩ := hV blk Pp n nm st before after hb hP hn hArm k s m E ds y cols s'
    hT hd hS c V Wl r₁ r₂ s₁ t x z S3 Y rows Gr cd hc hL hW hr hbf Ay ha
  refine ⟨hty, hF, fun h1 => ?_, hsym⟩
  have hW0 := List.all_eq_true.1 frontSwitchW p hp
  rw [Bool.or_eq_true] at hW0
  obtain ⟨p₀, hq₀, hl₀⟩ : ∃ p₀ ∈ placesW, p₀.link + 1 = p.link := by
    rcases hW0 with q | q
    · exact absurd (of_decide_eq_true q) (by omega)
    · obtain ⟨p₀, a, b⟩ := List.any_eq_true.1 q
      exact ⟨p₀, a, of_decide_eq_true b⟩
  have hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀ := by
    rw [places_at_head h.toAtMg O]
    exact hq₀
  have e₀ : p₀.link = p.link - 1 := by omega
  obtain ⟨c₀, h₀⟩ := Option.isSome_iff_exists.1 (handed_at_book h O hB hp₀ k)
  have hval := hT.1.2.2.2.2.2.2
  have hr := rows_isSome (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) (fun v => (wit v).R)
    Bs.G₀.first.layout (segmentsOf Zp Bs.G₀) p₀ (closing_at_head h.toAtMg O p₀ hp₀) c₀ m.st.input
    (m.st.heard.take (0 + roundsTo cF.blocksInOrder (switchNo p₀)))
  rw [serves_at_head h.toAtMg O p₀ hp₀, roomy_at_head h.toAtMg O p₀ hp₀,
    publicOk_of_reads h O (hR4 m.st.input hval) p₀ hp₀, fits_at_head h.toAtMg O p₀ hp₀] at hr
  obtain ⟨V₀, hV₀⟩ : ∃ V₀, switchRowsLaid (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) (fun
    v => (wit v).R)
      (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p₀ c₀ m.st.input
      (m.st.heard.take (0 + roundsTo cF.blocksInOrder (switchNo p₀))) = .ok V₀ := by
    cases e : switchRowsLaid (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) (fun v => (wit
      v).R)
      (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p₀ c₀ m.st.input
      (m.st.heard.take (0 + roundsTo cF.blocksInOrder (switchNo p₀))) with
    | ok V' => exact ⟨V', rfl⟩
    | error _ =>
      rw [e] at hr
      cases hr
  obtain ⟨hf, hs⟩ := book_tests_at_head h hB hq₀ hp hl₀
  have hf' : carriedFits A.B (switchPlaces Zp Bs.G₀) p = true := by
    rw [places_at_head h.toAtMg O]
    exact hf
  have hlen : roundsTo cF.blocksInOrder (switchNo p) ≤ m.st.heard.length := by
    have e := drawsFit_length _ _ hT.1.2.1
    rw [e, List.length_append]
    exact Nat.le_add_left _ _
  exact ⟨p₀, c₀, V₀, _, _, hp₀, e₀, opener_at_join h O hA no Dd cellsQ tokQ wit own₀ rest ch Jt hJ
    own₂ n₀ ok codes sh sh₁ rest₂ Oth hO test item n₁ n₂ b₀ Vd Rd Kp w hR4 hI hp₀ hpS e₀ (by omega)
    k m.st.input m.st.heard ds hlen c₀ h₀ c V₀ hs hf' hV₀ (hLt p₀ hp₀ hl₀ (by omega))⟩

/-- h, O, hA AND EVERY BINDER NAMED IN THE HEAD ARE PREMISES; the rest are letters. **K2's WHOLE
DEBT UNDER "THE EXCHANGE", AT `JoinAsks`.** NOT IN FRONT OF A LAW OVER COINS. -/
theorem k2_exchange_left {Wj Xj : Type} (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (no : VerifiableInference.Desc.Place → Nat) (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (cellsQ : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
    (tokQ : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok)
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn ProofFile.Inst) (own₀ : Y)
    (rest : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr)) (ch : Nat)
    (Jt : K12.TestJob (Local W₀ Rc ProofFile.Inst Tr) X₂) (hJ : Jt.p.nums.stages.length = 6)
    (own₂ : X₂) (n₀ : Nat)
    (ok : Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → (Nat → K12.Stretch) → Bool)
    (codes : OnBytes.Codes) (sh sh₁ : Nat → OnBytes.OracleShape)
    (rest₂ : Nat → TreeLot A.B (Local W₀ Rc ProofFile.Inst Tr))
    (Oth : Others A.B (Local W₀ Rc ProofFile.Inst Tr))
    (hO : Oth = (switchShareAt A.B cF.blocksInOrder 0 Zp Bs.G₀ (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp
               Bs.G₀)
      (fun v => (wit v).R) rest).add
        (K12.k12Share ch Jt own₂ n₀ 77 (P5J.At.arr Zp) ok codes sh sh₁ 354 rest₂))
    (test : Nat → TS → Option String) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    {Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m)
    (hst : ∀ v i x u, (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).thread.stored v i x = some u →
      ∀ a ∈ u, a < fieldPrimeWord)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = (switchLot (X := X) (withSwitchData Sz.ref (K1.lotData
      Sz.ref) Zp Bs.G₀)
      (fun v => (wit v).R)).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K2) ∨
      M.halves A.Z A.G = (switchLot (X := X) (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀)
        (fun v => (wit v).R)).halves A.Z A.G)
    (hR4 : ∀ v, (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).valid v →
      ReadsLight Zp Bs.G₀ v.x)
    (hI : ∀ v, (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).valid v → (wit v).x = v.x)
    (left : ∀ p ∈ placesW, JoinAsks Wj Xj (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ
      (P5J.At.arr
      Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w) Said Zp Bs cF (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀)
      (fun v => (wit v).R) Bs.G₀.first.layout p) :
    ∀ b p₀, P5J.At.ps[b]? = some p₀ → p₀.kind = KindName.K2 →
      ∀ j : VerifiableInference.Desc.First.Item, j ∈ ((lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ
        tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).thread.row b).owes →
      (j ∈ (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).thread.opened b →
        (∀ m t, j ≠ VerifiableInference.Desc.First.Item.pin m t) ∧ j ≠
          VerifiableInference.Desc.First.Item.pinI ∧ j ≠ VerifiableInference.Desc.First.Item.pinW ∧
        ∀ m q, q ∈ P5J.parts4 → j ≠ VerifiableInference.Desc.First.Item.constr m q) →
      ExchangeAtS (lettersHead h A.H (joinQ cF.blocksInOrder 0 cellsQ tokQ (P5J.At.arr Zp) wit own₀
        (byNo cF.blocksInOrder (K1.lotJobs (X := Y) no (K1.lotData Sz.ref) Zp Bs.G₀ ++
                 wJobs (X := Y) no Dd Zp Bs.G₀)) Oth) test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd
          Rd Kp w).thread Said b j :=
  k2_exchange_step h O hA no Dd cellsQ tokQ wit own₀ rest ch Jt hJ own₂ n₀ ok codes sh sh₁ rest₂ Oth
    hO test item n₁ n₂ b₀ Vd Rd Kp w hOk hst (anyStrings _ _) hex ho hR4
    (fun p₀ hp₀ p hp _ v _ s m a hs ha =>
      heard_at_switches h O Sz.ref p₀ hp₀ p hp v.x s m a hs ha) hI
    fun p hp => stepAsks_of_join h O hA no Dd cellsQ tokQ wit own₀ rest ch Jt hJ own₂ n₀ ok codes sh
      sh₁ rest₂ Oth hO test item n₁ n₂ b₀ Vd Rd Kp w hR4 hI hp (left p hp)

end AtFullSide.K2

#print axioms AtFullSide.K2.frontSwitchW
#print axioms AtFullSide.K2.frontSwitchW_can_fail
#print axioms AtFullSide.K2.JoinAsks
#print axioms AtFullSide.K2.stepAsks_of_join
#print axioms AtFullSide.K2.k2_exchange_left
