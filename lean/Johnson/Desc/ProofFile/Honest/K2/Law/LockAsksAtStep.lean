-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/LockAsksAtStep.lean: the kind "the code switch" (K2):
`LockAsks` AT THE LETTERS OF A STEP: the four laws that end in it, laid in at the thread's stand at
a switch. What they ask and this file does not take off the stand is named in two records.
Structures of premises' forms; statements with their proofs: calls.

WHICH SLOT IT IS FOR. `ValuesAsks` (ValuesOfLock.lean of this folder) has `LockAsks` as a limb; here
that limb comes from what the two records name. The end is the premise hA of `claim_at_yes` and
`stored_at_yes`.

  `OpenerAsks`      at a switch whose closed group a switch p₀ opened: each binder of
                    `link_lockAsks` that this file does not take off the stand, as a field; HL
                    under the walk's own y' and Sg
  `FirstAsks`       at the switch into group 1: the like of `first_lockAsks`
  `lockAsks_of_step`   THE END: at a written switch, at the kind's own yes, where the first record
                    holds (p.link = 1) or the second

GIVEN BY THE STAND, NOT ASKED: the reached state and the front · f₀, hhd: the fold and what was
heard (the clause Made of the thread's stand) · hy', hS: the walk's step in front (`link_lastStep`,
`head_lastStep`, `fin_lastStep`, over `lotClosingAt_kept`) · hv: the thread's valid input.

By, of this folder: `link_lockAsks`, `first_lockAsks` (LockAsksAtLink.lean) · `head_lockAsks`,
`fin_lockAsks` (LockAsksAtArms.lean) · `rch_at_head`, `frontAt_stands` (ClaimAtYes.lean) ·
`segments_at_head` · `lotClosingAt_kept` (HonestAtClosing.lean).

Limits. AN IMPLICATION: THE TWO RECORDS ARE SHOWN OF NO SCRIPT, BOOK OR FILLING. Their fields bind a
run's coins k, c₀, c; in hLater c₀ and V stand under "there is", pinned by the fields h₀ and hV; in
HL, HF and HM stands cs, a cut of the coins, under "there is", pinned by each record's field cut.
They speak of the Script's words at them and of entries that hold coins: equations between two
texts' values: what is WRITTEN where. hOk, hst, hT, hty, y₀, A, hc, hW, hFirst AND hLater ARE
PREMISES. One run's coins: never quoted for a law. NOT IN FRONT OF A LAW OVER COINS.
The full size; the format's second hash function. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.StoredAtYes
import Johnson.Desc.ProofFile.Honest.K2.Law.LockAsksAtArms

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes
open VerifiableInference.Desc (Block Chain Strs foldBlocks fieldPrimeWord)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 AtYes frontAt)
open VerifiableInference.Desc.First.Close (seatK10)
open VerifiableInference.Desc.LinkJoin (loAt)
open VerifiableInference.Desc.K1 (parL noL firstPar gpOf)
open VerifiableInference.Desc.K2.Honest (Left carryExact)
open VerifiableInference.Desc.K2.Honest.Returns (link_door head_door fin_door)
open VerifiableInference.Desc.K13.Honest (roundsAhead)
open VerifiableInference.Desc.Sound (allOf EAll MsgT wordsFirst)
open Johnson.Prover.Send (shapeAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread (Script lettersHead OwnMsgs OwnPads)
open IM (k2P)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Cells Tok W X : Type}

/-- **WHAT `link_lockAsks`, `head_lockAsks` AND `fin_lockAsks` ASK THAT THIS FILE DOES NOT TAKE OFF
THE STAND**, at a switch p whose closed group m the switch p₀ opened. A structure of premises'
forms. Nothing here proves that it can be met. It names a run's coins. -/
structure OpenerAsks (Zp : ProofFile.Pub) (Bs : ProofFile.PureBase) (cF : Chain TS ProofFile.Cl) (m : Nat)
    (p₀ p : SwitchPlace) (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT)
    (Vd : Local W₀ Rc Xi Tr → Prop) (N ch fx₀ : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (lay : OnBytes.Params.ReqLayout) (k : Coins Bk)
    (w : Local W₀ Rc Xi Tr) (hdL ds : List Fmt.Drawn)
    (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries)
    (V : Nat → Johnson.Prover.Send.Rows) : Prop where
  hmS : ∀ n (i : Fin (loAt m).length), n < (switchSent p₀.sizes p₀.others).size - 1 →
      (VerifiableInference.Desc.First.Close.membersOf (loAt m))[n]? = some i →
      OwnMsgs Q Vd N (P5J.At.arr Zp (seatK10 (loAt m) (P5J.At.pseats Zp) m i).1
          (seatK10 (loAt m) (P5J.At.pseats Zp) m i).2) fx₀
        (switchMsgOff ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀ n)
  hpS : ∀ n (i : Fin (loAt m).length), n < (switchSent p₀.sizes p₀.others).size - 1 →
      (VerifiableInference.Desc.First.Close.membersOf (loAt m))[n]? = some i →
      OwnPads Q Vd (seatK10 (loAt m) (P5J.At.pseats Zp) m i).1
        (seatK10 (loAt m) (P5J.At.pseats Zp) m i).2 (fun k _ => switchPadTxt ch p₀ n k)
  hmF : OwnMsgs Q Vd N (P5J.At.arr Zp (VerifiableInference.Desc.First.Close.maskTree m)
        (VerifiableInference.Desc.First.Close.maskPart m)) fx₀
      (switchMsgTxt ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀
        ((switchSent p₀.sizes p₀.others).size - 1))
  hpF : OwnPads Q Vd (VerifiableInference.Desc.First.Close.maskTree m)
      (VerifiableInference.Desc.First.Close.maskPart m)
      (fun k _ => switchPadTxt ch p₀ ((switchSent p₀.sizes p₀.others).size - 1) k)
  hN : N ≤ (hdL ++ ds).length
  hfx₀ : fx₀ ≤ hdL.length
  h₀ : handed ch p₀ k = some c₀
  hs : carriedSame Bk p₀ p = true
  hf : carriedFits Bk (switchPlaces Zp Bs.G₀) p = true
  hgl : VerifiableInference.Desc.K13.Honest.roundsAhead cF.blocksInOrder
    (VerifiableInference.Desc.First.K2Caller.noAt (m - 1)) ≤ fx₀
  hD : ∀ s i ad, s < p₀.link → p.addrs s i = some ad → (D w.x).heardAt ad ≤ fx₀
  hV : switchRowsLaid D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀ c₀ w
      (hdL.take fx₀) = .ok V
  HL : ∀ (y' : Option (Left × List OnBytes.OracleShape) × Nat) (Sg : SegmentPub),
    closingFrom freshTable (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hdL) hdL
      (Stretch.carried p.carries c.2.2) ((segmentsOf Zp Bs.G₀).take m) 0 0 none = .ok y' →
    (segmentsOf Zp Bs.G₀)[m]? = some Sg →
    ∀ q, q < 2 → ∃ (wit : Local W₀ Rc Xi Tr → W) (J : K1.SendJob W X) (own₀ : X)
      (cs : Cs (K1.dueR J.P J.ride)) (e : Ahead)
      (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (front : Nat),
      SharedAsks Zp cF.blocksInOrder (parL Zp Bs.G₀ m (q == 1)) (K1.rideOf none) (noL m (q == 1)) 0
      (y'.2 + ((Sg.sent.headD #[]).size - 1) + 1 + q) ch p k
      (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hdL (0 + m)
      ((Sg.sent.headD #[]).size - 1 -
      (if (y'.1.map (·.1)).isSome then 1 + Sg.sizes.kept.length else 0) + q))
      Q Vd N w (hdL ++ ds) wit J own₀ cs e dataK front

/-- **WHAT `first_lockAsks` ASKS THAT THIS FILE DOES NOT TAKE OFF THE STAND**, at the switch into
the group 1. A structure of premises' forms. Nothing here proves that it can be met. It names a
run's coins. -/
structure FirstAsks (Zp : ProofFile.Pub) (Bs : ProofFile.PureBase) (cF : Chain TS ProofFile.Cl) (ch : Nat)
    (p : SwitchPlace) (k : Coins Bk) (c : SwitchCoins p.sizes p.others p.foldVars p.carries)
    (own : Nat → Nat → Nat → Nat → Cb.Gl.E) (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT)
    (Vd : Local W₀ Rc Xi Tr → Prop) (N : Nat) (w : Local W₀ Rc Xi Tr)
    (hdL ds : List Fmt.Drawn) : Prop where
  hN : N ≤ (hdL ++ ds).length
  asks : ∀ (y' : Option (Left × List OnBytes.OracleShape) × Nat) (Sg : SegmentPub),
    closingFrom freshTable own hdL (Stretch.carried p.carries c.2.2)
      ((segmentsOf Zp Bs.G₀).take 0) 0 0 none = .ok y' →
    (segmentsOf Zp Bs.G₀)[0]? = some Sg →
    (∀ n, n < (Sg.sent.headD #[]).size - 1 → ∃ (wit : Local W₀ Rc Xi Tr → W)
      (J : K1.SendJob W X) (own₀ : X) (cs : Cs (K1.dueR J.P J.ride)) (e : Ahead)
      (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (front : Nat),
      SharedAsks Zp cF.blocksInOrder (firstPar Bs.G₀.first (gpOf Zp))
      (K1.rideOf (K1.firstFold Bs.G₀.first)) 2 n (y'.2 + n) ch p k
      (dataAtOf Sg (y'.1.map (·.1)) (own (0 + 0)) n)
      Q Vd N w (hdL ++ ds) wit J own₀ cs e dataK front) ∧
    (∀ q, q < 2 → ∃ (wit : Local W₀ Rc Xi Tr → W) (J : K1.SendJob W X) (own₀ : X)
      (cs : Cs (K1.dueR J.P J.ride)) (e : Ahead)
      (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (front : Nat),
      SharedAsks Zp cF.blocksInOrder (parL Zp Bs.G₀ 0 (q == 1)) (K1.rideOf none) (noL 0 (q == 1)) 0
      (y'.2 + ((Sg.sent.headD #[]).size - 1) + 1 + q) ch p k
      (own (0 + 0) ((Sg.sent.headD #[]).size - 1 -
      (if (y'.1.map (·.1)).isSome then 1 + Sg.sizes.kept.length else 0) + q))
      Q Vd N w (hdL ++ ds) wit J own₀ cs e dataK front) ∧
    (∃ (wit : Local W₀ Rc Xi Tr → W) (J : K1.SendJob W X) (own₀ : X)
      (cs : Cs (K1.dueR J.P J.ride)) (e : Ahead) (front : Nat),
      MaskAsks Zp (firstPar Bs.G₀.first (gpOf Zp)) (K1.rideOf (K1.firstFold Bs.G₀.first))
      ((Sg.sent.headD #[]).size - 1) (y'.2 + ((Sg.sent.headD #[]).size - 1)) ch p k Q Vd N wit J
      own₀ cs e front)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Ky X₀ : Type} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- hOk, hst, hT, hty, y₀, A, hc, hW, hFirst AND hLater ARE PREMISES. One run's coins: never quoted
for a law. NOT IN FRONT OF A LAW OVER COINS. **`LockAsks` AT THE LETTERS OF A
STEP.** -/
theorem lockAsks_of_step {Wj Xj : Type} (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m)
    (hst : ∀ v i x u, (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w).thread.stored v i x = some u → ∀ a ∈ u, a < fieldPrimeWord)
    {p : SwitchPlace} (hp : p ∈ placesW) {n : P1K2.Nums} {st : VerifiableInference.Desc.First.K2.At}
    {before : TS → Except String TS} {after : TS → TS → Except String TS}
    (hArm : SwitchArm Zp Bs.G₀ p st before after) (hlen : switchNo p ≤ cF.blocksInOrder.length)
    {k : Coins Bk} {s s₁ t : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {Ev : Env}
    (hT : ThrS (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w).thread Said (switchNo p) k s m Ev)
    (hty : ∃ z : LPFD.Full.XF × OnBytes.Flat.RecFull, m.st.input.x.pub = (LPFD.Full.instanceAsPlainRecord z).pub)
    (y₀ : (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hb : before s = .ok s₁) (nm : String) {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {z : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {cd : Code}
    (A : AtYes (k2P Zp p.place nm st n) s₁ t r₁ r₂ gs x z S3 Y rows G cd)
    (ds : List Fmt.Drawn) (lay : OnBytes.Params.ReqLayout) (D : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries} (hc : handed 0 p k = some c)
    {Wl : Left}
    (hW : lotClosingAt lay (segmentsOf Zp Bs.G₀) p (D m.st.input.x) (readers m.st.input) m.st.heard
      (Stretch.carried p.carries c.2.2) = .ok Wl)
    (hFirst : p.link = 1 → ∃ N, FirstAsks (W := Wj) (X := Xj) Zp Bs cF 0 p k c
      (lotOwn segsW p (D m.st.input.x) (readers m.st.input) m.st.heard) Q
      (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w).valid N m.st.input m.st.heard ds)
    (hLater : 1 < p.link → ∃ (p₀ : SwitchPlace) (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars
        p₀.carries) (V : Nat → Johnson.Prover.Send.Rows) (N fx₀ : Nat),
      p₀ ∈ switchPlaces Zp Bs.G₀ ∧ p₀.link = p.link - 1 ∧
      OpenerAsks (W := Wj) (X := Xj) Zp Bs cF (p.link - 1) p₀ p Q
        (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w).valid N 0 fx₀ D readers lay k m.st.input m.st.heard ds c₀ c V) :
    LockAsks freshTable (lotOwn segsW p (D m.st.input.x) (readers m.st.input) m.st.heard) m.st.heard
      (Stretch.carried p.carries c.2.2) (p.link - 1) x
      (wordsFirst (P5J.At.arr Zp) x.st s₁.book (Q.wit k m.st.input (m.st.heard ++ ds))) := by
  have hpS : p ∈ switchPlaces Zp Bs.G₀ := by
    rw [places_at_head h.toAtMg O]
    exact hp
  have hlk : p.link = p.place.link.getD 25 := beq_iff_eq.1 (List.all_eq_true.1 placeLinksW.1 p hp)
  have hR := rch_at_head h H Q test item n₁ n₂ b₀ Vd Rd Kp w (carryExact Zp (P5J.At.arr Zp)) hOk hst
    hlen hT hty y₀
  have hv := hT.1.2.2.2.2.2.2
  obtain ⟨hseen, -, -, -, s₀, cols, hbeg, -, hfold⟩ := hT.1.2.2.2.2.1
  have e0 : s₀ = ProofFile.startS Zp m.st.input.x.pub := hbeg
  rw [e0] at hfold
  have hfold' : foldBlocks 0 (cF.blocksInOrder.take (switchNo p)) (ProofFile.startS Zp m.st.input.x.pub) m.seen
      cols = .ok (s, [], []) := hfold
  have eS := segments_at_head h.toAtMg O
  rw [eS] at hW
  obtain ⟨y, hy, ey⟩ := lotClosingAt_kept hW
  have hArm' := hArm
  rcases hArm' with ⟨rfl, -, h1, h24, ei, rfl, -⟩ | ⟨rfl, ep, ei, rfl, -⟩ | ⟨rfl, ep, ei, rfl, -⟩
  · obtain rfl : s = s₁ := Except.ok.inj hb
    have h23 : p.link - 1 < 23 := by omega
    have el : p.link = (p.link - 1) + 1 := by omega
    have hno : switchNo p = 14 * p.link + 2 := ei
    have eno : switchNo p = 14 * ((p.link - 1) + 1) + 2 := by
      rw [hno, ← el]
    have hR' : h.toAtMg.rch (14 * ((p.link - 1) + 1) + 2) ((m.st.input.x.pub, s), y₀) := by
      rw [← eno]
      exact hR
    obtain ⟨hstd, -⟩ := link_door h h23 _ hR'
    have hf : frontAt (ProofFile.pAtK2 Zp (p.link - 1)) s = some x :=
      (frontAt_stands (q := k2P Zp p.place nm .link n) hstd s).trans A.front
    rw [el] at hy
    obtain ⟨Sg, y', W', kept', hSg, hC, -, -, -⟩ := link_lastStep h h23 _ hR' hstd hf hy
    rw [eno] at hfold'
    by_cases e1 : p.link = 1
    · obtain ⟨N, F⟩ := hFirst e1
      have e00 : p.link - 1 = 0 := by omega
      rw [e00] at hR' hf hfold' hSg hC ⊢
      have hSg' : (segmentsOf Zp Bs.G₀)[0]? = some Sg := by
        rw [eS]
        exact hSg
      have hC' : closingFrom freshTable (lotOwn segsW p (D m.st.input.x) (readers m.st.input)
          m.st.heard) m.st.heard (Stretch.carried p.carries c.2.2)
          ((segmentsOf Zp Bs.G₀).take 0) 0 0 none = .ok y' := by
        rw [eS]
        exact hC
      obtain ⟨g1, g2, g3⟩ := F.asks y' Sg hC' hSg'
      exact first_lockAsks h O _ hR' hf 0 p k c hc _ Q _ N m.st.input hv m.st.heard ds F.hN hfold'
        hseen.symm hC' hSg' g1 g2 g3
    · obtain ⟨p₀, c₀, V, N, fx₀, hp₀, e₀, F⟩ := hLater (by omega)
      have hm1 : 1 ≤ p.link - 1 := by omega
      have hSg' : (segmentsOf Zp Bs.G₀)[p.link - 1]? = some Sg := by
        rw [eS]
        exact hSg
      have hC' : closingFrom freshTable (lotOwn (segmentsOf Zp Bs.G₀) p (D m.st.input.x)
          (readers m.st.input) m.st.heard) m.st.heard (Stretch.carried p.carries c.2.2)
          ((segmentsOf Zp Bs.G₀).take (p.link - 1)) 0 0 none = .ok y' := by
        rw [eS]
        exact hC
      exact link_lockAsks h O hm1 h23 _ hR' hf hp₀ hpS e₀ el Q _ N 0 fx₀ D readers lay F.hmS F.hpS
        F.hmF F.hpF k m.st.input hv m.st.heard ds F.hN F.hfx₀ c₀ F.h₀ c hc F.hs F.hf F.hgl F.hD
        F.hV hfold' hseen.symm hC' hSg' (F.HL y' Sg hC' hSg')
  · obtain rfl : s = s₁ := Except.ok.inj hb
    have e24 : p.link = 23 + 1 := by
      rw [hlk, ep]
      rfl
    have hR' : h.toAtMg.rch 339 ((m.st.input.x.pub, s), y₀) := by
      rw [← ei]
      exact hR
    obtain ⟨hstd, -⟩ := head_door h _ hR'
    have hf : frontAt (ProofFile.pAtK2 Zp 23) s = some x :=
      (frontAt_stands (q := k2P Zp p.place nm .head n) hstd s).trans A.front
    rw [e24] at hy
    obtain ⟨Sg, y', W', kept', hSg, hC, -, -, -⟩ := head_lastStep h _ hR' hstd hf hy
    have hno : switchNo p = 339 := ei
    rw [hno] at hfold'
    obtain ⟨p₀, c₀, V, N, fx₀, hp₀, e₀, F⟩ := hLater (by omega)
    have e23 : p.link - 1 = 23 := by omega
    rw [e23] at e₀ F ⊢
    have hSg' : (segmentsOf Zp Bs.G₀)[23]? = some Sg := by
      rw [eS]
      exact hSg
    have hC' : closingFrom freshTable (lotOwn (segmentsOf Zp Bs.G₀) p (D m.st.input.x)
        (readers m.st.input) m.st.heard) m.st.heard (Stretch.carried p.carries c.2.2)
        ((segmentsOf Zp Bs.G₀).take 23) 0 0 none = .ok y' := by
      rw [eS]
      exact hC
    exact head_lockAsks h O _ hR' hf hp₀ hpS e₀ e24 Q _ N 0 fx₀ D readers lay F.hmS F.hpS F.hmF
      F.hpF k m.st.input hv m.st.heard ds F.hN F.hfx₀ c₀ F.h₀ c hc F.hs F.hf F.hgl F.hD F.hV hfold'
      hseen.symm hC' hSg' (F.HL y' Sg hC' hSg')
  · have e25 : p.link = 24 + 1 := by
      rw [hlk, ep]
      rfl
    have hR' : h.toAtMg.rch 353 ((m.st.input.x.pub, s), y₀) := by
      rw [← ei]
      exact hR
    obtain ⟨hstd, -⟩ := fin_door h _ hR' hb
    have hf : frontAt (ProofFile.pAtK2 Zp 24) s₁ = some x :=
      (frontAt_stands (q := k2P Zp p.place nm .finish n) hstd s₁).trans A.front
    rw [e25] at hy
    obtain ⟨Sg, y', W', kept', hSg, hC, -, -, -⟩ := fin_lastStep h _ hR' hb hstd hf hy
    have hno : switchNo p = 353 := ei
    rw [hno] at hfold'
    obtain ⟨p₀, c₀, V, N, fx₀, hp₀, e₀, F⟩ := hLater (by omega)
    have e24' : p.link - 1 = 24 := by omega
    rw [e24'] at e₀ F ⊢
    have hSg' : (segmentsOf Zp Bs.G₀)[24]? = some Sg := by
      rw [eS]
      exact hSg
    have hC' : closingFrom freshTable (lotOwn (segmentsOf Zp Bs.G₀) p (D m.st.input.x)
        (readers m.st.input) m.st.heard) m.st.heard (Stretch.carried p.carries c.2.2)
        ((segmentsOf Zp Bs.G₀).take 24) 0 0 none = .ok y' := by
      rw [eS]
      exact hC
    exact fin_lockAsks h O _ hR' hb hf hp₀ hpS e₀ e25 Q _ N 0 fx₀ D readers lay F.hmS F.hpS F.hmF
      F.hpF k m.st.input hv m.st.heard ds F.hN F.hfx₀ c₀ F.h₀ c hc F.hs F.hf F.hgl F.hD F.hV hfold'
      hseen.symm hC' hSg' (F.HL y' Sg hC' hSg')

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.OpenerAsks
#print axioms ProofFile.Honest.K2.Law.FirstAsks
#print axioms ProofFile.Honest.K2.Law.lockAsks_of_step
