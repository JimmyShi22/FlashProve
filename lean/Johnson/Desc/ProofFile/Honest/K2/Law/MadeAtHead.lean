-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MadeAtHead.lean: the kind "the code switch" (K2): AT THE FIRST
CHAIN's LETTERS AT THE LIBRARY's HEAD: WHAT IS LEFT OF THE FIELD made OF `SwitchLeft`
(PaidAtHead.lean of this folder): THIRTEEN OF THE 21 FIELDS OF `MadeAsks` ARE LAID IN; EIGHT STAY,
AS ONE NAMED PREMISE. A JOIN: calls alone. One definition and one structure: premises' forms;
statements with their proofs.

  `reach_at_head`   from the thread's invariant with `Said`, where `Said` gives `SaidOk` and the
                    stored words lie below the prime: the library's "reached" over the blocks under
                    `below`, at these letters
  `MadeLeft`        WHAT IS LEFT, at one place: under the very binders of `SwitchLeft.made`: five
                    public fields (carriedNo · positionNo · check · fits · seated) and three on
                    values (claim · stored · symbols), each in the record's own text
  `SwitchLeftM`     `SwitchLeft`'s first four fields as they stand, and `MadeLeft` for the fifth
  `switchLeft_of_made`   `SwitchLeftM` ⊢ `SwitchLeft`
  `k2_exchange_of_made`  THE TOP: `SwitchLeftM` at each of the 25 written places ⊢ the kind's whole
                    debt under "the exchange", by kind

By, of this folder: `madeAsks_public_paid` (MadePublicPaid.lean): eleven public fields ·
`sizes_at_yes`, `fresh_at_yes` (SizesAtYes.lean): at a yes at a reached state the sizes are the
place's own; the field fresh · `honestMain_at_head` (HonestAtHead.lean): the field honest at the
place's own sizes · `k2_exchange_at_head` (PaidAtHead.lean). Of other authors: `reach_below`
(Honest/Thread/SaidOk.lean).

Limits. AN IMPLICATION: `MadeLeft` IS SHOWN OF NO PROVER AND NO SCRIPT. Three of its eight limbs
speak of values and are proved of no run. hOk AND hst ARE PREMISES: on the letter Said, and on the
prover's stored words. half, publicAt, msgs and pads stay as in PaidAtHead.lean. The head and the
opening are premises. NOT IN FRONT OF A LAW OVER COINS. The full size; the format's
second hash function. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PaidAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.MadePublicPaid
import Johnson.Desc.ProofFile.Honest.K2.Law.SizesAtYes
import Johnson.Desc.ProofFile.Honest.K2.Law.HonestAtHead
import Johnson.Desc.ProofFile.Honest.Thread.SaidOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Slice OnBytes.Means Cb Cb.Ood Johnson.Pack VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Wit Block KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (AtYes frameAt keptSamples targetRows)
open VerifiableInference.Desc.K2.Honest (Left OldFits SeatedAt sizesAt HonestMain ClaimTrue oldWords
  SymbolsAre carryExact)
open VerifiableInference.Desc.Sound (MsgT below)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (seatAtMember)
open _root_.Desc.K14.Law (secondAt seatZ shownGroups)

/-- **WHAT IS LEFT OF made, AT ONE PLACE.** A definition: the form of a premise. Nothing here proves
that it can be met. NOT IN FRONT OF A LAW OVER COINS. -/
def MadeLeft {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
    (L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (Zp : ProofFile.Pub) (G : ProofFile.Ground)
    (D : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (p : SwitchPlace) : Prop :=
  ∀ (blk : Block TS ProofFile.Cl) (Pp : P1K2.Prep) (n : P1K2.Nums) (nm : String)
    (st : VerifiableInference.Desc.First.K2.At) (before : TS → Except String TS)
    (after : TS → TS → Except String TS), L.bs[switchNo p]? = some blk →
    P1K2.prepOf Zp G = some Pp → P1K2.numsAt Pp p.place.link = some n →
    SwitchArm Zp G p st before after →
    ∀ k s m E ds y cols s', ThrS L.thread Said (switchNo p) k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      ∀ c V Wl r₁ r₂ s₁ t x z S3 Y rows Gr cd, handed 0 p k = some c →
        switchRowsLaid D readers (lotClosingAt lay (segmentsOf Zp G)) p c m.st.input m.st.heard =
          .ok V →
        lotClosingAt lay (segmentsOf Zp G) p (D m.st.input.x) (readers m.st.input)
          (m.st.heard.take (m.st.heard.length - 0)) (Stretch.carried p.carries c.2.2) = .ok Wl →
        (roundsOf y.1).map noDigest = [r₁, r₂] → before s = .ok s₁ →
        AtYes (IM.k2P Zp p.place nm st n) s₁ t r₁ r₂
          (shownGroups L.thread.ft blk (roundsOf y.1) cols) x z S3 Y rows Gr cd →
        after s₁ t = .ok s' →
        (∀ W₀, frameAt x = some W₀ → L.N.rowsAt p.link .carried = (0, 1 + keptSamples x W₀)) ∧
        (∀ W₀, frameAt x = some W₀ → L.N.rowsAt p.link .position = (1 + keptSamples x W₀,
          r₂.drawn.poss.length * (1 + targetRows x.T + 2))) ∧
        (switchTargetCheck S3 x.f.rows x.T = true) ∧
        (OldFits S3 x.f.rows) ∧
        (SeatedAt S3 x.f.rows x.T (z.ids.getD 0 noId) (z.ids.extract 1 (1 + x.T.kept.size))) ∧
        (ClaimTrue (sizesAt S3 x.f.rows x.T) x.f.rows Wl) ∧
        (∀ o ∈ (switchKept x.f.rows).toList, ∀ r ∈ (S3.oracles.getD o default).sampleRows.toList,
          Says rdE S3 r (oldWords (sizesAt S3 x.f.rows x.T) x.f.rows Wl)) ∧
        (SymbolsAre (sizesAt S3 x.f.rows x.T) x.f.rows Wl (Positions.ofDraws (IM.k2P Zp p.place nm
          st n).logN r₂.drawn.poss) Y)

/-- **WHAT IS LEFT OF `SwitchLeft`, AT ONE PLACE**: its first four fields as they stand, and
`MadeLeft` for the fifth. A structure of premises' forms. Nothing here proves that it can be met.
NOT IN FRONT OF A LAW OVER COINS. -/
structure SwitchLeftM {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
    (L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (Zp : ProofFile.Pub) (G : ProofFile.Ground)
    (D : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (p : SwitchPlace) : Prop where
  /-- the record's field: the half that stands at the place is the kind's one lot's -/
  half : (L.hs.find? fun g => g.place == p.place) = some (switchHalf (coreSender freshTable) D
    readers (lotClosingAt lay (segmentsOf Zp G)) p)
  /-- the record's field: the public test on the filling, at each valid input's instance -/
  publicAt : ∀ w, L.valid w → publicOk D lay p ((segmentsOf Zp G).take p.link) w.x = true
  /-- the record's field: the tie of the Script's messages to the kind's own text off the pads -/
  msgs : ∀ n, n < (switchPar p).sent.size → OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs
    (switchNo p)) ((P5J.At.arr Zp) (seatAtMember L.bs (switchNo p) (switchPar p) n).1 (seatAtMember
    L.bs (switchNo p) (switchPar p) n).2) (L.thread.front + roundsTo L.bs (switchNo p))
    (switchMsgOff 0 D readers (lotClosingAt lay (segmentsOf Zp G)) p n)
  /-- the record's field: the tie of the Script's pads -/
  pads : ∀ n, n < (switchPar p).sent.size → OwnPads L.Q L.valid (seatAtMember L.bs (switchNo p)
    (switchPar p) n).1 (seatAtMember L.bs (switchNo p) (switchPar p) n).2 (fun k _ => switchPadTxt 0
    p n k)
  /-- what is left of the field made -/
  left : MadeLeft L Said Zp G D readers lay p

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  {D : RowDataOf ProofFile.Inst} {readers : Local W₀ Rc ProofFile.Inst Tr → Readers}
  {lay : OnBytes.Params.ReqLayout} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- hOk AND hst ARE PREMISES. **FROM THE THREAD TO "REACHED" UNDER `below`, AT THESE LETTERS.** -/
theorem reach_at_head (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m)
    (hst : ∀ v i x u, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.stored v i x =
      some u → ∀ a ∈ u, a < fieldPrimeWord)
    {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hb : b ≤ cF.blocksInOrder.length)
    (hT : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said b k s m E) :
    Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) b (m.st.input.x.pub, s) :=
  reach_below (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread (ProofFile.startS Zp)
    m.st.input.x.pub hb (fun _ e => e) hst ⟨hT.1, hOk _ _ _ hT.2⟩

/-- hOk, hst AND hM ARE PREMISES. **`SwitchLeft` FROM WHAT IS LEFT.**
NOT IN FRONT OF A LAW OVER COINS. -/
theorem switchLeft_of_made
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m)
    (hst : ∀ v i x u, (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w).thread.stored v i x = some u → ∀ a ∈ u, a < fieldPrimeWord)
    {p : SwitchPlace} (hp : p ∈ placesW)
    (hM : SwitchLeftM (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w) Said Zp Bs.G₀ D readers lay p) :
    SwitchLeft (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp w)
      Said Zp Bs.G₀ D readers lay p where
  half := hM.half
  publicAt := hM.publicAt
  msgs := hM.msgs
  pads := hM.pads
  made := by
    intro blk Pp n nm st before after hblk hPp hn hArm k s m E ds y cols s' hT hdf hS c V Wl r₁ r₂
      s₁ t x z S3 Y rows Gr cd hc hV hW hr hb A ha
    have hpS : p ∈ switchPlaces Zp Bs.G₀ := by
      rw [places_at_head h.toAtMg O]
      exact hp
    have hlen : switchNo p ≤ cF.blocksInOrder.length :=
      Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk).1
    have hR := reach_at_head h H Q test item n₁ n₂ b₀ Vd Rd Kp w (carryExact Zp (P5J.At.arr Zp)) hOk
      hst hlen hT
    have hsz := sizes_at_yes h O hpS hArm hR hb nm A
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := hM.left blk Pp n nm st before after hblk hPp hn hArm
      k s m E ds y cols s' hT hdf hS c V Wl r₁ r₂ s₁ t x z S3 Y rows Gr cd hc hV hW hr hb A ha
    exact madeAsks_public_paid h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp w
      rfl O hpS hblk hPp hn hArm Said hT hS hr hb A ha (fresh_at_yes h O hpS hArm hR hb nm A) e1 e2
      e3 e4 e5 (by rw [hsz]; exact honestMain_at_head h.toAtMg O hpS hV hW) e6 e7 e8

/-- hOk, hst AND hM ARE PREMISES. **K2's WHOLE DEBT UNDER "THE EXCHANGE", BY KIND, FROM WHAT IS
LEFT.** NOT IN FRONT OF A LAW OVER COINS. -/
theorem k2_exchange_of_made
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m)
    (hst : ∀ v i x u, (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w).thread.stored v i x = some u → ∀ a ∈ u, a < fieldPrimeWord)
    (hM : ∀ p ∈ placesW, SwitchLeftM
      (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp w) Said Zp
      Bs.G₀ D readers lay p) :
    ∀ b p₀, P5J.At.ps[b]? = some p₀ → p₀.kind = KindName.K2 →
      ∀ j : First.Item, j ∈ ((lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀
        Vd Rd Kp w).thread.row b).owes →
      (j ∈ (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
          w).thread.opened b →
        (∀ m t, j ≠ First.Item.pin m t) ∧ j ≠ First.Item.pinI ∧ j ≠ First.Item.pinW ∧
        ∀ m q, q ∈ P5J.parts4 → j ≠ First.Item.constr m q) →
      ExchangeAtS (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
        w).thread Said b j :=
  k2_exchange_at_head h H Q test item n₁ n₂ b₀ Vd Rd Kp w O fun p hp =>
    switchLeft_of_made h H Q test item n₁ n₂ b₀ Vd Rd Kp w O hOk hst hp (hM p hp)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.MadeLeft
#print axioms ProofFile.Honest.K2.Law.SwitchLeftM
#print axioms ProofFile.Honest.K2.Law.reach_at_head
#print axioms ProofFile.Honest.K2.Law.switchLeft_of_made
#print axioms ProofFile.Honest.K2.Law.k2_exchange_of_made
