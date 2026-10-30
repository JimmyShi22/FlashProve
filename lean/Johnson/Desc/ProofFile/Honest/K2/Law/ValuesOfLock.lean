-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ValuesOfLock.lean: the kind "the code switch" (K2): OF THE
THREE LIMBS OF `ValuesLeft` (MadeValuesLeft.lean of this folder) THE FIRST TWO, claim AND stored,
COME OF `LockAsks` (ClaimOfLock.lean). A JOIN: calls alone. A definition and a structure: premises'
forms; statements with their proofs.

WHICH SLOT IT IS FOR. `k2_exchange_of_values` (MadeValuesLeft.lean) has the kind's whole debt under
the exchange from `SwitchLeftV` at each of the 25 written places; its end is the hypothesis hXk of
the frame's gather at the kind K2. Here that debt stands on a different premise, where
`link_lockAsks`, `first_lockAsks`, `head_lockAsks` and `fin_lockAsks` arrive. IT IS NOT WEAKER:
`ValuesAsks` gives `ValuesLeft`: it adds that the input is typed, and `LockAsks` asks more than the
two limbs need.

  `ValuesAsks`      THE PREMISE IN `ValuesLeft`'s STEAD, at one place, under its very binders:
                    that the input's public part is a typed instance's · `LockAsks` at the words
                    of the Script's witness · `SymbolsAre`
  `SwitchLeftL`     `SwitchLeftV`'s first four fields as they stand, and `ValuesAsks` for the fifth
  `valuesLeft_of_asks`   `ValuesAsks` ⊢ `ValuesLeft`
  `k2_exchange_of_asks`   THE TOP: `SwitchLeftL` at each of the 25 written places ⊢ the kind's whole
                    debt under the exchange, by kind

By, of this folder: `claim_at_yes` (ClaimAtYes.lean) · `stored_at_yes` (StoredAtYes.lean) ·
`k2_exchange_of_values` (MadeValuesLeft.lean, of other authors).

WHAT PAYS `LockAsks`: `link_lockAsks`, `first_lockAsks` (LockAsksAtLink.lean), `head_lockAsks`,
`fin_lockAsks` (LockAsksAtArms.lean), each under premises of its own, none of them joined here.

Limits. AN IMPLICATION: `ValuesAsks` AND `SwitchLeftL` ARE SHOWN OF NO PROVER AND NO SCRIPT. hOk,
hst AND y₀ ARE PREMISES; y₀ is one value of the verifier's stand's second component. `ValuesAsks`
binds a run's coins k and the carried coins c; `LockAsks` there speaks of the entries that hold
them, `SymbolsAre` of what the columns open: equations between two texts' values: what is WRITTEN
where. `SymbolsAre` IS PAID BY NO FILE OF THIS FOLDER. The full size; the format's second hash function. One
run's coins: never quoted for a law. NOT IN FRONT OF A LAW OVER COINS. Nothing on
any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.MadeValuesLeft
import Johnson.Desc.ProofFile.Honest.K2.Law.StoredAtYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Slice OnBytes.Means Cb Cb.Ood Johnson.Pack VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Wit Block KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (AtYes)
open VerifiableInference.Desc.K2.Honest (Left sizesAt ClaimTrue oldWords SymbolsAre carryExact)
open VerifiableInference.Desc.Sound (MsgT allOf EAll wordsFirst)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (seatAtMember)
open _root_.Desc.K14.Law (secondAt seatZ shownGroups)

/-- **THE PREMISE IN `ValuesLeft`'s STEAD, AT ONE PLACE.** A definition: the form of a premise.
Nothing here proves that it can be met. NOT IN FRONT OF A LAW OVER COINS. -/
def ValuesAsks {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
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
        (∃ z : LPFD.Full.XF × OnBytes.Flat.RecFull, m.st.input.x.pub = (LPFD.Full.instanceAsPlainRecord z).pub) ∧
        LockAsks freshTable
          (lotOwn segsW p (D m.st.input.x) (readers m.st.input)
            (m.st.heard.take (m.st.heard.length - 0)))
          (m.st.heard.take (m.st.heard.length - 0)) (Stretch.carried p.carries c.2.2) (p.link - 1) x
          (wordsFirst (P5J.At.arr Zp) x.st s₁.book (L.Q.wit k m.st.input (m.st.heard ++ ds))) ∧
        SymbolsAre (sizesAt S3 x.f.rows x.T) x.f.rows Wl (Positions.ofDraws (IM.k2P Zp p.place nm
          st n).logN r₂.drawn.poss) Y

/-- **`SwitchLeftV` WITH `ValuesAsks` IN ITS FIFTH FIELD**: its first four fields as they stand. A
structure of premises' forms. Nothing here proves that it can be met.
NOT IN FRONT OF A LAW OVER COINS. -/
structure SwitchLeftL {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
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
  /-- the fifth field -/
  left : ValuesAsks L Said Zp G D readers lay p

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  {D : RowDataOf ProofFile.Inst} {readers : Local W₀ Rc ProofFile.Inst Tr → Readers}
  {lay : OnBytes.Params.ReqLayout} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- hOk, hst, y₀ AND hV ARE PREMISES. **`ValuesLeft` FROM `ValuesAsks`.**
NOT IN FRONT OF A LAW OVER COINS. -/
theorem valuesLeft_of_asks (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
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
    (y₀ : (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    {p : SwitchPlace} (hp : p ∈ placesW)
    (hV : ValuesAsks (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w) Said Zp Bs.G₀ D readers lay p) :
    ValuesLeft (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w) Said Zp Bs.G₀ D readers lay p := by
  intro blk Pp n nm st before after hb hP hn hArm k s m E ds y cols s' hT hd hS c V Wl r₁ r₂ s₁ t x
    z S3 Y rows Gr cd hc hL hW hr hbf A ha
  obtain ⟨hty, hA, hsym⟩ := hV blk Pp n nm st before after hb hP hn hArm k s m E ds y cols s' hT hd
    hS c V Wl r₁ r₂ s₁ t x z S3 Y rows Gr cd hc hL hW hr hbf A ha
  have hlen : switchNo p ≤ cF.blocksInOrder.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 hb).1
  exact ⟨claim_at_yes h H Q test item n₁ n₂ b₀ Vd Rd Kp w O hOk hst hp hArm hlen hT hty y₀ hbf nm A
      ds hW hA,
    stored_at_yes h H Q test item n₁ n₂ b₀ Vd Rd Kp w O hOk hst hp hArm hlen hT hty y₀ hbf nm A ds
      hW hA, hsym⟩

/-- hOk, hst, y₀ AND hM ARE PREMISES. **K2's WHOLE DEBT UNDER "THE EXCHANGE", BY KIND, FROM
`SwitchLeftL`.** The end is `k2_exchange_of_values`'s.
NOT IN FRONT OF A LAW OVER COINS. -/
theorem k2_exchange_of_asks (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
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
    (y₀ : (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hM : ∀ p ∈ placesW, SwitchLeftL
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
  k2_exchange_of_values h H Q test item n₁ n₂ b₀ Vd Rd Kp w O hOk hst fun p hp =>
    ⟨(hM p hp).half, (hM p hp).publicAt, (hM p hp).msgs, (hM p hp).pads,
      valuesLeft_of_asks h H Q test item n₁ n₂ b₀ Vd Rd Kp w O hOk hst y₀ hp (hM p hp).left⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.ValuesAsks
#print axioms ProofFile.Honest.K2.Law.SwitchLeftL
#print axioms ProofFile.Honest.K2.Law.valuesLeft_of_asks
#print axioms ProofFile.Honest.K2.Law.k2_exchange_of_asks
