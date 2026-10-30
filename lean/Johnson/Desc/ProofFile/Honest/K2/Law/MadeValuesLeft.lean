-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MadeValuesLeft.lean: the kind "the code switch" (K2): AT THE
FIRST CHAIN's LETTERS AT THE LIBRARY's HEAD: OF THE EIGHT LIMBS OF `MadeLeft` (MadeAtHead.lean of
this folder) THE FIVE ON THE VERIFIER's STATE AT A YES ARE LAID IN; THE THREE ON VALUES STAY, AS ONE
NAMED PREMISE. So eighteen of the 21 fields of `MadeAsks` (ExchangeAtMade.lean) are had at these
letters: the seventeen that are not among its four on values, and, of these four, honest. A JOIN:
calls alone. One definition and one structure: premises' forms; statements with their proofs.

  `ValuesLeft`      WHAT IS LEFT, at one place: under the very binders of `MadeLeft`: claim ·
                    stored · symbols, each in the record's own text
  `SwitchLeftV`     `SwitchLeftM`'s first four fields as they stand, and `ValuesLeft` for the fifth
  `madeLeft_of_values`   `ValuesLeft` ⊢ `MadeLeft`
  `switchLeftM_of_values`   `SwitchLeftV` ⊢ `SwitchLeftM`
  `k2_exchange_of_values`   THE TOP: `SwitchLeftV` at each of the 25 written places ⊢ the kind's
                    whole debt under "the exchange", by kind

By, of this folder: `rows_at_yes` (AtYesRows.lean): carriedNo · positionNo · `check_at_yes`,
`fits_at_yes`, `seated_at_yes` (AtYesFits.lean) · `reach_at_head` (MadeAtHead.lean) ·
`k2_block_at_head` (BlockAtHead.lean): the kind's own yes, from the member's step ·
`switchArm_unique` (MadePublicPaid.lean) · `fold_of_thr` (SendsAtThread.lean) ·
`k2_exchange_of_made` (MadeAtHead.lean). HERE LEAN HOLDS THE FIVE TEXTS AGAINST `MadeLeft` ITSELF.
The way from the member's step to the kind's own yes goes as in the proof of `madeAsks_public_paid`.

Limits. AN IMPLICATION: `ValuesLeft` IS SHOWN OF NO PROVER AND NO SCRIPT: its three limbs speak of
values and are proved of no run. All three read Wl, which is made of the hidden readers and the
carried coins. None is paid. half, publicAt, msgs and pads stay as in PaidAtHead.lean of this
folder. hOk AND hst ARE PREMISES: on the letter Said, and on the prover's stored words. The head and
the opening are premises. A run's coins and the prover's state stand under the binders; of the
thread's stand the clause on how the state was made, and what was said, are read; of the step the
member's own step alone. NOT IN FRONT OF A LAW OVER COINS. It speaks at the head's
own size and hash: the full size, the format's second hash function. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.MadeAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.AtYesRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Slice OnBytes.Means Cb Cb.Ood Johnson.Pack VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Wit Block KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (AtYes frameAt keptSamples targetRows decideWith)
open VerifiableInference.Desc.K2.Honest (Left OldFits SeatedAt sizesAt HonestMain ClaimTrue oldWords
  SymbolsAre carryExact)
open VerifiableInference.Desc.Sound (MsgT below)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (seatAtMember)
open _root_.Tw.K2 (sendByL8)
open _root_.Desc.K14.Law (secondAt seatZ shownGroups)

/-- **WHAT IS LEFT OF `MadeLeft`, AT ONE PLACE**: its three limbs on values. A definition: the form
of a premise. Nothing here proves that it can be met.
NOT IN FRONT OF A LAW OVER COINS. -/
def ValuesLeft {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
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
        (ClaimTrue (sizesAt S3 x.f.rows x.T) x.f.rows Wl) ∧
        (∀ o ∈ (switchKept x.f.rows).toList, ∀ r ∈ (S3.oracles.getD o default).sampleRows.toList,
          Says rdE S3 r (oldWords (sizesAt S3 x.f.rows x.T) x.f.rows Wl)) ∧
        (SymbolsAre (sizesAt S3 x.f.rows x.T) x.f.rows Wl (Positions.ofDraws (IM.k2P Zp p.place nm
          st n).logN r₂.drawn.poss) Y)

/-- **WHAT IS LEFT OF `SwitchLeftM`, AT ONE PLACE**: its first four fields as they stand, and
`ValuesLeft` for the fifth. A structure of premises' forms. Nothing here proves that it can be met.
NOT IN FRONT OF A LAW OVER COINS. -/
structure SwitchLeftV {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
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
  /-- what is left of the field made: its three limbs on values -/
  left : ValuesLeft L Said Zp G D readers lay p

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

/-- hOk, hst AND hV ARE PREMISES. **`MadeLeft` FROM ITS THREE LIMBS ON VALUES.**
NOT IN FRONT OF A LAW OVER COINS. -/
theorem madeLeft_of_values
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m)
    (hst : ∀ v i x u, (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w).thread.stored v i x = some u → ∀ a ∈ u, a < fieldPrimeWord)
    {p : SwitchPlace} (hp : p ∈ placesW)
    (hV : ValuesLeft (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w) Said Zp Bs.G₀ D readers lay p) :
    MadeLeft (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp w)
      Said Zp Bs.G₀ D readers lay p := by
  intro blk Pp n nm st before after hblk hPp hn hArm k s m E ds y cols s' hT hdf hS c V Wl r₁ r₂
    s₁ t x z S3 Y rows Gr cd hc hVr hW hr hb A ha
  have hpS : p ∈ switchPlaces Zp Bs.G₀ := by
    rw [places_at_head h.toAtMg O]
    exact hp
  have hlen : switchNo p ≤ cF.blocksInOrder.length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.1 hblk).1
  have hR := reach_at_head h H Q test item n₁ n₂ b₀ Vd Rd Kp w (carryExact Zp (P5J.At.arr Zp)) hOk
    hst hlen hT
  obtain ⟨Pp', n', nm', st', before', after', hP', hn', hA', -, -, hdown⟩ :=
    k2_block_at_head h O hpS hblk
  obtain rfl : Pp' = Pp := Option.some.inj (hP'.symm.trans hPp)
  obtain rfl : n' = n := Option.some.inj (hn'.symm.trans hn)
  obtain ⟨rfl, rfl, rfl⟩ := switchArm_unique hA' hArm
  have hy := ((VerifiableInference.Desc.Sound.step_ok_iff _ _ _ _ _ _ _).1 hS.2).2.2.2
  rw [hr] at hy
  obtain ⟨s₁', u, hb', hd, -⟩ := hdown s _ _ s' hy
  obtain rfl : s₁' = s₁ := Except.ok.inj (hb'.symm.trans hb)
  have hd' : decideWith sendByL8 (IM.k2P Zp p.place nm st' n') s₁' [r₁, r₂] _ = .ok u := hd
  obtain ⟨R, C, hf⟩ := fold_of_thr h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd
    Kp w rfl hT.1
  obtain ⟨e6, e7, e8⟩ := hV blk Pp' n' nm st' before' after' hblk hPp hn hArm k s m E ds y cols s'
    hT hdf hS c V Wl r₁ r₂ s₁' t x z S3 Y rows Gr cd hc hVr hW hr hb A ha
  obtain ⟨c1, c2⟩ := rows_at_yes h O hpS hPp hn hArm hR hb nm hd' A
  exact ⟨c1, c2, check_at_yes h O hArm hf hb nm A, fits_at_yes h O hpS hArm hR hb nm A,
    seated_at_yes h O hpS hArm hR hb nm A, e6, e7, e8⟩

/-- hOk, hst AND hM ARE PREMISES. **`SwitchLeftM` FROM WHAT IS LEFT.**
NOT IN FRONT OF A LAW OVER COINS. -/
theorem switchLeftM_of_values
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m)
    (hst : ∀ v i x u, (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w).thread.stored v i x = some u → ∀ a ∈ u, a < fieldPrimeWord)
    {p : SwitchPlace} (hp : p ∈ placesW)
    (hM : SwitchLeftV (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w) Said Zp Bs.G₀ D readers lay p) :
    SwitchLeftM (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp w)
      Said Zp Bs.G₀ D readers lay p :=
  ⟨hM.half, hM.publicAt, hM.msgs, hM.pads,
    madeLeft_of_values h H Q test item n₁ n₂ b₀ Vd Rd Kp w O hOk hst hp hM.left⟩

/-- hOk, hst AND hM ARE PREMISES. **K2's WHOLE DEBT UNDER "THE EXCHANGE", BY KIND, FROM WHAT IS
LEFT.** NOT IN FRONT OF A LAW OVER COINS. -/
theorem k2_exchange_of_values
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hOk : ∀ b k m, Said b k m → SaidOk b k m)
    (hst : ∀ v i x u, (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w).thread.stored v i x = some u → ∀ a ∈ u, a < fieldPrimeWord)
    (hM : ∀ p ∈ placesW, SwitchLeftV
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
  k2_exchange_of_made h H Q test item n₁ n₂ b₀ Vd Rd Kp w O hOk hst fun p hp =>
    switchLeftM_of_values h H Q test item n₁ n₂ b₀ Vd Rd Kp w O hOk hst hp (hM p hp)

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.ValuesLeft
#print axioms ProofFile.Honest.K2.Law.SwitchLeftV
#print axioms ProofFile.Honest.K2.Law.madeLeft_of_values
#print axioms ProofFile.Honest.K2.Law.switchLeftM_of_values
#print axioms ProofFile.Honest.K2.Law.k2_exchange_of_values
