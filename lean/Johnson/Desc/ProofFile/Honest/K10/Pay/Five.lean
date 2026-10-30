-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/Five.lean: the closing of a segment (K10): the five statements that a sub-protocol's
authors owe at each of its borders (`FiveAtBorder`, Honest/Thread/FiveAtBorder.lean), at all 25 closings of the first chain's
thread as a named term (`firstThread`, Honest/Thread/TheFirstThread.lean), at the prover that the maker `onlineProverFromPublicFiles` returns at the
filling `onlineProverPartsInUse I o S O`. Four of the five have no premise left but the return, the head at it and, for the
acceptance, that Said gives `SaidOk`. The fifth, the exchange, is had from three named premises.

  `ThreeLeft`           the three premises of the exchange at the item `carry l` that are still unpaid, by name: three of the
                      nine fields of `CarryOwed` (Honest/K10/Xch/CarryTop.lean), to the letter, with the thread a letter:
                        made    at the coins that the book gives the part, the job's rows are made and pass the public test
                        tie     the group's tables made of the witness's words are the tables made of these rows
                        fresh   the witness's table at the fresh mask's message pairs with the coefficients of the run that
                                the part spends
  `exchangeS_of_owed`   at the head's thread at the exact carry: `ExchangeS` at a closing's border from `CarryOwed` there
  `exchangeS_of_three`  the same from `ClosingsFirst`, the filler and `ThreeLeft`, at a Said that gives `SaidOk`
  **`k10_exchange_first`**   `ExchangeS (firstThread h parts w) Said b` from `ThreeLeft` at that thread and its script
  **`k10_five_first`**   `FiveAtBorder (firstThread h parts w) Said fall b` at each of the 25 closings, from `ThreeLeft`

Limits. `ThreeLeft` is a premise: it is shown of no script and no book here. tie and fresh are sentences on the thread's
script, which has no value yet; by an argument, not a proof, fresh fails at a script that lays zeros at the fresh mask's
message. hSaid is spent by the acceptance and by the exchange. The return of
`onlineProverFromPublicFiles` and the head at it are premises. Where the thread's invariant holds at no stand of a border all five hold there for
nothing. The full size and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.AtFirstThread
import Johnson.Desc.ProofFile.Honest.K10.Pay.BehindFirst
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchOwedThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT wordsFirst)
open OnBytes.Maker (WholeD)
open Johnson.Prover.Link (Pairs)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)
open ProofFile.Honest.K10.LeftIs (stageB freshB)

section
variable {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}

/-- **The three premises of the exchange at a closing that are still unpaid, by name.** A definition, meant as a premise:
three fields of `CarryOwed`, to the letter, with the thread T a letter. -/
structure ThreeLeft (T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst)
    (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT) (Zp : ProofFile.Pub)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst) (Gr : ProofFile.Ground)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (l : Nat) (Qc : Par) (blk : Block TS ProofFile.Cl) :
    Prop where
  /-- At the coins that the book gives the part, the job's rows are made and pass the public test. -/
  made : ∀ {k s m En ds y cols s'}, StepAt T Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∀ {D}, CloseBase Qc (K9.recOf s) D → ∀ {cc},
      closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place
        (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
      ∃ R, (lotJob readers rows stAt Zp Gr Qc).rows m.st.input m.st.heard (handSnd cc).2.2 = .ok R ∧
        rowsFit s.st D.G R = true
  /-- The group's tables made of the witness's words are the tables made of the prover's own rows. -/
  tie : ∀ {k s m En ds y cols s'}, StepAt T Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∀ {D}, CloseBase Qc (K9.recOf s) D → ∀ {cc},
      closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place
        (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
      ∀ {R}, (lotJob readers rows stAt Zp Gr Qc).rows m.st.input m.st.heard (handSnd cc).2.2 = .ok R →
      rowsFit s.st D.G R = true → ∀ ds',
      OnBytes.Means.tablesOf (D.S1 (K9.recOf s)) (Own.layoutOf (K9.recOf s).st D.G)
          (wordsFirst (P5J.At.arr Zp) s.st s.book (Sc.wit k m.st.input (m.st.heard ++ (ds ++ ds')))) =
        OnBytes.Means.tablesOf (D.S1 (K9.recOf s)) (Own.layoutOf (K9.recOf s).st D.G) (rowWords D (K9.recOf s) R)
  /-- The witness's table at the fresh mask's message pairs with the coefficients of the run that the part spends. -/
  fresh : ∀ {k s m En ds y cols s'}, StepAt T Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
    ∀ {D}, CloseBase Qc (K9.recOf s) D → ∀ {cc},
      closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place
        (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
      ∀ ds' W, CoefOf (spentRun (lotJob readers rows stAt Zp Gr Qc) (handSnd cc)) W →
      Pairs (stageB D (K9.recOf s)) (stageB D (K9.recOf s)).Z.l W
        (freshB D (K9.recOf s)
          (wordsFirst (P5J.At.arr Zp) s.st s.book (Sc.wit k m.st.input (m.st.heard ++ (ds ++ ds')))))

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (rows : RowDataOf ProofFile.Inst) (stAt : StAtOf ProofFile.Inst)
  (Gr : ProofFile.Ground) (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

-- The exact carry at the head's letters; the first chain's thread under the head at that value of the carry. The option
-- turns off one early look at a notation's text, which has no case for a field access or a named argument; it loosens
-- nothing in what Lean checks of a theorem.
set_option quotPrecheck false in
local notation "𝕏" => (carryExact (P := ProofFile.InstPub) (Cells := CellsM OnBytes.Flat.numsFull) (Tok := P5J.At.Tok) Zp
  (P5J.At.arr Zp))
set_option quotPrecheck false in
local notation "𝕋X" => (lettersHead h H Sc test 𝕏 item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- **The exchange at a closing's border, whole, from the nine premises there.** -/
theorem exchangeS_of_owed (l : Nat) (hl : l < 25)
    (Ow : ∀ p Qc blk, Tied cF Zp l p Qc blk →
      CarryOwed h H Sc test item n₁ n₂ b₀ Vd Rd Kp w readers rows stAt Gr Said l Qc blk) :
    ExchangeS 𝕋X Said (14 * l + IM.nAt l + 5) :=
  (exchangeS_iff 𝕋X Said).2
    (exchange_owes_at h H Sc test 𝕏 item n₁ n₂ b₀ Vd Rd Kp w Said l hl
      (exchange_carry_top h H Sc test item n₁ n₂ b₀ Vd Rd Kp w readers rows stAt Gr Said l hl rfl Ow)
      (exchange_pinKept_at_head h H Sc test 𝕏 item n₁ n₂ b₀ Vd Rd Kp w l hl rfl Said))

/-- **The same from the premise on the prover's list of halves, the filler, and the three that are left.** -/
theorem exchangeS_of_three (hSaid : ∀ b k m, Said b k m → SaidOk b k m) (l : Nat) (hl : l < 25)
    (half : ClosingsFirst H.first readers rows stAt Zp Gr)
    (fill : stAt = fun ξ : ProofFile.Inst => stAtZero cF.blocksInOrder (ProofFile.startS Zp) ξ.pub)
    (Left : ∀ p Qc blk, Tied cF Zp l p Qc blk →
      ThreeLeft 𝕋X Sc Zp readers rows stAt Gr Said l Qc blk) :
    ExchangeS 𝕋X Said (14 * l + IM.nAt l + 5) :=
  exchangeS_of_owed h H Sc test item n₁ n₂ b₀ Vd Rd Kp w readers rows stAt Gr Said l hl fun p Qc blk Td =>
    carryOwed_of_three h H Sc test item n₁ n₂ b₀ Vd Rd Kp w readers rows stAt Gr Said hSaid Td half fill
      (Left p Qc blk Td).made (Left p Qc blk Td).tie (Left p Qc blk Td).fresh

end

/-! ## At the first thread -/

section
variable {W₀ : Type} {files : VerifierAndGoals.PublicFiles} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL (onlineProverPartsInUse I o S O) = .ok A)
  (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)

/-- The three premises that are left, at the first thread itself, its script, and the filling's readers, rows' data and
filler. -/
abbrev ThreeLeftFirst (Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) (l : Nat) (Qc : Par)
    (blk : Block TS ProofFile.Cl) : Prop :=
  ThreeLeft (firstThread h parts w) parts.script A.Z
    (fun v : Local W₀ IndexCommitterCoins Inst Cells => (⟨v.trace, I.weights A.Z v.w₀, v.rc⟩ : Readers)) (widerRows S A.Z A.G)
    (stAtZero h.firstChain.blocksInOrder fun ξ : Inst => ProofFile.startS A.Z ξ.pub) A.G Said l Qc blk

include hA in
/-- **The exchange at each closing's border of the first thread**, from the three premises that are left. -/
theorem k10_exchange_first (l : Nat) (hl : l < 25)
    {Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop}
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (Left : ∀ p Qc blk, Tied h.firstChain A.Z l p Qc blk → ThreeLeftFirst I S h parts w Said l Qc blk) :
    ExchangeS (firstThread h parts w) Said (14 * l + IM.nAt l + 5) :=
  exchangeS_of_three h.head A.H parts.script _ _ _ _ _ _ _ _ w _ _ _ A.G Said hSaid l hl
    (closingsFirst_baseHead h.head I o S O hA).2 rfl Left

include hA in
/-- **The five statements at each of the 25 closings of the first thread**, from the three premises that are left. -/
theorem k10_five_first (l : Nat) (hl : l < 25)
    {Said : Nat → Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop}
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) (fall : Nat → TS → List Fmt.Drawn → Option String)
    (Left : ∀ p Qc blk, Tied h.firstChain A.Z l p Qc blk → ThreeLeftFirst I S h parts w Said l Qc blk) :
    FiveAtBorder (firstThread h parts w) Said fall (14 * l + IM.nAt l + 5) where
  plays := k10_plays_first I o S O hA h parts w l hl Said
  behind := behindS_closing_first h parts w Said hl
  exchange := k10_exchange_first I o S O hA h parts w l hl hSaid Left
  ridesPast := ridesPastS_closing_first h parts w Said hl
  accepted := k10_accepted_first I o S O hA h parts w l hl hSaid fall

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.ThreeLeft
#print axioms ProofFile.Honest.K10.exchangeS_of_owed
#print axioms ProofFile.Honest.K10.exchangeS_of_three
#print axioms ProofFile.Honest.K10.k10_exchange_first
#print axioms ProofFile.Honest.K10.k10_five_first
