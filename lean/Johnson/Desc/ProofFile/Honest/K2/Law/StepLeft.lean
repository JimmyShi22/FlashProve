-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/StepLeft.lean: the kind "the code switch" (K2): THE PREMISE
`ValuesAsks` (ValuesOfLock.lean of this folder) WITH `LockAsks` TURNED INTO THE TWO RECORDS
`FirstAsks` AND `OpenerAsks` (LockAsksAtStep.lean). A definition: a premise's form. A statement
with its proof: one call.

  `StepAsks`        under `ValuesAsks`' very binders: that the input's public part is a typed
                    instance's · at p.link = 1 `FirstAsks` · beyond it a switch p₀ in front, with
                    `OpenerAsks` · `SymbolsAre`
  `valuesAsks_of_step`   `StepAsks` ⊢ `ValuesAsks`

Limits. AN IMPLICATION: `StepAsks` IS SHOWN OF NO PROVER AND NO SCRIPT. h, O, hOk, hst, y₀, hp AND
hV ARE PREMISES. It binds a run's coins k and c, and c₀ and V₀ stand under "there is"; the two
records speak of entries that hold them: equations between two texts' values: what is WRITTEN where.
One run's coins: never quoted for a law. NOT IN FRONT OF A LAW OVER COINS. The full
size; the format's second hash function. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ValuesOfLock
import Johnson.Desc.ProofFile.Honest.K2.Law.LockAsksAtStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes OnBytes.Slice OnBytes.Means Cb Cb.Ood Johnson.Pack VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Wit Block KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (AtYes)
open VerifiableInference.Desc.K2.Honest (Left sizesAt SymbolsAre carryExact)
open VerifiableInference.Desc.Sound (MsgT allOf EAll wordsFirst)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread
open _root_.Desc.K14.Law (secondAt seatZ shownGroups)

/-- **`ValuesAsks` WITH THE TWO RECORDS IN THE STEAD OF `LockAsks`, AT ONE PLACE.** A definition:
the form of a premise. Nothing here proves that it can be met.
NOT IN FRONT OF A LAW OVER COINS. -/
def StepAsks {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type} (Wj Xj : Type)
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
        (1 < p.link → ∃ (p₀ : SwitchPlace) (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars
            p₀.carries) (V₀ : Nat → Johnson.Prover.Send.Rows) (N fx₀ : Nat),
          p₀ ∈ switchPlaces Zp Bs.G₀ ∧ p₀.link = p.link - 1 ∧
          OpenerAsks (W := Wj) (X := Xj) Zp Bs cF (p.link - 1) p₀ p L.Q L.valid N 0 fx₀ D readers
            lay k m.st.input m.st.heard ds c₀ c V₀) ∧
        SymbolsAre (sizesAt S3 x.f.rows x.T) x.f.rows Wl (Positions.ofDraws (IM.k2P Zp p.place nm
          st n).logN r₂.drawn.poss) Y

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  {D : RowDataOf ProofFile.Inst} {readers : Local W₀ Rc ProofFile.Inst Tr → Readers}
  {lay : OnBytes.Params.ReqLayout} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- h, O, hOk, hst, y₀, hp AND hV ARE PREMISES. **`ValuesAsks` FROM `StepAsks`.**
NOT IN FRONT OF A LAW OVER COINS. -/
theorem valuesAsks_of_step {Wj Xj : Type} (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
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
    (hV : StepAsks Wj Xj (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd
      Kp
      w) Said Zp Bs cF D readers lay p) :
    ValuesAsks (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
      w) Said Zp Bs.G₀ D readers lay p := by
  intro blk Pp n nm st before after hb hP hn hArm k s m E ds y cols s' hT hd hS c V Wl r₁ r₂ s₁ t x
    z S3 Y rows Gr cd hc hL hW hr hbf A ha
  obtain ⟨hty, hF, hLt, hsym⟩ := hV blk Pp n nm st before after hb hP hn hArm k s m E ds y cols s'
    hT hd hS c V Wl r₁ r₂ s₁ t x z S3 Y rows Gr cd hc hL hW hr hbf A ha
  have hlen : switchNo p ≤ cF.blocksInOrder.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 hb).1
  have eh : m.st.heard.take (m.st.heard.length - 0) = m.st.heard := by simp
  rw [eh] at hW ⊢
  exact ⟨hty, lockAsks_of_step h H Q test item n₁ n₂ b₀ Vd Rd Kp w O hOk hst hp hArm hlen hT hty y₀
    hbf nm A ds lay D readers hc hW hF hLt, hsym⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.StepAsks
#print axioms ProofFile.Honest.K2.Law.valuesAsks_of_step
