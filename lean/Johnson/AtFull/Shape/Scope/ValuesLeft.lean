-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/ValuesLeft.lean: WHAT IS LEFT OF THE FIRST CHAIN's DEBT ON THE VALUES AT THE THREAD UNDER
THE HEAD: fourteen fields, 105 members: `SortValuesLeft`; with the four fields that ValuesReachedHead.lean pays
they give SortValues: `sortValues_at_head`; and the rule with all that handed in: `debts_at_head`: at
`lettersHead`'s thread, at all its letters: from the run on shapes, the test `halved`, "Said gives SaidOk" and the
fourteen fields: AcceptedJ and NextJ at every member of the first chain. Calls; nothing is evaluated.

Limits. NOTHING SAYS THAT A FIELD OF SortValuesLeft CAN BE MET, that the run on shapes returns, or that `halved`
accepts. RuleAtTable.lean's Limits are inherited. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.ValuesReachedHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest (Shape Thread ProverCoinCounts Coins Mid Prover Local SaidOk ValuesJ NextJ AcceptedJ shapeJ halved)
open ProofFile.Honest.FirstThread (Script lettersHead WtF)

/-- **THE FOURTEEN FIELDS LEFT.** It is a definition: a premise's form. -/
structure SortValuesLeft {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S ProofFile.Cl V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (J : Nat → S → Prop) (Zs : Shape S)
    (fall : Nat → S → List Fmt.Drawn → Option String) : Prop where
  /-- the layers' own rounds, at the even links: k4ValsV -/
  layers : ∀ l, l < 24 → l % 2 = 0 → ValuesJ T Said J Zs fall (14 * l + 3 + 1)
  /-- the reads' sending at the attention's links: midV at valsTS -/
  readsAtt : ∀ l, l < 24 → l % 2 = 1 → ValuesJ T Said J Zs fall (14 * l + 4 + 1)
  /-- the batching: cellV -/
  batch : ∀ l, l < 24 → ValuesJ T Said J Zs fall (14 * l + 8 + 1)
  /-- behind the batching: behindV₃ | behindV -/
  behind : ∀ l, l < 24 → ValuesJ T Said J Zs fall (14 * l + 9 + 1)
  /-- the one equation: oneV -/
  equation : ∀ l, l < 24 → ValuesJ T Said J Zs fall (14 * l + 10 + 1)
  /-- the reply: replyV -/
  reply : ValuesJ T Said J Zs fall (337 + 1)
  /-- the code switch at the head: headW -/
  switchHead : ValuesJ T Said J Zs fall (337 + 2)
  /-- the head's own rounds: k6V -/
  head : ValuesJ T Said J Zs fall (337 + 4)
  /-- the head's reads: midV at covered -/
  readsHead : ValuesJ T Said J Zs fall (337 + 5)
  /-- the lookup on the head's own digits: headVals -/
  lookHead : ValuesJ T Said J Zs fall (337 + 8)
  /-- the batching at the head: cellV -/
  batchHead : ValuesJ T Said J Zs fall (337 + 10)
  /-- behind it: behindV -/
  behindHead : ValuesJ T Said J Zs fall (337 + 11)
  /-- the one equation at the head: oneV -/
  equationHead : ValuesJ T Said J Zs fall (337 + 12)
  /-- the proximity test: testV -/
  test : ValuesJ T Said J Zs fall (353 + 1)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- **THE EIGHTEEN FROM THE FOURTEEN, AT THE THREAD UNDER THE HEAD.** -/
theorem sortValues_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hS : ∀ b k m, Said b k m → SaidOk b k m) (J : Nat → TS → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) (G : ProofFile.Ground)
    (Lf : SortValuesLeft (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said J
      (firstZA (Tab.g Zp G) (Tab.vals Zp G)) fall) :
    SortValues (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said J
      (firstZA (Tab.g Zp G) (Tab.vals Zp G)) fall :=
  have R := reached_fields_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hS J fall G
  { switch := R.1, layers := Lf.layers, readsAtt := Lf.readsAtt, batch := Lf.batch,
    behind := Lf.behind, equation := Lf.equation, close := R.2.2.1, reply := Lf.reply,
    switchHead := Lf.switchHead, head := Lf.head, readsHead := Lf.readsHead,
    lookHead := Lf.lookHead, batchHead := Lf.batchHead, behindHead := Lf.behindHead,
    equationHead := Lf.equationHead, closeHead := R.2.2.2, finish := R.2.1, test := Lf.test }

/-- **THE FIRST CHAIN's TWO DEBTS AT THE THREAD UNDER THE HEAD, AT ALL ITS LETTERS.** -/
theorem debts_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hS : ∀ b k m, Said b k m → SaidOk b k m)
    (fall : Nat → TS → List Fmt.Drawn → Option String)
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes startShA 358 = true)
    (h4 : halved cF.blocksInOrder H.first = true)
    (Lf : SortValuesLeft (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA)
      (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall) :
    (∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
        AcceptedJ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
          (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA) fall b) ∧
      (∀ b, b < (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length →
        NextJ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
          (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA) fall b) :=
  debts_of_sorts h hB _ rfl Said fall hyes h4
    (sortValues_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hS _ fall Bs.G₀ Lf)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.sortValues_at_head
#print axioms Johnson.AtFull.Shape.debts_at_head
