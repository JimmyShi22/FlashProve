-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/JoinTable.lean: THE LAST JOINT OF THE RUN ON SHAPES: FROM ONE FACT A PIECE
(RunsAll, JoinAll.lean) TO THE PREMISE hyes OF RuleAtTable.lean's LAWS ON THE FIRST CHAIN: the run
on shapes over THE TABLE's OWN STEPS returns at all 358 members, from the first shape startShA,
under the head at the stored full-size files: **`table_yes_of_runsAll`**. Three theorems.
Implications; nothing is evaluated in this file.

What it joins. record_there and yes_of_runsAll (JoinAll.lean) · yes_of_publicN (YesAtZFullN.lean:
from the record with written letters and numerals to the head's own letters) · startShA
(RuleAtTable.lean: the first state's whole shape at the full size, a closed term). Its conclusion
is the premise hyes of RuleAtTable.lean's first_chain_debts at a₀ := startShA: `debts_of_runsAll`
and `debts_halved_of_runsAll` (by first_chain_debts_halved) hand it in.

Limits. ALL PIECES ARE ONE PREMISE: ∀ k < K, RunsAll (border len k) (len k) (c k) (c (k + 1)): not
one such fact is shown here, and in the library none is. UNDER THE HEAD P5J.AtMgA at VerifierAndGoals.storedPublicFiles,
with baseOf's return, and under hsz: that the head has a member, and hsz itself, are shown in a side
library alone. The conclusion is one premise among several of RuleAtTable.lean's laws. FOR
VerifierAndGoals.zGap, THE OTHER NAMED SET OF PUBLIC FILES, NO SUCH JOINT STANDS. THE CONCLUSION DROPS THE
LAST SHAPE c K: it says that the run returns, not what. table_yes_of_runsAll RESTS, THROUGH
yes_of_publicN AND record_there, ON LINES OF LEAN's KERNEL ("decide +kernel"), AMONG THEM:
lettersTest_atXL (LettersNumerals.lean), k2_written (K2NumsWritten.lean), k9_written, close_written
and before_H8 (WrittenLiterals.lean), and the closed facts beneath publicOfO_zFull_of_rest
(owners_W, widths_W and their kin: Johnson/AtFull/Public/); the two uses besides on framedV_all
(TableBatch.lean). THIS LIST IS NOT WHOLE. IT STANDS OVER FIVE FILES OF THIS FOLDER THAT NO OTHER
FILE OF THE JOIN REACHES: RuleAtTable.lean, TableBatch.lean, TableFramesAll.lean, YesAtZFull.lean,
YesAtZFullN.lean. LIMITS OF RuleAtTable.lean's LAWS ARE INHERITED BY THE TWO USES: fall, T and Said
are free letters: one equation ties T.bs = cF.blocksInOrder; beyond it they stand under the uses' own
premises alone (hF and hV; in the second use h4 and hV). The premise on the values (Values |
ValuesJ) and both conclusions have "fall b s ds = none" among their premises: at a fall that always
speaks they hold emptily. They have Thr among their premises too: at a thread whose Thr never holds
they hold emptily AT EVERY fall; so do ValuesJ and both conclusions at a Said that never holds. Some
clauses of the table's tests hang on the draws: wherever the thread comes to an event at which such
a clause fails, the premise on the values wants a fall that speaks there (that file's head has it in
full). That the test `halved` accepts at any prover is not shown. h0 : c 0 = startShA: startShA is a
term, no literal: whoever takes it as c 0 pays by rfl, and the first piece's fact then unfolds it;
whoever writes the first border as a literal owes that equation besides. RuleAtTable.lean is
imported for startShA and for the two uses below. At the format's second hash function; synthetic weights.
Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.JoinAll
import Johnson.AtFull.Shape.YesAtZFullN
import Johnson.AtFull.Shape.RuleAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

variable {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- **THE LAST JOINT**: all pieces as one hypothesis, the first border startShA, the lengths' sum
358 ⊢ under the head at the stored full-size files: THE RUN ON SHAPES OVER THE TABLE's OWN STEPS
RETURNS AT ALL 358 MEMBERS: the premise hyes of RuleAtTable.lean's laws on the first chain. -/
theorem table_yes_of_runsAll (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (h : AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (len : Nat → Nat) (c : Nat → ShA) (K : Nat)
    (hp : ∀ k, k < K → RunsAll (ProofFile.Honest.border len k) (len k) (c k) (c (k + 1)))
    (h0 : c 0 = startShA) (hK : ProofFile.Honest.border len K = 358) :
    (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes startShA 358 = true := by
  obtain ⟨X₀, hX⟩ := record_there hsz
  have e := yes_of_runsAll len c K hp X₀ hX
  rw [h0, hK] at e
  exact yes_of_publicN hsz h hB ⟨X₀, hX, e⟩

open ProofFile.Honest (Thread Coins Mid ProverCoinCounts FitsAt Values NextJ AcceptedJ shapeJ) in
/-- **The use**: first_chain_debts (RuleAtTable.lean) with its premise on the run on shapes handed
in by table_yes_of_runsAll. Of that law's own premises the fits (hF) and the values (hV) are left;
the head, hB, hbs, hsz and the pieces themselves (hp, h0, hK) stay premises. -/
theorem debts_of_runsAll (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (h : AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (len : Nat → Nat) (c : Nat → ShA) (K : Nat)
    (hp : ∀ k, k < K → RunsAll (ProofFile.Honest.border len k) (len k) (c k) (c (k + 1)))
    (h0 : c 0 = startShA) (hK : ProofFile.Honest.border len K = 358)
    {V W X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder)
    (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String)
    (hF : ∀ b, b < 358 → FitsAt T b)
    (hV : ∀ b, b < 358 → Values T (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall b) :
    (∀ b, b < T.bs.length →
        AcceptedJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA) fall b) ∧
      (∀ b, b < T.bs.length →
        NextJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA) fall b) :=
  first_chain_debts h hB T hbs Said fall startShA
    (table_yes_of_runsAll hsz h hB len c K hp h0 hK) hF hV

open ProofFile.Honest (Thread Coins Mid ProverCoinCounts ValuesJ NextJ AcceptedJ shapeJ halved) in
/-- The same by first_chain_debts_halved: one test with code (halved) in the stead of the fits, and
the weaker ValuesJ in the stead of Values. -/
theorem debts_halved_of_runsAll (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (h : AtMgA OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (len : Nat → Nat) (c : Nat → ShA) (K : Nat)
    (hp : ∀ k, k < K → RunsAll (ProofFile.Honest.border len k) (len k) (c k) (c (k + 1)))
    (h0 : c 0 = startShA) (hK : ProofFile.Honest.border len K = 358)
    {V W X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder)
    (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String)
    (h4 : halved cF.blocksInOrder T.hs = true)
    (hV : ∀ b, b < 358 →
      ValuesJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA)
        (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall b) :
    (∀ b, b < T.bs.length →
        AcceptedJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA) fall b) ∧
      (∀ b, b < T.bs.length →
        NextJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) startShA) fall b) :=
  first_chain_debts_halved h hB T hbs Said fall startShA
    (table_yes_of_runsAll hsz h hB len c K hp h0 hK) h4 hV

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.table_yes_of_runsAll
#print axioms Johnson.AtFull.Shape.debts_of_runsAll
#print axioms Johnson.AtFull.Shape.debts_halved_of_runsAll
