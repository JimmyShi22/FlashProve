-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/NextWithoutValues.lean: "THE RUN ON SHAPES RETURNS THE STATE's SHAPE", ONE
MEMBER ON (NextJ at shapeJ, Johnson/Desc/ProofFile/Honest/Thread/ShapeJ.lean), AT THE PROOF FILE's
OWN FIRST CHAIN, WITH THE VALUES OWED AT THE BATCHING MEMBERS ALONE. RuleAtTable.lean's
first_chain_debts asks the premise on the values (Values) at all 358 members, because it pays two
debts at once (AcceptedJ and NextJ). NextJ alone wants them only where the table has the weaker
"carries". Two theorems. Implications; nothing is evaluated.

Purpose. Whoever has each member's acceptance from another road (a kind's own law) and wants of the
run on shapes only the SHAPE of the state at a border needs NextJ alone, and only up to that
border.

Main names.
* `nextJ_of_carries`: GENERAL, at any thread and any shape: nextJ_of_shape (ShapeJ.lean) from the
  strong Carries (Johnson/Desc/ProofFile/Honest/Thread/Shape.lean) instead of CarriesU: the premise
  Values falls away.
* **`first_chain_next`**: under the head, at the table's own letters, for every thread T with T.bs
  = cF.blocksInOrder, every Said, fall and a₀, and every border n up to 358: the run on shapes returns over
  the first n members; ValuesJ (Johnson/Desc/ProofFile/Honest/Thread/ShapeJV.lean: the values,
  asked with the family in hand; Values gives it) at the numbers b below n with framed b = false
  (TableFramesAll.lean: the batching members: 14 l + 9 for l below 24, and 347): then NextJ at
  every member below n.

Limits. THE RUN ON SHAPES' RETURN STAYS A PREMISE (JoinKeepsLastShape.lean's
table_yes_at_of_runsAll has it at every border from the pieces, of which none is shown in the
library). ValuesJ AT THE BATCHINGS BELOW n STAYS A PREMISE: there the table's test runs the
member's own gathering and asks each run's own premises (BatchFrames.lean: batchV). Some clauses of
that test hang on the draws: where one fails, the premise wants a fall that speaks there
(RuleAtTable.lean's head). NextJ has "nothing of the member stops" and "fall b s ds = none" among
its premises, and the thread's sentence in front: at a fall that always speaks, or a thread whose
sentence never holds, it holds emptily. NO ACCEPTANCE: AcceptedJ is not concluded. Under the head
P5J.AtMgA: that it has a member is shown in scope, where the reader returns and `protocolDataWellFormed` accepts
(`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at two named sets of
public files, in a side library. At the format's second hash function. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.RuleAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest (Shape Thread Coins Mid ProverCoinCounts Carries ValuesJ NextJ shapeJ run_front
  nextJ_of_shapeV)

/-- **nextJ_of_shape FROM THE STRONG "CARRIES"**: no premise on the values. -/
theorem nextJ_of_carries {σ Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk σ Cl V W X Pb)
    (Said : Nat → Coins Bk → Mid W X → Prop) (Zs : Shape σ) {a₀ : Zs.Sh} {n b : Nat}
    {fall : Nat → σ → List Fmt.Drawn → Option String} (hb : b < n) (hyes : Zs.yes a₀ n = true)
    (hC : Carries T.bs T.ft Zs b) : NextJ T Said (shapeJ Zs a₀) fall b := by
  intro blk hblk k s m E ds y cols s' _ hJ _ _ _ hS
  obtain ⟨t, ht⟩ := run_front Zs a₀ n (b + 1) hb hyes
  have hg : Zs.g b (Zs.sh s) = .ok t := by
    have ht' : (Zs.run b a₀).bind (Zs.g b) = .ok t := ht
    rw [show Zs.run b a₀ = .ok (Zs.sh s) from hJ] at ht'
    exact ht'
  have e := hC blk hblk s _ cols s' cols.length t hS.2 hg
  show Zs.run (b + 1) a₀ = .ok (Zs.sh s')
  rw [ht, e]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-- **AT THE FIRST CHAIN: ONE MEMBER ON AT EVERY MEMBER BELOW A BORDER, THE VALUES OWED AT THE
BATCHINGS ALONE.** -/
theorem first_chain_next (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    {V W X Pb : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder)
    (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String) (a₀ : ShA) {n : Nat} (hn : n ≤ 358)
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a₀ n = true)
    (hV : ∀ b, b < n → framed b = false →
      ValuesJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀)
        (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall b) :
    ∀ b, b < n →
      NextJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀) fall b := by
  intro b hb
  cases hf : framed b with
  | true =>
    exact nextJ_of_carries T Said _ hb hyes (by rw [hbs]; exact (table_frames h hB b hf T.ft).1)
  | false =>
    exact nextJ_of_shapeV T Said _ hb hyes
      (by rw [hbs]; exact carriesU_of_V (table_all h hB b (Nat.lt_of_lt_of_le hb hn) T.ft).1)
      (hV b hb hf)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.nextJ_of_carries
#print axioms Johnson.AtFull.Shape.first_chain_next
