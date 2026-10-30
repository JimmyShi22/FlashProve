-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchOwed.lean: the closing of a segment (K10): of the nine premises of the exchange
at the items that a closing owes (`CarryOwed`, Honest/K10/Xch/CarryTop.lean), three are theorems at every stand in front
of a closing: terms, mask and height. So the structure is built from the other six.

  `carryOwed_of_four`    at a block that `Tied` names, and at a second condition Said that gives `SaidOk`: from half and
                    fill (on parameters) and the four fields made, tie, fresh and door: `CarryOwed`
What it is for: `exchange_owes_of_kind` (Honest/K10/Xch/ByKind.lean) takes `CarryOwed` at all 25 closings.

By: `terms_reached` (Pay/Terms.lean) at the reach that the invariant with `SaidOk` gives (`thrS_reach_below`,
Honest/Thread/ReachAtHead.lean); `mask_at_thr` (Xch/Mask.lean); `height_at_thr` (Xch/Height.lean).

Limits. The six that are left are premises, shown here of no prover, script or state. The head is a premise. The thread
stands at the exact carry. The full size and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Xch.ByKind
import Johnson.Desc.ProofFile.Honest.K10.Xch.Height
import Johnson.Desc.ProofFile.Honest.K10.Xch.Mask
import Johnson.Desc.ProofFile.Honest.K10.Pay.Terms
import Johnson.Desc.ProofFile.Honest.K10.Pay.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.First.K2Caller (doorZ)
open VerifiableInference.Desc.K2.Honest (carryExact)
open VerifiableInference.Desc.Sound (MsgT wordsFirst)
open OnBytes.Maker (WholeD)
open Johnson.Prover.Link (Pairs)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K10.YesFree (BaseData CloseBase)
open ProofFile.Honest.K10.LeftIs (stageB freshB)

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

/-- **`CarryOwed` from six of its nine fields**, at a block that `Tied` names and at a Said that gives `SaidOk`. -/
theorem carryOwed_of_four (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Qc : Par} {blk : Block TS ProofFile.Cl}
    (Td : Tied cF Zp l p Qc blk)
    (half : ClosingsFirst H.first readers rows stAt Zp Gr)
    (fill : stAt = fun ξ : ProofFile.Inst => stAtZero cF.blocksInOrder (ProofFile.startS Zp) ξ.pub)
    (made : ∀ {k s m En ds y cols s'}, StepAt 𝕋X Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
      ∀ {D}, CloseBase Qc (K9.recOf s) D → ∀ {cc},
        closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf (𝕋X).chain) (k.look (𝕋X).chain) blk.place
          (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
        ∃ R, (lotJob readers rows stAt Zp Gr Qc).rows m.st.input m.st.heard (handSnd cc).2.2 = .ok R ∧
          rowsFit s.st D.G R = true)
    (tie : ∀ {k s m En ds y cols s'}, StepAt 𝕋X Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
      ∀ {D}, CloseBase Qc (K9.recOf s) D → ∀ {cc},
        closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf (𝕋X).chain) (k.look (𝕋X).chain) blk.place
          (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
        ∀ {R}, (lotJob readers rows stAt Zp Gr Qc).rows m.st.input m.st.heard (handSnd cc).2.2 = .ok R →
        rowsFit s.st D.G R = true → ∀ ds',
        OnBytes.Means.tablesOf (D.S1 (K9.recOf s)) (Own.layoutOf (K9.recOf s).st D.G)
            (wordsFirst (P5J.At.arr Zp) s.st s.book (Sc.wit k m.st.input (m.st.heard ++ (ds ++ ds')))) =
          OnBytes.Means.tablesOf (D.S1 (K9.recOf s)) (Own.layoutOf (K9.recOf s).st D.G) (rowWords D (K9.recOf s) R))
    (fresh : ∀ {k s m En ds y cols s'}, StepAt 𝕋X Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
      ∀ {D}, CloseBase Qc (K9.recOf s) D → ∀ {cc},
        closeCoins (V := Local W₀ Rc ProofFile.Inst Tr) (X := X) Bk (Bk.rowsOf (𝕋X).chain) (k.look (𝕋X).chain) blk.place
          (lotJob readers rows stAt Zp Gr Qc) = .ok cc →
        ∀ ds' W, CoefOf (spentRun (lotJob readers rows stAt Zp Gr Qc) (handSnd cc)) W →
        Pairs (stageB D (K9.recOf s)) (stageB D (K9.recOf s)).Z.l W
          (freshB D (K9.recOf s)
            (wordsFirst (P5J.At.arr Zp) s.st s.book (Sc.wit k m.st.input (m.st.heard ++ (ds ++ ds'))))))
    (door : ∀ {k s m En ds y cols s'}, StepAt 𝕋X Said (14 * l + IM.nAt l + 5) blk k s m En ds y cols s' →
      ∃ t fx, doorZ Zp l s' = some t ∧ First.K2.frontAt (ProofFile.pAtK2 Zp l) t = some fx) :
    CarryOwed h H Sc test item n₁ n₂ b₀ Vd Rd Kp w readers rows stAt Gr Said l Qc blk where
  half := half
  fill := fill
  terms := fun {k s m En _ _ _ _} St => by
    have hblk : cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk := Td.2.2.1
    have hlt : 14 * l + IM.nAt l + 5 < cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hblk).1
    have hT : ThrS 𝕋X SaidOk (14 * l + IM.nAt l + 5) k s m En := And.intro St.thr.1 (hSaid _ _ _ St.thr.2)
    exact terms_reached h (link_lt h hlt)
      (thrS_reach_below h H Sc test 𝕏 item n₁ n₂ b₀ Vd Rd Kp w (Nat.le_of_lt hlt) hT)
      (run_held_thr h H Sc test 𝕏 item n₁ n₂ b₀ Vd Rd Kp w St.thr.1).1
  mask := fun St => mask_at_thr h H Sc test 𝕏 item n₁ n₂ b₀ Vd Rd Kp w Td St.thr.1
  height := fun St _ Hb => height_at_thr h H Sc test 𝕏 item n₁ n₂ b₀ Vd Rd Kp w Td St.thr.1 Hb
  made := made
  tie := tie
  fresh := fresh
  door := door

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.carryOwed_of_four
