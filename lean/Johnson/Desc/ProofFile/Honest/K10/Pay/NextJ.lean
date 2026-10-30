-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/NextJ.lean: the closing of a segment (K10) on the road by shapes: at the table of steps
on shapes of the first chain (Johnson/AtFull/Shape/TableOfSteps.lean) the member's named test on values passes at every
stand in front of a closing (`ValuesJ`, Honest/Thread/ShapeJV.lean), and so the family "the run on shapes over the members in
front returns the state's shape" (`shapeJ`) goes one member on across each closing (`NextJ`, Honest/Thread/ShapeJ.lean).

  `tab_vals_close`      at each of the 25 closings' numbers the table's test on values is `closeInOrdB` of the state
  **`valuesJ_at_closing`**   `ValuesJ 𝕋 Said J Zs fall b` at the head's thread, at every J and fall and every Said that gives
                      `SaidOk`, at the table at any ground G
  **`nextJ_at_closing`**     `NextJ 𝕋 Said (shapeJ Zs a₀) fall b`, under the named premise that the run on shapes returns over
                      all 358 members, at the table at the ground that the public part's seat makes

Limits. That the run on shapes returns (`Shape.yes`) is a premise, answered by no theorem here. The head is a premise. Where
the thread's invariant holds at no stand of a border both forms hold there for nothing.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.AtReach
import Johnson.Desc.ProofFile.Honest.Thread.ReachAtHead
import Johnson.AtFull.Shape.RuleAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Chain Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.AtFull.Shape
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- At each closing's number the table's test on values is the test `closeInOrdB` on the state. -/
theorem tab_vals_close (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) {l : Nat} (hl : l < 25) :
    ∀ s rs gs, Tab.vals Zp G (14 * l + IM.nAt l + 5) s rs gs = closeInOrdB s := by
  obtain ⟨p, Q, e1, e2, -⟩ := close_frame_ord h l hl
  by_cases h24 : l = 24
  · subst h24
    have hc : Tab.cells Zp G 350 = Tab.close Zp 24 := cells_head Zp G 13 (by omega) rfl
    unfold Tab.close at hc
    rw [e1] at hc
    simp only [Option.bind_some, e2] at hc
    intro s rs gs
    show Tab.vals Zp G 350 s rs gs = _
    rw [cell_v hc]
  · have hn : 14 * l + IM.nAt l + 5 = 14 * l + 12 := by
      unfold IM.nAt
      rw [if_neg h24]
    have hc : Tab.cells Zp G (14 * l + 12) = Tab.close Zp l := cells_link Zp G l 11 (by omega) (by omega) rfl
    unfold Tab.close at hc
    rw [e1] at hc
    simp only [Option.bind_some, e2] at hc
    intro s rs gs
    rw [hn, cell_v hc]

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Sc : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

-- The first chain's thread under the head, written out once. The option turns off one early look of the notation
-- command, which has no case for a field access; each use is elaborated and type-checked as any term is.
set_option quotPrecheck false in
local notation "𝕋" => (lettersHead h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread

/-- **The table's test on values passes at every stand in front of a closing.** -/
theorem valuesJ_at_closing (G : ProofFile.Ground) {l : Nat} (hl : l < 25)
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) (J : Nat → TS → Prop)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    ValuesJ 𝕋 Said J (firstZA (Tab.g Zp G) (Tab.vals Zp G)) fall (14 * l + IM.nAt l + 5) := by
  intro blk hblk k s m E ds y cols hT _ _ _ _ _
  show Tab.vals Zp G (14 * l + IM.nAt l + 5) s _ _ = true
  rw [tab_vals_close h G hl]
  have hlt : 14 * l + IM.nAt l + 5 < cF.blocksInOrder.length := (List.getElem?_eq_some_iff.1 hblk).1
  have hk : 14 * l + IM.nAt l + 5 ≤ 353 := by
    unfold IM.nAt
    split <;> omega
  exact closeInOrdB_reached h hk
    (thrS_reach_below h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w (Nat.le_of_lt hlt) ⟨hT.1, hSaid _ _ _ hT.2⟩)

set_option maxRecDepth 100000 in
/-- **The family on shapes goes one member on across each closing**, where the run on shapes returns over the chain. -/
theorem nextJ_at_closing {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {l : Nat}
    (hl : l < 25) {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m) (fall : Nat → TS → List Fmt.Drawn → Option String) (a₀ : ShA)
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a₀ 358 = true) :
    NextJ 𝕋 Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀) fall (14 * l + IM.nAt l + 5) := by
  have hb : 14 * l + IM.nAt l + 5 < 358 := by
    unfold IM.nAt
    split <;> omega
  exact nextJ_of_shapeV 𝕋 Said _ hb hyes (carriesU_of_V (table_all h hB _ hb _).1)
    (valuesJ_at_closing h H Sc test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs.G₀ hl hSaid _ fall)

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.tab_vals_close
#print axioms ProofFile.Honest.K10.valuesJ_at_closing
#print axioms ProofFile.Honest.K10.nextJ_at_closing
