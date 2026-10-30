-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/TiesAtHead.lean: the proofs of `ScriptAtHead` and
`TiesAtHead` (Honest/K11/Plays/TiesAtHeadStatement.lean), to the letter. Lemmas; none of the
library's goals.

How. The first: two fields are the premise's own. The third: at the head's letters the reader of the
pile's matrix is the library's `matOfCells` at the witness's cells (by unfolding: `MgData.rw13`,
Johnson/Desc/Sound/MgAll.lean; `rwBook`, Johnson/Desc/K13/Law/ReaderByBook.lean; `At.mat13`,
Johnson/P5J/LettersAt3.lean), which at the column with the number C is the cell by numbers
(`matOfCells_low`, Johnson/Desc/K13/Law/MatOfCells.lean); the witness's cells are the Script's at
the input, which is the same behind the member's step (the frame's `play_mid`); the matrix has as
many rows, and as many bits for a column, as the kind's layout (`colBitsAtFull`,
Johnson/Desc/K11/Exchange/NumsAtFull.lean, at the library's `numsB_head_of_public`, which brings one
evaluation in Lean's kernel). The second: `tiesOfScript` (Script.lean of this folder) at the first
and at `claimTrue_at_head` (ClaimTrue.lean of this folder), whose premise that the item is open at
346 is `weightsOpen_at_head` (OpenAt346.lean of this folder: a second evaluation in Lean's kernel).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.TiesAtHeadStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.ClaimTrue
import Johnson.Desc.ProofFile.Honest.K11.Plays.Script
import Johnson.Desc.ProofFile.Honest.K11.Plays.OpenAt346

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open VerifiableInference.Desc.K13.Law (matOfCells matOfCells_low lowBits)
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull colBitsAtFull)
open ProofFile.Honest.FirstThread (lettersHead head_valid)

/-- The kind's layout has the matrix's bits for a column and its rows, under the head. -/
theorem layAtHead {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    (_root_.K11.parOf Zp Bs.G₀).lay.lk = h.𝔇.P13.lin.kCol ∧
      (_root_.K11.parOf Zp Bs.G₀).lay.m0 = OnBytes.Flat.numsFull.rows := by
  obtain ⟨Bs', _, _, hB', _, _, h3, _, _, _⟩ := headMergeAtFull Z D r Zp Np cF x h
  obtain rfl : Bs = Bs' := Except.ok.inj (hB.symm.trans hB')
  obtain ⟨e1, e2⟩ := colBitsAtFull Z D r Zp Np cF x h Bs hB
    (LT28.K11Tests.numsB_head_of_public h.scope h.reads h.laid.pub h.pubOne
      (Nat.pow_right_injective (le_refl 2) (h.cols13.trans (by decide +kernel))))
  exact ⟨e1, by rw [e2, h3]⟩

/-- **The kind's premise on the Script in its first form, from the second, at the head's thread.**
-/
theorem scriptAtHead : ScriptAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs
    weights coins hB hM hQ
  obtain ⟨hk, hm0⟩ := layAtHead h hB
  refine ⟨hM.maskTie, hM.indexTie, ?_⟩
  intro blk k s m E ds y cols s' hT hS _ ds' i C hC
  obtain ⟨⟨⟨l, _, hy⟩, _⟩, _⟩ := hS
  have hin := (play_mid _ _ _ _ _ hy).1
  have hV : Vd m.st.input :=
    ((head_valid h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w m.st.input).1 hT.1.2.2.2.2.2.2).2
  have hC' : C < 2 ^ h.𝔇.P13.lin.kCol := hC
  show matOfCells OnBytes.Flat.numsFull.rows h.𝔇.P13.lin.kCol (Q.cells y.2.st.input) i
    (lowBits h.𝔇.P13.lin.kCol C) = _
  rw [matOfCells_low _ _ _ i C hC', hin]
  exact hQ.entries m.st.input hV i C (by rw [hm0]; exact i.isLt) (by rw [hk]; exact hC')

/-- **The field ties at the head's thread, from four facts on the Script.** -/
theorem tiesAtHead : TiesAtHead := by
  intro Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Bs
    weights coins hB hM hQ
  have hS := scriptAtHead Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd Rd
    Kp w Bs weights coins hB hM hQ
  have hm : (_root_.K11.parOf Zp Bs.G₀).lay.m0 ≤ OnBytes.Flat.numsFull.rows :=
    le_of_eq (layAtHead h hB).2
  have hC := claimTrue_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀
    Vd Rd Kp w Bs weights hB
    (weightsOpen_at_head Z D r Zp Np cF x h Bk W₀ Rc Ky Tr X₀ X H Q test carryX item n₁ n₂ b₀ Vd
      Rd Kp w)
    hQ.inRange hQ.entries
  intro blk k s m E ds y cols s' a claim x0 b9 a9 hT hSt hblk ha hcl hx hb9 ha9 ds'
  exact tiesOfScript _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hS hm hC blk k s m E ds y cols
    s' a claim x0 b9 a9 hT hSt hblk ha hcl hx hb9 ha9 ds'

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.layAtHead
#print axioms ProofFile.Honest.K11.scriptAtHead
#print axioms ProofFile.Honest.K11.tiesAtHead
