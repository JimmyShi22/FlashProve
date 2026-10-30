-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Second/Seam/ToldFitWritten.lean: toldFitB (SeatOfTold.lean) ACCEPTS AT THE TYPED VALUES: the closed fact to which SeatFits at the shared chain's two sendings was brought down (the ledger's premises hFU · hFO · hSh2 · hSh5), DECIDED BY LEAN's KERNEL at the closed terms: realSized (Johnson/Desc/K1/Law/CondReal.lean) and codesFull2 (Johnson/G/PackLit.lean). The sentence ToldFitOwed (Johnson/Desc/K14/Law/LedgerToldFitOwed.lean), in its own letters: that file is not imported; the sentence here is its text over the library's names, by reading.
  toldAt x            toldFitB codesFull2 x.shape ‹layU› ‹layO›, the two layouts read through getD as in that sentence.
  toldFit_any         (realSized.any fun p => toldAt p.1) = true: by the kernel. «any» is false at none: so it says besides that realSized returns.
  threeSome_any       THE THREE Options THAT toldAt READS THROUGH getD ARE THERE: (withU x.shape).isSome · both (layTrees …).isSome; and the codes that realSized returns are codesFull2; and three trees are told: by the kernel.
  toldFit_not         THREE NEGATIVE TWINS, each = false, by the kernel: o_omega's shape asked with a row more · o_omega's and o_sp's places one tree further · o_u asked at no codes: each turns what is ASKED and leaves what is TOLD.
  toldFit_written   ∀ x, realSized = some (x, codesFull2) → toldAt x = true: ToldFitOwed's sentence.
  seatFits_written  so, with seatFits_of_told: at every x that realSized returns, every P with P.codes = codesFull2 and P.S = x.shape, every G with hlo and hG: SeatFits at sendingU and sendingO, at every radius, at these two layouts. NO TEST IS LEFT AS A PREMISE.
Limits. What toldFitB's yes is worth: SeatOfTold.lean's head: it holds what K14's two sending sub-protocols tell against the very shape and codes from which they tell it; it binds neither to anything outside. That a seat's P has these codes and this shape is other files' to show («Written Z x»). hlo · hG stay premises. The full size; the proof file. No soundness is claimed.

-/
import Johnson.Second.Seam.SeatOfTold
import Johnson.Desc.K1.Law.CondReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Second.Seam
open OnBytes OnBytes.Params Johnson.G
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K1 (realSized)
open _root_.Desc.K14 (withU withOmega)
open Desc.K14.Law.Fence (sendingU sendingO)

/-- o_u's sending's layout of trees at the typed codes, read as the sentence ToldFitOwed reads it. -/
def layUAt (x : LinSized) : TreeLay := (layTrees codesFull2 ((withU x.shape).getD #[])).getD default
/-- o_omega's. -/
def layOAt (x : LinSized) : TreeLay := (layTrees codesFull2 (withOmega x.shape)).getD default

def toldAt (x : LinSized) : Bool := toldFitB codesFull2 x.shape (layUAt x) (layOAt x)

theorem toldFit_any : (realSized.any fun p => toldAt p.1) = true := by decide +kernel

theorem threeSome_any : (realSized.any fun p =>
    (withU p.1.shape).isSome && (layTrees codesFull2 ((withU p.1.shape).getD #[])).isSome &&
      (layTrees codesFull2 (withOmega p.1.shape)).isSome && decide (p.2 = codesFull2) &&
      decide ((toldOf codesFull2 p.1.shape).length = 3)) = true := by decide +kernel

theorem toldFit_not :
    (realSized.any fun p => fitAt (toldOf codesFull2 p.1.shape) codesFull2
      { p.1.shape.omega with mainRows := p.1.shape.omega.mainRows + 1 }
      ((layUAt p.1).shapes.size + (layOAt p.1).tree.getD 0 0) ((layOAt p.1).part.getD 0 0)) = false ∧
    (realSized.any fun p => toldFitB codesFull2 p.1.shape
      { layUAt p.1 with shapes := (layUAt p.1).shapes.push {} } (layOAt p.1)) = false ∧
    (realSized.any fun p => fitAt (toldOf codesFull2 p.1.shape) {} p.1.shape.fold.u
      ((layUAt p.1).tree.getD 0 0) ((layUAt p.1).part.getD 0 0)) = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel


theorem toldFit_written (x : LinSized) (h : realSized = some (x, codesFull2)) : toldAt x = true := by
  have t := toldFit_any
  rw [h] at t
  exact t

/-- No test is left as a premise. -/
theorem seatFits_written {Xi : Type} (G : FileDescription Xi) (P : _root_.Desc.K14.P14) (x : LinSized)
    (hx : realSized = some (x, codesFull2)) (hc : P.codes = codesFull2) (hS : P.S = x.shape)
    (t₁ : ℕ) (c : Model.Verify.Chains) (tests : List (Block _root_.Desc.K14.St Unit))
    (last : List (Block _root_.Desc.K14.St Unit) → Block _root_.Desc.K14.St Unit)
    (hlo : (oraclesOf G.first.blocksInOrder).length = t₁)
    (hG : oraclesOf G.shared.blocksInOrder = oraclesOf (_root_.Desc.K14.chainOf c P tests last).blocksInOrder)
    (rU rO rSp : ℕ) :
    SeatFits G P.codes (sendingU P.S rU t₁ (layUAt x) (layOAt x)).l
        (sendingU P.S rU t₁ (layUAt x) (layOAt x)).seat ∧
      SeatFits G P.codes (sendingO P.S rO rSp t₁ (layUAt x) (layOAt x)).l
        (sendingO P.S rO rSp t₁ (layUAt x) (layOAt x)).seat := by
  have s := threeSome_any
  rw [hx] at s
  have s1 : (withU x.shape).isSome = true := by
    simp only [Option.any_some, Bool.and_eq_true] at s
    exact s.1.1.1.1
  obtain ⟨sentU, hU⟩ := Option.isSome_iff_exists.1 s1
  have hB : toldFitB P.codes P.S (layUAt x) (layOAt x) = true := by
    rw [hc, hS]
    exact toldFit_written x hx
  exact seatFits_of_told G P t₁ (layUAt x) (layOAt x) c tests last (hS ▸ hU) hlo hG hB rU rO rSp

end Second.Seam

#print axioms Second.Seam.toldFit_any
#print axioms Second.Seam.threeSome_any
#print axioms Second.Seam.toldFit_not
#print axioms Second.Seam.toldFit_written
#print axioms Second.Seam.seatFits_written
