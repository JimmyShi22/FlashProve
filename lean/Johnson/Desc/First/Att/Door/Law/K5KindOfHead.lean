-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5KindOfHead.lean: kind K5: **THE KIND's SHARE IN THE FORM AtMgA.Kind (Johnson/P5J/RowsAtAll.lean) FROM THE HEAD, 36 BOOLS WITHOUT A LETTER, AND THE SENTENCE pads.** A joining: calls. It turns nothing of the condition (K5CondAt,
Door/Law/K5LeftOfCond.lean) or of the theorem k05_kind_of_cond (Door/Law/K05KindOfCond.lean).
Against Door/Law/K5KindOfTests.lean: the twelve tests oneC fall: oneC_at_head | one_of_head (Door/Law/K5OneOfHead.lean) give them from the head alone, over a closed fact that Lean's kernel has walked (one_written,
Door/Law/K5OneWritten.lean).
Compiled with the whole library.

(Where this and lean/THEOREM.md differ, the page holds.)
ONLY WHERE THE LIST OF Johnson/Desc/Laid/ProofAsks.lean HAS THE THIRTEEN TESTS OF ProofAsksFirstThirteenTests.lean AND THE HEAD OF Johnson/P5J/MgAtAll.lean HAS THE FIELDS opts · k3.

Main names:
  cells_of_tie: (∀ g < 12, tieWW g = true) → the premise cells of k05_kind_at_head₂ (Door/Law/K5AlongOfHead.lean), in its own text.
  **k05_kind_of_head₃**: the head · the three equations on 𝔏 · k5PlansB₂ = true · the twelve tieWW · pads → h.Kind 𝔏 .K5. Whoever proves pads from the head calls this.
  k05_kind_of_head₃C: the same with pads from the named test offC (AtMg.offC, HidBearsAtMg.lean).
IS IT EMPTY HERE? IMPLICATIONS. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/). NONE OF THE 36 BOOLS, NOR offC, IS SHOWN true IN LEAN. THE KIND's LAW IS NOT PROVED.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5KindOfTests
import Johnson.Desc.First.Att.Door.Law.K5OneOfHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Door
open OnBytes OnBytes.Flat OnBytes.Model OnBytes.Maker OnBytes.Slice KObj
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt)
open P5J (AtMg AtMgA F0T TS Free)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

/-- **The condition's part cells, from twelve Bools whose only letter is g.** -/
theorem cells_of_tie (hT : ∀ g, g < 12 → tieWW g = true) :
    ∀ g, g < 12 → ∀ (a : Attention.Plan) (x₁ : Look.Place), (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ → ∃ idx, K5CellsCond h a x₁ idx :=
  cells_of_one h hT fun _ hg => one_of_head h hg

variable (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
  (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁) (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
  (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
include q₁ q₂ q₃

/-- **THE KIND's SHARE, FROM THE HEAD, 36 BOOLS WITHOUT A LETTER, AND pads.** -/
theorem k05_kind_of_head₃ (hW : k5PlansB₂ = true) (hT : ∀ g, g < 12 → tieWW g = true) (pads : PadsAll h) : h.Kind 𝔏 KindName.K5 :=
  k05_kind_at_head₂ h 𝔏 q₁ q₂ q₃ hW pads (cells_of_tie h hT)

/-- The same with pads from the named test offC (Johnson/P5J/HidBearsAtMg.lean). -/
theorem k05_kind_of_head₃C (hW : k5PlansB₂ = true) (hT : ∀ g, g < 12 → tieWW g = true) (hC : h.toAtMg.offC = true) :
    h.Kind 𝔏 KindName.K5 :=
  k05_kind_of_head₃ h 𝔏 q₁ q₂ q₃ hW hT (pads_of_offC h hC)

end H2K5.Door

#print axioms H2K5.Door.cells_of_tie
#print axioms H2K5.Door.k05_kind_of_head₃
#print axioms H2K5.Door.k05_kind_of_head₃C
