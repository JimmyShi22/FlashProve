-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerFormsAll.lean: ALL THE FORMS THAT THE LEDGER OF THE SHARED CHAIN ASKS OF
A ROW OF TWELVE PIECES, OUT OF ONE EQUATION AND THE TILING. The ledger's tops (share_seamed,
ledger_all, ledger_at_cap) bear twenty-six binders on the pieces' forms: eight blocks as letters
(c2 … c8, c11), seven "decides as", six equations on rounds, four "holds in the wrap", "exact" at
the end, and two "is a lifted block" at the proximity tests. HERE: at any row of twelve pieces that
holds the blocks of the shared chain (chainOf c Q tests last).retype as a description's pieces do
(hps), WITH tests A FREE LIST, and that is tiled from its front piece (ht), all but "exact" are had
by proof, at c_k := b_k.retype and c11 := bareOf (last …).retype.

  tests_two        the equation's two lengths: tests is a list of just two.
  row_forms_all    **the forms**: tests = [t9, t10]; row_forms' nine conjuncts
                   (Johnson/Desc/K14/Law/LedgerForms.lean); the two proximity tests' pieces hold
                   lifted blocks; the seven blocks carried decide as the kind's and declare its
                   rounds.
"Exact" at the end: last_exact (LedgerForms.lean), where last is the proximity test's files' own
last block: it is called beside this lemma, not in it: here last is a letter.
What is not claimed. That a file's description has that chain as its shared chain. Nothing on the
rounds' data, on the piece at "LIN point" or on the front piece. It pays no law: it strikes binders.
No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.LedgerForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block Strs Wit FileDescription)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

variable {P₁ Cl Cells Tok : Type} {Fr : Frame}

/-- The chain, written out, where the kind's blocks can be said. -/
theorem chainOf_eq (c : Model.Verify.Chains) (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (tests : List (Block St Unit)) (last : List (Block St Unit) → Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    chainOf c Q tests last =
      { first := frontBlock c, front := [], links := []
        back := [b1, b2, b3, b4, b5, b6, b7, b8] ++ tests
        last := last ([b1, b2, b3, b4, b5, b6, b7, b8] ++ tests) } := by
  simp [chainOf, blocksOr, hbl]

/-- **The equation's two lengths: the tests are two.** -/
theorem tests_two (c : Model.Verify.Chains) (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (tests : List (Block St Unit)) (last : List (Block St Unit) → Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (f pt x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (hps : (f :: [pt, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11]).map (·.b) =
      (((chainOf c Q tests last).retype (Cl' := Cl)).blocksInOrder.map below).map
        (Block.lift Prod.snd fun t s => (t.1, s))) :
    ∃ t9 t10, tests = [t9, t10] := by
  rw [chainOf_eq c Q b1 b2 b3 b4 b5 b6 b7 b8 tests last hbl] at hps
  have hl := congrArg List.length hps
  simp [VerifiableInference.Desc.Chain.retype, VerifiableInference.Desc.Chain.blocksInOrder] at hl
  exact List.length_eq_two.1 (by omega)

/-- **All the forms, out of one equation and the tiling.** -/
theorem row_forms_all (c : Model.Verify.Chains) (Q : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (f pt x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
    (hps : (f :: [pt, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11]).map (·.b) =
      (((chainOf c Q tests last).retype (Cl' := Cl)).blocksInOrder.map below).map
        (Block.lift Prod.snd fun t s => (t.1, s)))
    (ht : Tiled f [pt, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11]) :
    ∃ t9 t10, tests = [t9, t10] ∧
      ((∃ d₁ d₂ ex er, x2 = pc2 b2.retype x2.base d₁ d₂ ex er) ∧ x3.b = heldW b3.retype ∧
        (∃ d ex er, x4 = pc1 b4.retype x4.base d ex er) ∧
        (∃ d₁ d₂ ex er, x5 = pc2 b5.retype x5.base d₁ d₂ ex er) ∧
        x6.b = heldW b6.retype ∧ (∃ d ex er, x7 = pc1 b7.retype x7.base d ex er) ∧
        x8.b = heldW b8.retype ∧
        x11.b = heldW (bareOf (last ([b1, b2, b3, b4, b5, b6, b7, b8] ++ [t9, t10])).retype) ∧
        Tiled x2 [x3, x4, x5, x6, x7, x8, x9, x10, x11]) ∧
      (∃ b₀ : Block St Cl, x9.b = b₀.lift Prod.snd fun t s => (t.1, s)) ∧
      (∃ b₀ : Block St Cl, x10.b = b₀.lift Prod.snd fun t s => (t.1, s)) ∧
      (∀ b : Block St Unit, DecidesAs (b.retype (Cl' := Cl)) b ∧
        (b.retype (Cl' := Cl)).rounds = b.rounds) := by
  obtain ⟨t9, t10, rfl⟩ := tests_two c Q b1 b2 b3 b4 b5 b6 b7 b8 tests last hbl f pt x2 x3 x4 x5 x6
    x7 x8 x9 x10 x11 hps
  refine ⟨t9, t10, rfl, row_forms c Q b1 b2 b3 b4 b5 b6 b7 b8 t9 t10 last hbl f pt x2 x3 x4 x5 x6 x7
    x8 x9 x10 x11 hps ht, ?_, ?_, fun b => ⟨retype_as b, rfl⟩⟩
  · rw [chainOf_eq c Q b1 b2 b3 b4 b5 b6 b7 b8 [t9, t10] last hbl] at hps
    exact ⟨_, Option.some.inj (congrArg (fun L => L[9]?) hps)⟩
  · rw [chainOf_eq c Q b1 b2 b3 b4 b5 b6 b7 b8 [t9, t10] last hbl] at hps
    exact ⟨_, Option.some.inj (congrArg (fun L => L[10]?) hps)⟩

end Desc.K14.Law

#print axioms Desc.K14.Law.chainOf_eq
#print axioms Desc.K14.Law.tests_two
#print axioms Desc.K14.Law.row_forms_all
