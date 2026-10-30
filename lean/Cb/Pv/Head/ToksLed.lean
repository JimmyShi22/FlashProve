-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/ToksLed.lean: the tables of the sumcheck of the row products, in the letters of the
final norm's ledger.

The four maps of that sumcheck extend, over the positions, the four row values sa, sb, Rlo, Rhi of
the ledger (Inst/Model/Common/LedgerForms.lean), each a function of the digits of a position's row.
dig m n i is digit number n of the row at position i, read in the entries m.

worldTV: the entries and tables. trueP_prods: the true product number j of the sumcheck
(Cb/Pv/Head/BatTok.lean) is the extension of the ledger's product number j.

What is not claimed. Which entries dig reads. Nothing on hiding.


-/
import Cb.Pv.Head.BatTok
import Cb.Pv.Head.Toks
import Inst.Model.Common.LedgerForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head.Tok
open Finset Inst.Model

section
variable {E : Type} [Field E]

/-- The four row values at a position, by number: sa, sb, Rlo, Rhi. -/
def rowVal (D : ℕ → E) (a : ℕ) : E :=
  match a with
  | 0 => Ledger.sa D
  | 1 => Ledger.sb D
  | 2 => Ledger.Rlo D
  | _ => Ledger.Rhi D

/-- The entries and tables of the sumcheck of the row products. Pb: whatever is public; the tables
do not read it. -/
@[reducible] def worldTV (lt sPv : ℕ) (Pb J : Type) [Fintype J] [DecidableEq J] (msk : ℕ → J)
    (dig : (J → E) → ℕ → ℕ → E) : TokWorld E (kindTV lt sPv) where
  Pb := Pb
  J := J
  msk := msk
  tab := fun _ m a i => rowVal (fun n => dig m n i) a

/-- A product of two of the four row values, by the list of pairs, is the ledger's product. -/
theorem pair_prods (D : ℕ → E) : ∀ j : Fin 7,
    rowVal D ((pairs7.get j).1 : ℕ) * rowVal D ((pairs7.get j).2 : ℕ) = Ledger.prods D j := by
  intro j
  fin_cases j
  · exact (pow_two _).symm
  · rfl
  · exact (pow_two _).symm
  · rfl
  · rfl
  · rfl
  · rfl

/-- The true product number j is the extension of the ledger's product number j. -/
theorem trueP_prods (lt sPv : ℕ) (Pb J : Type) [Fintype J] [DecidableEq J] (msk : ℕ → J)
    (dig : (J → E) → ℕ → ℕ → E) (st : TokSt E Pb (kindTV lt sPv)) (m : J → E) (j : Fin 7) :
    trueP (kindTV lt sPv) (worldTV lt sPv Pb J msk dig) st m j =
      Blocks.ext (lt + 0) (fun i => Ledger.prods (fun n => dig m n i) j) (Blocks.nat st.pt) :=
  congrArg (fun f => Blocks.ext (lt + 0) f (Blocks.nat st.pt))
    (funext fun i => pair_prods (fun n => dig m n i) j)

end

end Cb.Pv.Head.Tok

#print axioms Cb.Pv.Head.Tok.pair_prods
#print axioms Cb.Pv.Head.Tok.trueP_prods
