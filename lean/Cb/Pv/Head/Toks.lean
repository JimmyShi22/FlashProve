-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/Toks.lean: the three token sumchecks of the output head's sub-proof as three values of
one kind.

The verifier's routine hear (OnBytes/Model/HeadHeard.lean) runs them one behind the other: on the
row products of the final norm's ledger (hearProducts, behind a batch), on the stream times the
reciprocal (hearStream), and on the activations times the head's weights (hearLogits), which goes
on over the channels. Their slots follow each other, so all are computed here from the slot of the
first row product.

Main definitions: pairs7, kindTV, kindTV4, kindTN, kindTH, headToks, sizesTok, sizesBat.

What is not claimed. That the routine takes these slots. Cb/Pv/Head/TestToks.lean
compares them with the written list of Cb/Pv/Head/Sizes.lean; the head of that
file says what ties its list to the verifier's planner. No theorem is stated here.


-/
import Cb.Pv.Head.Tok

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head.Tok

/-- The seven row products with five limbs, among the four end values 0 = a, 1 = b, 2 = Rlo,
3 = Rhi, in the order of their weights (ledProducts5, OnBytes/Model/Ledger.lean). -/
def pairs7 : List (Fin 4 × Fin 4) := [(0, 0), (0, 1), (1, 1), (2, 0), (2, 1), (3, 0), (3, 1)]

/-- The sumcheck of the row products, with five limbs. sPv: the slot of the first product. -/
@[reducible] def kindTV (lt sPv : ℕ) : TokKind := ⟨lt, 0, 4, pairs7, sPv + 7⟩

/-- The same with four limbs: three products among 0 = sigma, 1 = Rlo, 2 = Rhi (productsShown,
OnBytes/Model/HeadHeard.lean). -/
@[reducible] def kindTV4 (lt sPv : ℕ) : TokKind := ⟨lt, 0, 3, [(0, 0), (1, 0), (2, 0)], sPv + 3⟩

/-- The sumcheck of the stream times the reciprocal: one product of the two end values. -/
@[reducible] def kindTN (lt sCl : ℕ) : TokKind := ⟨lt, 0, 2, [(0, 1)], sCl⟩

/-- The sumcheck of the activations times the head's weights: one product; lPd further rounds. -/
@[reducible] def kindTH (lt lPd sCl : ℕ) : TokKind := ⟨lt, lPd, 2, [(0, 1)], sCl⟩

/-- The head's three, with five limbs, from the slot of the first row product. -/
def headToks (lt lPd sPv : ℕ) : List TokKind :=
  let v := kindTV lt sPv
  let n := kindTN lt (v.sCl + v.slots)
  [v, n, kindTH lt lPd (n.sCl + n.slots)]

/-- The written list of the kinds, at two example configurations: 64 positions and width 512;
1,024 positions and width 5,120. 1575 and 2055 are the slots of the first row product there
(Cb/Pv/Head/Sizes.lean; Cb/Pv/Head/TestToks.lean compares). Length 6. -/
def sizesTok : List TokKind := headToks 6 9 1575 ++ headToks 10 13 2055

/-- The written list of the numbers of scalars that a batch of the head's norm takes: the sums of
limb products, the row products. -/
def sizesBat : List ℕ := [9, 7]

end Cb.Pv.Head.Tok
