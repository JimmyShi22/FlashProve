-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/PlanShapesOwed.lean: SEVEN STATEMENTS THAT ARE OWED FOR K14's LAW, AS
PROPOSITIONS BY def: NO PROOF HERE. The shared chain of the linear claim has two sendings (kind K1):
"o_u and the first mask" (piece 2: the messages withU S) and "o_omega and o_sp" (piece 5: the
messages withOmega S). K1's laws speak of a sending by its parameters (parK1, K14/Blocks.lean): how
many messages (shapesOf), the shape of message number k (shapeAt), whether it is sampled
(sampledAt). OWED: what these say at the two sendings, IN THE PLAN's OWN LETTERS (the fields of
LinShape).

  SizeUOwed        with masks sent ahead, o_u's sending has two messages
  SizeOmegaOwed    where the row (Fold) is split, o_omega's sending has two messages
  LengthsOwed      shapesOf has as many entries as the sending has messages, at both
  PlacesOwed       the places 0 (both sendings) and 1 (o_omega's, where split) are there
  ShapeUOwed       message 0 of o_u's sending has the plan's shape for G_u
  SampledIffOwed   sampledAt at the three messages is "the plan's shape has an answer"
  SampledOwed      under the shape's own conditions (LinShape.ok) the three are sampled
What is not claimed. That they hold.
(They are proved in Johnson/Desc/K14/Law/PlanShapes.lean: sizeU, sizeOmega, lengths, places,
shapeAtU, sampledIff, sampled.)
Nothing on soundness.

-/
import Johnson.Desc.K14.Blocks
import Johnson.Desc.K1.Law.Port6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params
open VerifiableInference.Desc.K1 (shapesOf shapeAt sampledAt)

/-- OWED: with masks sent ahead, two messages go out with o_u. -/
def SizeUOwed : Prop :=
  ∀ (S : LinShape) (sentU : Array OracleNotice), withU S = some sentU → S.masksAhead = true →
    sentU.size = 2

/-- OWED: where G_u and Omega differ in code, two messages go out with o_omega. -/
def SizeOmegaOwed : Prop :=
  ∀ S : LinShape, S.sharedSplitNeeded = true → (withOmega S).size = 2

/-- OWED: K1's list of shapes is as long as the sending, at both sendings. -/
def LengthsOwed : Prop :=
  ∀ (Q : P14) (sentU : Array OracleNotice),
    (shapesOf (parK1 Q 2 "o_u and the first mask" sentU)).length = sentU.size ∧
      (shapesOf (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S))).length =
        (withOmega Q.S).size

/-- OWED: the places that the law's callers name are there. -/
def PlacesOwed : Prop :=
  ∀ (Q : P14) (sentU : Array OracleNotice),
    (withU Q.S = some sentU →
      0 < (shapesOf (parK1 Q 2 "o_u and the first mask" sentU)).length) ∧
      0 < (shapesOf (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S))).length ∧
      (Q.S.sharedSplitNeeded = true →
        1 < (shapesOf (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S))).length)

/-- OWED: the first message of "send o_u" has the plan's shape for G_u. -/
def ShapeUOwed : Prop :=
  ∀ (Q : P14) (sentU : Array OracleNotice), withU Q.S = some sentU →
    ∀ h : 0 < (shapesOf (parK1 Q 2 "o_u and the first mask" sentU)).length,
      shapeAt (parK1 Q 2 "o_u and the first mask" sentU) ⟨0, h⟩ = Q.S.fold.u

/-- OWED: "sampled" at the three messages, in the plan's letters. -/
def SampledIffOwed : Prop :=
  ∀ (Q : P14) (sentU : Array OracleNotice),
    (withU Q.S = some sentU →
      ∀ h : 0 < (shapesOf (parK1 Q 2 "o_u and the first mask" sentU)).length,
        (sampledAt (parK1 Q 2 "o_u and the first mask" sentU) ⟨0, h⟩ ↔
          Q.S.fold.u.answers ≠ 0)) ∧
      (∀ h : 0 < (shapesOf (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S))).length,
        (sampledAt (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) ⟨0, h⟩ ↔
          Q.S.omega.answers ≠ 0)) ∧
      (∀ h : 1 < (shapesOf (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S))).length,
        (sampledAt (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) ⟨1, h⟩ ↔
          Q.S.sharedSplit.answers ≠ 0))

/-- OWED: under the shape's own conditions the three messages are sampled. -/
def SampledOwed : Prop :=
  ∀ (Q : P14) (sentU : Array OracleNotice), Q.S.ok = true →
    (withU Q.S = some sentU →
      ∀ h : 0 < (shapesOf (parK1 Q 2 "o_u and the first mask" sentU)).length,
        sampledAt (parK1 Q 2 "o_u and the first mask" sentU) ⟨0, h⟩) ∧
      (∀ h : 0 < (shapesOf (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S))).length,
        sampledAt (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) ⟨0, h⟩) ∧
      (∀ h : 1 < (shapesOf (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S))).length,
        sampledAt (parK1 Q 5 "o_omega and o_sp" (withOmega Q.S)) ⟨1, h⟩)

end Desc.K14.Law
