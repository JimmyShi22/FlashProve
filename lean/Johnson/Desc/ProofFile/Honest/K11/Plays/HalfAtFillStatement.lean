-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/HalfAtFillStatement.lean: THAT THE HONEST PROVER WHICH THE
FRAME's AUTHORS' MAKER BUILDS AT THEIR TWO FILLINGS HAS, AT THE PLACE OF THE MERGE OF THE CLAIMS ON
THE WEIGHTS (K11), THE KIND's OWN HALF: STATEMENTS ALONE: five definitions of propositions. NOTHING
IS PROVED IN THIS FILE, and none is one of the library's goals: they are lemmas' statements.

  `HalfAtNow`     at every public part and ground: in the list of halves that `firstOf` makes of
                  `(nowFill O).lots` (Honest/AtPureSixKinds.lean) the search by the kind's place finds
                  `headMergeHalf (O.claims Z G) id (K11.parOf Z G)`
  `HalfAtWider`   the like at `(widerFill o S O).lots` (Honest/AtPureWider.lean)
  `AtPureOpens`   where the maker `onlineProverFromPublicFiles` (Honest/AtPure.lean) returns A at a filling P: A.Z is
                  what `pubPlain` returns at the files · A.G is the blank ground of A.Z · the
                  prover's first list of halves is `firstOf A.Z A.G P.lots`
  `HalfAtPure`    so: where `onlineProverFromPublicFiles` returns A at `widerFill o S O`: the search in `A.H.first` finds
                  the kind's half at A's own public part and ground
  `HalfAtPureNow` the like where it returns A at `nowFill O`

Limits. GENERAL IN THE SIZE: no head, no number of a size. THE GROUND IS THE MAKER's (the blank
ground of the public part): THAT IT IS THE GROUND AT WHICH A LAW UNDER THE LIBRARY's HEAD READS THE
KIND's NUMBERS IS NOT SAID HERE. claims STAYS THE FILLING's OPEN FUNCTION `O.claims`. THAT `onlineProverFromPublicFiles`
RETURNS AT ANY FILES IS NOT SAID. The two lists of lots are the frame's authors' texts: if a list
turns, these lemmas ride again. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.AtPureWider

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11

/-- The statement at the first filling. Not proved here; a lemma's statement, none of the library's
goals. -/
def HalfAtNow : Prop :=
  ∀ (O : OnlineProverArguments) (Z : Pub) (G : Ground),
    ((firstOf Z G (nowFill O).lots).find? fun g =>
      g.place == headMergePlace (_root_.K11.parOf Z G)) =
      some (headMergeHalf (O.claims Z G) id (_root_.K11.parOf Z G))

/-- The statement at the wider filling. Not proved here; a lemma's statement, none of the library's
goals. -/
def HalfAtWider : Prop :=
  ∀ (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Z : Pub) (G : Ground),
    ((firstOf Z G (widerFill o S O).lots).find? fun g =>
      g.place == headMergePlace (_root_.K11.parOf Z G)) =
      some (headMergeHalf (O.claims Z G) id (_root_.K11.parOf Z G))

/-- The statement on the maker. Not proved here; a lemma's statement, none of the library's goals.
-/
def AtPureOpens : Prop :=
  ∀ (W₀ Rc Tr X₀ X : Type) (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (P : OnlineProverParts W₀ Rc Tr X₀ X)
    (A : OnlineProverWithDescription W₀ Rc Tr X₀ X), onlineProverFromPublicFiles o pol lay KL P = .ok A →
    pubPlain o pol lay KL = .ok A.Z ∧ blankBy pureRoad.links A.Z = some A.G ∧
      A.H.first = firstOf A.Z A.G P.lots

/-- The statement at the prover that the maker builds. Not proved here; a lemma's statement, none of
the library's goals. -/
def HalfAtPure : Prop :=
  ∀ (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (A : OnlineProverWithDescription Weights IndexCommitterCoins Cells Unit Unit),
    onlineProverFromPublicFiles o pol lay KL (widerFill o S O) = .ok A →
    (A.H.first.find? fun g => g.place == headMergePlace (_root_.K11.parOf A.Z A.G)) =
      some (headMergeHalf (O.claims A.Z A.G) id (_root_.K11.parOf A.Z A.G))

/-- The like at the first filling. Not proved here; a lemma's statement, none of the library's
goals. -/
def HalfAtPureNow : Prop :=
  ∀ (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (O : OnlineProverArguments)
    (A : OnlineProverWithDescription Weights IndexCommitterCoins Cells Unit Unit),
    onlineProverFromPublicFiles o pol lay KL (nowFill O) = .ok A →
    (A.H.first.find? fun g => g.place == headMergePlace (_root_.K11.parOf A.Z A.G)) =
      some (headMergeHalf (O.claims A.Z A.G) id (_root_.K11.parOf A.Z A.G))

end ProofFile.Honest.K11
