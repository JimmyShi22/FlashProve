-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/HalfAtAnyFillStatement.lean: "THE PROVER's HALF AT THE
MERGE's PLACE IS THE KIND's", AT THE PROVER THAT THE FRAME's MAKER `onlineProverFromPublicFiles` BUILDS AT ANY
FILLING, FROM TWO PREMISES ON THE FILLING's LIST OF LOTS IN THE FORM THAT A WRAPPED LOT CAN MEET:
STATEMENTS ALONE: three definitions of propositions. NOTHING IS PROVED IN THIS FILE, and none is one
of the library's goals: they are lemmas' statements.

Why. In a filling whose reader of the index depends on the public part a kind's lot, at one reader,
is no member of the list of lots: a wrapped lot is, whose halves at a public part are those of the
kind's lot at the reader of that public part. So the premises speak of halves, not of lots.

  `FindOfLots`         on lists and places alone: some lot of the list has L's halves · every lot of
                       the list has halves at places of other kinds than p's alone, or has L's
                       halves · the search by p in L's halves finds g: then the search by p in the
                       list of halves lot by lot finds g
  `HalfAtAnyFill`      general in the size: the maker returns A at a filling P · some lot of P.lots
                       has, at A.Z and A.G, the halves of `headMergeLot claims weights` · every lot
                       of P.lots has there halves at places of other kinds than K11 alone, or these
                       halves: then the search by the kind's place in A.H.first finds
                       `headMergeHalf (claims A.Z A.G) weights (K11.parOf A.Z A.G)`
  `HalfAtAnyFillHead`  under the library's head, at the maker's base, at the head's own three files:
                       A.Z = Zp · A.G = Bs.G₀ · the search by `IM.k11Place` in A.H.first finds
                       `headMergeHalf (claims Zp Bs.G₀) weights (K11.parOf Zp Bs.G₀)`: the premise
                       on the prover of `PlaysAtHead` and `AcceptedSAtHead` at H := A.H and claims
                       := claims Zp Bs.G₀

NEAR LEMMAS OF THE FRAME's AUTHORS, NOT IMPORTED HERE. `firstOf_find_kind`
(Honest/FirstFindKind.lean) has the second and third premises of `FindOfLots` and its end, with "L ∈
ls" for the first: `FindOfLots` follows from it in one call, at L := the lot that has L's halves.
`atPure_first_find_kind` (the same file) is the like for `HalfAtAnyFill`. The first two statements
here are near twins of these; the third is not.

Limits. THE TWO PREMISES ON THE LIST ARE SHOWN HERE OF NO FILLING. THAT `onlineProverFromPublicFiles` RETURNS IS A
PREMISE. claims and weights are letters. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.HalfAtFillStatement
import Johnson.P5J.MgAtAll
import Johnson.IMR.K11Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Chain Place KindName)

/-- The statement on lists and places. Not proved here; a lemma's statement, none of the library's
goals. -/
def FindOfLots : Prop :=
  ∀ (V W X : Type) (Z : Pub) (G : Ground) (ls : List (HLot V W X)) (L : HLot V W X) (p : Place)
    (g : Placed V W X),
    (∃ M ∈ ls, M.halves Z G = L.halves Z G) →
    (∀ M ∈ ls, (∀ x ∈ M.halves Z G, x.place.kind ≠ p.kind) ∨ M.halves Z G = L.halves Z G) →
    ((L.halves Z G).find? fun x => x.place == p) = some g →
    ((firstOf Z G ls).find? fun x => x.place == p) = some g

/-- The statement at the maker's prover. Not proved here; a lemma's statement, none of the library's
goals. -/
def HalfAtAnyFill : Prop :=
  ∀ (W₀ Rc Tr X₀ X : Type) (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (P : OnlineProverParts W₀ Rc Tr X₀ X)
    (A : OnlineProverWithDescription W₀ Rc Tr X₀ X)
    (claims : Pub → Ground → Inst → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights),
    onlineProverFromPublicFiles o pol lay KL P = .ok A →
    (∃ M ∈ P.lots, M.halves A.Z A.G = (headMergeLot claims weights).halves A.Z A.G) →
    (∀ M ∈ P.lots, (∀ x ∈ M.halves A.Z A.G, x.place.kind ≠ KindName.K11) ∨
      M.halves A.Z A.G = (headMergeLot claims weights).halves A.Z A.G) →
    (A.H.first.find? fun g => g.place == headMergePlace (_root_.K11.parOf A.Z A.G)) =
      some (headMergeHalf (claims A.Z A.G) weights (_root_.K11.parOf A.Z A.G))

/-- The statement under the head. Not proved here; a lemma's statement, none of the library's goals.
-/
def HalfAtAnyFillHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (_ : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (W₀ Rc Tr X₀ X : Type)
    (P : OnlineProverParts W₀ Rc Tr X₀ X) (A : OnlineProverWithDescription W₀ Rc Tr X₀ X) (Bs : ProofFile.PureBase)
    (claims : Pub → Ground → Inst → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights),
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A →
    (∃ M ∈ P.lots, M.halves A.Z A.G = (headMergeLot claims weights).halves A.Z A.G) →
    (∀ M ∈ P.lots, (∀ x ∈ M.halves A.Z A.G, x.place.kind ≠ KindName.K11) ∨
      M.halves A.Z A.G = (headMergeLot claims weights).halves A.Z A.G) →
    A.Z = Zp ∧ A.G = Bs.G₀ ∧
      (A.H.first.find? fun g => g.place == IM.k11Place) =
        some (headMergeHalf (claims Zp Bs.G₀) weights (_root_.K11.parOf Zp Bs.G₀))

end ProofFile.Honest.K11
