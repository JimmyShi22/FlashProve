-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/TiesAtSeat.lean: no soundness is claimed.
The two ties between the last chain's test on taken sources (takenSources, Johnson/Desc/Third/TakenSources.lean) and the proximity test's own record and rounds, on which firstOpens_at_last (Johnson/Desc/K12/Coin/FirstOpensAtLast.lean) leans. Here both types lie in one build.
  pairAt' | tkOf'      copies, sign for sign, of pairAt | tkOf of Johnson/Desc/K12/Coin/FirstOpensSets.lean (TiesOne.lean says by Lean that the copies are the originals)
  **takenOf_eq**       enterOwn s = .ok t → takenOf s = tkOf' t s.loc.omega: the first tie
  rounds_onOwn         (onOwn b).rounds = b.rounds := rfl
  **seat_second**      laterSecond Z = some B → ∃ N, placesOfMade Z.made = .ok N ∧ the chain's flat list is, in order: K14's second part · takenSources own · own at place 2 · the end, all at one own := onOwn (proximityTestKind guardedProximityTestParts (proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W)), up to the flat list's «bare» on planOk: the second tie: the block whose rounds the test reads is the block that stands behind it, at one π
  **rounds_at_seat**   so the rounds that the test reads are (proximityTestKind guardedProximityTestParts π).rounds at that π
Who reads each letter. ∃ N: fixed by its equation.
Does not show. That tkOf' is tkOf: that is TiesOne.lean's. Nothing on this: that a tree's number in the book is its place in its chain's order of sending. Nothing on soundness.
-/
import Johnson.ToldDescR.LastPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open ProofFile
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Seat (onOwn enterOwn)
open VerifiableInference.Desc.Third (S₃ P₁₄ takenOf takenSources lastChainWithOwnTest batchLinearConstraintsSecondPart end₃)

/-- A copy of `pairAt`. -/
def pairAt' (B : TreeBook) (ω i : ℕ) : Option (ℕ × ℕ) :=
  ((B.place[i]?).bind fun q => B.trees[q.1]?).map fun T => (if i == ω then 1 else 0, T.number)

/-- A copy of `tkOf`. -/
def tkOf' (t : T12) (ω : ℕ) : Option (List (ℕ × ℕ)) :=
  (t.st.groups[t.g]?).bind fun G => (G.members.toList ++ t.mask.toList).mapM (pairAt' t.book ω)

/-- **The first tie**: the list that the test on taken sources reads off the last chain's record is
the list said at the record that the seat makes of it. -/
theorem takenOf_eq (s : S₃) (t : T12) (h : enterOwn s = .ok t) :
    takenOf s = tkOf' t s.loc.omega := by
  have e : t = { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing
                 mask := s.loc.mask } := (Except.ok.inj h).symm
  subst e
  rfl

theorem rounds_onOwn {Cl : Type} (b : Block T12 Cl) : (onOwn b).rounds = b.rounds := rfl

/-- The last chain's flat list's rounds-bearing blocks, at every argument: the block whose rounds the
test reads is the block laid behind it. -/
theorem flat_tiedEnd_rounds {Cl : Type} (p : P₁₄) (own : Block S₃ Cl) :
    (lastChainWithOwnTest p own).blocksInOrder.map (·.rounds) =
      [(batchLinearConstraintsSecondPart p : Block S₃ Cl).rounds, (takenSources own).rounds, own.rounds,
        (end₃ [batchLinearConstraintsSecondPart p, takenSources own, VerifiableInference.Desc.Third.ownAt own]).rounds] :=
  rfl

/-- **The second tie.** -/
theorem seat_second {Z : ProofFile.Pub} {B : SecondSeat} (h : laterSecond Z = some B) :
    ∃ N : H2U.Places4, H2U.placesOfMade Z.made = .ok N ∧
      ∃ (e : B.σ = S₃) (p : P₁₄),
        (e ▸ B.chain : Chain S₃ Unit) =
          lastChainWithOwnTest p (onOwn (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W))) := by
  unfold laterSecond P2Third.secondSeat at h
  cases hN : H2U.placesOfMade Z.made with
  | error e =>
    rw [hN] at h
    exact nomatch h
  | ok N =>
    rw [hN] at h
    have e := Option.some.inj h
    subst e
    exact ⟨N, rfl, rfl, _, rfl⟩

/-- **The rounds that the test on taken sources reads are the proximity test's own, at one π.** -/
theorem rounds_at_seat (N : H2U.Places4) :
    (onOwn (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Unit)).rounds =
      (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Unit).rounds := rfl

end ToldDesc

#print axioms ToldDesc.takenOf_eq
#print axioms ToldDesc.flat_tiedEnd_rounds
#print axioms ToldDesc.seat_second
#print axioms ToldDesc.rounds_at_seat
