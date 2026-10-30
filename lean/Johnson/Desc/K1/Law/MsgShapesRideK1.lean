-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/MsgShapesRideK1.lean: the public item "K12.msgShapes" (K12.Door.msgShapesB,
MsgShapes.lean: "the statement's messages' shapes are the first of M") IS EARNED ANEW BY A SENDING
OF KIND K1, where the plan's list M goes on with the shapes of the place's notices. One term, and
its calls at the kind's three blocks at the first chain's record.

  msgShapes_ride     the term: over any step that appends x to the list of shapes.
  msgShapes_stay     over any step that leaves the list.
  sendAtS_msgShapes, commitAtS_msgShapes, firstAtS_msgShapes   the blocks.
The appendings: Johnson/Desc/K1/Law/ShapesAtRecord.lean.
What is not claimed. That the plan's list goes on so at a block's place. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.ShapesAtRecord
import Johnson.Desc.K12.Door.MsgShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (shapesIn)
open VerifiableInference.Desc.K12.Door (msgShapesB)

variable {Cl : Type}

theorem shapesIn_length (st : Statement) : (shapesIn st).length = st.oracles.size := by
  unfold shapesIn
  rw [List.length_map, Array.length_toList]

/-- The Bool in plain words. -/
theorem msgShapesB_iff (M : List OracleShape) (st : Statement) : msgShapesB M st = true ↔
    shapesIn st = M.take (shapesIn st).length ∧ (shapesIn st).length ≤ M.length := by
  unfold msgShapesB
  rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, shapesIn_length]
  rfl

/-- **The term.** -/
theorem msgShapes_ride {M x : List OracleShape} {st st' : Statement}
    (h : msgShapesB M st = true) (e : shapesIn st' = shapesIn st ++ x)
    (hx : (M.drop st.oracles.size).take x.length = x) : msgShapesB M st' = true := by
  obtain ⟨h1, h2⟩ := (msgShapesB_iff M st).1 h
  rw [← shapesIn_length] at hx
  exact (msgShapesB_iff M st').2 (prefix_ride M _ _ x h1 h2 e hx)

/-- Over a step that leaves the list of shapes. -/
theorem msgShapes_stay {M : List OracleShape} {st st' : Statement}
    (h : msgShapesB M st = true) (e : shapesIn st' = shapesIn st) : msgShapesB M st' = true := by
  rw [msgShapesB_iff] at h ⊢
  rw [e]
  exact h

theorem sendAtS_msgShapes (P : Par) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (sendAtS P : Block S Cl).decide s [r₁, r₂] gs = .ok s') {M : List OracleShape}
    (h0 : msgShapesB M s.st = true)
    (hx : (M.drop s.st.oracles.size).take (shapesOf P).length = shapesOf P) :
    msgShapesB M s'.st = true :=
  msgShapes_ride h0 (sendAtS_shapesIn P s s' r₁ r₂ gs h) hx

theorem commitAtS_msgShapes (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s')
    {M : List OracleShape} (h0 : msgShapesB M s.st = true)
    (hx : (M.drop s.st.oracles.size).take (shapesOf P).length = shapesOf P) :
    msgShapesB M s'.st = true :=
  msgShapes_ride h0 (commitAtS_shapesIn P link moment arrays s s' r₁ r₂ gs h) hx

theorem firstAtS_msgShapes (q : Params.First) (gp : GPar) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s [r₁, r₂] gs = .ok s') {M : List OracleShape}
    (h0 : msgShapesB M s.st = true)
    (hx : (M.drop s.st.oracles.size).take (shapesOf (firstPar q gp)).length =
      shapesOf (firstPar q gp)) : msgShapesB M s'.st = true :=
  msgShapes_ride h0 (firstAtS_shapesIn q gp s s' r₁ r₂ gs h) hx

end VerifiableInference.Desc.K1
