-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Door/MsgShapesRide.lean: **the rule for the Bool "K12.msgShapes"**: when it rides
over a step. One definition, five theorems; no kind is named; no Mathlib. The six are taken over to
the letter from K1's files Johnson/Desc/K1/Law/ShapesAtRecord.lean and MsgShapesRideK1.lean, so that
whoever wants the rule need not import K1's law; those files keep their own copies.

  `shapesIn St`: the shapes of the statement's oracle messages, in their order. `shapesIn_length`.
  `prefix_ride`: on lists alone: a prefix of M that grows by just what M goes on with is a prefix.
  `msgShapesB_iff`: what the Bool (MsgShapes.lean) says, in these words.
  `msgShapes_ride`: the Bool's yes at st · the shapes of st' are those of st and x behind them · M
    goes on with x behind as many as st has messages ⇒ the Bool's yes at st'.
  `msgShapes_stay`: where the list of shapes stays, so does the Bool's yes.
Limits. Nothing on soundness.

-/
import Johnson.Desc.K12.Door.MsgShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Door
open OnBytes OnBytes.Params

def shapesIn (St : Statement) : List OracleShape := St.oracles.toList.map (·.shape)

theorem prefix_ride {α : Type} (M l l' x : List α) (h : l = M.take l.length)
    (hl : l.length ≤ M.length) (e : l' = l ++ x) (hx : (M.drop l.length).take x.length = x) :
    l' = M.take l'.length ∧ l'.length ≤ M.length := by
  subst e
  have hlen : x.length ≤ M.length - l.length := by
    have := congrArg List.length hx
    rw [List.length_take, List.length_drop] at this
    omega
  refine ⟨?_, by rw [List.length_append]; omega⟩
  rw [List.length_append, List.take_add, ← h, hx]

theorem shapesIn_length (st : Statement) : (shapesIn st).length = st.oracles.size := by
  unfold shapesIn
  rw [List.length_map, Array.length_toList]

theorem msgShapesB_iff (M : List OracleShape) (st : Statement) : msgShapesB M st = true ↔
    shapesIn st = M.take (shapesIn st).length ∧ (shapesIn st).length ≤ M.length := by
  unfold msgShapesB
  rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, shapesIn_length]
  rfl

theorem msgShapes_ride {M x : List OracleShape} {st st' : Statement}
    (h : msgShapesB M st = true) (e : shapesIn st' = shapesIn st ++ x)
    (hx : (M.drop st.oracles.size).take x.length = x) : msgShapesB M st' = true := by
  obtain ⟨h1, h2⟩ := (msgShapesB_iff M st).1 h
  rw [← shapesIn_length] at hx
  exact (msgShapesB_iff M st').2 (prefix_ride M _ _ x h1 h2 e hx)

theorem msgShapes_stay {M : List OracleShape} {st st' : Statement}
    (h : msgShapesB M st = true) (e : shapesIn st' = shapesIn st) : msgShapesB M st' = true := by
  rw [msgShapesB_iff] at h ⊢
  rw [e]
  exact h

end VerifiableInference.Desc.K12.Door

#print axioms VerifiableInference.Desc.K12.Door.msgShapesB_iff
#print axioms VerifiableInference.Desc.K12.Door.msgShapes_ride
#print axioms VerifiableInference.Desc.K12.Door.msgShapes_stay
