-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5PairsRead.lean: kind K5: **WHAT THE PAIRS OF THE TWO TESTS ON THE PLAN READ OF THE CALLER's LIST**: three small rules over letters.

Main names:
  psOf_len: where the seat is a function of the member's number, psOf reads of the list its length alone.
  qsOf_shapes: qsOf reads of the list its shapes alone.
  calls_shapes: the shapes of the caller's list (sigListCalls, Johnson/Desc/First/Look/K3CallerAtt.lean) hang on the request's shape alone: on no radius and on no other field of what the planner sends. calls_len: so does its length.
  kept_shape: the kept messages likewise.
IS IT EMPTY HERE? Rules over letters.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05ReadMsgs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes
open VerifiableInference.Desc.First.Att.P (psOf qsOf)
open VerifiableInference.Desc.First.Look (Sent sigListCalls sigList keptAt messagesAt)

/-- Where the seat is a function of the number, the pairs (number, seat) read of the list its length alone. -/
theorem psOf_len (l l' : List (OracleShape × ℕ)) (σ : ℕ → ℕ × ℕ) (h : l.length = l'.length) (ks : List ℕ) :
    psOf l (fun j => σ j.1) ks = psOf l' (fun j => σ j.1) ks := by
  unfold psOf
  refine List.filterMap_congr fun k _ => ?_
  by_cases hk : k < l.length
  · rw [dif_pos hk, dif_pos (h ▸ hk)]
  · rw [dif_neg hk, dif_neg (h ▸ hk)]

/-- The pairs (number, shape) read of the list its shapes alone. -/
theorem qsOf_shapes (l l' : List (OracleShape × ℕ)) (h : l.map (·.1) = l'.map (·.1)) (ks : List ℕ) : qsOf l ks = qsOf l' ks := by
  unfold qsOf
  refine List.filterMap_congr fun k _ => ?_
  have e : (l[k]?).map (·.1) = (l'[k]?).map (·.1) := by
    rw [← List.getElem?_map, ← List.getElem?_map, h]
  have f : ∀ o : Option (OracleShape × ℕ), (o.map fun x => (k, x.1)) = (o.map (·.1)).map fun s => (k, s) := by
    intro o
    cases o <;> rfl
  rw [f, f, e]

/-- The kept messages hang on the request's shape alone. -/
theorem kept_shape {D D' : Sent} (h : D.shape = D'.shape) (i : ℕ) : keptAt D i = keptAt D' i := by
  unfold keptAt
  rw [h]

/-- **The shapes of the caller's list hang on the request's shape alone.** -/
theorem calls_shapes {D D' : Sent} (h : D.shape = D'.shape) (rad rad' : OracleShape → ℕ) (i : ℕ) :
    (sigListCalls D rad i).map (·.1) = (sigListCalls D' rad' i).map (·.1) := by
  unfold sigListCalls sigList messagesAt
  rw [kept_shape h, h]
  simp only [List.map_append, List.map_map, Function.comp_def]

/-- So does its length. -/
theorem calls_len {D D' : Sent} (h : D.shape = D'.shape) (rad rad' : OracleShape → ℕ) (i : ℕ) :
    (sigListCalls D rad i).length = (sigListCalls D' rad' i).length := by
  have e := congrArg List.length (calls_shapes h rad rad' i)
  rwa [List.length_map, List.length_map] at e

end H2K5.Door

#print axioms H2K5.Door.psOf_len
#print axioms H2K5.Door.qsOf_shapes
#print axioms H2K5.Door.kept_shape
#print axioms H2K5.Door.calls_shapes
#print axioms H2K5.Door.calls_len
