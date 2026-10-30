-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/StopIs.lean: the smallness test: what its part's second stop is.
At one drawn round the part stops with the second stop just where a combination of the input's cells
leaves its window, in both directions, and the stop reads of the input its trace alone: no index, no
randomness of a table, no coin. Of a filled half, at any reader of cells and any list of names.

  `smallPartAt`        the part as the half lays it
  `small_stop_iff`     **the part stops just where `leaves` finds a combination**
  `small_first_silent` it has no first stop
  `small_hid_of_trace`  **two inputs with one trace are one to the stop**

At the full size the list of names and the reader of cells are those of the prover's lot. Nothing here
bounds how often the stop fires; nothing here says that the cells are small. Nothing is claimed on
completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.Side

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open VerifiableInference.Desc.First.K8 (Par)
open VerifiableInference.Desc.First.K8.Honest (leaves)

variable {W₀ Rc Xi Tr X : Type}

/-- The part as the half lays it. -/
abbrev smallPartAt (cells : Tr → Cells) (P : Par × List (Nat × String × Nat)) :
    Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  (smallPart P.1).lift (askOfInput cells P.2) (askOfInput cells P.2) (fun _ => ()) fun x _ => x

/-- The half has this one part. -/
theorem smallHalf_parts (cells : Tr → Cells) (P : Par × List (Nat × String × Nat)) :
    (smallHalf (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells P).parts = [smallPartAt cells P] :=
  rfl

/-- **At one drawn round the part stops just where a combination leaves its window.** -/
theorem small_stop_iff (cells : Tr → Cells) (P : Par × List (Nat × String × Nat))
    (v : Local W₀ Rc Xi Tr) (loc : List Fmt.Drawn) (d : Fmt.Drawn) :
    (smallPartAt (X := X) cells P).stopAt (some v) loc [d] = some .hid ↔
      (leaves P.1 (cellsAtOf (cells v.trace) P.2) d.trits.toArray).isSome = true := by
  cases hl : leaves P.1 (cellsAtOf (cells v.trace) P.2) d.trits.toArray with
  | none =>
    simp [Part.stopAt, smallPartAt, Part.lift, smallPart, smallHid, askOfInput, hl,
      List.range_succ]
  | some x =>
    simp [Part.stopAt, smallPartAt, Part.lift, smallPart, smallHid, askOfInput, hl,
      List.range_succ]

/-- It has no first stop. -/
theorem small_first_silent (cells : Tr → Cells) (P : Par × List (Nat × String × Nat))
    (loc own : List Fmt.Drawn) : (smallPartAt (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells P).bad
      loc own = none :=
  rfl

/-- **Two inputs with one trace are one to the stop**: it reads no index, no randomness and no coin. -/
theorem small_hid_of_trace (cells : Tr → Cells) (P : Par × List (Nat × String × Nat))
    {v v' : Local W₀ Rc Xi Tr} (h : v.trace = v'.trace) (loc own : List Fmt.Drawn) :
    (smallPartAt (X := X) cells P).hid v loc own = (smallPartAt (X := X) cells P).hid v' loc own := by
  show smallHid P.1 (askOfInput cells P.2 v) loc own = smallHid P.1 (askOfInput cells P.2 v') loc own
  unfold askOfInput
  rw [h]

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.smallHalf_parts
#print axioms ProofFile.Honest.K8.small_stop_iff
#print axioms ProofFile.Honest.K8.small_first_silent
#print axioms ProofFile.Honest.K8.small_hid_of_trace
