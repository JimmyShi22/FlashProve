-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/EndedOf.lean: THE RECORD BEHIND A MASKED SUMCHECK'S ROUNDS IS `Ended`: ONCE,
FOR ALL THE FLAT FUNCTIONS. This folder writes the record behind the variables' rounds ms and the
further variable's round y as `endP p ms y` (FlSpec.lean). The library's tie to the typed sumcheck
takes of a record the predicate `Ended` (OnBytes/Tie/Pv/Psc/Run/PscSeam.lean). One statement and its
proof.

  `endP_ended`: for the record with which the flat `pscBegin` starts (target T, first slot f,
    coefficient eps, claim mu + eps T, start form C, begun), all rounds ms and every further round y
    whose weight is `atZero (dY + 1)`, all weights held: `Ended` holds of `endP … ms y` at C, T, mu,
    eps, f, the rounds' weights, the rounds as the library's pairs, dY, and what y sent and drew.

NO NEW ARGUMENT: `endP_spec` (FlSpec.lean), `walk_length` (Heard.lean), `claimAfter_lib`,
`endP_flags` (LevelEnded.lean). `level_ended` and `tsc_ended` (beside this file) say the same of two
functions' returns, each by its own walk: they could be corollaries of this. On records alone: no
function's return, no tape. Whether anything here reaches a routine of the program `verify-on-bytes`
is for the walk by constants to say.
-/
import OnBytes.Desc.First.P1.LevelEnded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Road (Ended)

/-- **The record behind a masked sumcheck's rounds is `Ended`.** -/
theorem endP_ended (T mu eps : E) (f : Nat) (C : Aff) (ms : List Rnd) (y : Rnd) (dY : Nat)
    (hy : y.1 = OnBytes.Psc.Weight.atZero (dY + 1)) (hheld : ∀ m ∈ ms ++ [y], Held m.1) :
    Ended
      (endP { target := T, first := f, eps := eps, claim := addE mu (mulE eps T), start := C,
              started := true } ms y)
      C T mu eps f (ms.map (·.1)) (ms.map fun m => (m.2.1, m.2.2)) dY y.2.1 y.2.2 := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := endP_spec
    { target := T, first := f, eps := eps, claim := addE mu (mulE eps T), start := C,
      started := true } ms y
  obtain ⟨f1, f2, f3⟩ := endP_flags
    { target := T, first := f, eps := eps, claim := addE mu (mulE eps T), start := C,
      started := true } ms y
  have hv := e1.trans (List.nil_append _)
  have hr := e2.trans (List.nil_append _)
  have hv1 : (ms ++ [y]).map (·.1) = ms.map (·.1) ++ [OnBytes.Psc.Weight.atZero (dY + 1)] := by
    rw [List.map_append, List.map_cons, List.map_nil, hy]
  have hm2 : (ms.map fun m => (m.2.1, m.2.2)).map (·.2) = ms.map (·.2.2) := by
    rw [List.map_map]
    rfl
  have hm3 : (ms ++ [y]).map (·.2.2) = (ms.map fun m => (m.2.1, m.2.2)).map (·.2) ++ [y.2.2] := by
    rw [List.map_append, hm2]
    rfl
  have hr' := hr.trans hm3
  refine ⟨?_, ?_, ?_, by rw [hv, hv1], hr', e4, e5, e6, e7, f1, f2, f3⟩
  · rw [e3, claimAfter_lib, hv1, List.map_append]
    rfl
  · unfold Psc.walk
    rw [zipT_eq, hv, hv1, hr']
  · rw [walk_length (ms := ms ++ [y]) (by simp) hv hr hheld, hv1]

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.endP_ended
