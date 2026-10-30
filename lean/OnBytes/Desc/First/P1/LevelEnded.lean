-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/LevelEnded.lean: WHERE THE FLAT FUNCTION OF A PRODUCT LAYER RETURNS, ITS
RECORD IS `Ended`. `Fl.levelIn` (OnBytes/K/Kc/Flat.lean) is what the layers' own text runs. The
library's tie of a masked sumcheck's record to the typed sumcheck (`sum_said`,
OnBytes/Tie/Pv/Lay/SumSaid.lean) takes one thing of the record: `Ended`
(OnBytes/Tie/Pv/Psc/Run/PscSeam.lean): twelve equations on it. The theorem `level_tie`
(OnBytes/Tie/Pv/Lay/LevelTie.lean) has `Ended` from the success of a routine of the program
`verify-on-bytes` in a context. Here it is had from the flat function's return, with every letter a
function of the tape. Statements and proofs.

NO NEW ARGUMENT: `levelIn_heard`, `walk_length` (Heard.lean, beside this file) give ten of the
twelve; the rest is two small facts on lists.

  `claimAfter_lib`: the running claim behind rounds, as this folder writes it (on triples) and as
    the library writes it (on the weights and on the pairs), is one.
  `runP_flags`, `endP_flags`: rounds leave the record's three flags as they were, but that the last
    sets `ended`.
  `levelRs`: a layer's rounds as the library's pairs (what was sent, the challenge).
  `level_ended`: if `Fl.levelIn mu rho C order F t` returns, then `Ended` holds of `levelRec mu rho
    C order F t` at the start form C, the record's target, `tapeMu t`, `tapeEps t`, F.next, the
    weights `levelWs mu rho order`, the rounds `levelRs …`, 2, and what the further round sent and
    drew.
  `levelWs_eq`: these weights are the library's `levelWeights`.

One direction: from a return. Nothing is said of what the record means. `Ended` is a predicate on a
RECORD of `verify-on-bytes` (Psc); no routine of it is called here.
-/
import OnBytes.Desc.First.P1.Heard
import OnBytes.Tie.Pv.Psc.Run.PscLayer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Road (Ended levelWeights)

/-- The running claim, written on triples and written on weights and pairs, is one. -/
theorem claimAfter_lib : ∀ (ms : List Rnd) (c : E),
    claimAfter ms c =
      OnBytes.Psc.claimAfter (ms.map (·.1)) (ms.map fun m => (m.2.1, m.2.2)) c
  | [], _ => rfl
  | m :: ms, c => claimAfter_lib ms (OnBytes.Psc.polyAt (m.1.complete m.2.1 c) m.2.2)

/-- Rounds leave the three flags as they were. -/
theorem runP_flags : ∀ (ms : List Rnd) (p : Psc),
    (runP p ms).started = p.started ∧ (runP p ms).ended = p.ended ∧
      (runP p ms).rowMade = p.rowMade
  | [], _ => ⟨rfl, rfl, rfl⟩
  | m :: ms, p => runP_flags ms (stepP p m)

theorem endP_flags (p : Psc) (ms : List Rnd) (y : Rnd) :
    (endP p ms y).started = p.started ∧ (endP p ms y).ended = true ∧
      (endP p ms y).rowMade = p.rowMade :=
  ⟨(runP_flags ms p).1, rfl, (runP_flags ms p).2.2⟩

/-- A layer's rounds as the library's pairs: what was sent, the challenge. -/
def levelRs (mu : Nat) (rho : Array E) (order : List Nat) (t : Tape) : List (List E × E) :=
  (levelMs mu rho order t).map fun m => (m.2.1, m.2.2)

/-- The weights of a layer's rounds are the library's. -/
theorem levelWs_eq (mu : Nat) (rho : Array E) (order : List Nat) :
    levelWs mu rho order = levelWeights mu rho order := rfl

/-- **Where the flat function of a product layer returns, its record is `Ended`.** -/
theorem level_ended {mu : Nat} {rho : Array E} {C : Aff} {order : List Nat} {F G : Fork}
    {t u : Tape} {L : Level} (h : Fl.levelIn mu rho C order F t = some (L, G, u)) :
    Ended (levelRec mu rho C order F t) C (levelRec mu rho C order F t).target (tapeMu t)
      (tapeEps t) F.next (levelWs mu rho order) (levelRs mu rho order t) 2 (levelY mu t).2.1
      (levelY mu t).2.2 := by
  obtain ⟨_, _, _, a1, hy, hheld, _, hvars, hr, hclaim, heps, hstart, hfirst, _⟩ :=
    levelIn_heard h
  have hm2 : (levelRs mu rho order t).map (·.2) = (levelMs mu rho order t).map (·.2.2) := by
    unfold levelRs
    rw [List.map_map]
    rfl
  have hr' : (levelRec mu rho C order F t).r.toList =
      (levelRs mu rho order t).map (·.2) ++ [(levelY mu t).2.2] := by
    rw [hr, List.map_append, hm2]
    rfl
  have hv1 : (levelMs mu rho order t ++ [levelY mu t]).map (·.1) =
      levelWs mu rho order ++ [OnBytes.Psc.Weight.atZero 3] := by
    rw [List.map_append, a1, List.map_cons, List.map_nil, hy]
  have hfl := endP_flags
    { target := (F.publicPart C).getD zeroE, first := F.next, eps := tapeEps t,
      claim := addE (tapeMu t) (mulE (tapeEps t) ((F.publicPart C).getD zeroE)),
      start := C, started := true } (levelMs mu rho order t) (levelY mu t)
  refine ⟨?_, ?_, ?_, hvars, hr', hstart, rfl, heps, hfirst, hfl.1, hfl.2.1, hfl.2.2⟩
  · rw [hclaim, claimAfter_lib, hv1, heps, List.map_append]
    rfl
  · unfold Psc.walk
    rw [zipT_eq, hvars, hr']
  · rw [walk_length (ms := levelMs mu rho order t ++ [levelY mu t]) (by simp)
      (by rw [hvars, hv1]) hr hheld, hv1]

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.claimAfter_lib
#print axioms OnBytes.Desc.First.P1.level_ended
