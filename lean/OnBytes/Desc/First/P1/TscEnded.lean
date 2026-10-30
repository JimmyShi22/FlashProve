-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/TscEnded.lean: WHERE THE FLAT FUNCTION OF A TOKEN SUMCHECK RETURNS, ITS RECORD
IS `Ended`. The like of LevelEnded.lean (beside this file) for `Fl.tscIn` (OnBytes/K/Kc/Flat.lean).
`tok_tie` (OnBytes/Tie/Pv/Lay/SumTop.lean) has `Ended` (OnBytes/Tie/Pv/Psc/Run/PscSeam.lean)
from the success of a routine of the program `verify-on-bytes` in a context.
Here it is had from the flat function's return. Statements and proofs.

NO NEW ARGUMENT: `tscIn_heard`, `tsc_walk` (Heard.lean) give nine of the twelve equations; the three
flags come from the specs of the flat functions that `tscIn_spec` (TscKit.lean) itself walks through
(`pscBegin_spec`, `tscLoop_spec`, `pscEnds_spec`), with `runP_flags` (LevelEnded.lean).

  `tscIn_flags`: the returned record has begun, has ended, and its row is not made.
  `tscRs`: a token sumcheck's rounds as the library's pairs (what was sent, the challenge).
  `tscWs_eq`: its weights are the library's `tokenWeights`.
  `tsc_ended`: if `Fl.tscIn P lt n dY F t` returns (o, G, u), then `Ended` holds of o.p at the start
    form `Aff.slot F.next`, the record's own target and first slot, `tapeMu2 t`, `tapeEps t`, the
    weights `tscWs (P.toList.take lt)`, the rounds `tscRs P lt t`, dY, and what the further round
    sent and drew.

One direction: from a return. Nothing is said of what the record means. The record's target and
first slot stand as o.p's own fields: `tsc_world` (Heard.lean) says what they are. `Ended` is a
predicate on a RECORD of `verify-on-bytes`; whether anything here reaches a routine of it is left
to a walk through the constants under these theorems: this file claims nothing of it.
-/
import OnBytes.Desc.First.P1.LevelEnded
import OnBytes.Tie.Pv.Psc.Run.PscToken

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Road (Ended tokenWeights)

/-- The returned record has begun, has ended, and its row is not made. -/
theorem tscIn_flags {P : Array E} {lt n dY : Nat} {F G : Fork} {t u : Tape} {o : Tsc}
    (h : Fl.tscIn P lt n dY F t = some (o, G, u)) :
    o.p.started = true ∧ o.p.ended = true ∧ o.p.rowMade = false := by
  unfold Fl.tscIn at h
  obtain ⟨o1, G1, u1, h1, k1⟩ := bind_some.mp h
  obtain ⟨x, G2, u2, h2, k2⟩ := bind_some.mp k1
  obtain ⟨sEnd, p2⟩ := x
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k2
  unfold Fl.tscRounds at h1
  obtain ⟨_, G3, u3, h3, k3⟩ := bind_some.mp h1
  obtain ⟨hlt, rfl, rfl⟩ := must_some.mp h3
  obtain ⟨sCl, G4, u4, h4, k4⟩ := bind_some.mp k3
  obtain ⟨rfl, v1, hv1, hG0⟩ := claimsIn_ledger h4
  obtain ⟨p0, G5, u5, h5, k5⟩ := bind_some.mp k4
  obtain ⟨T, mu0, eps, hT, rfl, rfl⟩ := pscBegin_spec h5
  obtain ⟨x, G6, u6, h6, k6⟩ := bind_some.mp k5
  obtain ⟨r, p1⟩ := x
  obtain ⟨ms, a1, a2, a3, rfl, a5, rfl⟩ := tscLoop_spec h6
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k6
  obtain ⟨hY, sentY, beta, v, b1, b2, rfl, rfl, hG⟩ := pscEnds_spec h2
  exact endP_flags
    { target := T, first := G4.next, eps := eps, claim := addE mu0 (mulE eps T),
      start := Aff.slot F.next, started := true } ms
    (OnBytes.Psc.Weight.atZero (dY + 1), sentY, beta)

/-- A token sumcheck's rounds as the library's pairs: what was sent, the challenge. -/
def tscRs (P : Array E) (lt : Nat) (t : Tape) : List (List E × E) :=
  (tscMs P lt t).map fun m => (m.2.1, m.2.2)

/-- The weights of a token sumcheck's rounds are the library's. -/
theorem tscWs_eq (P : Array E) (lt : Nat) : tscWs (P.toList.take lt) = tokenWeights P lt := rfl

/-- **Where the flat function of a token sumcheck returns, its record is `Ended`.** -/
theorem tsc_ended {P : Array E} {lt n dY : Nat} {F G : Fork} {t u : Tape} {o : Tsc}
    (h : Fl.tscIn P lt n dY F t = some (o, G, u)) :
    Ended o.p (Aff.slot F.next) o.p.target (tapeMu2 t) (tapeEps t) o.p.first
      (tscWs (P.toList.take lt)) (tscRs P lt t) dY (tscY P lt dY t).2.1
      (tscY P lt dY t).2.2 := by
  obtain ⟨_, a1, hy, _, _, hvars, hr, hclaim, heps, hstart, _⟩ := tscIn_heard h
  obtain ⟨f1, f2, f3⟩ := tscIn_flags h
  have hm2 : (tscRs P lt t).map (·.2) = (tscMs P lt t).map (·.2.2) := by
    unfold tscRs
    rw [List.map_map]
    rfl
  have hr' : o.p.r.toList = (tscRs P lt t).map (·.2) ++ [(tscY P lt dY t).2.2] := by
    rw [hr, List.map_append, hm2]
    rfl
  have hv1 : (tscMs P lt t ++ [tscY P lt dY t]).map (·.1) =
      tscWs (P.toList.take lt) ++ [OnBytes.Psc.Weight.atZero (dY + 1)] := by
    rw [List.map_append, a1, List.map_cons, List.map_nil, hy]
  refine ⟨?_, ?_, tsc_walk h, hvars, hr', hstart, rfl, heps, rfl, f1, f2, f3⟩
  · rw [hclaim, claimAfter_lib, hv1, heps, List.map_append]
    rfl
  · unfold Psc.walk
    rw [zipT_eq, hvars, hr']

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.tscIn_flags
#print axioms OnBytes.Desc.First.P1.tsc_ended
