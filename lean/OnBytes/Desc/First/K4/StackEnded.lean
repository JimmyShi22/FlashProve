-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/K4/StackEnded.lean: THE BATCHED SUMCHECK OF THE LAYERS' OWN ROUNDS: WHERE
`hearStack` (OnBytes/Desc/First/K4/Hear.lean) RETURNS OVER THE PLAIN ENGINE, THE RECORD BEHIND ITS
ROUNDS IS `Ended` (OnBytes/Tie/Pv/Psc/Run/PscSeam.lean), with every letter but two read off the tape
by a function. Definitions, two statements and their proofs.

  `stackRs`: the sumcheck's rounds (`stackMs`, StackLaw.lean) as the library's pairs: what was sent,
    the challenge.
  `stackVals`: what the round of the end values sent.
  `stackRec`: the record behind the rounds: `endP` (OnBytes/Desc/First/P1/FlSpec.lean) of the record
    with which the flat `pscBegin` starts, at the start form `stackStart` (StackLaw.lean), its value
    on what the ledger shows, the ledger's next slot, and what the second round sent and drew.
  `stack_heard`: `hearStack_tape` (StackTape.lean) with its letters named by these functions: the
    rounds' weights are lamS times `Weight.plain 3`; all weights are held; each round sent one
    scalar fewer than its weight's number of coefficients; the row is `stackRec`'s form at the
    product of the two end elements, nothing kept; the first end value's slot; and there are an
    array vals, WHOSE LIST IS `stackVals`, of 2 + (1 + P.y.LamM) + NCLp values, and a ledger G1,
    with the two `hideRun` equations: the end values are laid from that slot on under the further
    challenge, which gives G1; the sumcheck's own slots are laid in G1, which gives the ledger that
    is returned.
  `stack_ended`: `Ended` holds of `stackRec` at these letters, with 2 for the further variable.

NO NEW ARGUMENT: `hearStack_tape`; the seven equations on what the functions read off the tape are
those in `stack_law`'s proof (StackLaw.lean); `endP_ended` (OnBytes/Desc/First/P1/EndedOf.lean).

Limits. One direction: from a return. G1 stands under "there is"; the first `hideRun` equation fixes
it. What the start form, the end values and the two end elements mean is not said. No law of a
sumcheck is applied. Whether anything here reaches a routine of the program `verify-on-bytes` is for
the walk by constants to say.
-/
import OnBytes.Desc.First.K4.StackLaw
import OnBytes.Desc.First.P1.EndedOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.Model.Road (Ended)
open OnBytes.Desc.First.P1 (msOf plainWs endP Rnd Held tapeMu tapeEps tapeMu_cons tapeEps_cons
  roundAt roundAt_cons msOf_append_same drop_one_cons drop_first drop_second sentOf sentOf_cons
  endP_ended)

/-! ### What is read off the tape -/

/-- The sumcheck's rounds as the library's pairs: what was sent, the challenge. -/
def stackRs (lamS : Nat) (t : Tape) : List (List E × E) :=
  (stackMs lamS t).map fun m => (m.2.1, m.2.2)

/-- What the round of the end values sent. -/
def stackVals (lamS : Nat) (t : Tape) : List E := sentOf (t.drop (lamS + 3))

/-- The record behind the sumcheck's rounds. -/
def stackRec (v : Env) (H : Heard) (lamS : Nat) (F : Fork) (t : Tape) : Psc :=
  endP { target := (F.publicPart (stackStart v H F t)).getD zeroE, first := F.next,
         eps := tapeEps (t.drop 1),
         claim := addE (tapeMu (t.drop 1))
           (mulE (tapeEps (t.drop 1)) ((F.publicPart (stackStart v H F t)).getD zeroE)),
         start := stackStart v H F t, started := true } (stackMs lamS t) (stackY lamS t)

/-! ### Where the function returns -/

/-- **What the batched sumcheck has heard, by functions of the tape.** -/
theorem stack_heard {P : Pub} {v : Env} {H : Heard} {lamS NCLp : Nat} {F G : Fork} {t u : Tape}
    {S : HeardStack} (h : hearStack engFl P v H lamS NCLp F t = some (S, G, u)) :
    (stackMs lamS t).map (·.1) = plainWs lamS ∧
      (∀ m ∈ stackMs lamS t ++ [stackY lamS t], Held m.1) ∧
      (∀ m ∈ stackMs lamS t ++ [stackY lamS t], m.2.1.length + 1 = m.1.d) ∧
      S.rowS = (stackRec v H lamS F t).rowForm (mulE S.fin.As S.fin.Bs) {} ∧
      S.sA0 = F.next + 1 + 2 * lamS + 2 ∧
      ∃ (vals : Array E) (G1 : Fork), vals.toList = stackVals lamS t ∧
        vals.size = 2 + (1 + P.y.LamM) + NCLp ∧
        ({ F with next := F.next + 1 + 2 * lamS + 2 + (2 + (1 + P.y.LamM) + NCLp) } : Fork).hideRun
          S.sA0 vals (stackY lamS t).2.2 = some G1 ∧
        G1.hideRun (stackRec v H lamS F t).first
          (Array.replicate (stackRec v H lamS F t).walk.1.length zeroE) (subE zeroE oneE) =
            some G := by
  obtain ⟨x, mu0, eps, beta, T, rs, sentY, vals, w1, wY, wV, C, G1, ms, y, p, ht, hrs, _, hC, hT,
    hms, hyy, hp, a1, hheld, hlens, _, hsA0, _, _, _, hvs, hG1, hrow, hG⟩ := hearStack_tape h
  have hlen : (plainWs lamS).length = lamS := List.length_replicate
  have hwr : (plainWs lamS).length = rs.length := by rw [hlen, hrs]
  have q0 : tapeEps t = x := by rw [ht, tapeEps_cons]
  have q1 : stackMs lamS t = ms := by
    unfold stackMs
    rw [ht, drop_two_cons, msOf_append_same _ _ _ hwr, hms]
  have q2 : stackY lamS t = y := by
    unfold stackY
    rw [ht, ← hrs, drop_succ_cons', drop_first, roundAt_cons, hyy]
  have q3 : tapeMu (t.drop 1) = mu0 := by rw [ht, drop_one_cons, tapeMu_cons]
  have q4 : tapeEps (t.drop 1) = eps := by rw [ht, drop_one_cons, tapeEps_cons]
  have q5 : stackStart v H F t = C := by
    unfold stackStart
    rw [q0, hC, Option.map_some, Option.getD_some]
  have q6 : (F.publicPart C).getD zeroE = T := by rw [hT, Option.getD_some]
  have q7 : stackVals lamS t = vals.toList := by
    unfold stackVals
    rw [ht, ← hrs, drop_succ_cons', drop_second, sentOf_cons]
  have q8 : stackRec v H lamS F t = p := by
    unfold stackRec
    rw [q1, q2, q3, q4, q5, q6, hp]
  have q9 : y.2.2 = beta := by rw [hyy]
  rw [q1, q2, q8, q9]
  exact ⟨a1, hheld, hlens, hrow, hsA0, vals, G1, q7.symm, hvs, hG1, hG⟩

/-- **The record behind the batched sumcheck's rounds is `Ended`.** -/
theorem stack_ended {P : Pub} {v : Env} {H : Heard} {lamS NCLp : Nat} {F G : Fork} {t u : Tape}
    {S : HeardStack} (h : hearStack engFl P v H lamS NCLp F t = some (S, G, u)) :
    Ended (stackRec v H lamS F t) (stackStart v H F t)
      ((F.publicPart (stackStart v H F t)).getD zeroE) (tapeMu (t.drop 1)) (tapeEps (t.drop 1))
      F.next (plainWs lamS) (stackRs lamS t) 2 (stackY lamS t).2.1 (stackY lamS t).2.2 := by
  obtain ⟨a1, hheld, _⟩ := stack_heard h
  have e := endP_ended ((F.publicPart (stackStart v H F t)).getD zeroE) (tapeMu (t.drop 1))
    (tapeEps (t.drop 1)) F.next (stackStart v H F t) (stackMs lamS t) (stackY lamS t) 2 rfl hheld
  rw [a1] at e
  exact e

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.stack_heard
#print axioms OnBytes.Desc.First.K4.stack_ended
