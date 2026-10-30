-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/StackLed.lean: CONDITIONAL.

What is here. The batched sumcheck's own claim (`OwnBack.stack`, Johnson/Road/K4/W/Join.lean) on the
honest part's rounds, AT THE ROW's OWN JOB AND FROM THE HEARING's RETURN AS A WHOLE.

  `stackSum`, `k4Sum_stack`   the job; it is the row's
  `stack_led`   **`OwnBack.stack`**

Limits. At the reading `Reading.gl`. ONE THING STAYS A HYPOTHESIS ON WHAT IS SUMMED: THE START (hσ:
the verifier's start form is worth the reading of the total of the honest job's cube: it holds the
lookup's join and the second token sumcheck's form). That on the true end values the job's summand
is the cube's is had from Johnson/Road/K4/C/StackTrue.lean and StackCube.lean. ONE ON WHAT WAS SEEN
(hsh): the values that the ledger shows under the second token sumcheck's end slots are those which
the part reads off the rounds that it has seen. THREE ON THE INPUT's READER OF THE LOOKUP, at the
challenges in front: its token point, its weights of the calls and the calls' points are those of
what the hearing was handed (hzx, he, hzk). Beside them: the hearing returns, from a sized ledger,
and its return is opened in the letters of `LedG`; the tape has sampled what the challenges hold,
and they reach the batched sumcheck's first round; as many challenges stand in front of the
sub-protocol as the public data say; the part stands at the batched sumcheck's entry; the challenges
fit the call; the part, played alone, makes the rounds, which the tape holds; the world holds the
part's hiding coins under the sumcheck's own slots; the row's job is made and fits its call. No
example of the premises together is known. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.StackOwn
import Johnson.Desc.ProofFile.Honest.K4.Law.ClaimsAre
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsPow
import Johnson.Road.K4.C.StackSidesOf
import Johnson.Road.K4.C.StackTrue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading Fork World Level Tsc powers Forest.Heard)
open OnBytes.Model.Layer (Own nEndT)
open OnBytes.Slice (GE)
open OnBytes.K.Kc (Tape)
open OnBytes.Road.K4 (LedG)
open OnBytes.Desc.First.P1 (tapeEps)
open OnBytes.Desc.First.K4 (engFl hear)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc.Part.MaskedSum hiding hear
open ProofFile.Honest.SumLaw

variable {V : Type}

/-- The number of the batched sumcheck's end values. -/
abbrev stackEndsNo (Q : K4Pub) : ℕ :=
  2 + (1 + Q.P.y.LamM) + (Q.hp.NCL - (if (Q.g == 0) = true then 1 else 0))

/-- The batched sumcheck's job, as the row lays it: its summand holds the second token sumcheck's
end values as the part has seen them sent. -/
abbrev stackSum (Q : K4Pub) : SumJob K4In Unit :=
  k4SumJob (k4PlainShape Q.hp.lamS 2 (stackEndsNo Q)) fun w fr =>
    jobStack Q w (ptsOf Q w fr.heard) (k4SentAt fr.seen.rounds (k4TermsEnds Q))

/-- The batched sumcheck's part in the row. -/
theorem k4Sum_stack (Q : K4Pub) (i : ℕ) :
    k4SumSeen Q ((k4Shapes Q).getD 3 ⟨0, [], none⟩) jobStack i =
      sumPart (runName maskRowRun (k4Addr Q i) "sum") (runName maskRowRun (k4Addr Q i) "ends")
        (stackSum Q) := rfl

variable {Q : K4Pub} {tk : Array Nat} {t : Tape} {fo : Forest.Heard} {o : Own}
  {F G : Fork} {u : Tape} {H1 : OnBytes.Model.Layer.Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}

/-- **THE BATCHED SUMCHECK's OWN CLAIM IS WORTH 0 ON THE HONEST PART's ROUNDS**, at the row's job,
from the hearing as a whole. D: the data of the honest job at the part's entry. -/
theorem stack_led (h : List Fmt.Drawn)
    (hH : hear engFl { Q.P with tokv := tk } Q.hp Q.g fo F t = some (o, G, u))
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 3 ≤ ds.length)
    (hh : h.length = Q.r0) (Wd : World GE) (name endName : String)
    (c : SumCoins name endName (stackSum Q)) (st : State K4In Unit) (seen : Seen)
    (dp : List Fmt.Drawn) (rounds : List Fmt.RoundView)
    (hst : st.heard = h ++ ds.take (k4StartAt Q 3))
    (hzx : (st.input.look h).zx = fo.zx) (he : (st.input.look h).e = fo.e)
    (hzk : (st.input.look h).zk = fo.zk)
    (hd : drawsOk ((stackSum Q).callAt st.input (frontOf st seen)) dp = true)
    (ha : alone (sumPart (V := V) name endName (stackSum Q)) c st seen dp = some rounds)
    (hs : ∀ i, i < ownSlots ((stackSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (G2.next + i) = hidingCoin c i)
    (D : StackData)
    (hDt : stackData Q st.input (ptsOf Q st.input st.heard)
      (k4SentAt (frontOf st seen).seen.rounds (k4TermsEnds Q)) = some D)
    (hfit : k4JobFits (k4PlainShape Q.hp.lamS 2 (stackEndsNo Q)) (jobStackOn D) = true)
    (hT : TapeIs (t.drop (k4StartAt Q 3)) rounds)
    (hσ : ∀ C, OnBytes.Desc.First.K4.joinStart engFl o.v o.H
        (powers (tapeEps (t.drop (k4StartAt Q 3 - 1))) 2) G2 (t.drop (k4StartAt Q 3)) =
      some (C, G2, t.drop (k4StartAt Q 3)) →
      C.value Reading.gl Wd = Reading.gl.val (jobStackOn D).cube.total)
    (hsh : ∀ tT' a, o.H.tT = some tT' →
      ((Array.range (nEndT Q.P.y)).mapM fun i => G2.shown (tT'.sEnd + i)) = some a →
      a = k4SentAt (frontOf st seen).seen.rounds (k4TermsEnds Q)) :
    o.K.rowS.value Reading.gl Wd = 0 := by
  have s3 : k4StartAt Q 3 = k4StartAt Q 2 + (Q.P.y.h.lt + 4) := rfl
  have e3 : k4StartAt Q 2 + (Q.P.y.h.lt + 3) = k4StartAt Q 3 - 1 := by omega
  have c4 := L.c4
  rw [at_b3, e3] at c4
  have ed : (t.drop (k4StartAt Q 3 - 1)).drop 1 = t.drop (k4StartAt Q 3) := by
    rw [List.drop_drop]
    congr 1
  have hlam : D.S.Q.hp.lamS = Q.hp.lamS := by
    rw [(sidesOf_pub (OnBytes.Road.K4.C.stack_open hDt).1).1]
  have hj : (fun (w : K4In) (fr : Front Unit) =>
      jobStack Q w (ptsOf Q w fr.heard) (k4SentAt fr.seen.rounds (k4TermsEnds Q))) st.input
      (frontOf st seen) = some (jobStackOn D) := by
    show (stackData Q st.input (ptsOf Q st.input st.heard)
      (k4SentAt (frontOf st seen).seen.rounds (k4TermsEnds Q))).map jobStackOn = _
    rw [hDt]
    rfl
  exact stack_own (V := V) (P := { Q.P with tokv := tk }) name endName _ c st seen dp rounds G2 Wd
    hd ha hs hDt hlam hj hfit c4 L.s2 (by rw [ed]; exact hT) (by rw [ed]; exact hσ)
    (fun _ _ hr he' => OnBytes.Road.K4.C.stack_sides_true hDt hr he') rfl rfl
    (env_is hH _ (by rw [hst, at_look st.input h ds hh]; exact hzk))
    (by rw [hst, at_look st.input h ds hh, he, led_fo L])
    (by rw [hst]; exact at_zt st.input h L ds hh hzx _)
    (by rw [hst]; exact at_stackPow st.input h L ds hD hl hh _ (Nat.le_refl _)) hsh

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4Sum_stack
#print axioms ProofFile.Honest.K4.stack_led
