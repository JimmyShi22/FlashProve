-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/StackWhole.lean: CONDITIONAL.

What is here. The batched sumcheck's own claim (`OwnBack.stack`, Johnson/Road/K4/W/Join.lean) is
worth 0 where BOTH the second token sumcheck's part and the batched sumcheck's part have played
honestly: StackLed.lean's statement with its premise on the start (hσ) had from TermsSent.lean (what
the second token sumcheck's form is worth), StackStartLed.lean (the start form's worth) and ONE
HYPOTHESIS ON THE LOOKUP's JOIN.

  `sidesOf_fo`   what the two jobs share reads, of the sampled values, what the lookup returned
     alone
  `stack_whole`   **`OwnBack.stack`**

Limits. At the reading `Reading.gl`. WHAT STAYS A HYPOTHESIS ON WHAT IS SUMMED: `JoinWorth`
(StackStart.lean), at the factors that the verifier's text makes: THE FIRST PASS IS THE LOOKUP's
JOIN: nothing here shows it; and the start of the second token sumcheck (hσ3: the slot of its
claimed sum is worth the reading of its cube's total). ON WHAT WAS SEEN: hseen (what the batched
sumcheck's part reads off the rounds that it has seen is the list of scalars of the other part's
last round) and hsh (it is also what the ledger shows under the end slots). ON PUBLIC DATA:
`TermsPub` (TermsAll.lean), the test `triPlainB` among its clauses; the second token sumcheck has an
end value (hnE). ON A CHALLENGE: the three words of the second token sumcheck's first challenge lie
below the prime (hok). ON THE INPUT's READER OF THE LOOKUP: hzx, he, hzk; and the lookup's point is
not empty (hz0). Beside them, for each of the two parts: it stands at its entry, with one input; the
challenges fit the call; played alone it makes its rounds, which the tape holds; the world holds its
hiding coins under its sumcheck's own slots; its job is made and fits its call; and the hearing
returns, opened in the fields of `LedG`; the tape has sampled what the challenges hold, and they
reach the batched sumcheck's first round (hl); as many challenges stand in front of the sub-protocol
as the public data say (hh). No example of the premises together is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.StackLed
import Johnson.Desc.ProofFile.Honest.K4.Law.StackStartLed
import Johnson.Desc.ProofFile.Honest.K4.Law.TermsSent
import Johnson.Desc.ProofFile.Honest.K4.Law.StackHval
import Johnson.Desc.ProofFile.Honest.K4.Law.TermsWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork World Level Tsc powers Forest.Heard)
open OnBytes.Model.Layer (Own nEndT)
open OnBytes.Slice (GE)
open OnBytes.K.Kc (Tape)
open OnBytes.Road.K4 (LedG)
open OnBytes.Desc.First.P1 (tapeEps)
open OnBytes.Desc.First.K4 (engFl hear)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc.Part.MaskedSum hiding hear
open ProofFile.Honest.SumLaw

/-- What the two jobs share reads, of the sampled values, what the lookup returned alone. -/
theorem sidesOf_fo (Q : K4Pub) (w : K4In) {p p' : Pts} (h : p.fo = p'.fo) :
    OnBytes.Desc.First.K4.Honest.Sides.of Q w p = OnBytes.Desc.First.K4.Honest.Sides.of Q w p' := by
  unfold OnBytes.Desc.First.K4.Honest.Sides.of OnBytes.Desc.First.K4.Honest.envOf ztOf
  rw [h]

variable {V : Type} {Q : K4Pub} {tk : Array Nat} {t : Tape} {fo : Forest.Heard} {o : Own}
  {F G : Fork} {u : Tape} {H1 : OnBytes.Model.Layer.Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}

/-- **The batched sumcheck's own claim is worth 0 where the two parts have played honestly.**
CONDITIONAL: on every hypothesis named: above all on hJW (`JoinWorth`: the first pass is the
lookup's join) and hσ3 (the second token sumcheck's claimed sum), which bear what is summed. The
letters with 3: the second token sumcheck's part; with 4: the batched sumcheck's. -/
theorem stack_whole (h : List Fmt.Drawn)
    (hH : hear engFl { Q.P with tokv := tk } Q.hp Q.g fo F t = some (o, G, u))
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 3 ≤ ds.length)
    (hh : h.length = Q.r0) (Wd : World GE) (w : K4In)
    (hzx : (w.look h).zx = fo.zx) (he : (w.look h).e = fo.e) (hzk : (w.look h).zk = fo.zk)
    -- the second token sumcheck's part
    (name3 end3 : String) (c3 : SumCoins name3 end3 (termsSum Q)) (st3 : State K4In Unit)
    (seen3 : Seen) (dp3 : List Fmt.Drawn) (rounds3 : List Fmt.RoundView) (hin3 : st3.input = w)
    (hst3 : st3.heard = h ++ ds.take (k4StartAt Q 2))
    (hdr3 : drawsOk ((termsSum Q).callAt st3.input (frontOf st3 seen3)) dp3 = true)
    (ha3 : alone (sumPart (V := V) name3 end3 (termsSum Q)) c3 st3 seen3 dp3 = some rounds3)
    (hs3 : ∀ i, i < ownSlots ((termsSum Q).callAt st3.input (frontOf st3 seen3)).all →
      Wd.slot (G1.next + 1 + i) = hidingCoin c3 i)
    (S : OnBytes.Desc.First.K4.Honest.Sides)
    (hS : OnBytes.Desc.First.K4.Honest.Sides.of Q st3.input (ptsOf Q st3.input st3.heard) =
      some S)
    (P : TermsPub S) (j : Job) (hJ : jobTermsOn S = some j)
    (hfit3 : k4JobFits (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)) j = true)
    (hnE : 1 ≤ nEndT Q.P.y)
    (hσ3 : (Aff.slot G1.next).value Reading.gl Wd = Reading.gl.val j.cube.total)
    (hT3 : TapeIs (t.drop (k4StartAt Q 2)) rounds3)
    (hok : OnBytes.okE tT.p.eps = true)
    -- the batched sumcheck's part
    (name4 end4 : String) (c4 : SumCoins name4 end4 (stackSum Q)) (st4 : State K4In Unit)
    (seen4 : Seen) (dp4 : List Fmt.Drawn) (rounds4 : List Fmt.RoundView) (hin4 : st4.input = w)
    (hst4 : st4.heard = h ++ ds.take (k4StartAt Q 3))
    (hdr4 : drawsOk ((stackSum Q).callAt st4.input (frontOf st4 seen4)) dp4 = true)
    (ha4 : alone (sumPart (V := V) name4 end4 (stackSum Q)) c4 st4 seen4 dp4 = some rounds4)
    (hs4 : ∀ i, i < ownSlots ((stackSum Q).callAt st4.input (frontOf st4 seen4)).all →
      Wd.slot (G2.next + i) = hidingCoin c4 i)
    (D : StackData)
    (hDt : stackData Q st4.input (ptsOf Q st4.input st4.heard)
      (k4SentAt (frontOf st4 seen4).seen.rounds (k4TermsEnds Q)) = some D)
    (hfit4 : k4JobFits (k4PlainShape Q.hp.lamS 2 (stackEndsNo Q)) (jobStackOn D) = true)
    (hT4 : TapeIs (t.drop (k4StartAt Q 3)) rounds4)
    -- what was seen
    (hseen : ∀ (rv : Fmt.RoundView) (s : List E), rounds3.getLast? = some rv → scalars rv.vals = some s →
      k4SentAt (frontOf st4 seen4).seen.rounds (k4TermsEnds Q) = s.toArray)
    (hsh : ∀ tT' a, o.H.tT = some tT' →
      ((Array.range (nEndT Q.P.y)).mapM fun i => G2.shown (tT'.sEnd + i)) = some a →
      a = k4SentAt (frontOf st4 seen4).seen.rounds (k4TermsEnds Q))
    -- what is summed
    (hz0 : fo.zx.isEmpty = false)
    (hJW : ∀ (weighed : Array _) (parts : List Aff) (tT' : Tsc),
      o.v.y.calls.mapM o.v.weighedOf = some weighed →
      ((o.v.y.calls.zip weighed).toList.zipIdx.mapM fun x =>
        o.v.joinPart o.H.fo.alpha o.H.fo.theta x.2 x.1.1 x.1.2) = some parts →
      o.H.tT = some tT' → JoinWorth o.H tT' parts Wd D) :
    o.K.rowS.value Reading.gl Wd = 0 := by
  subst hin3
  -- the second token sumcheck's form
  obtain ⟨rv, s, a1, a2, _, hsz, hKT⟩ := terms_KT_sent (V := V) h L ds hh Wd name3 end3 c3 st3
    seen3 dp3 rounds3 hst3 hzx hdr3 ha3 hs3 S hS P j hJ hfit3 hnE hσ3 hT3 (led_window L)
    (led_hinv L hok)
  -- one S, one point, one list of shown values
  have eS : D.S = S := by
    have h1 := (OnBytes.Road.K4.C.stack_open hDt).1
    rw [hin4, sidesOf_fo Q st3.input (p' := ptsOf Q st3.input st3.heard)
      (by rw [hst4, hst3, at_look st3.input h ds hh, at_look st3.input h ds hh]), hS] at h1
    exact (Option.some.inj h1).symm
  have ert : (ptsOf Q st4.input st4.heard).rt = tT.r := by
    rw [hst4]
    exact at_rt st4.input h L ds hD hl hh _ (by simp only [k4StartAt]; omega)
  have esh := hseen rv s a1 a2
  have hy : S.v.y = Q.P.y := (sidesOf_pub hS).2
  have hT0 : 0 < S.v.y.T := by
    rw [P.T]
    exact Nat.pos_of_ne_zero (by positivity)
  obtain ⟨sT, hsT⟩ := Option.isSome_iff_exists.mp
    (jobTermsOn_summand hJ hT0 s.toArray tT.r (by rw [hy]; exact hsz))
  rw [hsT] at hKT
  refine stack_led (V := V) h hH L ds hD hl hh Wd name4 end4 c4 st4 seen4 dp4 rounds4 hst4
    (by rw [hin4]; exact hzx) (by rw [hin4]; exact he) (by rw [hin4]; exact hzk) hdr4 ha4 hs4 D
    hDt hfit4 hT4 (fun C hC => ?_) hsh
  exact stack_sigma_of hDt
    (by rw [hst4]; exact at_stackPow st4.input h L ds hD hl hh _ (Nat.le_refl _)) Wd
    (by rw [eS, esh, ert]; exact hsT)
    (stack_hval hDt
      (by rw [hst4, at_look st4.input h ds hh, hin4, hzx]; exact hz0) (by rw [ert]; exact hsz))
    hKT hJW hC

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.sidesOf_fo
#print axioms ProofFile.Honest.K4.stack_whole
