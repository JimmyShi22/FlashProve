-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/K4/StackWords.lean: where K4's text of the batched sumcheck returns, the arrays
on which it calls `stackEnd` hold the words that the round of the end values sent.

`hearStack_public` (StackPublic.lean) says on which arrays `stackEnd` returned K.fin, each of them
"what a ledger Fe shows"; of Fe it says nothing more. `hearStack_tape` (StackTape.lean) says which
ledger stands behind the round of the end values, and throws the arrays away. Here the two are said
of one and the same ledger, by hearStack_tape's own proof with nothing thrown away.

Main names:
  `hearStack_both`: the tape, the ledger G1 behind the round of the end values, the four reads of
    shown values at G1, the panels, and `stackEnd`'s return.
  `shown_run`: a member of a run of shown values is what the ledger holds.
  `hearStack_words`: `stackEnd` returned K.fin on arrays whose members are the words of
    `stackVals`: number 0 for the A side, 1 + k for never-sent vector k, 1 + (1 + LamM) for the B
    side, 2 + (1 + LamM) + n for weight claim n.
Limits. One direction: from a return; the ledger in front must be Sized. An identity on data:
nothing on what anything is worth, on a draw, on soundness or on hiding.


-/
import OnBytes.Desc.First.K4.StackTape
import OnBytes.Desc.First.K4.StackEnded
import OnBytes.Desc.First.K4.ShownUnder
import OnBytes.Desc.First.K4.RowsLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.Desc.First.P1 (bind_some pure_some need_some ask_some batch_spec pscBegin_tape
  plainRounds_tape pscEnds_tape pscRow_spec msOf plainWs endP endP_spec runP stepP Rnd Held
  claimAfter)
open OnBytes.Desc.First.P1 (tapeEps sentOf sentOf_cons drop_second shown_some array_getD_toList)
open OnBytes.PscRun (Sized)

/-- **The tape, the ledger, the reads and the return, of one run.** -/
theorem hearStack_both {P : Pub} {v : Env} {H : Heard} {lamS NCLp : Nat} {F G : Fork} {t u : Tape}
    {K : HeardStack} (h : hearStack engFl P v H lamS NCLp F t = some (K, G, u)) :
    ∃ (tT : Tsc) (shownT : Array E) (TS : List Nat) (pans : Panels) (G1 : Fork)
      (vals H1 V : Array E) (shA shB beta : E),
      H.tT = some tT ∧
      ((Array.range (nEndT P.y)).mapM fun i => F.shown (tT.sEnd + i)) = some shownT ∧
      callsTS P = some TS ∧
      panelsT { v := v, e := H.fo.e, shownT := shownT, zt := H.ztF, stubO := stubO P.y } TS
        (panelsA { v := v, e := H.fo.e, shownT := shownT, zt := H.ztF, stubO := stubO P.y } {}) =
        some pans ∧
      vals.toList = stackVals lamS t ∧ vals.size = 2 + (1 + P.y.LamM) + NCLp ∧
      ({ F with next := F.next + 1 + 2 * lamS + 2 + (2 + (1 + P.y.LamM) + NCLp) } : Fork).hideRun
        K.sA0 vals beta = some G1 ∧
      K.sH1 = K.sA0 + 1 ∧ K.sB0 = K.sH1 + (1 + P.y.LamM) ∧ K.sV = K.sB0 + 1 ∧
      ((Array.range (1 + P.y.LamM)).mapM fun i => G1.shown (K.sH1 + i)) = some H1 ∧
      ((Array.range NCLp).mapM fun i => G1.shown (K.sV + i)) = some V ∧
      G1.shown K.sA0 = some shA ∧ G1.shown K.sB0 = some shB ∧
      stackEnd P.y (placePanels pans.bl).1 K.rs lamS (powers (tapeEps t) 2) H1 V shA shB =
        some K.fin := by
  unfold hearStack at h
  obtain ⟨om, F1, t1, h1, k1⟩ := bind_some.mp h
  obtain ⟨_, rfl, x, e1, rfl⟩ := batch_spec h1
  obtain ⟨tT, A2, a2, c2, k2⟩ := bind_some.mp k1
  obtain ⟨q2, rfl, rfl⟩ := need_some.mp c2
  obtain ⟨shownT, A3, a3, c3, k3⟩ := bind_some.mp k2
  obtain ⟨rfl, rfl, q3⟩ := shownRun_spec c3
  obtain ⟨TS, A4, a4, c4, k4⟩ := bind_some.mp k3
  obtain ⟨q4, rfl, rfl⟩ := need_some.mp c4
  obtain ⟨pans, A5, a5, c5, k5⟩ := bind_some.mp k4
  obtain ⟨q5, rfl, rfl⟩ := need_some.mp c5
  obtain ⟨_, A6, a6, c6, k6⟩ := bind_some.mp k5
  obtain ⟨_, rfl, rfl⟩ := P1.must_some.mp c6
  obtain ⟨C, A7, a7, c7, k7⟩ := bind_some.mp k6
  obtain ⟨rfl, rfl⟩ := joinStart_quiet c7
  obtain ⟨p0, F8, t8, c8, k8⟩ := bind_some.mp k7
  obtain ⟨T, mu0, eps, w1, hT, rfl, rfl, e8⟩ := pscBegin_tape c8
  obtain ⟨st, F9, t9, c9, k9⟩ := bind_some.mp k8
  obtain ⟨rs, e9, hrs, hnames, a1, a2', a3', hstp, hstr, _, rfl⟩ :=
    plainRounds_tape (fun _ _ _ _ => rfl) c9
  obtain ⟨lam', rs', p'⟩ := st
  have hstp' : p' = runP _ (msOf (plainWs lamS) rs) := hstp
  subst hstp'
  obtain ⟨_, A10, a10, c10, k10⟩ := bind_some.mp k9
  obtain ⟨_, rfl, rfl⟩ := P1.must_some.mp c10
  obtain ⟨z, F11, t11, c11, k11⟩ := bind_some.mp k10
  obtain ⟨sA0, p2⟩ := z
  obtain ⟨hY, sentY, beta, vals, wY, wV, b1, b2, rfl, rfl, hG1, e11⟩ := pscEnds_tape c11
  obtain ⟨x1, A12, a12, c12, k12⟩ := bind_some.mp k11
  obtain ⟨rfl, rfl, q12⟩ := shownRun_spec c12
  obtain ⟨x2, A13, a13, c13, k13⟩ := bind_some.mp k12
  obtain ⟨rfl, rfl, q13⟩ := shownRun_spec c13
  obtain ⟨x3, A14, a14, c14, k14⟩ := bind_some.mp k13
  have c14' : Fl.shown _ _ _ = some (x3, A14, a14) := c14
  obtain ⟨q14, rfl, rfl⟩ := ask_some.mp c14'
  obtain ⟨x4, A15, a15, c15, k15⟩ := bind_some.mp k14
  have c15' : Fl.shown _ _ _ = some (x4, A15, a15) := c15
  obtain ⟨q15, rfl, rfl⟩ := ask_some.mp c15'
  obtain ⟨fin, A16, a16, c16, k16⟩ := bind_some.mp k15
  obtain ⟨q16, rfl, rfl⟩ := need_some.mp c16
  obtain ⟨z2, F17, t17, c17, k17⟩ := bind_some.mp k16
  obtain ⟨rowS, p3⟩ := z2
  have c17' : Fl.pscRow _ (mulE fin.As fin.Bs) {} F11 t11 = some ((rowS, p3), F17, t17) := c17
  obtain ⟨rfl, rfl, hG⟩ := pscRow_spec c17'
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k17
  have hx : tapeEps t = x := by
    rw [e1]
    rfl
  obtain ⟨more, ht⟩ : ∃ more, t = ⟨some RoundName.batSigma.name, 0, 2, [], [x]⟩ ::
      ⟨some RoundName.pscEpsilon.name, 0, w1, [mu0], [eps]⟩ ::
      (rs ++ ⟨some RoundName.pscY.name, 1, wY, sentY, [beta]⟩ ::
        ⟨some RoundName.pscValues.name, 0, wV, vals.toList, []⟩ :: more) :=
    ⟨_, by rw [e1, e8, e9, e11]⟩
  have hrs' : rs.length = lamS := hrs
  have hv : vals.toList = stackVals lamS t := by
    unfold stackVals
    rw [ht, ← hrs', drop_succ_cons', drop_second, sentOf_cons]
  rw [hx]
  exact ⟨tT, shownT, TS, pans, F11, vals, x1, x2, x3, x4, beta, q2, q3, q4, q5, hv, b2, hG1, rfl,
    rfl, rfl, q12, q13, q14, q15, q16⟩

/-- A member of a run of shown values is what the ledger holds. -/
theorem shown_run {F : Fork} {s n : Nat} {r : Array E}
    (h : ((Array.range n).mapM fun i => F.shown (s + i)) = some r) {i : Nat} (hi : i < n) :
    r.getD i zeroE = F.vp.getD (s + i) zeroE := by
  rw [Array.mapM_eq_mapM_toList] at h
  obtain ⟨ys, hl, e⟩ := Option.map_eq_some_iff.mp h
  subst e
  have hl' : ((List.range n).mapM fun i => F.shown (s + i)) = some ys := by simpa using hl
  obtain ⟨b, hb, hg⟩ := mapM_range_get _ hl' hi
  rw [array_getD_toList, List.getD_eq_getElem?_getD]
  show (ys[i]?).getD zeroE = _
  rw [hg]
  exact (shown_some hb).2.2

/-- **`stackEnd` returned K.fin on the words of the round of the end values.** -/
theorem hearStack_words {P : Pub} {v : Env} {H : Heard} {lamS NCLp : Nat} {F G : Fork}
    {t u : Tape} {K : HeardStack} (hF : Sized F)
    (h : hearStack engFl P v H lamS NCLp F t = some (K, G, u)) :
    ∃ (tT : Tsc) (shownT : Array E) (TS : List Nat) (pans : Panels) (H1 V : Array E) (shA shB : E),
      H.tT = some tT ∧
      ((Array.range (nEndT P.y)).mapM fun i => F.shown (tT.sEnd + i)) = some shownT ∧
      callsTS P = some TS ∧
      panelsT { v := v, e := H.fo.e, shownT := shownT, zt := H.ztF, stubO := stubO P.y } TS
        (panelsA { v := v, e := H.fo.e, shownT := shownT, zt := H.ztF, stubO := stubO P.y } {}) =
        some pans ∧
      stackEnd P.y (placePanels pans.bl).1 K.rs lamS (powers (tapeEps t) 2) H1 V shA shB =
        some K.fin ∧
      shA = (stackVals lamS t).getD 0 zeroE ∧
      (∀ k, k < 1 + P.y.LamM → H1.getD k zeroE = (stackVals lamS t).getD (1 + k) zeroE) ∧
      shB = (stackVals lamS t).getD (1 + (1 + P.y.LamM)) zeroE ∧
      ∀ n, n < NCLp → V.getD n zeroE = (stackVals lamS t).getD (2 + (1 + P.y.LamM) + n) zeroE := by
  obtain ⟨tT, shownT, TS, pans, G1, vals, H1, V, shA, shB, beta, q2, q3, q4, q5, hv, hs, hG1, s1,
    s2, s3, q12, q13, q14, q15, q16⟩ := hearStack_both h
  have hF' : Sized ({ F with next := F.next + 1 + 2 * lamS + 2 + (2 + (1 + P.y.LamM) + NCLp) } :
      Fork) := hF
  have w : ∀ i, i < 2 + (1 + P.y.LamM) + NCLp →
      G1.vp.getD (K.sA0 + i) zeroE = (stackVals lamS t).getD i zeroE := fun i hi =>
    hideRun_shown hF' hG1 hv (Fo.Later.refl G1) i (by rw [hs]; exact hi)
  refine ⟨tT, shownT, TS, pans, H1, V, shA, shB, q2, q3, q4, q5, q16, ?_, fun k hk => ?_, ?_,
    fun n hn => ?_⟩
  · rw [(shown_some q14).2.2, ← w 0 (by omega), Nat.add_zero]
  · rw [shown_run q12 hk, ← w (1 + k) (by omega), s1, Nat.add_assoc]
  · rw [(shown_some q15).2.2, ← w (1 + (1 + P.y.LamM)) (by omega), s2, s1, Nat.add_assoc]
  · rw [shown_run q13 hn, ← w (2 + (1 + P.y.LamM) + n) (by omega), s3, s2, s1]
    congr 1
    omega

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.hearStack_words
#print axioms OnBytes.Desc.First.K4.hearStack_both
