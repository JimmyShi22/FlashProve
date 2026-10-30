-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TermsSent.lean: CONDITIONAL.

What is here. The form that the second token sumcheck of the feed-forward layers' rounds leaves
(`Heard.KT`) is worth, on the honest part's rounds, the honest side's summand (`Sides.summand`,
Johnson/Desc/K4/Honest/Sides.lean) AT THE SUMCHECK's END POINT ON THE SCALARS OF THE PART's LAST
ROUND: TermsTop.lean's statement, with the masked end values replaced by what was sent.

  `terms_sent`   the job's summand on the last round's scalars reads as on the masked end values
  `terms_atEnds_is`   the job's summand is the honest side's, at the point that the challenges make
  `terms_KT_sent`   **the form's worth, on what was sent**

Limits. Those of TermsTop.lean: at the reading `Reading.gl`; the start (the slot of the claimed sum
is worth the reading of the cube's total), the eight clauses `TermsPub` and the premise on the
reading of the first challenge's inverse are premises, with the hearing's return opened (`LedG`) and
what TermsLed.lean's head lists. No function of the verifier makes the number on the right. No
example of the premises together is known. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TermsTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE subE invE)
open OnBytes.Model (Reading Aff Fork World Level Tsc Forest.Heard)
open OnBytes.Model.Layer (Own nEndT)
open OnBytes.PscRun (Sized)
open OnBytes.Slice (GE)
open OnBytes.K.Kc (Fl Tape)
open OnBytes.Desc.First.P1 (tscWs tscIn_tape tapeCl)
open OnBytes.Road.K4 (LedG)
open OnBytes.Road.K4.C (jobTermsOn_whole)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw
open VerifiableInference.Desc.Part.MaskedSum
open ProofFile.Honest.SumLaw

variable {V : Type}

/-- **The job's summand on the last round's scalars reads as on the masked end values.** -/
theorem terms_sent (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (termsSum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (F0 : Fork)
    (hd : drawsOk ((termsSum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (termsSum Q)) c st seen ds = some rounds)
    (j : Job) (hj : jobTerms Q st.input (ptsOf Q st.input st.heard) = some j)
    (hfitJ : k4JobFits (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)) j = true)
    (hnE : 1 ≤ nEndT Q.P.y)
    (hA : ∀ rs, rs.length = Q.P.y.h.lt → ReadsAlike (j.atEnds rs))
    {tp u : Tape} {G2 : Fork} {o : Tsc}
    (hF : Fl.tscIn (ztOf Q (ptsOf Q st.input st.heard)) Q.P.y.h.lt (nEndT Q.P.y) 1 F0 tp =
      some (o, G2, u))
    (hS : Sized F0) (hT : TapeIs tp rounds) (Fz F1 : Fork) (hL : Fo.Later G2 Fz) (hSz : Sized Fz)
    (hW : Fz.hideRun o.p.first (Array.replicate o.p.walk.1.length zeroE) (subE zeroE oneE) =
      some F1) :
    ∃ (rv : Fmt.RoundView) (s : List E), rounds.getLast? = some rv ∧ scalars rv.vals = some s ∧
      s.length = nEndT Q.P.y ∧
      Reading.gl.val (j.atEnds o.r.toList s) = Reading.gl.val (j.atEnds o.r.toList
        (maskedEnds (j.ends o.r.toList) (endRun c) (o.p.r.toList.getD Q.P.y.h.lt zeroE))) := by
  obtain ⟨hn, _, _, _, _, hel⟩ := terms_parts hj
  obtain ⟨hle, T, cl, mu0, eps, rs, sentY, beta, w0, wY, wV, ms, y, v1, v, F, ht, _, _, _, _,
    hv1, _, _, hG0', _, a1, _, _, _, _, hpr, _, _, _, _, _, hor, _⟩ := tscIn_tape hF
  have ecl : tapeCl tp = cl := by
    rw [ht]
    rfl
  have hG0 : ({ F0 with next := F0.next + 1 } : Fork).hideRun F0.next #[tapeCl tp] oneE =
      some F := by
    rw [ecl, ← hv1]
    exact hG0'
  have hk := terms_weights Q st.input (frontOf st seen) j hj
  obtain ⟨h, G, hh, _⟩ := k4_hears (V := V) name endName (termsSum Q) c st seen ds rounds
    (Aff.slot F0.next) F (shapeOk_token _ (Nat.le_refl 1) hnE) hd ha
    (tsc_ready hF hS hG0 _ hk hnE hL hSz hW)
  obtain ⟨hSL, _⟩ := tsc_sameLetters hF hS hG0 _ hk hh hT
  have hlen : (ms.map (·.2.2)).length = Q.P.y.h.lt := by
    have e1 := congrArg List.length a1
    rw [List.length_map, tscWs, List.length_map, List.length_take] at e1
    have e2 : (ztOf Q (ptsOf Q st.input st.heard)).toList.length =
        (ztOf Q (ptsOf Q st.input st.heard)).size := Array.length_toList
    rw [List.length_map]
    omega
  have hr1 : h.r.take j.cube.n = o.r.toList := by
    rw [← hSL.r, hpr, List.map_append, hor, hn, ← hlen, List.take_left]
  have hr2 : h.r.getD j.cube.n zeroE = o.p.r.toList.getD Q.P.y.h.lt zeroE := by
    rw [← hSL.r, hn]
  have hol : o.r.toList.length = Q.P.y.h.lt := by rw [hor]; exact hlen
  have hr : h.r = varsOf ((termsSum Q).callAt st.input (frontOf st seen)) ds :=
    (sumClaim V K4In Unit name endName _ c st seen ds rounds (Aff.slot F0.next) F G h hd ha
      hh).2.1
  obtain ⟨r, s, c1, c2, c3, c4⟩ := k4_sent_summand (V := V) name endName
    (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)) (fun w fr => jobTerms Q w (ptsOf Q w fr.heard)) c st
    seen ds rounds j ⟨1, nEndT Q.P.y⟩ hd ha hj (jobFits_parts hfitJ) rfl (hel _)
    (by rw [← hr, hr1]; exact hA _ hol)
  rw [← hr, hr1, hr2] at c4
  exact ⟨r, s, c1, c2, c3, c4⟩

/-- The job's summand is the honest side's, at the point that the challenges make. -/
theorem terms_atEnds_is {S : OnBytes.Desc.First.K4.Honest.Sides} {J : Job}
    (hJ : jobTermsOn S = some J) (rs : List E) (hr : rs.length = S.v.y.h.lt) (e : List E) :
    J.atEnds rs e = (S.summand e.toArray rs.toArray).getD zeroE := by
  obtain ⟨rows, _, hfit, _, _, rfl⟩ := jobTermsOn_whole hJ
  show (S.summand e.toArray ((OnBytes.Road.K4.C.termsCube S rows).pointOf rs)).getD zeroE = _
  rw [pointOf_default _ hfit rfl rs hr]

variable {Q : K4Pub} {tk : Array Nat} {t : Tape} {fo : Forest.Heard} {o : Own}
  {F G : Fork} {u : Tape} {H1 : OnBytes.Model.Layer.Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}

/-- **THE FORM IS WORTH THE HONEST SIDE's SUMMAND AT THE SUMCHECK's END POINT ON WHAT WAS SENT.** -/
theorem terms_KT_sent (h : List Fmt.Drawn)
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn)
    (hh : h.length = Q.r0) (Wd : World GE) (name endName : String)
    (c : SumCoins name endName (termsSum Q)) (st : State K4In Unit) (seen : Seen)
    (dp : List Fmt.Drawn) (rounds : List Fmt.RoundView)
    (hst : st.heard = h ++ ds.take (k4StartAt Q 2)) (hzx : (st.input.look h).zx = fo.zx)
    (hd : drawsOk ((termsSum Q).callAt st.input (frontOf st seen)) dp = true)
    (ha : alone (sumPart (V := V) name endName (termsSum Q)) c st seen dp = some rounds)
    (hs : ∀ i, i < ownSlots ((termsSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (G1.next + 1 + i) = hidingCoin c i)
    (S : OnBytes.Desc.First.K4.Honest.Sides)
    (hS : OnBytes.Desc.First.K4.Honest.Sides.of Q st.input (ptsOf Q st.input st.heard) = some S)
    (P : TermsPub S)
    (j : Job) (hJ : jobTermsOn S = some j)
    (hfitJ : k4JobFits (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)) j = true)
    (hnE : 1 ≤ nEndT Q.P.y)
    (hσ : (Aff.slot G1.next).value Reading.gl Wd = Reading.gl.val j.cube.total)
    (hT : TapeIs (t.drop (k4StartAt Q 2)) rounds)
    (hW : G1'.hideRun tT.p.first (Array.replicate tT.p.walk.1.length zeroE) (subE zeroE oneE) =
      some G2)
    (hinv : Reading.gl.val (invE tT.p.eps) * Reading.gl.val tT.p.eps = 1) :
    ∃ (rv : Fmt.RoundView) (s : List E), rounds.getLast? = some rv ∧ scalars rv.vals = some s ∧
      s.length = nEndT Q.P.y ∧ tT.r.size = Q.P.y.h.lt ∧
      o.H.KT.value Reading.gl Wd =
        Reading.gl.val ((S.summand s.toArray tT.r).getD zeroE) := by
  have hj : jobTerms Q st.input (ptsOf Q st.input st.heard) = some j := by
    unfold jobTerms
    rw [hS]
    exact hJ
  have hy : S.v.y = Q.P.y := (sidesOf_pub hS).2
  have c3 := call_terms st.input h L ds hh hzx (k4StartAt Q 2)
  rw [← hst] at c3
  obtain ⟨rv, s, a1, a2, a3, a4⟩ := terms_sent (V := V) name endName Q c st seen dp rounds G1 hd ha
    j hj hfitJ hnE (fun rs hr => (terms_three P hJ rs (by rw [hy]; exact hr)).2.1) c3 L.s1 hT G1'
    G2 (Fo.Later.refl _) L.s1' hW
  have hl : tT.r.toList.length = Q.P.y.h.lt := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, ms, _, _, _, _, _, _, _, _, _, _, _, _, _, _, b1, _, _,
      _, _, _, _, _, _, _, _, hor, _⟩ := tscIn_tape c3
    have e1 := congrArg List.length b1
    rw [List.length_map, tscWs, List.length_map, List.length_take] at e1
    have hle := (tscIn_tape c3).1
    have e2 : (ztOf Q (ptsOf Q st.input st.heard)).toList.length =
        (ztOf Q (ptsOf Q st.input st.heard)).size := Array.length_toList
    rw [hor, List.length_map]
    omega
  refine ⟨rv, s, a1, a2, a3, by rw [← Array.length_toList]; exact hl, ?_⟩
  rw [terms_KT_pub (V := V) h L ds hh Wd name endName c st seen dp rounds hst hzx hd ha hs S hS P j
    hJ hfitJ hnE hσ hT hW hinv, ← a4, terms_atEnds_is hJ _ (by rw [hy]; exact hl)]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.terms_sent
#print axioms ProofFile.Honest.K4.terms_atEnds_is
#print axioms ProofFile.Honest.K4.terms_KT_sent
