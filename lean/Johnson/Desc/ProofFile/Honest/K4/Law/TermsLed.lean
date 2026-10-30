-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TermsLed.lean: CONDITIONAL.

What is here. THE FORM THAT THE SECOND TOKEN SUMCHECK OF THE FEED-FORWARD LAYERS' ROUNDS LEAVES
(`Heard.KT`, OnBytes/Desc/First/K4/Hear.lean: `hearTerms`) IS WORTH, ON THE HONEST PART's ROUNDS,
THE JOB's SUMMAND ON THE END VALUES AS `maskedEnds` WRITES THEM (the true end values, each plus the
last challenge times its mask entry; that the last round's scalars read as these is
TermsSent.lean's; the summand: the honest side's `Sides.summand`, Johnson/Desc/K4/Honest/Sides.lean,
which is made of the verifier's panels; no function of the verifier makes that number). That
sumcheck has no claim of its own in the verifier's lists: the hearing makes its row at the summand 0
and goes on with the row's form over minus the first challenge, which enters the batched sumcheck's
start form. Statements and proofs.

K4 is the sub-protocol of the feed-forward layers' rounds.

  `termsSum`, `k4Sum_terms`   the job; it is the row's
  `terms_parts`, `terms_weights`   the job's way, weights and number of end values
  `led_KT`, `call_terms`   the form, and the flat function at the makers' letters, off the hearing's
     return
  `terms_row`   the row at the summand 0
  `terms_KT`   **the form's worth**

Limits. At the reading `Reading.gl` alone. THE START IS A PREMISE: the slot of the claimed sum is
worth the reading of the cube's total. THREE PREMISES ON THE JOB, at all lists of lt challenges:
along the masked line its summand is a polynomial of degree at most 1; it reads its values through
the reading; on the true end values it is the cube's summand (not shown here: TermsAll.lean has the
three from `TermsPub` (public data, and the sizes of a sampled point and of a table of the input's
products) and the job's return). ONE PREMISE ON THE READING, as in the library's law on this stretch
(`terms_law`, OnBytes/Desc/First/K4/TermsLaw.lean): the reading of the inverse of the first
challenge, times that challenge's, is 1. THE OTHER PREMISES of `terms_KT`: the hearing's return,
opened (`LedG`); as many challenges stand in front of the sub-protocol as the public data say; the
part stands at its entry; of what the input's reader of the lookup returns, the token point is that
of what the hearing was handed (zx); the challenges fit the call; the part, played alone, makes the
rounds; the world holds the part's hiding coins under the sumcheck's own slots; the job is made and
fits its call; there is an end value; the tape holds the rounds; the laying of the sumcheck's own
slots behind its rounds returns (hW: TermsWindow.lean's `led_window`, a later file, has it from
`LedG` alone). It asks neither that the tape has sampled what the challenges hold nor the test
`k4Fits`. Where the honest side's summand is not made the job's `atEnds` is the zero word
(Johnson/Desc/K4/Honest/Terms.lean). No statement here names a scalar of the rounds: `maskedEnds` is
written out of the job's true end values and the part's mask entries. No example of the premises
together is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatLed
import Johnson.Desc.ProofFile.Honest.K4.Law.AtEnds
import Johnson.Road.K4.C.StackIs
import Johnson.Road.K4.C.TermsOpen
import OnBytes.Desc.First.K4.HearLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE subE negE invE)
open OnBytes.Model (Reading Aff Fork World Level Tsc orderDefault Forest.Heard)
open OnBytes.Model.Layer (Own nEndT)
open OnBytes.PscRun (Sized)
open OnBytes.Slice (GE)
open OnBytes.K.Kc (Fl Tape)
open OnBytes.Desc.First.P1 (tscWs tscIn_tape tapeCl)
open OnBytes.Desc.First.K4 (hearTerms_KT)
open OnBytes.Road.K4 (LedG)
open OnBytes.Road.K4.C (termsCube endMapsOf jobTermsOn_whole)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw
open OnBytes.Desc.First.K4.Honest.PtsLaw
open VerifiableInference.Desc.Part.MaskedSum
open ProofFile.Honest.SumLaw

variable {V : Type}

/-! ## 1 The job -/

/-- The second token sumcheck's job, as the row lays it. -/
abbrev termsSum (Q : K4Pub) : SumJob K4In Unit :=
  k4SumJob (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)) fun w fr => jobTerms Q w (ptsOf Q w fr.heard)

/-- The second token sumcheck's part in the row. -/
theorem k4Sum_terms (Q : K4Pub) (i : ℕ) :
    k4Sum Q ((k4Shapes Q).getD 2 ⟨0, [], none⟩) maskRowRun jobTerms i =
      sumPart (runName maskRowRun (k4Addr Q i) "sum") (runName maskRowRun (k4Addr Q i) "ends")
        (termsSum Q) := rfl

/-- Where the job is made: its cube's number of variables, order, way and fit; its degree in the
further variable; its number of end values. -/
theorem terms_parts {Q : K4Pub} {w : K4In} {p : Pts} {j : Job} (hj : jobTerms Q w p = some j) :
    j.cube.n = Q.P.y.h.lt ∧ j.cube.order = orderDefault Q.P.y.h.lt ∧
      j.cube.way = .point (ztOf Q p) ∧ j.cube.fits = true ∧ j.dY = 1 ∧
      ∀ rs, (j.ends rs).length = nEndT Q.P.y := by
  unfold jobTerms at hj
  obtain ⟨S, hS, hj⟩ := Option.bind_eq_some_iff.mp hj
  obtain ⟨hy, hzt, _⟩ := OnBytes.Road.K4.C.sides_parts hS
  obtain ⟨rows, _, hfit, _, _, rfl⟩ := jobTermsOn_whole hj
  refine ⟨by show S.v.y.h.lt = _; rw [hy], by show orderDefault S.v.y.h.lt = _; rw [hy],
    by show Way.point S.zt = _; rw [hzt], hfit, rfl, fun rs => ?_⟩
  show (((endMapsOf S.v.y rows).map _).toList).length = _
  rw [Array.length_toList, Array.size_map, ← hy]
  simp [endMapsOf]

/-- The call's weights are a token sumcheck's at the lookup's token point. -/
theorem terms_weights (Q : K4Pub) (w : K4In) (fr : Front Unit) (j : Job)
    (hj : jobTerms Q w (ptsOf Q w fr.heard) = some j) :
    ((termsSum Q).callAt w fr).vs.map Var.weight =
      tscWs ((ztOf Q (ptsOf Q w fr.heard)).toList.take Q.P.y.h.lt) := by
  obtain ⟨hn, ho, hw, hfit, _, _⟩ := terms_parts hj
  rw [← levelWs_tsc Q.P.y.h.lt _ (by rw [← hn]; exact fits_way _ hfit _ hw), ← ho]
  exact point_weights (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)) Q.P.y.h.lt rfl
    (fun w fr => jobTerms Q w (ptsOf Q w fr.heard)) w fr j _ hj hw hn
    (by rw [ho]; simp [orderDefault])

/-! ## 2 Off the hearing's return -/

variable {Q : K4Pub} {tk : Array Nat} {t : Tape} {fo : Forest.Heard} {o : Own}
  {F G : Fork} {u : Tape} {H1 : OnBytes.Model.Layer.Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}

/-- The form that the stretch leaves, in the letters of the token sumcheck's own return. -/
theorem led_KT
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5) :
    o.H.KT = (tT.p.rowForm zeroE {}).scale (negE (invE tT.p.eps)) := by
  obtain ⟨u1, _, hT⟩ := L.nt
  obtain ⟨tT', h1, h2, _⟩ := hearTerms_KT hT
  have e : tT' = { tT with p := { tT.p with rowMade := true } } :=
    Option.some.inj (h1.symm.trans L.kTT)
  rw [h2, e]
  rfl

/-- **The second token sumcheck has run at the makers' letters**, at every prefix. -/
theorem call_terms (w : K4In) (h : List Fmt.Drawn)
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hh : h.length = Q.r0) (hzx : (w.look h).zx = fo.zx) (n : ℕ) :
    Fl.tscIn (ztOf Q (ptsOf Q w (h ++ ds.take n))) Q.P.y.h.lt (nEndT Q.P.y) 1 G1
        (t.drop (k4StartAt Q 2)) =
      some (tT, G1', t.drop (k4StartAt Q 2 + (Q.P.y.h.lt + 3))) := by
  have c3 := L.c3
  rw [at_s2, at_b3] at c3
  rw [at_zt w h L ds hh hzx n, L.ztF]
  exact c3

/-! ## 3 The row at the summand 0, and the form -/

/-- **The row that the hearing makes of the sumcheck, at the summand 0 and with nothing kept, is
worth minus the first challenge times the job's summand on the end values as `maskedEnds` writes
them.** F0: the ledger in front of the claimed sum's laying. Fz: a later ledger at which the
sumcheck's own slots are laid. -/
theorem terms_row (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (termsSum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (F0 : Fork) (Wd : World GE)
    (hd : drawsOk ((termsSum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (termsSum Q)) c st seen ds = some rounds)
    (hs : ∀ i, i < ownSlots ((termsSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (F0.next + 1 + i) = hidingCoin c i)
    (j : Job) (hj : jobTerms Q st.input (ptsOf Q st.input st.heard) = some j)
    (hfitJ : k4JobFits (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)) j = true)
    (hnE : 1 ≤ nEndT Q.P.y)
    (hσ : (Aff.slot F0.next).value Reading.gl Wd = Reading.gl.val j.cube.total)
    (hP : ∀ rs, rs.length = Q.P.y.h.lt →
      PolyOn j.dY fun y => j.atEnds rs (maskedEnds (j.ends rs) (endRun c) y))
    (hA : ∀ rs, rs.length = Q.P.y.h.lt → ReadsAlike (j.atEnds rs))
    (hE : ∀ rs, rs.length = Q.P.y.h.lt →
      Reading.gl.val (j.atEnds rs (j.ends rs)) = Reading.gl.val (j.cube.summandAt rs))
    {tp u : Tape} {G2 : Fork} {o : Tsc}
    (hF : Fl.tscIn (ztOf Q (ptsOf Q st.input st.heard)) Q.P.y.h.lt (nEndT Q.P.y) 1 F0 tp =
      some (o, G2, u))
    (hS : Sized F0) (hT : TapeIs tp rounds) (Fz F1 : Fork) (hL : Fo.Later G2 Fz) (hSz : Sized Fz)
    (hW : Fz.hideRun o.p.first (Array.replicate o.p.walk.1.length zeroE) (subE zeroE oneE) =
      some F1) :
    (o.p.rowForm zeroE {}).value Reading.gl Wd =
      -(Reading.gl.val o.p.eps * Reading.gl.val (j.atEnds (o.r.toList)
        (maskedEnds (j.ends o.r.toList) (endRun c) (o.p.r.toList.getD Q.P.y.h.lt zeroE)))) := by
  obtain ⟨hn, _, _, _, hdY, hel⟩ := terms_parts hj
  obtain ⟨hle, T, cl, mu0, eps, rs, sentY, beta, w0, wY, wV, ms, y, v1, v, F, ht, _, _, _, _,
    hv1, _, _, hG0', _, a1, _, _, _, _, hpr, _, _, _, _, _, hor, _⟩ := tscIn_tape hF
  have ecl : tapeCl tp = cl := by
    rw [ht]
    rfl
  have hG0 : ({ F0 with next := F0.next + 1 } : Fork).hideRun F0.next #[tapeCl tp] oneE =
      some F := by
    rw [ecl, ← hv1]
    exact hG0'
  have hF1 : Sized ({ F0 with next := F0.next + 1 } : Fork) := hS
  have hnext : F.next = F0.next + 1 := (OnBytes.PscRun.hideRun_ok _ F _ _ _ hF1 hG0).1.next
  have hk := terms_weights Q st.input (frontOf st seen) j hj
  obtain ⟨h, G, hh, hf⟩ := k4_hears (V := V) name endName (termsSum Q) c st seen ds rounds
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
  rw [tsc_row_worth Reading.gl Wd hF hS hG0 _ hk hh hT,
    k4_rowForm_worth (V := V) name endName (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y))
      (fun w fr => jobTerms Q w (ptsOf Q w fr.heard)) c st seen ds rounds (Aff.slot F0.next) F G h
      zeroE {} Wd j ⟨1, nEndT Q.P.y⟩ hd ha hh (by rw [hf, hnext]; exact hs) hσ hj
      (jobFits_parts hfitJ) rfl (by rw [hdY]; norm_num) (hel _)
      (by rw [hr1]; exact hP _ hol) (by rw [hr1]; exact hA _ hol) (by rw [hr1]; exact hE _ hol),
    hr1, hr2, ← hSL.eps, Reading.gl.zero, Aff.value_empty]
  ring

/-- **THE FORM IS WORTH THE JOB's SUMMAND ON THE END VALUES AS `maskedEnds` WRITES THEM**, from the
hearing as a whole. -/
theorem terms_KT (h : List Fmt.Drawn)
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
    (j : Job) (hj : jobTerms Q st.input (ptsOf Q st.input st.heard) = some j)
    (hfitJ : k4JobFits (k4TokenShape Q.P.y.h.lt 1 (nEndT Q.P.y)) j = true)
    (hnE : 1 ≤ nEndT Q.P.y)
    (hσ : (Aff.slot G1.next).value Reading.gl Wd = Reading.gl.val j.cube.total)
    (hP : ∀ rs, rs.length = Q.P.y.h.lt →
      PolyOn j.dY fun y => j.atEnds rs (maskedEnds (j.ends rs) (endRun c) y))
    (hA : ∀ rs, rs.length = Q.P.y.h.lt → ReadsAlike (j.atEnds rs))
    (hE : ∀ rs, rs.length = Q.P.y.h.lt →
      Reading.gl.val (j.atEnds rs (j.ends rs)) = Reading.gl.val (j.cube.summandAt rs))
    (hT : TapeIs (t.drop (k4StartAt Q 2)) rounds)
    (hW : G1'.hideRun tT.p.first (Array.replicate tT.p.walk.1.length zeroE) (subE zeroE oneE) =
      some G2)
    (hinv : Reading.gl.val (invE tT.p.eps) * Reading.gl.val tT.p.eps = 1) :
    o.H.KT.value Reading.gl Wd = Reading.gl.val (j.atEnds tT.r.toList
      (maskedEnds (j.ends tT.r.toList) (endRun c) (tT.p.r.toList.getD Q.P.y.h.lt zeroE))) := by
  have c3 := call_terms st.input h L ds hh hzx (k4StartAt Q 2)
  rw [← hst] at c3
  have hrow := terms_row (V := V) name endName Q c st seen dp rounds G1 Wd hd ha hs j hj hfitJ hnE
    hσ hP hA hE c3 L.s1 hT G1' G2 (Fo.Later.refl _) L.s1' hW
  rw [led_KT L, Aff.value_scale, gl_neg, hrow]
  linear_combination (Reading.gl.val (j.atEnds tT.r.toList
    (maskedEnds (j.ends tT.r.toList) (endRun c) (tT.p.r.toList.getD Q.P.y.h.lt zeroE)))) * hinv

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4Sum_terms
#print axioms ProofFile.Honest.K4.terms_parts
#print axioms ProofFile.Honest.K4.terms_weights
#print axioms ProofFile.Honest.K4.led_KT
#print axioms ProofFile.Honest.K4.call_terms
#print axioms ProofFile.Honest.K4.terms_row
#print axioms ProofFile.Honest.K4.terms_KT
