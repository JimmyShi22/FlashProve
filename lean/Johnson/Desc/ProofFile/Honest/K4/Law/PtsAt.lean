-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/PtsAt.lean: CONDITIONAL. Statements with their proofs; no
definition.

What is here. THE SAMPLED VALUES THAT THE HONEST PARTS OF THE FEED-FORWARD LAYERS' ROUNDS READ ARE
THOSE THAT THE VERIFIER HAS HEARD; AND THE VERIFIER HAS RUN FOUR FLAT FUNCTIONS AT THE MAKERS'
LETTERS. Where the hearing has returned o (the library's `LedG`, Johnson/Road/K4/OwnLedgersG.lean)
on a tape that has sampled what the sub-protocol's own challenges ds hold, each field of `ptsOf` at
the challenges h in front and the first n of ds, but fo, om and rhoW, is o's field, or the letter by
which `LedG` names it (rt: tT.r; r14: hd2.r), or, for the two points that o does not hold (rhoI,
rhoM), what the tape's round has sampled: AT EVERY n FROM THE FIELD's OWN ROUND ON; and the squares'
level, the row products' token sumcheck and the two gated products' levels have run at the point,
the powers and the numbers that the honest makers lay at such a prefix.

  `innerAt_eq`, `levelR_eq`, `drawnE_take_length`   a run of challenges once all are heard; the two
     texts of a level's point; as many first elements as challenges
  `at_look`, `at_zt`, `at_PV`, `at_ZE`, `at_tkh`, `at_gp`, `at_omV`, `at_rhoI`, `at_rhoM`   **the
     points and powers**
  `at_r6`, `at_rtV`, `at_rt`, `at_rs`, `at_r12`, `at_r14`   **the sumchecks' points of challenges**
  `call_squares`, `call_rows`, `call_gated`, `call_gated2`   **the four flat functions at the
     makers' letters**

Limits. Premises: `LedG`; THE TAPE HAS SAMPLED WHAT THE CHALLENGES HOLD (`DrawnIs`, PtsNorms.lean);
as many challenges stand in front of the sub-protocol as the public data say; ds reaches the field's
round and beyond, as PtsHear.lean's statements ask (PV, gp, omV: the row products' first round; the
embedding's two: three challenges; each point of challenges: the next sumcheck's first round); for
the lookup's token point, and so for the first gated product's level: THE LOOKUP's POINT IN WHAT THE
INPUT's READER OF THE LOOKUP RETURNS AT h IS THE ONE IN WHAT THE HEARING WAS HANDED: that one field,
and no other, is asked. THAT THE WHOLE OF WHAT THE READER RETURNS IS WHAT THE HEARING WAS HANDED IS
ASKED BY NO STATEMENT OF THIS FILE. ON THREE AND ON SIX OF ITS FIELDS there are sentences that tie
them to what the verifier's state holds of the lookup (`K4LookTieAt`, `K4LookWideAt`,
Law/ScriptAt.lean) and statements that end in them, each conditional: `lookTie_head`
(Law/W/LookTieHead.lean), `lookTie_k3` (Law/LookPtsHead.lean), `lookWide_k3`
(Law/LookOpenHead.lean), `lookTie_all_head` (Law/OwnItemHead.lean): FIVE FILES THAT ARE NO PART OF
THE LIBRARY YET. The embedding's two points: in the first group of layers alone. NOT HERE: the two
fields of powers om and rhoW. Equations between machine words. No prover's message is named.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsHear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE)
open OnBytes.Model (Fork Level Tsc Aff powers orderDefault orderRange ledNS ledNP ledNO lastOf
  Forest.Heard)
open OnBytes.Model.Layer (Own normsStart downFrom)
open OnBytes.K.Kc (Fl Tape)
open OnBytes.Desc.First.P1 (drawnOf)
open OnBytes.Desc.First.K4 (k0)
open OnBytes.Road.K4 (LedG ksOf)
open OnBytes.Desc.First.K4.Honest

/-! ## 1 Three tools -/

/-- A run of challenges, once all are heard: their first elements. -/
theorem innerAt_eq (own : List Fmt.Drawn) (s n : ℕ) (h : s + 1 + n ≤ own.length) :
    innerAt own s n = (drawnE ((own.drop (s + 1)).take n)).toArray := by
  have hs : (onesFrom own (s + 1) n).size = n := by
    simp only [onesFrom, List.size_toArray, List.length_map, List.length_take, List.length_drop]
    omega
  unfold innerAt whole
  rw [if_pos (by simpa using hs)]
  rfl

/-- The honest parts' text of a level's point of challenges is the library's, once all challenges
are there. -/
theorem levelR_eq (mu : ℕ) (order : List ℕ) (rs : List E) (hr : rs.length = mu) :
    levelR mu order rs.toArray =
      OnBytes.Desc.First.P1.levelR mu order rs (Array.replicate mu zeroE) := by
  have a := pointOf_front { n := mu, order := order, way := .plain, maps := #[], pairs := [] } rs hr
  have b := pointOf_levelR { n := mu, order := order, way := .plain, maps := #[], pairs := [] } rs
  exact a.symm.trans b

/-- As many first elements as challenges. -/
theorem drawnE_take_length (ds : List Fmt.Drawn) (s n : ℕ) (h : s + n ≤ ds.length) :
    (drawnE ((ds.drop s).take n)).length = n := by
  simp only [drawnE, List.length_map, List.length_take, List.length_drop]
  omega

/-! ## 2 The fields -/

variable {Q : K4Pub} {tk : Array Nat} {t : Tape} {fo : Forest.Heard} {o : Own} {F G : Fork}
  {u : Tape} {H1 : OnBytes.Model.Layer.Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape} (w : K4In) (h : List Fmt.Drawn)

/-- What the honest parts take for the lookup's sampled values: what the input's reader of the
lookup returns at the challenges in front. No verifier is named. -/
theorem at_look (ds : List Fmt.Drawn) (hh : h.length = Q.r0) (n : ℕ) :
    (ptsOf Q w (h ++ ds.take n)).fo = w.look h := by
  rw [pts_fo_val, ← hh, List.take_left]

/-- The lookup's token point: of what the reader of the lookup returns it reads the point alone. -/
theorem at_zt
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hh : h.length = Q.r0) (hzx : (w.look h).zx = fo.zx) (n : ℕ) :
    ztOf Q (ptsOf Q w (h ++ ds.take n)) = o.H.ztF := by
  unfold ztOf
  rw [pts_fo_val, ← hh, List.take_left, hzx, led_ztF L]
  rfl

theorem at_PV
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 1 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : 0 < n) : (ptsOf Q w (h ++ ds.take n)).PV = o.H.PV := by
  rw [pts_PV_val, own_take Q h ds hh, elemsAt_take ds 0 n hn, (led_norms L ds hD hl).1]

theorem at_gp
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 1 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : k0 Q.g < n) :
    (ptsOf Q w (h ++ ds.take n)).gp = o.H.gp := by
  rw [pts_gp_val, own_take Q h ds hh, powersAt_take ds _ _ n hn, (led_norms L ds hD hl).2.1]

theorem at_omV
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 1 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : k4StartAt Q 1 ≤ n) :
    (ptsOf Q w (h ++ ds.take n)).omV = o.H.omV := by
  have s1 : k4StartAt Q 1 = k0 Q.g + 2 + (Q.P.rd.muV + 5) := rfl
  rw [pts_omV_val, own_take Q h ds hh, powersAt_take ds _ _ n (by omega),
    (led_norms L ds hD hl).2.2]

theorem at_ZE
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : 3 ≤ ds.length)
    (hg : (Q.g == 0) = true) (hh : h.length = Q.r0) (n : ℕ) (hn : 1 < n) :
    (ptsOf Q w (h ++ ds.take n)).ZE = o.H.ZE := by
  rw [pts_ZE_val, if_pos hg, own_take Q h ds hh, elemsAt_take ds 1 n hn, (led_ZE L ds hD hl hg).1]

theorem at_tkh
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : 3 ≤ ds.length)
    (hg : (Q.g == 0) = true) (hh : h.length = Q.r0) (n : ℕ) (hn : 2 < n) :
    (ptsOf Q w (h ++ ds.take n)).tkh = o.H.tkh := by
  rw [pts_tkh_val, if_pos hg, own_take Q h ds hh, elemsAt_take ds 2 n hn, (led_ZE L ds hD hl hg).2]

/-- The point on the norms' numbers: no field of what the verifier has heard holds it; the library
writes it off the tape. -/
theorem at_rhoI (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 0 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : k4StartAt Q 0 ≤ n) :
    (ptsOf Q w (h ++ ds.take n)).rhoI = (drawnOf ((t.drop (k0 Q.g)).drop 1)).toArray := by
  have s0 : k4StartAt Q 0 = k0 Q.g + 2 := rfl
  rw [pts_rhoI_val, own_take Q h ds hh, elemsAt_take ds _ n (by omega),
    OnBytes.Desc.First.K4.drop_drop', hD.elems (by omega)]
  congr 1

/-- The newly drawn point of the layer bits: likewise. -/
theorem at_rhoM (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 5 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : k4StartAt Q 5 ≤ n) :
    (ptsOf Q w (h ++ ds.take n)).rhoM =
      (drawnOf ((((ksOf { Q.P with tokv := tk } Q.hp).tc5 (t.drop (k0 Q.g))).drop
        (Q.P.rd.muH + 3)).drop 1)).toArray := by
  have s5 : k4StartAt Q 5 = k4StartAt Q 4 + (Q.P.rd.muH + 5) := rfl
  rw [pts_rhoM_val, own_take Q h ds hh, elemsAt_take ds _ n (by omega), led_rhoM ds hD hl]

theorem at_r6
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 1 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : k4StartAt Q 0 + 1 + Q.P.rd.muV ≤ n) :
    (ptsOf Q w (h ++ ds.take n)).r6 = o.H.wpl.r := by
  have s1 : k4StartAt Q 1 = k4StartAt Q 0 + (Q.P.rd.muV + 5) := rfl
  rw [pts_r6_val, own_take Q h ds hh, innerAt_take ds _ _ n hn, innerAt_eq ds _ _ (by omega),
    levelR_eq _ _ _ (drawnE_take_length ds _ _ (by omega)), led_r6 L ds hD hl]

theorem at_rtV
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 2 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : k4StartAt Q 1 + 1 + Q.P.y.h.lt ≤ n) :
    (ptsOf Q w (h ++ ds.take n)).rtV = o.H.tV.r := by
  have s2 : k4StartAt Q 2 = k4StartAt Q 1 + (Q.P.y.h.lt + 3) := rfl
  rw [pts_rtV_val, own_take Q h ds hh, innerAt_take ds _ _ n hn, innerAt_eq ds _ _ (by omega),
    led_rtV L ds hD hl]

theorem at_rt
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 3 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : k4StartAt Q 2 + 1 + Q.P.y.h.lt ≤ n) :
    (ptsOf Q w (h ++ ds.take n)).rt = tT.r := by
  have s3 : k4StartAt Q 3 = k4StartAt Q 2 + (Q.P.y.h.lt + 4) := rfl
  rw [pts_rt_val, own_take Q h ds hh, innerAt_take ds _ _ n hn, innerAt_eq ds _ _ (by omega),
    led_rt L ds hD hl]

theorem at_rs
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 4 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : k4StartAt Q 3 + 1 + Q.hp.lamS ≤ n) :
    (ptsOf Q w (h ++ ds.take n)).rs = o.K.rs := by
  have s4 : k4StartAt Q 4 = k4StartAt Q 3 + (Q.hp.lamS + 3) := rfl
  rw [pts_rs_val, own_take Q h ds hh, innerAt_take ds _ _ n hn, innerAt_eq ds _ _ (by omega),
    led_rs L ds hD hl]

theorem at_r12
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 5 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : k4StartAt Q 4 + 1 + Q.P.rd.muH ≤ n) :
    (ptsOf Q w (h ++ ds.take n)).r12 = o.hd.r := by
  have s5 : k4StartAt Q 5 = k4StartAt Q 4 + (Q.P.rd.muH + 5) := rfl
  rw [pts_r12_val, own_take Q h ds hh, innerAt_take ds _ _ n hn, innerAt_eq ds _ _ (by omega),
    levelR_eq _ _ _ (drawnE_take_length ds _ _ (by omega)), led_r12 L ds hD hl]

theorem at_r14
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 6 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : k4StartAt Q 5 + 1 + Q.P.rd.muH2 ≤ n) :
    (ptsOf Q w (h ++ ds.take n)).r14 = hd2.r := by
  have s6 : k4StartAt Q 6 = k4StartAt Q 5 + (Q.P.rd.muH2 + 5) := rfl
  rw [pts_r14_val, own_take Q h ds hh, innerAt_take ds _ _ n hn, innerAt_eq ds _ _ (by omega),
    levelR_eq _ _ _ (drawnE_take_length ds _ _ (by omega)), led_r14 L ds hD hl]

/-! ## 3 The four flat functions at the makers' letters -/

/-- **The squares' level**, at every prefix from its first round on. -/
theorem call_squares
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 1 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : k4StartAt Q 0 ≤ n) :
    ∃ v1, Fl.levelIn Q.P.rd.muV
        (normsStart Q.P.y 0 (ptsOf Q w (h ++ ds.take n)).gp (ptsOf Q w (h ++ ds.take n)).rhoI
          (ptsOf Q w (h ++ ds.take n)).PV).2
        (normsStart Q.P.y o.H.sW (ptsOf Q w (h ++ ds.take n)).gp
          (ptsOf Q w (h ++ ds.take n)).rhoI (ptsOf Q w (h ++ ds.take n)).PV).1
        (orderDefault Q.P.rd.muV) F4 (t.drop (k4StartAt Q 0)) = some (o.H.wpl, F7, v1) := by
  have s0 : k4StartAt Q 0 = k0 Q.g + 2 := rfl
  have s1 : k4StartAt Q 1 = k4StartAt Q 0 + (Q.P.rd.muV + 5) := rfl
  obtain ⟨v1, c1⟩ := L.c1
  rw [at_s0] at c1
  refine ⟨v1, ?_⟩
  rw [at_PV w h L ds hD hl hh n (by omega), at_gp w h L ds hD hl hh n (by omega),
    at_rhoI w h ds hD (by omega) hh n hn, L.kPV, L.kGp, L.kSW, L.kWpl]
  exact c1

/-- **The row products' token sumcheck.** -/
theorem call_rows
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 1 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : 0 < n) :
    ∃ v2, Fl.tscIn (ptsOf Q w (h ++ ds.take n)).PV Q.P.y.h.lt (ledNO Q.P.y.h.xl * Q.P.y.NI) 2 F8
        (t.drop (k4StartAt Q 1)) = some (o.H.tV, G1, v2) := by
  obtain ⟨v2, c2⟩ := L.c2
  rw [at_s1] at c2
  refine ⟨v2, ?_⟩
  rw [at_PV w h L ds hD hl hh n hn, L.kPV, L.kTV]
  exact c2

/-- **The first gated product's level**, at every prefix from its first round on. Of what the reader
of the lookup returns the lookup's point alone is asked to be the hearing's. -/
theorem call_gated
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 4 ≤ ds.length)
    (hh : h.length = Q.r0) (hzx : (w.look h).zx = fo.zx) (n : ℕ) (hn : k4StartAt Q 4 ≤ n) :
    ∃ v5, Fl.levelIn Q.P.rd.muH
        (downFrom (ptsOf Q w (h ++ ds.take n)).rs (Q.P.y.h.ll + Q.P.y.lPf) ++
          ztOf Q (ptsOf Q w (h ++ ds.take n))) (Aff.slot o.K.sH1) (orderRange Q.P.rd.muH) G3
        (t.drop (k4StartAt Q 4)) = some (o.hd, G3', v5) := by
  have s4 : k4StartAt Q 4 = k4StartAt Q 3 + (Q.hp.lamS + 3) := rfl
  obtain ⟨v5, c5⟩ := L.c5
  rw [at_s4, led_wD L] at c5
  refine ⟨v5, ?_⟩
  rw [at_rs w h L ds hD hl hh n (by omega), at_zt w h L ds hh hzx n]
  exact c5

/-- **The second gated product's level**, at every prefix from its first round on. -/
theorem call_gated2
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 5 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : k4StartAt Q 5 ≤ n) :
    Fl.levelIn Q.P.rd.muH2
        ((ptsOf Q w (h ++ ds.take n)).rhoM ++
          downFrom (ptsOf Q w (h ++ ds.take n)).rs Q.P.y.lfe ++ (ptsOf Q w (h ++ ds.take n)).rt)
        (OnBytes.Road.Rows.start2 Q.P.y.LamM o.K.sH1 (ptsOf Q w (h ++ ds.take n)).rhoM)
        (orderRange Q.P.rd.muH2) G3' (t.drop (k4StartAt Q 5)) =
      some (hd2, G4, t.drop (k4StartAt Q 5 + (Q.P.rd.muH2 + 4))) := by
  have s3 : k4StartAt Q 3 = k4StartAt Q 2 + (Q.P.y.h.lt + 4) := rfl
  have s4 : k4StartAt Q 4 = k4StartAt Q 3 + (Q.hp.lamS + 3) := rfl
  have s5 : k4StartAt Q 5 = k4StartAt Q 4 + (Q.P.rd.muH + 5) := rfl
  have c6 := L.c6
  rw [at_s5, at_b6] at c6
  rw [at_rs w h L ds hD (by omega) hh n (by omega), at_rt w h L ds hD (by omega) hh n (by omega),
    at_rhoM (tk := tk) w h ds hD hl hh n hn]
  exact c6

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.innerAt_eq
#print axioms ProofFile.Honest.K4.levelR_eq
#print axioms ProofFile.Honest.K4.drawnE_take_length
#print axioms ProofFile.Honest.K4.at_look
#print axioms ProofFile.Honest.K4.at_zt
#print axioms ProofFile.Honest.K4.at_PV
#print axioms ProofFile.Honest.K4.at_gp
#print axioms ProofFile.Honest.K4.at_omV
#print axioms ProofFile.Honest.K4.at_ZE
#print axioms ProofFile.Honest.K4.at_tkh
#print axioms ProofFile.Honest.K4.at_rhoI
#print axioms ProofFile.Honest.K4.at_rhoM
#print axioms ProofFile.Honest.K4.at_r6
#print axioms ProofFile.Honest.K4.at_rtV
#print axioms ProofFile.Honest.K4.at_rt
#print axioms ProofFile.Honest.K4.at_rs
#print axioms ProofFile.Honest.K4.at_r12
#print axioms ProofFile.Honest.K4.at_r14
#print axioms ProofFile.Honest.K4.call_squares
#print axioms ProofFile.Honest.K4.call_rows
#print axioms ProofFile.Honest.K4.call_gated
#print axioms ProofFile.Honest.K4.call_gated2
