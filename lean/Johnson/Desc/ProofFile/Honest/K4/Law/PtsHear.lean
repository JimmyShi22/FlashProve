-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/PtsHear.lean: CONDITIONAL. Statements with their proofs; no
definition.

What is here. WHAT THE VERIFIER's HEARING OF THE FEED-FORWARD LAYERS' ROUNDS HOLDS, IN THE
CHALLENGES' OWN LETTERS. Where the hearing has returned o (in the form of the library's `LedG`,
Johnson/Road/K4/OwnLedgersG.lean: the calls on their named cuts of the tape, and the ledgers between
them) on a tape that has sampled what a list of challenges holds (`DrawnIs`, PtsNorms.lean beside
this file), each sampled value in o, or the letter by which `LedG` names it (tT.r, hd2.r), or, for
the newly drawn point of the layer bits, which o does not hold, what the tape's round has sampled,
is written of the challenge, or the run of challenges, whose number in the sub-protocol's own rounds
is written out: for the points and powers in the same letters in which PtsVals.lean writes the
honest parts' `ptsOf`; for the six points of challenges in the library's letters (`drawnE`,
`P1.levelR`), which PtsAt.lean ties to PtsVals.lean's (`innerAt_eq`, `levelR_eq`).

  `ks_tc1` … `ks_tcW`, `at_s0`, `at_s1`, `at_s2`, `at_b3`, `at_s4`, `at_join2`, `at_s5`,
     `at_b6`   the library's cuts of the tape, by the rounds' numbers: at_s‹k›: the first round of
     masked sumcheck number k; at_b3, at_b6: THE BATCHING ROUND ONE IN FRONT of sumcheck number 3, 6
  `led_norms`   the norms' stretch: PV, gp, omV
  `led_fo`, `led_ztF`, `led_ZE`   what the lookup has sampled; its token point; the embedding's two
     points
  `led_r6`, `led_rtV`, `led_rt`, `led_rs`, `led_r12`, `led_rhoM`, `led_r14`   **the sumchecks'
     points of challenges, and the newly drawn point**
  `led_sCl`   the slots of the two token sumchecks' claimed sums
  `led_wD`   the down product's panel has ll + lPf bits

Limits. Premises: `LedG` (the library's `own_ledG` has it from the hearing's return at a sized
ledger); THE TAPE HAS SAMPLED WHAT THE CHALLENGES HOLD; the challenges reach the field's round and
beyond (each point of challenges asks that they reach the next sumcheck's first round). The public
data are the honest parts', with any list of tokens laid. NOT HERE: the element that joins the two
claims in front of the batched sumcheck; the element that batches the merge's claims; the point that
joins in front of the squares' level (rhoI: PtsAt.lean's `at_rhoI` has it, of the tape's round).
`led_rhoM` has no premise `LedG` and names no field of o: that the verifier's second gated level ran
at that cut's elements is `LedG`'s own clause, not this statement's. Equations between machine
words. No prover's message is named.

Kin. `ks_tc1` … `ks_tcW` are general in the library's numbers (`Ks`) and in the round a. At the
plan's own numbers (`ksOf P hp`) and a := k0 g the same cuts are written a second time (here:
`at_s0` … `at_b6`, but `at_join2`), in those files' own names for the rounds: `tcP_drop`
(RowsLedger.lean) and `cuts` (SlotsUnder.lean) beside this file; both stand lower than this file and
unfold the library's cuts themselves.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsNorms
import Johnson.Road.K4.OwnLedgersG
import Johnson.Road.K4.OutTiesK
import OnBytes.Desc.First.K4.EmbTape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE)
open OnBytes.Model (Fork Level Tsc Aff powers orderDefault orderRange ledNS ledNP lastOf
  Forest.Heard)
open OnBytes.Model.Layer (Own)
open OnBytes.K.Kc (Fl Tape FlatRound)
open OnBytes.Desc.First.P1 (drawnOf msOf Ks plainWs)
open OnBytes.Desc.First.K4 (k0 engFl hearNorms hearNorms_calls hearTerms_keeps hearStack_tape
  hearNorms_emb_tape drawnAt drop_drop')
open OnBytes.Road.K4 (LedG ksOf stack_wD)
open OnBytes.Desc.First.K4.Honest

/-! ## 1 The library's cuts of the tape, by the rounds' numbers -/

/-- The library's six cuts of a tape from its round number a on, as one cut each. -/
theorem ks_tc1 (k : Ks) (t : Tape) (a : ℕ) : k.tc1 (t.drop a) = t.drop (a + 2) := by
  unfold Ks.tc1
  rw [drop_drop', drop_drop']

theorem ks_tcP (k : Ks) (t : Tape) (a : ℕ) : k.tcP (t.drop a) = t.drop (a + 2 + (k.k1 + 4)) := by
  unfold Ks.tcP
  rw [ks_tc1, drop_drop', drop_drop']

theorem ks_tc4 (k : Ks) (t : Tape) (a : ℕ) :
    k.tc4 (t.drop a) = t.drop (a + 2 + (k.k1 + 5) + (k.k2 + 3) + (k.k3 + 3)) := by
  unfold Ks.tc4
  rw [ks_tcP, drop_drop', drop_drop', drop_drop']
  congr 1
  omega

theorem ks_tc5 (k : Ks) (t : Tape) (a : ℕ) :
    k.tc5 (t.drop a) = t.drop (a + 2 + (k.k1 + 5) + (k.k2 + 3) + (k.k3 + 4) + (k.k4 + 3)) := by
  unfold Ks.tc5
  rw [ks_tc4, drop_drop', drop_drop']
  congr 1
  omega

theorem ks_tc6 (k : Ks) (t : Tape) (a : ℕ) :
    k.tc6 (t.drop a) =
      t.drop (a + 2 + (k.k1 + 5) + (k.k2 + 3) + (k.k3 + 4) + (k.k4 + 3) + (k.k5 + 5)) := by
  unfold Ks.tc6
  rw [ks_tc5, drop_drop', drop_drop', drop_drop']

theorem ks_tcW (k : Ks) (t : Tape) (a : ℕ) :
    k.tcW (t.drop a) = t.drop
      (a + 2 + (k.k1 + 5) + (k.k2 + 3) + (k.k3 + 4) + (k.k4 + 3) + (k.k5 + 5) + (k.k6 + 4)) := by
  unfold Ks.tcW
  rw [ks_tc6, drop_drop', drop_drop']

variable {Q : K4Pub} {tk : Array Nat} (t : Tape)

/-- The squares' level begins at its round "PSC epsilon". -/
theorem at_s0 : (ksOf { Q.P with tokv := tk } Q.hp).tc1 (t.drop (k0 Q.g)) =
    t.drop (k4StartAt Q 0) := ks_tc1 _ _ _

/-- So does the row products' token sumcheck. -/
theorem at_s1 : ((ksOf { Q.P with tokv := tk } Q.hp).tcP (t.drop (k0 Q.g))).drop 1 =
    t.drop (k4StartAt Q 1) := by
  rw [ks_tcP, drop_drop']
  rfl

/-- So does the second token sumcheck. -/
theorem at_s2 : (((ksOf { Q.P with tokv := tk } Q.hp).tcP (t.drop (k0 Q.g))).drop 1).drop
    (Q.P.y.h.lt + 3) = t.drop (k4StartAt Q 2) := by
  rw [at_s1, drop_drop']
  rfl

/-- The batched sumcheck's stretch begins one round in front of its round "PSC epsilon". -/
theorem at_b3 : (ksOf { Q.P with tokv := tk } Q.hp).tc4 (t.drop (k0 Q.g)) =
    t.drop (k4StartAt Q 2 + (Q.P.y.h.lt + 3)) := ks_tc4 _ _ _

/-- The first gated product's level. -/
theorem at_s4 : (ksOf { Q.P with tokv := tk } Q.hp).tc5 (t.drop (k0 Q.g)) =
    t.drop (k4StartAt Q 4) := ks_tc5 _ _ _

/-- The round that samples the newly drawn point stands one round in front of the second level. -/
theorem at_join2 : (((ksOf { Q.P with tokv := tk } Q.hp).tc5 (t.drop (k0 Q.g))).drop
    (Q.P.rd.muH + 3)).drop 1 = t.drop (k4StartAt Q 4 + (Q.P.rd.muH + 4)) := by
  rw [at_s4, drop_drop', drop_drop']

/-- The second gated product's level. -/
theorem at_s5 : (ksOf { Q.P with tokv := tk } Q.hp).tc6 (t.drop (k0 Q.g)) =
    t.drop (k4StartAt Q 5) := ks_tc6 _ _ _

/-- The merge's batching round stands one round in front of its round "PSC epsilon". -/
theorem at_b6 : (ksOf { Q.P with tokv := tk } Q.hp).tcW (t.drop (k0 Q.g)) =
    t.drop (k4StartAt Q 5 + (Q.P.rd.muH2 + 4)) := ks_tcW _ _ _

/-! ## 2 What the hearing holds -/

variable {t} {fo : Forest.Heard} {o : Own} {F G : Fork} {u : Tape}
  {H1 : OnBytes.Model.Layer.Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}

/-- **The norms' stretch.** -/
theorem led_norms
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 1 ≤ ds.length) :
    o.H.PV = elemsAt ds 0 ∧ o.H.gp = powersAt ds (k0 Q.g) (ledNS Q.P.y.h.xl) ∧
      o.H.omV = powersAt ds (k4StartAt Q 1 - 1) (ledNP Q.P.y.h.xl * Q.P.y.NI) := by
  obtain ⟨u1, hN, _⟩ := L.nt
  obtain ⟨a1, a2, a3, _⟩ := norms_vals hN ds hD hl
  exact ⟨by rw [L.kPV, a1], by rw [L.kGp, a2], by rw [L.kOmV, a3]⟩

/-- What the lookup has sampled is what the hearing was handed. -/
theorem led_fo
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5) :
    o.H.fo = fo := by
  obtain ⟨u1, hN, hT⟩ := L.nt
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, e⟩ := hearNorms_calls hN
  rw [(hearTerms_keeps hT).1, e]

/-- The lookup's token point: the last coordinates of its point. -/
theorem led_ztF
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5) :
    (lastOf fo.zx Q.P.y.h.lt).toOption = some o.H.ztF := by
  obtain ⟨u1, hN, _⟩ := L.nt
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, e, _⟩ :=
    hearNorms_calls hN
  rw [L.ztF]
  exact e

/-- The embedding's two points, in the first group of layers. -/
theorem led_ZE
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : 3 ≤ ds.length) (hg : (Q.g == 0) = true) :
    o.H.ZE = elemsAt ds 1 ∧ o.H.tkh = elemsAt ds 2 := by
  obtain ⟨u1, hN, hT⟩ := L.nt
  obtain ⟨a1, _, a3, _⟩ := hearNorms_emb_tape hN hg
  obtain ⟨_, _, k3, k4, _⟩ := hearTerms_keeps hT
  exact ⟨by rw [k3, a1]; exact hD.elems (n := 1) (by omega),
    by rw [k4, a3]; exact hD.elems (n := 2) (by omega)⟩

/-- **The squares' level.** -/
theorem led_r6
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 1 ≤ ds.length) :
    o.H.wpl.r = OnBytes.Desc.First.P1.levelR Q.P.rd.muV (orderDefault Q.P.rd.muV)
      (drawnE ((ds.drop (k4StartAt Q 0 + 1)).take Q.P.rd.muV))
      (Array.replicate Q.P.rd.muV zeroE) := by
  obtain ⟨v1, c1⟩ := L.c1
  rw [at_s0] at c1
  have s1 : k4StartAt Q 1 = k4StartAt Q 0 + (Q.P.rd.muV + 5) := rfl
  rw [L.kWpl, level_r_is c1 (ds.drop (k4StartAt Q 0)) (hD.drop _)
    (by rw [List.length_drop]; show Q.P.rd.muV + 1 ≤ _; omega), List.drop_drop]

/-- **The row products' token sumcheck.** -/
theorem led_rtV
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 2 ≤ ds.length) :
    o.H.tV.r = (drawnE ((ds.drop (k4StartAt Q 1 + 1)).take Q.P.y.h.lt)).toArray := by
  obtain ⟨v2, c2⟩ := L.c2
  rw [at_s1] at c2
  have s2 : k4StartAt Q 2 = k4StartAt Q 1 + (Q.P.y.h.lt + 3) := rfl
  rw [L.kTV, tsc_r_is c2 (ds.drop (k4StartAt Q 1)) (hD.drop _)
    (by rw [List.length_drop]; show Q.P.y.h.lt + 1 ≤ _; omega), List.drop_drop]

/-- The slots of the two token sumchecks' claimed sums: each is the next slot of the ledger from
which the sumcheck has run. -/
theorem led_sCl
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5) :
    o.H.tV.sCl = F8.next ∧ tT.sCl = G1.next := by
  obtain ⟨v2, c2⟩ := L.c2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, a, _⟩ :=
    OnBytes.Desc.First.P1.tscIn_tape c2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, b, _⟩ :=
    OnBytes.Desc.First.P1.tscIn_tape L.c3
  exact ⟨by rw [L.kTV]; exact a, b⟩

/-- **The second token sumcheck.** -/
theorem led_rt
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 3 ≤ ds.length) :
    tT.r = (drawnE ((ds.drop (k4StartAt Q 2 + 1)).take Q.P.y.h.lt)).toArray := by
  have c3 := L.c3
  rw [at_s2] at c3
  have s3 : k4StartAt Q 3 = k4StartAt Q 2 + (Q.P.y.h.lt + 4) := rfl
  rw [tsc_r_is c3 (ds.drop (k4StartAt Q 2)) (hD.drop _)
    (by rw [List.length_drop]; show Q.P.y.h.lt + 1 ≤ _; omega), List.drop_drop]

/-- **The batched sumcheck**: its challenges, the last first. -/
theorem led_rs
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 4 ≤ ds.length) :
    o.K.rs = (drawnE ((ds.drop (k4StartAt Q 3 + 1)).take Q.hp.lamS)).toArray.reverse := by
  have c4 := L.c4
  rw [at_b3] at c4
  obtain ⟨x, mu0, eps, beta, T, rs, sentY, vals, w1, wY, wV, C, Ga, ms, y, p, ht, hrs, _, _, _,
    hms, _, _, _, _, _, hK, _⟩ := hearStack_tape c4
  have s3 : k4StartAt Q 3 = k4StartAt Q 2 + (Q.P.y.h.lt + 4) := rfl
  have s4 : k4StartAt Q 4 = k4StartAt Q 3 + (Q.hp.lamS + 3) := rfl
  obtain ⟨more, hm⟩ : ∃ more, (t.drop (k4StartAt Q 2 + (Q.P.y.h.lt + 3))).drop 2 = rs ++ more :=
    ⟨_, by rw [ht]; rfl⟩
  have e2 : k4StartAt Q 2 + (Q.P.y.h.lt + 3) + 2 = k4StartAt Q 3 + 1 := by omega
  rw [drop_drop', e2] at hm
  have h1 : DrawnIs (rs ++ more) (ds.drop (k4StartAt Q 3 + 1)) := hm ▸ hD.drop _
  have e : o.K.rs.toList = (drawnE ((ds.drop (k4StartAt Q 3 + 1)).take Q.hp.lamS)).reverse := by
    rw [hK, hms, msOf_heads _ _ (by rw [plainWs, List.length_replicate, hrs]),
      heads_are rs more _ h1 (by rw [hrs, List.length_drop]; omega), hrs]
  apply Array.toList_inj.mp
  rw [e, Array.toList_reverse]

/-- The down product's panel has ll + lPf bits. -/
theorem led_wD
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5) :
    o.K.fin.wD = Q.P.y.h.ll + Q.P.y.lPf := stack_wD L.c4

/-- **The first gated product's level.** -/
theorem led_r12
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 5 ≤ ds.length) :
    o.hd.r = OnBytes.Desc.First.P1.levelR Q.P.rd.muH (orderRange Q.P.rd.muH)
      (drawnE ((ds.drop (k4StartAt Q 4 + 1)).take Q.P.rd.muH))
      (Array.replicate Q.P.rd.muH zeroE) := by
  obtain ⟨v5, c5⟩ := L.c5
  rw [at_s4] at c5
  have s5 : k4StartAt Q 5 = k4StartAt Q 4 + (Q.P.rd.muH + 5) := rfl
  rw [level_r_is c5 (ds.drop (k4StartAt Q 4)) (hD.drop _)
    (by rw [List.length_drop]; show Q.P.rd.muH + 1 ≤ _; omega), List.drop_drop]

/-- **The newly drawn point of the layer bits.** -/
theorem led_rhoM (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 5 ≤ ds.length) :
    (drawnOf ((((ksOf { Q.P with tokv := tk } Q.hp).tc5 (t.drop (k0 Q.g))).drop
      (Q.P.rd.muH + 3)).drop 1)).toArray = elemsAt ds (k4StartAt Q 5 - 1) := by
  have s5 : k4StartAt Q 5 = k4StartAt Q 4 + (Q.P.rd.muH + 5) := rfl
  rw [at_join2, hD.elems (by omega)]
  congr 1

/-- **The second gated product's level.** -/
theorem led_r14
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 6 ≤ ds.length) :
    hd2.r = OnBytes.Desc.First.P1.levelR Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
      (drawnE ((ds.drop (k4StartAt Q 5 + 1)).take Q.P.rd.muH2))
      (Array.replicate Q.P.rd.muH2 zeroE) := by
  have c6 := L.c6
  rw [at_s5] at c6
  have s6 : k4StartAt Q 6 = k4StartAt Q 5 + (Q.P.rd.muH2 + 5) := rfl
  rw [level_r_is c6 (ds.drop (k4StartAt Q 5)) (hD.drop _)
    (by rw [List.length_drop]; show Q.P.rd.muH2 + 1 ≤ _; omega), List.drop_drop]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.ks_tc1
#print axioms ProofFile.Honest.K4.ks_tcP
#print axioms ProofFile.Honest.K4.ks_tc4
#print axioms ProofFile.Honest.K4.ks_tc5
#print axioms ProofFile.Honest.K4.ks_tc6
#print axioms ProofFile.Honest.K4.ks_tcW
#print axioms ProofFile.Honest.K4.at_s0
#print axioms ProofFile.Honest.K4.at_s1
#print axioms ProofFile.Honest.K4.at_s2
#print axioms ProofFile.Honest.K4.at_b3
#print axioms ProofFile.Honest.K4.at_s4
#print axioms ProofFile.Honest.K4.at_join2
#print axioms ProofFile.Honest.K4.at_s5
#print axioms ProofFile.Honest.K4.at_b6
#print axioms ProofFile.Honest.K4.led_norms
#print axioms ProofFile.Honest.K4.led_fo
#print axioms ProofFile.Honest.K4.led_ztF
#print axioms ProofFile.Honest.K4.led_ZE
#print axioms ProofFile.Honest.K4.led_r6
#print axioms ProofFile.Honest.K4.led_rtV
#print axioms ProofFile.Honest.K4.led_sCl
#print axioms ProofFile.Honest.K4.led_rt
#print axioms ProofFile.Honest.K4.led_rs
#print axioms ProofFile.Honest.K4.led_wD
#print axioms ProofFile.Honest.K4.led_r12
#print axioms ProofFile.Honest.K4.led_rhoM
#print axioms ProofFile.Honest.K4.led_r14
