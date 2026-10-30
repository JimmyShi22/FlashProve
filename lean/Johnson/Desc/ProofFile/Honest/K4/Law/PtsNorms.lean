-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/PtsNorms.lean: CONDITIONAL. One definition, and statements with
their proofs.

What is here. THE SAMPLED VALUES THAT THE HONEST PARTS READ ARE THOSE THAT THE VERIFIER HAS HEARD,
IN THE NORMS' STRETCH OF THE FEED-FORWARD LAYERS' ROUNDS; AND THE VERIFIER RUNS ITS TWO FLAT
FUNCTIONS THERE AT THE MAKERS' LETTERS. Where the verifier's hearing of the norms' stretch returns
(`hearNorms`, OnBytes/Desc/First/K4/Hear.lean, at the flat engine) on a tape that has sampled what a
list of challenges holds, the fields PV, gp, omV of `ptsOf` (Johnson/Desc/K4/Honest/Front.lean) at
these challenges are the hearing's; the squares' product level and the row products' token sumcheck
have run at the point, the powers and the numbers that the honest makers lay; and the two sumchecks'
points of challenges are the challenges'.

  `DrawnIs`, `DrawnIs.drop`, `DrawnIs.at`, `DrawnIs.elems`   the tape has sampled what the
     challenges hold
  `msOf_heads`, `heads_are`   the first elements that a stretch of the tape's rounds sampled
  `level_r_is`, `tsc_r_is`   a level's and a token sumcheck's point of challenges
  `norms_vals`   what the hearing holds, in the challenges' letters, with the two returns
  `norms_PV`, `norms_gp`, `norms_omV`   **three fields, at every prefix from the field's round on**
  `norms_level_at`, `norms_tsc_at`   **the two flat functions at the makers' letters**
  `norms_r6`, `norms_rtV`   **the two points of challenges**

Limits. THE NORMS' STRETCH ALONE: nothing on the second token sumcheck, the batched sumcheck, the
gated products or the merge. OF `ptsOf`'s FIELDS: PV, gp, omV alone, and rhoI inside the level's
call; nothing on ZE, tkh; r6 and rtV are not named as fields (`norms_r6`, `norms_rtV` write the
hearing's points of the challenges; the tie is PtsAt.lean's `at_r6`, `at_rtV`). Premises: the
hearing RETURNS; THE TAPE HAS SAMPLED WHAT THE CHALLENGES HOLD (`DrawnIs`: round by round); as many
challenges stand in front of the sub-protocol as the public data say; the sub-protocol's own
challenges reach the field's round and beyond (all statements but `norms_rtV` ask that they reach
the row products' first round), and the prefix that is read reaches the field's round. The public
data are the honest parts', with any list of tokens laid. Equations between machine words. No
prover's message is named.

Kin. `DrawnIs` is the second clause of `TapeIs` (FlatCore.lean beside this file: what was sent and
what was sampled, at a view's rounds), written of the challenges alone; no statement here ties the
two. Other writers have a sentence of the same name on another matter: `DrawnIs`
(Johnson/Desc/K12/Law/DrawnOnto.lean): that a challenge fits its entry.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsVals
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatCore
import Johnson.Desc.ProofFile.Honest.K4.Law.SumPoints
import OnBytes.Desc.First.P1.TscLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE)
open OnBytes.Model (Fork Level Tsc Aff powers orderDefault ledNS ledNP ledNO Forest.Heard)
open OnBytes.Model.Layer (normsStart)
open OnBytes.K.Kc (Fl Tape FlatRound)
open OnBytes.Desc.First.P1 (drawnOf msOf levelIn_tape tscIn_tape levelWs tscWs drop_length_add)
open OnBytes.Desc.First.K4 (k0 engFl hearNorms hearNorms_tape drop_drop')
open OnBytes.Desc.First.K4.Honest

/-! ## 1 The tape has sampled what the challenges hold -/

/-- Round by round: the tape's round number n has sampled the elements of challenge number n. Where
the tape has no round of that number the challenge is asked to hold no element. Of a challenge the
elements alone are read; of the tape nothing behind the last challenge. -/
def DrawnIs (t : Tape) (ds : List Fmt.Drawn) : Prop :=
  ∀ (n : ℕ) (d : Fmt.Drawn), ds[n]? = some d → drawnOf (t.drop n) = d.elems.map E.ofTriple

/-- From round number k on. -/
theorem DrawnIs.drop {t : Tape} {ds : List Fmt.Drawn} (h : DrawnIs t ds) (k : ℕ) :
    DrawnIs (t.drop k) (ds.drop k) := by
  intro n d hn
  rw [List.getElem?_drop] at hn
  rw [drop_drop']
  exact h (k + n) d hn

/-- Where the tape's round number n is known, the challenge's elements are what it sampled. -/
theorem DrawnIs.at {t : Tape} {ds : List Fmt.Drawn} (h : DrawnIs t ds) {n : ℕ} {r : FlatRound}
    {u : Tape} (ht : t.drop n = r :: u) (hn : n < ds.length) : elemsAt ds n = r.drawn.toArray := by
  have e := h n ds[n] (List.getElem?_eq_getElem hn)
  rw [ht] at e
  have e' : r.drawn = ds[n].elems.map E.ofTriple := e
  unfold elemsAt
  rw [List.getElem?_eq_getElem hn, e']
  rfl

/-- What the tape's round number n sampled, as an array, is the challenge's elements. -/
theorem DrawnIs.elems {t : Tape} {ds : List Fmt.Drawn} (h : DrawnIs t ds) {n : ℕ}
    (hn : n < ds.length) : (drawnOf (t.drop n)).toArray = elemsAt ds n := by
  rw [h n ds[n] (List.getElem?_eq_getElem hn)]
  unfold elemsAt
  rw [List.getElem?_eq_getElem hn]
  rfl

/-- **The first elements that the tape's rounds rs sampled are the first elements of as many
challenges.** -/
theorem heads_are : ∀ (rs : List FlatRound) (more : Tape) (ds : List Fmt.Drawn),
    DrawnIs (rs ++ more) ds → rs.length ≤ ds.length →
    rs.map (fun r => r.drawn.headD zeroE) = drawnE (ds.take rs.length)
  | [], _, _, _, _ => rfl
  | _ :: _, _, [], _, hl => by simp at hl
  | r :: rs, more, d :: ds, h, hl => by
    have e0 : r.drawn = d.elems.map E.ofTriple := h 0 d rfl
    have ih := heads_are rs more ds (by
      have := h.drop 1
      exact this) (by simpa using hl)
    rw [List.map_cons, ih, e0, List.length_cons, List.take_succ_cons]
    show _ = ((d.elems.head?.map E.ofTriple).getD zeroE) :: drawnE (ds.take rs.length)
    congr 1
    cases d.elems <;> rfl

/-! ## 2 Two points of challenges -/

/-- The flat text's rounds under as many weights: their challenges. -/
theorem msOf_heads (ws : List OnBytes.Psc.Weight) (rs : List FlatRound)
    (h : ws.length = rs.length) :
    (msOf ws rs).map (·.2.2) = rs.map fun r => r.drawn.headD zeroE := by
  have e := congrArg (List.map (·.2)) (msOf_pairs ws rs h)
  rw [List.map_map, List.map_map] at e
  exact e

/-- **A product level's point of challenges**, of the challenges behind its first round. -/
theorem level_r_is {mu : ℕ} {rho : Array E} {C : Aff} {order : List ℕ} {F G : Fork} {t u : Tape}
    {L : Level} (hF : Fl.levelIn mu rho C order F t = some (L, G, u)) (ds : List Fmt.Drawn)
    (hD : DrawnIs t ds) (hl : mu + 1 ≤ ds.length) :
    L.r = OnBytes.Desc.First.P1.levelR mu order (drawnE ((ds.drop 1).take mu))
      (Array.replicate mu zeroE) := by
  obtain ⟨hom, T, mu0, eps, rs, sentY, beta, tau, w0, wY, wV, wT, ms, y, shL, shR, v, G1, p, ht,
    hrs, _, _, _, hms, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hLr, _⟩ := levelIn_tape hF
  obtain ⟨more, hm⟩ : ∃ more, t.drop 1 = rs ++ more := ⟨_, by rw [ht]; rfl⟩
  have h1 : DrawnIs (rs ++ more) (ds.drop 1) := hm ▸ hD.drop 1
  rw [hLr, hms, msOf_heads _ _ (by rw [levelWs, List.length_map, hom, hrs]),
    heads_are rs _ (ds.drop 1) h1 (by rw [hrs, List.length_drop]; omega), hrs]

/-- **A token sumcheck's point of challenges.** -/
theorem tsc_r_is {P : Array E} {lt n dY : ℕ} {F G : Fork} {t u : Tape} {o : Tsc}
    (hF : Fl.tscIn P lt n dY F t = some (o, G, u)) (ds : List Fmt.Drawn)
    (hD : DrawnIs t ds) (hl : lt + 1 ≤ ds.length) :
    o.r = (drawnE ((ds.drop 1).take lt)).toArray := by
  obtain ⟨hP, T, cl, mu0, eps, rs, sentY, beta, w0, wY, wV, ms, y, v1, v, G0, ht, hrs, _, hms, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hor, _⟩ := tscIn_tape hF
  have hlen : (P.toList.take lt).length = lt := by
    rw [List.length_take, Array.length_toList]
    exact Nat.min_eq_left hP
  rw [hlen] at hrs
  obtain ⟨more, hm⟩ : ∃ more, t.drop 1 = rs ++ more := ⟨_, by rw [ht]; rfl⟩
  have h1 : DrawnIs (rs ++ more) (ds.drop 1) := hm ▸ hD.drop 1
  have e : o.r.toList = drawnE ((ds.drop 1).take lt) := by
    rw [hor, hms, msOf_heads _ _ (by rw [tscWs, List.length_map, hlen, hrs]),
      heads_are rs _ (ds.drop 1) h1 (by rw [hrs, List.length_drop]; omega), hrs]
  rw [← e]

/-! ## 3 What the hearing holds, in the challenges' letters -/

variable {Q : K4Pub} {tk : Array Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
  {H : OnBytes.Model.Layer.Heard}

/-- **The norms' stretch, in the challenges' letters.** ds: the sub-protocol's own challenges; they
reach the row products' token sumcheck. -/
theorem norms_vals (hN : hearNorms engFl { Q.P with tokv := tk } Q.g fo F t = some (H, G, u))
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 1 ≤ ds.length) :
    H.PV = elemsAt ds 0 ∧ H.gp = powersAt ds (k0 Q.g) (ledNS Q.P.y.h.xl) ∧
      H.omV = powersAt ds (k4StartAt Q 1 - 1) (ledNP Q.P.y.h.xl * Q.P.y.NI) ∧
      H.PV.size = Q.P.y.h.lt ∧
      ∃ F4 F7 F8 : Fork,
        Fl.levelIn Q.P.rd.muV
            (normsStart Q.P.y H.sW H.gp (elemsAt ds (k4StartAt Q 0 - 1)) H.PV).2
            (normsStart Q.P.y H.sW H.gp (elemsAt ds (k4StartAt Q 0 - 1)) H.PV).1
            (orderDefault Q.P.rd.muV) F4 (t.drop (k4StartAt Q 0)) =
          some (H.wpl, F7, t.drop (k4StartAt Q 1 - 1)) ∧
        Fl.tscIn H.PV Q.P.y.h.lt (ledNO Q.P.y.h.xl * Q.P.y.NI) 2 F8 (t.drop (k4StartAt Q 1)) =
          some (H.tV, G, u) := by
  obtain ⟨F4, F7, F8, rhoI, vW, vP, gam, om, w0, wI, d0, dI, a1, a2, a3, a4, _, _, _, a8, a9, _,
    a11, a12, a13, _, _, _, a17, a18, _⟩ := hearNorms_tape hN
  have s0 : k4StartAt Q 0 = k0 Q.g + 2 := rfl
  have s1 : k4StartAt Q 1 = k0 Q.g + Q.P.rd.muV + 7 := by
    show k0 Q.g + 2 + (Q.P.rd.muV + 5) = _
    omega
  have b0 : elemsAt ds 0 = d0.toArray := hD.at (n := 0) a1 (by omega)
  have b1 : elemsAt ds (k0 Q.g) = #[gam] := hD.at (n := k0 Q.g) a4 (by omega)
  have b2 : elemsAt ds (k0 Q.g + 1) = dI.toArray := hD.at (n := k0 Q.g + 1) a9 (by omega)
  have b3 : elemsAt ds (k0 Q.g + Q.P.rd.muV + 6) = #[om] :=
    hD.at (n := k0 Q.g + Q.P.rd.muV + 6) a13 (by omega)
  have e0 : k4StartAt Q 0 - 1 = k0 Q.g + 1 := by omega
  have e1 : k4StartAt Q 1 - 1 = k0 Q.g + Q.P.rd.muV + 6 := by omega
  refine ⟨by rw [a3, b0], ?_, ?_, by rw [a3]; exact a2, F4, F7, F8, ?_, ?_⟩
  · rw [a8]
    unfold powersAt
    rw [b1]
    rfl
  · rw [a17, e1]
    unfold powersAt
    rw [b3]
    rfl
  · rw [e0, b2, ← a11, s0, e1]
    exact a12
  · rw [s1]
    exact a18

/-! ## 4 The fields, at every prefix from the field's round on -/

variable (w : K4In) (h : List Fmt.Drawn)

/-- **PV.** h: the challenges in front of the sub-protocol. n: how many of its own are read. -/
theorem norms_PV (hN : hearNorms engFl { Q.P with tokv := tk } Q.g fo F t = some (H, G, u))
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 1 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : 0 < n) : (ptsOf Q w (h ++ ds.take n)).PV = H.PV := by
  rw [pts_PV_val, own_take Q h ds hh, elemsAt_take ds 0 n hn, (norms_vals hN ds hD hl).1]

/-- **gp.** -/
theorem norms_gp (hN : hearNorms engFl { Q.P with tokv := tk } Q.g fo F t = some (H, G, u))
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 1 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : k0 Q.g < n) :
    (ptsOf Q w (h ++ ds.take n)).gp = H.gp := by
  rw [pts_gp_val, own_take Q h ds hh, powersAt_take ds _ _ n hn, (norms_vals hN ds hD hl).2.1]

/-- **omV.** -/
theorem norms_omV (hN : hearNorms engFl { Q.P with tokv := tk } Q.g fo F t = some (H, G, u))
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 1 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : k4StartAt Q 1 ≤ n) :
    (ptsOf Q w (h ++ ds.take n)).omV = H.omV := by
  have s1 : 0 < k4StartAt Q 1 := by
    show 0 < k0 Q.g + 2 + (Q.P.rd.muV + 5)
    omega
  rw [pts_omV_val, own_take Q h ds hh, powersAt_take ds _ _ n (by omega),
    (norms_vals hN ds hD hl).2.2.1]

/-- **The squares' product level has run at the makers' letters**: at the point that the honest
maker lays at every prefix from the level's first round on, and at the start form of the same
letters. -/
theorem norms_level_at (hN : hearNorms engFl { Q.P with tokv := tk } Q.g fo F t = some (H, G, u))
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 1 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : k4StartAt Q 0 ≤ n) :
    ∃ F4 F7 : Fork, Fl.levelIn Q.P.rd.muV
        (normsStart Q.P.y 0 (ptsOf Q w (h ++ ds.take n)).gp (ptsOf Q w (h ++ ds.take n)).rhoI
          (ptsOf Q w (h ++ ds.take n)).PV).2
        (normsStart Q.P.y H.sW (ptsOf Q w (h ++ ds.take n)).gp
          (ptsOf Q w (h ++ ds.take n)).rhoI (ptsOf Q w (h ++ ds.take n)).PV).1
        (orderDefault Q.P.rd.muV) F4 (t.drop (k4StartAt Q 0)) =
      some (H.wpl, F7, t.drop (k4StartAt Q 1 - 1)) := by
  have s0 : k4StartAt Q 0 = k0 Q.g + 2 := rfl
  obtain ⟨_, _, _, _, F4, F7, _, a, _⟩ := norms_vals hN ds hD hl
  refine ⟨F4, F7, ?_⟩
  rw [norms_PV w h hN ds hD hl hh n (by omega), norms_gp w h hN ds hD hl hh n (by omega),
    pts_rhoI_val, own_take Q h ds hh, elemsAt_take ds _ n (by omega)]
  exact a

/-- **The row products' token sumcheck has run at the makers' letters.** -/
theorem norms_tsc_at (hN : hearNorms engFl { Q.P with tokv := tk } Q.g fo F t = some (H, G, u))
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 1 ≤ ds.length)
    (hh : h.length = Q.r0) (n : ℕ) (hn : 0 < n) :
    ∃ F8 : Fork, Fl.tscIn (ptsOf Q w (h ++ ds.take n)).PV Q.P.y.h.lt
        (ledNO Q.P.y.h.xl * Q.P.y.NI) 2 F8 (t.drop (k4StartAt Q 1)) = some (H.tV, G, u) := by
  obtain ⟨_, _, _, _, _, _, F8, _, a⟩ := norms_vals hN ds hD hl
  exact ⟨F8, by rw [norms_PV w h hN ds hD hl hh n hn]; exact a⟩

/-! ## 5 The two points of challenges -/

/-- **The squares' level: its point of challenges is that of every cube of as many variables in the
order from the highest down, at the first elements of the challenges behind the level's first
round.** -/
theorem norms_r6 (hN : hearNorms engFl { Q.P with tokv := tk } Q.g fo F t = some (H, G, u))
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 1 ≤ ds.length) (c : Cube)
    (hc : c.n = Q.P.rd.muV) (ho : c.order = orderDefault Q.P.rd.muV) :
    c.pointOf (drawnE ((ds.drop (k4StartAt Q 0 + 1)).take Q.P.rd.muV)) = H.wpl.r := by
  obtain ⟨_, _, _, _, F4, F7, _, a, _⟩ := norms_vals hN ds hD hl
  have s1 : k4StartAt Q 1 = k4StartAt Q 0 + (Q.P.rd.muV + 5) := rfl
  rw [level_r_is a (ds.drop (k4StartAt Q 0)) (hD.drop _) (by rw [List.length_drop]; omega),
    pointOf_levelR, hc, ho, List.drop_drop]

/-- **The row products' token sumcheck: its point of challenges**, likewise. -/
theorem norms_rtV (hN : hearNorms engFl { Q.P with tokv := tk } Q.g fo F t = some (H, G, u))
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds)
    (hl : k4StartAt Q 1 + Q.P.y.h.lt + 1 ≤ ds.length) :
    (drawnE ((ds.drop (k4StartAt Q 1 + 1)).take Q.P.y.h.lt)).toArray = H.tV.r := by
  obtain ⟨_, _, _, _, _, _, F8, _, a⟩ := norms_vals hN ds hD (by omega)
  rw [tsc_r_is a (ds.drop (k4StartAt Q 1)) (hD.drop _) (by rw [List.length_drop]; omega),
    List.drop_drop]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.DrawnIs
#print axioms ProofFile.Honest.K4.DrawnIs.drop
#print axioms ProofFile.Honest.K4.DrawnIs.at
#print axioms ProofFile.Honest.K4.DrawnIs.elems
#print axioms ProofFile.Honest.K4.heads_are
#print axioms ProofFile.Honest.K4.msOf_heads
#print axioms ProofFile.Honest.K4.level_r_is
#print axioms ProofFile.Honest.K4.tsc_r_is
#print axioms ProofFile.Honest.K4.norms_vals
#print axioms ProofFile.Honest.K4.norms_PV
#print axioms ProofFile.Honest.K4.norms_gp
#print axioms ProofFile.Honest.K4.norms_omV
#print axioms ProofFile.Honest.K4.norms_level_at
#print axioms ProofFile.Honest.K4.norms_tsc_at
#print axioms ProofFile.Honest.K4.norms_r6
#print axioms ProofFile.Honest.K4.norms_rtV
