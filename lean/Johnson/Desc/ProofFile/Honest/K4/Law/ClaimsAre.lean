-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ClaimsAre.lean: CONDITIONAL. Statements with their proofs; no
definition.

What is here. THE WEIGHT CLAIMS THAT THE HONEST PARTS OF THE FEED-FORWARD LAYERS' ROUNDS MERGE ARE
THE VERIFIER's. Where the verifier's hearing returns o on a tape that has sampled what the
sub-protocol's own challenges hold, the structure that the verifier's forms read (`Own.v`) is the
one that the honest parts make (`envOf`, Johnson/Desc/K4/Honest/Front.lean); the list of claims that
the hearing hands to the merge (`mergeClaims`, OnBytes/Desc/First/K4/MergeClaims.lean) is the honest
parts' list (`mergeClaimsAt`, Johnson/Desc/K4/Honest/Merge.lean); and what the merge leaves of each
claim (`WsForkOut.recs`) is written of that list, each claim with its power of the batching element
as the honest parts read it (`Pts.rhoW`).

  `env_is`, `claimEnv_is`   the structures that the forms and the claims read
  `claims_are`   **the list of claims**
  `ptsOf_look`, `claimsAt_input`   what that list reads of the input
  `mergeSlots_size`, `mergePow_at`, `recs_are`   **what the merge leaves of each claim**

Limits. Premises: the hearing RETURNS, from a sized ledger; THE TAPE HAS SAMPLED WHAT THE CHALLENGES
HOLD (`DrawnIs`, PtsNorms.lean), and they reach the merge; as many challenges stand in front of the
sub-protocol as the public data say; OF WHAT THE INPUT's READER OF THE LOOKUP RETURNS AT THESE, THE
CALLS' POINTS ARE THOSE IN WHAT THE HEARING WAS HANDED (one field: zk); THE INPUT's TOKENS ARE THOSE
LAID IN THE VERIFIER's PUBLIC DATA; the prefix that is read reaches the first gated product's level
(for `mergePow_at` and `recs_are`: the merge's first round). `mergeSlots_size` asks the hearing's
return alone. Equations between machine words. Nothing on any claim's value.

Kin. `mergeSlots_size` IS IN THE LIBRARY ALREADY, MORE GENERALLY: under the same name, at every
public data P where this one stands at { Q.P with tokv := tk }:
Johnson/Desc/K13/Honest/MergeLayersJoin.lean, of other writers; this file does not build on that
one.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsPow
import OnBytes.Desc.First.K4.HearPublic
import Johnson.Top.H0.MergeLaw.Pinned

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE mulE)
open OnBytes.Model (Fork WsClaim powers wsRowPart wsEpsT Forest.Heard)
open OnBytes.Model.Layer (Own)
open OnBytes.K.Kc (Tape)
open OnBytes.Desc.First.P1 (tapeEps)
open OnBytes.Desc.First.K4 (engFl hear hear_public mergeClaims mergeSlots)
open OnBytes.Road.K4 (own_ledG own_callsG)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc.First.MergeLaw (hear_ended hear_of_flat)

variable {Q : K4Pub} {tk : Array Nat} {t u : Tape} {fo : Forest.Heard} {o : Own} {F G : Fork}

/-- **The structure that the verifier's forms read is the one that the honest parts make**, at
sampled values whose calls' points are the hearing's. -/
theorem env_is (hH : hear engFl { Q.P with tokv := tk } Q.hp Q.g fo F t = some (o, G, u))
    (p : Pts) (hzk : p.fo.zk = fo.zk) : envOf Q p = some o.v := by
  obtain ⟨_, _, iU3, tab, laid, nU3, _, _, _, _, e3, _, e5, _, ev, _⟩ := hear_public hH
  have e5' : OnBytes.Model.Layer.layTables (matsOf Q)
      (OnBytes.Model.Layer.tableAsks Q.P.y Q.P.rd Q.g) 0 = some (tab, laid, nU3) := e5
  unfold envOf
  rw [e3, e5', ev, hzk]
  rfl

variable (w : K4In) (h : List Fmt.Drawn)

/-- The structure that the claims read, likewise. -/
theorem claimEnv_is (hH : hear engFl { Q.P with tokv := tk } Q.hp Q.g fo F t = some (o, G, u))
    (hS : OnBytes.PscRun.Sized F) (ds : List Fmt.Drawn) (hD : DrawnIs t ds)
    (hl : k4StartAt Q 4 ≤ ds.length) (hh : h.length = Q.r0) (hzk : (w.look h).zk = fo.zk) (n : ℕ)
    (hn : k4StartAt Q 4 ≤ n) :
    claimEnvOf Q (ptsOf Q w (h ++ ds.take n)) =
      some (OnBytes.Desc.First.K4.envOf { Q.P with tokv := tk } o) := by
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L⟩ := own_ledG hS hH
  have s3 : k4StartAt Q 3 = k4StartAt Q 2 + (Q.P.y.h.lt + 4) := rfl
  have s4 : k4StartAt Q 4 = k4StartAt Q 3 + (Q.hp.lamS + 3) := rfl
  unfold claimEnvOf
  rw [env_is hH _ (by rw [at_look w h ds hh n]; exact hzk),
    at_rs w h L ds hD hl hh n (by omega), at_rt w h L ds hD (by omega) hh n (by omega)]
  unfold OnBytes.Desc.First.K4.envOf
  rw [L.kTT]
  rfl

/-- **The list of claims that the hearing hands to the merge is the honest parts' list**, at every
prefix from the first gated product's level on. -/
theorem claims_are (hH : hear engFl { Q.P with tokv := tk } Q.hp Q.g fo F t = some (o, G, u))
    (hS : OnBytes.PscRun.Sized F) (ds : List Fmt.Drawn) (hD : DrawnIs t ds)
    (hl : k4StartAt Q 4 ≤ ds.length) (hh : h.length = Q.r0) (hzk : (w.look h).zk = fo.zk)
    (htk : w.tokv = tk) (n : ℕ) (hn : k4StartAt Q 4 ≤ n) (cl : Array WsClaim)
    (hc : mergeClaims { Q.P with tokv := tk } Q.g o = some cl) :
    mergeClaimsAt Q w (ptsOf Q w (h ++ ds.take n)) = some cl.toList := by
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L⟩ := own_ledG hS hH
  have hce := claimEnv_is w h hH hS ds hD hl hh hzk n hn
  have m : 3 ≤ k4StartAt Q 4 := by
    simp only [k4StartAt]
    omega
  unfold mergeClaims at hc
  obtain ⟨TS, hTS, hc⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨cp, hcp, hc⟩ := Option.bind_eq_some_iff.mp hc
  obtain ⟨ce, hce2, hc⟩ := Option.map_eq_some_iff.mp hc
  have hTS' : OnBytes.Model.Layer.callsTS Q.P = some TS := hTS
  have hp : panelClaims Q (ptsOf Q w (h ++ ds.take n)) = some cp := by
    unfold panelClaims
    rw [hce, hTS']
    exact hcp
  have he : (if Q.g == 0 then (embClaim Q w (ptsOf Q w (h ++ ds.take n))).map ([·])
      else some []) = some ce := by
    by_cases hg : (Q.g == 0) = true
    · rw [if_pos hg] at hce2 ⊢
      unfold embClaim
      rw [if_pos hg, hce, at_ZE w h L ds hD (by omega) hg hh n (by omega),
        at_tkh w h L ds hD (by omega) hg hh n (by omega), htk]
      exact hce2
    · rw [if_neg hg] at hce2 ⊢
      exact hce2
  subst hc
  unfold mergeClaimsAt
  rw [hp]
  by_cases hg : (Q.g == 0) = true
  · rw [if_pos hg] at he
    simp only [Option.bind_eq_bind, Option.bind_some, hg, if_true, he, Option.pure_def]
  · rw [if_neg hg] at he
    have e : ce = [] := (Option.some.inj he).symm
    simp only [Option.bind_eq_bind, Option.bind_some, hg, if_false, Bool.false_eq_true, e,
      Option.pure_def]

/-- The sampled values read, of the input, its reader of the lookup alone. -/
theorem ptsOf_look (Q : K4Pub) (w w' : K4In) (hl : w.look = w'.look) (hd : List Fmt.Drawn) :
    ptsOf Q w hd = ptsOf Q w' hd := by
  unfold ptsOf
  rw [hl]

/-- **The honest parts' list of claims reads, of the input, its reader of the lookup and its tokens
alone.** -/
theorem claimsAt_input (Q : K4Pub) (w w' : K4In) (hl : w.look = w'.look)
    (ht : w.tokv = w'.tokv) (hd : List Fmt.Drawn) :
    mergeClaimsAt Q w (ptsOf Q w hd) = mergeClaimsAt Q w' (ptsOf Q w' hd) := by
  rw [ptsOf_look Q w w' hl hd]
  unfold mergeClaimsAt embClaim
  rw [ht]

/-- **The merge's slots are as many as the plan counts claims.** -/
theorem mergeSlots_size (hH : hear engFl { Q.P with tokv := tk } Q.hp Q.g fo F t = some (o, G, u)) :
    (mergeSlots Q.hp Q.g o).size = Q.hp.NCL := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, G5, _, _, _, _, u5, cl, _, _, _, _, _, _, _, _, _, _,
    _, _, _, hsz, c7, _⟩ := own_callsG hH
  have hq := (VerifiableInference.Desc.First.MergeLaw.hear_tests (hear_of_flat c7)).1
  simp only [Bool.and_eq_true, beq_iff_eq] at hq
  rw [hq.2, hsz]

/-- The powers under which the honest parts batch the claims, off the tape's batching round. -/
theorem mergePow_at (hH : hear engFl { Q.P with tokv := tk } Q.hp Q.g fo F t = some (o, G, u))
    (hS : OnBytes.PscRun.Sized F) (ds : List Fmt.Drawn) (hD : DrawnIs t ds)
    (hl : k4StartAt Q 6 ≤ ds.length) (hh : h.length = Q.r0) (n : ℕ) (hn : k4StartAt Q 6 ≤ n) :
    (ptsOf Q w (h ++ ds.take n)).rhoW =
      powers (tapeEps (t.drop (k4StartAt Q 5 + (Q.P.rd.muH2 + 4)))) Q.hp.NCL := by
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, L⟩ := own_ledG hS hH
  rw [at_mergePow w h L ds hD hl hh n hn, L.u5e, at_b6]

/-- **What the merge leaves of each claim**, written of the honest parts' list of claims, each with
its power of the batching element as the honest parts read it. cls: that list. -/
theorem recs_are (hH : hear engFl { Q.P with tokv := tk } Q.hp Q.g fo F t = some (o, G, u))
    (hS : OnBytes.PscRun.Sized F) (ds : List Fmt.Drawn) (hD : DrawnIs t ds)
    (hl : k4StartAt Q 6 ≤ ds.length) (hh : h.length = Q.r0) (hzk : (w.look h).zk = fo.zk)
    (htk : w.tokv = tk) (n : ℕ) (hn : k4StartAt Q 6 ≤ n) :
    ∃ cls, mergeClaimsAt Q w (ptsOf Q w (h ++ ds.take n)) = some cls ∧ cls.length = Q.hp.NCL ∧
      o.wo.recs = (cls.zip (ptsOf Q w (h ++ ds.take n)).rhoW.toList).map fun y =>
        wsRowPart Q.P.wsLay y.1 (mulE y.2 (wsEpsT Q.P.wsLay y.1 o.wo.rm)) := by
  have m : k4StartAt Q 4 ≤ k4StartAt Q 6 := by
    simp only [k4StartAt]
    omega
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, G5, _, _, _, _, u5, cl, _, _, _, _, _, _, _, _, _, _,
    _, _, hc, hsz, c7, _, e5⟩ := own_callsG hH
  obtain ⟨x, mu, c, beta, v, T, r1, rY, rV, qs, _, _, et, _, _, _, _, _, _, _, hrec⟩ :=
    hear_ended (hear_of_flat c7)
  have ex : tapeEps u5 = x := by
    rw [et]
    rfl
  refine ⟨cl.toList, claims_are w h hH hS ds hD (by omega) hh hzk htk n (by omega) cl hc,
    by rw [Array.length_toList]; exact hsz, ?_⟩
  rw [mergePow_at w h hH hS ds hD hl hh n hn, ← at_b6 (tk := tk), ← e5, ex, hrec,
    mergeSlots_size hH, Array.toList_zip]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.env_is
#print axioms ProofFile.Honest.K4.claimEnv_is
#print axioms ProofFile.Honest.K4.claims_are
#print axioms ProofFile.Honest.K4.ptsOf_look
#print axioms ProofFile.Honest.K4.claimsAt_input
#print axioms ProofFile.Honest.K4.mergeSlots_size
#print axioms ProofFile.Honest.K4.mergePow_at
#print axioms ProofFile.Honest.K4.recs_are
