-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/MergeLed.lean: CONDITIONAL.

What is here. What the merge of the feed-forward layers' rounds leaves (`Own.wo`), on the honest
part's rounds, from the hearing's return as a whole: at ONE list of claims and ONE prefix of the
challenges.

What is shown. There is one list of claims, the honest parts' at the merge's entry, such that: what
the merge leaves for the rows is made of that list and the powers at that entry; the value that the
merge shows reads as the library's function of the input's matrix at the merge's point, plus the
part's mask entry times the last challenge; the point has a coordinate for each column bit. The
joining of ClaimsAre.lean and MergeValue.lean. One statement and its proof, with two tools.

  `shape_ok`, `shape_unit`   a claim that passes the verifier's test on sizes
  `merge_value_led`   **what the merge leaves**

Limits. At the reading `Reading.gl`. Premises: the hearing returns, from a sized ledger, and its
return is opened in the letters of `LedG` (Johnson/Road/K4/OwnLedgersG.lean); the tape has sampled
what the challenges hold, and they reach the merge; as many challenges stand in front of the
sub-protocol as the public data say; of what the input's reader of the lookup returns at these, the
calls' points are those in what the hearing was handed (zk); the input's tokens are those laid in
the verifier's public data; the part stands at the merge's entry; the test `k4Fits` and the
challenges' shapes; the part, played alone, makes the rounds, which the tape holds; at a later sized
ledger the laying of the sumcheck's own slots returns; EVERY UNIT OF THE LAYOUT MEETS THE LIBRARY's
CONDITION `UnitOK` (public; the library has it of every layout that its maker returns: `ofLay_unit`,
Johnson/Top/H0/K11Caller/AtLay.lean). NO WORLD AND NO SLOT IS NAMED. The matrix is the one that the
part's input holds, at all its rows: that a commitment is to it, and that it reads 0 from some row
on, is not said. No example of the premises together is known. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.MergeValue
import Johnson.Desc.ProofFile.Honest.K4.Law.ClaimsAre
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatLed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE subE mulE)
open OnBytes.Model (Reading Fork Level Tsc WsLay WsClaim WsUnit wsClaimShape wsRowPart wsEpsT
  Forest.Heard)
open OnBytes.Model.Layer (Own)
open OnBytes.K.Kc (Tape)
open OnBytes.Road (UnitOK fmAt)
open OnBytes.Road.K4 (LedG)
open OnBytes.Desc.First.K4 (engFl hear)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.PtsLaw
open VerifiableInference.Desc.Part.MaskedSum hiding hear
open ProofFile.Honest.SumLaw

/-- A test that answers has the one answer. -/
theorem shape_ok {lay : WsLay} {c : WsClaim} (h : (wsClaimShape lay c).isOk = true) :
    wsClaimShape lay c = .ok () := by
  cases hc : wsClaimShape lay c with
  | ok a => rfl
  | error e =>
    rw [hc] at h
    cases h

/-- A claim that passes names a unit of the layout. -/
theorem shape_unit {lay : WsLay} {c : WsClaim} (h : wsClaimShape lay c = .ok ()) :
    ∃ u, lay.U[c.ui]? = some u := by
  unfold wsClaimShape at h
  cases hu : lay.U[c.ui]? with
  | some u => exact ⟨u, rfl⟩
  | none =>
    rw [hu] at h
    cases h

variable {V : Type} {Q : K4Pub} {tk : Array Nat} {t : Tape} {fo : Forest.Heard} {o : Own}
  {F G : Fork} {u : Tape} {H1 : OnBytes.Model.Layer.Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}

/-- **What the merge leaves, on the honest part's rounds.** Fz: a ledger later than the one that the
hearing leaves, at which the verifier lays the sumcheck's own slots. -/
theorem merge_value_led (h : List Fmt.Drawn)
    (hH : hear engFl { Q.P with tokv := tk } Q.hp Q.g fo F t = some (o, G, u))
    (hS : OnBytes.PscRun.Sized F)
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 6 ≤ ds.length)
    (hh : h.length = Q.r0) (name endName : String)
    (c : SumCoins name endName (mergeSum Q)) (st : State K4In Unit) (seen : Seen)
    (dp : List Fmt.Drawn) (rounds : List Fmt.RoundView)
    (hst : st.heard = h ++ ds.take (k4StartAt Q 6))
    (hzk : (st.input.look h).zk = fo.zk) (htk : st.input.tokv = tk)
    (hk : k4Fits Q (st.input.look h) st.input.tokv = true) (hf : OwnFits Q st.heard)
    (hd : drawsOk ((mergeSum Q).callAt st.input (frontOf st seen)) dp = true)
    (ha : alone (sumPart (V := V) name endName (mergeSum Q)) c st seen dp = some rounds)
    (hT : TapeIs (t.drop (k4StartAt Q 6)) rounds) (Fz F1 : Fork) (hL : Fo.Later G Fz)
    (hSz : OnBytes.PscRun.Sized Fz)
    (hW : Fz.hideRun o.wo.toWsMerged.p.first
      (Array.replicate o.wo.toWsMerged.p.walk.1.length zeroE) (subE zeroE oneE) = some F1)
    (hU : ∀ (i : ℕ) (u : WsUnit), Q.P.wsLay.U[i]? = some u → UnitOK Q.P.wsLay.lk u) :
    ∃ cls, mergeClaimsAt Q st.input (ptsOf Q st.input st.heard) = some cls ∧
      o.wo.recs = (cls.zip (ptsOf Q st.input st.heard).rhoW.toList).map (fun y =>
        wsRowPart Q.P.wsLay y.1 (mulE y.2 (wsEpsT Q.P.wsLay y.1 o.wo.rm))) ∧
      Reading.gl.val o.wo.fvp =
        fmAt Reading.gl Q.P.wsLay (wmOf st.input.w)
            (cls.zip (ptsOf Q st.input st.heard).rhoW.toList) o.wo.rm +
          Reading.gl.val ((endRun c).getD 0 zeroE) * Reading.gl.val o.wo.beta ∧
      o.wo.rm.size = Q.P.wsLay.lk := by
  obtain ⟨cl, c7⟩ := L.c7
  have e : u5.drop 1 = t.drop (k4StartAt Q 6) := by
    rw [L.u5d, at_b6, OnBytes.Desc.First.K4.drop_drop']
    rfl
  obtain ⟨cls, hc, hn, hrho, hsh⟩ := merge_run st.input hk st.heard hf
    (entry_len h ds st.heard 6 (by omega) hst hh hl)
    (entry_look h st.input ds st.heard _ hst hh)
  obtain ⟨cls', hc', _, hrecs⟩ := recs_are st.input h hH hS ds hD hl hh hzk htk (k4StartAt Q 6)
    (Nat.le_refl _)
  rw [← hst] at hc' hrecs
  obtain rfl : cls = cls' := Option.some.inj (hc.symm.trans hc')
  have hcl : ∀ c ∈ cls, ∃ u, Q.P.wsLay.U[c.ui]? = some u ∧
      wsClaimShape Q.P.wsLay c = .ok () ∧ UnitOK Q.P.wsLay.lk u := by
    intro c hcm
    have h1 := shape_ok (hsh c hcm)
    obtain ⟨u, hu⟩ := shape_unit h1
    exact ⟨u, hu, h1, hU _ u hu⟩
  exact ⟨cls, hc, hrecs,
    merge_value_win (V := V) name endName Q c st seen dp rounds G5 hd ha cls hc hcl
      (by rw [hn, hrho]) c7 L.sG5 (by rw [e]; exact hT) Fz F1 hL hSz hW,
    merge_rm_size c7⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.shape_ok
#print axioms ProofFile.Honest.K4.shape_unit
#print axioms ProofFile.Honest.K4.merge_value_led
