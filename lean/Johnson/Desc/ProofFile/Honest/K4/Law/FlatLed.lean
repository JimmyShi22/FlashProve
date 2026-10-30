-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FlatLed.lean: CONDITIONAL.

What is here. THE OWN CLAIMS OF FIVE MASKED SUMCHECKS OF THE FEED-FORWARD LAYERS' ROUNDS ARE WORTH 0
ON THE HONEST PARTS' ROUNDS, FROM THE VERIFIER's HEARING AS A WHOLE: the five statements of
FlatRun.lean with the flat functions' returns, their letters and their ledgers' sizes TAKEN OFF THE
HEARING's RETURN (the library's `LedG`, Johnson/Road/K4/OwnLedgersG.lean; PtsAt.lean beside this
file). Each ends in a field of the hypotheses `OwnFront`, `OwnBack` (Johnson/Road/K4/W/Join.lean) at
the hearing's own o. K4 has seven masked sumchecks: NOT HERE: the own claims of the second token
sumcheck and of the batched sumcheck (`OwnBack.stack`): `OwnFront`'s four fields are reached, of
`OwnBack`'s two the merge's alone. Statements and proofs.

K4 is the sub-protocol of the feed-forward layers' rounds.

  `entry_len`, `entry_look`   the part's state stands at the part's entry
  `squares_led`, `rows_led`, `gated_led`, `gated2_led`, `merge_led`   **the five**

Limits. At the reading `Reading.gl` alone. THE START IS A PREMISE OF EACH, AND IT IS THE JOB's OWN
CONTENT: the verifier's claimed form is worth the reading of the total of the cube of whatever job
the maker returns. The other premises: `LedG` (the library has it from the hearing's return at a
sized ledger); THE TAPE HAS SAMPLED WHAT K4's OWN CHALLENGES ds HOLD (`DrawnIs`) and they reach the
merge; as many challenges h stand in front as the public data say; THE PART's STATE HAS HEARD h AND
JUST THE CHALLENGES IN FRONT OF THE PART; the public test `k4Fits` accepts at what the input's
reader of the lookup returns at h and at the input's tokens; for the first gated product: the
lookup's point in what that reader returns is the one in what the hearing was handed (that field
alone); the challenges heard have the table's shape; the part's own challenges have the call's shape
and its moves answer; THE TAPE FROM THE PART's FIRST ROUND ON HOLDS WHAT THE PART's ROUNDS HOLD
(`TapeIs`); THE WORLD HOLDS THE PART's COINS from the sumcheck's first slot on; for the row products
and the merge: THE VERIFIER's LATER LAYING OF THE SUMCHECK's OWN SLOTS RETURNS, at a sized ledger
later than the one that the hearing leaves (FlatWindow.lean: ONE DIRECTION: FROM RETURNS: room is
moved, not paid; the like holds of `LedG`: all five statements stand behind a hearing that has
returned). For the row products besides: norms of five limbs, at least one norm, and sh IS WHAT THAT
LATER LEDGER SHOWS under the sumcheck's end slots. The merge's statement does not ask what the tape
has sampled. WHICH WORLD IS MEANT (at the row products and the merge: that of a ledger behind the
making of the row) and what is shown of the start (at the two gated products and the merge:
nothing): FlatTops.lean's head. No example of the premises together is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatRun
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatWindow
import Johnson.Desc.ProofFile.Honest.K4.Law.PtsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE subE)
open OnBytes.Model (Reading Aff Fork World Level Tsc WsClaim wsForkStart powers orderRange
  orderDefault ledNO Forest.Heard)
open OnBytes.Model.Layer (Own downFrom normsStart)
open OnBytes.Slice (GE)
open OnBytes.K.Kc (Fl Tape)
open OnBytes.Desc.First.P1 (tapeEps)
open OnBytes.Desc.First.K4 (rowsSummand mergeSlots)
open OnBytes.Road.K4 (LedG)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.PtsLaw
open VerifiableInference.Desc.Part.MaskedSum (ownSlots)
open ProofFile.Honest.SumLaw

variable {V : Type} {Q : K4Pub} {tk : Array Nat} {t : Tape} {fo : Forest.Heard} {o : Own}
  {F G : Fork} {u : Tape} {H1 : OnBytes.Model.Layer.Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape} (h : List Fmt.Drawn)

/-- A state that has heard h and the first challenges of ds up to masked sumcheck number k has heard
just as many of K4's own as stand in front of that sumcheck. -/
theorem entry_len (ds heard : List Fmt.Drawn) (k : ℕ) (hk : k < 7)
    (hst : heard = h ++ ds.take (k4StartAt Q k)) (hh : h.length = Q.r0)
    (hl : k4StartAt Q k ≤ ds.length) :
    (heard.drop Q.r0).length = (starts Q).getD k 0 := by
  rw [hst, own_take Q h ds hh, List.length_take, Nat.min_eq_left hl, starts_eq,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

/-- What the reader of the lookup returns there has its own lengths. -/
theorem entry_look (w : K4In) (ds heard : List Fmt.Drawn) (n : ℕ) (hst : heard = h ++ ds.take n)
    (hh : h.length = Q.r0) : LookSkel (w.look (heard.take Q.r0)) (w.look h) := by
  rw [hst, ← hh, List.take_left]
  exact lookSkel_refl _

/-- **The squares**: `OwnFront.squares`. -/
theorem squares_led
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 6 ≤ ds.length)
    (hh : h.length = Q.r0) (Wd : World GE) (name endName : String)
    (c : SumCoins name endName (squaresSum Q)) (st : State K4In Unit) (seen : Seen)
    (dp : List Fmt.Drawn) (rounds : List Fmt.RoundView)
    (hst : st.heard = h ++ ds.take (k4StartAt Q 0))
    (hk : k4Fits Q (st.input.look h) st.input.tokv = true) (hf : OwnFits Q st.heard)
    (hd : drawsOk ((squaresSum Q).callAt st.input (frontOf st seen)) dp = true)
    (ha : alone (sumPart (V := V) name endName (squaresSum Q)) c st seen dp = some rounds)
    (hs : ∀ i, i < ownSlots ((squaresSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (F4.next + i) = hidingCoin c i)
    (hσ : ∀ j, jobSquares Q st.input (ptsOf Q st.input st.heard) = some j →
      (normsStart Q.P.y o.H.sW (ptsOf Q st.input st.heard).gp (ptsOf Q st.input st.heard).rhoI
        (ptsOf Q st.input st.heard).PV).1.value Reading.gl Wd = Reading.gl.val j.cube.total)
    (hT : TapeIs (t.drop (k4StartAt Q 0)) rounds) :
    o.H.wpl.row.value Reading.gl Wd = 0 := by
  have m : k4StartAt Q 0 ≤ k4StartAt Q 1 ∧ k4StartAt Q 1 ≤ k4StartAt Q 6 := by
    simp only [k4StartAt]
    omega
  obtain ⟨v1, c1⟩ := call_squares st.input h L ds hD (by omega) hh (k4StartAt Q 0) (Nat.le_refl _)
  rw [← hst] at c1
  exact squares_at (V := V) name endName Q c st seen dp rounds _ F4 Wd _ hk hf
    (entry_len h ds st.heard 0 (by omega) hst hh (by omega))
    (entry_look h st.input ds st.heard _ hst hh) hd ha hs hσ c1 L.s4 hT

/-- **The row products**: `OwnFront.rowV`. Fz: a ledger later than the one that the hearing leaves,
at which the verifier lays the sumcheck's own slots. sh: the values that it shows under the
sumcheck's end slots. -/
theorem rows_led
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 6 ≤ ds.length)
    (hh : h.length = Q.r0) (Wd : World GE) (name endName : String)
    (c : SumCoins name endName (rowsSum Q)) (st : State K4In Unit) (seen : Seen)
    (dp : List Fmt.Drawn) (rounds : List Fmt.RoundView)
    (hst : st.heard = h ++ ds.take (k4StartAt Q 1))
    (hk : k4Fits Q (st.input.look h) st.input.tokv = true) (hf : OwnFits Q st.heard)
    (hd : drawsOk ((rowsSum Q).callAt st.input (frontOf st seen)) dp = true)
    (ha : alone (sumPart (V := V) name endName (rowsSum Q)) c st seen dp = some rounds)
    (hs : ∀ i, i < ownSlots ((rowsSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (F8.next + 1 + i) = hidingCoin c i)
    (hxl : Q.P.y.h.xl = 5) (hNI : 1 ≤ Q.P.y.NI)
    (hσ : ∀ j, jobRows Q st.input (ptsOf Q st.input st.heard) = some j →
      (Aff.slot F8.next).value Reading.gl Wd = Reading.gl.val j.cube.total)
    (hT : TapeIs (t.drop (k4StartAt Q 1)) rounds) (Fz F1 : Fork) (sh : Array E)
    (hL : Fo.Later G Fz) (hSz : OnBytes.PscRun.Sized Fz)
    (hW : Fz.hideRun o.H.tV.p.first (Array.replicate o.H.tV.p.walk.1.length zeroE)
      (subE zeroE oneE) = some F1)
    (hsh : ((Array.range (4 * Q.P.y.NI)).mapM fun i => Fz.shown (o.H.tV.sEnd + i)) = some sh) :
    (o.H.tV.p.rowForm (rowsSummand Q.P.y o.H sh) {}).value Reading.gl Wd = 0 := by
  have m : 0 < k4StartAt Q 1 ∧ k4StartAt Q 1 ≤ k4StartAt Q 6 := by
    simp only [k4StartAt]
    omega
  obtain ⟨v2, c2⟩ := call_rows st.input h L ds hD (by omega) hh (k4StartAt Q 1) m.1
  have hom := at_omV st.input h L ds hD (by omega) hh (k4StartAt Q 1) (Nat.le_refl _)
  rw [← hst] at c2 hom
  obtain ⟨j, hj, _⟩ := rows_run st.input hk st.heard hf
    (entry_len h ds st.heard 1 (by omega) hst hh (by omega))
    (entry_look h st.input ds st.heard _ hst hh)
  exact rows_win (V := V) name endName Q c st seen dp rounds F8 Wd hd ha hs j hj hxl hNI o.H
    hom.symm (hσ j hj) c2 L.s8 hT Fz F1 sh (L.g1.trans hL) hSz hW hsh

/-- **The first gated product**: `OwnFront.gated1`. -/
theorem gated_led
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 6 ≤ ds.length)
    (hh : h.length = Q.r0) (Wd : World GE) (name endName : String)
    (c : SumCoins name endName (gatedSum Q)) (st : State K4In Unit) (seen : Seen)
    (dp : List Fmt.Drawn) (rounds : List Fmt.RoundView)
    (hst : st.heard = h ++ ds.take (k4StartAt Q 4)) (hzx : (st.input.look h).zx = fo.zx)
    (hk : k4Fits Q (st.input.look h) st.input.tokv = true) (hf : OwnFits Q st.heard)
    (hd : drawsOk ((gatedSum Q).callAt st.input (frontOf st seen)) dp = true)
    (ha : alone (sumPart (V := V) name endName (gatedSum Q)) c st seen dp = some rounds)
    (hs : ∀ i, i < ownSlots ((gatedSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (G3.next + i) = hidingCoin c i)
    (hσ : ∀ tb, gatedTabs Q st.input = some tb →
      (Aff.slot o.K.sH1).value Reading.gl Wd =
        Reading.gl.val (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
          (downFrom (ptsOf Q st.input st.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++
            ztOf Q (ptsOf Q st.input st.heard)) tb).cube.total)
    (hT : TapeIs (t.drop (k4StartAt Q 4)) rounds) :
    o.hd.row.value Reading.gl Wd = 0 := by
  have m : k4StartAt Q 4 ≤ k4StartAt Q 6 := by
    simp only [k4StartAt]
    omega
  obtain ⟨v5, c5⟩ := call_gated st.input h L ds hD (by omega) hh hzx (k4StartAt Q 4)
    (Nat.le_refl _)
  rw [← hst] at c5
  exact gated_at (V := V) name endName Q c st seen dp rounds _ G3 Wd _ hk hf
    (entry_len h ds st.heard 4 (by omega) hst hh (by omega))
    (entry_look h st.input ds st.heard _ hst hh) hd ha hs hσ c5 L.s3 hT

/-- **The second gated product**: `OwnFront.gated2`. -/
theorem gated2_led
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hD : DrawnIs t ds) (hl : k4StartAt Q 6 ≤ ds.length)
    (hh : h.length = Q.r0) (Wd : World GE) (name endName : String)
    (c : SumCoins name endName (gated2Sum Q)) (st : State K4In Unit) (seen : Seen)
    (dp : List Fmt.Drawn) (rounds : List Fmt.RoundView)
    (hst : st.heard = h ++ ds.take (k4StartAt Q 5))
    (hk : k4Fits Q (st.input.look h) st.input.tokv = true) (hf : OwnFits Q st.heard)
    (hd : drawsOk ((gated2Sum Q).callAt st.input (frontOf st seen)) dp = true)
    (ha : alone (sumPart (V := V) name endName (gated2Sum Q)) c st seen dp = some rounds)
    (hs : ∀ i, i < ownSlots ((gated2Sum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (G3'.next + i) = hidingCoin c i)
    (hσ : ∀ tb, gatedTabs2 Q st.input = some tb →
      (OnBytes.Road.Rows.start2 Q.P.y.LamM o.K.sH1 (ptsOf Q st.input st.heard).rhoM).value
          Reading.gl Wd =
        Reading.gl.val (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
          ((ptsOf Q st.input st.heard).rhoM ++
            downFrom (ptsOf Q st.input st.heard).rs Q.P.y.lfe ++
            (ptsOf Q st.input st.heard).rt) tb).cube.total)
    (hT : TapeIs (t.drop (k4StartAt Q 5)) rounds) :
    ∀ o2, o.hd2 = some o2 → o2.row.value Reading.gl Wd = 0 := by
  intro o2 h2
  have e2 : o2 = hd2 := Option.some.inj (h2.symm.trans L.eHd2)
  have m : k4StartAt Q 5 ≤ k4StartAt Q 6 := by
    simp only [k4StartAt]
    omega
  have c6 := call_gated2 st.input h L ds hD (by omega) hh (k4StartAt Q 5) (Nat.le_refl _)
  rw [← hst] at c6
  rw [e2]
  exact gated2_at (V := V) name endName Q c st seen dp rounds _ G3' Wd _ hk hf
    (entry_len h ds st.heard 5 (by omega) hst hh (by omega))
    (entry_look h st.input ds st.heard _ hst hh) hd ha hs hσ c6 L.s3' hT

/-- **The merge**: `OwnBack.merge`. Fz: a ledger later than the one that the hearing leaves, at
which the verifier lays the sumcheck's own slots. -/
theorem merge_led
    (L : LedG { Q.P with tokv := tk } Q.hp Q.g fo o F G t u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4
      G5 u5)
    (ds : List Fmt.Drawn) (hl : k4StartAt Q 6 ≤ ds.length)
    (hh : h.length = Q.r0) (Wd : World GE) (name endName : String)
    (c : SumCoins name endName (mergeSum Q)) (st : State K4In Unit) (seen : Seen)
    (dp : List Fmt.Drawn) (rounds : List Fmt.RoundView)
    (hst : st.heard = h ++ ds.take (k4StartAt Q 6))
    (hk : k4Fits Q (st.input.look h) st.input.tokv = true) (hf : OwnFits Q st.heard)
    (hd : drawsOk ((mergeSum Q).callAt st.input (frontOf st seen)) dp = true)
    (ha : alone (sumPart (V := V) name endName (mergeSum Q)) c st seen dp = some rounds)
    (hs : ∀ i, i < ownSlots ((mergeSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (G5.next + i) = hidingCoin c i)
    (hσ : ∀ cls, mergeClaimsAt Q st.input (ptsOf Q st.input st.heard) = some cls →
      (wsForkStart (mergeSlots Q.hp Q.g o)
          (powers (tapeEps u5) (mergeSlots Q.hp Q.g o).size)).value Reading.gl Wd =
        Reading.gl.val
          (mergeJobOf Q.P.wsLay st.input.w cls (ptsOf Q st.input st.heard).rhoW).cube.total)
    (hT : TapeIs (t.drop (k4StartAt Q 6)) rounds) (Fz F1 : Fork) (hL : Fo.Later G Fz)
    (hSz : OnBytes.PscRun.Sized Fz)
    (hW : Fz.hideRun o.wo.toWsMerged.p.first
      (Array.replicate o.wo.toWsMerged.p.walk.1.length zeroE) (subE zeroE oneE) = some F1) :
    (o.wo.toWsMerged.p.rowForm o.wo.toWsMerged.fvp {}).value Reading.gl Wd = 0 := by
  obtain ⟨cl, c7⟩ := L.c7
  have e : u5.drop 1 = t.drop (k4StartAt Q 6) := by
    rw [L.u5d, at_b6, OnBytes.Desc.First.K4.drop_drop']
    rfl
  obtain ⟨cls, hc, _⟩ := merge_run st.input hk st.heard hf
    (entry_len h ds st.heard 6 (by omega) hst hh hl)
    (entry_look h st.input ds st.heard _ hst hh)
  exact merge_win (V := V) name endName Q c st seen dp rounds G5 Wd hd ha hs cls hc (hσ cls hc) c7
    L.sG5 (by rw [e]; exact hT) Fz F1 hL hSz hW

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.entry_len
#print axioms ProofFile.Honest.K4.entry_look
#print axioms ProofFile.Honest.K4.squares_led
#print axioms ProofFile.Honest.K4.rows_led
#print axioms ProofFile.Honest.K4.gated_led
#print axioms ProofFile.Honest.K4.gated2_led
#print axioms ProofFile.Honest.K4.merge_led
