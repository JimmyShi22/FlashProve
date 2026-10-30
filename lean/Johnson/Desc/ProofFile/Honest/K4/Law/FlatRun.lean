-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FlatRun.lean: CONDITIONAL.

What is here. The five statements of FlatTops.lean UNDER THE PUBLIC TEST `k4Fits`
(Honest/K4/Part.lean): no premise on a maker is left: that each maker returns at the run, and that
the run's cube fits, comes from the test (SumAtRun.lean). Statements and proofs.

K4 is the sub-protocol of the feed-forward layers' rounds.

  `squares_at`, `rows_at`, `gated_at`, `gated2_at`, `merge_at`   **the five**

Limits. At the reading `Reading.gl` alone. THE START IS A PREMISE OF EACH, AND IT IS THE JOB's OWN
CONTENT: the claimed form is worth the reading of the total of the cube of whatever job the maker
returns. In the makers' stead: the test accepts, at the run's own tokens; K4's own challenges heard
at the part's entry have the shape of the verifier's table of rounds and are just as many as the
number of the part's round "PSC epsilon" in the table (`starts`; that this is the number of moves in
front of the part is not typed: StartsAre.lean's head); what the lookup in front has sampled has the
public numbers and the lengths of that at which the test was asked (`LookSkel`). All other premises
are those of FlatTops.lean, whose head says what each is and where the world that is meant stands.
No example of the premises together is known. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatTops
import Johnson.Desc.ProofFile.Honest.K4.Law.SumAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE oneE)
open OnBytes.Model (Reading Aff Fork World Level Tsc WsClaim WsForkOut wsForkStart powers
  orderRange orderDefault ledNO)
open OnBytes.Model.Layer (downFrom normsStart)
open OnBytes.Slice (GE)
open OnBytes.K.Kc (Fl Tape flatForkEnd)
open OnBytes.Desc.First.P1 (tapeEps)
open OnBytes.Desc.First.K4 (rowsSummand)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.PtsLaw
open VerifiableInference.Desc.Part.MaskedSum (ownSlots)
open ProofFile.Honest.SumLaw

variable {V : Type}

/-- **The squares' level: its row is worth 0.** -/
theorem squares_at (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (squaresSum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F : Fork) (Wd : World GE)
    (fo : OnBytes.Model.Forest.Heard) (hk : k4Fits Q fo st.input.tokv = true)
    (hf : OwnFits Q st.heard) (hn : (st.heard.drop Q.r0).length = (starts Q).getD 0 0)
    (hLk : LookSkel (st.input.look (st.heard.take Q.r0)) fo)
    (hd : drawsOk ((squaresSum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (squaresSum Q)) c st seen ds = some rounds)
    (hs : ∀ i, i < ownSlots ((squaresSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (F.next + i) = hidingCoin c i)
    (hσ : ∀ j, jobSquares Q st.input (ptsOf Q st.input st.heard) = some j →
      C.value Reading.gl Wd = Reading.gl.val j.cube.total)
    {tp u : Tape} {G2 : Fork} {L : Level}
    (hF : Fl.levelIn Q.P.rd.muV (normsStart Q.P.y 0 (ptsOf Q st.input st.heard).gp
      (ptsOf Q st.input st.heard).rhoI (ptsOf Q st.input st.heard).PV).2 C
      (orderDefault Q.P.rd.muV) F tp = some (L, G2, u))
    (hS : OnBytes.PscRun.Sized F) (hT : TapeIs tp rounds) :
    L.row.value Reading.gl Wd = 0 := by
  obtain ⟨j, hj, _⟩ := squares_run st.input hk st.heard hf hn hLk
  exact squares_top (V := V) name endName Q c st seen ds rounds C F Wd hd ha hs j hj (hσ j hj) hF hS
    hT

/-- **The row products: the form that the flat text's state leaves, on the values as a later ledger
shows them, is worth 0.** -/
theorem rows_at (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (rowsSum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (F0 : Fork) (Wd : World GE)
    (fo : OnBytes.Model.Forest.Heard) (hk : k4Fits Q fo st.input.tokv = true)
    (hf : OwnFits Q st.heard) (hn : (st.heard.drop Q.r0).length = (starts Q).getD 1 0)
    (hLk : LookSkel (st.input.look (st.heard.take Q.r0)) fo)
    (hd : drawsOk ((rowsSum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (rowsSum Q)) c st seen ds = some rounds)
    (hs : ∀ i, i < ownSlots ((rowsSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (F0.next + 1 + i) = hidingCoin c i)
    (hxl : Q.P.y.h.xl = 5) (hNI : 1 ≤ Q.P.y.NI) (H : OnBytes.Model.Layer.Heard)
    (hom : H.omV = (ptsOf Q st.input st.heard).omV)
    (hσ : ∀ j, jobRows Q st.input (ptsOf Q st.input st.heard) = some j →
      (Aff.slot F0.next).value Reading.gl Wd = Reading.gl.val j.cube.total)
    {tp u : Tape} {G2 : Fork} {o : Tsc}
    (hF : Fl.tscIn (ptsOf Q st.input st.heard).PV Q.P.y.h.lt (ledNO Q.P.y.h.xl * Q.P.y.NI) 2 F0 tp =
      some (o, G2, u))
    (hR : D6.Ret.Room F0 (1 + (ownSlots ((rowsSum Q).callAt st.input (frontOf st seen)).all +
      ((rowsSum Q).callAt st.input (frontOf st seen)).endsN)))
    (hT : TapeIs tp rounds) (Fz : Fork) (sh : Array E) (hL : Fo.Later G2 Fz)
    (hsh : ((Array.range (4 * Q.P.y.NI)).mapM fun i => Fz.shown (o.sEnd + i)) = some sh) :
    (o.p.rowForm (rowsSummand Q.P.y H sh) {}).value Reading.gl Wd = 0 := by
  obtain ⟨j, hj, _⟩ := rows_run st.input hk st.heard hf hn hLk
  exact rows_top (V := V) name endName Q c st seen ds rounds F0 Wd hd ha hs j hj hxl hNI H hom
    (hσ j hj) hF hR hT Fz sh hL hsh

/-- **The first gated product's level: its row is worth 0.** -/
theorem gated_at (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (gatedSum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F : Fork) (Wd : World GE)
    (fo : OnBytes.Model.Forest.Heard) (hk : k4Fits Q fo st.input.tokv = true)
    (hf : OwnFits Q st.heard) (hn : (st.heard.drop Q.r0).length = (starts Q).getD 4 0)
    (hLk : LookSkel (st.input.look (st.heard.take Q.r0)) fo)
    (hd : drawsOk ((gatedSum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (gatedSum Q)) c st seen ds = some rounds)
    (hs : ∀ i, i < ownSlots ((gatedSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (F.next + i) = hidingCoin c i)
    (hσ : ∀ tb, gatedTabs Q st.input = some tb →
      C.value Reading.gl Wd = Reading.gl.val (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
        (downFrom (ptsOf Q st.input st.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++
          ztOf Q (ptsOf Q st.input st.heard)) tb).cube.total)
    {tp u : Tape} {G2 : Fork} {L : Level}
    (hF : Fl.levelIn Q.P.rd.muH
      (downFrom (ptsOf Q st.input st.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++
        ztOf Q (ptsOf Q st.input st.heard)) C (orderRange Q.P.rd.muH) F tp = some (L, G2, u))
    (hS : OnBytes.PscRun.Sized F) (hT : TapeIs tp rounds) :
    L.row.value Reading.gl Wd = 0 := by
  obtain ⟨tb, ht, hfit⟩ := gated_run st.input hk st.heard hf hn hLk
  exact gated_top (V := V) name endName Q c st seen ds rounds C F Wd hd ha hs tb ht hfit (hσ tb ht)
    hF hS hT

/-- **The second gated product's level: its row is worth 0.** -/
theorem gated2_at (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (gated2Sum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F : Fork) (Wd : World GE)
    (fo : OnBytes.Model.Forest.Heard) (hk : k4Fits Q fo st.input.tokv = true)
    (hf : OwnFits Q st.heard) (hn : (st.heard.drop Q.r0).length = (starts Q).getD 5 0)
    (hLk : LookSkel (st.input.look (st.heard.take Q.r0)) fo)
    (hd : drawsOk ((gated2Sum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (gated2Sum Q)) c st seen ds = some rounds)
    (hs : ∀ i, i < ownSlots ((gated2Sum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (F.next + i) = hidingCoin c i)
    (hσ : ∀ tb, gatedTabs2 Q st.input = some tb →
      C.value Reading.gl Wd = Reading.gl.val (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
        ((ptsOf Q st.input st.heard).rhoM ++ downFrom (ptsOf Q st.input st.heard).rs Q.P.y.lfe ++
          (ptsOf Q st.input st.heard).rt) tb).cube.total)
    {tp u : Tape} {G2 : Fork} {L : Level}
    (hF : Fl.levelIn Q.P.rd.muH2
      ((ptsOf Q st.input st.heard).rhoM ++ downFrom (ptsOf Q st.input st.heard).rs Q.P.y.lfe ++
        (ptsOf Q st.input st.heard).rt) C (orderRange Q.P.rd.muH2) F tp = some (L, G2, u))
    (hS : OnBytes.PscRun.Sized F) (hT : TapeIs tp rounds) :
    L.row.value Reading.gl Wd = 0 := by
  obtain ⟨tb, ht, hfit⟩ := gated2_run st.input hk st.heard hf hn hLk
  exact gated2_top (V := V) name endName Q c st seen ds rounds C F Wd hd ha hs tb ht hfit (hσ tb ht)
    hF hS hT

/-- **The merge: the form that the flat text's state leaves, on the value that it shows, is worth
0.** tp: the tape, the batching round first. -/
theorem merge_at (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (mergeSum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (F : Fork) (Wd : World GE)
    {cl : Array WsClaim} {sv : Array Nat} {tp u : Tape} {G2 : Fork} {wo : WsForkOut}
    (fo : OnBytes.Model.Forest.Heard) (hk : k4Fits Q fo st.input.tokv = true)
    (hf : OwnFits Q st.heard) (hn : (st.heard.drop Q.r0).length = (starts Q).getD 6 0)
    (hLk : LookSkel (st.input.look (st.heard.take Q.r0)) fo)
    (hd : drawsOk ((mergeSum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (mergeSum Q)) c st seen ds = some rounds)
    (hs : ∀ i, i < ownSlots ((mergeSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (F.next + i) = hidingCoin c i)
    (hσ : ∀ cls, mergeClaimsAt Q st.input (ptsOf Q st.input st.heard) = some cls →
      (wsForkStart sv (powers (tapeEps tp) sv.size)).value Reading.gl Wd = Reading.gl.val
        (mergeJobOf Q.P.wsLay st.input.w cls (ptsOf Q st.input st.heard).rhoW).cube.total)
    (hF : flatForkEnd Q.P.wsLay cl sv F tp = some (wo, G2, u))
    (hR : D6.Ret.Room F (ownSlots ((mergeSum Q).callAt st.input (frontOf st seen)).all +
      ((mergeSum Q).callAt st.input (frontOf st seen)).endsN))
    (hT : TapeIs (tp.drop 1) rounds) :
    (wo.p.rowForm wo.fvp {}).value Reading.gl Wd = 0 := by
  obtain ⟨cls, hc, _⟩ := merge_run st.input hk st.heard hf hn hLk
  exact merge_top (V := V) name endName Q c st seen ds rounds F Wd hd ha hs cls hc (hσ cls hc) hF hR
    hT

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.squares_at
#print axioms ProofFile.Honest.K4.rows_at
#print axioms ProofFile.Honest.K4.gated_at
#print axioms ProofFile.Honest.K4.gated2_at
#print axioms ProofFile.Honest.K4.merge_at
