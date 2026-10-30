-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FlatTops.lean: CONDITIONAL.

What is here. THE OWN CLAIMS OF FIVE MASKED SUMCHECKS OF THE FEED-FORWARD LAYERS' ROUNDS, AS THE
VERIFIER's FLAT TEXT LEAVES THEM, ARE WORTH 0 ON THE HONEST PARTS' ROUNDS: the statements of
FlatLevelJobs.lean, FlatToken.lean and FlatMerge.lean WITHOUT THE PART's TEXT OF THE VERIFIER IN
THEM: that `hear` returns is no premise any more. Statements and proofs.

  `heard_first`   `hear` begins at the ledger's next slot
  `k4_hears`   `hear` returns on the honest part's rounds, at a ready ledger
  `squares_top`, `gated_top`, `gated2_top`, `rows_top`, `merge_top`   **the five**

Limits. At the reading `Reading.gl` alone. THE START IS A PREMISE OF EACH, AND IT IS THE JOB's OWN
CONTENT: the claimed form is worth the reading of the cube's total. It holds by the way the part is
made at the row products alone (the claimed sum is sent); at the squares it is an identity on the
sums of limb products; at the two gated products and the merge the claimed form names end values of
the batched sumcheck, on which nothing is shown. SO NONE OF THE FIVE STANDS WITHOUT IT. The other
premises: the flat function RETURNS on the tape, AT THE MAKER's LETTERS (number of variables, point,
order; layout): that the verifier runs it at these is not shown; the ledger in front is sized, and
for the row products and the merge it HAS ROOM for the sumcheck's slots (`Room`,
OnBytes/K/Kc/Returns/FlReturns.lean: these two functions lay nothing under the sumcheck's own slots,
so their returns do not say that these are free); the challenges have the call's shape and the
part's moves answer; THE TAPE HOLDS WHAT THE ROUNDS HOLD (`TapeIs`, FlatCore.lean); THE WORLD HOLDS
THE PART's COINS from the sumcheck's first slot on: at the row products and the merge that is so
only in the world of a ledger BEHIND THE MAKING OF THE ROW (one ledger earlier nothing lies under
these slots); the job's maker returns at the run's input; for a gated product the run's cube fits.
For the row products: norms of five limbs, at least one norm, the verifier has heard the powers that
the maker lays, and the values are those that a later ledger shows. No example of the premises
together is known. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatLevelJobs
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatToken
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatMerge
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatReady
import Johnson.Desc.ProofFile.Honest.K4.Law.ShapesOk
import Johnson.Desc.ProofFile.Honest.SumLaw.Law

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E F mulE zeroE oneE)
open OnBytes.Model (Reading Aff Fork World Level Tsc WsClaim WsForkOut wsForkStart powers
  orderRange orderDefault ledNO)
open OnBytes.Model.Layer (downFrom normsStart)
open OnBytes.Slice (GE)
open OnBytes.K.Kc (Fl Tape flatForkEnd)
open OnBytes.Desc.First.P1 (tapeEps tapeCl tscIn_tape filledA_of_publicPart)
open OnBytes.Desc.First.K4 (rowsSummand)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc.Part.MaskedSum
open VerifiableInference.Desc.First.MergeLaw (hear_ended hear_of_flat)
open ProofFile.Honest.SumLaw

variable {V W X : Type}

/-- `hear` begins at the ledger's next slot. -/
theorem heard_first {C : Aff} {k : Call} {F G : Fork} {rs : List Fmt.RoundView} {h : Heard}
    (hh : hear C k F rs = some (h, G)) : h.first = F.next := by
  obtain ⟨_, T, R, _, _, e, _⟩ := hear_spec hh
  rw [e]

/-- **`hear` returns on the honest part's rounds, at a ready ledger**: the law of the honest part,
with the library's test on the shape asked at the shape. -/
theorem k4_hears (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (st : State W X) (seen : Seen) (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff)
    (F : Fork) (hsh : shapeOk J.shape = true)
    (hd : drawsOk (J.callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName J) c st seen ds = some rounds)
    (hL : LedgerReady C (J.callAt st.input (frontOf st seen)) F) :
    ∃ h G, hear C (J.callAt st.input (frontOf st seen)) F rounds = some (h, G) ∧
      h.first = F.next := by
  obtain ⟨h, G, hh⟩ := sumHeard V W X name endName J c st seen ds rounds C F
    (by rw [shapeOk_callAt]; exact hsh) hd ha hL
  exact ⟨h, G, hh, heard_first hh⟩

/-- **The squares.** -/
theorem squares_top (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (squaresSum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F : Fork) (Wd : World GE)
    (hd : drawsOk ((squaresSum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (squaresSum Q)) c st seen ds = some rounds)
    (hs : ∀ i, i < ownSlots ((squaresSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (F.next + i) = hidingCoin c i)
    (j : Job) (hj : jobSquares Q st.input (ptsOf Q st.input st.heard) = some j)
    (hσ : C.value Reading.gl Wd = Reading.gl.val j.cube.total)
    {tp u : Tape} {G2 : Fork} {L : Level}
    (hF : Fl.levelIn Q.P.rd.muV (normsStart Q.P.y 0 (ptsOf Q st.input st.heard).gp
      (ptsOf Q st.input st.heard).rhoI (ptsOf Q st.input st.heard).PV).2 C
      (orderDefault Q.P.rd.muV) F tp = some (L, G2, u))
    (hS : OnBytes.PscRun.Sized F) (hT : TapeIs tp rounds) :
    L.row.value Reading.gl Wd = 0 := by
  obtain ⟨h, G, hh, hf⟩ := k4_hears (V := V) name endName (squaresSum Q) c st seen ds rounds C F
    (shapeOk_level _) hd ha
    (level_ready hF hS _ (squares_weights Q st.input (frontOf st seen) j hj))
  exact squares_flat_zero (V := V) name endName Q c st seen ds rounds C F G h Wd hd ha hh
    (by rw [hf]; exact hs) j hj hσ hF hS hT

/-- **The first gated product.** -/
theorem gated_top (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (gatedSum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F : Fork) (Wd : World GE)
    (hd : drawsOk ((gatedSum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (gatedSum Q)) c st seen ds = some rounds)
    (hs : ∀ i, i < ownSlots ((gatedSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (F.next + i) = hidingCoin c i)
    (tb : Tab × Tab) (ht : gatedTabs Q st.input = some tb)
    (hfit : (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
      (downFrom (ptsOf Q st.input st.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++
        ztOf Q (ptsOf Q st.input st.heard)) tb).cube.fits = true)
    (hσ : C.value Reading.gl Wd = Reading.gl.val (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
      (downFrom (ptsOf Q st.input st.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++
        ztOf Q (ptsOf Q st.input st.heard)) tb).cube.total)
    {tp u : Tape} {G2 : Fork} {L : Level}
    (hF : Fl.levelIn Q.P.rd.muH
      (downFrom (ptsOf Q st.input st.heard).rs (Q.P.y.h.ll + Q.P.y.lPf) ++
        ztOf Q (ptsOf Q st.input st.heard)) C (orderRange Q.P.rd.muH) F tp = some (L, G2, u))
    (hS : OnBytes.PscRun.Sized F) (hT : TapeIs tp rounds) :
    L.row.value Reading.gl Wd = 0 := by
  obtain ⟨h, G, hh, hf⟩ := k4_hears (V := V) name endName (gatedSum Q) c st seen ds rounds C F
    (shapeOk_level _) hd ha
    (level_ready hF hS _ (gated_weights Q st.input (frontOf st seen) tb ht hfit))
  exact gated_flat_zero (V := V) name endName Q c st seen ds rounds C F G h Wd hd ha hh
    (by rw [hf]; exact hs) tb ht hfit hσ hF hS hT

/-- **The second gated product.** -/
theorem gated2_top (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (gated2Sum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F : Fork) (Wd : World GE)
    (hd : drawsOk ((gated2Sum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (gated2Sum Q)) c st seen ds = some rounds)
    (hs : ∀ i, i < ownSlots ((gated2Sum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (F.next + i) = hidingCoin c i)
    (tb : Tab × Tab) (ht : gatedTabs2 Q st.input = some tb)
    (hfit : (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
      ((ptsOf Q st.input st.heard).rhoM ++ downFrom (ptsOf Q st.input st.heard).rs Q.P.y.lfe ++
        (ptsOf Q st.input st.heard).rt) tb).cube.fits = true)
    (hσ : C.value Reading.gl Wd = Reading.gl.val (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
      ((ptsOf Q st.input st.heard).rhoM ++ downFrom (ptsOf Q st.input st.heard).rs Q.P.y.lfe ++
        (ptsOf Q st.input st.heard).rt) tb).cube.total)
    {tp u : Tape} {G2 : Fork} {L : Level}
    (hF : Fl.levelIn Q.P.rd.muH2
      ((ptsOf Q st.input st.heard).rhoM ++ downFrom (ptsOf Q st.input st.heard).rs Q.P.y.lfe ++
        (ptsOf Q st.input st.heard).rt) C (orderRange Q.P.rd.muH2) F tp = some (L, G2, u))
    (hS : OnBytes.PscRun.Sized F) (hT : TapeIs tp rounds) :
    L.row.value Reading.gl Wd = 0 := by
  obtain ⟨h, G, hh, hf⟩ := k4_hears (V := V) name endName (gated2Sum Q) c st seen ds rounds C F
    (shapeOk_level _) hd ha
    (level_ready hF hS _ (gated2_weights Q st.input (frontOf st seen) tb ht hfit))
  exact gated2_flat_zero (V := V) name endName Q c st seen ds rounds C F G h Wd hd ha hh
    (by rw [hf]; exact hs) tb ht hfit hσ hF hS hT

/-- **The row products.** F0: the ledger in front of the claimed sum's laying: it has room for that
slot, the sumcheck's own slots and its end values. Fz: a ledger later than the one that the flat
function leaves. sh: the values that Fz shows under the sumcheck's end slots. H: what the verifier
has heard. -/
theorem rows_top (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (rowsSum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (F0 : Fork) (Wd : World GE)
    (hd : drawsOk ((rowsSum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (rowsSum Q)) c st seen ds = some rounds)
    (hs : ∀ i, i < ownSlots ((rowsSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (F0.next + 1 + i) = hidingCoin c i)
    (j : Job) (hj : jobRows Q st.input (ptsOf Q st.input st.heard) = some j)
    (hxl : Q.P.y.h.xl = 5) (hNI : 1 ≤ Q.P.y.NI) (H : OnBytes.Model.Layer.Heard)
    (hom : H.omV = (ptsOf Q st.input st.heard).omV)
    (hσ : (Aff.slot F0.next).value Reading.gl Wd = Reading.gl.val j.cube.total)
    {tp u : Tape} {G2 : Fork} {o : Tsc}
    (hF : Fl.tscIn (ptsOf Q st.input st.heard).PV Q.P.y.h.lt (ledNO Q.P.y.h.xl * Q.P.y.NI) 2 F0 tp =
      some (o, G2, u))
    (hR : D6.Ret.Room F0 (1 + (ownSlots ((rowsSum Q).callAt st.input (frontOf st seen)).all +
      ((rowsSum Q).callAt st.input (frontOf st seen)).endsN)))
    (hT : TapeIs tp rounds) (Fz : Fork) (sh : Array E) (hL : Fo.Later G2 Fz)
    (hsh : ((Array.range (4 * Q.P.y.NI)).mapM fun i => Fz.shown (o.sEnd + i)) = some sh) :
    (o.p.rowForm (rowsSummand Q.P.y H sh) {}).value Reading.gl Wd = 0 := by
  obtain ⟨F, hG0, hRF, hnext, _⟩ := D6.Ret.takeHide hR #[tapeCl tp] rfl oneE
  have hC : Fo.FilledA F (Aff.slot F0.next) := by
    obtain ⟨_, T, cl, mu0, eps, rs, sentY, beta, w0, wY, wV, ms, y, v1, v, G0', ht, _, _, _, _,
      hv1, _, _, hG0', hTp, _⟩ := tscIn_tape hF
    have ecl : tapeCl tp = cl := by
      rw [ht]
      rfl
    have eG : G0' = F := by
      rw [hv1, ← ecl, hG0] at hG0'
      exact (Option.some.inj hG0').symm
    rw [eG] at hTp
    exact filledA_of_publicPart hTp
  obtain ⟨h, G, hh, hf⟩ := k4_hears (V := V) name endName (rowsSum Q) c st seen ds rounds
    (Aff.slot F0.next) F
    (shapeOk_token _ (by norm_num) (by rw [hxl]; show 1 ≤ 4 * Q.P.y.NI; omega)) hd ha
    (ready_of_room hRF hC)
  exact rows_flat_zero (V := V) name endName Q c st seen ds rounds F0 F G h Wd hd ha hh
    (by rw [hf, hnext]; exact hs) j hj hxl H hom hσ hF hR.sized hG0 hT Fz sh hL hsh

/-- **The merge.** tp: the tape, the batching round first. -/
theorem merge_top (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (mergeSum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (F : Fork) (Wd : World GE)
    {cl : Array WsClaim} {sv : Array Nat} {tp u : Tape} {G2 : Fork} {wo : WsForkOut}
    (hd : drawsOk ((mergeSum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (mergeSum Q)) c st seen ds = some rounds)
    (hs : ∀ i, i < ownSlots ((mergeSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (F.next + i) = hidingCoin c i)
    (cls : List WsClaim) (hc : mergeClaimsAt Q st.input (ptsOf Q st.input st.heard) = some cls)
    (hσ : (wsForkStart sv (powers (tapeEps tp) sv.size)).value Reading.gl Wd = Reading.gl.val
      (mergeJobOf Q.P.wsLay st.input.w cls (ptsOf Q st.input st.heard).rhoW).cube.total)
    (hF : flatForkEnd Q.P.wsLay cl sv F tp = some (wo, G2, u))
    (hR : D6.Ret.Room F (ownSlots ((mergeSum Q).callAt st.input (frontOf st seen)).all +
      ((mergeSum Q).callAt st.input (frontOf st seen)).endsN))
    (hT : TapeIs (tp.drop 1) rounds) :
    (wo.p.rowForm wo.fvp {}).value Reading.gl Wd = 0 := by
  have hC : Fo.FilledA F (wsForkStart sv (powers (tapeEps tp) sv.size)) := by
    obtain ⟨x, mu, c', beta, v, T, r1, rY, rV, qs, _, _, et, hTp, _⟩ :=
      hear_ended (hear_of_flat hF)
    have ex : tapeEps tp = x := by
      rw [et]
      rfl
    rw [ex]
    exact filledA_of_publicPart hTp
  obtain ⟨h, G, hh, hf⟩ := k4_hears (V := V) name endName (mergeSum Q) c st seen ds rounds
    (wsForkStart sv (powers (tapeEps tp) sv.size)) F
    (shapeOk_plain _ (Nat.le_refl 1) (Nat.le_refl 1)) hd ha (ready_of_room hR hC)
  exact merge_flat_zero (V := V) name endName Q c st seen ds rounds F G h Wd hd ha hh
    (by rw [hf]; exact hs) cls hc hσ hF hR.sized hT

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.heard_first
#print axioms ProofFile.Honest.K4.k4_hears
#print axioms ProofFile.Honest.K4.squares_top
#print axioms ProofFile.Honest.K4.gated_top
#print axioms ProofFile.Honest.K4.gated2_top
#print axioms ProofFile.Honest.K4.rows_top
#print axioms ProofFile.Honest.K4.merge_top
