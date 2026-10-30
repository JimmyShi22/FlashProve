-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FlatToken.lean: CONDITIONAL.

What is here. THE TWO TEXTS OF THE VERIFIER's MASKED SUMCHECK, TIED AT A TOKEN SUMCHECK; AND AT THE
SUMCHECK ON THE NORMS' ROW PRODUCTS THE FORM THAT THE FLAT TEXT's STATE LEAVES IS WORTH 0 ON THE
HONEST PART's ROUNDS. Where the flat function of a token sumcheck returns (`Fl.tscIn`,
OnBytes/K/Kc/Flat.lean) on a tape, and the part's text (`hear`, Johnson/Desc/Part/MaskedSum4.lean)
returns on rounds that hold what the tape holds, the flat text's state has the letters of what
`hear` hands back (`SameLetters`, Johnson/Desc/Part/MaskedSumFlat.lean). Statements and proofs.

  `shown_run`   a run of values that was laid, as a later ledger shows it
  `tsc_sameLetters`   **the tie**: the letters; the last round holds the end values, and every later
     ledger shows them under the end slots
  `tsc_row_worth`   the state's form is worth what `rowForm` is worth, at every summand and kept
     form
  `rows_flat_zero`   **the row products**: at the values as shown

Limits. `hear` is asked FROM THE LEDGER BEHIND THE CLAIMED SUM's LAYING (G0: the flat function lays
the claimed sum under the ledger's next slot, with the factor 1, and begins there) and at the
claimed form that is this slot. The ledger in front is sized. The call has one lead value, and its
variables' weights are the token sumcheck's (`tscWs`). THE TAPE HOLDS WHAT THE ROUNDS HOLD
(`TapeIs`, FlatCore.lean). Every equation between values is between readings, but that of the shown
values, which is on words. For `rows_flat_zero`, at the reading `Reading.gl`, beside these the
premises of `rows_rowForm_sent` (SumEndJobs.lean), and among them: norms of five limbs (xl = 5); THE
START IS A PREMISE: the slot of the claimed sum is worth the reading of the cube's total. THE FLAT
FUNCTION LAYS NOTHING UNDER THE SUMCHECK's OWN SLOTS: the world that is meant, in which these slots
hold the part's coins, is that of a ledger behind the making of the row. THE FLAT FUNCTION IS TYPED
AT THE MAKER's POINT AND NUMBERS: that the verifier runs it at these, and that it has heard the
powers which the maker lays, is not shown. That a verifier's step makes its row of this state, on
`rowsSummand` of the shown values, with nothing kept, is by reading. It stands on
Johnson/Desc/Part/MaskedSumFlat.lean and MaskedSumFlatProofs.lean. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatCore
import Johnson.Desc.ProofFile.Honest.K4.Law.SumEndJobs
import Johnson.Desc.ProofFile.Honest.K4.Law.SumPoints
import Johnson.Desc.Part.MaskedSumFlatProofs
import OnBytes.Desc.First.P1.TscLaw
import OnBytes.Desc.First.K4.ShownUnder
import OnBytes.Desc.First.K4.RowsLaws
import OnBytes.Maker.TablesLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E mulE addE zeroE oneE)
open OnBytes.Model (Reading World Aff Fork Psc Tsc ledNO)
open OnBytes.Slice (GE)
open OnBytes.K.Kc (Fl Tape)
open OnBytes.Desc.First.P1 (tscWs tscIn_tape tapeCl shown_some)
open OnBytes.Desc.First.K4 (rowsSummand)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc.Part.MaskedSum
open ProofFile.Honest.SumLaw

variable {V : Type}

/-! ## 1 The tie at a token sumcheck -/

/-- A run of values that was laid, as every later ledger shows it: the array of the shown values is
the run. -/
theorem shown_run {F G Fz : Fork} {first n : ℕ} {v sh : Array E} {f : E}
    (hS : OnBytes.PscRun.Sized F) (h : F.hideRun first v f = some G) (hn : v.size = n)
    (hL : Fo.Later G Fz)
    (hsh : ((Array.range n).mapM fun i => Fz.shown (first + i)) = some sh) : sh = v := by
  rw [Array.mapM_eq_mapM_toList, Array.toList_range] at hsh
  obtain ⟨l, hl, e⟩ := Option.map_eq_some_iff.mp hsh
  have hlen : l.length = n := by
    rw [OnBytes.Maker.mapM_length _ _ _ hl, List.length_range]
  have hlv : l = v.toList := by
    refine List.ext_getElem (by rw [hlen, Array.length_toList, hn]) fun i h1 h2 => ?_
    obtain ⟨b, hb, hb'⟩ := OnBytes.Desc.First.K4.mapM_range_get _ hl (i := i)
      (by rw [← hlen]; exact h1)
    have e1 : l[i] = b := by
      rw [List.getElem?_eq_getElem h1] at hb'
      exact Option.some.inj hb'
    have e2 := OnBytes.Desc.First.K4.hideRun_shown hS h rfl hL i (by rw [hn, ← hlen]; exact h1)
    rw [e1, (shown_some hb).2.2, e2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    rfl
  rw [← e, hlv]

/-- **Where both texts return on the same rounds.** G0: the ledger behind the laying of the claimed
sum. v: the end values as sent: the last round holds them, and every later ledger shows them under
the sumcheck's end slots. -/
theorem tsc_sameLetters {P : Array E} {lt n dY : ℕ} {F G G0 G' : Fork} {t u : Tape} {o : Tsc}
    (hF : Fl.tscIn P lt n dY F t = some (o, G, u)) (hS : OnBytes.PscRun.Sized F)
    (hG0 : ({ F with next := F.next + 1 } : Fork).hideRun F.next #[tapeCl t] oneE = some G0)
    (vs : List Var) (hk : vs.map Var.weight = tscWs (P.toList.take lt)) {rounds : List Fmt.RoundView}
    {h : Heard} (hh : hear (Aff.slot F.next) ⟨1, vs, some ⟨dY, n⟩⟩ G0 rounds = some (h, G'))
    (hT : TapeIs t rounds) :
    SameLetters o.p h ∧ ∃ (rv : Fmt.RoundView) (v : Array E), rounds.getLast? = some rv ∧
      scalars rv.vals = some v.toList ∧ v.size = n ∧
      ∀ (Fz : Fork) (sh : Array E), Fo.Later G Fz →
        ((Array.range n).mapM fun i => Fz.shown (o.sEnd + i)) = some sh → sh = v := by
  obtain ⟨_, T, cl, mu0, eps, rs, sentY, beta, w0, wY, wV, ms, y, v1, v, G0', ht, hrs, _, hms, hyy,
    hv1, _, _, hG0', hTp, a1, _, _, _, hvars, hr, hclaim, htar, heps, hstart, hfirst, _, _, hvn,
    hrun⟩ := tscIn_tape hF
  have ecl : tapeCl t = cl := by
    rw [ht]
    rfl
  have eG : G0' = G0 := by
    rw [hv1, ← ecl, hG0] at hG0'
    exact (Option.some.inj hG0').symm
  rw [eG] at hTp hfirst hrun
  have hF1 : OnBytes.PscRun.Sized ({ F with next := F.next + 1 } : Fork) := hS
  have hS0 : OnBytes.PscRun.Sized G0 := (OnBytes.PscRun.hideRun_ok _ G0 _ _ _ hF1 hG0).2.1
  rw [hms, hyy] at hr hclaim
  rw [hms] at a1
  obtain ⟨hSL, rv, b1, b2⟩ := sameLetters_of_tape (front := [cl]) (dY := dY) (n := n) ht
    (by rw [tscWs, List.length_map, hrs]) a1 hvars hr hclaim htar heps hstart hfirst hTp vs hk hh
    hT
  exact ⟨hSL, rv, v, b1, b2, hvn, fun Fz sh hL hsh => shown_run (F := { G0 with
    next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n }) hS0 hrun hvn hL hsh⟩

/-- **The state's form is worth what the part's `rowForm` is worth**, at every summand S0 and kept
form, at every reading and in every world. -/
theorem tsc_row_worth {K : Type} [CommRing K] (ρ : Reading K) (W : World K) {P : Array E}
    {lt n dY : ℕ} {F G G0 G' : Fork} {t u : Tape} {o : Tsc}
    (hF : Fl.tscIn P lt n dY F t = some (o, G, u)) (hS : OnBytes.PscRun.Sized F)
    (hG0 : ({ F with next := F.next + 1 } : Fork).hideRun F.next #[tapeCl t] oneE = some G0)
    (vs : List Var) (hk : vs.map Var.weight = tscWs (P.toList.take lt)) {rounds : List Fmt.RoundView}
    {h : Heard} (hh : hear (Aff.slot F.next) ⟨1, vs, some ⟨dY, n⟩⟩ G0 rounds = some (h, G'))
    (hT : TapeIs t rounds) (S0 : E) (kept : Aff) :
    (o.p.rowForm S0 kept).value ρ W = (rowForm h S0 kept).value ρ W :=
  flatRowTie K ρ W o.p h S0 kept (tsc_sameLetters hF hS hG0 vs hk hh hT).1

/-! ## 2 The row products -/

/-- **At the sumcheck on the norms' row products the form that the flat text's state leaves, made
with the verifier's summand on the values AS A LATER LEDGER SHOWS THEM and with nothing kept, is
worth 0.** tp: the tape. F0: the ledger in front of the claimed sum's laying. Fz: a ledger later
than the one that the flat function leaves. sh: the values that Fz shows under the sumcheck's end
slots. H: what the verifier has heard: of it the summand reads the powers omV alone. -/
theorem rows_flat_zero (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (rowsSum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (F0 F G : Fork) (h : Heard) (Wd : World GE)
    (hd : drawsOk ((rowsSum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (rowsSum Q)) c st seen ds = some rounds)
    (hh : hear (Aff.slot F0.next) ((rowsSum Q).callAt st.input (frontOf st seen)) F rounds =
      some (h, G))
    (hs : ∀ i, i < ownSlots ((rowsSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (h.first + i) = hidingCoin c i)
    (j : Job) (hj : jobRows Q st.input (ptsOf Q st.input st.heard) = some j)
    (hxl : Q.P.y.h.xl = 5) (H : OnBytes.Model.Layer.Heard)
    (hom : H.omV = (ptsOf Q st.input st.heard).omV)
    (hσ : (Aff.slot F0.next).value Reading.gl Wd = Reading.gl.val j.cube.total)
    {tp u : Tape} {G2 : Fork} {o : Tsc}
    (hF : Fl.tscIn (ptsOf Q st.input st.heard).PV Q.P.y.h.lt (ledNO Q.P.y.h.xl * Q.P.y.NI) 2 F0 tp =
      some (o, G2, u))
    (hS : OnBytes.PscRun.Sized F0)
    (hG0 : ({ F0 with next := F0.next + 1 } : Fork).hideRun F0.next #[tapeCl tp] oneE = some F)
    (hT : TapeIs tp rounds) (Fz : Fork) (sh : Array E) (hL : Fo.Later G2 Fz)
    (hsh : ((Array.range (4 * Q.P.y.NI)).mapM fun i => Fz.shown (o.sEnd + i)) = some sh) :
    (o.p.rowForm (rowsSummand Q.P.y H sh) {}).value Reading.gl Wd = 0 := by
  have hk := rows_weights Q st.input (frontOf st seen) j (ledNO Q.P.y.h.xl * Q.P.y.NI) hj
  obtain ⟨_, rv, v, a1, a2, _, a4⟩ := tsc_sameLetters hF hS hG0 _ hk hh hT
  obtain ⟨r', s', b1, b2, _, b4⟩ := rows_rowForm_sent (V := V) name endName Q c st seen ds rounds
    (Aff.slot F0.next) F G h {} Wd hd ha hh hs j hj hxl H hom hσ
  have e1 : rv = r' := Option.some.inj (a1.symm.trans b1)
  rw [e1] at a2
  have e2 : v.toList = s' := Option.some.inj (a2.symm.trans b2)
  have e4 : ledNO Q.P.y.h.xl * Q.P.y.NI = 4 * Q.P.y.NI := by
    rw [hxl]
    rfl
  have e3 : sh = v := a4 Fz sh hL (by rw [e4]; exact hsh)
  rw [← e2, Array.toArray_toList, ← e3] at b4
  rw [tsc_row_worth Reading.gl Wd hF hS hG0 _ hk hh hT, b4, Aff.value_empty, mul_zero]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.shown_run
#print axioms ProofFile.Honest.K4.tsc_sameLetters
#print axioms ProofFile.Honest.K4.tsc_row_worth
#print axioms ProofFile.Honest.K4.rows_flat_zero
