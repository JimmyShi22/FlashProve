-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/EquationsBlank.lean: WHAT THE RUN "K8.equations" OWES TO A LAW ON RUNS OF CLAIMS, on
ledgers and records alone: the part of the smallness test's record that the run leaves and that the single
equations read, as a function (blank); and the run's equation at a LATER record and ledger at which the test
by a second computation has said yes.

Definitions, statements and proofs. For kind K9's premise on one run (RunOk, in K9's files: not
imported, not named in any statement here). No routine of `verify-on-bytes` is named. USED OF THE FILES
UNDER OnBytes/, ON RECORDS AND PLAIN DATA ALONE: what EquationsAny.lean and EquationsRaw.lean list.
Main names:
  blank u t: the record t with the fourteen fields that the run and the step behind the adding write (joinObj9,
    bitFactor9, vt, vp, eqFirst, rowX, loX, gamX, gamV, foldTakenF, tieObj, tiesOn, nX4Laid; lsTail) set to
    those of a fixed record u.
  eq_blank: the run leaves blank u. blank_lsTail: so does the laying of lsTail.
  rawRows_blank, rowsTail_blank, topOf_blank, reads_blank, fits_blank: RawRows, the list of single
    equations, topOf, the list of reads and Fits read blank u t alone.
  **K08Run** (a closed Prop), **k08_run**: K08AnyAt with RawRows replaced: at ANY record ts with blank u ts =
    blank u tl and ANY ledger Fc with the batching element of F: rkSelfTestP ts Fc = .ok (), ReadsRaw at ts,
    Fc and A, and the two premises on public numbers, at ts.
  sheet_run: where the sheet (EquationsSheet.lean) says yes, all premises of K08Run hold at A0 := the returned
    ledger, ts := the returned record with lsTail laid, the ledger with the weights laid, ANY table A and the
    rawWorld made of A: so K08Run is not empty wherever the sheet has said yes.
Limits: those of K08AnyAt and K08Raw. From yeses alone. Of the first four claims only their number and place.

-/
import Johnson.Desc.First.TailClaims.EquationsAny
import Johnson.Desc.First.TailClaims.EquationsSheet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open OnBytes.Tie.Pv.Tail.Port OnBytes.Road.Rows Finset
open OnBytes.Tie.Pv.Tail (ReadsRaw UnitRow rawWorld rawWorld_reads)

/-- The record t with the fourteen written fields set to those of u. -/
def blank (u t : HTailF2) : HTailF2 :=
  { t with
    joinObj9 := u.joinObj9, bitFactor9 := u.bitFactor9, vt := u.vt, vp := u.vp, eqFirst := u.eqFirst,
    rowX := u.rowX, loX := u.loX, gamX := u.gamX, gamV := u.gamV, foldTakenF := u.foldTakenF,
    tieObj := u.tieObj, tiesOn := u.tiesOn, nX4Laid := u.nX4Laid, lsTail := u.lsTail }

theorem eq_blank (u : HTailF2) {front : Nat} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) :
    blank u tl' = blank u tl :=
  eq_same (blank u) h (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)

theorem blank_lsTail (u t : HTailF2) (x : Array E) : blank u { t with lsTail := x } = blank u t := rfl

theorem rawRows_blank {K : Type} [CommRing K] {W : World K} (u t : HTailF2) {G : Fork}
    {funs : Array HFun} {θ : K} {A : Nat → Nat → Nat → K} :
    RawRows W (blank u t) G funs θ A ↔ RawRows W t G funs θ A :=
  ⟨fun h => ⟨h.ties, h.reads, h.syms, h.tabs⟩, fun h => ⟨h.ties, h.reads, h.syms, h.tabs⟩⟩

theorem rowsTail_blank {K : Type} [Field K] (ρ : Reading K) (u t : HTailF2) (funs : Array HFun)
    (n : Nat) : rowsTail ρ (blank u t) funs n = rowsTail ρ t funs n := rfl

theorem topOf_blank (u t : HTailF2) (funs : Array HFun) : topOf (blank u t) funs = topOf t funs := rfl

theorem reads_blank (u t : HTailF2) (funs : Array HFun) :
    readsList (blank u t) funs = readsList t funs := rfl

theorem fits_blank (u t : HTailF2) : Fits (blank u t) ↔ Fits t := Iff.rfl

/-- **The run's equation at a later record and ledger.** -/
def K08Run : Prop :=
  ∀ (K : Type) [Field K] (ρ : Reading K) (W : World K) (A : Nat → Nat → Nat → K)
    (front : Nat) (tl tl' u ts : HTailF2) (funs : Array HFun) (F F1 A0 G Fc : Fork)
    (look cls : List Claim),
    F.LS.size = F.ns → equations front tl funs F = .ok (tl', F1, cls) →
    A0.LS.size = A0.ns → treesFrame A0.trees = treesFrame F1.trees → A0.theta = F1.theta →
    A0.planClaimsF = F1.planClaimsF →
    addAll A0 (look ++ cls) = some G → Fits tl →
    blank u ts = blank u tl → Fc.theta = F.theta → rkSelfTestP ts Fc = .ok () →
    ReadsRaw ρ ts funs Fc W A →
    (Fc.trees.getD ts.ix.ZZ {}).rows.size = 2 * ts.zzBlocks + 2 →
    (∀ x ∈ readsList ts funs, UnitRow Fc (uOf ts x.1) ∧
      ∀ d, d < (ts.mats.getD x.1.mat {}).k → posOf ts x.1 x.2 d < colsU F1 (uOf ts x.1)) →
    Rising (rowsTail ρ tl funs F.planClaimsF) ∧
    (∀ r ∈ rowsTail ρ tl funs F.planClaimsF,
      F.planClaimsF ≤ r.1 ∧ r.1 < F.planClaimsF + topOf tl funs) ∧
    ∃ (four rest : List Claim) (X X4 : Fork), cls = four ++ rest ∧ four.length = 4 ∧
      rest.length = tl.NM + (readsList tl funs).length ∧ addAll A0 look = some X ∧
      addAll X four = some X4 ∧ addAll X4 rest = some G ∧
      G.total ρ W = X4.total ρ W +
        batchOf (ρ.val F.theta) A (rowsTail ρ tl funs F.planClaimsF)

theorem k08_run : K08Run := by
  intro K _ ρ W A front tl tl' u ts funs F F1 A0 G Fc look cls hs h hsA hfrA hthA hplA hadd hfit hb hth
    hrk hW hrows hU
  have hr := rawRows_plain ρ ts Fc F1 funs W A hW hrk hrows hU
  rw [hth] at hr
  have hr' : RawRows W tl F1 funs (ρ.val F.theta) A :=
    (rawRows_blank u tl).1 (hb ▸ (rawRows_blank u ts).2 hr)
  exact k08_any_at K ρ W A front tl tl' funs F F1 A0 G look cls hs h hsA hfrA hthA hplA hadd hfit hr'

/-- **Where the sheet says yes, K08Run is not empty**: at any table of cells A and any values under the slots. -/
theorem sheet_run {K : Type} [Field K] (ρ : Reading K) (A : Nat → Nat → Nat → K) (slot : Nat → K)
    (u : HTailF2) {front : Nat} {tl ts : HTailF2} {funs : Array HFun} {F G Fc : Fork}
    {look : List Claim} (h : sheet front tl funs F look = .ok (ts, G, Fc)) :
    ∃ (tl' : HTailF2) (F1 : Fork) (cls : List Claim),
      equations front tl funs F = .ok (tl', F1, cls) ∧ blank u ts = blank u tl ∧
      Fc.theta = F.theta ∧ ReadsRaw ρ ts funs Fc (rawWorld ρ Fc slot A) A ∧
      ∃ (four rest : List Claim) (X X4 : Fork), cls = four ++ rest ∧ four.length = 4 ∧
        rest.length = tl.NM + (readsList tl funs).length ∧ addAll F1 look = some X ∧
        addAll X four = some X4 ∧ addAll X4 rest = some G ∧
        G.total ρ (rawWorld ρ Fc slot A) = X4.total ρ (rawWorld ρ Fc slot A) +
          batchOf (ρ.val F.theta) A (rowsTail ρ tl funs F.planClaimsF) := by
  obtain ⟨tl', F1, cls, b1, b2, -, he, -, hadd, rfl, hco, hrk, b5, b6⟩ := sheet_ok h
  have hs := sizedB_ok b1
  have os := eq_side he
  have e : blank u { tl' with lsTail := G.LS.extract tl'.slotA tl'.slotB } = blank u tl :=
    (blank_lsTail u tl' _).trans (eq_blank u he)
  have hth : Fc.theta = F.theta := (coef_theta hco).trans (eq_link hs he hadd).2.2.1
  have hW := rawWorld_reads ρ { tl' with lsTail := G.LS.extract tl'.slotA tl'.slotB } funs Fc slot A
  have hrows : (Fc.trees.getD (blank u { tl' with lsTail := G.LS.extract tl'.slotA tl'.slotB }).ix.ZZ
      {}).rows.size =
      2 * (blank u { tl' with lsTail := G.LS.extract tl'.slotA tl'.slotB }).zzBlocks + 2 := by
    rw [e]
    exact rowsB_ok b5
  have hU : ∀ x ∈ readsList (blank u { tl' with lsTail := G.LS.extract tl'.slotA tl'.slotB }) funs,
      UnitRow Fc (uOf (blank u { tl' with lsTail := G.LS.extract tl'.slotA tl'.slotB }) x.1) ∧
      ∀ d, d < ((blank u { tl' with lsTail := G.LS.extract tl'.slotA tl'.slotB }).mats.getD x.1.mat
          {}).k →
        posOf (blank u { tl' with lsTail := G.LS.extract tl'.slotA tl'.slotB }) x.1 x.2 d <
          colsU F1 (uOf (blank u { tl' with lsTail := G.LS.extract tl'.slotA tl'.slotB }) x.1) := by
    rw [e]
    exact unitB_ok b6
  exact ⟨tl', F1, cls, he, e, hth, hW,
    (k08_run K ρ _ A front tl tl' u _ funs F F1 F1 G Fc look cls hs he
      (by rw [os.LS, os.ns]; exact hs) rfl rfl rfl hadd (fitsB_ok b2) e hth hrk hW hrows hU).2.2⟩

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.sheet_run
#print axioms VerifiableInference.Desc.First.TailClaims.Law.eq_blank
#print axioms VerifiableInference.Desc.First.TailClaims.Law.rawRows_blank
#print axioms VerifiableInference.Desc.First.TailClaims.Law.k08_run
