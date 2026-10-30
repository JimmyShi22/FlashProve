--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Meaning/PlanesPaidK4.lean, SECOND FORM: the planes' row's conclusion IS the lookups' premise
"true reads" at the layers; and what follows, by their law, at the layers' own run of claims.

At a layers' link the lookup states no run of claims on the planes of its counts: the layers' own
run (`Desc.First.K4.formsFrontWith`) lays the three forms. It is shown what these are worth
and that, where they are worth 0 in a world with TRUE READS of the three tables, the item
"planes" of its row out holds (Johnson/Top/H/K4PlanesWorth.lean: `k4_planes_worth`, `k4_planes_out`,
`k4_planes_out_front`; the premise `K4ReadsTrue`); who pays the true reads is not
said there. The planes' row concludes three clauses (`K3HostPlanes`, Johnson/Meaning/PlanesLaw.lean,
at the layers' forms `k4Bit`, `k4Pin`, PlanesForms.lean). Here the two are one sentence.

THE FIRST FORM (,; landed nowhere) WAS, IN THE GREATER PART, A TWIN OF
K4PlanesWorth.lean, which was there first and which we had not seen: its lemmas on folds and on the
flat function's return (foldlM_need, planesAtF_need, planeClaimsF_need, k4_planeClaimsF) and the
first half of its k4_front_planes_worth HAVE FALLEN FOR CALLS. What is left is what that file has
not.

Main theorems (namespace `Meaning.Planes`).
  `readsTrue_iff_hostPlanes`: **THE BRIDGE**: at the three tables' look-ups: `K4ReadsTrue ρ v fo H ν
      entry` if and only if `K3HostPlanes fo.shape lmb (rdL ρ fo.zb0) (rdL ρ fo.zb1) ν (value in H's
      world) (k4Bit v tB0 tB1) (k4Pin v tP)`. By unfolding: their reader of a column is the
      library's planeCol.
  `k4_front_planes_worth`: **AN EQUATION AT ν's CELLS**: their `k4_planes_worth` at the letters of
      the layers' run and ANY ledger H later than what the run leaves, with the readers' values
      exchanged for the columns' sums by the three clauses: planesL is there, its members are among
      the run's forms, and their values are, one by one, claimLeaves … (colsK … zb0 ν), claimBits …
      (colsK … zb1 ν), countK … (pinColK lmb ν).
  `k4_front_planes_paid`, `k4_front_K3Planes`: **so all three are worth 0 IF AND ONLY IF the
      lookups' `K3Planes` holds** (written out; and under its name).
  `k4_front_K3OutPlanes`: the item of the row out, from the three planes' forms alone, in the world
      of any later ledger (theirs, `k4_planes_out_front`: from all of the run's forms, in the world
      of the ledger that the run leaves).

WHAT THE WORD "paid" MEANS HERE, AND WHAT IT DOES NOT. The planes' row's CONCLUSION is SPENT, as hK.
NOTHING OF THAT ROW's PREMISES IS DERIVED. It is the same one row, carried one step on to its user;
no new row. OWED AGAIN at this step: "own kept" up to the record at which the run is called, and the
run's return (the batching's call).
THE TOOTH is the way back: a planes' form that is not worth 0 makes one of the three claims fail;
the equation says which.
ALL PREMISES of the four: hfr (a return of the layers' run at the ledger F) · hI (HeardIs ρ o.H.fo
F0 (endsOf … first rs)) · h0 (F is later than F0) · hok (the heard shape is lawful) · hF (F's arrays
have their sizes) · hH (H is later than what the run leaves) · b0, b1, b2 (the three tables' first
entries: look-ups) · hK (the three clauses). WHO CAN PAY: hfr: a yes of the run "front" of K4's
block · hI, hok: THE LOOKUP's OWN YES, BY LANDED THEOREMS: `k3DecideHears_calls`
(Johnson/Top/H/K3DecideHearsAt.lean; K3DecideHears, K3LawKind.lean: behind a yes of K3.block's
decide at the calls' seat, under Sized F: HeardIs ρ g F' (endsOf g.shape lm F.next …) at every lm,
and ShapeOf) with the library's `shape_ok` (OnBytes/Tie/Pv/Lookup/Port/FoShape.lean); that o.H.fo is
the g that this yes left, and F0 its F', is not joined here · h0, hF, hH: the ledger's walk · hK:
the planes' row (Johnson/Meaning/PlanesRowTie.lean: RowTie [not in this library]; in it:
Johnson/Meaning/PlanesNumbers.lean: k4_host_planes_at, under the law of the reads).
OBJECT · USER · LETTERS. Object: part 3's `formsFrontWith`; the lookups' `K4ReadsTrue`, `K3Planes`,
`K3OutPlanes`; our `K3HostPlanes`. No seat and no seated description is named. User: the lookups'
row out; Johnson/Meaning/PlanesRowPaidTie.lean [not in this library]. Letters: K, ρ, rs, first, F0,
H, ν, entry: free, under "for all".
CALLED, NOT TYPED: the lookups' `front_cut`, `planesParts_cut`, `k4_planes_worth`
(K4PlanesWorth.lean), `claimLeaves_congr`, `claimBits_congr` (K3OutProof.lean), `paid_laterFo`
(K3RunsLaw.lean) · the library's `countK_congr`, `Fo.hideRun_later`, `hideRun_sized` · our
`planesParts_planesL`.





Limits. NO MEMBER IS SHOWN: that a run's records meet hfr, hI and hK together is a run's matter.
That the forms ARE worth 0 is the link's one equation's. That the o of the clauses is the o at which
the run is called ("own kept" up to that record) is not treated. A tie: no draw, no error. Nothing
on soundness.
READ: THE SECOND FORM: nobody. The first form's statements of k4_front_planes_worth and
k4_front_planes_paid, which stand here to the letter, were read (one reader of
another house, by reading, at the bytes); in its post's own words: "RIGHT AS IT STANDS.
«IS IT EMPTY HERE?»: NO, BY THE TEXTS: hK can never clash with hfr · hI (it reads other letters); no
member is shown, as the pen says." It was that reader who asked whether K4PlanesWorth was a twin.
-/
import Johnson.Meaning.PlanesHost
import Johnson.Top.H.K4PlanesWorth

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Planes
open Cb Cb.Fo Cb.Fo.NumsEq TwV
open OnBytes OnBytes.Model Fo
open Cb.Fo.Pin
open OnBytes.Model.Layer (Env Pub Own)
open OnBytes.Road.Rows (planesL planeCol)
open VerifiableInference.OnPublicFiles (K4ReadsTrue K3Planes K3OutPlanes front_cut planesParts_cut
        k4_planes_worth claimLeaves_congr claimBits_congr paid_laterFo)

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- **THE BRIDGE.** The three clauses of the host's law on the planes, at the layers' forms and at
the world of a ledger H, are the lookups' "true reads" there; and back. -/
theorem readsTrue_iff_hostPlanes {v : Env} {fo : Forest.Heard} {H : Fork} {ν : _root_.Fo.Pl → K}
    {entry : ℕ → ℕ → ℕ → K} {tB0 tB1 tP : ℕ} (b0 : v.tabAt "b-bits-0" = some tB0)
    (b1 : v.tabAt "b-bits-1" = some tB1) (b2 : v.tabAt "b-pin" = some tP) :
    K4ReadsTrue ρ v fo H ν entry ↔
      K3HostPlanes fo.shape v.y.h.lmb (rdL ρ fo.zb0) (rdL ρ fo.zb1) ν
        (fun f => f.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry))
        (k4Bit v tB0 tB1) (k4Pin v tP) := by
  constructor
  · intro h
    obtain ⟨h0, h1, hp⟩ := h tB0 tB1 tP b0 b1 b2
    exact ⟨h0, h1, hp⟩
  · intro hK t0 t1 tp e0 e1 ep
    obtain rfl : tB0 = t0 := Option.some.inj (b0.symm.trans e0)
    obtain rfl : tB1 = t1 := Option.some.inj (b1.symm.trans e1)
    obtain rfl : tP = tp := Option.some.inj (b2.symm.trans ep)
    exact ⟨hK.bit0, hK.bit1, hK.pin⟩

/-- **WHAT THE LAYERS' THREE CLAIMS ON THE PLANES ARE WORTH, AT ν's CELLS.** The lookups'
`k4_planes_worth`, at the letters of the layers' own run and any later ledger, with the readers'
values exchanged for the columns' sums by the three clauses. -/
theorem k4_front_planes_worth {rows : Bool} {P : Pub} {g : ℕ} {o : Own} {F G : Fork}
    {fs : Array Aff} (hfr : Desc.First.K4.formsFrontWith rows P g o F = some (fs, G))
    {F0 : Fork} {first : ℕ} {rs : TwV.Rounds K}
    (hI : _root_.Fo.HeardIs ρ o.H.fo F0 (_root_.Fo.endsOf o.H.fo.shape o.v.y.h.lmb first rs))
    (h0 : _root_.Fo.Later F0 F) (hok : FoNums.ok o.H.fo.shape = true) (hF : PscRun.Sized F)
    {H : Fork} (hH : _root_.Fo.Later G H) (ν : _root_.Fo.Pl → K) (entry : ℕ → ℕ → ℕ → K)
    {tB0 tB1 tP : ℕ} (b0 : o.v.tabAt "b-bits-0" = some tB0) (b1 : o.v.tabAt "b-bits-1" = some tB1)
    (b2 : o.v.tabAt "b-pin" = some tP)
    (hK : K3HostPlanes o.H.fo.shape o.v.y.h.lmb (rdL ρ o.H.fo.zb0) (rdL ρ o.H.fo.zb1) ν
      (fun f => f.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry))
      (k4Bit o.v tB0 tB1) (k4Pin o.v tP)) :
    ∃ lP, planesL o.v o.H.fo = some lP ∧ (∀ f ∈ lP, f ∈ fs.toList) ∧
      (lP.map fun f => f.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) =
        [_root_.Fo.claimLeaves o.H.fo.shape o.v.y.h.lmb first rs ν
            (colsK o.H.fo.shape o.v.y.h.lmb
              (_root_.Fo.endsOf o.H.fo.shape o.v.y.h.lmb first rs).zb0 ν),
          _root_.Fo.claimBits o.H.fo.shape o.v.y.h.lmb first rs ν
            (colsK o.H.fo.shape o.v.y.h.lmb
              (_root_.Fo.endsOf o.H.fo.shape o.v.y.h.lmb first rs).zb1 ν),
          countK o.H.fo.shape o.v.y.h.lmb (pinColK o.v.y.h.lmb ν)] := by
  obtain ⟨F1, F2, pp, rowL, r2, hq, a4, m1, m2, eG⟩ := front_cut hfr
  obtain ⟨at0, at1, count, -, -, -, -, e⟩ := planesParts_cut o.v o.H.fo pp b0 b1 b2 hq
  subst e
  obtain ⟨rfl, -, -⟩ := Desc.First.K4.ownClaim_some a4
  have l2 : _root_.Fo.Later F2 G := by
    rw [eG]
    split
    · exact (paid_laterFo _ _).trans (paid_laterFo _ _)
    · exact paid_laterFo _ _
  have w := k4_planes_worth ρ o.v o.H.fo _ _ _ _ F0 F1 F2 first rs b0 b1 b2 hq a4 hI
    (h0.trans (_root_.Fo.hideRun_later hF r2)) hok (PscRun.hideRun_sized hF r2) H (l2.trans hH) ν
    entry
  refine ⟨_, planesParts_planesL hq, fun f hf => ?_, ?_⟩
  · rcases List.mem_cons.1 hf with rfl | hf
    · exact m1
    · exact m2 _ hf
  · rw [claimLeaves_congr _ _ _ _ _ _
        (colsK o.H.fo.shape o.v.y.h.lmb
          (_root_.Fo.endsOf o.H.fo.shape o.v.y.h.lmb first rs).zb0 ν)
        (fun col hc => by rw [← hI.zb0]; exact hK.bit0 col hc),
      claimBits_congr _ _ _ _ _ _
        (colsK o.H.fo.shape o.v.y.h.lmb
          (_root_.Fo.endsOf o.H.fo.shape o.v.y.h.lmb first rs).zb1 ν)
        (fun col hc => by rw [← hI.zb1]; exact hK.bit1 col hc),
      Cb.Fo.PlaneClaims.countK_congr _ _
        (fun col => ((VerifiableInference.OnPublicFiles.k4Pin o.v tP col).getD {}).value ρ
          (H.worldOf ρ (fun j => ν (.mask j)) entry))
        (pinColK o.v.y.h.lmb ν) fun col hc => hK.pin col hc] at w
    exact w

/-- **So the three planes' forms are all worth 0 just where the lookup's three claims on the planes
hold at ν's cells.** FROM RIGHT TO LEFT IT IS THE TOOTH: a form that is not worth 0 makes one of the
three claims fail. -/
theorem k4_front_planes_paid {rows : Bool} {P : Pub} {g : ℕ} {o : Own} {F G : Fork}
    {fs : Array Aff} (hfr : Desc.First.K4.formsFrontWith rows P g o F = some (fs, G))
    {F0 : Fork} {first : ℕ} {rs : TwV.Rounds K}
    (hI : _root_.Fo.HeardIs ρ o.H.fo F0 (_root_.Fo.endsOf o.H.fo.shape o.v.y.h.lmb first rs))
    (h0 : _root_.Fo.Later F0 F) (hok : FoNums.ok o.H.fo.shape = true) (hF : PscRun.Sized F)
    {H : Fork} (hH : _root_.Fo.Later G H) (ν : _root_.Fo.Pl → K) (entry : ℕ → ℕ → ℕ → K)
    {tB0 tB1 tP : ℕ} (b0 : o.v.tabAt "b-bits-0" = some tB0) (b1 : o.v.tabAt "b-bits-1" = some tB1)
    (b2 : o.v.tabAt "b-pin" = some tP)
    (hK : K3HostPlanes o.H.fo.shape o.v.y.h.lmb (rdL ρ o.H.fo.zb0) (rdL ρ o.H.fo.zb1) ν
      (fun f => f.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry))
      (k4Bit o.v tB0 tB1) (k4Pin o.v tP)) :
    (∀ lP, planesL o.v o.H.fo = some lP →
      ∀ f ∈ lP, f.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) = 0) ↔
    (_root_.Fo.claimLeaves o.H.fo.shape o.v.y.h.lmb first rs ν
        (colsK o.H.fo.shape o.v.y.h.lmb
          (_root_.Fo.endsOf o.H.fo.shape o.v.y.h.lmb first rs).zb0 ν) = 0 ∧
      _root_.Fo.claimBits o.H.fo.shape o.v.y.h.lmb first rs ν
        (colsK o.H.fo.shape o.v.y.h.lmb
          (_root_.Fo.endsOf o.H.fo.shape o.v.y.h.lmb first rs).zb1 ν) = 0 ∧
      countK o.H.fo.shape o.v.y.h.lmb (pinColK o.v.y.h.lmb ν) = 0) := by
  obtain ⟨lP, hL, -, hv⟩ := k4_front_planes_worth ρ hfr hI h0 hok hF hH ν entry b0 b1 b2 hK
  constructor
  · intro hz
    have hall : ∀ y ∈ (lP.map fun f => f.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)),
        y = 0 := by
      intro y hy
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hy
      exact hz lP hL f hf
    rw [hv] at hall
    simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] using hall
  · rintro ⟨e0, e1, e2⟩ lP' hL' f hf
    obtain rfl : lP = lP' := Option.some.inj (hL.symm.trans hL')
    have hm : f.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) ∈
        (lP.map fun f => f.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) :=
      List.mem_map.mpr ⟨f, hf, rfl⟩
    rw [hv, e0, e1, e2] at hm
    simpa using hm

/-- The same under the lookups' name: the right side is `K3Planes`, by unfolding. -/
theorem k4_front_K3Planes {rows : Bool} {P : Pub} {g : ℕ} {o : Own} {F G : Fork}
    {fs : Array Aff} (hfr : Desc.First.K4.formsFrontWith rows P g o F = some (fs, G))
    {F0 : Fork} {first : ℕ} {rs : TwV.Rounds K}
    (hI : _root_.Fo.HeardIs ρ o.H.fo F0 (_root_.Fo.endsOf o.H.fo.shape o.v.y.h.lmb first rs))
    (h0 : _root_.Fo.Later F0 F) (hok : FoNums.ok o.H.fo.shape = true) (hF : PscRun.Sized F)
    {H : Fork} (hH : _root_.Fo.Later G H) (ν : _root_.Fo.Pl → K) (entry : ℕ → ℕ → ℕ → K)
    {tB0 tB1 tP : ℕ} (b0 : o.v.tabAt "b-bits-0" = some tB0) (b1 : o.v.tabAt "b-bits-1" = some tB1)
    (b2 : o.v.tabAt "b-pin" = some tP)
    (hK : K3HostPlanes o.H.fo.shape o.v.y.h.lmb (rdL ρ o.H.fo.zb0) (rdL ρ o.H.fo.zb1) ν
      (fun f => f.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry))
      (k4Bit o.v tB0 tB1) (k4Pin o.v tP)) :
    (∀ lP, planesL o.v o.H.fo = some lP →
      ∀ f ∈ lP, f.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) = 0) ↔
    K3Planes o.H.fo.shape o.v.y.h.lmb first ν rs :=
  k4_front_planes_paid ρ hfr hI h0 hok hF hH ν entry b0 b1 b2 hK

/-- **The item "planes at points" of the lookups' row out, at the layers' own run of claims, in the
world of ANY ledger later than what the run leaves, from the three planes' forms alone.** -/
theorem k4_front_K3OutPlanes {rows : Bool} {P : Pub} {g : ℕ} {o : Own} {F G : Fork}
    {fs : Array Aff} (hfr : Desc.First.K4.formsFrontWith rows P g o F = some (fs, G))
    {F0 : Fork} (first : ℕ)
    (h0 : _root_.Fo.Later F0 F) (hok : FoNums.ok o.H.fo.shape = true) (hF : PscRun.Sized F)
    {H : Fork} (hH : _root_.Fo.Later G H) (ν : _root_.Fo.Pl → K) (entry : ℕ → ℕ → ℕ → K)
    {tB0 tB1 tP : ℕ} (b0 : o.v.tabAt "b-bits-0" = some tB0) (b1 : o.v.tabAt "b-bits-1" = some tB1)
    (b2 : o.v.tabAt "b-pin" = some tP)
    (hK : K3HostPlanes o.H.fo.shape o.v.y.h.lmb (rdL ρ o.H.fo.zb0) (rdL ρ o.H.fo.zb1) ν
      (fun f => f.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry))
      (k4Bit o.v tB0 tB1) (k4Pin o.v tP))
    (hz : ∀ lP, planesL o.v o.H.fo = some lP →
      ∀ f ∈ lP, f.value ρ (H.worldOf ρ (fun j => ν (.mask j)) entry) = 0) :
    K3OutPlanes o.H.fo.shape o.v.y.h.lmb first ν ρ o.H.fo F0 :=
  fun _ hI => (k4_front_planes_paid ρ hfr hI h0 hok hF hH ν entry b0 b1 b2 hK).1 hz

end

#print axioms readsTrue_iff_hostPlanes
#print axioms k4_front_planes_worth
#print axioms k4_front_planes_paid
#print axioms k4_front_K3Planes
#print axioms k4_front_K3OutPlanes

end Meaning.Planes
