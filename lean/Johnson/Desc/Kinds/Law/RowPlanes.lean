-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Over the seats Stored/HeadSeatAt.lean and Stored/ReplySeatAt.lean, which go with Block.lean and
State.lean. planesRun_claims: the
run "planes" makes its three claims by planeClaimsOwn: the lookup's own
theorem planeClaimsOwn_eq (First/Look/LookPlanesOwnAgrees.lean, imported) brings it back to
planeClaimsF. rowPlanes takes two premises on the reads' array: it is there, with
a column: the seat's reader planesAt refuses without them.
Johnson/Desc/Kinds/Law/RowPlanes.lean: THE OUTPUT HEAD's ROW's CLAUSE ON "planes", WHICH STOOD ON
NEITHER SIDE OF K6Out | K6In (Law/RowPins.lean: no def of it turns): K6OutP | K6InP
BESIDE THEM, AND THE IMPLICATION, BOTH WAYS: rowPlanes. No draw, no error term: a tie in one world.
OBJECT: the lookup's run "planes" at the seat on a link's calls and THE HEAD's OWN READERS:
K3.planesRun (K3.seatCalls claim) lm (callerReaders (planesAt (readsOf W))) (planesRun_at: its
claims ARE the three forms of which K6OutP speaks). THAT THE SEATED DESCRIPTION STATES THIS VERY
TERM AT THE HEAD's LOOKUP IS NOT HELD HERE (the
lookup's block states "planes" by K3.withCaller: not this file's). USERS: Law/RowPlanesHost.lean ·
Law/PlanesRoad.lean. Meant for the table's item "planes" at the head, and for the lookup's law,
which spends the planes at every lookup. LETTERS: below.
  planesRun_claims | planesRun_at   what the run returns.
  K6OutP W lm sP Wd   WHAT THE ROW OPENS: the three forms, at what the lookup has heard at sP and at
  the head's readers (entries of the vector of reads), are worth 0 in the world Wd.
  K6InP lm sP Wd nu   WHAT IT CLOSES: the same three WITH THE COLUMNS' COMBINATIONS OF THE CELLS nu
  LAID IN (the library's colsK at the lookup's two points zb0 | zb1; pinColK)
  are worth 0.
  planes_exchange     under K3HostPlanes
  (Johnson/Meaning/PlanesLaw.lean): the one is so just where the other is.
  rowPlanes           MAIN: K6OutP W lm sP Wd IFF K6InP lm sP Wd nu, UNDER THE PREMISES OF
  head_host_planes_at (Law/HeadPlanes.lean), TO THE LETTER.
EVERY LETTER UNDER "THERE IS", AND WHAT PINS IT: gk: sP.lookHeard? = some gk · r: callerReaders
(planesAt (readsOf W)) sP = some r. UNDER "FOR ALL" IN rowPlanes, AND WHO READS THEM: Wd (the
world): read by both sides and by ReadsAll: TIED TO NO LEDGER AND NO RECORD HERE: the caller's · nu:
by K6InP and by h4 alone · cellM: by h4 and
ReadsAll · mats · funs: by the three LaidAt, hm, hk and ReadsAll: TIED TO THE RECORD's OWN TABLES
tt.funs BY NOTHING HERE · iB: meant NHf + 2: a letter · lm: meant the head's lmbH: a letter · b0 b1:
pinned by Forest.phiB gk lm 0 | 1 = some · e0 e1 eP: pinned by tt.tab.find? · o F tt: pinned by sP's
fields.
WHAT STAYS A PREMISE (all of head_host_planes_at's): (1) THE LAW OF THE READS: ReadsAll at Wd's
entries, the reads' array, its width in sP's ledger, and the cells cellM: K8's and the sending's
matter: NOT SHOWN · (2) three LaidAt: at the three tables' first entries the list funs holds the
planes' matrix iB in blocks of 2^lm rows under the
lookup's own weights b0 | b1 | phiP · (3) the three tables stand in the record's table of tables
with at least the planes' columns (h0 h1 hP l0 l1 lP) · (4) Forest.phiB returns twice · (5) the
matrix has its rows in one block and at least the planes' columns (hm hk) · (6) its cells are the
lookup's (h4) · (7) sP stands in the head's
link with a ledger AND WITH THE READS' PLACES LAID (o.t = some tt): so sP IS NOT THE RECORD BEHIND
K6's BLOCK: there the readers give nothing (not checked here: they answer from H:6 on).
WHAT IT IS NOT. No law on a decision or a step · not the join to K6Out | K6In's own records (s'
behind the block; s in front): these two clauses speak at a later record sP and at a world that is a
letter · that the three forms ARE worth 0 (K6OutP) is K9's batching's to give · no member: no values
at which the premises hold together are
shown. Nothing on soundness.
IMPORTED, NOT PROVED HERE: head_host_planes_at | planesAt_readers (Law/HeadPlanes.lean);
K3HostPlanes, LaidAt (Johnson/Meaning/PlanesLaw.lean | PlanesKit.lean);
the library's colsK, pinColK, rdL, ReadsAll, planeCols.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.PlanesValue
import Johnson.Desc.Kinds.Law.HeadPlanes
import Johnson.Desc.Kinds.Law.RowPins
import Johnson.Desc.First.Look.LookPlanesOwnAgrees

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model OnBytes.K.Kc
open Cb Cb.Fo Cb.Fo.NumsEq TwV Fo Meaning.Planes
open Cb.Fo.Pin
open VerifiableInference.Desc.First (S HeadOwn)
open Planes

/-- **WHAT THE RUN "planes" RETURNS**: its claims are the three forms planeForms, at what the lookup
has heard and at the forms that the caller's readers give, each as a claim. -/
theorem planesRun_claims {S' Cl : Type} (seat : K3.Seat S' Cl) (lm : Nat) (readers : K3.Readers S')
    (n : Nat) (s : S') (y : List Cl × S') (hy : K3.planesRun seat lm readers n s = .ok y) :
    ∃ g r, seat.heard s = some g ∧ readers s = some r ∧
      y.1 = (planeForms g lm (fun e col => (r.1 e col).getD {})
        fun col => (r.2 col).getD {}).toList.map seat.claim := by
  unfold K3.planesRun at hy
  simp only [bind, Except.bind] at hy
  cases hF : seat.fork s with
  | none => simp [hF, named] at hy
  | some F =>
    cases hg : seat.heard s with
    | none => simp [hF, hg, named] at hy
    | some g =>
      simp only [hF, hg, named] at hy
      split at hy
      · cases hy
      · cases hr : readers s with
        | none => simp [hr] at hy
        | some r =>
          simp only [hr] at hy
          split at hy
          · cases hy
          · rename_i x hx
            rw [First.Look.planeClaimsOwn_eq] at hx
            cases hall : (First.Look.planeClaimsF g lm (fun e col => Fl.need (r.1 e col))
                fun col => Fl.need (r.2 col)).andThen
                (fun fs => (First.Look.planesAddedF g).andThen fun _ => pure fs) F [] with
            | none => rw [hall] at hx; cases hx
            | some v =>
              rw [hall] at hx
              have ev : v = x := Except.ok.inj hx
              subst ev
              obtain ⟨fs, G, u, h1, h2⟩ := andThen_some _ _ F [] _ hall
              obtain ⟨_, G2, u2, _, h3⟩ := andThen_some _ _ G u _ h2
              have h3' : (some (fs, G2, u2) : Option (Array Aff × Fork × Tape)) = some v := h3
              have e1 : v.1 = fs := by rw [← Option.some.inj h3']
              obtain ⟨_, hfs⟩ := planeClaimsF_spec g lm r.1 r.2 fs F G [] u h1
              have ey := Except.ok.inj hy
              refine ⟨g, r, rfl, rfl, ?_⟩
              rw [← ey]
              show List.map seat.claim v.1.toList = _
              rw [e1, hfs]

/-- **WHAT THE ROW OPENS ON "planes"**, at a record sP at which the head's readers are there, in a
world Wd: the three forms of the run "planes", at what the lookup has heard and AT THE HEAD's OWN
READERS (entries of the vector of reads), are worth 0. -/
def K6OutP (W : OnBytes.Model.Verify.Public) (lm : Nat) (sP : S) (Wd : World K) : Prop :=
  ∃ gk r, sP.lookHeard? = some gk ∧ callerReaders (planesAt (readsOf W)) sP = some r ∧
    ∀ f ∈ (planeForms gk lm (fun e col => (r.1 e col).getD {})
      fun col => (r.2 col).getD {}).toList, f.value Reading.gl Wd = 0

/-- **WHAT IT CLOSES ON "planes"**: the same three, WITH THE COLUMNS' COMBINATIONS OF THE CELLS ν
LAID IN for the readers' forms (the library's colsK at the lookup's two points; pinColK), are worth
0. None of the head's readers' entries is read any more. -/
def K6InP (lm : Nat) (sP : S) (Wd : World K) (ν : _root_.Fo.Pl → K) : Prop :=
  ∃ gk, sP.lookHeard? = some gk ∧
    ∀ x ∈ planeVals Reading.gl Wd gk lm (colsK gk.shape lm (rdL Reading.gl gk.zb0) ν)
      (colsK gk.shape lm (rdL Reading.gl gk.zb1) ν) (pinColK lm ν), x = 0

/-- The one step: where the caller's forms are worth the columns' combinations
(K3HostPlanes), the three forms are worth 0 just where the three values are. -/
theorem planes_exchange (g : Forest.Heard) (lm : Nat) (bit : Nat → Nat → Aff) (pin : Nat → Aff)
    (ν : _root_.Fo.Pl → K) (Wd : World K)
    (H : K3HostPlanes g.shape lm (rdL Reading.gl g.zb0) (rdL Reading.gl g.zb1) ν
      (fun f => f.value Reading.gl Wd) bit pin) :
    (∀ f ∈ (planeForms g lm bit pin).toList, f.value Reading.gl Wd = 0) ↔
      ∀ x ∈ planeVals Reading.gl Wd g lm (colsK g.shape lm (rdL Reading.gl g.zb0) ν)
        (colsK g.shape lm (rdL Reading.gl g.zb1) ν) (pinColK lm ν), x = 0 := by
  rw [← planeForms_values Reading.gl Wd g lm bit pin _ _ _ H.bit0 H.bit1 H.pin]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

/-- **THE ROW's CLAUSE ON "planes": WHAT IS OPENED IS WORTH WHAT IS CLOSED**, under the premises of
head_host_planes_at (Law/HeadPlanes.lean), to the letter, at the reads' array readsOf W. No
draw, no error term. -/
theorem rowPlanes (W : OnBytes.Model.Verify.Public) {mats : Array TMat} {funs : Array HFun}
    {cellM : Nat → Nat → Nat → K} (gk : Forest.Heard) {lm iB : Nat}
    {b0 b1 : Array E} (y0 : Forest.phiB gk lm 0 = some b0) (y1 : Forest.phiB gk lm 1 = some b1)
    {sP : S} {o : HeadOwn} {F : Fork} {tt : Head.Tables}
    (hgk : sP.lookHeard? = some gk)
    (ho : sP.here = .head o) (hF : sP.fork? = some F) (ht : o.t = some tt)
    {tr : HTree} (htr : F.trees[readsOf W]? = some tr) (hK : tr.K ≠ 0)
    {e0 e1 eP : String × Nat × Nat}
    (h0 : (tt.tab.find? fun e => e.1 == "bH-bits-0") = some e0)
    (h1 : (tt.tab.find? fun e => e.1 == "bH-bits-1") = some e1)
    (hP : (tt.tab.find? fun e => e.1 == "bH-pin") = some eP)
    (l0 : planeCols gk.shape lm ≤ e0.2.2) (l1 : planeCols gk.shape lm ≤ e1.2.2)
    (lP : planeCols gk.shape lm ≤ eP.2.2)
    (T0 : LaidAt funs e0.2.1 iB (2 ^ lm) b0) (T1 : LaidAt funs e1.2.1 iB (2 ^ lm) b1)
    (TP : LaidAt funs eP.2.1 iB (2 ^ lm) (Forest.phiP lm))
    (hm : (mats.getD iB {}).m / 2 ^ lm = 1) (hk : planeCols gk.shape lm ≤ (mats.getD iB {}).k)
    (ν : _root_.Fo.Pl → K)
    (h4 : ∀ r < 2 ^ lm, ∀ c < planeCols gk.shape lm, cellM iB r c = ν (.cell r c))
    (Wd : World K)
    (hA : ReadsAll Reading.gl mats funs Wd.entry (readsOf W)
      (((F.trees[readsOf W]?).map (·.K)).getD 1) cellM) :
    K6OutP W lm sP Wd ↔ K6InP lm sP Wd ν := by
  obtain ⟨r, hr, H⟩ := head_host_planes_at Reading.gl gk y0 y1 ho hF ht htr hK h0 h1 hP l0 l1 lP T0
    T1 TP hm hk ν h4 Wd hA
  have X := planes_exchange gk lm _ _ ν Wd H
  constructor
  · rintro ⟨g2, r2, hg2, hr2, hv⟩
    obtain rfl : gk = g2 := Option.some.inj (hgk.symm.trans hg2)
    obtain rfl : r = r2 := Option.some.inj (hr.symm.trans hr2)
    exact ⟨gk, hgk, X.mp hv⟩
  · rintro ⟨g2, hg2, hv⟩
    obtain rfl : gk = g2 := Option.some.inj (hgk.symm.trans hg2)
    exact ⟨gk, r, hgk, hr, X.mpr hv⟩

/-- **K6OutP IS A SENTENCE ON THE RUN's OWN CLAIMS**: where the lookup's run "planes", at the seat
on a link's calls and the head's readers, returns at sP: its claims are the three forms of which
K6OutP speaks, each as a claim. -/
theorem planesRun_at {Cl : Type} (claim : Aff → Cl) (W : OnBytes.Model.Verify.Public) (lm n : Nat)
    (sP : S) (y : List Cl × S)
    (hy : K3.planesRun (K3.seatCalls claim) lm (callerReaders (planesAt (readsOf W))) n sP
      = .ok y) :
    ∃ gk r, sP.lookHeard? = some gk ∧ callerReaders (planesAt (readsOf W)) sP = some r ∧
      y.1 = (planeForms gk lm (fun e col => (r.1 e col).getD {})
        fun col => (r.2 col).getD {}).toList.map claim :=
  planesRun_claims (K3.seatCalls claim) lm _ n sP y hy

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.rowPlanes
#print axioms VerifiableInference.Desc.Kinds.Head.Law.planesRun_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.planesRun_claims
#print axioms VerifiableInference.Desc.Kinds.Head.Law.planes_exchange
