-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/PlanesTieK8.lean: the planes' three clauses from what stands in front of the
smallness test's block.

Johnson/Desc/First/K8/LawLay.lean lays the letters of the smallness test's proved block at a public
record tl0, with symbols, reads and digits read off one table of cells (`layReads`); what stands in
front of the block is its relation `relA a w` between a statement a (the carried record and the
strings) and a witness w. Johnson/Desc/First/K8/LawTie.lean says that relation as one plain formula
(`TieOf tl A`). Here the layers' instance of the planes' law is stated from either.

Main theorems (namespace `Meaning.Reads`).
  `u3_of_hear`: a run of the layers' plain hearing shows that the plan's record, closed with any
      shapes, names an array for the third vector of reads.
  `u3Of_of_hear`: that array is the hearing's o.v.iU3. `k4_hu_portWorld`: see THE WORLD.
  `readsAll_of_tie`: `TieOf tl A` gives small integers with the committed packing, and Fo.ReadsAll
      at every table of entries that agrees with A at row 0 of the array u3Of tl below K3.
  `k4_host_planes_of_tie`, `k4_host_planes_tie_pub`: the three clauses at the layers' forms from the
      tie; the second at a record with the public record's numbers and layout (`SamePub`:
      it asks each matrix's rows and columns, not the list of matrices itself).
  `k4_host_planes_of_relA`: the same from `relA a w`, by `tie_of_relA`; the cells under "there is".
  `k4_host_planes_relA_cells`: **from `relA a w`, at THE cells behind the symbols** (`cellN`,
      Johnson/Meaning/ReadsCells.lean): by ReadsTokens.lean at LawLay.lean's letters.

THE WORLD. World.entry is the entry of a VIRTUAL ROW (array, virtual row, index), not a cell. So the
world W is asked to agree with the committed cells AT THE ARRAY OF THE READS ALONE: in the theorems
from the tie at row 0 below K3; in the last at the places of the tables alone. WHO CAN PAY THAT:
`k4_hu_portWorld`: the library's world of committed entries (portWorld), where in its ledger that
array has one row under the weight 1 (UnitRow), the lay's cells of that array lie in rows below its
number of rows (RowsBelow), and the plan's number of reads is at most K3 (hK). That a run's ledger
has the first two is not shown here. A payer whose world is made of the witness's cells (entW) and
not of entE's needs `tie_of_relA`'s hE at that array besides.

ALL PREMISES of `k4_host_planes_relA_cells`: hh (a run of the hearing) · hq (planesParts is there) ·
hT, hG, hgp (the public record; hp a member of its plans) · e0 (tl0 is the plan's record closed with
the public shapes: a choice) · ht (a link is open: the carried record holds a record tl) · h (relA)
· hfun (tl.funs = o.funs: THE CLOSED LIST IN THE CARRIED RECORD IS WHAT THE HEARING HAS LEFT,
weights too) · hu (the world's entries at the tables' places are the committed cells of the array
o.v.iU3, as entE reads them) · h4 (the cells of the planes' matrix, `cellN`, which hang on entE's
symbols alone, are the lookup's); and the letters' own hs, hseat. Thirteen.
ALL PREMISES of `k4_host_planes_of_relA`: hh · hq · hT · hG · hgp · e0 · ht · h · hfun as above; hE,
hgt, hp0, hz (premises of `tie_of_relA`) · hK; hs, hseat: sixteen. hp0 is the layout alone
(`SameLay` at the record in the state: the second half of the condition in front of the block,
`lay_onA`). hz is the numbers (`SameSize tl tl0`). WHO CAN PAY hz: ALL OF `SamePub tl tl0`, at the
record behind a yes of the step that closes the list of tables: `quiet_front`
(Johnson/Meaning/QuietFront.lean); or `sameSize_of_place`
(Johnson/Desc/First/K8/LawPlace.lean) from `placeRec_of_yes` (a yes of the kind's block at a record
in which tl lies) and `PlaceRec p tl0`. THAT tl0 AS e0 FIXES IT HAS THE PLACE'S NUMBERS (PlaceRec p
at the plan's record closed with the public shapes) IS SHOWN NOWHERE HERE. And, IN THE PLACE OF hu
AND h4, inside the conclusion: a premise on the world at row 0 of the array o.v.iU3 below K3, AT
entW's cells, and an h4 on integers b under "there is", which smallness and packing pin, but no
lemma here says that they are `cellN`.
OBJECT · USER · LETTERS. Object: the library's formula `TieOf tl A` and LawLay.lean's `layReads ...
.relA` at a public record tl0; the layers' plain hearing `Desc.First.K4.hearFl` and its
`planesParts`. No seated description is named. User: `readsAll_of_tie`: K5's files' storey over
their own forms; the rest: Johnson/Meaning/PlanesTieK8Member.lean, PlanesTieK8Plan.lean and the row
at the seated description. Letters: ALL OF LawLay.lean's (J, Y, cs, l, seat', arr, entE, entW, G,
smpOf, Cl, F, p, base, e), A, W, ν: free, under "for all".

In `k4_host_planes_of_relA` the premise is hp0 : SameLay (K8.recOf tl0 a.1) tl0, with hz : SameSize
tl tl0 beside it; in `k4_host_planes_tie_pub` the premise hpub : SamePub … says what LawLay.lean's
record says.



Compiled with the whole library.
Limits. NO MEMBER IS SHOWN at these rows: that all premises can hold together is by reading alone.
No draw, no error: these lie with whoever shows relA. Nothing on soundness.
-/
import Johnson.Meaning.ReadsTokens
import Johnson.Desc.First.K8.LawTie
import OnBytes.Tie.Pv.Tail.EndPortUnit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Reads
open OnBytes OnBytes.Model Fo
open OnBytes.Tie.Pv.Tail OnBytes.Road.Rows Cb.Pv.Tail Iop
open OnBytes.Model.Layer (Pub Own HPlan2 matIx tailsOf planG plansG)
open OnBytes.K.Kc
open VerifiableInference.Desc.First.K8 (TieOf SamePub)
open Meaning.Planes

/-- A run of the hearing shows that the plan's record names an array for the third vector of reads.
-/
theorem u3_of_hear {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    (sh : List Tab) : ∃ u, (Closed.closedAt hp.tl sh).ix.U[2]? = some (some u) := by
  have h := (hear_iU3 hh).1
  refine ⟨o.v.iU3, ?_⟩
  show hp.tl.ix.U[2]? = some (some o.v.iU3)
  rw [Array.getD_eq_getD_getElem?] at h
  cases hU : hp.tl.ix.U[2]? with
  | none =>
    rw [hU] at h
    cases h
  | some v =>
    rw [hU] at h
    exact congrArg some h

/-- The array of the reads that the plan's record names, closed with any shapes, is the hearing's.
-/
theorem u3Of_of_hear {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    (sh : List Tab) : Port.u3Of (Closed.closedAt hp.tl sh) = o.v.iU3 := by
  unfold Port.u3Of
  show (hp.tl.ix.U.getD 2 none).getD 0 = o.v.iU3
  rw [(hear_iU3 hh).1]
  rfl

/-- **Who can pay the premise on the world**: the library's world of committed entries m at a ledger
Fs (portWorld), if in Fs the array of the reads has one row under the weight 1, the lay's cells of
that array lie in rows below its number of rows, and the plan's number of reads is at most K3. -/
theorem k4_hu_portWorld {P0 : Pub} {z : Array ℕ} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard}
    {Fk Fk' : Fork} {t t' : Tape} {o : Own}
    (hh : Desc.First.K4.hearFl { P0 with tokv := z } hp g fo Fk t = some (o, Fk', t'))
    {Gp : Array HPlan2} (hG : plansG P0 = .ok Gp) (hgp : Gp[g]? = some hp)
    (hK : hp.nU.getD 2 0 ≤ o.v.K3) {J : Type} [Fintype J] (Y : Lay J) (Fs : Fork)
    (m : J → Cb.Gl.E) (hr : RowsBelow Y Fs o.v.iU3) (h1 : UnitRow Fs o.v.iU3) :
    ∀ f ∈ o.funs.toList, f.tree = 2 → ∀ c < (hp.tl.mats.getD f.mat {}).k,
      ∀ sg < (hp.tl.mats.getD f.mat {}).m / f.len,
        Y.cellAt m o.v.iU3 0 (f.start + c * ((hp.tl.mats.getD f.mat {}).m / f.len) + sg) =
          u3Val (portWorld Reading.gl Y Fs m).entry o.v.iU3 o.v.K3
            (f.start + c * ((hp.tl.mats.getD f.mat {}).m / f.len) + sg) := by
  intro f hf _ c hc sg hsg
  obtain ⟨⟨O, hO⟩, _⟩ := plan_of_plansG hG hgp
  have hlt := k4_entries_below hh { hp.tl with funs := o.funs } rfl
    (sizes_of_map (Road.planG_sizes hO).1) hK f hf c hc sg hsg
  unfold u3Val
  rw [portWorld_unitAt Reading.gl Y Fs m o.v.iU3 hr h1 o.v.K3 _ hlt, Nat.div_eq_of_lt hlt,
    Nat.mod_eq_of_lt hlt]

/-- **The smallness test's tie, spelled as the law of the reads**, at every table of entries that
agrees with A at row 0 of the array of the reads, below K3. -/
theorem readsAll_of_tie {tl : HTailF2} {A : ℕ → ℕ → ℕ → Cb.Gl.E} (h : TieOf tl A) (K3 : ℕ)
    (hpos : ∀ (n : ℕ) (Fn : HFun), tl.funs[n]? = some Fn → ∀ c sg pos,
      tl.tabAt Fn c sg = some pos → pos < K3)
    (hNM : ∀ f ∈ tl.funs.toList, f.tree = 2 → f.mat < tl.NM) :
    ∃ a : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k → ∀ i, i < (tl.mats.getD μ {}).m →
        |a μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) ∧
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
          A (tl.gtTree.getD μ 0) i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => a μ i c) i' : ℤ) :
              Cb.Gl.E)) ∧
      ∀ entry : ℕ → ℕ → ℕ → Cb.Gl.E,
        (∀ pos < K3, entry (Port.u3Of tl) 0 pos = A (Port.u3Of tl) 0 pos) →
        ReadsAll Reading.gl tl.mats tl.funs entry (Port.u3Of tl) K3
          (fun μ r c => ((a μ r c : ℤ) : Cb.Gl.E)) := by
  obtain ⟨a, h1, h2, h3⟩ := h
  refine ⟨a, h1, h2, fun entry he => readsAll_of_tabs Reading.gl tl entry (Port.u3Of tl) K3 _ hNM
    fun n Fn hn c sg pos hp => ?_⟩
  have hlt := hpos n Fn hn c sg pos hp
  rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, he pos hlt]
  exact h3 n Fn hn c sg pos hp

/-- **The three clauses at the layers' forms, from the smallness test's tie.** -/
theorem k4_host_planes_of_tie {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P.tails = tailsOf P.y) (hg : g < P.y.NGr)
    {tl : HTailF2} {A : ℕ → ℕ → ℕ → Cb.Gl.E} (htie : TieOf tl A)
    (hfun : tl.funs = o.funs) (hix : tl.ix.U.getD 2 none = hp.tl.ix.U.getD 2 none)
    (hmat : ∀ μ, (tl.mats.getD μ {}).m = ((P.tails.getD g {}).mats.getD μ {}).m ∧
      (tl.mats.getD μ {}).k = ((P.tails.getD g {}).mats.getD μ {}).k)
    (hK : hp.nU.getD 2 0 ≤ o.v.K3)
    (hNM : ∀ f ∈ tl.funs.toList, f.tree = 2 → f.mat < tl.NM) :
    ∃ a : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k → ∀ i, i < (tl.mats.getD μ {}).m →
        |a μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) ∧
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
          A (tl.gtTree.getD μ 0) i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => a μ i c) i' : ℤ) :
              Cb.Gl.E)) ∧
      ∀ (ν : _root_.Fo.Pl → Cb.Gl.E) (W : World Cb.Gl.E),
        (∀ pos < o.v.K3, W.entry o.v.iU3 0 pos = A o.v.iU3 0 pos) →
        (∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
          ((a (matIx o.v.y).iB r c : ℤ) : Cb.Gl.E) = ν (.cell r c)) →
        ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
          o.v.tabAt "b-pin" = some tP ∧
          K3HostPlanes o.H.fo.shape o.v.y.h.lmb (rdL Reading.gl o.H.fo.zb0)
            (rdL Reading.gl o.H.fo.zb1) ν (fun f => f.value Reading.gl W)
            (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  obtain ⟨a, h1, h2, h3⟩ := readsAll_of_tie htie o.v.K3 (k4_places_below hh tl hfun hmat hK) hNM
  have eU : Port.u3Of tl = o.v.iU3 := by
    unfold Port.u3Of
    rw [hix, (hear_iU3 hh).1]
    rfl
  rw [eU, hfun] at h3
  refine ⟨a, h1, h2, fun ν W hW h4 => ?_⟩
  exact k4_host_planes_at Reading.gl hh hq hT hg _ _ rfl rfl
    (fun μ r c => ((a μ r c : ℤ) : Cb.Gl.E)) ν h4 W (readsAll_sizes Reading.gl hmat (h3 W.entry hW))

/-- **The same at a record with the public record's numbers**: tl0 is the plan's record, closed with
the public shapes; hp is a member of the list of plans of the record that holds no token. -/
theorem k4_host_planes_tie_pub {P0 : Pub} {z : Array ℕ} {hp : HPlan2} {g : ℕ}
    {fo : Forest.Heard} {F F' : Fork} {t t' : Tape} {o : Own}
    (hh : Desc.First.K4.hearFl { P0 with tokv := z } hp g fo F t = some (o, F', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P0.tails = tailsOf P0.y) {G : Array HPlan2} (hG : plansG P0 = .ok G)
    (hgp : G[g]? = some hp)
    {tl : HTailF2} {A : ℕ → ℕ → ℕ → Cb.Gl.E} (htie : TieOf tl A)
    (hpub : SamePub tl (Closed.closedAt hp.tl (Closed.layShapes { P0 with tokv := z } g)))
    (hfun : tl.funs = o.funs) (hK : hp.nU.getD 2 0 ≤ o.v.K3) :
    ∃ a : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k → ∀ i, i < (tl.mats.getD μ {}).m →
        |a μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) ∧
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
          A (tl.gtTree.getD μ 0) i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => a μ i c) i' : ℤ) :
              Cb.Gl.E)) ∧
      ∀ (ν : _root_.Fo.Pl → Cb.Gl.E) (W : World Cb.Gl.E),
        (∀ pos < o.v.K3, W.entry o.v.iU3 0 pos = A o.v.iU3 0 pos) →
        (∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
          ((a (matIx o.v.y).iB r c : ℤ) : Cb.Gl.E) = ν (.cell r c)) →
        ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
          o.v.tabAt "b-pin" = some tP ∧
          K3HostPlanes o.H.fo.shape o.v.y.h.lmb (rdL Reading.gl o.H.fo.zb0)
            (rdL Reading.gl o.H.fo.zb1) ν (fun f => f.value Reading.gl W)
            (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  obtain ⟨⟨O, hO⟩, hg⟩ := plan_of_plansG hG hgp
  obtain ⟨s1, s2⟩ := Road.planG_sizes hO
  have hn : tl.NM = hp.tl.NM := hpub.nm
  have hi : tl.ix = hp.tl.ix := hpub.ix
  have hsz : hp.tl.mats.size = (P0.tails.getD g {}).mats.size := by
    have := congrArg Array.size s1
    simpa using this
  refine k4_host_planes_of_tie hh hq hT hg htie hfun (by rw [hi])
    (fun μ => ⟨(hpub.m μ).trans (sizes_of_map s1 μ).1, (hpub.k μ).trans (sizes_of_map s1 μ).2⟩) hK
    fun f hf _ => ?_
  rw [hn, s2, hsz]
  rw [hfun] at hf
  exact k4_mats_below hh hT hg f hf

section AtTheLetters
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.Sound OnBytes.Maker Johnson.Pack

variable {J : Type} [Fintype J] (Y : Lay J) (tl0 : HTailF2) (cs : OnBytes.Codes)
  (l : List (OnBytes.OracleShape × ℕ)) (seat' : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  {Cells Tok : Type} (entE : (sigOf cs l).Msg → J → Cb.Gl.E)
  (entW : Wit Cells Tok MsgT → J → Cb.Gl.E)
  {Xi : Type} (G : FileDescription Xi) (smpOf : S → (sigOf cs l).Smp)
  (hs : ∀ (s : S) (tl : HTailF2) (mm : Array Int) (f : Array Nat), s.tl? = some tl →
    smpOf (s.putTl { tl with cfF := mm, cfFirst := f }) = smpOf s)
  (Cl : Type) (F : Frame) (p : K8.Par) (base e : ℕ) (hseat : ∀ i, (seat' i).1 < base)

/-- **The three clauses at the layers' forms, for every statement and witness in the relation that
stands in front of the smallness test's block**, where a link is open, the condition's second half
holds (hp0: the layout) and the open link's record has the public record's numbers (hz), in every
world that agrees with the witness's committed cells at row 0 of the array of the reads, below K3.
tl0: the plan's record, closed with the public shapes. -/
theorem k4_host_planes_of_relA {P0 : Pub} {z : Array ℕ} {hp : HPlan2} {g : ℕ}
    {fo : Forest.Heard} {Fk Fk' : Fork} {t t' : Tape} {o : Own}
    (hh : Desc.First.K4.hearFl { P0 with tokv := z } hp g fo Fk t = some (o, Fk', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P0.tails = tailsOf P0.y) {Gp : Array HPlan2} (hG : plansG P0 = .ok Gp)
    (hgp : Gp[g]? = some hp)
    (e0 : tl0 = Closed.closedAt hp.tl (Closed.layShapes { P0 with tokv := z } g))
    (hE : ∀ w j, early tl0 (Y.addr j) = true → entE (msgsOf cs l seat' arr w) j = entW w j)
    (hgt : tl0.NM ≤ tl0.gtTree.size)
    (a : S × F.E.Str) (w : Wit Cells Tok MsgT) (tl : HTailF2) (ht : a.1.tl? = some tl)
    (hp0 : SameLay (K8.recOf tl0 a.1) tl0) (hz : SameSize tl tl0)
    (h : (layReads Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat).relA a w)
    (hfun : tl.funs = o.funs) (hK : hp.nU.getD 2 0 ≤ o.v.K3) :
    ∃ b : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k → ∀ i, i < (tl.mats.getD μ {}).m →
        |b μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) ∧
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
          Y.cellAt (entW w) (tl.gtTree.getD μ 0) i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => b μ i c) i' : ℤ) :
              Cb.Gl.E)) ∧
      ∀ (ν : _root_.Fo.Pl → Cb.Gl.E) (W : World Cb.Gl.E),
        (∀ pos < o.v.K3, W.entry o.v.iU3 0 pos = Y.cellAt (entW w) o.v.iU3 0 pos) →
        (∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
          ((b (matIx o.v.y).iB r c : ℤ) : Cb.Gl.E) = ν (.cell r c)) →
        ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
          o.v.tabAt "b-pin" = some tP ∧
          K3HostPlanes o.H.fo.shape o.v.y.h.lmb (rdL Reading.gl o.H.fo.zb0)
            (rdL Reading.gl o.H.fo.zb1) ν (fun f => f.value Reading.gl W)
            (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  have hu : ∃ u, tl0.ix.U[2]? = some (some u) := by
    rw [e0]
    exact u3_of_hear hh _
  obtain ⟨tl', ht', htie⟩ := tie_of_relA Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e
    hseat hE hgt hu a w tl ht hp0 hz h
  obtain rfl : tl = tl' := Option.some.inj (ht.symm.trans ht')
  have hx : K8.recOf tl0 a.1 = blank tl := by
    unfold K8.recOf
    rw [ht]
    rfl
  have hpub : SamePub tl tl0 := by
    rw [hx] at hp0
    exact { toSameSize := hz, toSameLay := ⟨hp0.gt, hp0.ix, hp0.mz, hp0.off⟩ }
  rw [e0] at hpub
  exact k4_host_planes_tie_pub hh hq hT hG hgp htie hpub hfun hK

/-- **The three clauses at the layers' forms, for every statement and witness in the relation that
stands in front of the smallness test's block, at THE cells behind the symbols**, where a link is
open. The world is asked for at the tables' places alone. -/
theorem k4_host_planes_relA_cells {P0 : Pub} {z : Array ℕ} {hp : HPlan2} {g : ℕ}
    {fo : Forest.Heard} {Fk Fk' : Fork} {t t' : Tape} {o : Own}
    (hh : Desc.First.K4.hearFl { P0 with tokv := z } hp g fo Fk t = some (o, Fk', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P0.tails = tailsOf P0.y) {Gp : Array HPlan2} (hG : plansG P0 = .ok Gp)
    (hgp : Gp[g]? = some hp)
    (e0 : tl0 = Closed.closedAt hp.tl (Closed.layShapes { P0 with tokv := z } g))
    (a : S × F.E.Str) (w : Wit Cells Tok MsgT) (tl : HTailF2) (ht : a.1.tl? = some tl)
    (h : (layReads Y tl0 cs l seat' arr entE entW G smpOf hs Cl F p base e hseat).relA a w)
    (hfun : tl.funs = o.funs) (W : World Cb.Gl.E)
    (hu : ∀ f ∈ o.funs.toList, f.tree = 2 → ∀ c < (hp.tl.mats.getD f.mat {}).k,
      ∀ sg < (hp.tl.mats.getD f.mat {}).m / f.len,
        Y.cellAt (entE (msgsOf cs l seat' arr w)) o.v.iU3 0
            (f.start + c * ((hp.tl.mats.getD f.mat {}).m / f.len) + sg) =
          u3Val W.entry o.v.iU3 o.v.K3
            (f.start + c * ((hp.tl.mats.getD f.mat {}).m / f.len) + sg))
    (ν : _root_.Fo.Pl → Cb.Gl.E)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      cellN tl0 (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT) (symL Y tl0 entE)
        (u3L Y tl0 entE) (digL Y tl0 entW)) (msgsOf cs l seat' arr w) (matIx o.v.y).iB r c =
        ν (.cell r c)) :
    ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
      o.v.tabAt "b-pin" = some tP ∧
      K3HostPlanes o.H.fo.shape o.v.y.h.lmb (rdL Reading.gl o.H.fo.zb0)
        (rdL Reading.gl o.H.fo.zb1) ν (fun f => f.value Reading.gl W)
        (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  have h' : relIn (thetaRec tl0 (sigOf cs l).Msg (Wit Cells Tok MsgT) (symL Y tl0 entE)
      (u3L Y tl0 entE) (digL Y tl0 entW)).letters (K8.recOf tl0 a.1) (msgsOf cs l seat' arr w) :=
    h.2.2
  have hx : K8.recOf tl0 a.1 = blank tl := by
    unfold K8.recOf
    rw [ht]
    rfl
  rw [hx] at h'
  subst e0
  have eU := u3Of_of_hear hh (Closed.layShapes { P0 with tokv := z } g)
  refine k4_host_planes_tokens Reading.gl hh hq hT hG hgp _ _ rfl rfl _ h' (fun n Fn hn j _ => ?_)
    W (fun f hf ht c hc sg hsg => ?_) ν h4
  swap
  · show Y.cellAt _ (Port.u3Of _) 0 _ = _
    rw [eU]
    exact hu f hf ht c hc sg hsg
  show phiAt Reading.gl (blank tl) n j = _
  unfold phiAt
  have e : (blank tl).funs.getD n default = Fn := by
    show tl.funs.getD n default = Fn
    rw [hfun, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, hn]
    rfl
  rw [e]

end AtTheLetters

#print axioms u3_of_hear
#print axioms u3Of_of_hear
#print axioms k4_hu_portWorld
#print axioms k4_host_planes_of_relA
#print axioms k4_host_planes_relA_cells
#print axioms readsAll_of_tie
#print axioms k4_host_planes_of_tie
#print axioms k4_host_planes_tie_pub

end Meaning.Reads
