-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/ReadsK4.lean: the layers' debt to the lookup on the planes, from the relation that
stands in front of the draw of the smallness test's matrix.

Johnson/Meaning/PlanesHost.lean pays the three clauses on the planes (`K3HostPlanes`,
Johnson/Meaning/PlanesLaw.lean) in every world with the law of the reads.
Johnson/Meaning/ReadsLaw.lean gets that law, in the world of the committed entries, from the first
joint of the smallness test's proved block. Here the two are joined at a record of the smallness
test that holds the tables which the layers' hearing has left.

Main theorems (namespace `Meaning.Reads`).
  `hear_iU3`: the array of the reads and its width, as a run of the hearing leaves them.
  `hear_shapes`: the matrices, lengths and first entries of the hearing's tables are public: those
      of what layTables lays. `tails_iB_lt`: the planes' matrix is one of the group's list.
  `k4_entries_below`, `k4_places_below`: every entry of such a table lies below K3, if the plan's
      number of reads is at most K3.
  `k4_readsAll_of_relIn`: the law of the reads at the layers' own tables and list of matrices.
  `k4_host_planes_of_relIn`: **the three clauses at the layers' forms, in the world of the committed
      entries**: there is one integer matrix for each committed matrix, small, whose packing is the
      committed symbols, such that for every reading ν of the lookup's places that takes the cells
      of the planes' matrix to these integers' images, the three clauses hold.
  `k4_host_planes_of_atA`: the same at any letters of the smallness test that are read off the
      arrays' entries A (the library's AtA, OnBytes/Tie/Pv/Tail/EndsAt.lean), in every world whose
      entries of virtual rows are A; there the premises on the lay and the ledger fall away.
  `k4_host_planes_cells`: **the same with the integers named**: THE cells behind the committed
      symbols (`cellN`, Johnson/Meaning/ReadsCells.lean), in the library's field, at any letters
      over the record's sizes, with just the two premises on the letters that are spent.
  `k4_host_planes_cells_atA`: at letters that are read off the arrays' entries A.
  `k4_member`: at EVERY record with the shapes of the hearing's tables and the sizes of the group's
      matrices there are letters and a world that meet together the premises of
      `k4_host_planes_cells` on them, whatever small integers stand in the cells. `k4_record`: such
      a record there is, with no weight in it.

Premises that nobody pays here. On the record tl: its tables are the hearing's (tl.funs = o.funs);
its matrices have the sizes of the group's list; each table's matrix is one of the record's. On the
lay and the ledger: the cells of the array of the reads and of the symbol arrays are early; that
array has one row with the weight 1 (RowsBelow, UnitRow). On the plan: hp.nU[2] is at most o.v.K3.
THE RELATION IN FRONT OF THE DRAW. And those of `k4_host_planes_at`.
Limits. No draw, no error term: the error lies in whoever shows the relation in front of the draw.
That ν is the reading at which the lookup's claims are judged is the spender's to show; the integers
are pinned by "small, with the committed packing" (Cb/Pv/Tail/Unique.lean). Nothing on soundness.

-/
import Johnson.Meaning.ReadsMember
import Johnson.Meaning.PlanesNumbers
import Johnson.Meaning.PlanesLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Reads
open Finset
open OnBytes OnBytes.Model Fo
open OnBytes.Tie.Pv.Tail OnBytes.Road.Rows Cb.Pv.Tail Iop
open OnBytes.Model.Layer (Pub Own HPlan2 matIx tailsOf Lay TableAsk layTables tableAsks)
open OnBytes.K.Kc
open Meaning.Planes
open Meaning.HKT (bind_some pure_some)

/-- What a run of the layers' plain hearing leaves on the array of the reads: its number is the
plan's record's third vector's, and K3 is the number of its columns in the planned ledger. -/
theorem hear_iU3 {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (h : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t')) :
    hp.tl.ix.U.getD 2 none = some o.v.iU3 ∧
      o.v.K3 = ((hp.Fp.trees[o.v.iU3]?).map (·.K)).getD 0 := by
  unfold Desc.First.K4.hearFl Desc.First.K4.hear at h
  obtain ⟨_, _, _, _, h⟩ := bind_some h
  obtain ⟨_, _, _, _, h⟩ := bind_some h
  obtain ⟨iU3, _, _, hi, h⟩ := bind_some h
  obtain ⟨H0, _, _, _, h⟩ := bind_some h
  obtain ⟨H, _, _, _, h⟩ := bind_some h
  obtain ⟨_, _, _, _, h⟩ := bind_some h
  obtain ⟨⟨tab, laid, nU3⟩, _, _, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨_, _, _, _, h⟩ := bind_some h
  obtain ⟨K, _, _, _, h⟩ := bind_some h
  obtain ⟨⟨hd, hd2⟩, _, _, _, h⟩ := bind_some h
  dsimp only at h
  obtain ⟨_, _, _, _, h⟩ := bind_some h
  obtain ⟨claimsP, _, _, _, h⟩ := bind_some h
  split at h <;>
  · obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    obtain ⟨_, _, _, _, h⟩ := bind_some h
    rw [pure_some h]
    exact ⟨need_val hi, rfl⟩

/-- The matrices, lengths and first entries of the tables that layTables has laid, in their order.
-/
def shapesOf (laid : List (TableAsk × List (ℕ × ℕ))) : List Tab :=
  (laid.map fun x => x.2.map fun m => (⟨m.1, x.1.L, m.2⟩ : Tab)).flatten

theorem flat_shapes (y : Lay) (fo : Forest.Heard) (pt : List (String × Array E)) :
    ∀ (laid : List (TableAsk × List (ℕ × ℕ))) (l : List (List HFun)),
    laid.mapM (famFuns y fo pt) = some l →
      l.flatten.map (fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)) = shapesOf laid
  | [], l, h => by
    have e : [] = l := by simpa using h
    rw [← e]
    rfl
  | x :: rest, l, h => by
    rw [List.mapM_cons] at h
    obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨zs, hzs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl : z :: zs = l := Option.some.inj h
    unfold famFuns at hz
    obtain ⟨phi, _, hz⟩ := Option.bind_eq_some_iff.mp hz
    obtain rfl := Option.some.inj hz
    have ih := flat_shapes y fo pt rest zs hzs
    unfold shapesOf at ih ⊢
    rw [List.flatten_cons, List.map_append, ih, List.map_cons, List.flatten_cons, List.map_map]
    rfl

/-- **The shapes of the hearing's tables are public**: they are those of what layTables lays at the
group's list of matrices and the public families of tables; nothing drawn enters. -/
theorem hear_shapes {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t')) :
    ∃ laid,
      layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) (tableAsks P.y P.rd g) 0 =
        some (o.v.tab, laid, hp.nU.getD 2 0) ∧
      o.funs.toList.map (fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)) = shapesOf laid := by
  obtain ⟨laid, pt, hl, hf⟩ := hear_tables_n hh
  refine ⟨laid, hl, ?_⟩
  have h' : (laid.mapM (famFuns P.y fo pt)).bind (fun l => some l.flatten.toArray) = some o.funs :=
    hf
  obtain ⟨l, hl', e⟩ := Option.bind_eq_some_iff.mp h'
  rw [← Option.some.inj e, List.toList_toArray]
  exact flat_shapes P.y fo pt laid l hl'

/-- The planes' matrix is one of the group's list. -/
theorem tails_iB_lt (y : Lay) (g : ℕ) (hg : g < y.NGr) :
    (matIx y).iB < ((tailsOf y).getD g {}).mats.size := by
  unfold tailsOf
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range, hg, if_true,
    Option.map_some, Option.getD_some, List.size_toArray, List.length_map, List.length_zipIdx,
    List.length_append, List.length_range, List.length_cons, List.length_nil]
  show y.parts.getD 0 0 + y.parts.getD 1 0 + 1 < _
  simp only [Array.getD_eq_getD_getElem?]
  omega

/-- Every entry of one of the hearing's tables lies below K3, if the plan's number of reads is at
most K3. -/
theorem k4_entries_below {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    (tl : HTailF2) (hfun : tl.funs = o.funs)
    (hmat : ∀ μ, (tl.mats.getD μ {}).m = ((P.tails.getD g {}).mats.getD μ {}).m ∧
      (tl.mats.getD μ {}).k = ((P.tails.getD g {}).mats.getD μ {}).k)
    (hK : hp.nU.getD 2 0 ≤ o.v.K3) :
    ∀ f ∈ tl.funs.toList, ∀ c < (tl.mats.getD f.mat {}).k,
      ∀ sg < (tl.mats.getD f.mat {}).m / f.len,
        f.start + c * ((tl.mats.getD f.mat {}).m / f.len) + sg < o.v.K3 := by
  intro Fn hmem c g2 sg g3
  rw [hfun] at hmem
  have hb := (k4_tables_apart hh).1 Fn hmem
  unfold entriesOf stretches at hb
  rw [← (hmat Fn.mat).1, ← (hmat Fn.mat).2] at hb
  have h1 : c * ((tl.mats.getD Fn.mat {}).m / Fn.len) + sg <
      (tl.mats.getD Fn.mat {}).k * ((tl.mats.getD Fn.mat {}).m / Fn.len) := by
    calc c * ((tl.mats.getD Fn.mat {}).m / Fn.len) + sg
        < c * ((tl.mats.getD Fn.mat {}).m / Fn.len) + (tl.mats.getD Fn.mat {}).m / Fn.len :=
          Nat.add_lt_add_left g3 _
      _ = (c + 1) * ((tl.mats.getD Fn.mat {}).m / Fn.len) := by rw [Nat.succ_mul]
      _ ≤ (tl.mats.getD Fn.mat {}).k * ((tl.mats.getD Fn.mat {}).m / Fn.len) :=
          Nat.mul_le_mul_right _ g2
  omega

/-- The same of every place that the record's tabAt names. -/
theorem k4_places_below {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    (tl : HTailF2) (hfun : tl.funs = o.funs)
    (hmat : ∀ μ, (tl.mats.getD μ {}).m = ((P.tails.getD g {}).mats.getD μ {}).m ∧
      (tl.mats.getD μ {}).k = ((P.tails.getD g {}).mats.getD μ {}).k)
    (hK : hp.nU.getD 2 0 ≤ o.v.K3) :
    ∀ (n : ℕ) (Fn : HFun), tl.funs[n]? = some Fn → ∀ c sg pos,
      tl.tabAt Fn c sg = some pos → pos < o.v.K3 := by
  intro n Fn hn c sg pos hp'
  obtain ⟨_, g2, g3, rfl⟩ := tabAt_some tl hp'
  exact k4_entries_below hh tl hfun hmat hK Fn
    (List.mem_iff_getElem?.mpr ⟨n, by rw [Array.getElem?_toList]; exact hn⟩) c g2 sg g3

section
variable {K J : Type} [Field K] [Fintype J] (ρ : Reading K)

/-- **The law of the reads at the layers' own tables**, from the relation in front of the draw. -/
theorem k4_readsAll_of_relIn {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    (Y : Lay J) (tl : HTailF2) (Fw : Fork) (X : Type) (Ex : ExtSpec) (W₀ : Type)
    (ride : X × Ex.Str → (JE Y tl → K) → Cb.Pv.Tail.Dig K (Tie.Pv.Tail.sizeOf tl).size × W₀ → Prop)
    {x : X} (m : J → K) (hfun : tl.funs = o.funs)
    (hmat : ∀ μ, (tl.mats.getD μ {}).m = ((P.tails.getD g {}).mats.getD μ {}).m ∧
      (tl.mats.getD μ {}).k = ((P.tails.getD g {}).mats.getD μ {}).k)
    (hK : hp.nU.getD 2 0 ≤ o.v.K3)
    (heU : ∀ r c, early tl (.cell o.v.iU3 r c) = true)
    (heS : ∀ μ i' c, μ < tl.NM → early tl (.cell (tl.gtTree.getD μ 0) i' c) = true)
    (hR : RowsBelow Y Fw o.v.iU3) (hU : UnitRow Fw o.v.iU3)
    (hNM : ∀ f ∈ tl.funs.toList, f.tree = 2 → f.mat < tl.NM)
    (h : relIn (thetaAt ρ Y tl o.v.iU3 o.v.K3 X Ex W₀ ride).letters x (earlyOf Y tl m)) :
    ∃ a : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k → ∀ i, i < (tl.mats.getD μ {}).m →
        |a μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) ∧
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
          Y.cellAt m (tl.gtTree.getD μ 0) i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => a μ i c) i' : ℤ) :
              K)) ∧
      ReadsAll ρ (P.tails.getD g {}).mats o.funs (portWorld ρ Y Fw m).entry o.v.iU3 o.v.K3
        (fun μ r c => ((a μ r c : ℤ) : K)) := by
  obtain ⟨a, h1, h2, h3⟩ := readsAll_at ρ Y tl Fw o.v.iU3 o.v.K3 X Ex W₀ ride m heU heS hR hU
    (k4_places_below hh tl hfun hmat hK) hNM h
  refine ⟨a, h1, h2, ?_⟩
  rw [hfun] at h3
  exact readsAll_sizes ρ hmat h3

/-- **The three clauses on the planes at the layers' forms, in the world of the committed entries,
from the relation in front of the draw.** -/
theorem k4_host_planes_of_relIn {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P.tails = tailsOf P.y) (hg : g < P.y.NGr)
    (zb0 zb1 : List K) (hz0 : rdL ρ o.H.fo.zb0 = zb0) (hz1 : rdL ρ o.H.fo.zb1 = zb1)
    (Y : Lay J) (tl : HTailF2) (Fw : Fork) (X : Type) (Ex : ExtSpec) (W₀ : Type)
    (ride : X × Ex.Str → (JE Y tl → K) → Cb.Pv.Tail.Dig K (Tie.Pv.Tail.sizeOf tl).size × W₀ → Prop)
    {x : X} (m : J → K) (hfun : tl.funs = o.funs)
    (hmat : ∀ μ, (tl.mats.getD μ {}).m = ((P.tails.getD g {}).mats.getD μ {}).m ∧
      (tl.mats.getD μ {}).k = ((P.tails.getD g {}).mats.getD μ {}).k)
    (hK : hp.nU.getD 2 0 ≤ o.v.K3)
    (heU : ∀ r c, early tl (.cell o.v.iU3 r c) = true)
    (heS : ∀ μ i' c, μ < tl.NM → early tl (.cell (tl.gtTree.getD μ 0) i' c) = true)
    (hR : RowsBelow Y Fw o.v.iU3) (hU : UnitRow Fw o.v.iU3)
    (hNM : ∀ f ∈ tl.funs.toList, f.tree = 2 → f.mat < tl.NM)
    (h : relIn (thetaAt ρ Y tl o.v.iU3 o.v.K3 X Ex W₀ ride).letters x (earlyOf Y tl m)) :
    ∃ a : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k → ∀ i, i < (tl.mats.getD μ {}).m →
        |a μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) ∧
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
          Y.cellAt m (tl.gtTree.getD μ 0) i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => a μ i c) i' : ℤ) :
              K)) ∧
      ∀ ν : _root_.Fo.Pl → K,
        (∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
          ((a (matIx o.v.y).iB r c : ℤ) : K) = ν (.cell r c)) →
        ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
          o.v.tabAt "b-pin" = some tP ∧
          K3HostPlanes o.H.fo.shape o.v.y.h.lmb zb0 zb1 ν
            (fun f => f.value ρ (portWorld ρ Y Fw m)) (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  obtain ⟨a, h1, h2, h3⟩ := k4_readsAll_of_relIn ρ hh Y tl Fw X Ex W₀ ride m hfun hmat hK heU heS
    hR hU hNM h
  exact ⟨a, h1, h2, fun ν h4 =>
    k4_host_planes_at ρ hh hq hT hg zb0 zb1 hz0 hz1 (fun μ r c => ((a μ r c : ℤ) : K)) ν h4
      (portWorld ρ Y Fw m) h3⟩

end

/-- **The same where the smallness test's letters are read off the arrays' entries A** (the
library's AtA): in every world whose entries of virtual rows are A. hix: the record keeps the plan's
number of the array of the reads. -/
theorem k4_host_planes_of_atA {K : Type} [CommRing K] (ρ : Reading K) {P : Pub} {hp : HPlan2}
    {g : ℕ} {fo : Forest.Heard} {F F' : Fork} {t t' : Tape} {o : Own}
    (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P.tails = tailsOf P.y) (hg : g < P.y.NGr)
    (zb0 zb1 : List K) (hz0 : rdL ρ o.H.fo.zb0 = zb0) (hz1 : rdL ρ o.H.fo.zb1 = zb1)
    (tl : HTailF2) (Θ : TLetters K (Tie.Pv.Tail.sizeOf tl)) {x : Θ.X} {msg : Θ.M}
    {Z : Cb.Pv.Tail.Dig K (Tie.Pv.Tail.sizeOf tl).size} {β : Dr (Tie.Pv.Tail.sizeOf tl).size}
    {A : ℕ → ℕ → ℕ → K} (at' : Port.AtA ρ tl Θ x msg Z β A) (h : relIn Θ.letters x msg)
    (hfun : tl.funs = o.funs) (hix : tl.ix.U.getD 2 none = hp.tl.ix.U.getD 2 none)
    (hmat : ∀ μ, (tl.mats.getD μ {}).m = ((P.tails.getD g {}).mats.getD μ {}).m ∧
      (tl.mats.getD μ {}).k = ((P.tails.getD g {}).mats.getD μ {}).k)
    (hK : hp.nU.getD 2 0 ≤ o.v.K3)
    (hNM : ∀ f ∈ tl.funs.toList, f.tree = 2 → f.mat < tl.NM) :
    ∃ a : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k → ∀ i, i < (tl.mats.getD μ {}).m →
        |a μ c i| < 2 * ((2 ^ lbz : ℕ) : ℤ)) ∧
      (∀ μ, μ < tl.NM → ∀ c, c < (tl.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl.mats.getD μ {}).m →
          A (tl.gtTree.getD μ 0) i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => a μ c i) i' : ℤ) :
              K)) ∧
      ∀ (ν : _root_.Fo.Pl → K) (W : World K), W.entry = A →
        (∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
          ((a (matIx o.v.y).iB c r : ℤ) : K) = ν (.cell r c)) →
        ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
          o.v.tabAt "b-pin" = some tP ∧
          K3HostPlanes o.H.fo.shape o.v.y.h.lmb zb0 zb1 ν (fun f => f.value ρ W)
            (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  obtain ⟨a, h1, h2, h3⟩ := readsAll_of_atA ρ tl Θ at' h o.v.K3
    (fun f hf _ => k4_entries_below hh tl hfun hmat hK f hf) hNM
  have eU : Port.u3Of tl = o.v.iU3 := by
    unfold Port.u3Of
    rw [hix, (hear_iU3 hh).1]
    rfl
  rw [eU, hfun] at h3
  refine ⟨a, h1, h2, fun ν W hW h4 => ?_⟩
  subst hW
  exact k4_host_planes_at ρ hh hq hT hg zb0 zb1 hz0 hz1 (fun μ r c => ((a μ c r : ℤ) : K)) ν h4 W
    (readsAll_sizes ρ hmat h3)

/-- **The three clauses at the layers' forms, at THE cells behind the committed symbols**, in the
library's field, from the relation in front of the draw at any letters Θ over the record's sizes.
The record tl gives sizes alone: hsh: its tables have the matrices, lengths and first entries of the
hearing's; the hearing's weights, which hang on what was drawn, stand in o.funs alone. hphi: the
letters' weights are the hearing's tables'. hu: the letters' committed reads are the world's
entries, read as the layers' forms read them. h4: ν takes the cells of the planes' matrix to `cellN`
(the library's `cellValS` of the committed symbols). -/
theorem k4_host_planes_cells (ρ : Reading Cb.Gl.E) {P : Pub} {hp : HPlan2}
    {g : ℕ} {fo : Forest.Heard} {F F' : Fork} {t t' : Tape} {o : Own}
    (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P.tails = tailsOf P.y) (hg : g < P.y.NGr)
    (zb0 zb1 : List Cb.Gl.E) (hz0 : rdL ρ o.H.fo.zb0 = zb0) (hz1 : rdL ρ o.H.fo.zb1 = zb1)
    (tl : HTailF2) (Θ : TLetters Cb.Gl.E (Tie.Pv.Tail.sizeOf tl)) {x : Θ.X} {msg : Θ.M}
    (h : relIn Θ.letters x msg)
    (hsh : (Tie.Pv.Tail.sizeOf tl).tabs =
      o.funs.toList.map fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab))
    (hmat : ∀ μ, (tl.mats.getD μ {}).m = ((P.tails.getD g {}).mats.getD μ {}).m ∧
      (tl.mats.getD μ {}).k = ((P.tails.getD g {}).mats.getD μ {}).k)
    (hNM : ∀ f ∈ o.funs.toList, f.tree = 2 → f.mat < tl.NM)
    (hphi : ∀ n Fn, o.funs.toList[n]? = some Fn → ∀ j, j < Fn.len →
      Θ.phi x n j = ρ.val (Fn.phi.getD j zeroE))
    (W : World Cb.Gl.E)
    (hu : ∀ f ∈ o.funs.toList, f.tree = 2 → ∀ c < (tl.mats.getD f.mat {}).k,
      ∀ sg < (tl.mats.getD f.mat {}).m / f.len,
        Θ.u3 msg (f.start + c * ((tl.mats.getD f.mat {}).m / f.len) + sg) =
          u3Val W.entry o.v.iU3 o.v.K3 (f.start + c * ((tl.mats.getD f.mat {}).m / f.len) + sg))
    (ν : _root_.Fo.Pl → Cb.Gl.E)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      cellN tl Θ msg (matIx o.v.y).iB r c = ν (.cell r c)) :
    ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
      o.v.tabAt "b-pin" = some tP ∧
      K3HostPlanes o.H.fo.shape o.v.y.h.lmb zb0 zb1 ν (fun f => f.value ρ W)
        (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  have h3 := readsAll_cells ρ tl Θ h o.funs hsh W.entry o.v.iU3 o.v.K3 hphi hu hNM
  exact k4_host_planes_at ρ hh hq hT hg zb0 zb1 hz0 hz1 (cellN tl Θ msg) ν h4 W
    (readsAll_sizes ρ hmat h3)

/-- The same where the letters are read off the arrays' entries A (the library's AtA, of which the
fields phi and u3 are spent), in every world whose entries of virtual rows are A. hix: the record
keeps the plan's number of the array of the reads. hK: the plan's number of reads is at most K3. -/
theorem k4_host_planes_cells_atA (ρ : Reading Cb.Gl.E) {P : Pub} {hp : HPlan2}
    {g : ℕ} {fo : Forest.Heard} {F F' : Fork} {t t' : Tape} {o : Own}
    (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    {pp : Aff × List Aff} (hq : Desc.First.K4.planesParts o.v o.H.fo = some pp)
    (hT : P.tails = tailsOf P.y) (hg : g < P.y.NGr)
    (zb0 zb1 : List Cb.Gl.E) (hz0 : rdL ρ o.H.fo.zb0 = zb0) (hz1 : rdL ρ o.H.fo.zb1 = zb1)
    (tl : HTailF2) (Θ : TLetters Cb.Gl.E (Tie.Pv.Tail.sizeOf tl)) {x : Θ.X} {msg : Θ.M}
    {Z : Cb.Pv.Tail.Dig Cb.Gl.E (Tie.Pv.Tail.sizeOf tl).size}
    {β : Dr (Tie.Pv.Tail.sizeOf tl).size} {A : ℕ → ℕ → ℕ → Cb.Gl.E}
    (at' : Port.AtA ρ tl Θ x msg Z β A) (h : relIn Θ.letters x msg)
    (hfun : tl.funs = o.funs) (hix : tl.ix.U.getD 2 none = hp.tl.ix.U.getD 2 none)
    (hmat : ∀ μ, (tl.mats.getD μ {}).m = ((P.tails.getD g {}).mats.getD μ {}).m ∧
      (tl.mats.getD μ {}).k = ((P.tails.getD g {}).mats.getD μ {}).k)
    (hK : hp.nU.getD 2 0 ≤ o.v.K3)
    (hNM : ∀ f ∈ tl.funs.toList, f.tree = 2 → f.mat < tl.NM)
    (ν : _root_.Fo.Pl → Cb.Gl.E) (W : World Cb.Gl.E) (hW : W.entry = A)
    (h4 : ∀ r < 2 ^ o.v.y.h.lmb, ∀ c < planeCols o.H.fo.shape o.v.y.h.lmb,
      cellN tl Θ msg (matIx o.v.y).iB r c = ν (.cell r c)) :
    ∃ tB0 tB1 tP, o.v.tabAt "b-bits-0" = some tB0 ∧ o.v.tabAt "b-bits-1" = some tB1 ∧
      o.v.tabAt "b-pin" = some tP ∧
      K3HostPlanes o.H.fo.shape o.v.y.h.lmb zb0 zb1 ν (fun f => f.value ρ W)
        (k4Bit o.v tB0 tB1) (k4Pin o.v tP) := by
  have eU : Port.u3Of tl = o.v.iU3 := by
    unfold Port.u3Of
    rw [hix, (hear_iU3 hh).1]
    rfl
  have hu := atA_reads at' o.v.K3 (fun f hf _ => k4_entries_below hh tl hfun hmat hK f hf) hNM
  rw [eU, ← hW] at hu
  rw [hfun] at hu hNM
  have hphi := at'.phi
  rw [hfun] at hphi
  exact k4_host_planes_cells ρ hh hq hT hg zb0 zb1 hz0 hz1 tl Θ h
    (by rw [← hfun]; rfl) hmat hNM hphi W hu ν h4

/-- The hearing's tables do not overlap at any list of matrices with the sizes of the group's. -/
theorem k4_apart_at {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F F' : Fork}
    {t t' : Tape} {o : Own} (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t'))
    (tl : HTailF2)
    (hmat : ∀ μ, (tl.mats.getD μ {}).m = ((P.tails.getD g {}).mats.getD μ {}).m ∧
      (tl.mats.getD μ {}).k = ((P.tails.getD g {}).mats.getD μ {}).k) :
    ∀ f ∈ o.funs.toList, ∀ f' ∈ o.funs.toList, ∀ col < entriesOf tl.mats f,
      ∀ col' < entriesOf tl.mats f', f.start + col = f'.start + col' → f = f' := by
  have e : ∀ f, entriesOf tl.mats f = entriesOf (P.tails.getD g {}).mats f := by
    intro f
    unfold entriesOf stretches
    rw [(hmat f.mat).1, (hmat f.mat).2]
  intro f hf f' hf' col hc col' hc'
  rw [e] at hc hc'
  exact (k4_tables_apart hh).2 f hf f' hf' col hc col' hc'

/-- **The premises of `k4_host_planes_cells` on the letters and the world hold together, at every
record with the shapes of the hearing's tables and the sizes of the group's matrices**, whatever
small integers stand in the matrices' cells. -/
theorem k4_member {K : Type} [CommRing K] (ρ : Reading K) {P : Pub} {hp : HPlan2} {g : ℕ}
    {fo : Forest.Heard} {F F' : Fork} {t t' : Tape} {o : Own}
    (hh : Desc.First.K4.hearFl P hp g fo F t = some (o, F', t')) (tl : HTailF2)
    (hsh : (Tie.Pv.Tail.sizeOf tl).tabs =
      o.funs.toList.map fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab))
    (hmat : ∀ μ, (tl.mats.getD μ {}).m = ((P.tails.getD g {}).mats.getD μ {}).m ∧
      (tl.mats.getD μ {}).k = ((P.tails.getD g {}).mats.getD μ {}).k)
    (a : ℕ → ℕ → ℕ → ℤ) (small : ∀ μ c i, |a μ c i| < 2 * ((2 ^ lbz : ℕ) : ℤ)) :
    ∃ (Θ : TLetters K (Tie.Pv.Tail.sizeOf tl)) (x : Θ.X) (msg : Θ.M) (W : World K),
      relIn Θ.letters x msg ∧
      (∀ n Fn, o.funs.toList[n]? = some Fn → ∀ j, j < Fn.len →
        Θ.phi x n j = ρ.val (Fn.phi.getD j zeroE)) ∧
      (∀ pos, Θ.u3 msg pos = u3Val W.entry o.v.iU3 o.v.K3 pos) ∧
      ∀ μ i' c, Θ.sym msg μ i' c =
        ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl.mats.getD μ {}).m => a μ c i) i' : ℤ) :
          K) := by
  obtain ⟨h1, h2, entry, h3⟩ := reads_member ρ tl o.funs hsh a small (k4_apart_at hh tl hmat)
    o.v.iU3 o.v.K3
  exact ⟨madeLetters ρ tl o.funs a, (), (), ⟨fun _ => 0, entry⟩, h1, h2, h3, fun _ _ _ => rfl⟩

/-- Such a record there is: the hearing's tables without their weights, the group's list of
matrices, a number of matrices above every table's. -/
theorem k4_record {P : Pub} {g : ℕ} {o : Own} :
    ∃ tl : HTailF2,
      (Tie.Pv.Tail.sizeOf tl).tabs =
        o.funs.toList.map (fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)) ∧
      (∀ μ, (tl.mats.getD μ {}).m = ((P.tails.getD g {}).mats.getD μ {}).m ∧
        (tl.mats.getD μ {}).k = ((P.tails.getD g {}).mats.getD μ {}).k) ∧
      (∀ f ∈ o.funs.toList, f.tree = 2 → f.mat < tl.NM) ∧
      ∀ f ∈ tl.funs.toList, f.phi = #[] := by
  obtain ⟨N, hN⟩ := mats_bound o.funs.toList
  refine ⟨{ funs := o.funs.map fun f => { f with phi := #[] },
            mats := (P.tails.getD g {}).mats, NM := N }, ?_, fun _ => ⟨rfl, rfl⟩,
    fun f hf _ => hN f hf, fun f hf => ?_⟩
  · show ((o.funs.map fun f => { f with phi := #[] }).toList.map
      fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)) = _
    rw [Array.toList_map, List.map_map]
    rfl
  · have hf' : f ∈ (o.funs.map fun f => { f with phi := #[] }).toList := hf
    rw [Array.toList_map] at hf'
    obtain ⟨f0, _, rfl⟩ := List.mem_map.mp hf'
    rfl

#print axioms hear_shapes
#print axioms tails_iB_lt
#print axioms k4_apart_at
#print axioms k4_record
#print axioms k4_member
#print axioms k4_host_planes_cells
#print axioms k4_host_planes_cells_atA
#print axioms hear_iU3
#print axioms k4_entries_below
#print axioms k4_host_planes_of_atA
#print axioms k4_places_below
#print axioms k4_readsAll_of_relIn
#print axioms k4_host_planes_of_relIn

end Meaning.Reads
