-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Tabs.lean: at an attention segment the list of tables that the verifier
makes and closes has the shapes that the smallness test's place expects.

The block of the smallness test's draw holds the closed list of tables (of each table its matrix,
the rows to an entry and its first entry) against `K8.tabs par`
(Johnson/Desc/First/K8/Hear.lean): the shapes that the place's families of tables make at the
place's rows and columns. At an attention segment the families are `K8.Asks.attention S`
(Johnson/Desc/First/K8/Asks.lean), and the list is made by `tablesP`
(Johnson/Desc/First/Att/TablesP.lean) inside the quiet step `readsAtSO`
(Johnson/Desc/First/Att/ReadsO.lean). Here the two are tied.

Main names (those of the first four entries in the namespace H2K5.Honest.Tabs):
  `entriesAt par M len`: how many entries the place gives a table of matrix M with len rows to an
    entry. `layAt`, `endAt`: tables, each given by its matrix and its rows to an entry, laid one
    behind the other. `spread`: a list of families as the list of its tables.
  `tabs_spread`: `K8.tabs par` is `layAt` of the spread families, from entry 0 on.
  `units_are`: the number of units that `K8.Asks.attention` counts is the library's `nScores S`.
  `spread_attention`: the spread families of an attention segment are the library's list
    `attAsks S (nScores S)` (OnBytes/Tie/Pv/Tail/ShapesAtt.lean) without the numbers of entries.
  `tabs_attShapes`: two public terms: `K8.tabs par` is the library's `attShapes S (nScores S)`.
    Conditional: the families are the segment's, and each table's written number of entries is
    the place's. Nothing here pays the second premise but a return of `tablesP` (`fits_entries`):
    the lemma is a stepping stone to the next.
  `tabs_attention`: where `tablesP` returns t, the shapes of `t.funs` are `K8.tabs par`.
    Conditional: the families are the segment's; the place's columns and rows are those of the
    list of matrices that `tablesP` was given; the points have as many units of the scores as the
    shape has.
  `tabs_attention_pts`: the last premise paid where the points come from `pointsOf`.
  `tabs_reads`: behind a yes of the quiet step the closed list that the state bears has the shapes
    `K8.tabs par`. Conditional: the families are the plan's shape's; the place's columns and rows
    are those of the plan's list of matrices.

WHO PAYS `tabs_reads`' PREMISES AT THE VERIFIER'S OWN PLACE (`ProofFile.k8Par`,
Johnson/Desc/ProofFile/Lot/K8.lean):
  ha, hk, hm: Johnson/Desc/K5/Honest/Law/TabsAt.lean pays the three: at any link of the attention
    sort whose group has the plan and whose smallness test's numbers are the plan's
    (`k8Par_attention`), and so at each attention link in the library's scope
    (`tabs_reads_scope`). For hk alone the library has `IM.k8_of_attention`
    (Johnson/IMR/K8Seat.lean).
  That the list of matrices in the STATE's part of the smallness test is the plan's: not a premise
    here, but whoever holds the place's numbers against the state's list needs it; no lemma is
    known by name.

Limits. Shapes alone: nothing on the tables' weights. `tabs_reads` speaks of the state just behind
the quiet step: that later blocks leave the list is not said here. The quiet step takes the rows
and columns from the plan's list of matrices and not from the state's: that the two lists agree is
not said here. Where `tablesP` or the step refuses nothing is said.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.K8.LawShapes
import Johnson.Desc.First.Att.Door.Law.K5FunsSkel
import Johnson.Desc.First.Att.Claims.ReadsApart
import Johnson.Desc.K5.Honest.Law.ReadsStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S K8.Par K8.tabs K8.layFamily K8.layFamily_eq K8.goFam
  K8.ofTab K8.Asks.attention)
open VerifiableInference.Desc.First.Att
open OnBytes.Tie.Pv.Tail.Closed (attShapes attAsks asPart nScores place rep)

namespace Tabs

/-! ## Tables laid one behind the other -/

/-- How many entries the place gives a table of matrix M with len rows to an entry: one for each
column and each run of len rows. -/
def entriesAt (par : K8.Par) (M len : ℕ) : ℕ := par.ks.getD M 0 * (par.ms.getD M 0 / len)

/-- Tables, each given by its matrix and its rows to an entry, laid from entry e on; w: a table's
number of entries. Of each: its matrix, its rows to an entry, its first entry. -/
def layAt (w : ℕ → ℕ → ℕ) : List (ℕ × ℕ) → ℕ → List (ℕ × ℕ × ℕ)
  | [], _ => []
  | a :: l, e => (a.1, a.2, e) :: layAt w l (e + w a.1 a.2)

/-- The first entry behind them. -/
def endAt (w : ℕ → ℕ → ℕ) : List (ℕ × ℕ) → ℕ → ℕ
  | [], e => e
  | a :: l, e => endAt w l (e + w a.1 a.2)

/-- A list of families (first matrix, number of matrices in a row, rows to an entry) as the list of
its tables. -/
def spread (asks : List (ℕ × ℕ × ℕ)) : List (ℕ × ℕ) :=
  asks.flatMap fun a => (List.range' a.1 a.2.1).map fun M => (M, a.2.2)

theorem layAt_append (w : ℕ → ℕ → ℕ) : ∀ (l l' : List (ℕ × ℕ)) (e : ℕ),
    layAt w (l ++ l') e = layAt w l e ++ layAt w l' (endAt w l e)
  | [], _, _ => rfl
  | a :: l, l', e => by
    show _ :: layAt w (l ++ l') _ = _ :: (layAt w l _ ++ _)
    rw [layAt_append w l l']
    rfl

theorem endAt_append (w : ℕ → ℕ → ℕ) : ∀ (l l' : List (ℕ × ℕ)) (e : ℕ),
    endAt w (l ++ l') e = endAt w l' (endAt w l e)
  | [], _, _ => rfl
  | a :: l, l', e => endAt_append w l l' (e + w a.1 a.2)

theorem spread_nil : spread [] = [] := rfl

theorem spread_cons (a : ℕ × ℕ × ℕ) (l : List (ℕ × ℕ × ℕ)) :
    spread (a :: l) = ((List.range' a.1 a.2.1).map fun M => (M, a.2.2)) ++ spread l :=
  List.flatMap_cons

theorem spread_append (l l' : List (ℕ × ℕ × ℕ)) : spread (l ++ l') = spread l ++ spread l' :=
  List.flatMap_append

/-- One family, by the plain recursion that the smallness test's laws use. -/
theorem goFam_lay (w : ℕ → ℕ → ℕ) (L : ℕ) : ∀ (n M e : ℕ),
    (K8.goFam (fun M => w M L) n M e).1.map (fun y => (y.1, L, y.2)) =
        layAt w ((List.range' M n).map fun M => (M, L)) e ∧
      (K8.goFam (fun M => w M L) n M e).2 = endAt w ((List.range' M n).map fun M => (M, L)) e
  | 0, _, _ => ⟨rfl, rfl⟩
  | n + 1, M, e => by
    obtain ⟨h1, h2⟩ := goFam_lay w L n (M + 1) (e + w M L)
    refine ⟨?_, ?_⟩
    · show (M, L, e) :: (K8.goFam (fun M => w M L) n (M + 1) (e + w M L)).1.map _ = _
      rw [h1, List.range'_succ]
      rfl
    · show (K8.goFam (fun M => w M L) n (M + 1) (e + w M L)).2 = _
      rw [h2, List.range'_succ]
      rfl

/-- The place's fold over its families. -/
theorem fold_spread (par : K8.Par) : ∀ (asks : List (ℕ × ℕ × ℕ)) (pre : List (ℕ × ℕ × ℕ)) (e : ℕ),
    asks.foldl (fun x a => let y := K8.layFamily par a x.2; (x.1 ++ y.1, y.2)) (pre, e) =
      (pre ++ layAt (entriesAt par) (spread asks) e, endAt (entriesAt par) (spread asks) e)
  | [], pre, e => by
    show (pre, e) = (pre ++ [], e)
    rw [List.append_nil]
  | a :: asks, pre, e => by
    obtain ⟨h1, h2⟩ := goFam_lay (entriesAt par) a.2.2 a.2.1 a.1 e
    have f1 : (K8.layFamily par a e).1 =
        layAt (entriesAt par) ((List.range' a.1 a.2.1).map fun M => (M, a.2.2)) e := by
      rw [K8.layFamily_eq]
      exact h1
    have f2 : (K8.layFamily par a e).2 =
        endAt (entriesAt par) ((List.range' a.1 a.2.1).map fun M => (M, a.2.2)) e := by
      rw [K8.layFamily_eq]
      exact h2
    rw [List.foldl_cons]
    show asks.foldl _ (pre ++ (K8.layFamily par a e).1, (K8.layFamily par a e).2) = _
    rw [fold_spread par asks, f1, f2, spread_cons, layAt_append, endAt_append, List.append_assoc]

/-- **The place's shapes are its spread families, laid from entry 0 on.** No premise. -/
theorem tabs_spread (par : K8.Par) :
    K8.tabs par = layAt (entriesAt par) (spread par.asks) 0 := by
  unfold K8.tabs
  rw [fold_spread]
  rfl

/-- The library's placing of tables that are given with their numbers of entries, where these
numbers are w's. -/
theorem place_lay (w : ℕ → ℕ → ℕ) : ∀ (A : List (ℕ × ℕ × ℕ)) (m : ℕ),
    (∀ a ∈ A, a.2.2 = w a.1 a.2.1) →
      (place A m).map K8.ofTab = layAt w (A.map fun a => (a.1, a.2.1)) m
  | [], _, _ => rfl
  | a :: A, m, h => by
    show (a.1, a.2.1, m) :: (place A (m + a.2.2)).map K8.ofTab =
      (a.1, a.2.1, m) :: layAt w (A.map fun a => (a.1, a.2.1)) (m + w a.1 a.2.1)
    rw [place_lay w A _ fun b hb => h b (List.mem_cons_of_mem _ hb), h a List.mem_cons_self]

/-! ## The families of an attention segment -/

/-- The two counts of the units of the scores, side by side. -/
theorem units_aux : ∀ (l : List Attention.ACall) (k a : ℕ),
    (l.filter fun c => c.kind == Attention.Table.kfd).foldl
        (fun a c => a +
          ([Attention.Seg.fm, Attention.Seg.fd].filter fun s => c.segs.contains s).length) a =
      a + ((l.zipIdx k).flatMap fun x =>
        if x.1.kind == Attention.Table.kfd then
          ([Attention.Seg.fm, Attention.Seg.fd].filter fun s => x.1.holds s).map
            fun s => (x.2, x.1, s)
        else []).length
  | [], _, _ => rfl
  | c :: l, k, a => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.length_append]
    by_cases hc : (c.kind == Attention.Table.kfd) = true
    · rw [List.filter_cons_of_pos (p := fun c : Attention.ACall => c.kind == Attention.Table.kfd)
          (a := c) (l := l) hc, List.foldl_cons, units_aux l (k + 1), if_pos hc, List.length_map,
        Nat.add_assoc]
      rfl
    · rw [List.filter_cons_of_neg (p := fun c : Attention.ACall => c.kind == Attention.Table.kfd)
          (a := c) (l := l) hc, units_aux l (k + 1), if_neg hc]
      simp

/-- **The number of units that the place's families count is the library's.** -/
theorem units_are (Sh : Attention.Shape) :
    (Sh.calls.toList.filter fun c => c.kind == Attention.Table.kfd).foldl
        (fun a c => a +
          ([Attention.Seg.fm, Attention.Seg.fd].filter fun s => c.segs.contains s).length) 0 =
      nScores Sh := by
  rw [units_aux Sh.calls.toList 0 0, Nat.zero_add]
  rfl

theorem rep_one {β : Type} (f : ℕ × ℕ × ℕ → β) (a : ℕ × ℕ × ℕ) : ∀ k : ℕ,
    (rep k [a]).map f = List.replicate k (f a)
  | 0 => rfl
  | k + 1 => by
    show f a :: (rep k [a]).map f = _
    rw [rep_one f a k]
    rfl

theorem rep_two {β : Type} (f : ℕ × ℕ × ℕ → β) (a : ℕ × ℕ × ℕ) : ∀ k : ℕ,
    (rep k ([a] ++ [a])).map f = List.replicate (2 * k) (f a)
  | 0 => rfl
  | k + 1 => by
    show f a :: f a :: (rep k ([a] ++ [a])).map f = _
    rw [rep_two f a k]
    rfl

theorem spread_one (M L : ℕ) : ∀ k : ℕ,
    spread (List.replicate k (M, 1, L)) = List.replicate k (M, L)
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ, spread_cons, spread_one M L k]
    rfl

theorem asPart_map (Sh : Attention.Shape) :
    (asPart Sh).map (fun a => (a.1, a.2.1)) =
      (List.range' 0 Sh.cf.NAs).map fun M => (M, 2 ^ Sh.cf.lmS) := by
  unfold asPart
  rw [← List.range_eq_range', List.map_flatMap, List.map_eq_flatMap]
  rfl

/-- **The spread families of an attention segment are the library's list of its tables**, the
numbers of entries dropped. No premise. -/
theorem spread_attention (Sh : Attention.Shape) :
    spread (K8.Asks.attention Sh) = (attAsks Sh (nScores Sh)).map fun a => (a.1, a.2.1) := by
  unfold K8.Asks.attention attAsks
  dsimp only
  rw [units_are]
  generalize nScores Sh = n
  simp only [spread_append, spread_one, List.map_append, asPart_map, rep_one, rep_two,
    List.replicate_add, List.map_cons, List.map_nil]
  simp only [List.replicate_succ, List.replicate_zero, spread_cons, spread_nil, List.append_nil,
    List.append_assoc, List.cons_append, List.nil_append, List.range'_one, List.map_cons,
    List.map_nil]

/-- A list of numbers read off a list of matrices, at a number. -/
theorem getD_of_map (f : TMat → ℕ) (g : ℕ × ℕ → ℕ) (hg : g (0, 0) = 0)
    (hfg : ∀ X : TMat, g (X.m, X.k) = f X) (mats : Array TMat) (M : ℕ) :
    (mats.toList.map f).getD M 0 = g ((mats.map fun X => (X.m, X.k)).getD M (0, 0)) := by
  rw [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, List.getElem?_map,
    Array.getElem?_map, Array.getElem?_toList]
  cases mats[M]? with
  | none => exact hg.symm
  | some X => exact (hfg X).symm

end Tabs

open Tabs

/-- **Two public terms: the place's shapes at an attention segment are the library's.**
Conditional: ha: the place's families are the segment's (the plan's maker pays it); hf: each
table's written number of entries is one for each column and each run of rows of its matrix in the
place's lists (paid by `fits_entries` where `tablesP` returns; nothing else is known to pay it). -/
theorem tabs_attShapes (par : K8.Par) (Sh : Attention.Shape) (ha : par.asks = K8.Asks.attention Sh)
    (hf : ∀ a ∈ attAsks Sh (nScores Sh), a.2.2 = entriesAt par a.1 a.2.1) :
    K8.tabs par = (attShapes Sh (nScores Sh)).map K8.ofTab := by
  unfold attShapes
  rw [tabs_spread, ha, spread_attention, place_lay (entriesAt par) _ 0 hf]

/-! ## What the verifier's text makes -/

/-- Where `tablesP` returns, each table's written number of entries is the place's: by the test
that the placing asks at every table. Conditional on hk, hm: the place's columns and rows are
those of the list of matrices (rows, columns) that `tablesP` was given. -/
theorem fits_entries {Sh : Attention.Shape} {mats : Array (ℕ × ℕ)} {nW : ℕ} {lk : P.LookIn}
    {p : P.Pts} {t : P.TablesP} (par : K8.Par)
    (hk : ∀ M, par.ks.getD M 0 = (mats.getD M (0, 0)).2)
    (hm : ∀ M, par.ms.getD M 0 = (mats.getD M (0, 0)).1)
    (h : P.tablesP (P.geoOf Sh) mats nW lk p = some t) :
    ∀ a ∈ attAsks Sh p.scores.size, a.2.2 = entriesAt par a.1 a.2.1 := by
  intro a ha
  rw [← H2K5.Door.asks_laid Sh lk p] at ha
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  have hfit : P.fits mats x.mat x.len x.entries = true :=
    List.all_eq_true.1 (K5Law.tablesP_fits h) x hx
  unfold P.fits at hfit
  show x.entries = par.ks.getD x.mat 0 * (par.ms.getD x.mat 0 / x.len)
  rw [hk, hm, Array.getD_eq_getD_getElem?]
  cases hM : mats[x.mat]? with
  | none => rw [hM] at hfit; cases hfit
  | some M =>
    rw [hM] at hfit
    simp only [Bool.and_eq_true, beq_iff_eq] at hfit
    exact hfit.2

/-- **Where the verifier's text makes the tables, their shapes are the place's.** Conditional:
ha: the place's families are the segment's; hk, hm: the place's columns and rows are those of the
list of matrices (rows, columns) that `tablesP` was given (both the plan's maker's to pay); hn: the
points have as many units of the scores as the shape (paid by `tabs_attention_pts`); h: the
return. -/
theorem tabs_attention {Sh : Attention.Shape} {mats : Array (ℕ × ℕ)} {nW : ℕ} {lk : P.LookIn}
    {p : P.Pts} {t : P.TablesP} (par : K8.Par) (ha : par.asks = K8.Asks.attention Sh)
    (hk : ∀ M, par.ks.getD M 0 = (mats.getD M (0, 0)).2)
    (hm : ∀ M, par.ms.getD M 0 = (mats.getD M (0, 0)).1)
    (hn : p.scores.size = nScores Sh)
    (h : P.tablesP (P.geoOf Sh) mats nW lk p = some t) :
    t.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = K8.tabs par := by
  have hf := fits_entries par hk hm h
  rw [hn] at hf
  rw [tabs_attShapes par Sh ha hf]
  unfold attShapes
  rw [← hn, ← H2K5.Door.asks_laid Sh lk p, ← H2K5.Door.lay_place, K5Law.tablesP_laid h,
    List.map_map]
  rfl

/-- The same where the points are made of what was heard: the number of units is then the
shape's. -/
theorem tabs_attention_pts {Sh : Attention.Shape} {mats : Array (ℕ × ℕ)} {nW : ℕ} {lk : P.LookIn}
    {zk : Array (Array E)} {hh : P.Heard} {Lf : P.Left} {p : P.Pts} {t : P.TablesP} (par : K8.Par)
    (ha : par.asks = K8.Asks.attention Sh)
    (hk : ∀ M, par.ks.getD M 0 = (mats.getD M (0, 0)).2)
    (hm : ∀ M, par.ms.getD M 0 = (mats.getD M (0, 0)).1)
    (hp : P.pointsOf (P.geoOf Sh) zk hh Lf = some p)
    (h : P.tablesP (P.geoOf Sh) mats nW lk p = some t) :
    t.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = K8.tabs par :=
  tabs_attention par ha hk hm (H2K5.Door.units_plan hp) h

/-- **Behind a yes of the quiet step the closed list that the state bears has the place's
shapes**: the form in which the law of the smallness test's draw asks it. Conditional: ha: the
place's families are the plan's shape's; hk, hm: the place's columns and rows are those of the
plan's list of matrices; h: the step's yes. The three are facts on how the place's numbers are
made of the public parameters; Johnson/Desc/K5/Honest/Law/TabsAt.lean pays them at the verifier's
own place. -/
theorem tabs_reads (A : Attention.Plan) (par : K8.Par) (ha : par.asks = K8.Asks.attention A.S)
    (hk : par.ks = A.mats.toList.map (·.k)) (hm : par.ms = A.mats.toList.map (·.m))
    {s s' : S} (h : readsAtSO A s = .ok s') :
    ∀ tl, s'.tl? = some tl →
      tl.funs.toList.map (fun Fn => (Fn.mat, Fn.len, Fn.start)) = K8.tabs par := by
  obtain ⟨a, hh, g, p, t, _, _, _, _, hp, ht, _, _, rfl⟩ := (readsAtSO_iff A s s').1 h
  intro tl htl
  obtain rfl : ({ a.tl with funClosed := true, funs := (tabsBack t).funs } : HTailF2) = tl :=
    Option.some.inj htl
  unfold P.ptsFrom at hp
  obtain ⟨Lf, _, hp'⟩ := Option.bind_eq_some_iff.1 hp
  rw [← tabs_attention_pts (mats := (P.parCOf A).mats) par ha
    (fun M => by rw [hk]; exact getD_of_map (·.k) (·.2) rfl (fun _ => rfl) A.mats M)
    (fun M => by rw [hm]; exact getD_of_map (·.m) (·.1) rfl (fun _ => rfl) A.mats M) hp' ht]
  show ((t.funs.map funBack).toList.map fun Fn : HFun => (Fn.mat, Fn.len, Fn.start)) = _
  rw [Array.toList_map, List.map_map]
  rfl

end H2K5.Honest

#print axioms H2K5.Honest.Tabs.layAt_append
#print axioms H2K5.Honest.Tabs.endAt_append
#print axioms H2K5.Honest.Tabs.spread_nil
#print axioms H2K5.Honest.Tabs.spread_cons
#print axioms H2K5.Honest.Tabs.spread_append
#print axioms H2K5.Honest.Tabs.goFam_lay
#print axioms H2K5.Honest.Tabs.fold_spread
#print axioms H2K5.Honest.Tabs.tabs_spread
#print axioms H2K5.Honest.Tabs.place_lay
#print axioms H2K5.Honest.Tabs.units_aux
#print axioms H2K5.Honest.Tabs.units_are
#print axioms H2K5.Honest.Tabs.rep_one
#print axioms H2K5.Honest.Tabs.rep_two
#print axioms H2K5.Honest.Tabs.spread_one
#print axioms H2K5.Honest.Tabs.asPart_map
#print axioms H2K5.Honest.Tabs.spread_attention
#print axioms H2K5.Honest.Tabs.getD_of_map
#print axioms H2K5.Honest.tabs_attShapes
#print axioms H2K5.Honest.fits_entries
#print axioms H2K5.Honest.tabs_attention
#print axioms H2K5.Honest.tabs_attention_pts
#print axioms H2K5.Honest.tabs_reads
