-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysTrue2.lean: the tables of the reads at the end point of the second token
sumcheck are true of the cells that are read in the matrices' entries, if every table of the
verifier's list holds what it says of its matrix.

The theorems on the forms of the lookup's segments ask that six families of tables are true at the
lookup's point (TrueAt, Johnson/Road/FormsKeysFits.lean), and Johnson/Road/FormsKeysTrue.lean
concludes that from Holds (Johnson/Road/FormsKeysMat.lean). The forms of the panels that belong to
the second token sumcheck read tables at another point: the end point of that sumcheck. This file
states the like record for these families (TrueAt2) and concludes it from the same hypothesis, on
the same list of tables.

Which families, by the verifier's text. A matrix has a table at that end point, under the point's
name Y for a long table and rt for a short one, if some segment's readsR names the matrix's letter
(readsOf, OnBytes/Model/LayerLayout.lean). readsR returns the letters of af, of the stream that
comes in, of ad and of ar, and no other. So there are four families: af@Y, xbI@Y, ad@rt, ar@rt. No
layout has a table of the stream that goes out, or of qa, at that end point. That there is no fifth
family is read off the text of readsR; no theorem here says it.
The points (pointsOf, OnBytes/Model/Layer.lean): rt is the end point; Y is the first ls coordinates
of Z followed by the end point, where Z, as in TrueAt, is the last la coordinates of the lookup's
point.

What is compared with what: texts of the verifier with each other, as in
Johnson/Road/FormsKeysTab.lean: the numbering of a family's entries that the forms use with that of
the smallness test; and tableAsks, readsOf, pointsOf, phiOf and funsOf with the record's names and
points. cellsAt and Holds are definitions of Johnson/Road/FormsKeysMat.lean. The library is not
mentioned.

Main definitions: TrueAt2, Found2, anyR.
Main theorems: points2_of_layout, found2_of_layout (the four families are asked for and found);
four_numbers; pointsOf_names2; phiOf_inv; family_of_name; trueAt2_of_holds; trueAt2_met.
That the end point has lt coordinates is concluded, from phiOf's own test: it is not asked.

Which value is which. Z and the end point are public: challenges that the verifier has kept. The
entries of the reads are hidden values (World.entry). No value that was sent occurs.

The hypotheses of trueAt2_of_holds, and where they are met. Those of trueAt_of_holds but the line
that makes the token point: see there; htm and hNM are theorems on the verifier's own plans:
plan_sizes, Johnson/Road/FormsKeysPlan.lean. htT, that the second token sumcheck has been heard:
the runs of Johnson/Road/FormsKeysRun8.lean and Johnson/Road/FormsKeysRunK.lean, in which the
verifier's lines return together, are made with such a record (heardR8). The hypothesis on the
world: trueAt2_met has, for any matrices, one world that meets it, in which TrueAt and TrueAt2 hold
together.

What is not claimed. The verifier never tests Holds: see Johnson/Road/FormsKeysMat.lean. M is any
function; nothing ties it to a commitment. The families at the sub-proof's other points and the
three on the matrix of counts are not in the record; laid1_family and holds_met cover them. What the
panels' forms are worth is not looked at here. The program does not import this file.
-/
import Johnson.Road.FormsKeysMet

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff HFun HTailF2 Level Tsc lastOf eqTab longPhi longPoint)
open OnBytes.Model.Layer (Env Lay Shape Reads Heard TableAsk TableAt layout readsOf readsR layTables
  layParts tableAsks pointsOf phiOf funsOf)

/-! ## The record -/

/-- The entries of four more families of tables are true in the world W: the long tables of af and
of the stream that comes in at the point (low | u'), and the short tables of ad and ar at the point
u'. The names are those under which the verifier's forms read a matrix at the end point of the
second token sumcheck: Y for a long table, rt for a short one. -/
structure TrueAt2 {K : Type} [Field K] (ρ : Reading K) (W : World K) (v : Env) (lT : ℕ)
    (c : Cells K) (low u' : ℕ → K) : Prop where
  af : ∀ b, v.tabAt ("af" ++ "@" ++ "Y") = some b → LongTrue ρ W v b 0 v.y.ls lT c low u'
  xi : ∀ b, v.tabAt ("xbI" ++ "@" ++ "Y") = some b → LongTrue ρ W v b 4 v.y.ls lT c low u'
  ad : ∀ b, v.tabAt ("ad" ++ "@" ++ "rt") = some b → ShortTrue ρ W v b 1 lT c u'
  ar : ∀ b, v.tabAt ("ar" ++ "@" ++ "rt") = some b → ShortTrue ρ W v b 2 lT c u'

/-- These four families are found under their names. -/
structure Found2 (v : Env) : Prop where
  af : ∃ b, v.tabAt ("af" ++ "@" ++ "Y") = some b
  xi : ∃ b, v.tabAt ("xbI" ++ "@" ++ "Y") = some b
  ad : ∃ b, v.tabAt ("ad" ++ "@" ++ "rt") = some b
  ar : ∃ b, v.tabAt ("ar" ++ "@" ++ "rt") = some b

/-! ## Which matrices are read at the end point of the second token sumcheck -/

/-- True if a term of some segment of some call reads, at that end point, the matrix with the letter
ch (readsR in OnBytes/Model/LayerLayout.lean). -/
def anyR (y : Lay) (ch : Char) : Bool :=
  (y.calls.toList.map fun c => c.segs.flatMap fun s => readsR y.h.p3 s.name).any (·.contains ch)

/-- The lists of points that readsOf returns have that end point for each matrix that some segment's
term reads there. -/
theorem readsOf_points2 {y : Lay} {rd : Reads} (h : readsOf y = .ok rd) :
    (anyR y 'f' = true → "Y" ∈ rd.rdAF) ∧ (anyR y 'i' = true → "Y" ∈ rd.rdXI) ∧
    (anyR y 'd' = true → "rt" ∈ rd.rdAD) ∧ (anyR y 'r' = true → "rt" ∈ rd.rdAR) := by
  unfold readsOf at h
  have h2 := refuse_bind h
  have e := (Except.ok.inj h2).symm
  subst e
  have m : ∀ (ch : Char) (p : String), anyR y ch = true →
      p ∈ (if anyR y ch = true then [p] else []) := by
    intro ch p ha
    rw [if_pos ha]
    exact List.mem_singleton.mpr rfl
  refine ⟨fun ha => ?_, fun ha => ?_, fun ha => ?_, fun ha => ?_⟩
  · exact List.mem_append_left _ (List.mem_append_right _ (m 'f' "Y" ha))
  · exact List.mem_append_left _ (List.mem_append_right _ (m 'i' "Y" ha))
  · exact List.mem_append_right _ (m 'd' "rt" ha)
  · exact List.mem_append_right _ (m 'r' "rt" ha)

/-- A matrix is read at that end point if a segment is there whose term reads it. -/
theorem anyR_of_seg {y : Lay} {n : String} (hs : HasSeg y n) {ch : Char}
    (hch : ch ∈ readsR y.h.p3 n) : anyR y ch = true := by
  obtain ⟨c, hc, s, hs, rfl⟩ := hs
  have hm : ch ∈ c.segs.flatMap fun s => readsR y.h.p3 s.name :=
    List.mem_flatMap.mpr ⟨s, hs, hch⟩
  unfold anyR
  rw [List.any_eq_true]
  exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, by simpa using hm⟩

/-- With the segments N1 and QK in its calls, a layout has all four families. -/
theorem points2_of_segs {y : Lay} {rd : Reads} (h : readsOf y = .ok rd) (s1 : HasSeg y "N1")
    (s2 : HasSeg y "QK") :
    "Y" ∈ rd.rdAF ∧ "Y" ∈ rd.rdXI ∧ "rt" ∈ rd.rdAD ∧ "rt" ∈ rd.rdAR := by
  obtain ⟨p1, p2, p3, p4⟩ := readsOf_points2 h
  exact ⟨p1 (anyR_of_seg s1 (by simp [readsR])), p2 (anyR_of_seg s1 (by simp [readsR])),
    p3 (anyR_of_seg s2 (by simp [readsR])), p4 (anyR_of_seg s1 (by simp [readsR]))⟩

/-- The numbers of the four families: each is asked for under its name with the first part and the
number of parts of its matrix, with runs of 2^la rows (a long table) or T rows (a short one), and
with its point's name and its kind. -/
theorem four_numbers (y : Lay) (rd : Reads) (g : ℕ) (hAF : "Y" ∈ rd.rdAF) (hXI : "Y" ∈ rd.rdXI)
    (hAD : "rt" ∈ rd.rdAD) (hAR : "rt" ∈ rd.rdAR) :
    (∃ a ∈ tableAsks y rd g, a.name = "af" ++ "@" ++ "Y" ∧ a.M0 = firstM y 0 ∧
      a.parts = partsM y 0 ∧ a.L = 2 ^ y.h.la ∧ a.point = "Y" ∧ a.lng = true) ∧
    (∃ a ∈ tableAsks y rd g, a.name = "xbI" ++ "@" ++ "Y" ∧ a.M0 = firstM y 4 ∧
      a.parts = partsM y 4 ∧ a.L = 2 ^ y.h.la ∧ a.point = "Y" ∧ a.lng = true) ∧
    (∃ a ∈ tableAsks y rd g, a.name = "ad" ++ "@" ++ "rt" ∧ a.M0 = firstM y 1 ∧
      a.parts = partsM y 1 ∧ a.L = y.T ∧ a.point = "rt" ∧ a.lng = false) ∧
    (∃ a ∈ tableAsks y rd g, a.name = "ar" ++ "@" ++ "rt" ∧ a.M0 = firstM y 2 ∧
      a.parts = partsM y 2 ∧ a.L = y.T ∧ a.point = "rt" ∧ a.lng = false) := by
  have m : ∀ (f : String → TableAsk) (p : String) (l : List String), p ∈ l → f p ∈ l.map f :=
    fun f p l h => List.mem_map.mpr ⟨p, h, rfl⟩
  exact
   ⟨⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (m _ _ _ hAF)))))))),
      rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (m _ _ _ hXI))))))), rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (m _ _ _ hAD)))), rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨_, List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (m _ _ _ hAR))), rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- A name of the verifier's list of families is found. -/
theorem found_name {v : Env} {n : String} (h : n ∈ v.tab.map (·.name)) :
    ∃ b, v.tabAt n = some b := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  unfold Env.tabAt
  cases hf : v.tab.find? (fun t => t.name == x.name) with
  | none =>
    have h1 := List.find?_eq_none.mp hf x hx
    simp at h1
  | some t => exact ⟨t.first, rfl⟩

/-! ## The two points, and the weights at them -/

/-- In the verifier's list of points by name, Y is the first ls coordinates of Z followed by the end
point of the second token sumcheck, and rt is that end point. Z: the last la coordinates of the
lookup's point. -/
theorem pointsOf_names2 {y : Lay} {H : Heard} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)} (h : pointsOf y H hd hd2 = some pts) {tT : Tsc}
    (htT : H.tT = some tT) :
    ∃ Z, lastOf H.fo.zx y.h.la = .ok Z ∧
      pts.find? (fun p => p.1 == "Y") = some ("Y", longPoint (Z.extract 0 y.ls) tT.r) ∧
      pts.find? (fun p => p.1 == "rt") = some ("rt", tT.r) := by
  unfold pointsOf at h
  rw [htT] at h
  obtain ⟨Z, hZ, h⟩ := bind_some h
  cases hd2 with
  | none =>
    obtain ⟨routed, _, h⟩ := bind_some h
    obtain ⟨a, _, h⟩ := bind_some h
    obtain ⟨b, _, h⟩ := bind_some h
    have e := Option.some.inj h
    subst e
    exact ⟨Z, ok_of_toOption hZ, by simp, by simp⟩
  | some o =>
    obtain ⟨routed, _, h⟩ := bind_some h
    obtain ⟨a, _, h⟩ := bind_some h
    obtain ⟨b, _, h⟩ := bind_some h
    have e := Option.some.inj h
    subst e
    exact ⟨Z, ok_of_toOption hZ, by simp, by simp⟩

/-- What phiOf has tested and returned, for a family that is not on the matrix of counts and whose
point is found: the point has la coordinates for a long table and lt for a short one, and the
weights are those of a long table at the point, or its equality weights. -/
theorem phiOf_inv {y : Lay} {fo : Model.Forest.Heard} {pts : List (String × Array E)}
    {a : TableAsk} {phi : Array E} (h : phiOf y fo pts a = some phi)
    (h0 : (a.name == "b-bits-0") = false) (h1 : (a.name == "b-bits-1") = false)
    (h2 : (a.name == "b-pin") = false) {P : String} {Y : Array E} (hp : a.point = P)
    (hf : pts.find? (fun p => p.1 == P) = some (P, Y)) :
    Y.size = (if a.lng then y.h.la else y.h.lt) ∧
      phi = if a.lng then longPhi Y y.ls y.h.lt else eqTab Y := by
  unfold phiOf at h
  rw [h0, h1, h2, hp, hf] at h
  have h' : (if (Y.size != (if a.lng then y.h.la else y.h.lt)) = true then none
      else some (if a.lng then longPhi Y y.ls y.h.lt else eqTab Y)) = some phi := h
  by_cases hs : (Y.size != (if a.lng then y.h.la else y.h.lt)) = true
  · rw [if_pos hs] at h'
    cases h'
  · rw [if_neg hs] at h'
    exact ⟨by simpa using hs, (Option.some.inj h').symm⟩

/-- None of the four names is a name of a table on the matrix of counts. -/
theorem four_not_b : ∀ n ∈ ["af" ++ "@" ++ "Y", "xbI" ++ "@" ++ "Y", "ad" ++ "@" ++ "rt",
    "ar" ++ "@" ++ "rt"],
    (n == "b-bits-0") = false ∧ (n == "b-bits-1") = false ∧ (n == "b-pin") = false := by
  simp

/-- A family that is found under a name: it was asked for under that name; phiOf has returned
weights for it; and each of its parts, laid from the entry that was found, has its table with these
weights in the verifier's list of tables. -/
theorem family_of_name {v : Env} {fo : Model.Forest.Heard} {pts : List (String × Array E)}
    {mats : Array (ℕ × ℕ)} {asks : List TableAsk}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {funs : Array HFun}
    (hl : layTables mats asks 0 = some r) (ht : v.tab = r.1)
    (hfun : funsOf v.y fo pts r.2.1 = some funs) {n : String} {b : ℕ}
    (hb : v.tabAt n = some b) :
    ∃ a ∈ asks, a.name = n ∧ ∃ phi, phiOf v.y fo pts a = some phi ∧
      ∀ m ∈ (layParts mats a a.parts b).1,
        ({ mat := m.1, len := a.L, phi := phi, tree := 2, start := m.2 } : HFun) ∈ funs := by
  obtain ⟨x, hx, hxn, hxf⟩ := tabAt_mem hb
  rw [ht] at hx
  obtain ⟨q, q1, q2, q3, q4⟩ := layTables_laid mats _ 0 r hl x hx
  obtain ⟨phi, hphi, hmem⟩ := funsOf_mem hfun q1
  refine ⟨q.1, q2, q3.symm.trans hxn, phi, hphi, ?_⟩
  rw [← hxf, ← q4]
  exact hmem

/-! ## From Holds -/

section Run

variable {K : Type} [Field K] {h : Shape} {pc : List (List String)} {v : Env} {rd : Reads}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- Each of the four matrices is read at the end point of the second token sumcheck. -/
theorem points2_of_layout (hy : layout h pc = .ok v.y) (S : Switches h)
    (hrd : readsOf v.y = .ok rd) :
    "Y" ∈ rd.rdAF ∧ "Y" ∈ rd.rdXI ∧ "rt" ∈ rd.rdAD ∧ "rt" ∈ rd.rdAR :=
  points2_of_segs hrd (hasSeg_of_layout hy S .N1) (hasSeg_of_layout hy S .QK)

/-- The four families are found under their names. -/
theorem found2_of_layout {mats : Array (ℕ × ℕ)} (hy : layout h pc = .ok v.y) (S : Switches h)
    (hrd : readsOf v.y = .ok rd) (hl : layTables mats (tableAsks v.y rd v.g) 0 = some r)
    (ht : v.tab = r.1) : Found2 v := by
  obtain ⟨p1, p2, p3, p4⟩ := points2_of_layout hy S hrd
  obtain ⟨⟨a1, m1, e1, -⟩, ⟨a2, m2, e2, -⟩, ⟨a3, m3, e3, -⟩, ⟨a4, m4, e4, -⟩⟩ :=
    four_numbers v.y rd v.g p1 p2 p3 p4
  obtain ⟨-, c2⟩ := layTables_chain mats _ 0 r hl
  have F : ∀ a ∈ tableAsks v.y rd v.g, ∃ b, v.tabAt a.name = some b := by
    intro a ha
    refine found_name ?_
    rw [ht, c2]
    exact List.mem_map_of_mem ha
  exact ⟨e1 ▸ F a1 m1, e2 ▸ F a2 m2, e3 ▸ F a3 m3, e4 ▸ F a4 m4⟩

/-- TrueAt2 as a conclusion. Under the hypotheses of trueAt_of_holds
(Johnson/Road/FormsKeysTrue.lean), among them that every table of the verifier's list funs holds in
the world W what it says of the matrices M, and if the second token sumcheck has been heard (htT):
its end point has lt coordinates, and the four families of tables at that end point are true in W of
the cells that are read in the entries of M, at the verifier's own points: the first ls coordinates
of Z, and the end point. -/
theorem trueAt2_of_holds (ρ : Reading K) (W : World K) (hy : layout h pc = .ok v.y)
    (S : Switches h) (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
    (hl : layTables (matsR v.y v.g) (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    {tl : HTailF2} (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR v.y v.g)
    (hNM : tl.NM = tl.mats.size) {H : Heard} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)} {funs : Array HFun}
    (hp : pointsOf v.y H hd hd2 = some pts) (hfun : funsOf v.y H.fo pts r.2.1 = some funs)
    {tT : Tsc} (htT : H.tT = some tT) (M : Mats K)
    (Hd : ∀ Fn ∈ funs, Holds ρ W tl v.iU3 v.K3 M Fn) :
    ∃ Z, lastOf H.fo.zx v.y.h.la = .ok Z ∧ tT.r.size = v.y.h.lt ∧
      TrueAt2 ρ W v v.y.h.lt (cellsAt v.y M) (pt ρ Z) (pt ρ tT.r) := by
  have A := admitted_of_layout hy S.p3
  have L2 := laid2_of_layout hy
  have hT := L2.T
  have hla : v.y.h.la = v.y.ls + v.y.h.lt := by
    rw [A.shape]
    exact A.la
  obtain ⟨p1, p2, p3, p4⟩ := points2_of_layout hy S hrd
  obtain ⟨n0, n4, n1, n2⟩ := four_numbers v.y rd v.g p1 p2 p3 p4
  obtain ⟨Z, hZ, fY, fr⟩ := pointsOf_names2 hp htT
  obtain ⟨-, hT5⟩ := tails_sizes v.y hg
  have hZs : Z.size = v.y.h.la := size_last hZ
  -- one family: its weights, the size of its point, and Laid1
  have step : ∀ (n : String) (mat L : ℕ) (P : String) (Y : Array E) (lng : Bool), mat ≤ 5 →
      n ∈ ["af" ++ "@" ++ "Y", "xbI" ++ "@" ++ "Y", "ad" ++ "@" ++ "rt", "ar" ++ "@" ++ "rt"] →
      (∃ a ∈ tableAsks v.y rd v.g, a.name = n ∧ a.M0 = firstM v.y mat ∧
        a.parts = partsM v.y mat ∧ a.L = L ∧ a.point = P ∧ a.lng = lng) →
      pts.find? (fun p => p.1 == P) = some (P, Y) →
      ∀ tb, v.tabAt n = some tb →
        Y.size = (if lng then v.y.h.la else v.y.h.lt) ∧
        Laid1 ρ W v tl funs tb mat L (rowsM v.y mat / L)
          (if lng then longPhi Y v.y.ls v.y.h.lt else eqTab Y) := by
    intro n mat L P Y lng hmat hn ⟨a, ha, an, aM, ap, aL, aP, al⟩ hf tb htb
    obtain ⟨a', ha', an', phi, hphi, hfn⟩ := family_of_name hl ht hfun htb
    have ea : a' = a := ask_of_name hrd ha' ha (an'.trans an.symm)
    subst ea
    obtain ⟨b0, b1, b2⟩ := four_not_b n hn
    rw [← an'] at b0 b1 b2
    obtain ⟨hsz, hph⟩ := phiOf_inv hphi b0 b1 b2 aP hf
    rw [al] at hsz hph
    refine ⟨hsz, ?_⟩
    rw [← aL, ← hph]
    refine laid1_family hl ht htb (fun q' hq' e => ask_of_name hrd hq' ha' (e.trans an'.symm)) aM
      (fun p hp' => ?_) (fun p hp' => ?_) hfn
    · rw [ap] at hp'
      rw [aM]
      exact tails_pair v.y hg hmat hp'
    · rw [ap] at hp'
      rw [aM]
      obtain ⟨hi, -, -⟩ := hT5 mat p hmat hp'
      have hsz2 : tl.mats.size = ((Model.Layer.tailsOf v.y).getD v.g {}).mats.size := by
        have h1 := congrArg Array.size htm
        simpa [matsR] using h1
      have hi' : firstM v.y mat + p < tl.mats.size := by
        rw [hsz2]
        exact hi
      have e := getD_map_sizes tl.mats hi'
      rw [htm, tails_pair v.y hg hmat hp'] at e
      exact ⟨by rw [hNM]; exact hi', (congrArg Prod.fst e).symm, (congrArg Prod.snd e).symm⟩
  -- the end point's size, from the family ad@rt, which is found
  obtain ⟨tb1, htb1⟩ := (found2_of_layout hy S hrd hl ht).ad
  have hrt : tT.r.size = v.y.h.lt :=
    (step _ 1 _ "rt" tT.r false (by omega) (by simp) n1 fr tb1 htb1).1
  have hTr : v.y.T = 2 ^ tT.r.size := by rw [hrt]; exact hT
  -- a short family
  have short : ∀ (n : String) (mat : ℕ), mat ≤ 5 →
      n ∈ ["af" ++ "@" ++ "Y", "xbI" ++ "@" ++ "Y", "ad" ++ "@" ++ "rt", "ar" ++ "@" ++ "rt"] →
      (∃ a ∈ tableAsks v.y rd v.g, a.name = n ∧ a.M0 = firstM v.y mat ∧
        a.parts = partsM v.y mat ∧ a.L = v.y.T ∧ a.point = "rt" ∧ a.lng = false) →
      ∀ tb, v.tabAt n = some tb →
        ShortTrue ρ W v tb mat v.y.h.lt (cellsAt v.y M) (pt ρ tT.r) := by
    intro n mat hmat hn hnum tb htb
    have L1 := (step n mat _ "rt" tT.r false hmat hn hnum fr tb htb).2
    rw [← hrt]
    refine (shortTrue_iff_phi ρ W v tb mat _ tT.r).mpr fun φ a hφ => ?_
    rw [short_of_holds Hd L1 hφ, hTr]
    rfl
  -- a long family
  have hYs : (longPoint (Z.extract 0 v.y.ls) tT.r).size = v.y.ls + v.y.h.lt := by
    unfold longPoint
    rw [Array.size_append, Array.size_extract, hrt, hZs]
    omega
  have hYu : ∀ j, j < v.y.h.lt →
      pt ρ tT.r j = pt ρ (longPoint (Z.extract 0 v.y.ls) tT.r) (v.y.ls + j) := by
    intro j hj
    have h1 : (Z.extract 0 v.y.ls).size = v.y.ls := by
      rw [Array.size_extract, hZs]
      omega
    unfold pt longPoint
    congr 1
    simp [Array.getD, h1, hrt, hj]
  have hYl : ∀ j, j < v.y.ls →
      pt ρ (longPoint (Z.extract 0 v.y.ls) tT.r) (0 + j) = pt ρ Z (0 + j) := by
    intro j hj
    have h1 : (Z.extract 0 v.y.ls).size = v.y.ls := by
      rw [Array.size_extract, hZs]
      omega
    have h2 : j < Z.size := by
      rw [hZs]
      omega
    unfold pt longPoint
    congr 1
    simp [Array.getD, h1, hrt, hj, h2]
    omega
  have long : ∀ (n : String) (mat : ℕ), mat ≤ 5 → mat ∈ [0, 3, 4, 5] →
      n ∈ ["af" ++ "@" ++ "Y", "xbI" ++ "@" ++ "Y", "ad" ++ "@" ++ "rt", "ar" ++ "@" ++ "rt"] →
      (∃ a ∈ tableAsks v.y rd v.g, a.name = n ∧ a.M0 = firstM v.y mat ∧
        a.parts = partsM v.y mat ∧ a.L = 2 ^ v.y.h.la ∧ a.point = "Y" ∧ a.lng = true) →
      ∀ tb, v.tabAt n = some tb →
        LongTrue ρ W v tb mat v.y.ls v.y.h.lt (cellsAt v.y M) (pt ρ Z) (pt ρ tT.r) := by
    intro n mat hmat hm4 hn hnum tb htb
    have L1 := (step n mat _ "Y" _ true hmat hn hnum fY tb htb).2
    obtain ⟨lm, hle, hrow⟩ := rows_of_laid2 L2 mat hm4
    have e1 : 2 ^ v.y.h.la = 2 ^ v.y.ls * v.y.T := by rw [hT, ← Nat.pow_add, ← hla]
    have hfc : fcM v.y mat = rowsM v.y mat / 2 ^ v.y.h.la * 2 ^ v.y.ls := by
      unfold fcM
      rw [hrow, hT, Nat.pow_div (by omega) (by norm_num), Nat.pow_div hle (by norm_num),
        ← Nat.pow_add]
      congr 1
      omega
    have L1' : Laid1 ρ W v tl funs tb mat (2 ^ v.y.ls * v.y.T) (rowsM v.y mat / 2 ^ v.y.h.la)
        (longPhi (longPoint (Z.extract 0 v.y.ls) tT.r) v.y.ls v.y.h.lt) := by
      rw [← e1]
      exact L1
    have T1 : LongTrue ρ W v tb mat v.y.ls v.y.h.lt (cellsAt v.y M)
        (pt ρ (longPoint (Z.extract 0 v.y.ls) tT.r)) (pt ρ tT.r) := by
      refine (longTrue_iff_phi ρ W v tb mat v.y.h.lt _ hYs hYu).mpr fun b a hb => ?_
      rw [long_of_holds Hd hfc L1' hb, hT]
    intro b a hb
    rw [T1 b a hb]
    refine sum_congr rfl fun r' _ => ?_
    rw [eqN_congr' v.y.ls 0 hYl r']
  exact ⟨Z, hZ, hrt,
    { af := long _ 0 (by omega) (by simp) (by simp) n0
      xi := long _ 4 (by omega) (by simp) (by simp) n4
      ad := short _ 1 (by omega) (by simp) n1
      ar := short _ 2 (by omega) (by simp) n2 }⟩

/-- The hypotheses on the world can be met together at any matrices. Under the hypotheses of
trueAt_of_holds but the one on the world, with the second token sumcheck heard: for any matrices M
there is one world in which every table of the verifier's list holds what it says of M, the six
families at the lookup's point are true, and the four families at the end point of the second token
sumcheck are true, all of the cells that are read in the entries of M. -/
theorem trueAt2_met (ρ : Reading K) (hy : layout h pc = .ok v.y) (S : Switches h)
    (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
    (hl : layTables (matsR v.y v.g) (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    {tl : HTailF2} (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR v.y v.g)
    (hNM : tl.NM = tl.mats.size) {H : Heard} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)} {funs : Array HFun}
    (hp : pointsOf v.y H hd hd2 = some pts) (hzt : lastOf H.fo.zx v.y.h.lt = .ok H.ztF)
    (hfun : funsOf v.y H.fo pts r.2.1 = some funs) {tT : Tsc} (htT : H.tT = some tT)
    (M : Mats K) :
    ∃ W : World K, (∀ Fn ∈ funs, Holds ρ W tl v.iU3 v.K3 M Fn) ∧
      ∃ Z, lastOf H.fo.zx v.y.h.la = .ok Z ∧
        TrueAt ρ W v v.y.h.lt (cellsAt v.y M) (pt ρ Z) (pt ρ H.ztF) ∧
        TrueAt2 ρ W v v.y.h.lt (cellsAt v.y M) (pt ρ Z) (pt ρ tT.r) := by
  obtain ⟨W, hW, Z, hZ, T⟩ := trueAt_met ρ hy S hg hrd hl ht htm hNM hp hzt hfun M
  obtain ⟨Z', hZ', -, T2⟩ := trueAt2_of_holds ρ W hy S hg hrd hl ht htm hNM hp hfun htT M hW
  have e : Z' = Z := by
    rw [hZ] at hZ'
    exact (Except.ok.inj hZ').symm
  subst e
  exact ⟨W, hW, Z', hZ, T, T2⟩

end Run

#print axioms points2_of_layout
#print axioms found2_of_layout
#print axioms trueAt2_of_holds
#print axioms trueAt2_met

end OnBytes.Road
