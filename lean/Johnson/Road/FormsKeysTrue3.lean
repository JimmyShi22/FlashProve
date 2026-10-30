-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysTrue3.lean: the tables of the reads at the norms' points and at the
embedding's point are true, from what the tables say.

The reads of a layer sub-proof hold families of tables: each entry is a sum of a matrix's cells
under the weights of a point. Johnson/Road/FormsKeysTrue.lean and FormsKeysTrue2.lean conclude, from
one hypothesis on the reads (every table of the verifier's list holds what it says of the matrices
M), that the families at the lookup's point and at the end point of the second token sumcheck are
true of the cells that are read in M. This file does the same for the families that the claims on
the norms and on the embedding read: the stream that comes in and af at the point Z_V, ar at P_V and
r_tV, and, in the first group, the stream that comes in at Z_E.

What is compared with what: the verifier's functions with themselves (readsOf, tableAsks, layTables,
pointsOf, phiOf, funsOf) and with this folder's predicates ShortTrue and LongTrue.

Main theorems.
 - family_laid, short_family, long_family: one family of tables, under any name, on any of the six
   matrices, at any point of the verifier's list. They are the steps inside the proof of
   trueAt2_of_holds, lifted out and freed of its four names.
 - readsOf_points3: readsOf lists these points for every layout; five_numbers; pointsOf_names3.
 - trueAt3_of_holds: the record TrueAt3 as a conclusion.
Main definition: TrueAt3.

Hypotheses that no theorem concludes: those of trueAt_of_holds: the verifier's own lines (layout,
readsOf, layTables, pointsOf and funsOf return; the environment's tables are those laid; the plan's
list of matrices), the switches, and Hd, the hypothesis on the world. That they can be met together:
holds_met (Johnson/Road/FormsKeysMet.lean) gives a world with Hd at any matrices, under these lines;
the lines are run in Johnson/Road/FormsKeysCallerRun.lean, at a made-up shape.

What is not claimed. That the reads hold what they say: Hd stands for the smallness test. Nothing on
the tables of af at Z_a and Z_b, which the claims on the gated products read: long_family serves
them as it stands, but no record here names them. The program does not import this file.
-/
import Johnson.Road.FormsKeysTrue2

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff HFun HTailF2 Level Tsc lastOf eqTab longPhi longPoint)
open OnBytes.Model.Layer (Env Lay Shape Reads Heard TableAsk TableAt layout readsOf readsR layTables
  layParts tableAsks pointsOf phiOf funsOf)

/-! ## One family of tables, at any point of the verifier's list -/

section Family

variable {K : Type} [Field K] {h : Shape} {pc : List (List String)} {v : Env} {rd : Reads}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
  (ρ : Reading K) (W : World K) (hy : layout h pc = .ok v.y) (S : Switches h)
  (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
  (hl : layTables (matsR v.y v.g) (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
  {tl : HTailF2} (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR v.y v.g)
  (hNM : tl.NM = tl.mats.size) {fo : Model.Forest.Heard} {pts : List (String × Array E)}
  {funs : Array HFun} (hfun : funsOf v.y fo pts r.2.1 = some funs)

include hg hrd hl ht htm hNM hfun in
/-- One family of tables that is not on the matrix of counts: the size of its point, and where its
tables lie, with their weights. The step inside the proof of trueAt2_of_holds
(Johnson/Road/FormsKeysTrue2.lean), for any name and any point of the verifier's list. -/
theorem family_laid {n : String} {mat L : ℕ} {P : String} {Y : Array E} {lng : Bool}
    (hmat : mat ≤ 5)
    (hnb : (n == "b-bits-0") = false ∧ (n == "b-bits-1") = false ∧ (n == "b-pin") = false)
    (hnum : ∃ a ∈ tableAsks v.y rd v.g, a.name = n ∧ a.M0 = firstM v.y mat ∧
      a.parts = partsM v.y mat ∧ a.L = L ∧ a.point = P ∧ a.lng = lng)
    (hf : pts.find? (fun p => p.1 == P) = some (P, Y)) {tb : ℕ} (htb : v.tabAt n = some tb) :
    Y.size = (if lng then v.y.h.la else v.y.h.lt) ∧
      Laid1 ρ W v tl funs tb mat L (rowsM v.y mat / L)
        (if lng then longPhi Y v.y.ls v.y.h.lt else eqTab Y) := by
  obtain ⟨a, ha, an, aM, ap, aL, aP, al⟩ := hnum
  obtain ⟨-, hT5⟩ := tails_sizes v.y hg
  obtain ⟨a', ha', an', phi, hphi, hfn⟩ := family_of_name hl ht hfun htb
  have ea : a' = a := ask_of_name hrd ha' ha (an'.trans an.symm)
  subst ea
  obtain ⟨b0, b1, b2⟩ := hnb
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

variable (M : Mats K) (Hd : ∀ Fn ∈ funs, Holds ρ W tl v.iU3 v.K3 M Fn)

include hy hg hrd hl ht htm hNM hfun Hd in
/-- A family of short tables at the point Y of the verifier's list: Y has lt coordinates, and the
tables are true of the cells that are read in the entries of M. -/
theorem short_family {n : String} {mat : ℕ} {P : String} {Y : Array E} (hmat : mat ≤ 5)
    (hnb : (n == "b-bits-0") = false ∧ (n == "b-bits-1") = false ∧ (n == "b-pin") = false)
    (hnum : ∃ a ∈ tableAsks v.y rd v.g, a.name = n ∧ a.M0 = firstM v.y mat ∧
      a.parts = partsM v.y mat ∧ a.L = v.y.T ∧ a.point = P ∧ a.lng = false)
    (hf : pts.find? (fun p => p.1 == P) = some (P, Y)) {tb : ℕ} (htb : v.tabAt n = some tb) :
    Y.size = v.y.h.lt ∧ ShortTrue ρ W v tb mat v.y.h.lt (cellsAt v.y M) (pt ρ Y) := by
  have hT := (laid2_of_layout hy).T
  obtain ⟨hs, L1⟩ := family_laid ρ W hg hrd hl ht htm hNM hfun hmat hnb hnum hf htb
  have hs' : Y.size = v.y.h.lt := hs
  have hTr : v.y.T = 2 ^ Y.size := by rw [hs']; exact hT
  refine ⟨hs', ?_⟩
  rw [← hs']
  refine (shortTrue_iff_phi ρ W v tb mat _ Y).mpr fun φ a hφ => ?_
  rw [short_of_holds Hd L1 hφ, hTr]
  rfl

include hy S hg hrd hl ht htm hNM hfun Hd in
/-- A family of long tables at the point Y of the verifier's list: Y has la coordinates, and the
tables are true of the cells that are read in the entries of M, at the first ls coordinates of Y for
the features of a block and the others for the positions. -/
theorem long_family {n : String} {mat : ℕ} {P : String} {Y : Array E} (hmat : mat ≤ 5)
    (hm4 : mat ∈ [0, 3, 4, 5])
    (hnb : (n == "b-bits-0") = false ∧ (n == "b-bits-1") = false ∧ (n == "b-pin") = false)
    (hnum : ∃ a ∈ tableAsks v.y rd v.g, a.name = n ∧ a.M0 = firstM v.y mat ∧
      a.parts = partsM v.y mat ∧ a.L = 2 ^ v.y.h.la ∧ a.point = P ∧ a.lng = true)
    (hf : pts.find? (fun p => p.1 == P) = some (P, Y)) {tb : ℕ} (htb : v.tabAt n = some tb) :
    Y.size = v.y.h.la ∧ LongTrue ρ W v tb mat v.y.ls v.y.h.lt (cellsAt v.y M) (pt ρ Y)
      (fun j => pt ρ Y (v.y.ls + j)) := by
  have A := admitted_of_layout hy S.p3
  have L2 := laid2_of_layout hy
  have hT := L2.T
  have hla : v.y.h.la = v.y.ls + v.y.h.lt := by
    rw [A.shape]
    exact A.la
  obtain ⟨hs, L1⟩ := family_laid ρ W hg hrd hl ht htm hNM hfun hmat hnb hnum hf htb
  have hs' : Y.size = v.y.h.la := hs
  obtain ⟨lm, hle, hrow⟩ := rows_of_laid2 L2 mat hm4
  have e1 : 2 ^ v.y.h.la = 2 ^ v.y.ls * v.y.T := by rw [hT, ← Nat.pow_add, ← hla]
  have hfc : fcM v.y mat = rowsM v.y mat / 2 ^ v.y.h.la * 2 ^ v.y.ls := by
    unfold fcM
    rw [hrow, hT, Nat.pow_div (by omega) (by norm_num), Nat.pow_div hle (by norm_num),
      ← Nat.pow_add]
    congr 1
    omega
  have L1' : Laid1 ρ W v tl funs tb mat (2 ^ v.y.ls * v.y.T) (rowsM v.y mat / 2 ^ v.y.h.la)
      (longPhi Y v.y.ls v.y.h.lt) := by
    rw [← e1]
    exact L1
  refine ⟨hs', (longTrue_iff_phi ρ W v tb mat v.y.h.lt _ (by rw [hs', hla])
    (fun j _ => rfl)).mpr fun b a hb => ?_⟩
  rw [long_of_holds Hd hfc L1' hb, hT]

end Family

/-! ## The five families -/

/-- The entries of five more families of tables are true in the world W: the long tables of the
stream that comes in and of af at the point named Z_V, whose first ls coordinates are lowV and whose
others are uV; the short tables of ar at the points named P_V and r_tV; and, in the first group, the
long table of the stream that comes in at the point named Z_E. -/
structure TrueAt3 {K : Type} [Field K] (ρ : Reading K) (W : World K) (v : Env) (lT : ℕ)
    (c : Cells K) (lowV uV uP uR lowE uE : ℕ → K) : Prop where
  /-- the stream that comes in, at Z_V -/
  xiV : ∀ b, v.tabAt ("xbI" ++ "@" ++ "Z_V") = some b → LongTrue ρ W v b 4 v.y.ls lT c lowV uV
  /-- af at Z_V -/
  afV : ∀ b, v.tabAt ("af" ++ "@" ++ "Z_V") = some b → LongTrue ρ W v b 0 v.y.ls lT c lowV uV
  /-- ar at P_V -/
  arP : ∀ b, v.tabAt ("ar" ++ "@" ++ "P_V") = some b → ShortTrue ρ W v b 2 lT c uP
  /-- ar at r_tV -/
  arR : ∀ b, v.tabAt ("ar" ++ "@" ++ "r_tV") = some b → ShortTrue ρ W v b 2 lT c uR
  /-- in the first group: the stream that comes in, at Z_E -/
  xiE : v.g = 0 → ∀ b, v.tabAt ("xbI" ++ "@" ++ "Z_E") = some b →
    LongTrue ρ W v b 4 v.y.ls lT c lowE uE

/-- The lists of points that readsOf returns have the norms' points, for every layout. -/
theorem readsOf_points3 {y : Lay} {rd : Reads} (h : readsOf y = .ok rd) :
    "Z_V" ∈ rd.rdAF ∧ "Z_V" ∈ rd.rdXI ∧ "P_V" ∈ rd.rdAR ∧ "r_tV" ∈ rd.rdAR := by
  unfold readsOf at h
  have h2 := refuse_bind h
  have e := (Except.ok.inj h2).symm
  subst e
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_singleton.mpr rfl)))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_singleton.mpr rfl)))
  · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self))
  · exact List.mem_append_left _ (List.mem_append_right _
      (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)))

/-- The numbers of the five families. -/
theorem five_numbers (y : Lay) (rd : Reads) (g : ℕ) (hAF : "Z_V" ∈ rd.rdAF)
    (hXI : "Z_V" ∈ rd.rdXI) (hP : "P_V" ∈ rd.rdAR) (hR : "r_tV" ∈ rd.rdAR) :
    (∃ a ∈ tableAsks y rd g, a.name = "af" ++ "@" ++ "Z_V" ∧ a.M0 = firstM y 0 ∧
      a.parts = partsM y 0 ∧ a.L = 2 ^ y.h.la ∧ a.point = "Z_V" ∧ a.lng = true) ∧
    (∃ a ∈ tableAsks y rd g, a.name = "xbI" ++ "@" ++ "Z_V" ∧ a.M0 = firstM y 4 ∧
      a.parts = partsM y 4 ∧ a.L = 2 ^ y.h.la ∧ a.point = "Z_V" ∧ a.lng = true) ∧
    (∃ a ∈ tableAsks y rd g, a.name = "ar" ++ "@" ++ "P_V" ∧ a.M0 = firstM y 2 ∧
      a.parts = partsM y 2 ∧ a.L = y.T ∧ a.point = "P_V" ∧ a.lng = false) ∧
    (∃ a ∈ tableAsks y rd g, a.name = "ar" ++ "@" ++ "r_tV" ∧ a.M0 = firstM y 2 ∧
      a.parts = partsM y 2 ∧ a.L = y.T ∧ a.point = "r_tV" ∧ a.lng = false) ∧
    (g = 0 → ∃ a ∈ tableAsks y rd g, a.name = "xbI" ++ "@" ++ "Z_E" ∧ a.M0 = firstM y 4 ∧
      a.parts = partsM y 4 ∧ a.L = 2 ^ y.h.la ∧ a.point = "Z_E" ∧ a.lng = true) := by
  have m : ∀ (f : String → TableAsk) (p : String) (l : List String), p ∈ l → f p ∈ l.map f :=
    fun f p l h => List.mem_map.mpr ⟨p, h, rfl⟩
  refine
   ⟨⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (m _ _ _ hAF)))))))),
      rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (m _ _ _ hXI))))))), rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨_, List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (m _ _ _ hP))), rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨_, List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (m _ _ _ hR))), rfl, rfl, rfl, rfl, rfl, rfl⟩, fun h0 => ?_⟩
  subst h0
  exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_singleton.mpr rfl)))))), rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- In the verifier's list of points by name: Z_V is the last la coordinates of the challenges of
the product layer of the squares; P_V the norms' token point; Z_E the embedding's point; r_tV the
challenges of the token sumcheck of the row products. -/
theorem pointsOf_names3 {y : Lay} {H : Heard} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)} (h : pointsOf y H hd hd2 = some pts) :
    ∃ ZV, lastOf H.wpl.r y.h.la = .ok ZV ∧
      pts.find? (fun p => p.1 == "Z_V") = some ("Z_V", ZV) ∧
      pts.find? (fun p => p.1 == "P_V") = some ("P_V", H.PV) ∧
      pts.find? (fun p => p.1 == "Z_E") = some ("Z_E", H.ZE) ∧
      pts.find? (fun p => p.1 == "r_tV") = some ("r_tV", H.tV.r) := by
  unfold pointsOf at h
  obtain ⟨Z, hZ, h⟩ := bind_some h
  cases hd2 with
  | none =>
    obtain ⟨routed, _, h⟩ := bind_some h
    obtain ⟨a, ha, h⟩ := bind_some h
    obtain ⟨b, _, h⟩ := bind_some h
    have e := Option.some.inj h
    subst e
    exact ⟨a, ok_of_toOption ha, by simp, by simp, by simp, by simp⟩
  | some o =>
    obtain ⟨routed, _, h⟩ := bind_some h
    obtain ⟨a, ha, h⟩ := bind_some h
    obtain ⟨b, _, h⟩ := bind_some h
    have e := Option.some.inj h
    subst e
    exact ⟨a, ok_of_toOption ha, by simp, by simp, by simp, by simp⟩

section Run

variable {K : Type} [Field K] {h : Shape} {pc : List (List String)} {v : Env} {rd : Reads}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- TrueAt3 as a conclusion. Under the hypotheses of trueAt_of_holds
(Johnson/Road/FormsKeysTrue.lean), among them that every table of the verifier's list funs holds in
the world W what it says of the matrices M: the five families of tables at the norms' points and at
the embedding's point are true in W of the cells that are read in the entries of M, at the
verifier's own points. -/
theorem trueAt3_of_holds (ρ : Reading K) (W : World K) (hy : layout h pc = .ok v.y)
    (S : Switches h) (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
    (hl : layTables (matsR v.y v.g) (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    {tl : HTailF2} (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR v.y v.g)
    (hNM : tl.NM = tl.mats.size) {H : Heard} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)} {funs : Array HFun}
    (hp : pointsOf v.y H hd hd2 = some pts) (hfun : funsOf v.y H.fo pts r.2.1 = some funs)
    (M : Mats K) (Hd : ∀ Fn ∈ funs, Holds ρ W tl v.iU3 v.K3 M Fn) :
    ∃ ZV, lastOf H.wpl.r v.y.h.la = .ok ZV ∧
      TrueAt3 ρ W v v.y.h.lt (cellsAt v.y M) (pt ρ ZV) (fun j => pt ρ ZV (v.y.ls + j))
        (pt ρ H.PV) (pt ρ H.tV.r) (pt ρ H.ZE) (fun j => pt ρ H.ZE (v.y.ls + j)) := by
  obtain ⟨p1, p2, p3, p4⟩ := readsOf_points3 hrd
  obtain ⟨n0, n4, nP, nR, nE⟩ := five_numbers v.y rd v.g p1 p2 p3 p4
  obtain ⟨ZV, hZV, fV, fP, fE, fR⟩ := pointsOf_names3 hp
  refine ⟨ZV, hZV, ?_⟩
  exact
    { xiV := fun b hb => (long_family ρ W hy S hg hrd hl ht htm hNM hfun M Hd (by omega) (by simp)
        (by simp) n4 fV hb).2
      afV := fun b hb => (long_family ρ W hy S hg hrd hl ht htm hNM hfun M Hd (by omega) (by simp)
        (by simp) n0 fV hb).2
      arP := fun b hb => (short_family ρ W hy hg hrd hl ht htm hNM hfun M Hd (by omega)
        (by simp) nP fP hb).2
      arR := fun b hb => (short_family ρ W hy hg hrd hl ht htm hNM hfun M Hd (by omega)
        (by simp) nR fR hb).2
      xiE := fun h0 b hb => (long_family ρ W hy S hg hrd hl ht htm hNM hfun M Hd (by omega)
        (by simp) (by simp) (nE h0) fE hb).2 }

end Run

#print axioms family_laid
#print axioms short_family
#print axioms long_family
#print axioms trueAt3_of_holds

end OnBytes.Road
