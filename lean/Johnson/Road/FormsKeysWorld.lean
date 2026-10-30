-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysWorld.lean: a world in which the tables that the lookup's forms read are true,
for any cells.

Johnson/Road/FormsKeysFits.lean leaves one hypothesis on hidden values: the record Tabs, which says
that six families of tables are found under their names and that their entries hold the sums of
cells that they stand for. This file shows that the record can be met. For any cells and any point
it defines a world (worldOf with meanOf) and proves Tabs of it, if the verifier's list of families
is the one that layTables returns and the six names are among the names that were asked for.

The way. layTables lays the families one after the other, and refuses an empty one (Chain,
layTables_chain). So an entry of the reads lies in at most one family (chain_holder, chain_apart),
and no two families begin at one entry (chain_first). The world gives an entry the value that the
name of its family and its place in the family stand for. Env.U3at names an entry through the family
that begins at a given entry, and refuses a place past that family's end, so a form that it returns
is worth the value of that family (world_entry).

Which names are asked for follows from the layout: each of the six matrices is read at the lookup's
point if the calls have the segments CN1, CV, O, D and ROW (readsOf_points, points_of_segs). They
have them if three lines of layoutBase hold of the layout (hasSeg_of_taken, five_segs).

Main definitions: Chain, holds, readAt, worldOf, longAt, shortAt, meanOf, anyZ, HasSeg.
Main theorems: layTables_chain, chain_apart, world_entry, found_of_names, trueAt_of_chain,
tabs_of_chain, tabs_of_layTables, found_of_reads, tabs_of_reads, hasSeg_of_taken, five_segs.

What is not claimed. The three lines of layoutBase are hypotheses of five_segs here;
Johnson/Road/FormsKeysLaid.lean proves them of every layout that the verifier's function returns
for a shape with routed experts.
The world is made for this purpose: its entries are true by its definition, and nothing says that a
prover's reads are such a world. What the world shows is that one world can serve all six families
at once, for any cells. What does not speak of the world, that the six names are found, is stated
apart (found_of_names, found_of_reads), for use with any world. That entry number φ of a family
belongs to feature or block number φ of its matrix is the reading of ShortTrue and LongTrue, which
the world follows; how the parts of a matrix share a family's entries is not looked at. A family
under another name than the six holds 0. If two families had one name, both would hold the values
that the name stands for. See also Johnson/Road/FormsKeysKit.lean. The program does not import this
file.
-/
import Johnson.Road.FormsKeysFits

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff)
open OnBytes.Model (refuseIf Seg CallD SegAsk place)
open OnBytes.Model.Layer (Env Lay Reads TableAsk TableAt layParts layTables tableAsks readsZ
  readsOf takeSegments takeCalls segmentList)

/-! ## The families lie one after the other -/

/-- The families of a list lie one after the other from entry p on, and none is empty. -/
def Chain : List TableAt → ℕ → Prop
  | [], _ => True
  | x :: l, p => x.first = p ∧ 0 < x.len ∧ Chain l (p + x.len)

/-- What Chain says of a list with a first member. -/
theorem chain_cons {x : TableAt} {l : List TableAt} {p : ℕ} :
    Chain (x :: l) p ↔ x.first = p ∧ 0 < x.len ∧ Chain l (p + x.len) := Iff.rfl

/-- The first free entry after the parts of a family is not before the first entry. -/
theorem layParts_le (mats : Array (ℕ × ℕ)) (a : TableAsk) :
    ∀ (n p : ℕ), p ≤ (layParts mats a n p).2
  | 0, p => Nat.le_refl p
  | n + 1, p => by
    show p ≤ (layParts mats a n (p + (mats.getD (a.M0 + (a.parts - (n + 1))) (0, 0)).2 *
      ((mats.getD (a.M0 + (a.parts - (n + 1))) (0, 0)).1 / a.L))).2
    exact Nat.le_trans (Nat.le_add_right _ _) (layParts_le mats a n _)

/-- What layTables returns lies one family after the other from its first entry on, and has the
names that were asked for, in their order. -/
theorem layTables_chain (mats : Array (ℕ × ℕ)) : ∀ (asks : List TableAsk) (p : ℕ)
    (r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ), layTables mats asks p = some r →
    Chain r.1 p ∧ r.1.map (·.name) = asks.map (·.name)
  | [], p, r, h => by
    have e : r = ([], [], p) := by simpa [layTables] using h.symm
    subst e
    exact ⟨trivial, rfl⟩
  | a :: rest, p, r, h => by
    have hle := layParts_le mats a a.parts p
    have h' : (if ((layParts mats a a.parts p).2 == p) = true then none else
        (layTables mats rest (layParts mats a a.parts p).2).map fun r =>
          ((⟨a.name, p, (layParts mats a a.parts p).2 - p⟩ : TableAt) :: r.1,
            (a, (layParts mats a a.parts p).1) :: r.2.1, r.2.2)) = some r := h
    by_cases hq : ((layParts mats a a.parts p).2 == p) = true
    · rw [if_pos hq] at h'
      cases h'
    · rw [if_neg hq] at h'
      obtain ⟨r', h1, h2⟩ := map_some h'
      obtain ⟨c1, c2⟩ := layTables_chain mats rest _ r' h1
      subst h2
      have hne : (layParts mats a a.parts p).2 ≠ p := by simpa using hq
      have e : p + ((layParts mats a a.parts p).2 - p) = (layParts mats a a.parts p).2 := by omega
      refine ⟨chain_cons.mpr ⟨rfl, ?_, ?_⟩, ?_⟩
      · show 0 < (layParts mats a a.parts p).2 - p
        omega
      · show Chain r'.1 (p + ((layParts mats a a.parts p).2 - p))
        rw [e]
        exact c1
      · show a.name :: r'.1.map (·.name) = a.name :: rest.map (·.name)
        rw [c2]

/-- No family of a chain begins before the chain. -/
theorem chain_ge : ∀ (l : List TableAt) (p : ℕ), Chain l p → ∀ x ∈ l, p ≤ x.first
  | [], _, _, x, hx => by simp at hx
  | y :: l, p, h, x, hx => by
    obtain ⟨h1, _, h3⟩ := chain_cons.mp h
    rcases List.mem_cons.mp hx with e | hx
    · subst e
      exact Nat.le_of_eq h1.symm
    · have := chain_ge l _ h3 x hx
      omega

/-- The search for the family that begins where a member x begins finds x. -/
theorem chain_first : ∀ (l : List TableAt) (p : ℕ), Chain l p → ∀ x ∈ l,
    l.find? (fun y => y.first == x.first) = some x
  | [], _, _, x, hx => by simp at hx
  | y :: l, p, h, x, hx => by
    obtain ⟨h1, h2, h3⟩ := chain_cons.mp h
    rcases List.mem_cons.mp hx with e | hx
    · subst e
      rw [List.find?_cons_of_pos (by simp)]
    · have hge := chain_ge l _ h3 x hx
      have hne : y.first ≠ x.first := by omega
      rw [List.find?_cons_of_neg (by simpa using hne)]
      exact chain_first l _ h3 x hx

/-- True if entry e of the reads lies in the family x. -/
def holds (e : ℕ) (x : TableAt) : Bool := decide (x.first ≤ e) && decide (e < x.first + x.len)

/-- The search for the family that holds an entry of a member x finds x. -/
theorem chain_holder : ∀ (l : List TableAt) (p : ℕ), Chain l p → ∀ x ∈ l, ∀ e : ℕ,
    x.first ≤ e → e < x.first + x.len → l.find? (holds e) = some x
  | [], _, _, x, hx, _, _, _ => by simp at hx
  | y :: l, p, h, x, hx, e, he1, he2 => by
    obtain ⟨h1, _, h3⟩ := chain_cons.mp h
    rcases List.mem_cons.mp hx with q | hx
    · subst q
      rw [List.find?_cons_of_pos (by simp [holds, he1, he2])]
    · have hge := chain_ge l _ h3 x hx
      have hn : ¬ e < y.first + y.len := by omega
      rw [List.find?_cons_of_neg (by simp [holds, hn])]
      exact chain_holder l _ h3 x hx e he1 he2

/-- Two families of a chain that share an entry are one. -/
theorem chain_apart {l : List TableAt} {p : ℕ} (h : Chain l p) {x y : TableAt} (hx : x ∈ l)
    (hy : y ∈ l) {e : ℕ} (x1 : x.first ≤ e) (x2 : e < x.first + x.len) (y1 : y.first ≤ e)
    (y2 : e < y.first + y.len) : x = y := by
  have a := chain_holder l p h x hx e x1 x2
  have b := chain_holder l p h y hy e y1 y2
  rw [a] at b
  exact Option.some.inj b

/-! ## The world -/

section TheWorld

variable {K : Type} [Field K]

/-- What entry e of the reads holds, if a family's entry number j holds mean name j: the value for
the family that holds e; 0 if none does. -/
def readAt (tab : List TableAt) (mean : String → ℕ → K) (e : ℕ) : K :=
  match tab.find? (holds e) with
  | some x => mean x.name (e - x.first)
  | none => 0

/-- What an entry holds that lies in the family x. -/
theorem readAt_of {tab : List TableAt} {mean : String → ℕ → K} {e : ℕ} {x : TableAt}
    (h : tab.find? (holds e) = some x) : readAt tab mean e = mean x.name (e - x.first) := by
  simp [readAt, h]

/-- The world in which entry i of row r of the array of the reads, which has K3 columns, holds what
entry r K3 + i of the reads stands for. Every other hidden value is 0. -/
def worldOf (iU3 K3 : ℕ) (tab : List TableAt) (mean : String → ℕ → K) : World K where
  slot _ := 0
  entry a r i := if a = iU3 then readAt tab mean (r * K3 + i) else 0

/-- In that world a form that Env.U3at returns for entry φ of the family found under the name n is
worth mean n φ. -/
theorem world_entry (ρ : Reading K) (v : Env) {p0 : ℕ} (hc : Chain v.tab p0)
    (mean : String → ℕ → K) {n : String} {tb φ : ℕ} {a : Aff} (ht : v.tabAt n = some tb)
    (h : v.U3at tb φ = some a) : a.value ρ (worldOf v.iU3 v.K3 v.tab mean) = mean n φ := by
  unfold Env.tabAt at ht
  obtain ⟨x, hx, hxf⟩ := map_some ht
  have hxf' : x.first = tb := hxf
  subst hxf'
  have hmem : x ∈ v.tab := List.mem_of_find?_eq_some hx
  have hname : x.name = n := by simpa using List.find?_some hx
  have hy := chain_first v.tab p0 hc x hmem
  unfold Env.U3at at h
  rw [hy] at h
  have h' : (if (decide (φ < x.len) && v.K3 != 0 &&
        decide ((x.first + φ) / v.K3 < 2 ^ 32)) = true then
      some (Aff.ent v.iU3 ((x.first + φ) / v.K3) ((x.first + φ) % v.K3)) else none) = some a := h
  by_cases hcnd : (decide (φ < x.len) && v.K3 != 0 &&
      decide ((x.first + φ) / v.K3 < 2 ^ 32)) = true
  · rw [if_pos hcnd] at h'
    have ha : Aff.ent v.iU3 ((x.first + φ) / v.K3) ((x.first + φ) % v.K3) = a :=
      Option.some.inj h'
    have hlen : φ < x.len := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcnd
      exact hcnd.1.1
    have hh := chain_holder v.tab p0 hc x hmem (x.first + φ) (Nat.le_add_right _ _) (by omega)
    rw [← ha, Aff.value_ent]
    show (if v.iU3 = v.iU3 then
      readAt v.tab mean ((x.first + φ) / v.K3 * v.K3 + (x.first + φ) % v.K3) else 0) = _
    rw [if_pos rfl, Nat.div_add_mod', readAt_of hh, hname, Nat.add_sub_cancel_left]
  · rw [if_neg hcnd] at h'
    cases h'

/-- What entry b of a long table of matrix mat stands for at the point (low | u). -/
def longAt (ls lt : ℕ) (c : Cells K) (low u : ℕ → K) (mat b : ℕ) : K :=
  ∑ r ∈ range (2 ^ ls), Blocks.eqN ls 0 low r * Blocks.ext lt (fun i => c mat (b * 2 ^ ls + r) i) u

/-- What entry φ of a short table of matrix mat stands for at the point u. -/
def shortAt (lt : ℕ) (c : Cells K) (u : ℕ → K) (mat φ : ℕ) : K :=
  Blocks.ext lt (fun i => c mat φ i) u

/-- What entry j of the family with the name n stands for: for the six names that the lookup's forms
read, the sum of cells of the name's matrix at the name's point; 0 for every other name. -/
def meanOf (ls lt : ℕ) (c : Cells K) (low u : ℕ → K) (n : String) (j : ℕ) : K :=
  if n = "af@Z" then longAt ls lt c low u 0 j
  else if n = "qa@Z" then longAt ls lt c low u 3 j
  else if n = "xbI@Z" then longAt ls lt c low u 4 j
  else if n = "xbO@Z" then longAt ls lt c low u 5 j
  else if n = "ad@zt" then shortAt lt c u 1 j
  else if n = "ar@zt" then shortAt lt c u 2 j
  else 0

/-- A name of the list is found. -/
theorem tabAt_some (v : Env) {n : String} (h : n ∈ v.tab.map (·.name)) :
    ∃ b, v.tabAt n = some b := by
  obtain ⟨x, hx, hn⟩ := List.mem_map.mp h
  have hn' : x.name = n := hn
  unfold Env.tabAt
  cases hf : v.tab.find? (fun t => t.name == n) with
  | none =>
    have hno := List.find?_eq_none.mp hf x hx
    simp [hn'] at hno
  | some y => exact ⟨y.first, rfl⟩

omit [Field K] in
/-- The six families are found if their names are among the names of the verifier's list. -/
theorem found_of_names (v : Env)
    (hAF : "af" ++ "@" ++ "Z" ∈ v.tab.map (·.name)) (hQA : "qa" ++ "@" ++ "Z" ∈ v.tab.map (·.name))
    (hXI : "xbI" ++ "@" ++ "Z" ∈ v.tab.map (·.name))
    (hXO : "xbO" ++ "@" ++ "Z" ∈ v.tab.map (·.name))
    (hAD : "ad" ++ "@" ++ "zt" ∈ v.tab.map (·.name))
    (hAR : "ar" ++ "@" ++ "zt" ∈ v.tab.map (·.name)) : Found v :=
  ⟨tabAt_some v hAF, tabAt_some v hQA, tabAt_some v hXI, tabAt_some v hXO, tabAt_some v hAD,
    tabAt_some v hAR⟩

variable (ρ : Reading K) (v : Env) {p0 : ℕ} (hc : Chain v.tab p0) (mean : String → ℕ → K)
  (lT : ℕ) (c : Cells K) (low u : ℕ → K)
include hc

/-- The long tables under a name are true in the world if the name stands for them. -/
theorem longTrue_world {n : String} {b mat : ℕ} (hb : v.tabAt n = some b)
    (hm : ∀ j, mean n j = longAt v.y.ls lT c low u mat j) :
    LongTrue ρ (worldOf v.iU3 v.K3 v.tab mean) v b mat v.y.ls lT c low u := by
  intro j a h
  exact (world_entry ρ v hc mean hb h).trans (hm j)

/-- The short tables under a name are true in the world if the name stands for them. -/
theorem shortTrue_world {n : String} {b mat : ℕ} (hb : v.tabAt n = some b)
    (hm : ∀ j, mean n j = shortAt lT c u mat j) :
    ShortTrue ρ (worldOf v.iU3 v.K3 v.tab mean) v b mat lT c u := by
  intro j a h
  exact (world_entry ρ v hc mean hb h).trans (hm j)

/-- The entries of the six families are true in the world, for any cells and any point, if the
families lie one after the other. -/
theorem trueAt_of_chain :
    TrueAt ρ (worldOf v.iU3 v.K3 v.tab (meanOf v.y.ls lT c low u)) v lT c low u where
  af := fun _ hb => longTrue_world ρ v hc _ lT c low u hb fun j => by simp [meanOf]
  qa := fun _ hb => longTrue_world ρ v hc _ lT c low u hb fun j => by simp [meanOf]
  xi := fun _ hb => longTrue_world ρ v hc _ lT c low u hb fun j => by simp [meanOf]
  xo := fun _ hb => longTrue_world ρ v hc _ lT c low u hb fun j => by simp [meanOf]
  ad := fun _ hb => shortTrue_world ρ v hc _ lT c u hb fun j => by simp [meanOf]
  ar := fun _ hb => shortTrue_world ρ v hc _ lT c u hb fun j => by simp [meanOf]

/-- The record Tabs holds of the world, for any cells and any point, if the families lie one after
the other and the six names are among theirs. -/
theorem tabs_of_chain
    (hAF : "af" ++ "@" ++ "Z" ∈ v.tab.map (·.name)) (hQA : "qa" ++ "@" ++ "Z" ∈ v.tab.map (·.name))
    (hXI : "xbI" ++ "@" ++ "Z" ∈ v.tab.map (·.name))
    (hXO : "xbO" ++ "@" ++ "Z" ∈ v.tab.map (·.name))
    (hAD : "ad" ++ "@" ++ "zt" ∈ v.tab.map (·.name))
    (hAR : "ar" ++ "@" ++ "zt" ∈ v.tab.map (·.name)) :
    Tabs ρ (worldOf v.iU3 v.K3 v.tab (meanOf v.y.ls lT c low u)) v lT c low u :=
  tabs_of (found_of_names v hAF hQA hXI hXO hAD hAR) (trueAt_of_chain ρ v hc lT c low u)

end TheWorld

/-! ## The names that are asked for -/

/-- The names of the families of group g, in their order. -/
theorem tableAsks_names (y : Lay) (rd : Reads) (g : ℕ) :
    (tableAsks y rd g).map (·.name) =
      rd.rdAF.map (fun n => "af" ++ "@" ++ n) ++ rd.rdQA.map (fun n => "qa" ++ "@" ++ n) ++
      rd.rdXI.map (fun n => "xbI" ++ "@" ++ n) ++
      (if g == 0 then ["xbI" ++ "@" ++ "Z_E"] else []) ++
      rd.rdXO.map (fun n => "xbO" ++ "@" ++ n) ++ rd.rdAD.map (fun n => "ad" ++ "@" ++ n) ++
      rd.rdAR.map (fun n => "ar" ++ "@" ++ n) ++
      (if y.h.p4 then rd.rdQS.map (fun n => "qa" ++ "@" ++ n) else []) ++
      ["b-bits-0", "b-bits-1", "b-pin"] := by
  unfold tableAsks
  cases hg : (g == 0) <;> cases hp : y.h.p4 <;> simp [List.map_map, Function.comp_def]

/-- The six names that the lookup's forms read are asked for if each matrix is read at the lookup's
point. -/
theorem six_names (y : Lay) (rd : Reads) (g : ℕ) (hAF : "Z" ∈ rd.rdAF) (hQA : "Z" ∈ rd.rdQA)
    (hXI : "Z" ∈ rd.rdXI) (hXO : "Z" ∈ rd.rdXO) (hAD : "zt" ∈ rd.rdAD) (hAR : "zt" ∈ rd.rdAR) :
    "af" ++ "@" ++ "Z" ∈ (tableAsks y rd g).map (·.name) ∧
    "qa" ++ "@" ++ "Z" ∈ (tableAsks y rd g).map (·.name) ∧
    "xbI" ++ "@" ++ "Z" ∈ (tableAsks y rd g).map (·.name) ∧
    "xbO" ++ "@" ++ "Z" ∈ (tableAsks y rd g).map (·.name) ∧
    "ad" ++ "@" ++ "zt" ∈ (tableAsks y rd g).map (·.name) ∧
    "ar" ++ "@" ++ "zt" ∈ (tableAsks y rd g).map (·.name) := by
  rw [tableAsks_names]
  have m : ∀ (mn p : String) (l : List String), p ∈ l →
      mn ++ "@" ++ p ∈ l.map (fun n => mn ++ "@" ++ n) :=
    fun mn p l h => List.mem_map.mpr ⟨p, h, rfl⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_left _ (m _ _ _ hAF))))))))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_right _ (m _ _ _ hQA))))))))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (m _ _ _ hXI)))))))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ (m _ _ _ hXO)))))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (m _ _ _ hAD))))
  · exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (m _ _ _ hAR)))

/-- The record Tabs holds of the world, for any cells and any point, if the verifier's list of
families is what layTables returns for the families of its group, and each matrix is read at the
lookup's point. -/
theorem tabs_of_layTables {K : Type} [Field K] (ρ : Reading K) (v : Env) (mats : Array (ℕ × ℕ))
    (rd : Reads) {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hl : layTables mats (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    (hAF : "Z" ∈ rd.rdAF) (hQA : "Z" ∈ rd.rdQA) (hXI : "Z" ∈ rd.rdXI) (hXO : "Z" ∈ rd.rdXO)
    (hAD : "zt" ∈ rd.rdAD) (hAR : "zt" ∈ rd.rdAR) (lT : ℕ) (c : Cells K) (low u : ℕ → K) :
    Tabs ρ (worldOf v.iU3 v.K3 v.tab (meanOf v.y.ls lT c low u)) v lT c low u := by
  obtain ⟨c1, c2⟩ := layTables_chain mats _ 0 r hl
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := six_names v.y rd v.g hAF hQA hXI hXO hAD hAR
  rw [← c2, ← ht] at n1 n2 n3 n4 n5 n6
  rw [← ht] at c1
  exact tabs_of_chain ρ v c1 lT c low u n1 n2 n3 n4 n5 n6

/-! ## Which matrices are read at the lookup's point -/

/-- True if the form of some segment of some call reads, at the lookup's point, the matrix with the
letter ch (readsZ in OnBytes/Model/LayerLayout.lean). -/
def anyZ (y : Lay) (ch : Char) : Bool :=
  (y.calls.toList.map fun c => c.segs.flatMap fun s => readsZ y.h.p4 s.name).any (·.contains ch)

/-- If a test and what follows it return a value, what follows it returns that value. -/
theorem refuse_bind {α : Type} {b : Bool} {name : String} {k : Except String α} {r : α}
    (h : (do refuseIf b name; k) = .ok r) : k = .ok r := by
  cases b with
  | true => cases h
  | false => exact h

/-- The lists of points that readsOf returns have the lookup's point for each matrix that some
segment's form reads there. -/
theorem readsOf_points {y : Lay} {rd : Reads} (h : readsOf y = .ok rd) :
    (anyZ y 'f' = true → "Z" ∈ rd.rdAF) ∧ (anyZ y 'q' = true → "Z" ∈ rd.rdQA) ∧
    (anyZ y 'i' = true → "Z" ∈ rd.rdXI) ∧ (anyZ y 'o' = true → "Z" ∈ rd.rdXO) ∧
    (anyZ y 'd' = true → "zt" ∈ rd.rdAD) ∧ (anyZ y 'r' = true → "zt" ∈ rd.rdAR) := by
  unfold readsOf at h
  have h2 := refuse_bind h
  have e := (Except.ok.inj h2).symm
  subst e
  have m : ∀ (ch : Char) (p : String), anyZ y ch = true →
      p ∈ (if anyZ y ch = true then [p] else []) := by
    intro ch p ha
    rw [if_pos ha]
    exact List.mem_singleton.mpr rfl
  refine ⟨fun ha => ?_, fun ha => ?_, fun ha => ?_, fun ha => ?_, fun ha => ?_, fun ha => ?_⟩
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (m 'f' "Z" ha)))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (m 'q' "Z" ha)))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (m 'i' "Z" ha)))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (m 'o' "Z" ha)))
  · exact List.mem_append_left _ (List.mem_append_left _ (m 'd' "zt" ha))
  · exact List.mem_append_left _ (List.mem_append_left _ (m 'r' "zt" ha))

/-- Some call of the layout has a segment with the name n. -/
def HasSeg (y : Lay) (n : String) : Prop := ∃ c ∈ y.calls.toList, ∃ s ∈ c.segs, s.name = n

/-- A matrix is read at the lookup's point if a segment is there whose form reads it. -/
theorem anyZ_of_seg {y : Lay} {n : String} (hs : HasSeg y n) {ch : Char}
    (hch : ch ∈ readsZ y.h.p4 n) : anyZ y ch = true := by
  obtain ⟨c, hc, s, hs, rfl⟩ := hs
  have hm : ch ∈ c.segs.flatMap fun s => readsZ y.h.p4 s.name :=
    List.mem_flatMap.mpr ⟨s, hs, hch⟩
  unfold anyZ
  rw [List.any_eq_true]
  exact ⟨_, List.mem_map.mpr ⟨c, hc, rfl⟩, by simpa using hm⟩

/-- With the segments CN1, CV, O, D and ROW in its calls, a layout has all six families. -/
theorem points_of_segs {y : Lay} {rd : Reads} (h : readsOf y = .ok rd) (s1 : HasSeg y "CN1")
    (s2 : HasSeg y "CV") (s3 : HasSeg y "O") (s4 : HasSeg y "D") (s5 : HasSeg y "ROW") :
    "Z" ∈ rd.rdAF ∧ "Z" ∈ rd.rdQA ∧ "Z" ∈ rd.rdXI ∧ "Z" ∈ rd.rdXO ∧ "zt" ∈ rd.rdAD ∧
      "zt" ∈ rd.rdAR := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := readsOf_points h
  exact ⟨p1 (anyZ_of_seg s1 (by simp [readsZ])), p2 (anyZ_of_seg s2 (by simp [readsZ])),
    p3 (anyZ_of_seg s3 (by cases y.h.p4 <;> simp [readsZ])),
    p4 (anyZ_of_seg s4 (by simp [readsZ])), p5 (anyZ_of_seg s1 (by simp [readsZ])),
    p6 (anyZ_of_seg s5 (by simp [readsZ]))⟩

/-! ## The calls take every segment -/

/-- If two steps that may refuse return a value, so does the first, and the second on its value. -/
theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- A name that takeSegments returns as taken was taken before or is the name of a segment that it
returns. -/
theorem takeSegments_seen (sd : List (String × String × ℕ × Bool)) (kind : String) :
    ∀ (ns seen : List String) (r : List SegAsk × List String),
      takeSegments sd kind ns seen = .ok r → ∀ n ∈ r.2, n ∈ seen ∨ n ∈ r.1.map (·.1)
  | [], seen, r, h, n, hn => by
    have e : r = ([], seen) := (Except.ok.inj h).symm
    subst e
    exact Or.inl hn
  | n0 :: ns, seen, r, h, n, hn => by
    unfold takeSegments at h
    cases hf : sd.find? (fun s => s.1 == n0) with
    | none =>
      rw [hf] at h
      cases h
    | some s =>
      rw [hf] at h
      have h1 := refuse_bind h
      obtain ⟨r', h2, h3⟩ := except_bind_ok h1
      have e : r = ((s.1, s.2.2.1, s.2.2.2) :: r'.1, r'.2) := (Except.ok.inj h3).symm
      subst e
      have hs : s.1 = n0 := by simpa using List.find?_some hf
      rcases takeSegments_seen sd kind ns (n0 :: seen) r' h2 n hn with h4 | h4
      · rcases List.mem_cons.mp h4 with e | h5
        · right
          show n ∈ s.1 :: r'.1.map (·.1)
          rw [e, hs]
          exact List.mem_cons_self
        · exact Or.inl h5
      · right
        exact List.mem_cons_of_mem _ h4

/-- A name that takeCalls returns as taken was taken before or is the name of a segment of a call
that it returns. -/
theorem takeCalls_seen (sd : List (String × String × ℕ × Bool)) :
    ∀ (lines : List (List String)) (names seen : List String)
      (r : List (String × String × List SegAsk) × List String),
      takeCalls sd lines names seen = .ok r →
      ∀ n ∈ r.2, n ∈ seen ∨ ∃ c ∈ r.1, n ∈ c.2.2.map (·.1)
  | [], _, seen, r, h, n, hn => by
    have e : r = ([], seen) := (Except.ok.inj h).symm
    subst e
    exact Or.inl hn
  | [] :: _, _, _, _, h, _, _ => by cases h
  | [_] :: _, _, _, _, h, _, _ => by cases h
  | [_, _] :: _, _, _, _, h, _, _ => by cases h
  | (name :: kind :: s :: more) :: rest, names, seen, r, h, n, hn => by
    have h0 : (do
        refuseIf (names.contains name) "policy-call-list"
        refuseIf (["V", "a", "b", "E"].contains name) "policy-call-list"
        let a ← takeSegments sd kind (s :: more) seen
        let r ← takeCalls sd rest (name :: names) a.2
        pure ((name, kind, a.1) :: r.1, r.2)) = Except.ok r := h
    have h1 := refuse_bind (refuse_bind h0)
    obtain ⟨a, h2, h3⟩ := except_bind_ok h1
    obtain ⟨r', h4, h5⟩ := except_bind_ok h3
    have e : r = ((name, kind, a.1) :: r'.1, r'.2) := (Except.ok.inj h5).symm
    subst e
    rcases takeCalls_seen sd rest (name :: names) a.2 r' h4 n hn with h6 | ⟨c, hc, hn'⟩
    · rcases takeSegments_seen sd kind (s :: more) seen a h2 n h6 with h7 | h7
      · exact Or.inl h7
      · exact Or.inr ⟨(name, kind, a.1), List.mem_cons_self, h7⟩
    · exact Or.inr ⟨c, List.mem_cons_of_mem _ hc, hn'⟩

/-- A member of a list is there with some number. -/
theorem exists_zipIdx {α : Type} : ∀ (l : List α) (k : ℕ) (a : α), a ∈ l →
    ∃ i, (a, i) ∈ l.zipIdx k
  | [], _, _, h => by simp at h
  | x :: l, k, a, h => by
    rw [List.zipIdx_cons]
    rcases List.mem_cons.mp h with e | h
    · subst e
      exact ⟨k, List.mem_cons_self⟩
    · obtain ⟨i, hi⟩ := exists_zipIdx l (k + 1) a h
      exact ⟨i, List.mem_cons_of_mem _ hi⟩

/-- Three lines of layoutBase (OnBytes/Model/LayerLayout.lean) as hypotheses: the calls are read by
takeCalls from nothing taken; the test that every present segment is taken has passed; the layout's
calls are the calls that were read, placed. Then every present segment is a segment of some call. -/
theorem hasSeg_of_taken {y : Lay} {sd : List (String × String × ℕ × Bool)}
    {cl : List (List String)} {taken : List (String × String × List SegAsk) × List String}
    {fl : ℕ} (ht : takeCalls sd cl [] [] = .ok taken)
    (hall : (sd.any fun s => !taken.2.contains s.1) = false)
    (hcalls : y.calls = (taken.1.map fun c => place c.1 c.2.1 c.2.2 fl).toArray) :
    ∀ s ∈ sd, HasSeg y s.1 := by
  intro s hs
  have hin : s.1 ∈ taken.2 := by
    by_contra hc
    have ha : (sd.any fun s => !taken.2.contains s.1) = true :=
      List.any_eq_true.mpr ⟨s, hs, by simpa using hc⟩
    rw [hall] at ha
    cases ha
  rcases takeCalls_seen sd cl [] [] taken ht s.1 hin with h | ⟨c, hc, hn⟩
  · simp at h
  · obtain ⟨a, ha, hna⟩ := List.mem_map.mp hn
    obtain ⟨i, hi⟩ := exists_zipIdx c.2.2 0 a ha
    have hmem : place c.1 c.2.1 c.2.2 fl ∈ y.calls.toList := by
      rw [hcalls]
      exact List.mem_map.mpr ⟨c, hc, rfl⟩
    exact ⟨_, hmem, _, (List.mem_map.mpr ⟨(a, i), hi, rfl⟩ :
      _ ∈ (place c.1 c.2.1 c.2.2 fl).segs), hna⟩

/-- The same three lines, with the list of present segments that layoutBase uses: the calls have the
five segments that points_of_segs asks for. -/
theorem five_segs {y : Lay} {nqk dkv : ℕ} {cl : List (List String)}
    {taken : List (String × String × List SegAsk) × List String} {fl : ℕ}
    (ht : takeCalls (segmentList y.h nqk dkv) cl [] [] = .ok taken)
    (hall : ((segmentList y.h nqk dkv).any fun s => !taken.2.contains s.1) = false)
    (hcalls : y.calls = (taken.1.map fun c => place c.1 c.2.1 c.2.2 fl).toArray) :
    HasSeg y "CN1" ∧ HasSeg y "CV" ∧ HasSeg y "O" ∧ HasSeg y "D" ∧ HasSeg y "ROW" := by
  have H := hasSeg_of_taken ht hall hcalls
  exact ⟨H ("CN1", "FC", y.h.d, false) (by simp [segmentList]),
    H ("CV", "FC", dkv, false) (by simp [segmentList]),
    H ("O", "R16", y.h.d, false) (by simp [segmentList]),
    H ("D", "R16", y.h.d, false) (by simp [segmentList]),
    H ("ROW", "R8", Model.ledNR y.h.xl * 2, false) (by simp [segmentList])⟩

/-- The six families are found if the verifier's list of families is what layTables returns for the
families of its group, with the points that readsOf returns for its layout, and the layout's calls
have the segments CN1, CV, O, D and ROW. No world is spoken of. -/
theorem found_of_reads (v : Env) (mats : Array (ℕ × ℕ)) {rd : Reads} (hrd : readsOf v.y = .ok rd)
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hl : layTables mats (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    (s1 : HasSeg v.y "CN1") (s2 : HasSeg v.y "CV") (s3 : HasSeg v.y "O") (s4 : HasSeg v.y "D")
    (s5 : HasSeg v.y "ROW") : Found v := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := points_of_segs hrd s1 s2 s3 s4 s5
  obtain ⟨_, c2⟩ := layTables_chain mats _ 0 r hl
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := six_names v.y rd v.g p1 p2 p3 p4 p5 p6
  rw [← c2, ← ht] at n1 n2 n3 n4 n5 n6
  exact found_of_names v n1 n2 n3 n4 n5 n6

/-- The entries of the six families are true in the world, for any cells and any point, if the
verifier's list of families is what layTables returns. -/
theorem trueAt_of_layTables {K : Type} [Field K] (ρ : Reading K) (v : Env) (mats : Array (ℕ × ℕ))
    (asks : List TableAsk) {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hl : layTables mats asks 0 = some r) (ht : v.tab = r.1) (lT : ℕ) (c : Cells K)
    (low u : ℕ → K) :
    TrueAt ρ (worldOf v.iU3 v.K3 v.tab (meanOf v.y.ls lT c low u)) v lT c low u := by
  obtain ⟨c1, _⟩ := layTables_chain mats _ 0 r hl
  rw [← ht] at c1
  exact trueAt_of_chain ρ v c1 lT c low u

/-- The record Tabs holds of the world, for any cells and any point, if the verifier's list of
families is what layTables returns for the families of its group, with the points that readsOf
returns for its layout, and the layout's calls have the segments CN1, CV, O, D and ROW. -/
theorem tabs_of_reads {K : Type} [Field K] (ρ : Reading K) (v : Env) (mats : Array (ℕ × ℕ))
    {rd : Reads} (hrd : readsOf v.y = .ok rd)
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hl : layTables mats (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    (s1 : HasSeg v.y "CN1") (s2 : HasSeg v.y "CV") (s3 : HasSeg v.y "O") (s4 : HasSeg v.y "D")
    (s5 : HasSeg v.y "ROW") (lT : ℕ) (c : Cells K) (low u : ℕ → K) :
    Tabs ρ (worldOf v.iU3 v.K3 v.tab (meanOf v.y.ls lT c low u)) v lT c low u := by
  obtain ⟨p1, p2, p3, p4, p5, p6⟩ := points_of_segs hrd s1 s2 s3 s4 s5
  exact tabs_of_layTables ρ v mats rd hl ht p1 p2 p3 p4 p5 p6 lT c low u

#print axioms layTables_chain
#print axioms tabs_of_chain
#print axioms tabs_of_layTables
#print axioms found_of_reads
#print axioms trueAt_of_layTables
#print axioms tabs_of_reads
#print axioms five_segs

end OnBytes.Road
