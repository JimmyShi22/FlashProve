-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysMet.lean: the hypothesis Holds can be met at any matrices.

The theorem trueAt_of_holds (Johnson/Road/FormsKeysTrue.lean) begins "if every table of the
verifier's list holds in the world W what it says of the matrices M" (Holds,
Johnson/Road/FormsKeysMat.lean). This file shows that such a world exists for every M: the
world in which each place of the reads holds the sum that the table which owns the place says. That
is the honest prover's direction, and it is true by construction. What has to be shown is that no
place is owned twice.
What is compared with what: two texts of the verifier, layParts, layTables and funsOf
(OnBytes/Model/LayerForms.lean, OnBytes/Model/Layer.lean) with tabAt (OnBytes/Model/Tail.lean). The
library is not mentioned.
Main definitions: flatLaid, widthOf, Tiles (the tables lie one behind the other), Apart, saysOf.
Main theorems: tiles_layTables; funsOf_inv; apart_of_run; holds_of_apart; holds_met; trueAt_met.
holds_met speaks of every table of the verifier's list: those of all families at all points, and
the three on the matrix of counts. It asks neither for the switches nor for a layout, and holds for
any number K3 of columns of the array of reads, 0 too.
The hypotheses of holds_met, and where they are met: hl and hfun, the verifier's lines that lay the
tables and make the list, return together at made-up numbers (the guard on runR8 hR8 in
Johnson/Road/FormsKeysRun8.lean, a run, with the sizes of tailsOf); hNM and the sizes in hl are met
by the record with the list of matrices of tailsOf and its length. For the records that the
verifier's own plans build they are theorems: plan_sizes, Johnson/Road/FormsKeysPlan.lean. The
hypotheses of trueAt_met are those of trueAt_of_holds without the one on the world.

What is not claimed. The verifier never tests Holds; how its random combinations lead there is not
looked at. The world of holds_met is made for the matrices; nothing is said of other worlds. The
program does not import this file.
-/
import Johnson.Road.FormsKeysTrue

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World HFun HTailF2 Level lastOf)
open OnBytes.Model.Layer (Env Lay Shape Reads Heard TableAsk TableAt layParts layTables tableAsks
  layout readsOf pointsOf phiOf funsOf)

/-! ## The tables lie one behind the other -/

/-- The tables that layTables has laid, one after the other: the family that was asked for, the
matrix's number in the list, and the table's first entry. -/
def flatLaid (laid : List (TableAsk × List (ℕ × ℕ))) : List (TableAsk × ℕ × ℕ) :=
  laid.flatMap fun q => q.2.map fun m => (q.1, m)

/-- The number of entries of a table: one for each column and each run of rows of its matrix. mats:
the rows and the columns of each matrix. -/
def widthOf (mats : Array (ℕ × ℕ)) (t : TableAsk × ℕ × ℕ) : ℕ :=
  (mats.getD t.2.1 (0, 0)).2 * ((mats.getD t.2.1 (0, 0)).1 / t.1.L)

/-- The tables of a list lie one behind the other, without a gap, from entry p up to entry e. -/
def Tiles (mats : Array (ℕ × ℕ)) : List (TableAsk × ℕ × ℕ) → ℕ → ℕ → Prop
  | [], p, e => p = e
  | t :: l, p, e => t.2.2 = p ∧ Tiles mats l (p + widthOf mats t) e

/-- Two such lists, the second from where the first ends, make one. -/
theorem tiles_append (mats : Array (ℕ × ℕ)) : ∀ (l1 l2 : List (TableAsk × ℕ × ℕ)) (p e e' : ℕ),
    Tiles mats l1 p e → Tiles mats l2 e e' → Tiles mats (l1 ++ l2) p e'
  | [], l2, p, e, e', h1, h2 => by
    have h : p = e := h1
    subst h
    exact h2
  | t :: l1, l2, p, e, e', h1, h2 =>
    ⟨h1.1, tiles_append mats l1 l2 _ e e' h1.2 h2⟩

/-- No table of such a list begins before the list. -/
theorem tiles_ge (mats : Array (ℕ × ℕ)) : ∀ (l : List (TableAsk × ℕ × ℕ)) (p e : ℕ),
    Tiles mats l p e → ∀ t ∈ l, p ≤ t.2.2
  | [], _, _, _, t, ht => by cases ht
  | x :: l, p, e, h, t, ht => by
    rcases List.mem_cons.mp ht with rfl | ht
    · exact Nat.le_of_eq h.1.symm
    · have := tiles_ge mats l _ e h.2 t ht
      omega

/-- Two tables of such a list that share an entry are one. -/
theorem tiles_apart (mats : Array (ℕ × ℕ)) : ∀ (l : List (TableAsk × ℕ × ℕ)) (p e : ℕ),
    Tiles mats l p e → ∀ t ∈ l, ∀ t' ∈ l, ∀ pos, t.2.2 ≤ pos → pos < t.2.2 + widthOf mats t →
      t'.2.2 ≤ pos → pos < t'.2.2 + widthOf mats t' → t = t'
  | [], _, _, _, t, ht, _, _, _, _, _, _, _ => by cases ht
  | x :: l, p, e, h, t, ht, t', ht', pos, a1, a2, b1, b2 => by
    have hx : x.2.2 = p := h.1
    rcases List.mem_cons.mp ht with e1 | ht
    · rcases List.mem_cons.mp ht' with e2 | ht'
      · rw [e1, e2]
      · have := tiles_ge mats l _ e h.2 t' ht'
        subst e1
        omega
    · rcases List.mem_cons.mp ht' with e2 | ht'
      · have := tiles_ge mats l _ e h.2 t ht
        subst e2
        omega
      · exact tiles_apart mats l _ e h.2 t ht t' ht' pos a1 a2 b1 b2

/-- The parts of a family lie one behind the other. -/
theorem tiles_layParts (mats : Array (ℕ × ℕ)) (a : TableAsk) : ∀ (n p : ℕ),
    Tiles mats ((layParts mats a n p).1.map fun m => (a, m)) p (layParts mats a n p).2
  | 0, _ => rfl
  | n + 1, p => by
    rw [layParts_succ]
    exact ⟨rfl, tiles_layParts mats a n _⟩

/-- All tables that layTables has laid lie one behind the other, from the entry at which it began up
to the first free entry that it returns. -/
theorem tiles_layTables (mats : Array (ℕ × ℕ)) : ∀ (asks : List TableAsk) (p : ℕ)
    (r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ), layTables mats asks p = some r →
    Tiles mats (flatLaid r.2.1) p r.2.2
  | [], p, r, h => by
    have e : r = ([], [], p) := by simpa [layTables] using h.symm
    subst e
    rfl
  | a :: rest, p, r, h => by
    have h' : (if ((layParts mats a a.parts p).2 == p) = true then none else
        (layTables mats rest (layParts mats a a.parts p).2).map fun r =>
          ((⟨a.name, p, (layParts mats a a.parts p).2 - p⟩ : TableAt) :: r.1,
            (a, (layParts mats a a.parts p).1) :: r.2.1, r.2.2)) = some r := h
    by_cases hq : ((layParts mats a a.parts p).2 == p) = true
    · rw [if_pos hq] at h'
      cases h'
    · rw [if_neg hq] at h'
      obtain ⟨r', h1, h2⟩ := map_some h'
      subst h2
      show Tiles mats (flatLaid ((a, (layParts mats a a.parts p).1) :: r'.2.1)) p r'.2.2
      unfold flatLaid
      rw [List.flatMap_cons]
      exact tiles_append mats _ _ p _ _ (tiles_layParts mats a a.parts p)
        (tiles_layTables mats rest _ r' h1)

/-! ## The verifier's list of tables -/

/-- Every table of the verifier's list is the table of a part that was laid, with the weights of the
part's family. -/
theorem funsOf_inv {y : Lay} {fo : Model.Forest.Heard} {pts : List (String × Array E)}
    {laid : List (TableAsk × List (ℕ × ℕ))} {funs : Array HFun}
    (h : funsOf y fo pts laid = some funs) {Fn : HFun} (hF : Fn ∈ funs) :
    ∃ t ∈ flatLaid laid, ∃ phi, phiOf y fo pts t.1 = some phi ∧
      Fn = { mat := t.2.1, len := t.1.L, phi := phi, tree := 2, start := t.2.2 } := by
  unfold funsOf at h
  obtain ⟨l, hl, h⟩ := bind_some h
  have e := Option.some.inj h
  subst e
  have hF' : Fn ∈ l.flatten := by simpa using hF
  obtain ⟨L, hL, hFL⟩ := List.mem_flatten.mp hF'
  obtain ⟨hlen, hi⟩ := list_mapM_some _ _ _ hl
  obtain ⟨i, hiL⟩ := List.getElem?_of_mem hL
  have hil : i < laid.length := by
    rw [← hlen]
    exact (List.getElem?_eq_some_iff.mp hiL).1
  obtain ⟨b, hb, hf⟩ := hi i laid[i] (List.getElem?_eq_getElem hil)
  have eb : b = L := Option.some.inj (hb.symm.trans hiL)
  subst eb
  obtain ⟨phi, hphi, hf⟩ := bind_some hf
  have e2 := Option.some.inj hf
  subst e2
  obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hFL
  exact ⟨(laid[i].1, m), List.mem_flatMap.mpr ⟨laid[i], List.getElem_mem hil,
    List.mem_map.mpr ⟨m, hm, rfl⟩⟩, phi, hphi, rfl⟩

/-- No place of the reads belongs to two tables, or twice to one: if the smallness test has one
place for column c, run sg of a table of the list and for column c', run sg' of a table of the list,
the tables, the columns and the runs are the same. -/
def Apart (tl : HTailF2) (funs : Array HFun) : Prop :=
  ∀ Fn ∈ funs, ∀ Fn' ∈ funs, ∀ c sg c' sg' pos, tl.tabAt Fn c sg = some pos →
    tl.tabAt Fn' c' sg' = some pos → Fn = Fn' ∧ c = c' ∧ sg = sg'

/-- The verifier's list of tables is apart. Asked: layTables has laid the tables from the rows and
columns of the smallness test's own list of matrices, funsOf has made the list funs from what was
laid, and NM is the length of the list of matrices. -/
theorem apart_of_run {y : Lay} {fo : Model.Forest.Heard} {pts : List (String × Array E)}
    {tl : HTailF2} {asks : List TableAsk} {p0 : ℕ}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {funs : Array HFun}
    (hl : layTables (tl.mats.map fun M => (M.m, M.k)) asks p0 = some r)
    (hfun : funsOf y fo pts r.2.1 = some funs) (hNM : tl.NM = tl.mats.size) : Apart tl funs := by
  have T := tiles_layTables _ asks p0 r hl
  have iv : ∀ (t : TableAsk × ℕ × ℕ) (phi : Array E) (c sg pos : ℕ),
      tl.tabAt { mat := t.2.1, len := t.1.L, phi := phi, tree := 2, start := t.2.2 } c sg =
        some pos →
      t.2.2 ≤ pos ∧ pos < t.2.2 + widthOf (tl.mats.map fun M => (M.m, M.k)) t ∧
        sg < (tl.mats.getD t.2.1 {}).m / t.1.L ∧
        pos = t.2.2 + (c * ((tl.mats.getD t.2.1 {}).m / t.1.L) + sg) := by
    intro t phi c sg pos h
    obtain ⟨h1, -, h3, h4, h5⟩ := tailAt_inv tl _ h
    have h1' : t.2.1 < tl.mats.size := by
      rw [← hNM]
      exact h1
    have h3' : c < (tl.mats.getD t.2.1 {}).k := h3
    have h4' : sg < (tl.mats.getD t.2.1 {}).m / t.1.L := h4
    have h5' : pos = t.2.2 + c * ((tl.mats.getD t.2.1 {}).m / t.1.L) + sg := h5
    have w : widthOf (tl.mats.map fun M => (M.m, M.k)) t =
        (tl.mats.getD t.2.1 {}).k * ((tl.mats.getD t.2.1 {}).m / t.1.L) := by
      unfold widthOf
      rw [getD_map_sizes _ h1']
    rw [w]
    generalize (tl.mats.getD t.2.1 {}).m / t.1.L = n at h4' h5' ⊢
    generalize (tl.mats.getD t.2.1 {}).k = k at h3' ⊢
    have h6 := Nat.mul_le_mul_right n (Nat.succ_le_of_lt h3')
    rw [Nat.succ_mul] at h6
    refine ⟨by omega, by omega, h4', by omega⟩
  intro Fn hF Fn' hF' c sg c' sg' pos h h'
  obtain ⟨t, ht, phi, hphi, rfl⟩ := funsOf_inv hfun hF
  obtain ⟨t', ht', phi', hphi', rfl⟩ := funsOf_inv hfun hF'
  obtain ⟨a1, a2, a3, a4⟩ := iv t phi c sg pos h
  obtain ⟨b1, b2, b3, b4⟩ := iv t' phi' c' sg' pos h'
  have e : t = t' := tiles_apart _ _ p0 _ T t ht t' ht' pos a1 a2 b1 b2
  subst e
  have e2 : phi = phi' := Option.some.inj (hphi.symm.trans hphi')
  subst e2
  obtain ⟨e3, e4⟩ := layer_column a3 b3 (by omega : c * ((tl.mats.getD t.2.1 {}).m / t.1.L) + sg =
    c' * ((tl.mats.getD t.2.1 {}).m / t.1.L) + sg')
  exact ⟨rfl, e3, e4⟩

/-! ## A world for any matrices -/

section Met

variable {K : Type} [Field K] (ρ : Reading K)

/-- What the table Fn says that its entry for column c and run sg holds. -/
def saysOf (M : Mats K) (Fn : HFun) (c sg : ℕ) : K :=
  ∑ j ∈ range Fn.len, ρ.val (Fn.phi.getD j zeroE) * M Fn.mat (sg * Fn.len + j) c

/-- For a list of tables that is apart and any matrices M there is a world in which every table of
the list holds what it says of M: the place of the reads that the smallness test has for a column
and a run of a table holds that table's sum; every other hidden value is 0. -/
theorem holds_of_apart {tl : HTailF2} {funs : Array HFun} (hA : Apart tl funs) (iU3 K3 : ℕ)
    (M : Mats K) : ∃ W : World K, ∀ Fn ∈ funs, Holds ρ W tl iU3 K3 M Fn := by
  classical
  refine ⟨{ slot := fun _ => 0,
            entry := fun a r i => if a = iU3 then
              (if h : ∃ x : HFun × ℕ × ℕ, x.1 ∈ funs ∧ tl.tabAt x.1 x.2.1 x.2.2 = some (r * K3 + i)
               then saysOf ρ M h.choose.1 h.choose.2.1 h.choose.2.2 else 0) else 0 }, ?_⟩
  intro Fn hF c sg pos hpos
  show (if iU3 = iU3 then
    (if h : ∃ x : HFun × ℕ × ℕ, x.1 ∈ funs ∧
        tl.tabAt x.1 x.2.1 x.2.2 = some (pos / K3 * K3 + pos % K3)
     then saysOf ρ M h.choose.1 h.choose.2.1 h.choose.2.2 else 0) else 0) = saysOf ρ M Fn c sg
  rw [if_pos rfl, Nat.div_add_mod']
  have hex : ∃ x : HFun × ℕ × ℕ, x.1 ∈ funs ∧ tl.tabAt x.1 x.2.1 x.2.2 = some pos :=
    ⟨(Fn, c, sg), hF, hpos⟩
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  obtain ⟨e1, e2, e3⟩ := hA _ h1 _ hF _ _ _ _ _ h2 hpos
  rw [e1, e2, e3]

/-- Holds can be met at any matrices. On the verifier's lines that lay the tables and make the list
of tables, with the smallness test's own list of matrices: for any matrices M there is a world in
which every table of the verifier's list, those on the matrix of counts and those at all points
among them, holds what it says of M. -/
theorem holds_met {y : Lay} {fo : Model.Forest.Heard} {pts : List (String × Array E)}
    {tl : HTailF2} {asks : List TableAsk} {p0 : ℕ}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {funs : Array HFun}
    (hl : layTables (tl.mats.map fun M => (M.m, M.k)) asks p0 = some r)
    (hfun : funsOf y fo pts r.2.1 = some funs) (hNM : tl.NM = tl.mats.size) (iU3 K3 : ℕ)
    (M : Mats K) : ∃ W : World K, ∀ Fn ∈ funs, Holds ρ W tl iU3 K3 M Fn :=
  holds_of_apart ρ (apart_of_run hl hfun hNM) iU3 K3 M

/-- The hypothesis on the world under the theorems on the forms can be met at any matrices. Under
the hypotheses of trueAt_of_holds (Johnson/Road/FormsKeysTrue.lean) but the one on the world: for
any matrices M there is a world in which every table of the verifier's list holds what it says of M,
and in which the six families of tables are true, at the verifier's own point, of the cells that are
read in the entries of M. -/
theorem trueAt_met {h : Shape} {pc : List (List String)} {v : Env} {rd : Reads}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} (hy : layout h pc = .ok v.y)
    (S : Switches h) (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
    (hl : layTables (matsR v.y v.g) (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    {tl : HTailF2} (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR v.y v.g)
    (hNM : tl.NM = tl.mats.size) {H : Heard} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)}
    {funs : Array HFun} (hp : pointsOf v.y H hd hd2 = some pts)
    (hzt : lastOf H.fo.zx v.y.h.lt = .ok H.ztF) (hfun : funsOf v.y H.fo pts r.2.1 = some funs)
    (M : Mats K) :
    ∃ W : World K, (∀ Fn ∈ funs, Holds ρ W tl v.iU3 v.K3 M Fn) ∧
      ∃ Z, lastOf H.fo.zx v.y.h.la = .ok Z ∧
        TrueAt ρ W v v.y.h.lt (cellsAt v.y M) (pt ρ Z) (pt ρ H.ztF) := by
  have hl' : layTables (tl.mats.map fun M => (M.m, M.k)) (tableAsks v.y rd v.g) 0 = some r := by
    rw [htm]
    exact hl
  obtain ⟨W, hW⟩ := holds_met ρ hl' hfun hNM v.iU3 v.K3 M
  exact ⟨W, hW, trueAt_of_holds ρ W hy S hg hrd hl ht htm hNM hp hzt hfun M hW⟩

end Met

#print axioms tiles_layTables
#print axioms funsOf_inv
#print axioms apart_of_run
#print axioms holds_of_apart
#print axioms holds_met
#print axioms trueAt_met

end OnBytes.Road
