-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysO.lean: the attention output o at profile 4: found, tied and true at the
lookup's token point.

The theorem panelO_spec (Johnson/Road/FormsKeysW.lean) sets the panel that the verifier appends for
the segment O at profile 4 against the library's panel Pan.O. It has a hypothesis of its own,
HasShort for the array o: the verifier finds the tensor "o" and the short tables of its matrix qa at
the token point, the library's names of the cells of o are tied to the tensor's places, and the
tables are true. The record Fits does not give it: Fits knows six families of tables, and o is read
from a seventh, "qa@zt". This file shows from what the hypothesis follows.

Main theorems.
 - hasShort_o: HasShort for o, from the plain facts on a layout (Laid), the switches, sizes that
   agree with the shape, profile 4, and the seventh family found and true.
 - readsOf_short_qa, name_short_qa, found_o: at profile 4 the seventh family is found, from the
   verifier's own lines (the layout, the switches, readsOf, layTables). No world is spoken of.
 - panelO_of_layout: the conclusion of panelO_spec from the seven lines of
   Johnson/Road/FormsKeysAdmit.lean, profile 4, and two hypotheses on the world W: the entries of
   the six families are true (TrueAt), and so are those of the seventh.
 - seven_true: the two hypotheses on the world can be met together, for any cells and any point: in
   the world worldO, which is built from the cells, all seven families are true by definition. (In
   the world worldAt of Johnson/Road/FormsKeysAdmit.lean the seventh family holds zeros.)

What is compared with what. As in panelO_spec: the verifier's panelA against the library's Pan.O. In
hasShort_o the verifier's place of a cell of o is compared with the library's rule (place_eq_feat in
Johnson/Road/FormsKeysFits.lean); found_o speaks of the verifier's functions alone; worldO and meanO
are definitions of this file.

A run. That the lines hold together at some shape with profile 4 is no theorem. The made-up shape hR
of Johnson/Road/FormsKeysRun.lean has profile 4 (p4R), and the "#guard" at the end evaluates the
verifier's functions on it: in both groups the family "qa@zt" and the tensor "o" with it are found.
A second "#guard" is a control: with the profile set to 3 no such family is found. What that file
says of its runs holds here too: hR is not a shape that the verifier has admitted.

What is not claimed. When the entries of a prover's reads are true is not looked at. Which point and
which weights the name "qa@zt" stands for in the verifier's list of tables is not shown. Nothing is
said of profile 3, of the B side of the panel, or of what a verifier's acceptance shows. The program
does not import this file.
-/
import Johnson.Road.FormsKeysAdmit
import Johnson.Road.FormsKeysW
import Johnson.Road.FormsKeysRun

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff)
open OnBytes.Model.Layer (Env Lay Shape Reads TableAsk TableAt layout scalesOf scalesHeld readsOf
  readsZ layTables tableAsks SBlk Panels PanelEnv panelA)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Pan Rd valU)

/-! ## The array o, from a layout's facts -/

/-- At profile 4 the array o is found, tied and true at the token point, if the short tables of qa
at that point are found and true. The library's names of the cells of o are read in the cells c by
the library's own rule (cellsOf). -/
theorem hasShort_o {K : Type} [Field K] {ρ : Reading K} {W : World K} {v : Env} (L : Laid v.y)
    (S : Switches v.y.h) {D : Dim} (Z : Sized v.y.h D) (h4 : v.y.h.p4 = true) (c : Cells K)
    (u : ℕ → K) {b : ℕ} (hb : v.tabAt ("qa" ++ "@" ++ "zt") = some b)
    (R : ShortTrue ρ W v b 3 v.y.h.lt c u) : HasShort ρ W v D c (cellsOf D c) u .o := by
  obtain ⟨ten, hT, hm, hn, _, _, _⟩ := ten_of L S .o (Or.inr ⟨rfl, h4⟩)
  have hm3 : ten.mat = 3 := hm
  refine ⟨ten, b, tensorAt_of hT (by rw [hm3]; exact hb),
    tied_cellsOf L S Z c (Or.inr ⟨rfl, h4⟩) hT hn, ?_⟩
  rw [hm3, Z.lT]
  exact R

/-! ## The seventh family is found -/

/-- The list of points of the short tables of qa that readsOf returns has the token point, if some
segment's form reads such a table there. -/
theorem readsOf_short_qa {y : Lay} {rd : Reads} (h : readsOf y = .ok rd)
    (ha : anyZ y 'Q' = true) : "zt" ∈ rd.rdQS := by
  unfold readsOf at h
  have h2 := refuse_bind h
  have e := (Except.ok.inj h2).symm
  subst e
  have m : "zt" ∈ (if anyZ y 'Q' = true then ["zt"] else []) := by
    rw [if_pos ha]
    exact List.mem_singleton.mpr rfl
  exact List.mem_append_left _ (List.mem_append_left _ m)

/-- At profile 4 the name "qa@zt" is asked for, if qa has a short table at the token point. -/
theorem name_short_qa (y : Lay) (rd : Reads) (g : ℕ) (h4 : y.h.p4 = true)
    (hQS : "zt" ∈ rd.rdQS) : "qa" ++ "@" ++ "zt" ∈ (tableAsks y rd g).map (·.name) := by
  rw [tableAsks_names, if_pos h4]
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨"zt", hQS, rfl⟩))

/-! ## A world in which all seven families are true -/

section TheWorld

variable {K : Type} [Field K]

/-- What entry j of the family with the name n stands for: as meanOf says for its six names, and for
"qa@zt" the sum of the cells of feature j of matrix qa at the token point. -/
def meanO (ls lt : ℕ) (c : Cells K) (low u : ℕ → K) (n : String) (j : ℕ) : K :=
  if n = "qa@zt" then shortAt lt c u 3 j else meanOf ls lt c low u n j

/-- The world in which the seven families of tables are true for the cells c at the point
(low | u). -/
def worldO (v : Env) (c : Cells K) (low u : ℕ → K) : World K :=
  worldOf v.iU3 v.K3 v.tab (meanO v.y.ls v.y.h.lt c low u)

end TheWorld

section Lines

/- The verifier's own lines, as in Johnson/Road/FormsKeysAdmit.lean, and profile 4. -/
variable {h : Shape} {pc : List (List String)} {v : Env} {rd : Reads} {mats : Array (ℕ × ℕ)}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
  (hy : layout h pc = .ok v.y) (S : Switches h) (hs : scalesHeld h v.sc = .ok ())
  (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
  (hl : layTables mats (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1) (h4 : h.p4 = true)

include hy S hrd hl ht h4 in
/-- At profile 4 the short tables of qa at the token point are found under their name. -/
theorem found_o : ∃ b, v.tabAt ("qa" ++ "@" ++ "zt") = some b := by
  have e := (admitted_of_layout hy S.p3).shape
  subst e
  have s3 : HasSeg v.y "O" := hasSeg_of_layout hy S .O
  have hQ := readsOf_short_qa hrd (anyZ_of_seg s3 (by rw [h4]; simp [readsZ]))
  obtain ⟨_, c2⟩ := layTables_chain mats _ 0 r hl
  have n := name_short_qa v.y rd v.g h4 hQ
  rw [← c2, ← ht] at n
  exact tabAt_some v n

include hy S hl ht in
/-- In the world worldO the entries of the six families are true, and so are the entries of the
short tables of qa at the token point: the two hypotheses of panelO_of_layout on the world (T, R)
can be met together, for any cells and any point. -/
theorem seven_true {K : Type} [Field K] (ρ : Reading K) (c : Cells K) (low u : ℕ → K) :
    TrueAt ρ (worldO v c low u) v h.lt c low u ∧
      ∀ b, v.tabAt ("qa" ++ "@" ++ "zt") = some b →
        ShortTrue ρ (worldO v c low u) v b 3 h.lt c u := by
  have e := (admitted_of_layout hy S.p3).shape
  subst e
  obtain ⟨c1, _⟩ := layTables_chain mats _ 0 r hl
  rw [← ht] at c1
  exact ⟨
    { af := fun _ hb => longTrue_world ρ v c1 _ _ c low u hb fun j => by simp [meanO, meanOf]
      qa := fun _ hb => longTrue_world ρ v c1 _ _ c low u hb fun j => by simp [meanO, meanOf]
      xi := fun _ hb => longTrue_world ρ v c1 _ _ c low u hb fun j => by simp [meanO, meanOf]
      xo := fun _ hb => longTrue_world ρ v c1 _ _ c low u hb fun j => by simp [meanO, meanOf]
      ad := fun _ hb => shortTrue_world ρ v c1 _ _ c u hb fun j => by simp [meanO, meanOf]
      ar := fun _ hb => shortTrue_world ρ v c1 _ _ c u hb fun j => by simp [meanO, meanOf] },
    fun _ hb => shortTrue_world ρ v c1 _ _ c u hb fun j => by simp [meanO]⟩

include hy S h4 in
/-- hasShort_o for the layout that layout returns. -/
theorem hasShort_o_of_layout {K : Type} [Field K] {ρ : Reading K} {W : World K} {D : Dim}
    (Z : Sized h D) (c : Cells K) (u : ℕ → K) {b : ℕ}
    (hb : v.tabAt ("qa" ++ "@" ++ "zt") = some b) (R : ShortTrue ρ W v b 3 h.lt c u) :
    HasShort ρ W v D c (cellsOf D c) u .o := by
  have A := admitted_of_layout hy S.p3
  have e := A.shape
  subst e
  exact hasShort_o A.laid S Z h4 c u hb R

include hy S hs hg hrd hl ht h4 in
/-- The panel that the verifier appends for the segment O at profile 4, against the library's panel
Pan.O: the conclusion of panelO_spec, from the verifier's own lines, in every world in which the
entries of the six families (T) and of the short tables of qa at the token point (R) are true. The
library's table of scales is sclOf of the verifier's scale file; its names of cells are read in the
cells c by the library's own rule (cellsOf). -/
theorem panelO_of_layout {K : Type} [Field K] {ρ : Reading K} (hρ : Numerals ρ) {D : Dim}
    (Z : Sized h D) {W : World K} (c : Cells K) (low u : ℕ → K)
    (T : TrueAt ρ W v h.lt c low u)
    (R : ∀ b, v.tabAt ("qa" ++ "@" ++ "zt") = some b → ShortTrue ρ W v b 3 h.lt c u)
    (p : PanelEnv) (hp : p.v = v) (ec : E) (el : Array E) (s : Panels) :
    letI : Scl := sclOf h v.sc v.g v.y.Lam
    ∃ b : SBlk, (panelA p ec el "O" s).bl = s.bl.push b ∧
      (panelA p ec el "O" s).nextV = s.nextV + v.y.Lam ∧
      b.tri = false ∧ b.claim = 0 ∧ b.ec = ec ∧ b.ni = Pan.O.nr D ∧ b.ny = Pan.O.nc D ∧
      b.v0 = some s.nextV ∧ b.virt = none ∧ b.B.isNone = true ∧
      (∃ A, b.A = some A ∧ ∀ (r : Rd K), (∀ l j, r.o1 l j = valU D (cellsOf D c) .o l j u) →
        ∀ lam k2 a, A lam k2 = some a → a.value ρ W = Pan.O.A D r lam k2) ∧
      ∀ lam, lam < v.y.Lam → ρ.val (b.wt.getD lam zeroE) =
        Inst.Model.Site.scl (D.Pl lam).ko (ρ.val (el.getD lam zeroE)) := by
  obtain ⟨b, hb⟩ := found_o hy S hrd hl ht h4
  have F := fits_of_layout_true hy S hs hg hrd hl ht hρ Z c low u T
  have ho := hasShort_o_of_layout (ρ := ρ) (W := W) hy S h4 Z c u hb (R b hb)
  have e := (admitted_of_layout hy S.p3).shape
  exact panelO_spec (scl := sclOf h v.sc v.g v.y.Lam) F (by rw [e]; exact h4) ho p hp ec el s

end Lines

/-! ## A run on made-up numbers -/

/-- The made-up shape of Johnson/Road/FormsKeysRun.lean has profile 4. -/
theorem p4R : hR.p4 = true := rfl

/- on that shape, in each of its groups: the short tables of qa at the token point are found, and so
is the tensor "o" with them -/
#guard (match layout hR pcR, scalesOf hR klR with
  | .ok y, .ok sc =>
    (match readsOf y with
    | .ok rd =>
      y.NGr == 2 && (List.range y.NGr).all fun g =>
        match envR y sc rd g with
        | some v => (v.tabAt ("qa" ++ "@" ++ "zt")).isSome && (v.tensorAt "o" "zt").isSome
        | none => false
    | .error _ => false)
  | _, _ => false)

/- a control: with the profile set to 3 the functions still return, and no family "qa@zt" is
found -/
#guard (match layout { hR with prof := 3 } pcR, scalesOf hR klR with
  | .ok y, .ok sc =>
    (match readsOf y with
    | .ok rd =>
      y.NGr == 2 && (List.range y.NGr).all fun g =>
        match envR y sc rd g with
        | some v => (v.tabAt ("qa" ++ "@" ++ "zt")).isNone
        | none => false
    | .error _ => false)
  | _, _ => false)

#print axioms hasShort_o
#print axioms found_o
#print axioms seven_true
#print axioms hasShort_o_of_layout
#print axioms panelO_of_layout
#print axioms p4R

end OnBytes.Road
