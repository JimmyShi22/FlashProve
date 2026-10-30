-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysTrue.lean: the one hypothesis on the world, as a conclusion.

The theorems on the forms of the lookup's segments and on the lookup's join ask one thing of the
world: TrueAt, the truth of six families of tables of the reads, of cells that are free there. Here
the cells are those that are read in the entries M of the sub-proof's matrices (cellsAt,
Johnson/Road/FormsKeysMat.lean; M is any function), and TrueAt follows from Holds: every table in
the verifier's own list of tables holds, entry by entry, what it says of its matrix.

What is compared with what: the verifier with itself: the numbering of a family's entries that its
forms use with the numbering of the smallness test, on the verifier's own layout, list of matrices,
points and list of tables.

The parts: Johnson/Road/FormsKeysTab.lean (how the two numberings meet: laid1_of_run),
Johnson/Road/FormsKeysHolds.lean (the sums), Johnson/Road/FormsKeysPoint.lean (TrueAt is a sum under
the verifier's own weights).

Main theorems: trueAt_of_holds; line_of_holds (what the form of a segment is worth, in cells read
in the matrices).

Hypotheses that no theorem concludes: the switches; that the verifier's functions return (layout,
scalesHeld, readsOf, layTables, pointsOf, funsOf, line: runs alone: on made-up numbers in
Johnson/Road/FormsKeysRun8.lean, on the two examples' own files in Johnson/Road/FormsKeysRunK.lean);
that the matrices of the smallness test's list have the rows and columns of those of tailsOf, and NM
is their number (htm, hNM: theorems on the verifier's own plans: plan_sizes,
Johnson/Road/FormsKeysPlan.lean; no theorem composes them with this file's); and Holds.

What is not claimed. The theorem adds no strength on the world: it is a renumbering: free matrices
and free cells are one freedom. M is tied to no commitment and to no order of messages. The verifier
never tests Holds: for each table and each run of rows it adds one claim, a random combination over
the columns; the step from these claims to Holds is not looked at; it must put in the matrices that
were committed before the points were drawn.
That the array and the number of columns by which the forms name an entry of the reads (iU3, K3) are
those by which the smallness test names it is not shown. The program does not import this file.
-/
import Johnson.Road.FormsKeysTab

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff HFun HTailF2 Level lastOf)
open OnBytes.Model.Layer (Env Lay Shape Reads Heard TableAsk TableAt layout scalesHeld readsOf
  layTables tableAsks pointsOf funsOf tailsOf)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Fam LW lin len present)

variable {K : Type} [Field K] {h : Shape} {pc : List (List String)} {v : Env} {rd : Reads}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- TrueAt as a conclusion. On the verifier's own layout, reads, places of the tables (laid from the
sizes of the matrices of tailsOf), points and list of tables funs, under the switches: if every
table of funs holds in the world W what it says of the matrices M, then the six families of tables
are true in W, at the verifier's own point, of the cells that are read in the entries of M. tl: the
smallness test's numbers, by which Holds places a table's entries; asked of it: its matrices have
the rows and columns of those of tailsOf (htm), and NM is their number (hNM). -/
theorem trueAt_of_holds (ρ : Reading K) (W : World K) (hy : layout h pc = .ok v.y) (S : Switches h)
    (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
    (hl : layTables (matsR v.y v.g) (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    {tl : HTailF2} (htm : tl.mats.map (fun M => (M.m, M.k)) = matsR v.y v.g)
    (hNM : tl.NM = tl.mats.size)
    {H : Heard} {hd : Level} {hd2 : Option Level} {pts : List (String × Array E)}
    {funs : Array HFun} (hp : pointsOf v.y H hd hd2 = some pts)
    (hzt : lastOf H.fo.zx v.y.h.lt = .ok H.ztF) (hfun : funsOf v.y H.fo pts r.2.1 = some funs)
    (M : Mats K) (Hd : ∀ Fn ∈ funs, Holds ρ W tl v.iU3 v.K3 M Fn) :
    ∃ Z, lastOf H.fo.zx v.y.h.la = .ok Z ∧
      TrueAt ρ W v v.y.h.lt (cellsAt v.y M) (pt ρ Z) (pt ρ H.ztF) := by
  obtain ⟨Z, hZ, hT, LL, LS⟩ := laid1_of_run ρ W hy S hg hrd hl ht htm hNM hp hzt hfun
  obtain ⟨Z', hZ', -, -, -, -, -, hiff⟩ := tables_of_run ρ hy S hrd hl ht hp hzt hfun
  have e : Z' = Z := by
    rw [hZ] at hZ'
    exact (Except.ok.inj hZ').symm
  subst e
  exact ⟨Z', hZ, (hiff W (cellsAt v.y M)).mpr (summed_of_holds Hd hT LL LS)⟩

/-- What the form of a segment is worth, in cells read in the entries of any matrices M. Under the
hypotheses of trueAt_of_holds, with scales that pass the verifier's test, a reading that takes
numerals to numbers and sizes that agree with the shape: for every family s, at a layer lam of the
group on which the family is present, with weights as Fits.line_lin asks them: if line returns a
form, the form is worth the weighted sum of the extensions, at the verifier's token point, of the
affine part of the library's keys, in the cells that the library's rule for a cell's feature finds
in the entries of M. -/
theorem line_of_holds {ρ : Reading K} (hρ : Numerals ρ) (W : World K)
    (hy : layout h pc = .ok v.y) (S : Switches h) (hs : scalesHeld h v.sc = .ok ())
    (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
    (hl : layTables (matsR v.y v.g) (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    {tl : HTailF2} (htm : tl.mats.map (fun M => (M.m, M.k)) = matsR v.y v.g)
    (hNM : tl.NM = tl.mats.size)
    {H : Heard} {hd : Level} {hd2 : Option Level} {pts : List (String × Array E)}
    {funs : Array HFun} (hp : pointsOf v.y H hd hd2 = some pts)
    (hzt : lastOf H.fo.zx v.y.h.lt = .ok H.ztF) (hfun : funsOf v.y H.fo pts r.2.1 = some funs)
    (M : Mats K) (Hd : ∀ Fn ∈ funs, Holds ρ W tl v.iU3 v.K3 M Fn) {D : Dim} (Z : Sized h D)
    (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (s : Fam) (lam : ℕ) (hlam : lam < 2 ^ h.ll)
    (hp' : present s lam = true) :
    ∃ Zp, lastOf H.fo.zx v.y.h.la = .ok Zp ∧ ∀ {ew wh : Array E}, ew.size = len D s →
      (byBlocks s = true → Wts ρ ew wh v.y.ls (pt ρ Zp) (len D s)) → ∀ {f : Aff},
      v.line (segName s) lam ew wh = some f →
      f.value ρ W = ∑ x ∈ range (len D s), ρ.val (ew.getD x zeroE) *
        Blocks.ext D.lT (fun i => lin (scl := sclOf h v.sc v.g v.y.Lam) D
          (cellsOf D (cellsAt v.y M)) tb L0 w s lam x i) (pt ρ H.ztF) := by
  obtain ⟨Zp, hZp, T⟩ := trueAt_of_holds ρ W hy S hg hrd hl ht htm hNM hp hzt hfun M Hd
  have e := (admitted_of_layout hy S.p3).shape
  rw [e] at T
  refine ⟨Zp, hZp, ?_⟩
  intro ew wh hsz hbl f hf
  exact line_of_layout_true hy S hs hg hrd hl ht hρ Z (cellsAt v.y M) (pt ρ Zp) (pt ρ H.ztF) T tb L0
    w s lam hlam hp' hsz hbl hf

#print axioms trueAt_of_holds
#print axioms line_of_holds

end OnBytes.Road
