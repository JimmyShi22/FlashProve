-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysAdmit.lean: the record Fits holds of what the verifier itself computes, in
every world in which six families of tables are true.

Johnson/Road/FormsKeysKit.lean gathers in the record Fits all that the theorems on the forms of the
lookup's segments ask. This file shows from what the record follows. The hypotheses are lines of the
verifier's own run, in its own words: the layout that layout returns for the shape, the scales that
have passed scalesHeld, a group of the layout, the points that readsOf returns, the families of
tables as layTables has laid them; and the switches for which alone the library has keys (Switches).
The library's sizes D are any that agree with the shape (Sized); its table of scales and its names
of cells are defined in Johnson/Road/FormsKeysFits.lean (sclOf, cellsOf).

Each theorem comes in two forms.
 - The form with "true" in its name holds in any world W. It has one hypothesis on W: the entries of
   the six families are true in W at the point (low | u), for the cells c (TrueAt). This is the form
   for an argument on soundness, where the world is the prover's.
 - The form without holds in the world worldAt, which Johnson/Road/FormsKeysWorld.lean builds from
   the cells, and in which the entries are true by definition. It shows that the hypothesis on the
   world can be met for any cells and any point. An honest prover's reads are meant to be such a
   world; that they are is not shown.

Main theorems.
 - hasSeg_of_layout: every family has a segment in some call. (That every segment of a call holds a
   family is segs_of_layout in Johnson/Road/FormsKeysLaid.lean.)
 - points_of_layout, found_of_layout: each of the six matrices is read at the lookup's point, and
   the six families are found under their names. No world is spoken of.
 - fits_of_layout_true; fits_of_layout_any, fits_of_layout: the record Fits.
 - line_of_layout_true; line_of_layout: what the form of a segment is worth (Fits.line_lin). Left as
   hypotheses, beside the lines, the switches and the world's: the layer's number, that the family
   is present, the weights', and that line returns a form.
 - joinPart_of_layout_true; joinPart_of_layout: what one call's factor in the lookup's join is worth
   (Fits.joinPart_lin). What is asked of the call's segments follows from the layout. Left, beside
   that joinPart returns a form: two hypotheses on the call's point, which the lookup draws when the
   verifier runs (Johnson/Road/FormsKeysPoint.lean derives them from the verifier's tests). The
   number q is not tied to the call cd here.

What is not claimed. That there are a shape, calls, scales and matrices for which all these lines
hold together is no theorem: every theorem here begins "if they do". Each line is a computation on
public numbers, so a run of these functions decides it; Johnson/Road/FormsKeysRun.lean has such a
run, on made-up numbers. When the entries of a
prover's reads are true is not looked at. Nothing is said for other switches. See also
Johnson/Road/FormsKeysKit.lean. The program does not import this file.
-/
import Johnson.Road.FormsKeysLaid
import Johnson.Road.FormsKeysWorld
import Johnson.Road.FormsKeysCall

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff Seg CallD)
open OnBytes.Model.Layer (Env Shape Reads TableAsk TableAt layout scalesHeld readsOf layTables
  tableAsks)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Fam LW lin len present)

/-- The world in which the six families of tables that the forms of v read are true for the cells c
at the point (low | u). -/
def worldAt {K : Type} [Field K] (v : Env) (c : Cells K) (low u : ℕ → K) : World K :=
  worldOf v.iU3 v.K3 v.tab (meanOf v.y.ls v.y.h.lt c low u)

/-- A family has as many entries at sizes that agree with the shape as at dimOf. -/
theorem Sized.len_eq {h : Shape} {D : Dim} (Z : Sized h D) (s : Fam) :
    len D s = len (dimOf h) s := by
  cases s <;> simp only [len, Z.f_eq, Z.d_eq, Z.dqk_eq, Z.dkv_eq, Z.nx_eq]

section Lines

/- The verifier's own lines. v holds what the forms of one layer sub-proof depend on; its fields
iU3, K3 and zk are arbitrary. -/
variable {h : Shape} {pc : List (List String)} {v : Env} {rd : Reads} {mats : Array (ℕ × ℕ)}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
  (hy : layout h pc = .ok v.y) (S : Switches h) (hs : scalesHeld h v.sc = .ok ())
  (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
  (hl : layTables mats (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)

include hy S in
/-- Every one of the library's families has a segment in some call of the layout. -/
theorem hasSeg_of_layout (fam : Fam) : HasSeg v.y (segName fam) := by
  obtain ⟨cl, taken, h1, h2, h3⟩ := (admitted_of_layout hy S.p3).calls
  obtain ⟨q, hq, e⟩ := segmentList_has h S fam
  exact e ▸ hasSeg_of_taken h1 h2 h3 q hq

include hy S hrd in
/-- Each of the six matrices is read at the lookup's point. -/
theorem points_of_layout :
    "Z" ∈ rd.rdAF ∧ "Z" ∈ rd.rdQA ∧ "Z" ∈ rd.rdXI ∧ "Z" ∈ rd.rdXO ∧ "zt" ∈ rd.rdAD ∧
      "zt" ∈ rd.rdAR := by
  have A := admitted_of_layout hy S.p3
  obtain ⟨cl, taken, h1, h2, h3⟩ := A.calls
  have e := A.shape
  subst e
  obtain ⟨s1, s2, s3, s4, s5⟩ := five_segs h1 h2 h3
  exact points_of_segs hrd s1 s2 s3 s4 s5

include hy S hrd hl ht in
/-- The six families of tables that the forms read are found under their names. -/
theorem found_of_layout : Found v := by
  have A := admitted_of_layout hy S.p3
  obtain ⟨cl, taken, h1, h2, h3⟩ := A.calls
  have e := A.shape
  subst e
  obtain ⟨s1, s2, s3, s4, s5⟩ := five_segs h1 h2 h3
  exact found_of_reads v mats hrd hl ht s1 s2 s3 s4 s5

include hl ht in
/-- In the world worldAt the entries of the six families are true. -/
theorem trueAt_worldAt {K : Type} [Field K] (ρ : Reading K) (c : Cells K) (low u : ℕ → K) :
    TrueAt ρ (worldAt v c low u) v v.y.h.lt c low u :=
  trueAt_of_layTables ρ v mats _ hl ht v.y.h.lt c low u

include hy S hs hg hrd hl ht

/-! ## In any world with true tables -/

section AnyWorld

variable {K : Type} [Field K] {ρ : Reading K} (hρ : Numerals ρ) {D : Dim} (Z : Sized h D)
  {W : World K} (c : Cells K) (low u : ℕ → K) (T : TrueAt ρ W v h.lt c low u)
include hρ Z T

/-- The record Fits holds of the verifier's own layout, scales and tables, in every world in which
the entries of the six families are true, for any reading that takes numerals to numbers and any
sizes that agree with the shape. -/
theorem fits_of_layout_true :
    Fits (scl := sclOf h v.sc v.g v.y.Lam) ρ W v D c (cellsOf D c) low u := by
  have Fd := found_of_layout hy S hrd hl ht
  have A := admitted_of_layout hy S.p3
  have e := A.shape
  subst e
  exact fits_of_laid hρ v A.laid S (K_of_env v A hs hg) Z c low u (tabs_of Fd T)

/-- What the form of a segment is worth. For every family s, at a layer lam of the group on which
the family is present, with one weight for each entry and, if the segment is read by blocks, block
weights that are one set with them: if line returns a form, the form is worth the weighted sum of
the extensions of the affine part of the library's keys. -/
theorem line_of_layout_true (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (s : Fam) (lam : ℕ)
    (hlam : lam < 2 ^ h.ll) (hp : present s lam = true) {ew wh : Array E}
    (hsz : ew.size = len D s) (hbl : byBlocks s = true → Wts ρ ew wh v.y.ls low (len D s))
    {f : Aff} (hf : v.line (segName s) lam ew wh = some f) :
    f.value ρ W = ∑ x ∈ range (len D s), ρ.val (ew.getD x zeroE) *
      Blocks.ext D.lT (fun i => lin (scl := sclOf h v.sc v.g v.y.Lam) D (cellsOf D c)
        tb L0 w s lam x i) u :=
  Fits.line_lin (scl := sclOf h v.sc v.g v.y.Lam)
    (fits_of_layout_true hy S hs hg hrd hl ht hρ Z c low u T) tb L0 w s lam
    (by rw [Z.nl_eq]; exact hlam) hp hsz hbl hf

/-- What one call's factor in the lookup's join is worth. For a call cd of the layout, each of its
segments holds one of the library's families (fam), and if joinPart returns a form, the form is
worth alpha - q theta, less the padding key times the weight of the padding's columns, less, for
each segment and each layer on which it exists, the layer's weight times the weighted sum of the
extensions of the affine part of the keys of the segment's family. hzk, hlow: the two hypotheses on
the call's point. The number q, from which the point, the layers' weights and the padding key are
taken, is any number: that cd is call number q is not asked here. -/
theorem joinPart_of_layout_true (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (alpha theta : E) (q : ℕ)
    (cd : CallD) (hcd : cd ∈ v.y.calls) (weighed : Array Bool)
    (hzk : v.y.h.ll + cd.lJ ≤ (v.zk.getD q #[]).size)
    (hlow : ∀ j, j < v.y.ls → low j = pt ρ (v.zj q cd.lJ) (cd.lJ - v.y.ls + j))
    {f : Aff} (hf : v.joinPart alpha theta q cd weighed = some f) :
    ∃ fam : Seg → Fam, (∀ s ∈ cd.segs, SegFits v D cd.lJ s (fam s)) ∧
      f.value ρ W = ρ.val alpha - (q : K) * ρ.val theta -
        ρ.val (ofF ((v.y.cl.getD q {}).tauAt (v.y.cl.getD q {}).t0)) * padJ ρ v q cd weighed -
        (cd.segs.map fun s => ((List.range v.y.Lam).map fun lam =>
          if (s.moe && !v.isMoe lam) = true then 0
          else ρ.val (elJ v q lam) * ∑ x ∈ range (len D (fam s)),
            ρ.val ((ewJ v q cd s).getD x zeroE) *
              Blocks.ext D.lT (fun i => lin (scl := sclOf h v.sc v.g v.y.Lam) D (cellsOf D c)
                tb L0 w (fam s) lam x i) u).sum).sum := by
  have HS := segs_of_layout hy S cd hcd
  have HS' : ∀ s : Seg, ∃ fam : Fam, s ∈ cd.segs → SegFits v D cd.lJ s fam := by
    intro s
    by_cases hm : s ∈ cd.segs
    · obtain ⟨fam, a1, a2, a3, a4, a5⟩ := HS s hm
      exact ⟨fam, fun _ => ⟨a1, a2.trans (Z.len_eq fam).symm, a3, a4, a5⟩⟩
    · exact ⟨.G, fun hc => absurd hc hm⟩
  choose fam hfam using HS'
  exact ⟨fam, hfam, Fits.joinPart_lin (scl := sclOf h v.sc v.g v.y.Lam)
    (fits_of_layout_true hy S hs hg hrd hl ht hρ Z c low u T) tb L0 w alpha theta q cd weighed fam
    hfam hzk (lJ_of_layout hy cd hcd) hlow hf⟩

end AnyWorld

/-! ## In the world that is built from the cells -/

/-- The hypothesis on the world can be met: in the world worldAt the record Fits holds, for any
cells, any point, any reading that takes numerals to numbers and any sizes that agree with the
shape. -/
theorem fits_of_layout_any {K : Type} [Field K] {ρ : Reading K} (hρ : Numerals ρ) {D : Dim}
    (Z : Sized h D) (c : Cells K) (low u : ℕ → K) :
    Fits (scl := sclOf h v.sc v.g v.y.Lam) ρ (worldAt v c low u) v D c (cellsOf D c) low u := by
  refine fits_of_layout_true hy S hs hg hrd hl ht hρ Z c low u ?_
  have e := (admitted_of_layout hy S.p3).shape
  rw [← e]
  exact trueAt_worldAt hl ht ρ c low u

/-- The same for the reading in the library's field. -/
theorem fits_of_layout {D : Dim} (Z : Sized h D) (c : Cells Cb.Gl.E) (low u : ℕ → Cb.Gl.E) :
    Fits (scl := sclOf h v.sc v.g v.y.Lam) Reading.gl (worldAt v c low u) v D c (cellsOf D c)
      low u :=
  fits_of_layout_any hy S hs hg hrd hl ht gl_numerals Z c low u

/-- line_of_layout_true in the world worldAt, for the reading in the library's field. -/
theorem line_of_layout {D : Dim} (Z : Sized h D) (c : Cells Cb.Gl.E) (low u : ℕ → Cb.Gl.E)
    (tb : Tables) (L0 : ℕ) (w : ℕ → LW Cb.Gl.E) (s : Fam) (lam : ℕ) (hlam : lam < 2 ^ h.ll)
    (hp : present s lam = true) {ew wh : Array E} (hsz : ew.size = len D s)
    (hbl : byBlocks s = true → Wts Reading.gl ew wh v.y.ls low (len D s)) {f : Aff}
    (hf : v.line (segName s) lam ew wh = some f) :
    f.value Reading.gl (worldAt v c low u) =
      ∑ x ∈ range (len D s), Reading.gl.val (ew.getD x zeroE) *
        Blocks.ext D.lT (fun i => lin (scl := sclOf h v.sc v.g v.y.Lam) D (cellsOf D c)
          tb L0 w s lam x i) u :=
  Fits.line_lin (scl := sclOf h v.sc v.g v.y.Lam) (fits_of_layout hy S hs hg hrd hl ht Z c low u)
    tb L0 w s lam (by rw [Z.nl_eq]; exact hlam) hp hsz hbl hf

/-- joinPart_of_layout_true in the world worldAt, for the reading in the library's field. -/
theorem joinPart_of_layout {D : Dim} (Z : Sized h D) (c : Cells Cb.Gl.E) (low u : ℕ → Cb.Gl.E)
    (tb : Tables) (L0 : ℕ) (w : ℕ → LW Cb.Gl.E) (alpha theta : E) (q : ℕ) (cd : CallD)
    (hcd : cd ∈ v.y.calls) (weighed : Array Bool)
    (hzk : v.y.h.ll + cd.lJ ≤ (v.zk.getD q #[]).size)
    (hlow : ∀ j, j < v.y.ls → low j = pt Reading.gl (v.zj q cd.lJ) (cd.lJ - v.y.ls + j))
    {f : Aff} (hf : v.joinPart alpha theta q cd weighed = some f) :
    ∃ fam : Seg → Fam, (∀ s ∈ cd.segs, SegFits v D cd.lJ s (fam s)) ∧
      f.value Reading.gl (worldAt v c low u) =
        Reading.gl.val alpha - (q : Cb.Gl.E) * Reading.gl.val theta -
        Reading.gl.val (ofF ((v.y.cl.getD q {}).tauAt (v.y.cl.getD q {}).t0)) *
          padJ Reading.gl v q cd weighed -
        (cd.segs.map fun s => ((List.range v.y.Lam).map fun lam =>
          if (s.moe && !v.isMoe lam) = true then 0
          else Reading.gl.val (elJ v q lam) * ∑ x ∈ range (len D (fam s)),
            Reading.gl.val ((ewJ v q cd s).getD x zeroE) *
              Blocks.ext D.lT (fun i => lin (scl := sclOf h v.sc v.g v.y.Lam) D (cellsOf D c)
                tb L0 w (fam s) lam x i) u).sum).sum := by
  refine joinPart_of_layout_true hy S hs hg hrd hl ht gl_numerals Z c low u ?_ tb L0 w alpha theta
    q cd hcd weighed hzk hlow hf
  have e := (admitted_of_layout hy S.p3).shape
  rw [← e]
  exact trueAt_worldAt hl ht Reading.gl c low u

end Lines

#print axioms hasSeg_of_layout
#print axioms points_of_layout
#print axioms found_of_layout
#print axioms trueAt_worldAt
#print axioms fits_of_layout_true
#print axioms line_of_layout_true
#print axioms joinPart_of_layout_true
#print axioms fits_of_layout_any
#print axioms fits_of_layout
#print axioms line_of_layout
#print axioms joinPart_of_layout

end OnBytes.Road
