-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysKF.lean: one call's factor in the lookup's join, in the library's own
quantities of that call.

Johnson/Road/FormsKeysCall.lean says what the verifier's joinPart is worth, with the weights of the
layers and of the entries, the weight of the padding and the list of segments as the verifier has
them. This file replaces each by the library's: the weight of a layer (elP), of an entry (ewP,
through the library's rule pos for an entry's column), of the padding (PADWP, through the library's
isPad), and the list of a call's families (fams, famsIn), all at the call's own point, read as a
free point ζ (Johnson/Road/FormsKeysFree.lean).

What is compared with what: the verifier's elJ, ewJ, padJ and cd.segs with the library's el, ew,
PADW and fams, under the record CallFits.

Main definitions: famOf; CallFits (what is asked of a call for it to be the library's call cc).
Main theorems: segName_inj; elJ_value, colJ_value; padJ_eq; Fits.joinPart_lines, Fits.joinPart_KF.

What is not claimed: see Johnson/Road/FormsKeysKit.lean. That a call of the verifier's layout meets
CallFits is not shown here. That the verifier's padding key is the library's is a hypothesis (the
two texts' tables are not compared). How the call's point is cut out of the point of the whole
lookup is not looked at. The program does not import this file.
-/
import Johnson.Road.FormsKeysCall
import Johnson.Road.FormsKeysFree
import Inst.Model.FF.IndexFacts

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff eqTab Seg CallD)
open OnBytes.Model.Layer (Env)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam LW lin len present isExp call pos lJ isPad fams famsIn lut)

/-! ## A segment's name names one family -/

/-- The family whose segment has the name n, if there is one. -/
def famOf (n : String) : Option Fam :=
  ([.G, .U, .UT, .QK, .N1, .N2, .O, .D, .V, .LR, .XR, .LT, .DD, .GH, .UH, .OH, .DH, .VH, .LH, .QKH,
    .N1H, .N2H, .ROW, .SEL, .L3, .G0, .CN1, .CN2, .CQK, .CV, .CLR, .F, .MR, .CG] :
      List Fam).find? fun s => segName s == n

/-- It finds each family under its segment's name. -/
theorem famOf_segName (s : Fam) : famOf (segName s) = some s := by cases s <;> rfl

/-- Two families with one name for their segments are one. -/
theorem segName_inj {s s' : Fam} (h : segName s = segName s') : s = s' := by
  have e := famOf_segName s
  rw [h, famOf_segName s'] at e
  exact (Option.some.inj e).symm

/-! ## Sums over lists -/

section Sums

variable {K : Type} [Field K]

/-- A sum over a list of sums over a range, the other way round. -/
theorem list_sum_comm {α : Type} (g : α → ℕ → K) (n : ℕ) : ∀ L : List α,
    (L.map fun s => ∑ l ∈ range n, g s l).sum = ∑ l ∈ range n, (L.map fun s => g s l).sum
  | [] => by simp
  | a :: L => by
    simp only [List.map_cons, List.sum_cons]
    rw [list_sum_comm g n L, sum_add_distrib]

/-- A sum over a list in which the members without a property count 0 and the others under one
factor. -/
theorem list_sum_filter {α : Type} (p : α → Bool) (a : K) (h : α → K) : ∀ L : List α,
    (L.map fun s => if p s = true then a * h s else 0).sum = a * ((L.filter p).map h).sum
  | [] => by simp
  | x :: L => by
    rw [List.map_cons, List.sum_cons, list_sum_filter p a h L]
    by_cases hx : p x = true
    · rw [if_pos hx, List.filter_cons_of_pos hx, List.map_cons, List.sum_cons]
      ring
    · rw [if_neg hx, List.filter_cons_of_neg hx, zero_add]

/-- A sum over List.range, as a sum over Finset.range. -/
theorem range_map_sum (f : ℕ → K) (n : ℕ) : ((List.range n).map f).sum = ∑ l ∈ range n, f l := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

end Sums

/-! ## The verifier's weights at the call's point -/

section Weights

variable {K : Type} [Field K] (ρ : Reading K)

/-- An entry of a stretch of an array. -/
theorem getD_stretch {α : Type} (a : Array α) {s e j : ℕ} (he : e ≤ a.size) (hj : j < e - s)
    (d : α) : (a.extract s e).getD j d = a.getD (s + j) d := by
  have h1 : j < min e a.size - s := by omega
  have h2 : s + j < a.size := by omega
  simp [Array.getD, h1, h2]

/-- The verifier's weight of layer lam at the point of call q is the library's, at that point. -/
theorem elJ_value (v : Env) (D : Dim) (q : ℕ) (hll : v.y.h.ll = D.lL)
    (hsz : v.y.h.ll ≤ (v.zk.getD q #[]).size) {lam : ℕ} (hlam : lam < 2 ^ D.lL) :
    ρ.val (elJ v q lam) = elP D (pt ρ (v.zk.getD q #[])) lam := by
  have s1 : (v.zl q).size = D.lL := by
    unfold Env.zl
    rw [Array.size_extract]
    omega
  unfold elJ elP
  rw [eqTab_value ρ _ _ (by rw [s1]; exact hlam), s1]
  refine eqN_congr' _ _ (fun j hj => ?_) _
  unfold pt Env.zl
  rw [Nat.zero_add, getD_stretch _ hsz (by omega), Nat.zero_add]

/-- The verifier's weight of column p of call q, which has 2^lJ' columns, is the equality weight of
the coordinates of the column in the call's point. -/
theorem colJ_value (v : Env) (D : Dim) (q lJ' : ℕ) (hll : v.y.h.ll = D.lL)
    (hsz : v.y.h.ll + lJ' ≤ (v.zk.getD q #[]).size) {p : ℕ} (hp : p < 2 ^ lJ') :
    ρ.val ((eqTab (v.zj q lJ')).getD p zeroE) =
      Blocks.eqN lJ' D.lL (pt ρ (v.zk.getD q #[])) p := by
  have s1 : (v.zj q lJ').size = lJ' := by
    unfold Env.zj
    rw [Array.size_extract]
    omega
  rw [eqTab_value ρ _ _ (by rw [s1]; exact hp), s1,
    ← eqN_shift' lJ' D.lL (pt ρ (v.zk.getD q #[])) p]
  refine eqN_congr' lJ' 0 (fun j hj => ?_) p
  show pt ρ (v.zj q lJ') (0 + j) = pt ρ (v.zk.getD q #[]) (D.lL + (0 + j))
  unfold pt Env.zj
  rw [Nat.zero_add, getD_stretch _ hsz (by omega), hll]

end Weights

/-! ## A call of the verifier that is a call of the library -/

/-- What is asked of the verifier's call cd, with the marks weighed, for it to be the library's call
cc: the families of its segments are the library's list; each entry lies in the column that the
library's rule gives it; it has as many columns; a column is marked on a layer exactly if a segment
that exists on that layer lists it; a layer has as many coordinates as in the library. fam: the
family of each segment. The call's number in the layout is not read. -/
structure CallFits (v : Env) (D : Dim) (cd : CallD) (weighed : Array Bool) (cc : Fin 8)
    (fam : Seg → Fam) : Prop where
  /-- the families, in the library's order -/
  fams : cd.segs.map fam = Inst.Model.FFSeg.fams cc
  /-- the columns -/
  pos : ∀ s ∈ cd.segs, ∀ x, x < len D (fam s) → s.pos.getD x 0 = Inst.Model.FFSeg.pos D (fam s) x
  /-- the logarithm of the number of columns -/
  lJ : cd.lJ = Inst.Model.FFSeg.lJ D cc
  /-- the number of columns -/
  J : cd.J = 2 ^ cd.lJ
  /-- the marks -/
  marks : ∀ lam j, lam < v.y.Lam → j < cd.J →
    (weighed.getD (lam * cd.J + j) true = true ↔
      ∃ s ∈ cd.segs, (s.moe && !v.isMoe lam) = false ∧ ∃ x, x < s.pos.size ∧ s.pos.getD x 0 = j)
  /-- the layer's coordinates are as many as the library's -/
  ll : v.y.h.ll = D.lL

section Call

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} [scl : Scl] {v : Env} {D : Dim}
  {c : Cells K} {t : Cell → K} {low u : ℕ → K}

/-- The verifier's weight of the padding's columns is the library's, at the call's point. -/
theorem padJ_eq (F : Fits ρ W v D c t low u) {q : ℕ} {cd : CallD} {weighed : Array Bool}
    {cc : Fin 8} {fam : Seg → Fam} (C : CallFits v D cd weighed cc fam)
    (HS : ∀ s ∈ cd.segs, SegFits v D cd.lJ s (fam s))
    (hzk : v.y.h.ll + cd.lJ ≤ (v.zk.getD q #[]).size) :
    padJ ρ v q cd weighed = PADWP D cc (pt ρ (v.zk.getD q #[])) := by
  unfold padJ PADWP
  rw [range_map_sum, F.Lam]
  refine sum_congr rfl fun lam hlam => ?_
  have hl : lam < D.nl := mem_range.mp hlam
  rw [elJ_value ρ v D q C.ll (by omega) hl, range_map_sum, C.J, C.lJ]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  have hj' : j < 2 ^ lJ D cc := mem_range.mp hj
  have hjJ : j < cd.J := by rw [C.J, C.lJ]; exact hj'
  have hm := C.marks lam j (by rw [F.Lam]; exact hl) hjJ
  rw [C.J, C.lJ] at hm
  have hcol := colJ_value ρ v D q cd.lJ C.ll hzk (p := j) (by rw [C.lJ]; exact hj')
  rw [C.lJ] at hcol
  by_cases hp : isPad D cc lam j = true
  · rw [if_pos hp, if_neg, hcol]
    · rfl
    · intro hw
      obtain ⟨s, hs, hex, x, hx, hpx⟩ := hm.mp hw
      have S := HS s hs
      have hmem : fam s ∈ fams cc := by
        rw [← C.fams]
        exact List.mem_map_of_mem hs
      have hpr : present (fam s) lam = true := by
        rw [S.moe, F.isMoe] at hex
        unfold present
        cases h1 : isExp (fam s) with
        | false => rfl
        | true =>
          rw [h1] at hex
          simpa using hex
      have hx' : x < len D (fam s) := by rw [← S.n, ← S.size]; exact hx
      have hnp := (Inst.Model.FFSeg.IndexFacts.not_isPad_iff D cc lam j).mpr
        ⟨fam s, List.mem_filter.mpr ⟨hmem, hpr⟩, x, hx', by rw [← C.pos s hs x hx']; exact hpx⟩
      rw [hnp] at hp
      exact absurd hp (by decide)
  · have hp' : isPad D cc lam j = false := by simpa using hp
    rw [if_neg hp, if_pos]
    obtain ⟨s', hs', x, hx, hpx⟩ := (Inst.Model.FFSeg.IndexFacts.not_isPad_iff D cc lam j).mp hp'
    obtain ⟨hmem, hpr⟩ := List.mem_filter.mp hs'
    rw [← C.fams] at hmem
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hmem
    have S := HS s hs
    refine hm.mpr ⟨s, hs, ?_, x, by rw [S.size, S.n]; exact hx, by rw [C.pos s hs x hx]; exact hpx⟩
    rw [S.moe, F.isMoe]
    unfold present at hpr
    cases h1 : isExp (fam s) with
    | false => rfl
    | true =>
      rw [h1] at hpr
      simpa using hpr

/-- One call's factor in the lookup's join, in the quantities of Johnson/Road/FormsKeysFree.lean
(the library's, with the call's point ζ in the place of the library's own): alpha - q theta, less
the padding key times PADWP, less, for each layer under its weight elP, LINEP of each family of the
call that is present there. For all tb, L0 and w: no LINEP reads them. -/
theorem Fits.joinPart_lines (F : Fits ρ W v D c t low u) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
    (alpha theta : E) (q : ℕ) (cd : CallD) (weighed : Array Bool) (cc : Fin 8) (fam : Seg → Fam)
    (C : CallFits v D cd weighed cc fam) (HS : ∀ s ∈ cd.segs, SegFits v D cd.lJ s (fam s))
    (hzk : v.y.h.ll + cd.lJ ≤ (v.zk.getD q #[]).size) (hls : v.y.ls ≤ cd.lJ)
    (hlow : ∀ j, j < v.y.ls → low j = pt ρ (v.zj q cd.lJ) (cd.lJ - v.y.ls + j))
    (hu : ∀ j, j < D.lT → u j = pt ρ (v.zk.getD q #[]) (D.lL + lJ D cc + j))
    {f : Aff} (h : v.joinPart alpha theta q cd weighed = some f) :
    f.value ρ W = ρ.val alpha - (q : K) * ρ.val theta -
      ρ.val (ofF ((v.y.cl.getD q {}).tauAt (v.y.cl.getD q {}).t0)) *
        PADWP D cc (pt ρ (v.zk.getD q #[])) -
      ∑ l ∈ range D.nl, elP D (pt ρ (v.zk.getD q #[])) l *
        ((famsIn cc l).map fun s => LINEP D t tb L0 w (pt ρ (v.zk.getD q #[])) s l).sum := by
  rw [F.joinPart_lin tb L0 w alpha theta q cd weighed fam HS hzk hls hlow h, padJ_eq F C HS hzk]
  congr 1
  have inner : ∀ s ∈ cd.segs, ((List.range v.y.Lam).map fun lam =>
      if (s.moe && !v.isMoe lam) = true then 0
      else ρ.val (elJ v q lam) * ∑ x ∈ range (len D (fam s)),
        ρ.val ((ewJ v q cd s).getD x zeroE) *
          Blocks.ext D.lT (fun i => lin D t tb L0 w (fam s) lam x i) u).sum =
      ∑ l ∈ range D.nl, if present (fam s) l = true then
        elP D (pt ρ (v.zk.getD q #[])) l * LINEP D t tb L0 w (pt ρ (v.zk.getD q #[])) (fam s) l
        else 0 := by
    intro s hs
    have S := HS s hs
    have hmem : fam s ∈ fams cc := by
      rw [← C.fams]
      exact List.mem_map_of_mem hs
    have hcall : call (fam s) = cc := Inst.Model.FFSeg.IndexFacts.call_of_mem cc _ hmem
    rw [range_map_sum, F.Lam]
    refine sum_congr rfl fun lam hlam => ?_
    have hl : lam < D.nl := mem_range.mp hlam
    have hpe : ((s.moe && !v.isMoe lam) = true) ↔ ¬ present (fam s) lam = true := by
      rw [S.moe, F.isMoe]
      unfold present
      cases isExp (fam s) <;> cases Inst.Model.FFSeg.isExpL lam <;> decide
    by_cases hpr : present (fam s) lam = true
    · rw [if_neg (fun hh => hpe.mp hh hpr), if_pos hpr, elJ_value ρ v D q C.ll (by omega) hl]
      congr 1
      unfold LINEP
      refine sum_congr rfl fun x hx => ?_
      have hx' : x < len D (fam s) := mem_range.mp hx
      have hplt := Inst.Model.FFSeg.IndexFacts.pos_lt D hx'
      rw [hcall] at hplt
      have e1 : ρ.val ((ewJ v q cd s).getD x zeroE) =
          ewP D (pt ρ (v.zk.getD q #[])) (fam s) x := by
        unfold ewJ Env.ewFrom ewP ewcP
        rw [getD_map_lt _ _ (by rw [S.size, S.n]; exact hx') zeroE 0, C.pos s hs x hx',
          colJ_value ρ v D q cd.lJ C.ll hzk (by rw [C.lJ]; exact hplt), C.lJ, hcall]
      rw [e1]
      congr 1
      refine Blocks.ext_congr_point (fun j hj => ?_) _
      unfold uP
      rw [hcall]
      exact hu j hj
    · rw [if_pos (hpe.mpr hpr), if_neg hpr]
  rw [List.map_congr_left inner]
  have e2 : (cd.segs.map fun s => ∑ l ∈ range D.nl, if present (fam s) l = true then
        elP D (pt ρ (v.zk.getD q #[])) l * LINEP D t tb L0 w (pt ρ (v.zk.getD q #[])) (fam s) l
        else 0) =
      ((cd.segs.map fam).map fun s' => ∑ l ∈ range D.nl, if present s' l = true then
        elP D (pt ρ (v.zk.getD q #[])) l * LINEP D t tb L0 w (pt ρ (v.zk.getD q #[])) s' l
        else 0) := by
    rw [List.map_map]
    rfl
  rw [e2, C.fams, list_sum_comm]
  refine sum_congr rfl fun l _ => ?_
  exact list_sum_filter (fun s' => present s' l) _ _ _

/-- The same with KFP, the library's KF at the free point: the factor is alpha - q theta - KFP, plus
what KFP holds beyond the lines: TSP and the sums ACCP. These two stand inside KFP and are added
back: the right side does not hang on w or L0, and of the products in the keys nothing is said.
hpad: the verifier's padding key is the library's. -/
theorem Fits.joinPart_KF (F : Fits ρ W v D c t low u) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
    (alpha theta : E) (q : ℕ) (cd : CallD) (weighed : Array Bool) (cc : Fin 8) (fam : Seg → Fam)
    (C : CallFits v D cd weighed cc fam) (HS : ∀ s ∈ cd.segs, SegFits v D cd.lJ s (fam s))
    (hzk : v.y.h.ll + cd.lJ ≤ (v.zk.getD q #[]).size) (hls : v.y.ls ≤ cd.lJ)
    (hlow : ∀ j, j < v.y.ls → low j = pt ρ (v.zj q cd.lJ) (cd.lJ - v.y.ls + j))
    (hu : ∀ j, j < D.lT → u j = pt ρ (v.zk.getD q #[]) (D.lL + lJ D cc + j))
    (hpad : ρ.val (ofF ((v.y.cl.getD q {}).tauAt (v.y.cl.getD q {}).t0)) =
      (((lut tb cc).pad : ℤ) : K))
    {f : Aff} (h : v.joinPart alpha theta q cd weighed = some f) :
    f.value ρ W = ρ.val alpha - (q : K) * ρ.val theta -
      KFP D t tb L0 w cc (pt ρ (v.zk.getD q #[])) + TSP D t tb L0 w cc (pt ρ (v.zk.getD q #[])) +
      ∑ l ∈ range D.nl, elP D (pt ρ (v.zk.getD q #[])) l *
        ((famsIn cc l).map fun s => ACCP D t w (pt ρ (v.zk.getD q #[])) s l).sum := by
  rw [F.joinPart_lines tb L0 w alpha theta q cd weighed cc fam C HS hzk hls hlow hu h, hpad]
  have split : ∀ l, ((famsIn cc l).map fun s => LINEP D t tb L0 w (pt ρ (v.zk.getD q #[])) s l +
      ACCP D t w (pt ρ (v.zk.getD q #[])) s l).sum =
      ((famsIn cc l).map fun s => LINEP D t tb L0 w (pt ρ (v.zk.getD q #[])) s l).sum +
      ((famsIn cc l).map fun s => ACCP D t w (pt ρ (v.zk.getD q #[])) s l).sum := by
    intro l
    induction famsIn cc l with
    | nil => simp
    | cons a L ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring
  unfold KFP
  simp only [split, mul_add, sum_add_distrib]
  ring

end Call

#print axioms segName_inj
#print axioms padJ_eq
#print axioms Fits.joinPart_lines
#print axioms Fits.joinPart_KF

end OnBytes.Road
