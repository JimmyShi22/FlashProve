-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysVec.lean: the multilinear extension of the key vector of a lookup call.

The library defines the key vector of a call (FFSeg.keyVec in Inst/Model/FF/Trace.lean): at the
index (layer | column | position) it holds the key of the family that takes the column, and the
table's padding value where no family that is present in the layer takes it. The library also
defines a quantity KF of the call (Inst/Model/FF/Objects.lean): the padding value times the weight
of the padding, plus three weighted sums of the three parts of the keys. This file shows that, if
D.lT ≤ D.cap, KF is the multilinear extension of the key vector at the call's point.

What is compared with what. No theorem here names the verifier in OnBytes/. The quantities at a free
point ζ (elP, ewcP, ewP, uP, PADWP, KEYP, LINEP, TERMP, ACCP, TSP, KFP) are definitions of
Johnson/Road/FormsKeysFree.lean, written after the library's with ζ in the place of the call's
point. ext_keyVec and ext_keyVec_KFP set the library's keyVec against these; the theorems X_eq_XP
and XP_eq_X set each of these against the library's X; ext_keyVec_KF names objects of the library
alone.

Main theorems.
  ext_keyVec      for all sizes D and every point ζ: the extension of keyVec at ζ is the padding
                  value times PADWP, plus the sum over the layers and the families present there of
                  the weighted extensions of the whole keys (KEYP)
  ext_keyVec_KFP  the same with the keys split into their three parts: the extension is KFP
  el_eq_elP, ewc_eq_ewcP, ew_eq_ewP, PADW_eq_PADWP, TERM_eq_TERMP (for all sizes);
  zpos_eq_uP, LINE_eq_LINEP, ACC_eq_ACCP, TS_eq_TSP, KF_eq_KFP (if D.lT ≤ D.cap)
                  each quantity of the library is the one at the free point ζ := zc D z c
  ext_keyVec_KF   if D.lT ≤ D.cap: the extension of keyVec at zc D z c is the library's KF D .. z c
  elP_congr, ewcP_congr, PADWP_congr, LINEP_congr, KEYP_congr, TERMP_congr, ACCP_congr, TSP_congr,
  KFP_congr       the quantities of call c at a free point read its first aC D c coordinates alone
  elP_eq_el, ewP_eq_ew, PADWP_eq_PADW (for all sizes); LINEP_eq_LINE, ACCP_eq_ACC, TSP_eq_TS,
  KFP_eq_KF (if D.lT ≤ D.cap)
                  at a point that agrees with zc D z c on these coordinates they are the library's

The one hypothesis on the sizes, D.lT ≤ D.cap, says that a tree of the lookup may hold as many keys
as there are positions. Only the theorems that name zpos or an object built on it have it. The
library takes zpos from the coordinates of z that belong to a tree, as the last D.lT of them; with
fewer than D.lT such coordinates its definition and that of zc D z c read different coordinates of z
(so the two texts read; no theorem here says it). The reference sizes meet the hypothesis (ref_cap),
and so do all sizes with Dim.OK (cap_of_ok). The hypothesis of the theorems XP_eq_X, that ζ agrees
with zc D z c on the first aC D c coordinates, is met by ζ := zc D z c.

What is not claimed. Nothing is said about the verifier in OnBytes/, about how a point is drawn,
about what a lookup shows of the key vector, or about the trees into which the library cuts it. The
program does not import this file.
-/
import Johnson.Road.FormsKeysFree
import Inst.Model.FF.IndexFacts

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam LW key lin term mat key_eq len call pos lJ aC Dk isPad famAt
  fams famsIn present lut keyVec zc zpos el ewc ew PADW LINE TERM ACC TS KF)
open Inst.Model.FFSeg.IndexFacts (fams_nodup mem_fams_iff posInj pos_lt not_isPad_iff keyVecAt
  Dk_le T_pos foldl_min_le)

variable {K : Type} [Field K] (D : Dim)

/-! ## Tools -/

/-- The kernel of the point that begins at the coordinate off is the kernel from off on. -/
theorem eqN_from (m off : ℕ) (a : ℕ → K) (z : ℕ) :
    Blocks.eqN m 0 (fun j => a (off + j)) z = Blocks.eqN m off a z := by
  unfold Blocks.eqN
  exact prod_congr rfl fun j _ => by rw [Nat.zero_add]

/-- The extension of a sum over a list is the sum of the extensions. -/
theorem ext_listSum {α : Type} (g : ℕ) (L : List α) (f : α → ℕ → K) (pt : ℕ → K) :
    Blocks.ext g (fun i => (L.map fun s => f s i).sum) pt =
      (L.map fun s => Blocks.ext g (f s) pt).sum := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact Blocks.ext_zero_of_forall (fun _ _ => rfl) pt
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [Blocks.ext_add, ih]

/-- A number that is no more than the start and no more than any member's value is no more than the
least of them, as a fold computes it. -/
theorem le_foldl_min {α : Type} (f : α → ℕ) (m : ℕ) :
    ∀ (l : List α) (a : ℕ), m ≤ a → (∀ c ∈ l, m ≤ f c) →
      m ≤ l.foldl (fun k c => min k (f c)) a
  | [], _, ha, _ => ha
  | b :: l, a, ha, h => by
    rw [List.foldl_cons]
    exact le_foldl_min f m l (min a (f b)) (le_min ha (h b List.mem_cons_self))
      fun c hc => h c (List.mem_cons_of_mem b hc)

/-- A family that is listed as present in a layer of call c is a family of call c. -/
theorem call_of_famsIn {c : Fin 8} {l : ℕ} {s : Fam} (hs : s ∈ famsIn c l) : call s = c :=
  mem_fams_iff.mp (List.mem_filter.mp (show s ∈ (fams c).filter (present · l) from hs)).1

/-- The kernel reads the m coordinates from off on alone. -/
theorem eqN_agree (m off : ℕ) {a a' : ℕ → K} (h : ∀ j < m, a (off + j) = a' (off + j)) (z : ℕ) :
    Blocks.eqN m off a z = Blocks.eqN m off a' z := by
  unfold Blocks.eqN
  exact prod_congr rfl fun j hj => by rw [h j (mem_range.mp hj)]

/-! ## The index (layer | column | position) -/

/-- The extension of a vector with the indices of call c, as a sum over the layers, the columns and
the positions. -/
theorem ext_three (c : Fin 8) (ζ : ℕ → K) (v : ℕ → K) :
    Blocks.ext (aC D c) v ζ =
      ∑ l ∈ range D.nl, elP D ζ l * ∑ jj ∈ range (2 ^ lJ D c), ewcP D c ζ jj *
        Blocks.ext D.lT (fun i => v ((l * 2 ^ lJ D c + jj) * D.T + i)) (uP D c ζ) := by
  have ea : aC D c = D.lL + lJ D c + D.lT := rfl
  have eT : D.T = 2 ^ D.lT := rfl
  have eL : D.nl = 2 ^ D.lL := rfl
  unfold Blocks.ext elP ewcP uP
  rw [ea, eT, eL, pow_add, pow_add, Alg.sum_range_mul_add, Alg.sum_range_mul_add]
  refine sum_congr rfl fun l _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun jj hjj => ?_
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [Blocks.eqN_append' (D.lL + lJ D c) D.lT 0 ζ _ (mem_range.mp hi),
    Blocks.eqN_append' D.lL (lJ D c) 0 ζ l (mem_range.mp hjj), eqN_from, Nat.zero_add,
    Nat.zero_add]
  ring

/-- A sum over the columns of a call that are not padding in layer l is the sum over the families
that are present in the layer and over their entries: every such column is the column of one entry
of one such family. -/
theorem sum_taken (c : Fin 8) (l : ℕ) (F : ℕ → K) :
    ∑ jj ∈ range (2 ^ lJ D c), (if isPad D c l jj then 0 else F jj) =
      ((famsIn c l).map fun s => ∑ x ∈ range (len D s), F (pos D s x)).sum := by
  rw [show famsIn c l = (fams c).filter (present · l) from rfl]
  have hset : ((range (2 ^ lJ D c)).filter fun jj => isPad D c l jj = false) =
      ((fams c).filter (present · l)).toFinset.biUnion fun s =>
        (range (len D s)).image (pos D s) := by
    ext jj
    rw [mem_filter, mem_range, not_isPad_iff, mem_biUnion]
    constructor
    · rintro ⟨_, s, hs, x, hx, hp⟩
      exact ⟨s, List.mem_toFinset.mpr hs, mem_image.mpr ⟨x, mem_range.mpr hx, hp⟩⟩
    · rintro ⟨s, hs, hj⟩
      obtain ⟨x, hx, hp⟩ := mem_image.mp hj
      have hs' := List.mem_toFinset.mp hs
      have hc := mem_fams_iff.mp (List.mem_filter.mp hs').1
      refine ⟨?_, s, hs', x, mem_range.mp hx, hp⟩
      rw [← hp, ← hc]
      exact pos_lt D (mem_range.mp hx)
  have e1 : ∑ jj ∈ range (2 ^ lJ D c), (if isPad D c l jj then 0 else F jj) =
      ∑ jj ∈ (range (2 ^ lJ D c)).filter (fun jj => isPad D c l jj = false), F jj := by
    rw [sum_filter]
    refine sum_congr rfl fun jj _ => ?_
    cases isPad D c l jj <;> simp
  rw [e1, hset, sum_biUnion, ← List.sum_toFinset _ ((fams_nodup c).filter _)]
  · refine sum_congr rfl fun s _ => ?_
    rw [sum_image]
    intro x hx x' hx' h
    have hx1 : x < len D s := by simpa using hx
    have hx2 : x' < len D s := by simpa using hx'
    exact (posInj D s s x x' rfl hx1 hx2 h).2
  · intro s hs s' hs' hne
    refine disjoint_left.mpr fun jj h1 h2 => hne ?_
    obtain ⟨x, hx, hp⟩ := mem_image.mp h1
    obtain ⟨x', hx', hp'⟩ := mem_image.mp h2
    have hs1 : s ∈ (fams c).filter (present · l) := by simpa using hs
    have hs2 : s' ∈ (fams c).filter (present · l) := by simpa using hs'
    have hc := mem_fams_iff.mp (List.mem_filter.mp hs1).1
    have hc' := mem_fams_iff.mp (List.mem_filter.mp hs2).1
    exact (posInj D s s' x x' (hc.trans hc'.symm) (mem_range.mp hx)
      (mem_range.mp hx') (hp.trans hp'.symm)).1

/-! ## The quantities of the library that read no cell, at the call's point -/

/-- The library's weight of a layer is the one at the free point ζ := zc D z c. -/
theorem el_eq_elP (z : ℕ → K) (c : Fin 8) (l : ℕ) : el D z c l = elP D (zc D z c) l := rfl

/-- The library's weight of a column is the one at the free point ζ := zc D z c. -/
theorem ewc_eq_ewcP (z : ℕ → K) (c : Fin 8) (jj : ℕ) :
    ewc D z c jj = ewcP D c (zc D z c) jj := rfl

/-- The library's weight of an entry of family s is the one at the free point, the point of the call
of s. -/
theorem ew_eq_ewP (z : ℕ → K) (s : Fam) (x : ℕ) :
    ew D z s x = ewP D (zc D z (call s)) s x := rfl

/-- The library's weight of the padding is the one at the free point ζ := zc D z c. -/
theorem PADW_eq_PADWP (z : ℕ → K) (c : Fin 8) : PADW D z c = PADWP D c (zc D z c) := rfl

/-- If D.lT ≤ D.cap then D.lT ≤ Dk D: Dk D is the least of D.cap and the calls' numbers of
coordinates, and each call has at least D.lT coordinates. -/
theorem lT_le_Dk (hcap : D.lT ≤ D.cap) : D.lT ≤ Dk D :=
  le_foldl_min (aC D) D.lT (List.finRange 8) D.cap hcap fun c _ => by
    show D.lT ≤ D.lL + lJ D c + D.lT
    omega

/-- Sizes that meet the library's Dim.OK meet the hypothesis D.lT ≤ D.cap. -/
theorem cap_of_ok (hD : D.OK) : D.lT ≤ D.cap := by
  have h1 := hD.whole 0
  have h2 : Dk D ≤ D.cap := (foldl_min_le (aC D) (List.finRange 8) D.cap).1
  omega

/-- The reference sizes meet the hypothesis D.lT ≤ D.cap. -/
theorem ref_cap : Dim.ref.lT ≤ Dim.ref.cap := by decide

omit [Field K] in
/-- If D.lT ≤ D.cap, the library's point of the positions is, for every call c, what lies behind
the coordinates of the layer and the column in the call's point. -/
theorem zpos_eq_uP (hcap : D.lT ≤ D.cap) (z : ℕ → K) (c : Fin 8) :
    zpos D z = uP D c (zc D z c) := by
  funext j
  have h0 := lT_le_Dk D hcap
  have h1 := Dk_le D c
  have ea : aC D c = D.lL + lJ D c + D.lT := rfl
  simp only [zpos, Inst.Model.FFSeg.sh, uP, zc, Inst.Model.FFSeg.eC]
  generalize Dk D = k at *
  generalize aC D c = a at *
  generalize lJ D c = J at *
  rw [if_neg (by omega)]
  exact congrArg z (by omega)

/-! ## Which coordinates of the free point are read: the quantities that read no cell -/

/-- The weight of a layer reads coordinates below aC D c alone. -/
theorem elP_congr (c : Fin 8) {ζ ζ' : ℕ → K} (h : ∀ j < aC D c, ζ j = ζ' j) (l : ℕ) :
    elP D ζ l = elP D ζ' l :=
  eqN_agree D.lL 0 (fun j hj => h _ (by
    show 0 + j < D.lL + lJ D c + D.lT
    omega)) l

/-- The weight of a column of call c reads coordinates below aC D c alone. -/
theorem ewcP_congr (c : Fin 8) {ζ ζ' : ℕ → K} (h : ∀ j < aC D c, ζ j = ζ' j) (jj : ℕ) :
    ewcP D c ζ jj = ewcP D c ζ' jj :=
  eqN_agree (lJ D c) D.lL (fun j hj => h _ (by
    show D.lL + j < D.lL + lJ D c + D.lT
    omega)) jj

/-- An extension over the positions at the point uP D c ζ reads coordinates of ζ below aC D c
alone. -/
theorem ext_uP_congr (c : Fin 8) {ζ ζ' : ℕ → K} (h : ∀ j < aC D c, ζ j = ζ' j) (v : ℕ → K) :
    Blocks.ext D.lT v (uP D c ζ) = Blocks.ext D.lT v (uP D c ζ') :=
  Blocks.ext_congr_point (fun j hj => by
    show ζ (D.lL + lJ D c + j) = ζ' (D.lL + lJ D c + j)
    exact h _ (by
      show D.lL + lJ D c + j < D.lL + lJ D c + D.lT
      omega)) v

/-- The weight of the padding of call c reads coordinates below aC D c alone. -/
theorem PADWP_congr (c : Fin 8) {ζ ζ' : ℕ → K} (h : ∀ j < aC D c, ζ j = ζ' j) :
    PADWP D c ζ = PADWP D c ζ' := by
  unfold PADWP
  simp only [elP_congr D c h, ewcP_congr D c h]

/-- The weight of a layer at a point that agrees with the library's point of call c on its aC D c
coordinates is the library's. -/
theorem elP_eq_el {z ζ : ℕ → K} {c : Fin 8} (h : ∀ j < aC D c, ζ j = zc D z c j) (l : ℕ) :
    elP D ζ l = el D z c l :=
  elP_congr D c h l

/-- The weight of an entry of a family of call c at such a point is the library's. -/
theorem ewP_eq_ew {z ζ : ℕ → K} {c : Fin 8} {s : Fam} (hs : call s = c)
    (h : ∀ j < aC D c, ζ j = zc D z c j) (x : ℕ) : ewP D ζ s x = ew D z s x := by
  subst hs
  rw [ew_eq_ewP]
  exact ewcP_congr D (call s) h (pos D s x)

/-- The weight of the padding at such a point is the library's. -/
theorem PADWP_eq_PADW {z ζ : ℕ → K} {c : Fin 8} (h : ∀ j < aC D c, ζ j = zc D z c j) :
    PADWP D c ζ = PADW D z c :=
  PADWP_congr D c h

section Cells

variable [scl : Scl] (t : Cell → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)

/-! ## The key vector -/

/-- At a column that is padding in the layer the key vector holds the table's padding value. -/
theorem keyVec_pad {c : Fin 8} {l jj i : ℕ} (hjj : jj < 2 ^ lJ D c) (hi : i < D.T)
    (hp : isPad D c l jj = true) :
    keyVec D t tb L0 w c ((l * 2 ^ lJ D c + jj) * D.T + i) = (((lut tb c).pad : ℤ) : K) := by
  have hT := T_pos D
  have hJ : 0 < 2 ^ lJ D c := Nat.two_pow_pos _
  have e1 : ((l * 2 ^ lJ D c + jj) * D.T + i) / D.T = l * 2 ^ lJ D c + jj := by
    rw [Nat.mul_comm, Nat.mul_add_div hT, Nat.div_eq_of_lt hi, Nat.add_zero]
  have e3 : (l * 2 ^ lJ D c + jj) / 2 ^ lJ D c = l := by
    rw [Nat.mul_comm, Nat.mul_add_div hJ, Nat.div_eq_of_lt hjj, Nat.add_zero]
  have e4 : (l * 2 ^ lJ D c + jj) % 2 ^ lJ D c = jj := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hjj]
  unfold isPad at hp
  unfold keyVec
  rw [e1, e3, e4]
  cases hf : famAt D c jj with
  | none => rfl
  | some a =>
    obtain ⟨s, x⟩ := a
    rw [hf] at hp
    have hp' : present s l = false := by simpa using hp
    simp only
    rw [if_neg (by rw [hp']; exact Bool.false_ne_true)]

/-- One layer of the key vector: the sum over its columns of the column's weight times the extension
over the positions is the padding value times the weight of the layer's padding columns, plus the
weighted extensions of the keys of the families that are present in the layer. -/
theorem cols_keyVec (c : Fin 8) (ζ : ℕ → K) (l : ℕ) :
    ∑ jj ∈ range (2 ^ lJ D c), ewcP D c ζ jj *
        Blocks.ext D.lT (fun i => keyVec D t tb L0 w c ((l * 2 ^ lJ D c + jj) * D.T + i))
          (uP D c ζ) =
      (((lut tb c).pad : ℤ) : K) *
          (∑ jj ∈ range (2 ^ lJ D c), if isPad D c l jj then ewcP D c ζ jj else 0) +
        ((famsIn c l).map fun s => KEYP D t tb L0 w ζ s l).sum := by
  have h1 : ∀ jj ∈ range (2 ^ lJ D c), ewcP D c ζ jj *
        Blocks.ext D.lT (fun i => keyVec D t tb L0 w c ((l * 2 ^ lJ D c + jj) * D.T + i))
          (uP D c ζ) =
      (((lut tb c).pad : ℤ) : K) * (if isPad D c l jj then ewcP D c ζ jj else 0) +
        (if isPad D c l jj then 0 else ewcP D c ζ jj *
          Blocks.ext D.lT (fun i => keyVec D t tb L0 w c ((l * 2 ^ lJ D c + jj) * D.T + i))
            (uP D c ζ)) := by
    intro jj hjj
    cases hp : isPad D c l jj with
    | false => simp
    | true =>
      rw [Blocks.ext_congr (w := fun _ => (((lut tb c).pad : ℤ) : K))
        (fun i hi => keyVec_pad D t tb L0 w (mem_range.mp hjj) hi hp), Blocks.ext_const]
      simp [mul_comm]
  rw [sum_congr rfl h1, sum_add_distrib, ← mul_sum, sum_taken D c l fun jj => ewcP D c ζ jj *
    Blocks.ext D.lT (fun i => keyVec D t tb L0 w c ((l * 2 ^ lJ D c + jj) * D.T + i)) (uP D c ζ)]
  congr 2
  refine List.map_congr_left fun s hs => ?_
  obtain ⟨hs1, hs2⟩ := List.mem_filter.mp (show s ∈ (fams c).filter (present · l) from hs)
  have hc : call s = c := mem_fams_iff.mp hs1
  subst hc
  unfold KEYP
  refine sum_congr rfl fun x hx => ?_
  have e : Blocks.ext D.lT
        (fun i => keyVec D t tb L0 w (call s) ((l * 2 ^ lJ D (call s) + pos D s x) * D.T + i))
        (uP D (call s) ζ) =
      Blocks.ext D.lT (fun i => key D t tb L0 w s l x i) (uP D (call s) ζ) :=
    Blocks.ext_congr (fun i hi => keyVecAt K D t tb L0 w s l x i (mem_range.mp hx) hi hs2) _
  rw [e]
  rfl

/-- The multilinear extension of the key vector of call c at any point ζ: the table's padding value
times the weight of the padding, plus, for each layer and each family that is present in it, the
weighted extensions of the family's keys. For all sizes. -/
theorem ext_keyVec (c : Fin 8) (ζ : ℕ → K) :
    Blocks.ext (aC D c) (keyVec D t tb L0 w c) ζ =
      (((lut tb c).pad : ℤ) : K) * PADWP D c ζ +
        ∑ l ∈ range D.nl, elP D ζ l * ((famsIn c l).map fun s => KEYP D t tb L0 w ζ s l).sum := by
  rw [ext_three]
  unfold PADWP
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun l _ => ?_
  rw [cols_keyVec]
  ring

/-- The same with the extension written out as a sum over the indices of the call. -/
theorem sum_keyVec (c : Fin 8) (ζ : ℕ → K) :
    ∑ X ∈ range (2 ^ aC D c), Blocks.eqN (aC D c) 0 ζ X * keyVec D t tb L0 w c X =
      (((lut tb c).pad : ℤ) : K) * PADWP D c ζ +
        ∑ l ∈ range D.nl, elP D ζ l * ((famsIn c l).map fun s => KEYP D t tb L0 w ζ s l).sum :=
  ext_keyVec D t tb L0 w c ζ

/-! ## The three parts of the keys -/

/-- The weighted extensions of the keys of a family are those of the affine parts, plus the
extension of the weighted products, plus those of the matrix products. -/
theorem KEYP_parts (ζ : ℕ → K) (s : Fam) (l : ℕ) :
    KEYP D t tb L0 w ζ s l =
      LINEP D t tb L0 w ζ s l +
        Blocks.ext D.lT (fun i => TERMP D t tb L0 w ζ s l i) (uP D (call s) ζ) +
        ACCP D t w ζ s l := by
  unfold KEYP LINEP TERMP ACCP
  rw [Blocks.ext_sum, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [Blocks.ext_smul, Blocks.ext_congr (fun i _ => key_eq D t tb L0 w s l x i), Blocks.ext_add,
    Blocks.ext_add]
  ring

/-- What is left to the sumcheck over the positions, as a sum over the layers and the families. -/
theorem TSP_eq (c : Fin 8) (ζ : ℕ → K) :
    TSP D t tb L0 w c ζ =
      ∑ l ∈ range D.nl, elP D ζ l * ((famsIn c l).map fun s =>
        Blocks.ext D.lT (fun i => TERMP D t tb L0 w ζ s l i) (uP D c ζ)).sum := by
  unfold TSP
  rw [Blocks.ext_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [Blocks.ext_smul, ext_listSum]

/-- The multilinear extension of the key vector of call c at any point ζ is the library's KF with ζ
in the place of the call's point. For all sizes. -/
theorem ext_keyVec_KFP (c : Fin 8) (ζ : ℕ → K) :
    Blocks.ext (aC D c) (keyVec D t tb L0 w c) ζ = KFP D t tb L0 w c ζ := by
  rw [ext_keyVec]
  unfold KFP
  rw [TSP_eq, add_assoc, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun l _ => ?_
  rw [← mul_add, ← List.sum_map_add]
  congr 2
  refine List.map_congr_left fun s hs => ?_
  have hc : call s = c := call_of_famsIn hs
  rw [KEYP_parts, hc]
  ring

/-! ## The quantities of the library that read the cells, at the call's point -/

/-- The library's TERM is the one at the free point, the point of the call of s. -/
theorem TERM_eq_TERMP (z : ℕ → K) (s : Fam) (l i : ℕ) :
    TERM D t tb L0 w z s l i = TERMP D t tb L0 w (zc D z (call s)) s l i := rfl

/-- If D.lT ≤ D.cap, the library's LINE is the one at the free point, the point of the call of
s. -/
theorem LINE_eq_LINEP (hcap : D.lT ≤ D.cap) (z : ℕ → K) (s : Fam) (l : ℕ) :
    LINE D t tb L0 w z s l = LINEP D t tb L0 w (zc D z (call s)) s l := by
  unfold LINE LINEP
  rw [zpos_eq_uP D hcap z (call s)]
  rfl

/-- If D.lT ≤ D.cap, the library's ACC is the one at the free point, the point of the call of
s. -/
theorem ACC_eq_ACCP (hcap : D.lT ≤ D.cap) (z : ℕ → K) (s : Fam) (l : ℕ) :
    ACC D t w z s l = ACCP D t w (zc D z (call s)) s l := by
  unfold ACC ACCP
  rw [zpos_eq_uP D hcap z (call s)]
  rfl

/-- If D.lT ≤ D.cap, the library's TS is the one at the free point ζ := zc D z c. -/
theorem TS_eq_TSP (hcap : D.lT ≤ D.cap) (z : ℕ → K) (c : Fin 8) :
    TS D t tb L0 w z c = TSP D t tb L0 w c (zc D z c) := by
  have e : ∀ l i, ((famsIn c l).map fun s => TERM D t tb L0 w z s l i) =
      (famsIn c l).map fun s => TERMP D t tb L0 w (zc D z c) s l i := fun l i =>
    List.map_congr_left fun s hs => by
      have hc : call s = c := call_of_famsIn hs
      rw [TERM_eq_TERMP, hc]
  unfold TS TSP
  rw [zpos_eq_uP D hcap z c]
  simp only [e, el_eq_elP]

/-- If D.lT ≤ D.cap, the library's KF is the one at the free point ζ := zc D z c. -/
theorem KF_eq_KFP (hcap : D.lT ≤ D.cap) (z : ℕ → K) (c : Fin 8) :
    KF D t tb L0 w z c = KFP D t tb L0 w c (zc D z c) := by
  have e : ∀ l, ((famsIn c l).map fun s => LINE D t tb L0 w z s l + ACC D t w z s l) =
      (famsIn c l).map fun s =>
        LINEP D t tb L0 w (zc D z c) s l + ACCP D t w (zc D z c) s l := fun l =>
    List.map_congr_left fun s hs => by
      have hc : call s = c := call_of_famsIn hs
      rw [LINE_eq_LINEP D t tb L0 w hcap, ACC_eq_ACCP D t w hcap, hc]
  unfold KF KFP
  rw [PADW_eq_PADWP, TS_eq_TSP D t tb L0 w hcap]
  simp only [e, el_eq_elP]

/-- If D.lT ≤ D.cap: the library's KF of call c is the multilinear extension of the library's key
vector of the call at the library's point of the call. -/
theorem ext_keyVec_KF (hcap : D.lT ≤ D.cap) (z : ℕ → K) (c : Fin 8) :
    Blocks.ext (aC D c) (keyVec D t tb L0 w c) (zc D z c) = KF D t tb L0 w z c := by
  rw [ext_keyVec_KFP, KF_eq_KFP D t tb L0 w hcap]

/-! ## Which coordinates of the free point are read: the quantities that read the cells -/

/-- LINEP of a family of call c reads coordinates below aC D c alone. -/
theorem LINEP_congr {c : Fin 8} {s : Fam} (hs : call s = c) {ζ ζ' : ℕ → K}
    (h : ∀ j < aC D c, ζ j = ζ' j) (l : ℕ) :
    LINEP D t tb L0 w ζ s l = LINEP D t tb L0 w ζ' s l := by
  subst hs
  unfold LINEP ewP
  simp only [ewcP_congr D _ h, ext_uP_congr D _ h]

/-- KEYP of a family of call c reads coordinates below aC D c alone. -/
theorem KEYP_congr {c : Fin 8} {s : Fam} (hs : call s = c) {ζ ζ' : ℕ → K}
    (h : ∀ j < aC D c, ζ j = ζ' j) (l : ℕ) :
    KEYP D t tb L0 w ζ s l = KEYP D t tb L0 w ζ' s l := by
  subst hs
  unfold KEYP ewP
  simp only [ewcP_congr D _ h, ext_uP_congr D _ h]

/-- TERMP of a family of call c reads coordinates below aC D c alone. -/
theorem TERMP_congr {c : Fin 8} {s : Fam} (hs : call s = c) {ζ ζ' : ℕ → K}
    (h : ∀ j < aC D c, ζ j = ζ' j) (l i : ℕ) :
    TERMP D t tb L0 w ζ s l i = TERMP D t tb L0 w ζ' s l i := by
  subst hs
  unfold TERMP ewP
  simp only [ewcP_congr D _ h]

/-- ACCP of a family of call c reads coordinates below aC D c alone. -/
theorem ACCP_congr {c : Fin 8} {s : Fam} (hs : call s = c) {ζ ζ' : ℕ → K}
    (h : ∀ j < aC D c, ζ j = ζ' j) (l : ℕ) :
    ACCP D t w ζ s l = ACCP D t w ζ' s l := by
  subst hs
  unfold ACCP ewP
  simp only [ewcP_congr D _ h, ext_uP_congr D _ h]

/-- TSP of call c reads coordinates below aC D c alone. -/
theorem TSP_congr (c : Fin 8) {ζ ζ' : ℕ → K} (h : ∀ j < aC D c, ζ j = ζ' j) :
    TSP D t tb L0 w c ζ = TSP D t tb L0 w c ζ' := by
  have e : ∀ l i, ((famsIn c l).map fun s => TERMP D t tb L0 w ζ s l i) =
      (famsIn c l).map fun s => TERMP D t tb L0 w ζ' s l i := fun l i =>
    List.map_congr_left fun s hs => TERMP_congr D t tb L0 w (call_of_famsIn hs) h l i
  unfold TSP
  simp only [e, elP_congr D c h, ext_uP_congr D c h]

/-- KFP of call c reads coordinates below aC D c alone. -/
theorem KFP_congr (c : Fin 8) {ζ ζ' : ℕ → K} (h : ∀ j < aC D c, ζ j = ζ' j) :
    KFP D t tb L0 w c ζ = KFP D t tb L0 w c ζ' := by
  rw [← ext_keyVec_KFP, ← ext_keyVec_KFP]
  exact Blocks.ext_congr_point h _

/-! ## At a point that agrees with the library's point of the call on its aC D c coordinates -/

/-- If D.lT ≤ D.cap, LINEP of a family of call c at such a point is the library's LINE. -/
theorem LINEP_eq_LINE (hcap : D.lT ≤ D.cap) {z ζ : ℕ → K} {c : Fin 8} {s : Fam}
    (hs : call s = c) (h : ∀ j < aC D c, ζ j = zc D z c j) (l : ℕ) :
    LINEP D t tb L0 w ζ s l = LINE D t tb L0 w z s l := by
  rw [LINE_eq_LINEP D t tb L0 w hcap, hs]
  exact LINEP_congr D t tb L0 w hs h l

/-- If D.lT ≤ D.cap, ACCP of a family of call c at such a point is the library's ACC. -/
theorem ACCP_eq_ACC (hcap : D.lT ≤ D.cap) {z ζ : ℕ → K} {c : Fin 8} {s : Fam}
    (hs : call s = c) (h : ∀ j < aC D c, ζ j = zc D z c j) (l : ℕ) :
    ACCP D t w ζ s l = ACC D t w z s l := by
  rw [ACC_eq_ACCP D t w hcap, hs]
  exact ACCP_congr D t w hs h l

/-- If D.lT ≤ D.cap, TSP at such a point is the library's TS. -/
theorem TSP_eq_TS (hcap : D.lT ≤ D.cap) {z ζ : ℕ → K} {c : Fin 8}
    (h : ∀ j < aC D c, ζ j = zc D z c j) : TSP D t tb L0 w c ζ = TS D t tb L0 w z c := by
  rw [TS_eq_TSP D t tb L0 w hcap]
  exact TSP_congr D t tb L0 w c h

/-- If D.lT ≤ D.cap, KFP at such a point is the library's KF. -/
theorem KFP_eq_KF (hcap : D.lT ≤ D.cap) {z ζ : ℕ → K} {c : Fin 8}
    (h : ∀ j < aC D c, ζ j = zc D z c j) : KFP D t tb L0 w c ζ = KF D t tb L0 w z c := by
  rw [KF_eq_KFP D t tb L0 w hcap]
  exact KFP_congr D t tb L0 w c h

end Cells

#print axioms ext_keyVec
#print axioms sum_keyVec
#print axioms ext_keyVec_KFP
#print axioms zpos_eq_uP
#print axioms KF_eq_KFP
#print axioms ext_keyVec_KF
#print axioms KFP_congr
#print axioms TSP_eq_TS
#print axioms LINEP_eq_LINE
#print axioms ACCP_eq_ACC
#print axioms KFP_eq_KF
#print axioms ref_cap
#print axioms cap_of_ok

end OnBytes.Road
