-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/FormsKeysFits.lean: the record Fits follows from the verifier's own layout of the
tensors, a few switches, and the truth of six families of tables.

Johnson/Road/FormsKeysKit.lean gathers in the record Fits all that the theorems on the forms of the
lookup's segments ask. This file takes the record apart.
 - The library's sizes D are any that agree with the verifier's shape in nine numbers (Sized);
   dimOf is one such D.
 - The library's table of scales is defined from the verifier's scale file (wordsAt, sclOf).
 - The library's names of cells are read in the cells of the verifier's matrices by the library's
   own rule for the feature of a cell (cellsOf, through FFSeg.feat). That the verifier's forms find
   these cells at the verifier's own places is proved: the function that lays the verifier's tensors
   out (layTensors on tensorAsks) gives each cell the feature that the library's rule gives it
   (place_eq_feat, xb_eq_feat).
What is left as hypotheses of the last theorem, fits_of_laid:
 - Numerals: the reading takes the program's numerals, multiples and negatives to those of K (at the
   library's field: gl_numerals, Johnson/Road/FormsKeysKit.lean),
 - Laid: seventeen plain facts on the layout's numbers, each the text of a line of layoutBase or
   what one of its tests leaves; Johnson/Road/FormsKeysLaid.lean proves them of every layout that
   the verifier's function returns for a shape with routed experts,
 - Switches: the switches and digit forms for which alone the library has keys,
 - the norms' shifts are at least 16 on the group's layers (proved in the same file from the
   verifier's test of the scale file),
 - Found: six families of tables are found under their names (Johnson/Road/FormsKeysWorld.lean),
 - TrueAt: the entries of these six families are true. This is the one hypothesis on the world.

Main definitions: Sized, dimOf, wordsAt, sclOf, cellsOf, matNo, mxNo, Switches, Laid, Found, TrueAt,
Tabs.
Main theorems: layTensors_find, ten_of; layTensors_off, place_eq_feat, xb_eq_feat; tied_cellsOf;
lawful_sclOf; fits_of_laid.

What is not claimed: see Johnson/Road/FormsKeysKit.lean. Only the number of a cell's feature in its
matrix is compared with the library's; how a feature's number is turned into a part, a column and a
row of the matrix (the library's featAt, afPart) is not. dimOf fills with 0 the fields that no key
of a feed-forward segment reads, those of featAt among them. wordsAt follows the library's reading
of the scale file (KLFile.words and Words.scale in Inst/Model/ProgTests.lean) by its text; no
theorem compares the two. sclOf has zeros for the final normalisation. The program does not import
this file.

Files named above that a package may lack. Johnson/Road/FormsKeysWorld.lean,
Johnson/Road/FormsKeysLaid.lean and Inst/Model/ProgTests.lean are in the library's full tree and are
not imported by this file; a package that is cut to what its front theorems need may not hold them.
Where they lack, what this comment says of them cannot be checked there.

-/
import Johnson.Road.FormsKeysKit

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff tenCell TenAt)
open OnBytes.Model.Layer (Env Ten Lay Shape Scales layTensors tensorAsks)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell Arr)

/-! ## The library's arguments, defined from the verifier's -/

/-- The library's sizes of a feed-forward segment, from the verifier's shape. The fields that no key
reads (the vocabulary, the scales of Params, the matrices' and the lookup's sizes) are 0. -/
def dimOf (h : Shape) : Dim where
  P := { T := 2 ^ h.lt, V := 0, layers := h.L, d := h.d, nq := h.H, nkv := h.Gk, ch := h.dh,
         f := h.f, fe := h.fe, nexp := h.NE, kq := 0, kk := 0, kv := 0, ko := 0, kg := 0, ku := 0,
         kd := 0, kr := 0, kg' := 0, ku' := 0, n1 := ⟨0, 0, 0⟩, n2 := ⟨0, 0, 0⟩, nf := ⟨0, 0, 0⟩,
         expRows := 0, sh := 0 }
  lT := h.lt
  lL := h.ll
  fBig := 0
  fAd := 0
  fAr := 0
  parts := 0
  cap := 0
  r := 0
  lp := 0

/-- The library's sizes agree with the verifier's shape: the nine numbers that the keys, the places
of the cells and the record Fits read. -/
structure Sized (h : Shape) (D : Dim) : Prop where
  /-- the width of the stream -/
  d : D.P.d = h.d
  /-- the hidden units of a layer -/
  f : D.P.f = h.f
  /-- the hidden units of one expert -/
  fe : D.P.fe = h.fe
  /-- the experts -/
  nexp : D.P.nexp = h.NE
  /-- the query heads -/
  nq : D.P.nq = h.H
  /-- the key heads -/
  nkv : D.P.nkv = h.Gk
  /-- the width of a head -/
  ch : D.P.ch = h.dh
  /-- the logarithm of the number of positions -/
  lT : D.lT = h.lt
  /-- the logarithm of the number of layers in a group -/
  lL : D.lL = h.ll

/-- dimOf agrees with the shape. -/
theorem sized_dimOf (h : Shape) : Sized h (dimOf h) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The library's reference sizes agree with a shape that has the reference's nine numbers. -/
theorem sized_ref {h : Shape} (hd : h.d = Inst.Model.ppref.d) (hf : h.f = Inst.Model.ppref.f)
    (hfe : h.fe = Inst.Model.ppref.fe) (hNE : h.NE = Inst.Model.ppref.nexp)
    (hH : h.H = Inst.Model.ppref.nq) (hG : h.Gk = Inst.Model.ppref.nkv)
    (hdh : h.dh = Inst.Model.ppref.ch) (hlt : h.lt = Dim.ref.lT) (hll : h.ll = Dim.ref.lL) :
    Sized h Dim.ref :=
  ⟨hd.symm, hf.symm, hfe.symm, hNE.symm, hH.symm, hG.symm, hdh.symm, hlt.symm, hll.symm⟩

namespace Sized

variable {h : Shape} {D : Dim} (Z : Sized h D)
include Z

theorem nl_eq : D.nl = (dimOf h).nl := by unfold Dim.nl; rw [Z.lL]; rfl
theorem ne_eq : D.ne = (dimOf h).ne := by unfold Dim.ne; rw [Z.nl_eq]
theorem nNu_eq : D.nNu = (dimOf h).nNu := by unfold Dim.nNu; rw [Z.nl_eq]
theorem d_eq : D.d = (dimOf h).d := Z.d
theorem f_eq : D.f = (dimOf h).f := Z.f
theorem fe_eq : D.fe = (dimOf h).fe := Z.fe
theorem nx_eq : D.nx = (dimOf h).nx := Z.nexp
theorem dq_eq : D.dq = (dimOf h).dq := by unfold Dim.dq; rw [Z.nq, Z.ch]; rfl
theorem dkv_eq : D.dkv = (dimOf h).dkv := by unfold Dim.dkv; rw [Z.nkv, Z.ch]; rfl
theorem dqk_eq : D.dqk = (dimOf h).dqk := by unfold Dim.dqk; rw [Z.dq_eq, Z.dkv_eq]

/-- An array has as many instances at D as at dimOf h. -/
theorem cnt_eq (X : Arr) : X.cnt D = X.cnt (dimOf h) := by
  cases X <;> simp only [Arr.cnt, Z.nl_eq, Z.ne_eq, Z.nNu_eq]

/-- And as many channels. -/
theorem width_eq (X : Arr) : X.width D = X.width (dimOf h) := by
  cases X <;> simp only [Arr.width, Z.f_eq, Z.d_eq, Z.dqk_eq, Z.dq_eq, Z.dkv_eq, Z.nx_eq]

/-- The library's rule gives a cell the same feature at D as at dimOf h. -/
theorem feat_eq (X : Arr) (k inst j : ℕ) :
    Inst.Model.FFSeg.feat D X k inst j = Inst.Model.FFSeg.feat (dimOf h) X k inst j := by
  have e : Arr.nFeat D = Arr.nFeat (dimOf h) := by
    funext Y
    unfold Arr.nFeat
    rw [Z.cnt_eq, Z.width_eq]
  unfold Inst.Model.FFSeg.feat Inst.Model.FFSeg.OFF
  rw [e, Z.cnt_eq, Z.width_eq]

end Sized

/-- The library's scales of one layer, from the verifier's scale file: the words of layer L of the
model. Which word of a layer's record is which shift is said here, once, for all families. As in the
library's own reading of the file, an even layer, which has no router and no routed expert, gets 17,
16 and 20 for their three shifts, and the exponential has 2,307 rows. The field sh is word 11 of the
record, which holds a shift at profile 4 alone; no key of a feed-forward segment reads it. -/
def wordsAt (h : Shape) (sc : Scales) (L : ℕ) : Inst.Model.LayerScale :=
  { kq := sc.kl L Model.Layer.Lkq, kk := sc.kl L Model.Layer.Lkk, kv := sc.kl L Model.Layer.Lkv,
    ko := sc.kl L Model.Layer.Lko, kg := sc.kl L Model.Layer.Lkg, ku := sc.kl L Model.Layer.Lku,
    kd := sc.kl L Model.Layer.Lkd, kr := if L % 2 = 1 then sc.klM L 0 else 17,
    kg' := if L % 2 = 1 then sc.klM L 1 else 16, ku' := if L % 2 = 1 then sc.klM L 2 else 20,
    n1 := ⟨sc.kl L Model.Layer.LM1, sc.kl L Model.Layer.LK1, h.eps1⟩,
    n2 := ⟨sc.kl L Model.Layer.LM2, sc.kl L Model.Layer.LK2, h.eps2⟩,
    expRows := 2307, sh := sc.klSh L }

/-- The library's table of scales for the group g of Lam layers: layer l of the group has the words
of layer g Lam + l of the model. Past the group's last layer the group's words are repeated: the
library's theorems ask for lawful words at every number, and the verifier's scale file has an
end. -/
@[reducible] def sclOf (h : Shape) (sc : Scales) (g Lam : ℕ) : Scl where
  κ l := wordsAt h sc (g * Lam + l % Lam)
  nf := ⟨0, 0, 0⟩

/-- The number of the verifier's matrix that holds an array: 0 af, 1 ad, 2 ar, 3 qa; 4 and 5, by the
choice of Johnson/Road/FormsKeysKit.lean, for the two matrices at the borders of the stream. -/
def matNo : Arr → ℕ
  | .a | .m | .xr => 1
  | .lr | .rl | .sel | .sc | .D | .ly | .l3 => 2
  | .q | .kx | .v | .o => 3
  | .x0 => 4
  | .x8 => 5
  | _ => 0

/-- The number that Johnson/Road/FormsKeysKit.lean gives to the library's matrix. -/
def mxNo : Inst.Model.FFSeg.Mx → ℕ
  | .af => 0 | .ad => 1 | .ar => 2 | .qa => 3 | .xin => 4 | .xout => 5 | .b => 6

/-- An array's matrix is the library's. -/
theorem matNo_eq (X : Arr) : matNo X = mxNo X.mx := by cases X <;> rfl

/-- The library's names of cells, read in the cells c of the verifier's matrices by the library's
own rule: the cell ⟨X, k, inst, j, i⟩ is the cell of the array's matrix at the feature
feat D X k inst j and the position i. -/
def cellsOf {K : Type} (D : Dim) (c : Cells K) : Cell → K := fun q =>
  c (mxNo q.X.mx) (Inst.Model.FFSeg.feat D q.X q.k q.inst q.j) q.i

/-- The table of scales that sclOf defines is lawful in the library's sense, at every number, as
soon as the words of the group's own layers are. So the record Fits and the library's class Lawful
can hold of one table, though the verifier's scale file has an end. The library's LawfulW is written
at the reference sizes: a scale file that the verifier admits at other sizes need not meet it. -/
theorem lawful_sclOf (h : Shape) (sc : Scales) (g Lam : ℕ) (hLam : 0 < Lam)
    (H : ∀ l, l < Lam → Inst.Model.FFSeg.LawfulW ((sclOf h sc g Lam).κ l)) :
    Inst.Model.FFSeg.Lawful (scl := sclOf h sc g Lam) := by
  refine Inst.Model.FFSeg.Lawful.mk (scl := sclOf h sc g Lam) fun l => ?_
  have e : (sclOf h sc g Lam).κ l = (sclOf h sc g Lam).κ (l % Lam) := by
    show wordsAt h sc (g * Lam + l % Lam) = wordsAt h sc (g * Lam + l % Lam % Lam)
    rw [Nat.mod_mod]
  show Inst.Model.FFSeg.LawfulW ((sclOf h sc g Lam).κ l)
  rw [e]
  exact H _ (Nat.mod_lt _ hLam)

/-! ## The hypotheses that are left -/

/-- The switches and digit forms for which the library has keys. -/
structure Switches (h : Shape) : Prop where
  p3 : h.p3 = true
  gcl : h.gcl = true
  rcl : h.rcl = true
  xl : h.xl = 5
  hq : h.hq = 2
  hv : h.hv = 1
  ho : h.ho = 1
  hgD : h.hgD = 1
  huD : h.huD = 1
  hdD : h.hdD = 1
  hr : h.hr = 1

/-- Plain facts on a layout's numbers. Each is the text of a line of layoutBase
(OnBytes/Model/LayerLayout.lean), or follows from one of its tests. -/
structure Laid (y : Lay) : Prop where
  /-- a block has 2^ls features -/
  S2 : y.S2 = 2 ^ y.ls
  /-- a group has at least two layers -/
  ll : 1 ≤ y.h.ll
  /-- the layers of a group, and those with routed experts -/
  Lam : y.Lam = 2 ^ y.h.ll
  LamM : y.LamM = 2 ^ y.h.ll / 2
  /-- two writes to the stream and two norms in a layer -/
  NW : y.NW = 2
  NN : y.NN = 2
  /-- the widths of queries, of keys, and of both -/
  dq : y.dq = y.h.H * y.h.dh
  dkv : y.dkv = y.h.Gk * y.h.dh
  nqk : y.nqk = y.h.H * y.h.dh + y.h.Gk * y.h.dh
  /-- the widths are whole numbers of blocks -/
  bd : y.S2 ∣ y.h.d
  bf : y.S2 ∣ y.h.f
  bfe : y.S2 ∣ y.h.fe
  bdq : y.S2 ∣ y.h.H * y.h.dh
  bdkv : y.S2 ∣ y.h.Gk * y.h.dh
  /-- with routed experts a layer's hidden units are the shared expert's and the routed one's -/
  ffe : y.h.f = 2 * y.h.fe
  /-- the tensors are laid by layTensors from the list tensorAsks -/
  ten : y.ten = (layTensors (tensorAsks y.h (2 ^ y.h.ll) (2 ^ y.h.ll / 2)
    (y.h.H * y.h.dh + y.h.Gk * y.h.dh) (y.h.H * y.h.dh) (y.h.Gk * y.h.dh)) #[0, 0, 0, 0]).1
  /-- the one tensor of a matrix of the residual stream -/
  xb : y.xb = ⟨0, y.h.xl, 1, y.h.d⟩

/-- Six families of tables are found under their names. -/
structure Found (v : Env) : Prop where
  af : ∃ b, v.tabAt ("af" ++ "@" ++ "Z") = some b
  qa : ∃ b, v.tabAt ("qa" ++ "@" ++ "Z") = some b
  xi : ∃ b, v.tabAt ("xbI" ++ "@" ++ "Z") = some b
  xo : ∃ b, v.tabAt ("xbO" ++ "@" ++ "Z") = some b
  ad : ∃ b, v.tabAt ("ad" ++ "@" ++ "zt") = some b
  ar : ∃ b, v.tabAt ("ar" ++ "@" ++ "zt") = some b

/-- The entries of these six families are true in the world W: the long tables of af, qa and the two
matrices of the stream at the point (low | u), the short tables of ad and ar at the point u. This is
all that the record Fits asks of the world. -/
structure TrueAt {K : Type} [Field K] (ρ : Reading K) (W : World K) (v : Env) (lT : ℕ)
    (c : Cells K) (low u : ℕ → K) : Prop where
  af : ∀ b, v.tabAt ("af" ++ "@" ++ "Z") = some b → LongTrue ρ W v b 0 v.y.ls lT c low u
  qa : ∀ b, v.tabAt ("qa" ++ "@" ++ "Z") = some b → LongTrue ρ W v b 3 v.y.ls lT c low u
  xi : ∀ b, v.tabAt ("xbI" ++ "@" ++ "Z") = some b → LongTrue ρ W v b 4 v.y.ls lT c low u
  xo : ∀ b, v.tabAt ("xbO" ++ "@" ++ "Z") = some b → LongTrue ρ W v b 5 v.y.ls lT c low u
  ad : ∀ b, v.tabAt ("ad" ++ "@" ++ "zt") = some b → ShortTrue ρ W v b 1 lT c u
  ar : ∀ b, v.tabAt ("ar" ++ "@" ++ "zt") = some b → ShortTrue ρ W v b 2 lT c u

/-- Six families of tables are found under their names, and their entries are true: the long tables
of af, qa and the two matrices of the stream at the point (low | u), the short tables of ad and ar
at the point u. -/
structure Tabs {K : Type} [Field K] (ρ : Reading K) (W : World K) (v : Env) (lT : ℕ) (c : Cells K)
    (low u : ℕ → K) : Prop where
  af : ∃ b, v.tabAt ("af" ++ "@" ++ "Z") = some b ∧ LongTrue ρ W v b 0 v.y.ls lT c low u
  qa : ∃ b, v.tabAt ("qa" ++ "@" ++ "Z") = some b ∧ LongTrue ρ W v b 3 v.y.ls lT c low u
  xi : ∃ b, v.tabAt ("xbI" ++ "@" ++ "Z") = some b ∧ LongTrue ρ W v b 4 v.y.ls lT c low u
  xo : ∃ b, v.tabAt ("xbO" ++ "@" ++ "Z") = some b ∧ LongTrue ρ W v b 5 v.y.ls lT c low u
  ad : ∃ b, v.tabAt ("ad" ++ "@" ++ "zt") = some b ∧ ShortTrue ρ W v b 1 lT c u
  ar : ∃ b, v.tabAt ("ar" ++ "@" ++ "zt") = some b ∧ ShortTrue ρ W v b 2 lT c u

/-- Found and true together. -/
theorem tabs_of {K : Type} [Field K] {ρ : Reading K} {W : World K} {v : Env} {lT : ℕ} {c : Cells K}
    {low u : ℕ → K} (Fd : Found v) (T : TrueAt ρ W v lT c low u) : Tabs ρ W v lT c low u where
  af := Fd.af.imp fun b hb => ⟨hb, T.af b hb⟩
  qa := Fd.qa.imp fun b hb => ⟨hb, T.qa b hb⟩
  xi := Fd.xi.imp fun b hb => ⟨hb, T.xi b hb⟩
  xo := Fd.xo.imp fun b hb => ⟨hb, T.xo b hb⟩
  ad := Fd.ad.imp fun b hb => ⟨hb, T.ad b hb⟩
  ar := Fd.ar.imp fun b hb => ⟨hb, T.ar b hb⟩

/-- The part of Tabs that does not speak of the world. -/
theorem Tabs.found {K : Type} [Field K] {ρ : Reading K} {W : World K} {v : Env} {lT : ℕ}
    {c : Cells K} {low u : ℕ → K} (T : Tabs ρ W v lT c low u) : Found v where
  af := T.af.imp fun _ h => h.1
  qa := T.qa.imp fun _ h => h.1
  xi := T.xi.imp fun _ h => h.1
  xo := T.xo.imp fun _ h => h.1
  ad := T.ad.imp fun _ h => h.1
  ar := T.ar.imp fun _ h => h.1

/-! ## How layTensors lays a tensor -/

/-- Adding to one member of an array of numbers keeps a divisor of all the members that are
looked at, if it divides what is added. -/
theorem dvd_getD_modify (S : ℕ) (off : Array ℕ) (mat m x : ℕ) (h1 : S ∣ off.getD m 0)
    (h2 : m = mat → S ∣ x) : S ∣ (off.modify mat (· + x)).getD m 0 := by
  by_cases hm : m < off.size
  · by_cases e : mat = m
    · subst e
      have h1' : S ∣ off[mat] := by simpa [Array.getD, hm] using h1
      simpa [Array.getD, hm, Array.getElem_modify] using Nat.dvd_add h1' (h2 rfl)
    · simpa [Array.getD, hm, Array.getElem_modify, e] using h1
  · simp [Array.getD, hm]

/-- The tensor that the layout finds under a name is the first ask of that name with a limb, with
that ask's matrix, limbs, instances and features. If S divides the first free feature of every good
matrix and the features of every ask in a good matrix, it divides the tensor's first feature. -/
theorem layTensors_find (S : ℕ) (good : ℕ → Prop) :
    ∀ (asks : List (String × ℕ × ℕ × ℕ × ℕ)) (off : Array ℕ),
      (∀ m, good m → S ∣ off.getD m 0) → (∀ a ∈ asks, good a.2.1 → S ∣ a.2.2.2.2) →
      ∀ (n : String) (a : String × ℕ × ℕ × ℕ × ℕ),
        asks.find? (fun a => a.1 == n && a.2.2.1 != 0) = some a →
        ∃ OFF, (layTensors asks off).1.find? (fun t => t.name == n) =
            some ⟨a.1, a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2, OFF⟩ ∧ (good a.2.1 → S ∣ OFF)
  | [], _, _, _, _, _, h => by simp at h
  | (n', mat, nl, cnt, J) :: rest, off, ho, hJ, n, a, h => by
    have hJ' : ∀ a ∈ rest, good a.2.1 → S ∣ a.2.2.2.2 :=
      fun a ha => hJ a (List.mem_cons_of_mem _ ha)
    by_cases hnl : nl = 0
    · subst hnl
      have e : layTensors ((n', mat, 0, cnt, J) :: rest) off = layTensors rest off := rfl
      rw [e]
      refine layTensors_find S good rest off ho hJ' n a ?_
      simpa [List.find?_cons] using h
    · have hb : (nl == 0) = false := by simpa using hnl
      have e : layTensors ((n', mat, nl, cnt, J) :: rest) off =
          (⟨n', mat, nl, cnt, J, off.getD mat 0⟩ ::
              (layTensors rest (off.modify mat (· + nl * cnt * J))).1,
            (layTensors rest (off.modify mat (· + nl * cnt * J))).2) := by
        show (if nl == 0 then _ else _) = _
        rw [hb]
        rfl
      rw [e]
      by_cases hn : (n' == n) = true
      · have ha : a = (n', mat, nl, cnt, J) := by
          simpa [List.find?_cons, hn, hnl] using h.symm
        subst ha
        exact ⟨off.getD mat 0, by simp [hn], fun hg => ho mat hg⟩
      · have hn' : (n' == n) = false := by simpa using hn
        have h' : rest.find? (fun a => a.1 == n && a.2.2.1 != 0) = some a := by
          simpa [List.find?_cons, hn'] using h
        obtain ⟨OFF, h1, h2⟩ := layTensors_find S good rest (off.modify mat (· + nl * cnt * J))
          (fun m hm => dvd_getD_modify S off mat m _ (ho m hm) (fun em =>
            Dvd.dvd.mul_left (hJ (n', mat, nl, cnt, J) List.mem_cons_self (em ▸ hm)) _))
          hJ' n a h'
        exact ⟨OFF, by simpa [List.find?_cons, hn'] using h1, h2⟩

/-! ## The list of tensors under the switches -/

/-- The verifier's list of tensors under the switches, written with the library's sizes: name,
matrix, limbs, instances, features. -/
def asksRef (h : Shape) (D : Dim) : List (String × ℕ × ℕ × ℕ × ℕ) :=
  [("g0", 0, 1, D.nl, D.f), ("gc", 0, 1, D.nl, D.f), ("s", 0, 2, D.nl, D.f), ("u", 0, 2, D.nl, D.f),
   ("rg", 0, 1, D.nl, D.f), ("ru", 0, 1, D.nl, D.f), ("xs", 0, 5, 2 * D.nl - 1, D.d),
   ("ro", 0, 1, D.nl, D.d), ("rd", 0, 1, D.nl, D.d), ("aw", 0, 2, D.nl, D.d),
   ("ra", 0, 2, D.nl, D.d), ("mw", 0, 2, D.nl, D.d), ("rm", 0, 2, D.nl, D.d),
   ("qkw", 0, 2, D.nl, D.dqk), ("rqk", 0, 2, D.nl, D.dqk), ("vw", 0, 2, D.nl, D.dkv),
   ("rv", 0, 1, D.nl, D.dkv), ("gh", 0, 2, D.nl, D.f), ("a", 1, 2, D.nl, D.d),
   ("m", 1, 2, D.nl, D.d), ("xr", 1, 2, D.ne, D.d), ("lr", 2, 2, D.ne, D.nx),
   ("rl", 2, 1, D.ne, D.nx), ("sel", 2, 1, D.ne, D.nx), ("sc", 2, 3, D.ne, 1),
   ("row", 2, 1, 2 * D.nl, 99), ("ly", 2, 2, D.ne, D.nx), ("l3", 2, 1, D.ne, D.nx),
   ("q", 3, 2, D.nl, D.dq), ("kx", 3, 2, D.nl, D.dkv), ("v", 3, 2, D.nl, D.dkv)] ++
  (if h.p4 then [("o", 3, 2, D.nl, D.dq)] else [])

/-- Under the switches the verifier's list of tensors is that list. -/
theorem tensorAsks_ref (h : Shape) (S : Switches h) :
    tensorAsks h (2 ^ h.ll) (2 ^ h.ll / 2) (h.H * h.dh + h.Gk * h.dh) (h.H * h.dh) (h.Gk * h.dh) =
      asksRef h (dimOf h) := by
  unfold tensorAsks asksRef
  rw [S.gcl, S.p3, S.rcl, S.xl, S.hq, S.hv, S.ho, S.hgD, S.huD, S.hdD, S.hr]
  rfl

/-- True for an array that has a tensor in the verifier's list whatever the profile. -/
def listed (X : Arr) : Bool := readLong X || readShort X || X == .D

/-- An array has a tensor in the verifier's list at the shape h: the attention output o at profile 4
alone. The two arrays at the borders of the stream have none. -/
def inList (h : Shape) (X : Arr) : Prop := listed X = true ∨ (X = .o ∧ h.p4 = true)

/-- The first ask under an array's name has the library's matrix, cells, instances and width. -/
theorem find_ask (h : Shape) (D : Dim) (X : Arr) (hX : inList h X) :
    (asksRef h D).find? (fun a => a.1 == arrName X && a.2.2.1 != 0) =
      some (arrName X, matNo X, X.nCell, X.cnt D, X.width D) := by
  rcases hX with hX | ⟨rfl, hp⟩
  · cases X <;> first | rfl | exact absurd hX (by decide)
  · unfold asksRef
    rw [if_pos hp]
    rfl

/-- In the matrices af and qa every tensor's features are a whole number of blocks. -/
theorem asksRef_dvd (h : Shape) (D : Dim) (S : ℕ) (hf : S ∣ D.f) (hd : S ∣ D.d) (hqk : S ∣ D.dqk)
    (hkv : S ∣ D.dkv) (hq : S ∣ D.dq) :
    ∀ a ∈ asksRef h D, (a.2.1 = 0 ∨ a.2.1 = 3) → S ∣ a.2.2.2.2 := by
  intro a ha hg
  unfold asksRef at ha
  rw [List.mem_append] at ha
  rcases ha with ha | ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hf | exact hd | exact hqk | exact hkv | exact hq | exact absurd hg (by simp)
  · by_cases hp : h.p4 = true
    · rw [if_pos hp] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha
      exact hq
    · rw [if_neg hp] at ha
      simp at ha

/-- What an admitted layout's tensor of an array is: found under the array's name, in the array's
matrix, with the library's numbers of cells, instances and channels; in af and qa it begins at a
whole block. -/
theorem ten_of {y : Lay} (L : Laid y) (S : Switches y.h) (X : Arr) (hX : inList y.h X) :
    ∃ ten : Ten, y.T_ (arrName X) = some ten ∧ ten.mat = matNo X ∧ ten.nl = X.nCell ∧
      ten.cnt = X.cnt (dimOf y.h) ∧ ten.J = X.width (dimOf y.h) ∧
      ((matNo X = 0 ∨ matNo X = 3) → y.S2 ∣ ten.OFF) := by
  have hqk : y.S2 ∣ (dimOf y.h).dqk := Nat.dvd_add L.bdq L.bdkv
  obtain ⟨OFF, h1, h2⟩ := layTensors_find y.S2 (fun m => m = 0 ∨ m = 3) (asksRef y.h (dimOf y.h))
    #[0, 0, 0, 0] (by rintro m (rfl | rfl) <;> exact Nat.dvd_zero _)
    (asksRef_dvd y.h (dimOf y.h) y.S2 L.bf L.bd hqk L.bdkv L.bdq) (arrName X) _
    (find_ask y.h (dimOf y.h) X hX)
  refine ⟨⟨arrName X, matNo X, X.nCell, X.cnt (dimOf y.h), X.width (dimOf y.h), OFF⟩, ?_, rfl, rfl,
    rfl, rfl, fun hg => h2 hg⟩
  unfold Lay.T_
  rw [L.ten, tensorAsks_ref _ S]
  exact h1

/-! ## Where a tensor lies: the verifier's rule against the library's -/

/-- The features that the asks of one matrix take before the first ask of the name n that has a
limb. -/
def offBefore : List (String × ℕ × ℕ × ℕ × ℕ) → String → ℕ → ℕ
  | [], _, _ => 0
  | (n', mat', nl, cnt, J) :: rest, n, mat =>
    if nl == 0 then offBefore rest n mat
    else if n' == n then 0
    else if mat' = mat then nl * cnt * J + offBefore rest n mat
    else offBefore rest n mat

/-- Adding to one member of an array of numbers, read at any member. -/
theorem getD_modify_add (off : Array ℕ) (mat m x : ℕ) (hm : mat < off.size) :
    (off.modify mat (· + x)).getD m 0 = if mat = m then off.getD m 0 + x else off.getD m 0 := by
  by_cases e : mat = m
  · subst e
    simp [Array.getD, hm, Array.getElem_modify]
  · by_cases h : m < off.size
    · simp [Array.getD, h, Array.getElem_modify, e]
    · simp [Array.getD, h, e]

/-- The first feature of the tensor that the layout finds under a name: the matrix's first free
feature, plus what the earlier asks of that matrix take. -/
theorem layTensors_off :
    ∀ (asks : List (String × ℕ × ℕ × ℕ × ℕ)) (off : Array ℕ), (∀ a ∈ asks, a.2.1 < off.size) →
      ∀ (n : String) (a : String × ℕ × ℕ × ℕ × ℕ),
        asks.find? (fun a => a.1 == n && a.2.2.1 != 0) = some a →
        ∀ ten : Ten, (layTensors asks off).1.find? (fun t => t.name == n) = some ten →
          ten.OFF = off.getD a.2.1 0 + offBefore asks n a.2.1
  | [], _, _, _, _, h, _, _ => by simp at h
  | (n', mat, nl, cnt, J) :: rest, off, hs, n, a, h, ten, ht => by
    have hs' : ∀ a ∈ rest, a.2.1 < off.size := fun a ha => hs a (List.mem_cons_of_mem _ ha)
    by_cases hnl : nl = 0
    · subst hnl
      have e : layTensors ((n', mat, 0, cnt, J) :: rest) off = layTensors rest off := rfl
      have eo : offBefore ((n', mat, 0, cnt, J) :: rest) n a.2.1 = offBefore rest n a.2.1 := rfl
      rw [e] at ht
      rw [eo]
      exact layTensors_off rest off hs' n a (by simpa [List.find?_cons] using h) ten ht
    · have hb : (nl == 0) = false := by simpa using hnl
      have e : layTensors ((n', mat, nl, cnt, J) :: rest) off =
          (⟨n', mat, nl, cnt, J, off.getD mat 0⟩ ::
              (layTensors rest (off.modify mat (· + nl * cnt * J))).1,
            (layTensors rest (off.modify mat (· + nl * cnt * J))).2) := by
        show (if nl == 0 then _ else _) = _
        rw [hb]
        rfl
      rw [e] at ht
      by_cases hn : (n' == n) = true
      · have ha : a = (n', mat, nl, cnt, J) := by
          simpa [List.find?_cons, hn, hnl] using h.symm
        subst ha
        have hten : ten = ⟨n', mat, nl, cnt, J, off.getD mat 0⟩ := by
          simpa [List.find?_cons, hn] using ht.symm
        have eo : offBefore ((n', mat, nl, cnt, J) :: rest) n mat = 0 := by
          show (if nl == 0 then _ else if n' == n then 0 else _) = 0
          rw [hb, hn]
          rfl
        rw [hten]
        show off.getD mat 0 = off.getD mat 0 + offBefore ((n', mat, nl, cnt, J) :: rest) n mat
        rw [eo, Nat.add_zero]
      · have hn' : (n' == n) = false := by simpa using hn
        have h' : rest.find? (fun a => a.1 == n && a.2.2.1 != 0) = some a := by
          simpa [List.find?_cons, hn'] using h
        have ht' : (layTensors rest (off.modify mat (· + nl * cnt * J))).1.find?
            (fun t => t.name == n) = some ten := by
          simpa [List.find?_cons, hn'] using ht
        have ih := layTensors_off rest (off.modify mat (· + nl * cnt * J))
          (fun a ha => by simpa using hs' a ha) n a h' ten ht'
        have eo : offBefore ((n', mat, nl, cnt, J) :: rest) n a.2.1 =
            if mat = a.2.1 then nl * cnt * J + offBefore rest n a.2.1
            else offBefore rest n a.2.1 := by
          show (if nl == 0 then _ else if n' == n then 0 else _) = _
          rw [hb, hn']
          rfl
        rw [ih, eo, getD_modify_add off mat a.2.1 _ (hs _ List.mem_cons_self)]
        split_ifs <;> omega

/-- Before an array's tensor the verifier's list takes, in the array's matrix, as many features as
the library's list of arrays does. -/
theorem offBefore_ref (h : Shape) (D : Dim) (X : Arr) (hX : inList h X) :
    offBefore (asksRef h D) (arrName X) (matNo X) = Inst.Model.FFSeg.OFF D X := by
  rcases hX with hX | ⟨rfl, hp⟩
  · cases X <;> first | rfl | exact absurd hX (by decide)
  · unfold asksRef
    rw [if_pos hp]
    rfl

/-- Every ask names one of the four matrices. -/
theorem asksRef_mat (h : Shape) (D : Dim) : ∀ a ∈ asksRef h D, a.2.1 < 4 := by
  intro a ha
  unfold asksRef at ha
  rw [List.mem_append] at ha
  rcases ha with ha | ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · by_cases hp : h.p4 = true
    · rw [if_pos hp] at ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      subst ha
      simp
    · rw [if_neg hp] at ha
      simp at ha

/-- The feature of a cell by the verifier's rule is its feature by the library's. In a layout with
the facts Laid, under the switches, for every array X that has a tensor in the verifier's list (31
arrays at every profile, the attention output o at profile 4) and all sizes D that agree with the
shape: the feature that the verifier's rule gives to limb k, instance inst and channel j of the
tensor is the feature that the library's rule (feat) gives to that cell, and the tensor lies in the
library's matrix. Only the feature's number is compared, not its part, column and row. -/
theorem place_eq_feat {y : Lay} (L : Laid y) (S : Switches y.h) {D : Dim} (Z : Sized y.h D)
    (X : Arr) (hX : inList y.h X) {ten : Ten} (hT : y.T_ (arrName X) = some ten) (k inst j : ℕ) :
    tenCell ten.place k inst j = Inst.Model.FFSeg.feat D X k inst j ∧ ten.mat = mxNo X.mx := by
  obtain ⟨ten', hT', hm, _, hc, hJ, _⟩ := ten_of L S X hX
  have e : ten' = ten := by
    rw [hT'] at hT
    exact Option.some.inj hT
  subst e
  have hfind : (layTensors (asksRef y.h (dimOf y.h)) #[0, 0, 0, 0]).1.find?
      (fun t => t.name == arrName X) = some ten' := by
    have h1 := hT'
    unfold Lay.T_ at h1
    rw [L.ten, tensorAsks_ref _ S] at h1
    exact h1
  have hoff := layTensors_off (asksRef y.h (dimOf y.h)) #[0, 0, 0, 0]
    (asksRef_mat y.h (dimOf y.h)) (arrName X) _ (find_ask y.h (dimOf y.h) X hX) ten' hfind
  have hz : (#[0, 0, 0, 0] : Array ℕ).getD (matNo X) 0 = 0 := by cases X <;> rfl
  refine ⟨?_, by rw [hm, matNo_eq]⟩
  rw [Z.feat_eq]
  show ten'.OFF + (k * ten'.cnt + inst) * ten'.J + j = _
  rw [hoff, hc, hJ]
  show (#[0, 0, 0, 0] : Array ℕ).getD (matNo X) 0 +
    offBefore (asksRef y.h (dimOf y.h)) (arrName X) (matNo X) + _ + j = _
  rw [hz, offBefore_ref _ _ X hX, Nat.zero_add]
  rfl

/-- The same for the two matrices at the borders of the residual stream. -/
theorem xb_eq_feat {y : Lay} (L : Laid y) {D : Dim} (Z : Sized y.h D) (k inst j : ℕ) :
    tenCell y.xb k inst j = Inst.Model.FFSeg.feat D .x0 k inst j ∧
      tenCell y.xb k inst j = Inst.Model.FFSeg.feat D .x8 k inst j := by
  rw [L.xb, Z.feat_eq, Z.feat_eq]
  exact ⟨rfl, rfl⟩

/-! ## The record -/

section Record

variable {K : Type} [Field K] {ρ : Reading K} {W : World K}

/-- The verifier finds a tensor with its tables, if the layout has the tensor and the tables of its
matrix at the point are there. -/
theorem tensorAt_of {v : Env} {n Z : String} {ten : Ten} {b : ℕ} (hT : v.y.T_ n = some ten)
    (hb : v.tabAt (Env.mname ten.mat ++ "@" ++ Z) = some b) : v.tensorAt n Z = some (ten, b) := by
  unfold Env.tensorAt
  rw [hT]
  show (do let tb ← v.tabAt (Env.mname ten.mat ++ "@" ++ Z); pure (ten, tb)) = _
  rw [hb]
  rfl

omit [Field K] in
/-- The names of cells that cellsOf defines by the library's rule are tied to the places of the
verifier's tensor: by place_eq_feat. -/
theorem tied_cellsOf {y : Lay} (L : Laid y) (S : Switches y.h) {D : Dim} (Z : Sized y.h D)
    (c : Cells K) {X : Arr} {ten : Ten} (hX : inList y.h X) (hT : y.T_ (arrName X) = some ten)
    (hn : ten.nl = X.nCell) : Tied c (cellsOf D c) X ten.mat ten.place := by
  refine ⟨hn, fun k inst j i => ?_⟩
  obtain ⟨e1, e2⟩ := place_eq_feat L S Z X hX hT k inst j
  show c (mxNo X.mx) (Inst.Model.FFSeg.feat D X k inst j) i = _
  rw [e1, e2]

/-- The record reads of the library's sizes only what Sized fixes: it passes from dimOf to any sizes
that agree with the shape. -/
theorem Fits.sized [scl : Scl] {v : Env} {D : Dim} {c : Cells K} {t : Cell → K} {low u : ℕ → K}
    (F : Fits ρ W v (dimOf v.y.h) c t low u) (Z : Sized v.y.h D) : Fits ρ W v D c t low u := by
  have hn : ∀ {lam : ℕ}, lam < D.nl → lam < (dimOf v.y.h).nl := fun h => by
    rw [← Z.nl_eq]
    exact h
  exact
    { num := F.num, S2 := F.S2, lT := Z.lT.symm, d := Z.d.symm, f := Z.f.symm, fe := Z.fe.symm,
      NE := Z.nexp.symm, dq := F.dq.trans Z.dq_eq.symm, dkv := F.dkv.trans Z.dkv_eq.symm,
      nqk := F.nqk.trans Z.dqk_eq.symm
      bd := by rw [Z.d_eq]; exact F.bd
      bf := by rw [Z.f_eq]; exact F.bf
      bfe := by rw [Z.fe_eq]; exact F.bfe
      bdq := by rw [Z.dq_eq]; exact F.bdq
      bdkv := by rw [Z.dkv_eq]; exact F.bdkv
      ffe := by rw [Z.f_eq, Z.fe_eq]; exact F.ffe
      Lam := F.Lam.trans Z.nl_eq.symm, LamM := F.LamM.trans Z.ne_eq.symm, NN := F.NN
      last := by rw [Z.nl_eq]; exact F.last
      p3 := F.p3, gcl := F.gcl, rcl := F.rcl, xl := F.xl, hq := F.hq, hv := F.hv, ho := F.ho,
      hgD := F.hgD, huD := F.huD, hdD := F.hdD, hr := F.hr
      kq := fun lam hl => F.kq lam (hn hl), kk := fun lam hl => F.kk lam (hn hl)
      kv := fun lam hl => F.kv lam (hn hl), ko := fun lam hl => F.ko lam (hn hl)
      kg := fun lam hl => F.kg lam (hn hl), ku := fun lam hl => F.ku lam (hn hl)
      kd := fun lam hl => F.kd lam (hn hl), K1 := fun lam hl => F.K1 lam (hn hl)
      K2 := fun lam hl => F.K2 lam (hn hl), kr := fun lam hl => F.kr lam (hn hl)
      kgR := fun lam hl => F.kgR lam (hn hl), kuR := fun lam hl => F.kuR lam (hn hl)
      K1le := fun lam hl => F.K1le lam (hn hl), K2le := fun lam hl => F.K2le lam (hn hl)
      long := fun X hX => by
        have H := F.long X hX
        unfold HasLong at H ⊢
        rw [Z.lT]
        exact H
      short := fun X hX => by
        have H := F.short X hX
        unfold HasShort at H ⊢
        rw [Z.lT]
        exact H
      rowTab := by
        rw [Z.lT]
        exact F.rowTab
      stream := by
        rw [Z.lT]
        exact F.stream }

/-- A divisor that is the size of a block, written as the record writes it. -/
theorem blocks_of_dvd {y : Lay} (L : Laid y) {x : ℕ} (h : y.S2 ∣ x) : ∃ n, x = n * 2 ^ y.ls := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [hn, L.S2, Nat.mul_comm]⟩

/-- Every run of a tensor of af or qa begins at a whole block. -/
theorem aligned_of {y : Lay} {ten : Ten} (h1 : y.S2 ∣ ten.OFF) (h2 : y.S2 ∣ ten.J) (i l : ℕ) :
    y.S2 ∣ tenCell ten.place l i 0 :=
  Nat.dvd_add (Nat.dvd_add h1 (Dvd.dvd.mul_left h2 _)) (Nat.dvd_zero _)

/-- The record Fits, in any world W, at a reading that takes the program's numerals, multiples and
negatives to those of K (Numerals), from the verifier's own layout of the tensors, the switches, the
range of the norms' shifts on the group's layers, and six families of tables that are found and are
true in W. The library's sizes D are any that agree with the verifier's shape; its table of scales
is the one that sclOf defines from the verifier's scale file; its names of cells are read in the
cells c by the library's own rule (cellsOf). -/
theorem fits_of_laid (hρ : Numerals ρ) (v : Env) (L : Laid v.y) (S : Switches v.y.h)
    (hK : ∀ lam, lam < 2 ^ v.y.h.ll → 16 ≤ v.sc.kl (v.lay lam) Model.Layer.LK1 ∧
      16 ≤ v.sc.kl (v.lay lam) Model.Layer.LK2)
    {D : Dim} (Z : Sized v.y.h D) (c : Cells K) (low u : ℕ → K)
    (T : Tabs ρ W v v.y.h.lt c low u) :
    Fits (scl := sclOf v.y.h v.sc v.g v.y.Lam) ρ W v D c (cellsOf D c) low u := by
  letI : Scl := sclOf v.y.h v.sc v.g v.y.Lam
  have odd : ∀ lam, lam % 2 = 1 → v.lay lam % 2 = 1 := by
    intro lam ho
    obtain ⟨m, hm⟩ : ∃ m, v.y.Lam = 2 * m := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le L.ll
      exact ⟨2 ^ k, by rw [L.Lam, hk, pow_add, pow_one]⟩
    have e : v.lay lam = 2 * (v.g * m) + lam := by
      show v.g * v.y.Lam + lam = _
      rw [hm]
      ring
    rw [e]
    omega
  have md : ∀ lam, lam < (dimOf v.y.h).nl → v.g * v.y.Lam + lam % v.y.Lam = v.lay lam := by
    intro lam hl
    have hl' : lam < v.y.Lam := by rw [L.Lam]; exact hl
    rw [Nat.mod_eq_of_lt hl']
    rfl
  have wid : ∀ X : Arr, listed X = true → (matNo X = 0 ∨ matNo X = 3) →
      v.y.S2 ∣ X.width (dimOf v.y.h) := by
    intro X hX hm
    have hqk : v.y.S2 ∣ (dimOf v.y.h).dqk := Nat.dvd_add L.bdq L.bdkv
    cases X <;> first
      | exact L.bf | exact L.bd | exact hqk | exact L.bdkv | exact L.bdq
      | exact absurd hm (by decide)
  have long : ∀ X : Arr, readLong X = true →
      HasLong ρ W v (dimOf v.y.h) c (cellsOf D c) low u X := by
    intro X hX
    have hl : listed X = true := by unfold listed; rw [hX]; rfl
    obtain ⟨ten, hT, hm, hn, _, hJ, hO⟩ := ten_of L S X (Or.inl hl)
    have hm' : matNo X = 0 ∨ matNo X = 3 := by
      cases X <;> first | exact Or.inl rfl | exact Or.inr rfl | exact absurd hX (by decide)
    have hal := aligned_of (hO hm') (hJ ▸ wid X hl hm')
    rcases hm' with h0 | h3
    · obtain ⟨b, hb, R⟩ := T.af
      refine ⟨ten, b, tensorAt_of hT (by rw [hm, h0]; exact hb),
        tied_cellsOf L S Z c (Or.inl hl) hT hn, ?_, hal⟩
      rw [hm, h0]
      exact R
    · obtain ⟨b, hb, R⟩ := T.qa
      refine ⟨ten, b, tensorAt_of hT (by rw [hm, h3]; exact hb),
        tied_cellsOf L S Z c (Or.inl hl) hT hn, ?_, hal⟩
      rw [hm, h3]
      exact R
  have short : ∀ X : Arr, readShort X = true →
      HasShort ρ W v (dimOf v.y.h) c (cellsOf D c) u X := by
    intro X hX
    have hl : listed X = true := by unfold listed; rw [hX, Bool.or_true]; rfl
    obtain ⟨ten, hT, hm, hn, _, _, _⟩ := ten_of L S X (Or.inl hl)
    have hm' : matNo X = 1 ∨ matNo X = 2 := by
      cases X <;> first | exact Or.inl rfl | exact Or.inr rfl | exact absurd hX (by decide)
    rcases hm' with h1 | h2
    · obtain ⟨b, hb, R⟩ := T.ad
      refine ⟨ten, b, tensorAt_of hT (by rw [hm, h1]; exact hb),
        tied_cellsOf L S Z c (Or.inl hl) hT hn, ?_⟩
      rw [hm, h1]
      exact R
    · obtain ⟨b, hb, R⟩ := T.ar
      refine ⟨ten, b, tensorAt_of hT (by rw [hm, h2]; exact hb),
        tied_cellsOf L S Z c (Or.inl hl) hT hn, ?_⟩
      rw [hm, h2]
      exact R
  have rowTab : ∃ (trow : Ten) (b : ℕ), v.tabAt "ar@zt" = some b ∧ v.y.T_ "row" = some trow ∧
      trow.mat = 2 ∧ Tied c (cellsOf D c) .D trow.mat trow.place ∧ trow.J = 99 ∧
      ShortTrue ρ W v b trow.mat (dimOf v.y.h).lT c u := by
    obtain ⟨ten, hT, hm, hn, _, hJ, _⟩ := ten_of L S .D (Or.inl rfl)
    obtain ⟨b, hb, R⟩ := T.ar
    exact ⟨ten, b, hb, hT, hm, tied_cellsOf L S Z c (Or.inl rfl) hT hn, hJ, by rw [hm]; exact R⟩
  have stream : ∃ (bI bO bF : ℕ) (txs : Ten),
      v.tabAt ("xbI" ++ "@" ++ "Z") = some bI ∧ v.tabAt ("xbO" ++ "@" ++ "Z") = some bO ∧
      v.tabAt ("af" ++ "@" ++ "Z") = some bF ∧ v.y.T_ "xs" = some txs ∧ txs.mat = 0 ∧
      Tied c (cellsOf D c) .x0 4 v.y.xb ∧ Tied c (cellsOf D c) .x8 5 v.y.xb ∧
      Tied c (cellsOf D c) .xs txs.mat txs.place ∧
      LongTrue ρ W v bI 4 v.y.ls (dimOf v.y.h).lT c low u ∧
      LongTrue ρ W v bO 5 v.y.ls (dimOf v.y.h).lT c low u ∧
      LongTrue ρ W v bF txs.mat v.y.ls (dimOf v.y.h).lT c low u ∧
      (∀ l, v.y.S2 ∣ tenCell v.y.xb l 0 0) ∧ ∀ i l, v.y.S2 ∣ tenCell txs.place l i 0 := by
    obtain ⟨ten, hT, hm, hn, _, hJ, hO⟩ := ten_of L S .xs (Or.inl rfl)
    obtain ⟨bI, hI, RI⟩ := T.xi
    obtain ⟨bO, hOo, RO⟩ := T.xo
    obtain ⟨bF, hF, RF⟩ := T.af
    have hxl : v.y.xb.nl = 5 := by rw [L.xb]; exact S.xl
    have t0 : Tied c (cellsOf D c) .x0 4 v.y.xb := ⟨hxl, fun k inst j i => by
      show c 4 (Inst.Model.FFSeg.feat D .x0 k inst j) i = _
      rw [(xb_eq_feat L Z k inst j).1]⟩
    have t8 : Tied c (cellsOf D c) .x8 5 v.y.xb := ⟨hxl, fun k inst j i => by
      show c 5 (Inst.Model.FFSeg.feat D .x8 k inst j) i = _
      rw [(xb_eq_feat L Z k inst j).2]⟩
    refine ⟨bI, bO, bF, ten, hI, hOo, hF, hT, hm, t0, t8,
      tied_cellsOf L S Z c (Or.inl rfl) hT hn, RI, RO, by rw [hm]; exact RF, ?_,
      aligned_of (hO (Or.inl rfl)) (hJ ▸ L.bd)⟩
    intro l
    rw [L.xb]
    exact Nat.dvd_add (Nat.dvd_add (Nat.dvd_zero _) (Dvd.dvd.mul_left L.bd _)) (Nat.dvd_zero _)
  have F0 : Fits ρ W v (dimOf v.y.h) c (cellsOf D c) low u :=
    { num := hρ, S2 := L.S2, lT := rfl, d := rfl, f := rfl, fe := rfl, NE := rfl, dq := L.dq,
      dkv := L.dkv, nqk := L.nqk, bd := blocks_of_dvd L L.bd, bf := blocks_of_dvd L L.bf,
      bfe := blocks_of_dvd L L.bfe, bdq := blocks_of_dvd L L.bdq, bdkv := blocks_of_dvd L L.bdkv,
      ffe := by
        show v.y.h.f = v.y.h.fe + v.y.h.fe
        rw [L.ffe, Nat.two_mul]
      Lam := L.Lam, LamM := L.LamM, NN := L.NN
      last := by
        rw [L.NW, L.Lam]
        rfl
      p3 := S.p3, gcl := S.gcl, rcl := S.rcl, xl := S.xl, hq := S.hq, hv := S.hv, ho := S.ho,
      hgD := S.hgD, huD := S.huD, hdD := S.hdD, hr := S.hr,
      kq := fun lam hl => congrArg (fun l => v.sc.kl l Model.Layer.Lkq) (md lam hl).symm
      kk := fun lam hl => congrArg (fun l => v.sc.kl l Model.Layer.Lkk) (md lam hl).symm
      kv := fun lam hl => congrArg (fun l => v.sc.kl l Model.Layer.Lkv) (md lam hl).symm
      ko := fun lam hl => congrArg (fun l => v.sc.kl l Model.Layer.Lko) (md lam hl).symm
      kg := fun lam hl => congrArg (fun l => v.sc.kl l Model.Layer.Lkg) (md lam hl).symm
      ku := fun lam hl => congrArg (fun l => v.sc.kl l Model.Layer.Lku) (md lam hl).symm
      kd := fun lam hl => congrArg (fun l => v.sc.kl l Model.Layer.Lkd) (md lam hl).symm
      K1 := fun lam hl => congrArg (fun l => v.sc.kl l Model.Layer.LK1) (md lam hl).symm
      K2 := fun lam hl => congrArg (fun l => v.sc.kl l Model.Layer.LK2) (md lam hl).symm
      kr := fun lam hl ho => by
        show _ = if (v.g * v.y.Lam + lam % v.y.Lam) % 2 = 1 then
          v.sc.klM (v.g * v.y.Lam + lam % v.y.Lam) 0 else 17
        rw [md lam hl, if_pos (odd lam ho)]
      kgR := fun lam hl ho => by
        show _ = if (v.g * v.y.Lam + lam % v.y.Lam) % 2 = 1 then
          v.sc.klM (v.g * v.y.Lam + lam % v.y.Lam) 1 else 16
        rw [md lam hl, if_pos (odd lam ho)]
      kuR := fun lam hl ho => by
        show _ = if (v.g * v.y.Lam + lam % v.y.Lam) % 2 = 1 then
          v.sc.klM (v.g * v.y.Lam + lam % v.y.Lam) 2 else 20
        rw [md lam hl, if_pos (odd lam ho)]
      K1le := fun lam hl => by
        show 16 ≤ v.sc.kl (v.g * v.y.Lam + lam % v.y.Lam) Model.Layer.LK1
        rw [md lam hl]
        exact (hK lam hl).1
      K2le := fun lam hl => by
        show 16 ≤ v.sc.kl (v.g * v.y.Lam + lam % v.y.Lam) Model.Layer.LK2
        rw [md lam hl]
        exact (hK lam hl).2
      long := long, short := short, rowTab := rowTab, stream := stream }
  exact F0.sized Z

end Record

#print axioms layTensors_find
#print axioms ten_of
#print axioms sized_ref
#print axioms place_eq_feat
#print axioms xb_eq_feat
#print axioms tied_cellsOf
#print axioms Fits.sized
#print axioms fits_of_laid
#print axioms lawful_sclOf

end OnBytes.Road
