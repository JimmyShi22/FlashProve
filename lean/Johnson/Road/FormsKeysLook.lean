-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysLook.lean: the points and the weights of the lookup's calls, the verifier's
against the library's, at one point of the library.

The lookup of a layer sub-proof ends at two points: zx inside a tree and zy over the trees' numbers.
From them the verifier makes for each call a point, the last iota coordinates of zy followed by zx,
and a weight, the equality weight of the other coordinates of zy at the call's prefix (Forest.pad,
callWeight in OnBytes/Model/Look.lean). The library has one point z for the whole lookup and reads
each call's point zc and weight wc from it (Inst/Model/FF/Objects.lean).

What is compared with what: the verifier's Lean text for a call's point and weight against the
library's zc, wc and zpos, under the hypothesis that the numbers of the trees are the same
(TreesFit); and the closed forms of the numbers that Forest.shape computes against the library's eC,
NT, sg and firstTree (Inst/Model/FF/Index.lean).

Main definitions: zOf (zx, then zy, read in K), TreesFit.
Main theorems.
 - zc_of_look: each of the eight calls' points reads as zc at the ONE point zOf, on all coordinates.
 - size_of_look: it has as many coordinates as the library's call has bits.
 - wc_of_look: each call's weight reads as wc at that point.
 - zpos_of_look: the last lT coordinates of zx read as the library's token point there.
 - treesFit_of_numbers: TreesFit from the closed forms of the verifier's numbers.
 - n_of_layout: a call of a layout has as many keys as the library's call.

The hypotheses. TreesFit: Johnson/Road/FormsKeysLookT.lean concludes it from a layout whose eight
calls are the library's. hsx, hsy, hzk: the lengths of the two points, and the line of Forest.pad
that makes the calls' points, in the verifier's letters. The hypotheses hi, hN, hr, hf of
treesFit_of_numbers are the clauses of shape_numbers (Johnson/Road/FormsKeysForest.lean).
Johnson/Road/FormsKeysRunZ.lean runs all of it with the library's own definitions, at a made-up
shape and at the full-size example.
From that file's head, word for word: «zP: the point inside a tree, then the point over the trees'
numbers. […] Z1 the numbers of the trees: for each of the eight calls the logarithm of the number of
keys against aC, of the number of trees against eC, the first tree against firstTree, the prefix
against pre; the number of trees against NT, the bits of a tree's number against sg, the depth of a
tree against Dk; the call of each tree against callOf. Z2 every coordinate of every call's point
against zc at the point zP. Z3 every call's weight against wc at the point zP. Z4 the verifier's
token point against zpos at the point zP. […] Z2 and Z3 also at another point, zAlt, which is zP
where the two depths agree. What came out, and is held by the guards. Where no call is made longer
(hR8, the full-size example): all of it holds, for all eight calls, at the one point zP. At the two
shapes where some call is made longer (hR8c, the small example) no mark of Z1 to Z4 is true at zP. A
mark of Z1 speaks of all eight calls: the numbers of keys agree for the calls that are not made
longer, as the guards on the numbers show. At zAlt the points of the calls that are not made longer
are the library's. Their weights are the library's at hR8c; at the small example no call's weight
is. Why the two differ is not run.»

Which value is which: all are public: numbers, and challenges that the verifier has kept.

What is not claimed. That the verifier's arrays are made as hzk says, and have these lengths, is
asked. Nothing is said where the numbers of the trees differ. The program does not import this file.
-/
import Johnson.Road.FormsKeysShape
import Johnson.Road.FormsKeysPoint
import Johnson.Road.FormsKeysPos

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading Call CallD Seg lastOf clog2)
open OnBytes.Model.Layer (Env Lay layout)
open Inst.Model.FFSeg (Dim Fam aC eC Dk sg NT trees firstTree pre zc wc zpos call fams used lJ)

variable {K : Type} [Field K]

/-! ## Tools -/

/-- Member i of the array of the values of fn at 0 to n - 1, for values of any type. -/
theorem range_map_getD' {α : Type} (n : ℕ) (fn : ℕ → α) (d : α) {i : ℕ} (hi : i < n) :
    ((Array.range n).map fn).getD i d = fn i := by
  simp [Array.getD, hi]

/-- A member of two arrays laid end to end. -/
theorem getD_append' {α : Type} (a b : Array α) (j : ℕ) (d : α) :
    (a ++ b).getD j d = if j < a.size then a.getD j d else b.getD (j - a.size) d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_append]
  split <;> rfl

/-- A product that a fold computes in the verifier's field reads as the product of the readings. -/
theorem foldl_mul_value (ρ : Reading K) (f : ℕ → E) : ∀ n : ℕ,
    ρ.val ((List.range n).foldl (fun e i => mulE e (f i)) oneE) = ∏ i ∈ range n, ρ.val (f i)
  | 0 => by simpa using ρ.one
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, prod_range_succ, ← foldl_mul_value ρ f n]
    exact ρ.mul _ _

/-- A call has at most as many trees as there are numbers for trees. -/
theorem eC_le_sg (D : Dim) (c : Fin 8) : eC D c ≤ sg D := by
  have h1 : trees D c ≤ NT D :=
    Finset.single_le_sum (f := fun c => trees D c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  have h2 : NT D ≤ 2 ^ sg D := Nat.le_pow_clog (by norm_num) _
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_trans h1 h2)

/-! ## The library's point, from the lookup's two points -/

/-- The library's point of the whole lookup: the verifier's point inside a tree, then its point over
the trees' numbers. -/
def zOf (ρ : Reading K) (zx zy : Array E) : ℕ → K := fun t =>
  if t < zx.size then ρ.val (zx.getD t zeroE) else ρ.val (zy.getD (t - zx.size) zeroE)

/-- The numbers of the verifier's trees are the library's: the depth of a tree, the bits of a tree's
number, and for each of the eight calls the logarithm of the number of its trees and its first
tree. -/
structure TreesFit (fo : Model.Forest.Shape) (D : Dim) : Prop where
  dT : fo.dT = Dk D
  rK : fo.rK = sg D
  iota : ∀ c : Fin 8, fo.iota.getD c.val 0 = eC D c
  first : ∀ c : Fin 8, fo.first.getD c.val 0 = firstTree D c

section Look

variable {ρ : Reading K} {fo : Model.Forest.Shape} {D : Dim} {zx zy : Array E}

/-- (A) THE POINTS. If the numbers of the trees are the library's, there are eight calls (h8), the
two points have dT and rK coordinates, and the calls' points are made from them in the letters of
Forest.pad (OnBytes/Model/Look.lean), then the point of each of the eight calls reads, on all its
coordinates, as the library's point of that call at ONE point of the whole lookup. -/
theorem zc_of_look (T : TreesFit fo D) (h8 : fo.NC = 8) (hsx : zx.size = fo.dT)
    (hsy : zy.size = fo.rK) {zk : Array (Array E)}
    (hzk : zk = (Array.range fo.NC).map fun c =>
      zy.extract (fo.rK - fo.iota.getD c 0) zy.size ++ zx) (c : Fin 8) :
    ∀ j, j < aC D c → pt ρ (zk.getD c.val #[]) j = zc D (zOf ρ zx zy) c j := by
  intro j hj
  have hk : zk.getD c.val #[] = zy.extract (fo.rK - fo.iota.getD c.val 0) zy.size ++ zx := by
    rw [hzk, range_map_getD' _ _ _ (by rw [h8]; exact c.isLt)]
  have hle := eC_le_sg D c
  have hD := Inst.Model.FFSeg.IndexFacts.Dk_le D c
  have he : eC D c = aC D c - Dk D := rfl
  have hsy' : zy.size = sg D := hsy.trans T.rK
  unfold pt zc zOf
  rw [hk, T.iota, T.rK, getD_append', Array.size_extract, hsx, T.dT]
  generalize eC D c = ec at *
  generalize Dk D = k at *
  generalize aC D c = a at *
  generalize sg D = σ at *
  have hs : min zy.size zy.size - (σ - ec) = ec := by omega
  rw [hs]
  by_cases hlt : j < ec
  · have e : k + (σ - ec) + j - k = σ - ec + j := by omega
    rw [if_pos hlt, if_pos hlt, if_neg (by omega), getD_stretch zy (Nat.le_refl _) (by omega), e]
  · rw [if_neg hlt, if_neg hlt, if_pos (by omega)]

/-- Under the same hypotheses (h8: there are eight calls) the point of each call has as many
coordinates as the library's call has bits. -/
theorem size_of_look (T : TreesFit fo D) (h8 : fo.NC = 8) (hsx : zx.size = fo.dT)
    (hsy : zy.size = fo.rK) {zk : Array (Array E)}
    (hzk : zk = (Array.range fo.NC).map fun c =>
      zy.extract (fo.rK - fo.iota.getD c 0) zy.size ++ zx) (c : Fin 8) :
    (zk.getD c.val #[]).size = aC D c := by
  have hk : zk.getD c.val #[] = zy.extract (fo.rK - fo.iota.getD c.val 0) zy.size ++ zx := by
    rw [hzk, range_map_getD' _ _ _ (by rw [h8]; exact c.isLt)]
  have hle := eC_le_sg D c
  have hD := Inst.Model.FFSeg.IndexFacts.Dk_le D c
  have he : eC D c = aC D c - Dk D := rfl
  have hsy' : zy.size = sg D := hsy.trans T.rK
  rw [hk, T.iota, T.rK, Array.size_append, Array.size_extract, hsx, T.dT]
  generalize eC D c = ec at *
  generalize Dk D = k at *
  generalize aC D c = a at *
  generalize sg D = σ at *
  omega

/-- (B) THE WEIGHTS. The weight of each of the eight calls, as the lookup computes it from its point
over the trees' numbers, reads as the library's weight of the call at that one point. -/
theorem wc_of_look (T : TreesFit fo D) (hsx : zx.size = fo.dT) (c : Fin 8) :
    ρ.val (Model.Forest.callWeight fo zy c.val) = wc D (zOf ρ zx zy) c := by
  show ρ.val ((List.range (fo.rK - fo.iota.getD c.val 0)).foldl
    (fun e i => mulE e
      (if (fo.first.getD c.val 0 / 2 ^ fo.iota.getD c.val 0 /
          2 ^ (fo.rK - fo.iota.getD c.val 0 - 1 - i)) % 2 = 1
        then zy.getD i zeroE else subE oneE (zy.getD i zeroE))) oneE) = _
  rw [foldl_mul_value, T.rK, T.iota, T.first]
  unfold wc Blocks.eqN
  refine prod_congr rfl fun t _ => ?_
  have hz : zOf ρ zx zy (Dk D + t) = ρ.val (zy.getD t zeroE) := by
    unfold zOf
    rw [hsx, T.dT, if_neg (by omega), Nat.add_sub_cancel_left]
  have hp : firstTree D c / 2 ^ eC D c = pre D c := rfl
  rw [hz, hp]
  by_cases hb : (pre D c).testBit (sg D - eC D c - 1 - t) = true
  · rw [if_pos hb, if_pos ((Inst.Model.FFSeg.IndexFacts.testBit_iff _ _).mp hb)]
  · rw [if_neg hb, if_neg (fun h => hb ((Inst.Model.FFSeg.IndexFacts.testBit_iff _ _).mpr h)),
      ρ.sub, ρ.one]

/-- (D) THE TOKEN POINT. The last lT coordinates of the verifier's point inside a tree read as the
library's token point at that one point. -/
theorem zpos_of_look (T : TreesFit fo D) (hsx : zx.size = fo.dT) {zt : Array E}
    (hzt : lastOf zx D.lT = .ok zt) : ∀ j, j < D.lT → zpos D (zOf ρ zx zy) j = pt ρ zt j := by
  intro j hj
  obtain ⟨hle, e⟩ := lastOf_ok hzt
  show zOf ρ zx zy (Dk D - D.lT + j) = _
  unfold zOf pt
  rw [e, getD_stretch zx (Nat.le_refl _) (by omega), if_pos (by rw [hsx, T.dT] at *; omega), hsx,
    T.dT]

end Look

/-! ## The numbers of the trees -/

/-- The numbers of the verifier's trees are the library's, from what Forest.shape computes: hn: call
c has 2^(aC D c) keys; hd: the depth of a tree; hi, hN, hr, hf: the logarithms of the calls' numbers
of trees, the number of trees, the bits of a tree's number and the calls' first trees, as the text
of Forest.shape (OnBytes/Model/Forest.lean) makes them. -/
theorem treesFit_of_numbers {fo : Model.Forest.Shape} {D : Dim} {n : ℕ → ℕ}
    (hn : ∀ c : Fin 8, n c.val = aC D c) (hd : fo.dT = Dk D)
    (hi : ∀ c, c < 8 → fo.iota.getD c 0 = n c - fo.dT)
    (hN : fo.NT = ∑ c ∈ range 8, 2 ^ fo.iota.getD c 0) (hr : fo.rK = clog2 fo.NT)
    (hf : ∀ c, c < 8 → fo.first.getD c 0 = ∑ c' ∈ range 8,
      if fo.iota.getD c 0 < fo.iota.getD c' 0 ∨ (fo.iota.getD c' 0 = fo.iota.getD c 0 ∧ c' < c)
      then 2 ^ fo.iota.getD c' 0 else 0) : TreesFit fo D := by
  have io : ∀ c : Fin 8, fo.iota.getD c.val 0 = eC D c := by
    intro c
    rw [hi c.val c.isLt, hn, hd]
    rfl
  have hNT : fo.NT = NT D := by
    rw [hN, Finset.sum_range]
    exact Finset.sum_congr rfl fun c _ => by rw [io c]; rfl
  refine ⟨hd, ?_, io, fun c => ?_⟩
  · rw [hr, hNT]
    exact ceilLog2_eq_clog _
  · rw [hf c.val c.isLt, Finset.sum_range]
    refine Finset.sum_congr rfl fun c' _ => ?_
    have h1 := Inst.Model.FFSeg.IndexFacts.Dk_le D c
    have h2 := Inst.Model.FFSeg.IndexFacts.Dk_le D c'
    have e1 : eC D c = aC D c - Dk D := rfl
    have e2 : eC D c' = aC D c' - Dk D := rfl
    rw [io c, io c']
    refine if_congr ?_ rfl rfl
    constructor
    · rintro (h | ⟨h, hlt⟩)
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, hlt⟩
    · rintro (h | ⟨h, hlt⟩)
      · exact Or.inl (by omega)
      · exact Or.inr ⟨by omega, hlt⟩

/-- A call of a layout whose line is the library's, and whose least number of columns does not bite,
has as many keys as the library's call. The hypotheses are those of Dk_of_layout
(Johnson/Road/FormsKeysShape.lean), for one call. -/
theorem n_of_layout {h : Model.Layer.Shape} {pc : List (List String)} {v : Env}
    (hy : layout h pc = .ok v.y) (S : Switches h) {D : Dim} (Z : Sized h D) {cc : Fin 8}
    {cd : CallD} (hcq : v.y.calls[cc.val]? = some cd)
    (hn : cd.segs.map (·.name) = (fams cc).map segName)
    (hfl : h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D cc)) :
    (v.y.cl[cc.val]?).map (·.n) = some (aC D cc) := by
  have hsh := (admitted_of_layout hy S.p3).shape
  have hfl' : h.nmin - h.ll - h.lt ≤ lJ D cc := hfl
  have h2 : v.y.cl[cc.val]? = some (v.y.callRecord cc.val cd) := by
    rw [cl_of_layout hy]
    simp [hcq]
  rw [h2]
  show some (v.y.h.ll + cd.lJ + v.y.h.lt) = some (D.lL + lJ D cc + D.lT)
  rw [lJ_of_call hy S Z (Array.mem_of_getElem? hcq) hn, hsh, Z.lL, Z.lT, Nat.max_eq_left hfl']

#print axioms zc_of_look
#print axioms size_of_look
#print axioms n_of_layout
#print axioms wc_of_look
#print axioms zpos_of_look
#print axioms treesFit_of_numbers

end OnBytes.Road
