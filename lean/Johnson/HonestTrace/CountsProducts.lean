-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsProducts.lean

The values of a lookup that depend on the shift θ and the point of comparison al and on no other
challenge, as terms of the key vectors, the tables and the bits; and the claim on the number of
keys.

The byte format's page docs/format/11-1-machinery.md ("The lookup: what is looked up, the values,
and the claims") names: Z, the root of the key side's product tree; G_j, the root of plane j's
product tree; P_s, with P_31 = G_31 and P_s = P_(s+1)^2 G_s; a_pad, the padding's factor; and the
relation Z = a_pad times the product over j < 32 of G_j^(2^j). The levels N_m of a product tree
stand in the paragraph "A product level" of the same page. This file writes these down over the
joint vectors Ends.jointKey and Ends.jointTab (OnBytes/Tie/Pv/Lookup/Ends/Joint.lean), with the
library's own keyProd, tabProd, padFac (Cb/Gen/LkpAlg.lean, Cb/Pv/Lookup/Alg/PadAlg.lean),
Alg.Lookup.chainFrom (Alg/Lookup.lean) and Blocks.lvl (Blocks/LookupRel.lean).

Notation. NC, NT, kT, cK, dT, rK are fields of h : Forest.Shape; d = kT + cK; v = dT + rK. kv c i is
place i of call c's key vector; bits u j is bit j of row u = t 2^cK + c of the joint table; lm: the
planes' matrix has 2^lm rows. See the head of Johnson/HonestTrace/Counts.lean. "MidP" below is
Cb.Lkp.MidP v d 5 32 at jointKey h kv θ, jointTab h θ, FoNums.pads h, bits and al; law_bits
(Johnson/HonestTrace/CountsLaw.lean) concludes it.

Main definitions: "zRoot" (Z), "gRoot" (G_j), "pChain" (P_s), "aPad" (a_pad), "keyLvl" and "tabLvl"
(the levels N_m of the key side, m ≤ v, and of the table side, 5 ≤ m ≤ 5 + d).

Main theorems, each with its premises in its docstring:
* "roots_relation", "tie0": under MidP, Z = a_pad times the product of the G_j^(2^j), and Z = a_pad
  P_1^2 G_0. "tie_top", "tie_step", "pChain_zero": the chain of the P_s, for any bits.
* "aPad_facK", "aPad_trees": under FoNums.ok h, a_pad is Cb.Fo.PadFac.facK h θ al
  (OnBytes/Tie/Pv/Lookup/Forest/FoPadFac.lean), that is, the product tree by tree of the format's
  page. "jointTab_padRow": the joint table's row at a call's padding row is the call's padding key.
* "keyLvl_root", "keyLvl_step", "keyLvl_leaf", "tabLvl_root", "tabLvl_step", "tabLvl_leaf": root,
  step and leaves of the two trees. "jointKey_tree", "jointKey_empty", "jointTab_row": the leaves'
  keys and rows written out by tree, call and row.
* "countK_plane": under FoNums.ok h, Fits h T Kv H and 5 ≤ lm ≤ kT + 5, for every reading ν of the
  places Fo.Pl whose cells, at the rows below 2^lm and the columns below NC 2^(kT + 5 - lm), are
  plane h lm H: Cb.Fo.Pin.countK h lm (Cb.Fo.Pin.pinColK lm ν) = 0
  (OnBytes/Tie/Pv/Lookup/Forest/FoPin.lean): the claim that the counts add up to the number of keys
  that are not padding, in the form in which that file states it. It is an equation in K; in a field
  of small characteristic it says less than sum_plane_all (CountsLaw.lean), an equation of natural
  numbers. "facts_plane": tie0, "every such cell of ν is 0 or 1" and countK_plane in one statement.
  "aPad_ends": under FoNums.ok h, the public factor that Fo.endsOf
  (OnBytes/Tie/Pv/Lookup/Forest/FoEnds.lean) reads off given rounds is a_pad at these rounds' shift
  and point of comparison.

Limits. θ and al are arbitrary elements of an arbitrary field. The correspondence with the format's
letters is by reading the page: its dL, alpha, theta, npad(y), padkey_c, tree0(c) and call(y) are d,
al, θ, h.pub.getD y 0, Cb.Fo.PadFac.padKeyK h θ c, FoNums.fst h c and FoNums.co h y. No theorem of
this file compares a term with a program. Of the page's claims this file has one: countK is LP2.
tie0 and "every cell is 0 or 1" are what the format's "tie step 0" and its test of the bits are
about; they are not the claims LK0, LK(31 + v + dL) and LP1, which read further challenges and the
mask row. The terms are products over up to 2^v and 2^(5 + d) factors: specifications, not programs
to run. Of a sumcheck's rounds only aPad_ends speaks, and only of the three values a, theta and
alpha that Fo.endsOf reads off them. Nothing is said of points other than θ and al, of extensions at
a point, of the mask row, or of the numbers of the scalars sent. keyLvl and tabLvl are total
functions: above the tree's height and outside a level's indices their values mean nothing, and
tabLvl below m = 5 is the level m = 5. pChain beyond s = 31 is G_s. The subtractions in
jointKey_tree (y less the call's first tree) and aPad_trees (2^rK - NT) are those of natural
numbers.

Not claimed: that a prover sends these values; that any claim of the lookup argument but LP2 holds
at them; that a verifier accepts; completeness of the protocol.

-/
import Johnson.HonestTrace.CountsLaw
import OnBytes.Tie.Pv.Lookup.Forest.FoPin
import OnBytes.Tie.Pv.Lookup.Forest.FoEnds

set_option autoImplicit false

namespace OnBytes.HonestTrace

open Finset
open OnBytes.Model
open Cb.Lkp Cb.LdLkp

section
variable {K : Type} [Field K]

/-! ## The values of the lookup that depend on no round: Z, G_j, P_s, a_pad -/

/-- Z: the product of al - key over the 2^v places of the joint key vector. -/
def zRoot (h : Forest.Shape) (kv : ℕ → ℕ → K) (θ al : K) : K :=
  keyProd h.v (Ends.jointKey h kv θ) al

/-- G_j: the product over the 2^d rows u of the joint table of 1 + bits u j (al - 1 - row u). -/
def gRoot (h : Forest.Shape) (bits : ℕ → ℕ → K) (θ al : K) (j : ℕ) : K :=
  tabProd h.d (Ends.jointTab h θ) bits al j

/-- P_s for s ≤ 31: Alg.Lookup.chainFrom of the G_j, from plane 31 down to plane s. -/
def pChain (h : Forest.Shape) (bits : ℕ → ℕ → K) (θ al : K) (s : ℕ) : K :=
  Alg.Lookup.chainFrom (gRoot h bits θ al) (31 - s) s

/-- a_pad: the algebra's public factor padFac at the joint table and the list FoNums.pads h. -/
def aPad (h : Forest.Shape) (θ al : K) : K :=
  padFac (Ends.jointTab h θ) (FoNums.pads h) al

/-- If MidP holds at jointKey h kv θ, jointTab h θ, FoNums.pads h, bits and al, then
Z = a_pad times the product over j < 32 of G_j^(2^j). It is MidP's third clause. -/
theorem roots_relation {h : Forest.Shape} {kv : ℕ → ℕ → K} {bits : ℕ → ℕ → K} {θ al : K}
    (hM : MidP h.v h.d 5 32 (Ends.jointKey h kv θ) (Ends.jointTab h θ) (FoNums.pads h) bits al) :
    zRoot h kv θ al = aPad h θ al * ∏ j ∈ range 32, gRoot h bits θ al j ^ 2 ^ j :=
  hM.2.2

/-- P_31 = G_31. -/
theorem tie_top (h : Forest.Shape) (bits : ℕ → ℕ → K) (θ al : K) :
    pChain h bits θ al 31 = gRoot h bits θ al 31 := rfl

/-- For s < 31: P_s = P_(s+1)^2 G_s. -/
theorem tie_step (h : Forest.Shape) (bits : ℕ → ℕ → K) (θ al : K) {s : ℕ} (hs : s < 31) :
    pChain h bits θ al s = pChain h bits θ al (s + 1) ^ 2 * gRoot h bits θ al s := by
  have e : 31 - s = (31 - (s + 1)) + 1 := by omega
  unfold pChain
  rw [e]
  rfl

/-- P_0 is the product over j < 32 of G_j^(2^j). -/
theorem pChain_zero (h : Forest.Shape) (bits : ℕ → ℕ → K) (θ al : K) :
    pChain h bits θ al 0 = ∏ j ∈ range 32, gRoot h bits θ al j ^ 2 ^ j := by
  unfold pChain
  rw [Alg.Lookup.chainFrom_eq_prod]
  simp

/-- If MidP holds at jointKey h kv θ, jointTab h θ, FoNums.pads h, bits and al, then
Z = a_pad (P_1^2 G_0). -/
theorem tie0 {h : Forest.Shape} {kv : ℕ → ℕ → K} {bits : ℕ → ℕ → K} {θ al : K}
    (hM : MidP h.v h.d 5 32 (Ends.jointKey h kv θ) (Ends.jointTab h θ) (FoNums.pads h) bits al) :
    zRoot h kv θ al =
      aPad h θ al * (pChain h bits θ al 1 ^ 2 * gRoot h bits θ al 0) := by
  rw [roots_relation hM, ← pChain_zero, tie_step h bits θ al (by norm_num : 0 < 31)]

/-! ## The padding's factor, tree by tree -/

/-- Under FoNums.ok h, for c below h.NC: row FoNums.padRow h c of the joint table is the padding key
Cb.Fo.PadFac.padKeyK h θ c, the value of the call's padding row plus c θ. -/
theorem jointTab_padRow {h : Forest.Shape} (hok : FoNums.ok h = true) (θ : K) {c : ℕ}
    (hc : c < h.NC) :
    Ends.jointTab h θ (FoNums.padRow h c) = Cb.Fo.PadFac.padKeyK h θ c := by
  obtain ⟨⟨_, _, a3, _⟩, _⟩ := Cb.Fo.ok_parts hok
  have hc' : c < 2 ^ h.cK := lt_of_lt_of_le hc a3
  have hfT : Port.fT h (c + 2 ^ h.cK * FoNums.t0Of h c) = c := by
    unfold Port.fT
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc', Nat.min_eq_left (by omega)]
  rw [jointTab_sh hok]
  show Port.tab h (tabOf K h) (c + 2 ^ h.cK * FoNums.t0Of h c) +
    ((Port.fT h (c + 2 ^ h.cK * FoNums.t0Of h c) : ℕ) : K) * θ = _
  rw [tab_at hok (tabOf K h) hc (t0Of_lt hok hc), hfT]
  rfl

/-- Under FoNums.ok h: a_pad is Cb.Fo.PadFac.facK h θ al. -/
theorem aPad_facK {h : Forest.Shape} (hok : FoNums.ok h = true) (θ al : K) :
    aPad h θ al = Cb.Fo.PadFac.facK h θ al := by
  rw [← Cb.Fo.PadFac.pad_fac h hok 5 0 θ al]
  show (((List.range h.NC).map fun c => (FoNums.padRow h c, FoNums.padCount h c)).map
      fun e => (al - Ends.jointTab h θ e.1) ^ e.2).prod =
    (((List.range h.NC).map fun c => (FoNums.padRow h c, FoNums.padCount h c)).map
      fun e => (al - _root_.Fo.tabF h θ e.1) ^ e.2).prod
  rw [List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun c hc => ?_
  have hc' := List.mem_range.1 hc
  show (al - Ends.jointTab h θ (FoNums.padRow h c)) ^ FoNums.padCount h c =
    (al - _root_.Fo.tabF h θ (FoNums.padRow h c)) ^ FoNums.padCount h c
  rw [jointTab_padRow hok θ hc', Cb.Fo.PadFac.tab_padRow h hok θ c hc']

/-- Under FoNums.ok h: a_pad is (al - padding key of call 0)^((2^rK - NT) 2^dT) times the product
over the trees y below NT of (al - padding key of the tree's call)^(h.pub.getD y 0). -/
theorem aPad_trees {h : Forest.Shape} (hok : FoNums.ok h = true) (θ al : K) :
    aPad h θ al = (al - Cb.Fo.PadFac.padKeyK h θ 0) ^ ((2 ^ h.rK - h.NT) * 2 ^ h.dT) *
      ∏ y ∈ range h.NT, (al - Cb.Fo.PadFac.padKeyK h θ (FoNums.co h y)) ^ h.pub.getD y 0 := by
  rw [aPad_facK hok]
  unfold Cb.Fo.PadFac.facK
  rw [Cb.Fo.PadFac.foldl_mul]
  rfl

/-! ## The two product trees -/

/-- N_m(X) of the key side: Blocks.lvl over the leaves al - jointKey h kv θ X, X < 2^v. -/
def keyLvl (h : Forest.Shape) (kv : ℕ → ℕ → K) (θ al : K) (m X : ℕ) : K :=
  Blocks.lvl 0 h.v (facK (Ends.jointKey h kv θ) al) m X

/-- N_m(X) of the table side, for 5 ≤ m ≤ 5 + d: Blocks.lvl over the leaves
1 + bits u j (al - 1 - jointTab h θ u) at the index u 32 + j. -/
def tabLvl (h : Forest.Shape) (bits : ℕ → ℕ → K) (θ al : K) (m X : ℕ) : K :=
  Blocks.lvl 5 h.d (facT 5 (Ends.jointTab h θ) bits al) (m - 5) X

/-- The root of the key side's tree is Z. -/
theorem keyLvl_root (h : Forest.Shape) (kv : ℕ → ℕ → K) (θ al : K) :
    keyLvl h kv θ al 0 0 = zRoot h kv θ al := by
  unfold keyLvl zRoot keyProd facK
  rw [Blocks.lvl_zero]
  simp

/-- For m < v: N_m(X) = N_(m+1)(X) N_(m+1)(X + 2^m) on the key side. -/
theorem keyLvl_step (h : Forest.Shape) (kv : ℕ → ℕ → K) (θ al : K) {m : ℕ} (hm : m < h.v)
    (X : ℕ) :
    keyLvl h kv θ al m X = keyLvl h kv θ al (m + 1) X * keyLvl h kv θ al (m + 1) (X + 2 ^ m) :=
  Blocks.lvl_step 0 h.v _ hm X

/-- The level m = v of the key side holds the leaves al - jointKey h kv θ X. -/
theorem keyLvl_leaf (h : Forest.Shape) (kv : ℕ → ℕ → K) (θ al : K) (X : ℕ) :
    keyLvl h kv θ al h.v X = al - Ends.jointKey h kv θ X := by
  unfold keyLvl
  rw [Blocks.lvl_top]
  rfl

/-- For j < 32 the level m = 5 of the table side holds G_j at the index j. -/
theorem tabLvl_root (h : Forest.Shape) (bits : ℕ → ℕ → K) (θ al : K) {j : ℕ} (hj : j < 32) :
    tabLvl h bits θ al 5 j = gRoot h bits θ al j := by
  unfold tabLvl gRoot tabProd facT
  rw [Nat.sub_self, Blocks.lvl_zero]
  refine prod_congr rfl fun u _ => ?_
  have e1 : (u * 2 ^ 5 + j) / 2 ^ 5 = u := by norm_num; omega
  have e2 : (u * 2 ^ 5 + j) % 2 ^ 5 = j := by norm_num; omega
  rw [e1, e2]

/-- For 5 ≤ m < 5 + d: N_m(X) = N_(m+1)(X) N_(m+1)(X + 2^m) on the table side. -/
theorem tabLvl_step (h : Forest.Shape) (bits : ℕ → ℕ → K) (θ al : K) {m : ℕ} (h5 : 5 ≤ m)
    (hm : m < 5 + h.d) (X : ℕ) :
    tabLvl h bits θ al m X =
      tabLvl h bits θ al (m + 1) X * tabLvl h bits θ al (m + 1) (X + 2 ^ m) := by
  have e1 : m + 1 - 5 = (m - 5) + 1 := by omega
  have e2 : m - 5 + 5 = m := by omega
  unfold tabLvl
  rw [e1, Blocks.lvl_step 5 h.d _ (by omega : m - 5 < h.d) X, e2]

/-- For j < 32 the level m = 5 + d of the table side holds, at the index u 32 + j, the leaf
1 + bits u j (al - 1 - jointTab h θ u). -/
theorem tabLvl_leaf (h : Forest.Shape) (bits : ℕ → ℕ → K) (θ al : K) (u : ℕ) {j : ℕ}
    (hj : j < 32) :
    tabLvl h bits θ al (5 + h.d) (u * 32 + j) =
      1 + bits u j * (al - 1 - Ends.jointTab h θ u) := by
  have e0 : 5 + h.d - 5 = h.d := by omega
  have e1 : (u * 32 + j) / 2 ^ 5 = u := by norm_num; omega
  have e2 : (u * 32 + j) % 2 ^ 5 = j := by norm_num; omega
  unfold tabLvl
  rw [e0, Blocks.lvl_top]
  show 1 + bits ((u * 32 + j) / 2 ^ 5) ((u * 32 + j) % 2 ^ 5) *
    (al - 1 - Ends.jointTab h θ ((u * 32 + j) / 2 ^ 5)) = _
  rw [e1, e2]

/-! ## The leaves, written out -/

/-- At a place X whose tree y = X % 2^rK is below NT, with c the tree's call: the joint key is
kv c ((y - first tree of c) 2^dT + X / 2^rK) + c θ. -/
theorem jointKey_tree (h : Forest.Shape) (kv : ℕ → ℕ → K) (θ : K) {X : ℕ}
    (hy : X % 2 ^ h.rK < h.NT) :
    Ends.jointKey h kv θ X =
      kv (FoNums.co h (X % 2 ^ h.rK))
        ((X % 2 ^ h.rK - FoNums.fst h (FoNums.co h (X % 2 ^ h.rK))) * 2 ^ h.dT + X / 2 ^ h.rK) +
      ((FoNums.co h (X % 2 ^ h.rK) : ℕ) : K) * θ := by
  unfold Ends.jointKey
  simp only [if_pos hy]
  rfl

/-- Under FoNums.ok h, at a place X whose tree X % 2^rK is not below NT, the joint key is the
padding key of call 0. -/
theorem jointKey_empty {h : Forest.Shape} (hok : FoNums.ok h = true) (kv : ℕ → ℕ → K) (θ : K)
    {X : ℕ} (hy : h.NT ≤ X % 2 ^ h.rK) :
    Ends.jointKey h kv θ X = Cb.Fo.PadFac.padKeyK h θ 0 := by
  have h0 : 0 < h.calls.size := by
    have := calls_size hok
    omega
  unfold Ends.jointKey Cb.Fo.PadFac.padKeyK
  simp only [if_neg (Nat.not_lt.2 hy)]
  rw [← tabOf_eq K h h0]
  simp [tabOf, t0N_eq]

/-- Under FoNums.ok h, with c' = min (u % 2^cK) (NC - 1): row u of the joint table is
tabOf K h c' (u / 2^cK % 2^(k_c')) + c' θ. -/
theorem jointTab_row {h : Forest.Shape} (hok : FoNums.ok h = true) (θ : K) (u : ℕ) :
    Ends.jointTab h θ u =
      tabOf K h (min (u % 2 ^ h.cK) (h.NC - 1))
        (u / 2 ^ h.cK % 2 ^ FoNums.kOf h (min (u % 2 ^ h.cK) (h.NC - 1))) +
      ((min (u % 2 ^ h.cK) (h.NC - 1) : ℕ) : K) * θ := by
  rw [jointTab_sh hok]
  rfl

/-! ## The claim on the number of keys -/

/-- Under FoNums.ok h, Fits h T Kv H and 5 ≤ lm ≤ kT + 5: if ν reads plane h lm H r c, cast into K,
at every place .cell r c with r below 2^lm and c below NC 2^(kT + 5 - lm), then
Cb.Fo.Pin.countK h lm (Cb.Fo.Pin.pinColK lm ν) = 0. -/
theorem countK_plane (h : Forest.Shape) (T Kv : ℕ → ℕ → K) (H : Hits)
    (hok : FoNums.ok h = true) (hF : Fits h T Kv H) {lm : ℕ} (h5 : 5 ≤ lm)
    (hlm : lm ≤ h.kT + 5) (ν : _root_.Fo.Pl → K)
    (hν : ∀ r < 2 ^ lm, ∀ c < h.NC * 2 ^ (h.kT + 5 - lm),
      ν (.cell r c) = (plane h lm H r c : K)) :
    Cb.Fo.Pin.countK h lm (Cb.Fo.Pin.pinColK lm ν) = 0 := by
  have hS := sum_plane_all h T Kv H hok hF h5 hlm
  have hcast : ∑ col ∈ range (h.NC * 2 ^ (h.kT + 5 - lm)), Cb.Fo.Pin.pinColK lm ν col =
      ((∑ col ∈ range (h.NC * 2 ^ (h.kT + 5 - lm)), ∑ r ∈ range (2 ^ lm),
        2 ^ (r % 32) * plane h lm H r col : ℕ) : K) := by
    push_cast
    refine sum_congr rfl fun col hcol => ?_
    unfold Cb.Fo.Pin.pinColK
    exact sum_congr rfl fun r hr => by rw [hν r (mem_range.1 hr) col (mem_range.1 hcol)]
  unfold Cb.Fo.Pin.countK
  rw [Cb.Fo.Pin.foldl_add_from, hcast, neg_add_eq_zero]
  congr 1
  omega

/-- tie0, plane_01 and countK_plane in one statement. Nothing here ties kv and bits (of the premise
MidP) to T, Kv, H and ν: the caller does. If MidP holds at jointKey h kv θ, jointTab h θ,
FoNums.pads h, bits and al; FoNums.ok h and Fits h T Kv H hold; 5 ≤ lm ≤ kT + 5; and ν reads plane h
lm H r c, cast into K, at every place .cell r c with r below 2^lm and c below NC 2^(kT + 5 - lm):
then Z = a_pad (P_1^2 G_0); every x = ν (.cell r c) at such r and c has x (x - 1) = 0; and
Cb.Fo.Pin.countK h lm (Cb.Fo.Pin.pinColK lm ν) = 0. -/
theorem facts_plane {h : Forest.Shape} {kv : ℕ → ℕ → K} {bits : ℕ → ℕ → K} {θ al : K}
    (hM : MidP h.v h.d 5 32 (Ends.jointKey h kv θ) (Ends.jointTab h θ) (FoNums.pads h) bits al)
    (T Kv : ℕ → ℕ → K) (H : Hits) (hok : FoNums.ok h = true) (hF : Fits h T Kv H) {lm : ℕ}
    (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) (ν : _root_.Fo.Pl → K)
    (hν : ∀ r < 2 ^ lm, ∀ c < h.NC * 2 ^ (h.kT + 5 - lm),
      ν (.cell r c) = (plane h lm H r c : K)) :
    zRoot h kv θ al = aPad h θ al * (pChain h bits θ al 1 ^ 2 * gRoot h bits θ al 0) ∧
      (∀ r < 2 ^ lm, ∀ c < h.NC * 2 ^ (h.kT + 5 - lm),
        ν (.cell r c) * (ν (.cell r c) - 1) = 0) ∧
      Cb.Fo.Pin.countK h lm (Cb.Fo.Pin.pinColK lm ν) = 0 := by
  refine ⟨tie0 hM, fun r hr c hc => ?_, countK_plane h T Kv H hok hF h5 hlm ν hν⟩
  rw [hν r hr c hc]
  rcases plane_01 h lm H r c with e | e <;> rw [e] <;> simp

/-! ## The public factor that is read off given rounds -/

/-- Under FoNums.ok h: the public factor that Fo.endsOf reads off the rounds rs is a_pad at the
rounds' own shift and point of comparison. -/
theorem aPad_ends {h : Forest.Shape} (hok : FoNums.ok h = true) (lm jLK : ℕ)
    (rs : TwV.Rounds K) :
    (_root_.Fo.endsOf h lm jLK rs).a =
      aPad h (_root_.Fo.endsOf h lm jLK rs).theta (_root_.Fo.endsOf h lm jLK rs).alpha := by
  rw [aPad_facK hok]
  exact Cb.Fo.PadFac.pad_fac h hok lm jLK _ _

end

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.roots_relation
#print axioms OnBytes.HonestTrace.tie_top
#print axioms OnBytes.HonestTrace.tie_step
#print axioms OnBytes.HonestTrace.pChain_zero
#print axioms OnBytes.HonestTrace.tie0
#print axioms OnBytes.HonestTrace.jointTab_padRow
#print axioms OnBytes.HonestTrace.aPad_facK
#print axioms OnBytes.HonestTrace.aPad_trees
#print axioms OnBytes.HonestTrace.keyLvl_root
#print axioms OnBytes.HonestTrace.keyLvl_step
#print axioms OnBytes.HonestTrace.keyLvl_leaf
#print axioms OnBytes.HonestTrace.tabLvl_root
#print axioms OnBytes.HonestTrace.tabLvl_step
#print axioms OnBytes.HonestTrace.tabLvl_leaf
#print axioms OnBytes.HonestTrace.jointKey_tree
#print axioms OnBytes.HonestTrace.jointKey_empty
#print axioms OnBytes.HonestTrace.jointTab_row
#print axioms OnBytes.HonestTrace.countK_plane
#print axioms OnBytes.HonestTrace.facts_plane
#print axioms OnBytes.HonestTrace.aPad_ends
