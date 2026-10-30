-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysQK.lean: the two factors of the query-key weight claims that the verifier
writes out entry by entry, against the library's AH and kp.

A weight claim has one factor for each index group of its unit (OnBytes/Model/Weights.lean). The
claims of the lookup's segment QK (claimsT, OnBytes/Model/LayerPanels.lean; written out in
claimsT_QK_at of Johnson/Road/FormsKeysFold.lean) are on the unit of a layer's query and key
matrices. claimsT tells that unit's groups apart by name: the head (hd), the channel within a head
(cd), and any other, for which it calls facRs (Johnson/Road/FormsKeysFacRs.lean). This file says
what the factors on hd and cd weigh an index with, in the sense of facAt
(Johnson/Road/FormsKeysPan.lean):
 - hd: the first array of headWeights: the library's AH at the head, and 0 from the last head on
   (AH_at, fac_hd);
 - cd: the array of ropeFactor: the library's kp (kap_at, fac_cd). On the way: the second array of
   headWeights is the library's lf (lf_at).
The library's three quantities (Inst/Model/FF/Objects.lean) are read at the point of the verifier's
call, as a free point ζ, in the manner of Johnson/Road/FormsKeysFree.lean: AHP, lfP and kpP are the
library's definitions with ζ in the place of zc D z (call .QK). They are the library's own at
ζ := zc D z (call .QK) by definition (AH_eq_AHP, lf_eq_lfP, kp_eq_kpP), and at every ζ that agrees
with that point on the call's coordinates (AHP_eq_AH, kpP_eq_kp).

What is compared with what: the verifier's headWeights and ropeFactor with the library's AH, lf and
kp. In both texts the query heads stand before the key heads; the cosine goes with the channel
itself; at an even channel the sine times the next channel is added, at an odd channel the sine
times the channel before is taken away.

Where the two texts differ in their domains:
 - the library's AH is defined at every number, and its panel sums the heads below nq + nkv; the
   verifier's array has 64 entries, which are 0 from H + Gk on. AH_at has both cases;
 - the library's number of bits of a channel, lch, is a logarithm rounded down, the verifier's ldh
   one rounded up. They are one number because the layout refuses a width of a head that is no
   power of two (pow_of_manyBits, QKFits.lch_eq);
 - the verifier's tables of equality weights read 0 past their ends, the library's kernel reads the
   low bits of its index. The statements stay within the tables (QKFits.inside);
 - the library's lf and kp are defined at every number, the verifier's arrays have dh entries.
   lf_at and kap_at are for channels below dh.

Main definitions: AHP, lfP, kpP; QKFits, RopeFits (hypotheses); HeadsLaid; ropeSum; tbRope; metQK.
Main theorems: headWeights_entries, headWeights_value; AH_at, lf_at, kap_at, fac_hd, fac_cd;
QKFits.chOK; qkFits_of_layout (with pow_of_manyBits, headsLaid_of_layout, cols_of_layout);
Numerals.ofInt, ropeFits_of_words, ropeFits_met.

The hypotheses, and whether they can be met.
 - QKFits is the conclusion of qkFits_of_layout. No theorem concludes that theorem's own hypotheses:
   layout has returned; the switches; the library's sizes agree with the shape; the call that
   holds QK has the line of the library's call (hn); the verifier's least number of columns does not
   pass the library's number (hfl); the call's point has its coordinates (hsz: size_of_test of
   Johnson/Road/FormsKeysPoint.lean draws it from a run-time test). The run metQK at the end of this
   file finds them true together, with headWeights returning, at a made-up shape and made-up
   points, in both groups of layers. A run speaks of these numbers alone.
 - hrt, that the point rt has one coordinate for each bit of a position: no theorem. In metQK the
   point is made up with that length.
 - RopeFits, on the rotary tables: it can be met at every environment of the verifier
   (ropeFits_met: at tables that are written from the verifier's own entries, so true by
   construction). ropeFits_of_words brings it down to equations of integers between the words of
   the verifier's table and the library's C and S; it is composed with nothing. No theorem compares
   the verifier's table with the library's reference tables; Johnson/Road/FormsKeysRunK.lean holds
   a run that compares the table's words at the large example.

What is not claimed: that facAt is what the verifier's settling of a claim on the matrix of weights
comes to; that the unit's groups hd and cd have a class other than 'E' and 64 and dh indices (fac_hd
and fac_cd ask the class); anything on the weights themselves; how the call's point is cut out of
the point of the whole lookup; that rt is the end point of a sumcheck. Nothing here is a statement
on what a verifier's acceptance shows. The program does not import this file.
-/
import Johnson.Road.FormsKeysKV

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading eqTab Seg CallD WsGrp WsFac cutLast headFeat TenAt ofInt place topBit)
open OnBytes.Model.Layer (ClaimEnv Env Lay Shape Ten ropeC layout layoutBase manyBits)
open Inst.Model (Tables)
open Inst.Model.FFSeg (Dim Fam Arr len call pos lJ aC zc lch AH lf kp Ct St fams used)

/-! ## The library's three quantities, at a free point -/

section Free

variable {K : Type} [Field K] (D : Dim)

/-- The library's AH with a free point ζ in the place of zc D z (call .QK), the point of the call
that holds the family QK: the weight of head h. -/
def AHP (ζ : ℕ → K) (h : ℕ) : K :=
  Blocks.eqN (lJ D (call .QK) - lch D) D.lL ζ (pos D .QK (D.P.ch * h) / D.P.ch)

/-- The library's lf at the free point: the weight of channel x within a head. -/
def lfP (ζ : ℕ → K) (x : ℕ) : K :=
  Blocks.eqN (lch D) (D.lL + (lJ D (call .QK) - lch D)) ζ x

/-- The library's kp at the free point ζ: the factor on channel x within a head for layer l of the
group, with the rotary tables contracted at zh. -/
def kpP (tb : Tables) (L0 : ℕ) (ζ zh : ℕ → K) (l x : ℕ) : K :=
  if x % 2 = 0 then
    Ct D tb L0 l (x / 2) zh * lfP D ζ x + St D tb L0 l (x / 2) zh * lfP D ζ (x + 1)
  else Ct D tb L0 l (x / 2) zh * lfP D ζ x - St D tb L0 l (x / 2) zh * lfP D ζ (x - 1)

/-- The library's AH is AHP at the library's point of the call. -/
theorem AH_eq_AHP (z : ℕ → K) (h : ℕ) : AH D z h = AHP D (zc D z (call .QK)) h := rfl

/-- The library's lf is lfP at the library's point of the call. -/
theorem lf_eq_lfP (z : ℕ → K) (x : ℕ) : lf D z x = lfP D (zc D z (call .QK)) x := rfl

/-- The library's kp is kpP at the library's point of the call. -/
theorem kp_eq_kpP (tb : Tables) (L0 : ℕ) (z zh : ℕ → K) (l x : ℕ) :
    kp D tb L0 z zh l x = kpP D tb L0 (zc D z (call .QK)) zh l x := rfl

/-- AHP reads coordinates of ζ below aC D (call .QK) alone. -/
theorem AHP_congr {ζ ζ' : ℕ → K} (h : ∀ j < aC D (call .QK), ζ j = ζ' j) (hd : ℕ) :
    AHP D ζ hd = AHP D ζ' hd :=
  eqN_agree _ D.lL (fun j hj => h _ (by
    show D.lL + j < D.lL + lJ D (call .QK) + D.lT
    omega)) _

/-- So does lfP, if a head's channels have at most as many bits as the call's columns. -/
theorem lfP_congr (hcol : lch D ≤ lJ D (call .QK)) {ζ ζ' : ℕ → K}
    (h : ∀ j < aC D (call .QK), ζ j = ζ' j) (x : ℕ) : lfP D ζ x = lfP D ζ' x :=
  eqN_agree _ _ (fun j hj => h _ (by
    show D.lL + (lJ D (call .QK) - lch D) + j < D.lL + lJ D (call .QK) + D.lT
    omega)) _

/-- And kpP. -/
theorem kpP_congr (hcol : lch D ≤ lJ D (call .QK)) (tb : Tables) (L0 : ℕ) {ζ ζ' : ℕ → K}
    (h : ∀ j < aC D (call .QK), ζ j = ζ' j) (zh : ℕ → K) (l x : ℕ) :
    kpP D tb L0 ζ zh l x = kpP D tb L0 ζ' zh l x := by
  unfold kpP
  simp only [lfP_congr D hcol h]

/-- kpP reads the first lT coordinates of zh alone. -/
theorem kpP_zh (tb : Tables) (L0 : ℕ) (ζ : ℕ → K) {zh zh' : ℕ → K} (h : ∀ j < D.lT, zh j = zh' j)
    (l x : ℕ) : kpP D tb L0 ζ zh l x = kpP D tb L0 ζ zh' l x := by
  unfold kpP Ct St
  simp only [Blocks.ext_congr_point h]

end Free

/-! ## Tools: arrays -/

/-- Writing at one index leaves the others. -/
theorem getD_set_ne (a : Array E) {i j : ℕ} (h : i ≠ j) (x : E) :
    (a.setIfInBounds i x).getD j zeroE = a.getD j zeroE := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- What has been written at an index within the array is read there. -/
theorem getD_set_self (a : Array E) {i : ℕ} (h : i < a.size) (x : E) :
    (a.setIfInBounds i x).getD i zeroE = x := by
  simp [Array.getD_eq_getD_getElem?, h]

/-- An array of zeros reads 0 everywhere. -/
theorem getD_zeros (n i : ℕ) : (Array.replicate n zeroE).getD i zeroE = zeroE := by
  by_cases h : i < n
  · simp [Array.getD, h]
  · simp [Array.getD, h]

/-- A fold over a list of indices whose step, where it returns, writes at the index hd the element
w x, where x is what the function g, which may refuse, gives for hd. If the fold returns an array,
it has the first array's size; off the list it reads as the first array; and, if no index is listed
twice, g has returned a value at every listed index, and at a listed index within the array the
element for that value is read. -/
theorem foldSet_spec (step : Array E → ℕ → Option (Array E)) (g : ℕ → Option ℕ) (w : ℕ → E)
    (H : ∀ a hd a', step a hd = some a' → ∃ x, g hd = some x ∧ a' = a.setIfInBounds hd (w x)) :
    ∀ (l : List ℕ) (a b : Array E), l.foldlM step a = some b →
    b.size = a.size ∧ (∀ i, i ∉ l → b.getD i zeroE = a.getD i zeroE) ∧
      (l.Nodup → ∀ i ∈ l, ∃ x, g i = some x ∧ (i < a.size → b.getD i zeroE = w x))
  | [], a, b, h => by
    have e : a = b := by simpa using h
    subst e
    exact ⟨rfl, fun _ _ => rfl, fun _ i hi => absurd hi List.not_mem_nil⟩
  | hd :: l, a, b, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨a', h1, h2⟩ := bind_some h
    obtain ⟨x, hx, e⟩ := H a hd a' h1
    subst e
    obtain ⟨s1, s2, s3⟩ := foldSet_spec step g w H l _ b h2
    refine ⟨by rw [s1, Array.size_setIfInBounds], ?_, ?_⟩
    · intro i hi
      have hne : hd ≠ i := fun e => hi (e ▸ List.mem_cons_self)
      have hnl : i ∉ l := fun e => hi (List.mem_cons_of_mem _ e)
      rw [s2 i hnl]
      exact getD_set_ne a hne _
    · intro hnd i hi
      obtain ⟨hn1, hn2⟩ := List.nodup_cons.mp hnd
      rcases List.mem_cons.mp hi with e | hi'
      · subst e
        refine ⟨x, hx, fun hlt => ?_⟩
        rw [s2 i hn1]
        exact getD_set_self a hlt _
      · obtain ⟨x', hx', hv⟩ := s3 hn2 i hi'
        exact ⟨x', hx', fun hlt => hv (by rw [Array.size_setIfInBounds]; exact hlt)⟩

/-- An array that is made of one pair for each number below n, as a list. -/
theorem pairs_toList (n : ℕ) (f g : ℕ → E) :
    ((Array.range n).flatMap fun i => #[f i, g i]).toList =
      (List.range n).flatMap fun i => [f i, g i] := by
  simp [Array.toList_flatMap]

/-- Such a list has two members for each pair. -/
theorem pairs_length (f g : ℕ → E) : ∀ l : List ℕ,
    (l.flatMap fun i => [f i, g i]).length = 2 * l.length
  | [] => rfl
  | x :: l => by
    rw [List.flatMap_cons, List.length_append, pairs_length f g l, List.length_cons]
    show 2 + 2 * l.length = 2 * (l.length + 1)
    omega

/-- The array has 2 n entries. -/
theorem pairs_size (n : ℕ) (f g : ℕ → E) :
    ((Array.range n).flatMap fun i => #[f i, g i]).size = 2 * n := by
  rw [← Array.length_toList, pairs_toList, pairs_length, List.length_range]

/-- Its entries 2 i and 2 i + 1 are pair number i. -/
theorem pairs_getD (n : ℕ) (f g : ℕ → E) {i : ℕ} (hi : i < n) :
    ((Array.range n).flatMap fun i => #[f i, g i]).getD (2 * i) zeroE = f i ∧
      ((Array.range n).flatMap fun i => #[f i, g i]).getD (2 * i + 1) zeroE = g i := by
  have hl : (List.range n)[i]? = some i := by simp [hi]
  have a0 := flatMap_getElem? (fun i => [f i, g i]) 2 (List.range n) (by intro a _; rfl) i 0 i hl
    (by norm_num)
  have a1 := flatMap_getElem? (fun i => [f i, g i]) 2 (List.range n) (by intro a _; rfl) i 1 i hl
    (by norm_num)
  rw [← pairs_toList] at a0 a1
  have e0 : 2 * i = i * 2 + 0 := by omega
  have e1 : 2 * i + 1 = i * 2 + 1 := by omega
  constructor
  · rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, e0, a0]
    rfl
  · rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, e1, a1]
    rfl

/-! ## Tools: the verifier's small functions -/

/-- What cutLast returns. -/
theorem cutLast_some {z : Array E} {k : ℕ} {p : Array E × Array E}
    (h : (cutLast z k).toOption = some p) :
    k ≤ z.size ∧ p = (z.extract 0 (z.size - k), z.extract (z.size - k) z.size) := by
  unfold cutLast at h
  split at h
  · cases h
  · rename_i hk
    cases h
    exact ⟨by omega, rfl⟩

/-- What headFeat returns. -/
theorem headFeat_some {X : TenAt} {hd dh x : ℕ} (h : (headFeat X hd dh).toOption = some x) :
    x = hd * dh := by
  unfold headFeat at h
  split at h
  · cases h
  · cases h
    rfl

/-- The call that callOf returns is call number q of the layout, and the segment is one of its
segments and has the name that was asked for. -/
theorem callOf_spec {v : Env} {sn : String} {q : ℕ} {cd : CallD} {s : Seg}
    (h : v.callOf sn = some (q, cd, s)) :
    v.y.calls[q]? = some cd ∧ s ∈ cd.segs ∧ s.name = sn := by
  unfold Env.callOf at h
  obtain ⟨⟨cd', i⟩, ha, hf⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨s', hs', e⟩ := map_some hf
  cases e
  unfold CallD.seg? at hs'
  refine ⟨?_, List.mem_of_find?_eq_some hs', ?_⟩
  · simpa using List.mem_zipIdx_iff_getElem?.mp ha
  · simpa using List.find?_some hs'

section Values

variable {K : Type} [Field K] (ρ : Reading K)

/-- A sum of products folded over the first n numbers. -/
theorem foldl_madd_range (a b : ℕ → E) : ∀ n : ℕ,
    ρ.val ((List.range n).foldl (fun s t => addE s (mulE (a t) (b t))) zeroE) =
      ∑ t ∈ range n, ρ.val (a t) * ρ.val (b t)
  | 0 => by simp [ρ.zero]
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ρ.add, ρ.mul,
      foldl_madd_range a b n, sum_range_succ]

/-- The table of equality weights of a stretch of the coordinates of the column in the point of call
q: entry p reads as the library's kernel over these coordinates of the call's whole point. -/
theorem stretch_value (v : Env) (q lJ' a m : ℕ) (hsz : v.y.h.ll + lJ' ≤ (v.zk.getD q #[]).size)
    (ham : a + m ≤ lJ') {p : ℕ} (hp : p < 2 ^ m) :
    ρ.val ((eqTab ((v.zj q lJ').extract a (a + m))).getD p zeroE) =
      Blocks.eqN m (v.y.h.ll + a) (pt ρ (v.zk.getD q #[])) p := by
  have s1 : (v.zj q lJ').size = lJ' := by
    unfold Env.zj
    rw [Array.size_extract]
    omega
  have s2 : ((v.zj q lJ').extract a (a + m)).size = m := by
    rw [Array.size_extract, s1]
    omega
  rw [eqTab_value ρ _ _ (by rw [s2]; exact hp), s2,
    ← eqN_shift' m (v.y.h.ll + a) (pt ρ (v.zk.getD q #[])) p]
  refine eqN_congr' m 0 (fun j hj => ?_) p
  show pt ρ ((v.zj q lJ').extract a (a + m)) (0 + j) =
    pt ρ (v.zk.getD q #[]) (v.y.h.ll + a + (0 + j))
  unfold pt
  rw [Nat.zero_add, getD_stretch _ (by rw [s1]; exact ham) (by omega)]
  unfold Env.zj
  rw [getD_stretch _ hsz (by omega), Nat.add_assoc]

end Values

/-! ## The weights of the heads: what the verifier's function returns -/

/-- If headWeights returns, some call holds the segment QK. -/
theorem headWeights_call (c : ClaimEnv) {ah lfc : Array E}
    (h : c.headWeights = some (ah, lfc)) : ∃ q cd s, c.v.callOf "QK" = some (q, cd, s) := by
  unfold ClaimEnv.headWeights at h
  obtain ⟨⟨q, cd, s⟩, hq, -⟩ := bind_some h
  exact ⟨q, cd, s, hq⟩

/-- What headWeights returns, entry by entry, in the verifier's own words. z: the coordinates of the
column in the point of the call that holds QK. The second array is the table of equality weights of
the last ldh coordinates of z. The first has 64 entries. Its entry hd, for hd below H + Gk and below
64, is the entry of the table of equality weights of the other coordinates of z at the number
(column of entry x of QK) / dh, where x = hd dh for a query head, and the number of features of the
tensor q plus (hd - H) dh for a key head. From H + Gk on it reads 0. -/
theorem headWeights_entries (c : ClaimEnv) {q : ℕ} {cd : CallD} {s : Seg}
    (hcall : c.v.callOf "QK" = some (q, cd, s)) {ah lfc : Array E}
    (h : c.headWeights = some (ah, lfc)) :
    ∃ tq : Ten, c.v.y.T_ "q" = some tq ∧ c.v.y.ldh ≤ (c.v.zj q cd.lJ).size ∧
      lfc = eqTab ((c.v.zj q cd.lJ).extract ((c.v.zj q cd.lJ).size - c.v.y.ldh)
        (c.v.zj q cd.lJ).size) ∧
      ah.size = 64 ∧ (∀ hd, c.v.y.h.H + c.v.y.h.Gk ≤ hd → ah.getD hd zeroE = zeroE) ∧
      ∀ hd, hd < c.v.y.h.H + c.v.y.h.Gk → hd < 64 → ah.getD hd zeroE =
        (eqTab ((c.v.zj q cd.lJ).extract 0 ((c.v.zj q cd.lJ).size - c.v.y.ldh))).getD
          (s.pos.getD (if hd < c.v.y.h.H then hd * c.v.y.h.dh
            else tq.J + (hd - c.v.y.h.H) * c.v.y.h.dh) 0 / c.v.y.h.dh) zeroE := by
  unfold ClaimEnv.headWeights at h
  rw [hcall] at h
  obtain ⟨x0, hx0, h⟩ := bind_some h
  cases hx0
  obtain ⟨⟨hi, lo⟩, hp, h⟩ := bind_some h
  obtain ⟨hle, hpe⟩ := cutLast_some hp
  cases hpe
  obtain ⟨tq, htq, h⟩ := bind_some h
  obtain ⟨tk, htk, h⟩ := bind_some h
  obtain ⟨AH', hf, h⟩ := bind_some h
  cases h
  obtain ⟨s1, s2, s3⟩ := foldSet_spec _
    (fun hd => if hd < c.v.y.h.H then (headFeat tq.place hd c.v.y.h.dh).toOption
      else (headFeat tk.place (hd - c.v.y.h.H) c.v.y.h.dh).toOption.map (tq.place.J + ·))
    (fun x => (eqTab ((c.v.zj q cd.lJ).extract 0 ((c.v.zj q cd.lJ).size - c.v.y.ldh))).getD
      (s.pos.getD x 0 / c.v.y.h.dh) zeroE)
    (by
      intro a hd a' hs
      by_cases hH : hd < c.v.y.h.H
      · simp only [hH, ↓reduceIte] at hs
        obtain ⟨y, hy, e⟩ := bind_some hs
        exact ⟨y, (if_pos hH).trans hy, (Option.some.inj e).symm⟩
      · simp only [hH, ↓reduceIte] at hs
        obtain ⟨y, hy, e⟩ := bind_some hs
        exact ⟨y, (if_neg hH).trans hy, (Option.some.inj e).symm⟩) _ _ _ hf
  refine ⟨tq, htq, hle, rfl, by rw [s1, Array.size_replicate], ?_, ?_⟩
  · intro hd hhd
    rw [s2 hd (by rw [List.mem_range]; omega), getD_zeros]
  · intro hd hhd h64
    obtain ⟨x, hx, hv⟩ := s3 List.nodup_range hd (List.mem_range.mpr hhd)
    rw [hv (by rw [Array.size_replicate]; exact h64)]
    by_cases hH : hd < c.v.y.h.H
    · rw [if_pos hH] at hx
      rw [if_pos hH, headFeat_some hx]
    · rw [if_neg hH] at hx
      obtain ⟨x1, hx1, e⟩ := map_some hx
      rw [if_neg hH, ← e, headFeat_some hx1]
      rfl

/-- If headWeights returns, and the point of the call that holds QK has its coordinates of the layer
and the column, a head's channels have at most as many bits as the call's columns. -/
theorem headWeights_ldh (c : ClaimEnv) {q : ℕ} {cd : CallD} {s : Seg}
    (hcall : c.v.callOf "QK" = some (q, cd, s))
    (hsz : c.v.y.h.ll + cd.lJ ≤ (c.v.zk.getD q #[]).size) {ah lfc : Array E}
    (h : c.headWeights = some (ah, lfc)) : c.v.y.ldh ≤ cd.lJ := by
  obtain ⟨-, -, hle, -⟩ := headWeights_entries c hcall h
  have s1 : (c.v.zj q cd.lJ).size = cd.lJ := by
    unfold Env.zj
    rw [Array.size_extract]
    omega
  rw [s1] at hle
  exact hle

/-! ## The weights of the heads, read in K -/

section Heads

variable {K : Type} [Field K] (ρ : Reading K)

/-- The two arrays of headWeights, read in K with the library's kernel, at the point of the call
that holds QK. Entry hd of the first, for a head hd below H + Gk: the equality weight of the
coordinates of the column without the last ldh, at (the column of entry hd dh of QK) / dh. Entry x
of the second, for x below dh: the equality weight of the last ldh coordinates of the column at x.
Asked: the call's point has its coordinates of the layer and the column; dh = 2^ldh; at most 64
heads; the tensor q has H dh features; the columns of the first (H + Gk) dh entries of QK are
columns of the call. -/
theorem headWeights_value (c : ClaimEnv) {q : ℕ} {cd : CallD} {s : Seg}
    (hcall : c.v.callOf "QK" = some (q, cd, s))
    (hsz : c.v.y.h.ll + cd.lJ ≤ (c.v.zk.getD q #[]).size)
    (hpow : c.v.y.h.dh = 2 ^ c.v.y.ldh) (h64 : c.v.y.h.H + c.v.y.h.Gk ≤ 64)
    (htq : ∀ t : Ten, c.v.y.T_ "q" = some t → t.J = c.v.y.h.H * c.v.y.h.dh)
    (hin : ∀ x, x < (c.v.y.h.H + c.v.y.h.Gk) * c.v.y.h.dh → s.pos.getD x 0 < 2 ^ cd.lJ)
    {ah lfc : Array E} (h : c.headWeights = some (ah, lfc)) :
    (∀ hd, hd < c.v.y.h.H + c.v.y.h.Gk → ρ.val (ah.getD hd zeroE) =
      Blocks.eqN (cd.lJ - c.v.y.ldh) c.v.y.h.ll (pt ρ (c.v.zk.getD q #[]))
        (s.pos.getD (hd * c.v.y.h.dh) 0 / c.v.y.h.dh)) ∧
    ∀ x, x < c.v.y.h.dh → ρ.val (lfc.getD x zeroE) =
      Blocks.eqN c.v.y.ldh (c.v.y.h.ll + (cd.lJ - c.v.y.ldh)) (pt ρ (c.v.zk.getD q #[])) x := by
  obtain ⟨tq, htq', hle, hlfc, -, -, hent⟩ := headWeights_entries c hcall h
  have s1 : (c.v.zj q cd.lJ).size = cd.lJ := by
    unfold Env.zj
    rw [Array.size_extract]
    omega
  rw [s1] at hle hlfc hent
  refine ⟨?_, ?_⟩
  · intro hd hhd
    have hx : (if hd < c.v.y.h.H then hd * c.v.y.h.dh
        else tq.J + (hd - c.v.y.h.H) * c.v.y.h.dh) = hd * c.v.y.h.dh := by
      by_cases hH : hd < c.v.y.h.H
      · rw [if_pos hH]
      · rw [if_neg hH, htq tq htq', ← Nat.add_mul]
        congr 1
        omega
    have hpos : 0 < c.v.y.h.dh := by
      rw [hpow]
      positivity
    have h1 : (hd + 1) * c.v.y.h.dh ≤ (c.v.y.h.H + c.v.y.h.Gk) * c.v.y.h.dh :=
      Nat.mul_le_mul_right _ hhd
    have h2 : (hd + 1) * c.v.y.h.dh = hd * c.v.y.h.dh + c.v.y.h.dh := by ring
    have hP := hin (hd * c.v.y.h.dh) (by omega)
    rw [hent hd hhd (by omega), hx]
    generalize s.pos.getD (hd * c.v.y.h.dh) 0 = P at hP ⊢
    have hdiv : P / c.v.y.h.dh < 2 ^ (cd.lJ - c.v.y.ldh) := by
      rw [hpow]
      apply Nat.div_lt_of_lt_mul
      rw [← pow_add]
      have e : c.v.y.ldh + (cd.lJ - c.v.y.ldh) = cd.lJ := by omega
      rw [e]
      exact hP
    have r := stretch_value ρ c.v q cd.lJ 0 (cd.lJ - c.v.y.ldh) hsz (by omega) hdiv
    rw [Nat.zero_add, Nat.add_zero] at r
    exact r
  · intro x hx
    have r := stretch_value ρ c.v q cd.lJ (cd.lJ - c.v.y.ldh) c.v.y.ldh hsz (by omega) (p := x)
      (by rw [← hpow]; exact hx)
    have e : cd.lJ - c.v.y.ldh + c.v.y.ldh = cd.lJ := by omega
    rw [e] at r
    rw [hlfc]
    exact r

end Heads

/-! ## What is asked of the layout and of the library's sizes -/

/-- What the theorems on the two factors ask of the verifier's layout and points and of the
library's sizes D. (q, cd, s): the call that holds the segment QK, with its number, and the
segment. -/
structure QKFits (c : ClaimEnv) (D : Dim) (q : ℕ) (cd : CallD) (s : Seg) : Prop where
  /-- the call that holds QK -/
  found : c.v.callOf "QK" = some (q, cd, s)
  /-- the call's point has its coordinates of the layer and the column -/
  size : c.v.y.h.ll + cd.lJ ≤ (c.v.zk.getD q #[]).size
  /-- the positions -/
  T : c.v.y.T = 2 ^ c.v.y.h.lt
  /-- the width of a head is a power of two -/
  pow : c.v.y.h.dh = 2 ^ c.v.y.ldh
  /-- and even -/
  two : 1 ≤ c.v.y.ldh
  /-- at most 64 heads -/
  heads : c.v.y.h.H + c.v.y.h.Gk ≤ 64
  /-- the tensor q has the features of the query heads -/
  tq : ∀ t : Ten, c.v.y.T_ "q" = some t → t.J = c.v.y.h.H * c.v.y.h.dh
  /-- the library's sizes agree with the shape -/
  sized : Sized c.v.y.h D
  /-- the call has as many columns as the library's call of the family QK -/
  lJ : cd.lJ = Inst.Model.FFSeg.lJ D (call .QK)
  /-- each entry of QK lies in the column that the library's rule gives it -/
  pos : ∀ x, x < len D .QK → s.pos.getD x 0 = Inst.Model.FFSeg.pos D .QK x

section Fits

variable {c : ClaimEnv} {D : Dim} {q : ℕ} {cd : CallD} {s : Seg}

/-- The library's number of bits of a channel (a logarithm rounded down) is the verifier's (rounded
up). -/
theorem QKFits.lch_eq (F : QKFits c D q cd s) : lch D = c.v.y.ldh := by
  unfold lch
  rw [F.sized.ch, F.pow, Nat.log2_two_pow]

/-- The length of the family QK. -/
theorem QKFits.len_eq (F : QKFits c D q cd s) :
    len D .QK = (c.v.y.h.H + c.v.y.h.Gk) * c.v.y.h.dh := by
  have e : len (dimOf c.v.y.h) .QK = c.v.y.h.H * c.v.y.h.dh + c.v.y.h.Gk * c.v.y.h.dh := rfl
  rw [F.sized.len_eq, e, Nat.add_mul]

/-- Every column of QK is one of the call's. -/
theorem QKFits.inside (F : QKFits c D q cd s) :
    ∀ x, x < (c.v.y.h.H + c.v.y.h.Gk) * c.v.y.h.dh → s.pos.getD x 0 < 2 ^ cd.lJ := by
  intro x hx
  have hx' : x < len D .QK := by
    rw [F.len_eq]
    exact hx
  rw [F.pos x hx', F.lJ]
  exact Inst.Model.FFSeg.IndexFacts.pos_lt D hx'

/-- Where headWeights returns, the library's sizes meet the library's own condition for the panel of
the family QK. -/
theorem QKFits.chOK (F : QKFits c D q cd s) {ah lfc : Array E}
    (h : c.headWeights = some (ah, lfc)) : D.ChOK where
  pow := by
    rw [F.lch_eq, F.sized.ch]
    exact F.pow
  two := by
    rw [F.lch_eq]
    exact F.two
  col := by
    rw [F.lch_eq, ← F.lJ]
    exact headWeights_ldh c F.found F.size h

variable {K : Type} [Field K] (ρ : Reading K)

/-- The weights of the heads. Entry hd of the first array of headWeights reads as the library's AH
at the head hd, with the point of the verifier's call in the place of the library's, for hd below
nq + nkv; every other entry, and what is read past the array's end, is 0. -/
theorem AH_at (F : QKFits c D q cd s) {ah lfc : Array E} (h : c.headWeights = some (ah, lfc))
    (hd : ℕ) : ρ.val (ah.getD hd zeroE) =
      if hd < D.P.nq + D.P.nkv then AHP D (pt ρ (c.v.zk.getD q #[])) hd else 0 := by
  by_cases hhd : hd < D.P.nq + D.P.nkv
  · have hhd' : hd < c.v.y.h.H + c.v.y.h.Gk := by
      rw [← F.sized.nq, ← F.sized.nkv]
      exact hhd
    have hpos : 0 < c.v.y.h.dh := by
      rw [F.pow]
      positivity
    have h1 : (hd + 1) * c.v.y.h.dh ≤ (c.v.y.h.H + c.v.y.h.Gk) * c.v.y.h.dh :=
      Nat.mul_le_mul_right _ hhd'
    have h2 : (hd + 1) * c.v.y.h.dh = hd * c.v.y.h.dh + c.v.y.h.dh := by ring
    have hlt : hd * c.v.y.h.dh < len D .QK := by
      rw [F.len_eq]
      omega
    rw [if_pos hhd,
      (headWeights_value ρ c F.found F.size F.pow F.heads F.tq F.inside h).1 hd hhd']
    unfold AHP
    rw [F.lch_eq, ← F.lJ, F.sized.lL, F.sized.ch, Nat.mul_comm c.v.y.h.dh hd, ← F.pos _ hlt]
  · have hge : c.v.y.h.H + c.v.y.h.Gk ≤ hd := by
      rw [← F.sized.nq, ← F.sized.nkv]
      omega
    obtain ⟨-, -, -, -, -, hz, -⟩ := headWeights_entries c F.found h
    rw [if_neg hhd, hz hd hge, ρ.zero]

/-- The first array of headWeights has 64 entries. -/
theorem AH_size {ah lfc : Array E} (h : c.headWeights = some (ah, lfc)) : ah.size = 64 := by
  obtain ⟨q, cd, s, hcall⟩ := headWeights_call c h
  obtain ⟨-, -, -, -, hs, -⟩ := headWeights_entries c hcall h
  exact hs

/-- Entry x of the second array of headWeights, for a channel x below dh, reads as the library's lf
at x, with the point of the verifier's call in the place of the library's. -/
theorem lf_at (F : QKFits c D q cd s) {ah lfc : Array E} (h : c.headWeights = some (ah, lfc))
    {x : ℕ} (hx : x < c.v.y.h.dh) :
    ρ.val (lfc.getD x zeroE) = lfP D (pt ρ (c.v.zk.getD q #[])) x := by
  rw [(headWeights_value ρ c F.found F.size F.pow F.heads F.tq F.inside h).2 x hx]
  unfold lfP
  rw [F.lch_eq, ← F.lJ, F.sized.lL]

end Fits

/-! ## The factor on the channels within a head -/

/-- The sum over the tokens in ropeFactor: the rotary table's entries for layer lam of the group and
the pair i of channels, cosines or sines, under the weights et. -/
def ropeSum (c : ClaimEnv) (et : Array E) (lam i : ℕ) (sine : Bool) : E :=
  (List.range c.v.y.T).foldl
    (fun a t => addE a (mulE (et.getD t zeroE)
      (ofInt (ropeC c.v.y.h c.v.sc c.rope (c.v.lay lam) t i sine)))) zeroE

/-- ropeFactor, written out with ropeSum. -/
theorem ropeFactor_eq (c : ClaimEnv) (et lfc : Array E) (lam : ℕ) :
    c.ropeFactor et lfc lam = (Array.range (c.v.y.h.dh / 2)).flatMap fun i =>
      #[addE (mulE (ropeSum c et lam i false) (lfc.getD (2 * i) zeroE))
          (mulE (ropeSum c et lam i true) (lfc.getD (2 * i + 1) zeroE)),
        subE (mulE (ropeSum c et lam i false) (lfc.getD (2 * i + 1) zeroE))
          (mulE (ropeSum c et lam i true) (lfc.getD (2 * i) zeroE))] := rfl

/-- It has two entries for each pair of channels. -/
theorem ropeFactor_size (c : ClaimEnv) (et lfc : Array E) (lam : ℕ) :
    (c.ropeFactor et lfc lam).size = 2 * (c.v.y.h.dh / 2) := by
  rw [ropeFactor_eq]
  exact pairs_size _ _ _

/-- Its two entries for the pair i. -/
theorem ropeFactor_getD (c : ClaimEnv) (et lfc : Array E) (lam : ℕ) {i : ℕ}
    (hi : i < c.v.y.h.dh / 2) :
    (c.ropeFactor et lfc lam).getD (2 * i) zeroE =
        addE (mulE (ropeSum c et lam i false) (lfc.getD (2 * i) zeroE))
          (mulE (ropeSum c et lam i true) (lfc.getD (2 * i + 1) zeroE)) ∧
      (c.ropeFactor et lfc lam).getD (2 * i + 1) zeroE =
        subE (mulE (ropeSum c et lam i false) (lfc.getD (2 * i + 1) zeroE))
          (mulE (ropeSum c et lam i true) (lfc.getD (2 * i) zeroE)) := by
  rw [ropeFactor_eq]
  exact pairs_getD _ _ _ hi

section Rope

variable {K : Type} [Field K] (ρ : Reading K)

/-- The hypothesis on the rotary tables, for layer lam of the group: the entries that the verifier
reads for that layer, at every position t and every pair i of channels, read in K as the entries of
the library's tables C and S at layer L0 + lam. Nothing is asked past the positions or the pairs. -/
structure RopeFits (c : ClaimEnv) (D : Dim) (tb : Tables) (L0 lam : ℕ) : Prop where
  /-- the cosines -/
  cos : ∀ t i, t < 2 ^ D.lT → i < c.v.y.h.dh / 2 →
    ρ.val (ofInt (ropeC c.v.y.h c.v.sc c.rope (c.v.lay lam) t i false)) =
      ((tb.C (L0 + lam) t i : ℤ) : K)
  /-- the sines -/
  sin : ∀ t i, t < 2 ^ D.lT → i < c.v.y.h.dh / 2 →
    ρ.val (ofInt (ropeC c.v.y.h c.v.sc c.rope (c.v.lay lam) t i true)) =
      ((tb.S (L0 + lam) t i : ℤ) : K)

/-- The sum over the tokens under the equality weights of the point rt reads as the multilinear
extension, at rt, of what the table's entries read as. -/
theorem ropeSum_value (c : ClaimEnv) (D : Dim) (hT : c.v.y.T = 2 ^ D.lT)
    (hrt : c.rt.size = D.lT) (lam i : ℕ) (sine : Bool) (tab : ℕ → K)
    (htab : ∀ t, t < 2 ^ D.lT →
      ρ.val (ofInt (ropeC c.v.y.h c.v.sc c.rope (c.v.lay lam) t i sine)) = tab t) :
    ρ.val (ropeSum c (eqTab c.rt) lam i sine) = Blocks.ext D.lT tab (pt ρ c.rt) := by
  unfold ropeSum Blocks.ext
  refine (foldl_madd_range ρ (fun t => (eqTab c.rt).getD t zeroE)
    (fun t => ofInt (ropeC c.v.y.h c.v.sc c.rope (c.v.lay lam) t i sine)) _).trans ?_
  rw [hT]
  refine sum_congr rfl fun t ht => ?_
  have ht' := mem_range.mp ht
  show ρ.val ((eqTab c.rt).getD t zeroE) *
      ρ.val (ofInt (ropeC c.v.y.h c.v.sc c.rope (c.v.lay lam) t i sine)) =
    Blocks.eqN D.lT 0 (pt ρ c.rt) t * tab t
  rw [eqTab_value ρ c.rt t (by rw [hrt]; exact ht'), hrt, htab t ht']

variable {c : ClaimEnv} {D : Dim} {q : ℕ} {cd : CallD} {s : Seg}

/-- The factor on the channels. Entry x, for a channel x below dh, of the array that ropeFactor
makes for layer lam of the group from the equality weights of the point rt and the second array of
headWeights reads as the library's kp at layer lam and channel x, with the point of the verifier's
call in the place of the library's and the rotary tables contracted at rt. Asked beside QKFits: rt
has one coordinate for each bit of a position; the rotary tables (RopeFits). -/
theorem kap_at (F : QKFits c D q cd s) {ah lfc : Array E} (h : c.headWeights = some (ah, lfc))
    (hrt : c.rt.size = D.lT) {tb : Tables} {L0 lam : ℕ} (R : RopeFits ρ c D tb L0 lam) {x : ℕ}
    (hx : x < c.v.y.h.dh) :
    ρ.val ((c.ropeFactor (eqTab c.rt) lfc lam).getD x zeroE) =
      kpP D tb L0 (pt ρ (c.v.zk.getD q #[])) (pt ρ c.rt) lam x := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le F.two
  have hev : c.v.y.h.dh = 2 * 2 ^ k := by rw [F.pow, hk, pow_add, pow_one]
  have hT : c.v.y.T = 2 ^ D.lT := by rw [F.T, F.sized.lT]
  have hC : ∀ i, i < c.v.y.h.dh / 2 →
      ρ.val (ropeSum c (eqTab c.rt) lam i false) = Ct D tb L0 lam i (pt ρ c.rt) :=
    fun i hi => ropeSum_value ρ c D hT hrt lam i false _ (fun t ht => R.cos t i ht hi)
  have hS : ∀ i, i < c.v.y.h.dh / 2 →
      ρ.val (ropeSum c (eqTab c.rt) lam i true) = St D tb L0 lam i (pt ρ c.rt) :=
    fun i hi => ropeSum_value ρ c D hT hrt lam i true _ (fun t ht => R.sin t i ht hi)
  rcases Nat.even_or_odd' x with ⟨i, rfl | rfl⟩
  · have hi : i < c.v.y.h.dh / 2 := by omega
    rw [(ropeFactor_getD c _ lfc lam hi).1, ρ.add, ρ.mul, ρ.mul, hC i hi, hS i hi,
      lf_at ρ F h hx, lf_at ρ F h (x := 2 * i + 1) (by omega)]
    unfold kpP
    rw [if_pos (by omega), (by omega : 2 * i / 2 = i)]
  · have hi : i < c.v.y.h.dh / 2 := by omega
    rw [(ropeFactor_getD c _ lfc lam hi).2, ρ.sub, ρ.mul, ρ.mul, hC i hi, hS i hi,
      lf_at ρ F h hx, lf_at ρ F h (x := 2 * i) (by omega)]
    unfold kpP
    rw [if_neg (by omega), (by omega : (2 * i + 1) / 2 = i), (by omega : 2 * i + 1 - 1 = 2 * i)]

/-- The array has one entry for each channel of a head. -/
theorem kap_size (F : QKFits c D q cd s) (et lfc : Array E) (lam : ℕ) :
    (c.ropeFactor et lfc lam).size = c.v.y.h.dh := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le F.two
  have hev : c.v.y.h.dh = 2 * 2 ^ k := by rw [F.pow, hk, pow_add, pow_one]
  rw [ropeFactor_size]
  omega

/-! ## The two factors, as factors of a claim -/

/-- The factor with the first array of headWeights written out, which claimsT gives to a group of
the name hd, weighs the index hd with the library's AH below nq + nkv, and with 0 from
there on. Asked of the group: its class is not 'E'. Its name and its number of indices are not
read. -/
theorem fac_hd (F : QKFits c D q cd s) {ah lfc : Array E} (h : c.headWeights = some (ah, lfc))
    (G : WsGrp) (hA : (G.cls == 'E') = false) (hd : ℕ) :
    facAt ρ ({ AV := ah } : WsFac) G hd =
      if hd < D.P.nq + D.P.nkv then AHP D (pt ρ (c.v.zk.getD q #[])) hd else 0 := by
  unfold facAt
  rw [if_neg (by rw [hA]; exact Bool.false_ne_true)]
  exact AH_at ρ F h hd

/-- The factor with ropeFactor's array written out, which claimsT gives to a group of the name cd,
weighs the index x, below dh, with the library's kp. Asked of the group: its class is
not 'E'. Its name and its number of indices are not read. -/
theorem fac_cd (F : QKFits c D q cd s) {ah lfc : Array E} (h : c.headWeights = some (ah, lfc))
    (hrt : c.rt.size = D.lT) {tb : Tables} {L0 lam : ℕ} (R : RopeFits ρ c D tb L0 lam)
    (G : WsGrp) (hA : (G.cls == 'E') = false) {x : ℕ} (hx : x < c.v.y.h.dh) :
    facAt ρ ({ AV := c.ropeFactor (eqTab c.rt) lfc lam } : WsFac) G x =
      kpP D tb L0 (pt ρ (c.v.zk.getD q #[])) (pt ρ c.rt) lam x := by
  unfold facAt
  rw [if_neg (by rw [hA]; exact Bool.false_ne_true)]
  exact kap_at ρ F h hrt R hx

end Rope

/-! ## The same with the library's own point -/

section Lib

variable {K : Type} [Field K] (D : Dim)

/-- AHP at a point that agrees with the library's point of the call on its aC coordinates is the
library's AH. -/
theorem AHP_eq_AH {z ζ : ℕ → K} (h : ∀ j < aC D (call .QK), ζ j = zc D z (call .QK) j) (hd : ℕ) :
    AHP D ζ hd = AH D z hd :=
  AHP_congr D h hd

/-- kpP at such a point is the library's kp. Asked: a head's channels have at most as many bits as
the call's columns (a field of the library's Dim.ChOK). -/
theorem kpP_eq_kp (hcol : lch D ≤ lJ D (call .QK)) (tb : Tables) (L0 : ℕ) {z ζ : ℕ → K}
    (h : ∀ j < aC D (call .QK), ζ j = zc D z (call .QK) j) (zh : ℕ → K) (l x : ℕ) :
    kpP D tb L0 ζ zh l x = kp D tb L0 z zh l x :=
  kpP_congr D hcol tb L0 h zh l x

end Lib

/-! ## The record QKFits is a conclusion: what the layout's tests give -/

/-- A number from 2^k to 2^(k + 1) - 1 has bit k. -/
theorem bit_top {n k : ℕ} (h1 : 2 ^ k ≤ n) (h2 : n < 2 ^ (k + 1)) : n.testBit k = true := by
  rw [Inst.Model.FFSeg.IndexFacts.testBit_iff]
  have e : n / 2 ^ k = 1 := by
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [pow_succ] at h2
      omega
  simp [e]

/-- A number that is not 0 and passes the verifier's test manyBits is 2 to its rounded-up
logarithm. -/
theorem pow_of_manyBits {x : ℕ} (h : manyBits x = false) (h0 : x ≠ 0) : x = 2 ^ ceilLog2 x := by
  have hand : x &&& (x - 1) = 0 := by
    unfold manyBits at h
    simpa using h
  obtain ⟨k, hk⟩ : ∃ k, x = 2 ^ k := by
    by_contra hne
    have hlo : 2 ^ Nat.log 2 x ≤ x := Nat.pow_log_le_self 2 h0
    have hhi : x < 2 ^ (Nat.log 2 x + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
    have hne' : x ≠ 2 ^ Nat.log 2 x := fun e => hne ⟨_, e⟩
    generalize Nat.log 2 x = k at hlo hhi hne'
    have b1 : x.testBit k = true := bit_top hlo hhi
    have b2 : (x - 1).testBit k = true := bit_top (by omega) (by omega)
    have b3 : (x &&& (x - 1)).testBit k = true := by rw [Nat.testBit_and, b1, b2]; rfl
    rw [hand, Nat.zero_testBit] at b3
    cases b3
  subst hk
  rw [ceilLog2_eq_clog, Nat.clog_pow 2 k (by norm_num)]

/-- Three more plain facts on a layout's numbers, beside the record Laid: the positions; the width
of a head is 2^ldh; it is even. Each is the text of a line of layoutBase
(OnBytes/Model/LayerLayout.lean), or follows from its test on the heads. -/
structure HeadsLaid (y : Lay) : Prop where
  /-- the positions -/
  T : y.T = 2 ^ y.h.lt
  /-- the width of a head -/
  pow : y.h.dh = 2 ^ y.ldh
  /-- it is even -/
  two : 1 ≤ y.ldh

/-- The first half of the layout. -/
theorem headsLaid_of_base {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layoutBase h pc = .ok y) : HeadsLaid y := by
  unfold layoutBase at hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨e9, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨taken, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  generalize Model.Layer.gateTables h.eg h.smax h.p3 h.gcl = gt at hy
  obtain ⟨silu, fs⟩ := gt
  cases hy
  have c1 := or_false_split e9
  have c2 := or_false_split c1.1
  have c3 := or_false_split c2.1
  have c4 := or_false_split c3.1
  have c5 := or_false_split c4.1
  have hp : h.dh = 2 ^ ceilLog2 h.dh := pow_of_manyBits c4.2 (by simpa using c5.2)
  have h2 : 2 ≤ h.dh := Nat.not_lt.mp (of_decide_eq_false c3.2)
  refine { T := rfl, pow := hp, two := ?_ }
  show 1 ≤ ceilLog2 h.dh
  by_contra hc
  have e : ceilLog2 h.dh = 0 := by omega
  rw [e] at hp
  omega

/-- Every layout that the verifier returns has these facts: the second half of the layout changes
none of the fields that they name. -/
theorem headsLaid_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) : HeadsLaid y := by
  unfold layout at hy
  obtain ⟨y0, h0, h1⟩ := ok_of_bind hy
  have L := headsLaid_of_base h0
  obtain ⟨-, fo, kbm, rfl⟩ := look_keeps h1
  exact { T := L.T, pow := L.pow, two := L.two }

/-- The columns of a call of the verifier's layout whose line names the families of the library's
call cc, in the library's order: as many as the library's, and each entry in the column that the
library's rule gives it. These are two fields of the record CallFits
(Johnson/Road/FormsKeysKF.lean), here without a hypothesis on the call's marks. Asked as in
callFits_of_layout (Johnson/Road/FormsKeysKV.lean): the switches; sizes that agree with the shape;
the verifier's least logarithm of the number of columns is at most the library's logarithm. -/
theorem cols_of_layout {h : Shape} {pc : List (List String)} {y : Lay} (hy : layout h pc = .ok y)
    (S : Switches h) {D : Dim} (Z : Sized h D) {cd : CallD} (hcd : cd ∈ y.calls) {cc : Fin 8}
    (hn : cd.segs.map (·.name) = (fams cc).map segName)
    (hfl : h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D cc)) :
    cd.lJ = lJ D cc ∧
      ∀ s ∈ cd.segs, ∀ x, x < len D (famS s) → s.pos.getD x 0 = pos D (famS s) x := by
  have A := admitted_of_layout hy S.p3
  have hlen : ∀ s ∈ cd.segs, s.n = len D (famS s) := by
    intro s hs
    obtain ⟨fam, a1, a2, -, -, -⟩ := segs_of_layout hy S cd hcd s hs
    have e : famS s = fam := by
      unfold famS
      rw [a1, famOf_segName]
      rfl
    rw [e]
    exact a2.trans (Z.len_eq fam).symm
  have hfam : cd.segs.map famS = fams cc := by
    have e1 : cd.segs.map famS = (cd.segs.map (·.name)).map fun n => (famOf n).getD .G := by
      rw [List.map_map]
      rfl
    rw [e1, hn, List.map_map]
    conv_rhs => rw [← List.map_id (fams cc)]
    refine List.map_congr_left fun s _ => ?_
    show (famOf (segName s)).getD .G = s
    rw [famOf_segName]
    rfl
  have hlt : ∀ s ∈ fams cc, len D s < 2 ^ (topBit + 1) := fun s _ => by
    rw [Z.len_eq s]
    exact len_lt A s
  obtain ⟨cl, taken, -, -, h3⟩ := A.calls
  rw [h3] at hcd
  obtain ⟨c0, -, rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hcd)
  have hl := lengths_of_segs D cc c0.1 c0.2.1 c0.2.2 _ famS hfam hlen
  exact ⟨lJ_eq D cc c0.1 c0.2.1 c0.2.2 _ hl hlt hfl,
    pos_eq_segs D cc c0.1 c0.2.1 c0.2.2 _ famS hfam hlen hlt⟩

/-- The record QKFits, concluded. On a layout that the verifier has returned, under the switches,
for library sizes that agree with the shape: if the call that holds QK names the families of the
library's call of QK in the library's order (hn), the least number of columns does not bite (hfl),
and the call's point has its coordinates of the layer and the column (hsz), the record holds. -/
theorem qkFits_of_layout {h : Shape} {pc : List (List String)} {c : ClaimEnv}
    (hy : layout h pc = .ok c.v.y) (S : Switches h) {D : Dim} (Z : Sized h D) {q : ℕ} {cd : CallD}
    {s : Seg} (hcall : c.v.callOf "QK" = some (q, cd, s))
    (hn : cd.segs.map (·.name) = (fams (call .QK)).map segName)
    (hfl : h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D (call .QK)))
    (hsz : c.v.y.h.ll + cd.lJ ≤ (c.v.zk.getD q #[]).size) : QKFits c D q cd s := by
  have A := admitted_of_layout hy S.p3
  have HL := headsLaid_of_layout hy
  obtain ⟨hq, hs, hname⟩ := callOf_spec hcall
  obtain ⟨k1, k2⟩ := cols_of_layout hy S Z (Array.mem_of_getElem? hq) hn hfl
  have hfam : famS s = .QK := by
    unfold famS
    rw [hname]
    rfl
  have S' : Switches c.v.y.h := by
    rw [A.shape]
    exact S
  refine { found := hcall, size := hsz, T := HL.T, pow := HL.pow, two := HL.two, heads := ?_,
           tq := ?_, sized := ?_, lJ := k1, pos := ?_ }
  · rw [A.shape]
    exact A.heads
  · intro t ht
    obtain ⟨ten, h1, -, -, -, hJ, -⟩ := ten_of A.laid S' .q (Or.inl rfl)
    have e : t = ten := Option.some.inj (ht.symm.trans h1)
    rw [e]
    exact hJ
  · rw [A.shape]
    exact Z
  · intro x hx
    have r := k2 s hs x
    rw [hfam] at r
    exact r hx

/-! ## The hypothesis on the rotary tables can be met -/

section Met

variable {K : Type} [Field K] {ρ : Reading K}

/-- A reading that takes the program's numerals to numbers takes its integers to integers. -/
theorem Numerals.ofInt (hρ : Numerals ρ) (n : ℤ) : ρ.val (Model.ofInt n) = (n : K) := by
  have hp : 0 < pW.toNat := by
    have e : pW.toNat = 18446744069414584321 := rfl
    omega
  have red : ∀ m : ℕ, m < pW.toNat → ofF m.toUInt64 = Model.ofNat m := by
    intro m hm
    unfold Model.ofNat Model.fOfNat
    rw [Nat.mod_eq_of_lt hm]
  have hmod : ∀ m : ℕ, ((m % pW.toNat : ℕ) : K) = (m : K) := by
    intro m
    rw [← hρ.ofNat, ← hρ.ofNat]
    unfold Model.ofNat Model.fOfNat
    rw [Nat.mod_mod]
  have hp0 : ((pW.toNat : ℕ) : K) = 0 := by
    have e := hmod pW.toNat
    rw [Nat.mod_self, Nat.cast_zero] at e
    exact e.symm
  have hr : n.natAbs % pW.toNat < pW.toNat := Nat.mod_lt _ hp
  show ρ.val (ofF (if n < 0 ∧ n.natAbs % pW.toNat ≠ 0
    then (pW.toNat - n.natAbs % pW.toNat).toUInt64 else (n.natAbs % pW.toNat).toUInt64)) = (n : K)
  by_cases hc : n < 0 ∧ n.natAbs % pW.toNat ≠ 0
  · rw [if_pos hc, red _ (by omega), hρ.ofNat, Nat.cast_sub hr.le, hp0, hmod, zero_sub,
      Nat.cast_natAbs, abs_of_neg hc.1, Int.cast_neg, neg_neg]
  · rw [if_neg hc, red _ hr, hρ.ofNat, hmod]
    by_cases hn : n < 0
    · have h0 : n.natAbs % pW.toNat = 0 := by
        by_contra hh
        exact hc ⟨hn, hh⟩
      have e1 : ((n.natAbs : ℕ) : K) = 0 := by rw [← hmod, h0, Nat.cast_zero]
      have e2 : (n : K) = -((n.natAbs : ℕ) : K) := by
        rw [Nat.cast_natAbs, abs_of_neg hn, Int.cast_neg, neg_neg]
      rw [e2, e1, neg_zero]
    · rw [Nat.cast_natAbs, abs_of_nonneg (by omega)]

/-- The verifier's rotary entry for a layer without the rotary step. -/
theorem ropeC_off {h : Shape} {sc : Model.Layer.Scales} {rope : Array ℕ} {l : ℕ}
    (h0 : sc.klRp l = 0) (t i : ℕ) (sine : Bool) :
    ropeC h sc rope l t i sine = if sine then 0 else 2 ^ h.cs := by
  unfold ropeC
  exact if_pos (by rw [h0]; rfl)

/-- The verifier's rotary entry for a layer with the rotary step. -/
theorem ropeC_on {h : Shape} {sc : Model.Layer.Scales} {rope : Array ℕ} {l : ℕ}
    (h0 : sc.klRp l ≠ 0) (t i : ℕ) (sine : Bool) :
    ropeC h sc rope l t i sine =
      (rope.getD ((if sine then 2 ^ h.lt * (h.dh / 2) else 0) + t * (h.dh / 2) + i) 0 : ℤ) -
        4096 := by
  unfold ropeC
  exact if_neg (by simpa using h0)

/-- RopeFits from equations of integers. If the scale file marks the layer as one without the rotary
step: the library's C is 2^cs and its S is 0. Otherwise: the word of the verifier's table at
t (dh / 2) + i is the library's C plus 4096, and the word 2^lt (dh / 2) places further on is the
library's S plus 4096. All for the positions t and the pairs i of RopeFits alone. -/
theorem ropeFits_of_words (hρ : Numerals ρ) (c : ClaimEnv) (D : Dim) (tb : Tables) (L0 lam : ℕ)
    (hoff : c.v.sc.klRp (c.v.lay lam) = 0 → ∀ t i, t < 2 ^ D.lT → i < c.v.y.h.dh / 2 →
      tb.C (L0 + lam) t i = 2 ^ c.v.y.h.cs ∧ tb.S (L0 + lam) t i = 0)
    (hon : c.v.sc.klRp (c.v.lay lam) ≠ 0 → ∀ t i, t < 2 ^ D.lT → i < c.v.y.h.dh / 2 →
      (c.rope.getD (t * (c.v.y.h.dh / 2) + i) 0 : ℤ) = tb.C (L0 + lam) t i + 4096 ∧
      (c.rope.getD (2 ^ c.v.y.h.lt * (c.v.y.h.dh / 2) + t * (c.v.y.h.dh / 2) + i) 0 : ℤ) =
        tb.S (L0 + lam) t i + 4096) :
    RopeFits ρ c D tb L0 lam := by
  have key : ∀ t i, t < 2 ^ D.lT → i < c.v.y.h.dh / 2 →
      ropeC c.v.y.h c.v.sc c.rope (c.v.lay lam) t i false = tb.C (L0 + lam) t i ∧
      ropeC c.v.y.h c.v.sc c.rope (c.v.lay lam) t i true = tb.S (L0 + lam) t i := by
    intro t i ht hi
    by_cases h0 : c.v.sc.klRp (c.v.lay lam) = 0
    · obtain ⟨a, b⟩ := hoff h0 t i ht hi
      rw [ropeC_off h0, ropeC_off h0]
      exact ⟨a.symm, b.symm⟩
    · obtain ⟨a, b⟩ := hon h0 t i ht hi
      rw [ropeC_on h0, ropeC_on h0]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      omega
  exact ⟨fun t i ht hi => by rw [hρ.ofInt, (key t i ht hi).1],
    fun t i ht hi => by rw [hρ.ofInt, (key t i ht hi).2]⟩

/-- Tables of the library whose C and S are the verifier's own rotary entries. The three other
functions, which the rotary step does not read, are 0. -/
def tbRope (c : ClaimEnv) : Tables :=
  ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun L t i => ropeC c.v.y.h c.v.sc c.rope L t i false,
    fun L t i => ropeC c.v.y.h c.v.sc c.rope L t i true⟩

/-- RopeFits can be met: for every environment of the verifier, at the tables tbRope, with L0 the
number of the group's first layer in the model. True by construction: it shows that the hypothesis
is not empty, and nothing on the library's reference tables. -/
theorem ropeFits_met (hρ : Numerals ρ) (c : ClaimEnv) (D : Dim) (lam : ℕ) :
    RopeFits ρ c D (tbRope c) (c.v.g * c.v.y.Lam) lam :=
  ⟨fun _ _ _ _ => hρ.ofInt _, fun _ _ _ _ => hρ.ofInt _⟩

end Met

/-! ## A run: the hypotheses hold together -/

/-- At the made-up shape hR8 with the library's eight lines of calls
(Johnson/Road/FormsKeysRun8.lean) and made-up points, for each group of layers: whether callOf finds
QK in a call whose line is the library's, the least number of columns does not bite, the call's
point is long enough, the token point has lt coordinates, and headWeights returns. -/
def metQK : Except String (List Bool) := do
  let y ← layout hR8 pcR8
  let sc ← Model.Layer.scalesOf hR8 klR
  let rd ← Model.Layer.readsOf y
  let rope ← Model.Layer.ropeOf y.h
  (List.range y.NGr).mapM fun g =>
    match envR y sc rd g with
    | none => throw "no tables"
    | some v =>
      let c : ClaimEnv := { v, wsLay := {}, rope, rs := #[], rt := elemsR 900 y.h.lt }
      match v.callOf "QK" with
      | none => pure false
      | some (q, cd, _) =>
        pure ((cd.segs.map (·.name)) == (fams (call .QK)).map segName &&
          decide (hR8.nmin - hR8.ll - hR8.lt ≤ Nat.clog 2 (used (dimOf hR8) (call .QK))) &&
          decide (y.h.ll + cd.lJ ≤ (v.zk.getD q #[]).size) && c.rt.size == (dimOf hR8).lT &&
          c.headWeights.isSome)

#guard (match metQK with
  | .ok r => r == [true, true]
  | .error _ => false)

#print axioms headWeights_entries
#print axioms headWeights_value
#print axioms QKFits.chOK
#print axioms AH_at
#print axioms lf_at
#print axioms kap_at
#print axioms fac_hd
#print axioms fac_cd
#print axioms AHP_eq_AH
#print axioms kpP_eq_kp
#print axioms headsLaid_of_layout
#print axioms cols_of_layout
#print axioms qkFits_of_layout
#print axioms Numerals.ofInt
#print axioms ropeFits_of_words
#print axioms ropeFits_met

end OnBytes.Road
