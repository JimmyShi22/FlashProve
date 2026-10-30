-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysCalls.lean: the calls of a lookup as blocks of trees: the library's conditions
on such blocks hold of the library's eight calls and of what the verifier's Forest.shape returns.

Blocks/LookupCalls.lean of the library speaks of a forest of trees whose calls are blocks of trees
(LkCall: 2^e trees with one prefix). Under four conditions on the blocks (CallsOK) and one on the
keys (KeysOf) it proves that the extension of the vector of leaves, at a point, is the sum over the
calls of a call's weight times (alpha less the extension of the call's keys at the call's point)
(CallsOK.ext_leafK), and that all keys of all trees lie in their tables if and only if all keys of
all calls do (CallsOK.inTable_iff). This file shows CallsOK and KeysOf. The second theorem asks
beside them that the trees of a call have the call's table: that is a matter of the letter tb, which
is free here.

WHO READS THE TARGET. Blocks/LookupCalls.lean is imported by Inst/Model/FF/Objects.lean alone, which
takes LkCall from it. By a search of the library's files no other file reads its CallsOK, KeysOf,
wCall, zCall or its two theorems; a few files have other things of the same names. So what is joined
here is joined to two proved theorems that nothing else in the library reads. By a reading of the
library's files on that lookup (no theorem, and not by the writer of this file), the lookup that the
library proves over these letters is another than the verifier's: it has a product, a table and
counts for each tree, and no shift.

What is compared with what. In the first part the library with itself: the eight calls of a
feed-forward segment (lkCall in Inst/Model/FF/Objects.lean; firstTree, trees, callOf in
Inst/Model/FF/Index.lean; forestKey, keyVec in Inst/Model/FF/Trace.lean) against CallsOK and KeysOf.
In the second part the verifier's Lean text (Forest.shape in OnBytes/Model/Forest.lean; callWeight
and the line of Forest.pad for the calls' points in OnBytes/Model/Look.lean; eqTab) against the
library's CallsOK, wCall, zCall and eqN.

Main definitions, all of this file and none the library's or the verifier's: lkOf, lkP, tagKey,
tagVec, leafAll; foP, foCall. So leaf_ff and ext_leafAll set objects of this file, made of the
library's, against the library's; callsOK_shape and what follows it set objects of this file, made
of the verifier's numbers, against the library's. lkP P0 D and foP P0 fo take from
D and from fo the three numbers that CallsOK, KeysOf, wCall, zCall and the vector of leaves read
(the depth of a tree, the bits of a tree's number, the number of trees). The library's record of
letters has more: the tables, the padding's row and count of each tree, the sizes of tables and
counts, two letters on rounds. They are those of any record P0; no statement of this file reads
them.
Main theorems.
 - callsOK_tiles: CallsOK for blocks of trees that are given by numbers.
 - callsOK_ff, keysOf_ff, keysOf_tag: for all sizes D, with no condition on them.
 - leaf_ff: the extension of the library's vector of leaves at the keys moved by the call's number
   times a shift is the sum over the eight calls of wc (al - c shift - the extension of keyVec at
   zc).
 - ext_leafAll: with al - k in the place of 0 at the trees that belong to no call.
 - callsOK_shape: CallsOK for what Forest.shape returns, for any calls.
 - wCall_of_look, zCall_of_look, ey_of_look: the verifier's weight of a call, point of a call and
   table of equality weights compute wCall, zCall and eqN, for any numbers of a forest.
 - leaf_shape: so, for any calls, the extension of the vector of leaves at zOf is the sum over the
   calls of the verifier's weight times (al less the extension of the call's keys at the verifier's
   point of the call).

The hypotheses. The first part has none. callsOK_shape asks that Forest.shape returns:
shape_of_layout (Johnson/Road/FormsKeysShape.lean) has that for every layout that the verifier
returns. The last four ask the lengths of the lookup's two points and the line of Forest.pad for
the calls' points, in the verifier's letters; Johnson/Road/FormsKeysLookP.lean has the lengths from
that routine's own lines and one of its tests; a guard of
Johnson/Road/FormsKeysRunZ.lean (padZ)
holds all of them together at a made-up lookup.

Which value is which: all are public, but the cells t and the weights w, which are free.

What is not claimed. Nothing before the lookup's join: the tie, the levels of the trees, the counts.
That the verifier's arrays are made by the lines of Forest.pad is asked. The verifier's sum over the
trees that belong to no call is not evaluated here; ey_of_look reads its weights. The program does
not import this file.
-/
import Johnson.Road.FormsKeysLook
import Johnson.Road.FormsKeysForest
import Inst.Model.FF.Objects

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open Blocks (LkPar LkCall ext eqN)
open OnBytes.Model (Reading Call eqTab)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell LW aC eC Dk sg NT trees firstTree pre zc wc lkCall keyVec forestKey)
open Inst.Model.FFSeg.IndexFacts (base Ord base_add_le_total tile_inj tile_cover treesTile
  callOf_spec callOf_eq Dk_le)

variable {K : Type} [Field K]

/-! ## Tools -/

/-- A number lies in block number k of blocks of t numbers. -/
theorem div_eq_iff_block {θ t k : ℕ} (ht : 0 < t) : θ / t = k ↔ k * t ≤ θ ∧ θ < k * t + t := by
  constructor
  · rintro rfl
    have h1 := Nat.div_add_mod θ t
    have h2 := Nat.mod_lt θ ht
    have e : θ / t * t = t * (θ / t) := Nat.mul_comm _ _
    omega
  · rintro ⟨h1, h2⟩
    have a : k ≤ θ / t := (Nat.le_div_iff_mul_le ht).mpr h1
    have b : θ / t < k + 1 :=
      (Nat.div_lt_iff_lt_mul ht).mpr (by rw [Nat.add_mul, Nat.one_mul]; exact h2)
    omega

/-- The extension of a constant plus a vector. -/
theorem ext_const_add (g : ℕ) (a : K) (f pt : ℕ → K) :
    ext g (fun k => a + f k) pt = a + ext g f pt := by
  rw [Blocks.ext_add g (fun _ => a) f pt, Blocks.ext_const]

/-- The extension reads as many coordinates of its point as the vector has index bits. -/
theorem ext_same_pt (g : ℕ) (f : ℕ → K) {u u' : ℕ → K} (h : ∀ j, j < g → u j = u' j) :
    ext g f u = ext g f u' := by
  unfold Blocks.ext
  refine sum_congr rfl fun X _ => ?_
  have e : eqN g 0 u X = eqN g 0 u' X :=
    eqN_congr' g 0 (fun j hj => by rw [Nat.zero_add]; exact h j hj) X
  rw [e]

/-- The equality weights of a point add up to 1. -/
theorem sum_eqN_one (g : ℕ) (pt : ℕ → K) : ∑ x ∈ range (2 ^ g), eqN g 0 pt x = 1 := by
  have h := Blocks.ext_const g (1 : K) pt
  unfold Blocks.ext at h
  simpa using h

/-! ## The trees that belong to no call -/

/-- The vector of leaves with al - k, not 0, at the trees that belong to no call. -/
def leafAll (P : LkPar K) (key : ℕ → ℕ → K) (al k : K) (x : ℕ) : K :=
  if x % 2 ^ P.σ < P.NT then al - key (x % 2 ^ P.σ) (x / 2 ^ P.σ) else al - k

/-- Its extension is that of the library's vector of leaves, plus al - k times the equality weights
of the numbers of the trees that belong to no call. -/
theorem ext_leafAll (P : LkPar K) (key : ℕ → ℕ → K) (al k : K) (z : ℕ → K) :
    ext (P.D + P.σ) (leafAll P key al k) z =
      ext (P.D + P.σ) (P.leafK key al) z +
        (al - k) * ∑ θ ∈ range (2 ^ P.σ), if θ < P.NT then 0 else eqN P.σ P.D z θ := by
  have e : leafAll P key al k =
      fun x => P.leafK key al x + if x % 2 ^ P.σ < P.NT then 0 else al - k := by
    funext x
    unfold leafAll LkPar.leafK
    split_ifs <;> ring
  rw [e, Blocks.ext_add]
  congr 1
  rw [Blocks.ext_two]
  have h1 : ∀ x, ∀ y ∈ range (2 ^ P.σ),
      eqN P.D 0 z x * eqN P.σ P.D z y *
          (if (x * 2 ^ P.σ + y) % 2 ^ P.σ < P.NT then 0 else al - k) =
        eqN P.D 0 z x * ((al - k) * if y < P.NT then 0 else eqN P.σ P.D z y) := by
    intro x y hy
    have hm : (x * 2 ^ P.σ + y) % 2 ^ P.σ = y := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (mem_range.mp hy)]
    rw [hm]
    split_ifs <;> ring
  have h2 : ∀ x ∈ range (2 ^ P.D),
      ∑ y ∈ range (2 ^ P.σ), eqN P.D 0 z x * eqN P.σ P.D z y *
          (if (x * 2 ^ P.σ + y) % 2 ^ P.σ < P.NT then 0 else al - k) =
        eqN P.D 0 z x *
          ((al - k) * ∑ y ∈ range (2 ^ P.σ), if y < P.NT then 0 else eqN P.σ P.D z y) := by
    intro x _
    rw [sum_congr rfl (h1 x), ← mul_sum, ← mul_sum]
  rw [sum_congr rfl h2, ← sum_mul, sum_eqN_one, one_mul]

/-! ## Blocks of trees, in letters -/

section Letters

/-- The letters P0 of a forest with the depth d of a tree, s bits of a tree's number and n trees.
The letters on tables, padding and counts stay those of P0. -/
def lkOf (P0 : LkPar K) (d s n : ℕ) : LkPar K := { P0 with D := d, σ := s, NT := n }

variable {C : Type} [Fintype C] [DecidableEq C] {P0 : LkPar K} {d s n : ℕ}

omit [Field K] [Fintype C] [DecidableEq C] in
/-- Blocks of 2^(e c) trees from first c on meet the library's conditions if each starts at a
multiple of its size, they lie below n, fill the numbers below n and do not meet. -/
theorem callsOK_tiles {e first : C → ℕ} (hle : ∀ c, e c ≤ s) (hdvd : ∀ c, 2 ^ e c ∣ first c)
    (hin : ∀ c, first c + 2 ^ e c ≤ n)
    (hcov : ∀ θ, θ < n → ∃ c, first c ≤ θ ∧ θ < first c + 2 ^ e c)
    (hdis : ∀ c c' θ, first c ≤ θ → θ < first c + 2 ^ e c → first c' ≤ θ →
      θ < first c' + 2 ^ e c' → c = c') :
    (lkOf P0 d s n).CallsOK fun c => ⟨e c, first c / 2 ^ e c⟩ := by
  have hm : ∀ c, first c / 2 ^ e c * 2 ^ e c = first c := fun c => Nat.div_mul_cancel (hdvd c)
  have hH : ∀ c θ, (LkCall.mk (e c) (first c / 2 ^ e c)).Has θ ↔
      first c ≤ θ ∧ θ < first c + 2 ^ e c := by
    intro c θ
    show θ / 2 ^ e c = first c / 2 ^ e c ↔ _
    rw [div_eq_iff_block (Nat.two_pow_pos _), hm c]
  refine ⟨hle, fun c => ?_, fun θ hθ => ?_, fun c c' θ h1 h2 => ?_⟩
  · show (first c / 2 ^ e c + 1) * 2 ^ e c ≤ n
    rw [Nat.add_mul, hm c, Nat.one_mul]
    exact hin c
  · obtain ⟨c, hc⟩ := hcov θ hθ
    exact ⟨c, (hH c θ).mpr hc⟩
  · obtain ⟨a1, a2⟩ := (hH c θ).mp h1
    obtain ⟨b1, b2⟩ := (hH c' θ).mp h2
    exact hdis c c' θ a1 a2 b1 b2

/-- The library's CallsOK.ext_leafK (Blocks/LookupCalls.lean), with its letters written out. -/
theorem leaf_calls {e p : C → ℕ} (h : (lkOf P0 d s n).CallsOK fun c => ⟨e c, p c⟩)
    (hnt : n ≤ 2 ^ s) {key : ℕ → ℕ → K} {kc : C → ℕ → K}
    (hk : (lkOf P0 d s n).KeysOf (fun c => ⟨e c, p c⟩) key kc) (al : K) (z : ℕ → K) :
    ext (d + s) ((lkOf P0 d s n).leafK key al) z =
      ∑ c, eqN (s - e c) d z (p c) *
        (al - ext (e c + d) (kc c)
          fun t => if t < e c then z (d + (s - e c) + t) else z (t - e c)) :=
  h.ext_leafK hnt hk al z

end Letters

/-! ## The library's eight calls -/

section Library

/-- The letters of the library's forest for the sizes D: the depth of a tree, the bits of a tree's
number and the number of trees. The letters on tables, padding and counts are those of P0. -/
@[reducible] def lkP (P0 : LkPar K) (D : Dim) : LkPar K := lkOf P0 (Dk D) (sg D) (NT D)

variable (P0 : LkPar K) (D : Dim)

/-- The prefix of a call times the number of its trees is its first tree. -/
theorem pre_mul (c : Fin 8) : pre D c * 2 ^ eC D c = firstTree D c :=
  Nat.div_mul_cancel ((treesTile D).2 c).1

omit [Field K] in
/-- (J1) The library's eight calls meet the library's conditions on blocks of trees, for all
sizes. -/
theorem callsOK_ff : (lkP P0 D).CallsOK (lkCall D) :=
  callsOK_tiles (P0 := P0) (d := Dk D) (s := sg D) (n := NT D) (e := eC D) (first := firstTree D)
    (eC_le_sg D) (fun c => ((treesTile D).2 c).1) (fun c => ((treesTile D).2 c).2)
    (fun _ hθ => ⟨_, callOf_spec D hθ⟩)
    (fun _ _ _ a1 a2 b1 b2 => (callOf_eq D a1 a2).symm.trans (callOf_eq D b1 b2))

/-- There are at most as many trees as numbers for trees. -/
theorem nt_le : NT D ≤ 2 ^ sg D := Nat.le_pow_clog (by norm_num) _

variable [scl : Scl] (t : Cell → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)

/-- (J2) The keys of the library's trees are those of its calls. -/
theorem keysOf_ff :
    (lkP P0 D).KeysOf (lkCall D) (forestKey D t tb L0 w) (keyVec D t tb L0 w) := by
  intro c τ hτ i _
  show forestKey D t tb L0 w (pre D c * 2 ^ eC D c + τ) i =
    keyVec D t tb L0 w c (τ * 2 ^ Dk D + i)
  have hc : Inst.Model.FFSeg.callOf D (firstTree D c + τ) = c :=
    callOf_eq D (Nat.le_add_right _ _) (Nat.add_lt_add_left hτ _)
  rw [pre_mul]
  unfold Inst.Model.FFSeg.forestKey
  rw [hc, Nat.add_sub_cancel_left]

/-- The keys of a tree, moved by the number of the tree's call times a shift. -/
def tagKey (sh : K) (θ i : ℕ) : K :=
  ((Inst.Model.FFSeg.callOf D θ).val : K) * sh + forestKey D t tb L0 w θ i

/-- The keys of a call, moved by the call's number times a shift. -/
def tagVec (sh : K) (c : Fin 8) (k : ℕ) : K := (c.val : K) * sh + keyVec D t tb L0 w c k

/-- The same for the moved keys. -/
theorem keysOf_tag (sh : K) :
    (lkP P0 D).KeysOf (lkCall D) (tagKey D t tb L0 w sh) (tagVec D t tb L0 w sh) := by
  intro c τ hτ i hi
  have hc : Inst.Model.FFSeg.callOf D (firstTree D c + τ) = c :=
    callOf_eq D (Nat.le_add_right _ _) (Nat.add_lt_add_left hτ _)
  have h := keysOf_ff P0 D t tb L0 w c τ hτ i hi
  show ((Inst.Model.FFSeg.callOf D (pre D c * 2 ^ eC D c + τ)).val : K) * sh +
      forestKey D t tb L0 w (pre D c * 2 ^ eC D c + τ) i =
    (c.val : K) * sh + keyVec D t tb L0 w c (τ * 2 ^ Dk D + i)
  rw [show forestKey D t tb L0 w (pre D c * 2 ^ eC D c + τ) i =
    keyVec D t tb L0 w c (τ * 2 ^ Dk D + i) from h, pre_mul, hc]

/-- (J3) The extension, at any point z, of the library's vector of leaves at the moved keys is the
sum over the eight calls of the call's weight times: al, less the call's number times the shift,
less the extension of the call's key vector at the call's point. -/
theorem leaf_ff (al sh : K) (z : ℕ → K) :
    ext (Dk D + sg D) ((lkP P0 D).leafK (tagKey D t tb L0 w sh) al) z =
      ∑ c : Fin 8, wc D z c *
        (al - (c.val : K) * sh - ext (aC D c) (keyVec D t tb L0 w c) (zc D z c)) := by
  have h := leaf_calls (P0 := P0) (d := Dk D) (s := sg D) (n := NT D) (e := eC D) (p := pre D)
    (callsOK_ff P0 D) (nt_le D) (keysOf_tag P0 D t tb L0 w sh) al z
  refine h.trans (sum_congr rfl fun c _ => ?_)
  have e1 : eC D c + Dk D = aC D c := Nat.sub_add_cancel (Dk_le D c)
  rw [e1]
  show wc D z c * (al - ext (aC D c)
    (fun k => (c.val : K) * sh + keyVec D t tb L0 w c k) (zc D z c)) = _
  rw [ext_const_add]
  ring

end Library

/-! ## What Forest.shape returns -/

section Port

/-- The letters of the library's forest for the verifier's numbers of a lookup. The letters on
tables, padding and counts are those of P0. -/
@[reducible] def foP (P0 : LkPar K) (fo : Model.Forest.Shape) : LkPar K :=
  lkOf P0 fo.dT fo.rK fo.NT

/-- Call number c of the verifier's lookup as a block of trees. -/
def foCall (fo : Model.Forest.Shape) (c : ℕ) : LkCall :=
  ⟨fo.iota.getD c 0, fo.first.getD c 0 / 2 ^ fo.iota.getD c 0⟩

/-- The order in which Forest.shape lays the calls is a strict total order. -/
theorem ord_falls (key : ℕ → ℕ) (n : ℕ) : Ord (range n) (fallsBefore key) where
  irrefl := fun p _ => fallsBefore_irrefl key p
  trans := fun p _ q _ r _ h1 h2 => by
    unfold fallsBefore at *
    omega
  tri := fun p _ q _ hne => by
    unfold fallsBefore
    omega

omit [Field K] in
/-- (J4) What Forest.shape returns meets the library's conditions on blocks of trees, for any
calls. -/
theorem callsOK_shape (P0 : LkPar K) {calls : Array Call} {lid : ℕ} {fo : Model.Forest.Shape}
    (h : Model.Forest.shape calls lid = .ok fo) :
    (foP P0 fo).CallsOK fun c : Fin calls.size => foCall fo c.val := by
  obtain ⟨-, hN, hr, hf⟩ := shape_numbers h
  have O := ord_falls (fun c => fo.iota.getD c 0) calls.size
  have hb : ∀ c, c < calls.size → fo.first.getD c 0 =
      base (range calls.size) (fun c => 2 ^ fo.iota.getD c 0)
        (fallsBefore fun c => fo.iota.getD c 0) c := fun c hc =>
    (hf c hc).trans (sum_congr rfl fun c' _ => if_congr Iff.rfl rfl rfl)
  have hd : ∀ c, c < calls.size → 2 ^ fo.iota.getD c 0 ∣ fo.first.getD c 0 := by
    intro c hc
    rw [hf c hc]
    refine Finset.dvd_sum fun c' _ => ?_
    split_ifs with hq
    · exact pow_dvd_pow 2 (by omega)
    · exact Nat.dvd_zero _
  have hm : ∀ c, c < calls.size →
      fo.first.getD c 0 / 2 ^ fo.iota.getD c 0 * 2 ^ fo.iota.getD c 0 = fo.first.getD c 0 :=
    fun c hc => Nat.div_mul_cancel (hd c hc)
  have ht : ∀ c, c < calls.size → fo.first.getD c 0 + 2 ^ fo.iota.getD c 0 ≤ fo.NT := by
    intro c hc
    rw [hb c hc, hN]
    exact base_add_le_total (w := fun c => 2 ^ fo.iota.getD c 0) O (mem_range.mpr hc)
  have hH : ∀ c, c < calls.size → ∀ θ, (foCall fo c).Has θ ↔
      fo.first.getD c 0 ≤ θ ∧ θ < fo.first.getD c 0 + 2 ^ fo.iota.getD c 0 := by
    intro c hc θ
    show θ / 2 ^ fo.iota.getD c 0 = fo.first.getD c 0 / 2 ^ fo.iota.getD c 0 ↔ _
    rw [div_eq_iff_block (Nat.two_pow_pos _), hm c hc]
  refine ⟨fun c => ?_, fun c => ?_, fun θ hθ => ?_, fun c c' θ h1 h2 => ?_⟩
  · show fo.iota.getD c.val 0 ≤ fo.rK
    have h1 : 2 ^ fo.iota.getD c.val 0 ≤ fo.NT :=
      Nat.le_trans (Nat.le_add_left _ _) (ht c.val c.isLt)
    have h2 : fo.NT ≤ 2 ^ fo.rK := by
      rw [hr]
      exact le_two_pow_ceilLog2 fo.NT
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_trans h1 h2)
  · show (fo.first.getD c.val 0 / 2 ^ fo.iota.getD c.val 0 + 1) * 2 ^ fo.iota.getD c.val 0 ≤ fo.NT
    rw [Nat.add_mul, hm c.val c.isLt, Nat.one_mul]
    exact ht c.val c.isLt
  · have hθ' : θ < ∑ q ∈ range calls.size, 2 ^ fo.iota.getD q 0 := by
      rw [← hN]
      exact hθ
    obtain ⟨p, hp, a1, a2⟩ := tile_cover (w := fun c => 2 ^ fo.iota.getD c 0) O hθ'
    have hp' := mem_range.mp hp
    refine ⟨⟨p, hp'⟩, (hH p hp' θ).mpr ?_⟩
    rw [hb p hp']
    exact ⟨a1, a2⟩
  · obtain ⟨a1, a2⟩ := (hH c.val c.isLt θ).mp h1
    obtain ⟨b1, b2⟩ := (hH c'.val c'.isLt θ).mp h2
    rw [hb c.val c.isLt] at a1 a2
    rw [hb c'.val c'.isLt] at b1 b2
    exact Fin.ext (tile_inj (w := fun c => 2 ^ fo.iota.getD c 0) O (mem_range.mpr c.isLt)
      (mem_range.mpr c'.isLt) a1 a2 b1 b2)

variable (P0 : LkPar K) {ρ : Reading K} {fo : Model.Forest.Shape} {zx zy : Array E}

/-- (K1) The weight of a call, as the lookup computes it, reads as the library's weight of the block
at the point zOf. -/
theorem wCall_of_look (hsx : zx.size = fo.dT) (c : ℕ) :
    ρ.val (Model.Forest.callWeight fo zy c) = (foP P0 fo).wCall (foCall fo c) (zOf ρ zx zy) := by
  show ρ.val ((List.range (fo.rK - fo.iota.getD c 0)).foldl
    (fun e i => mulE e
      (if (fo.first.getD c 0 / 2 ^ fo.iota.getD c 0 /
          2 ^ (fo.rK - fo.iota.getD c 0 - 1 - i)) % 2 = 1
        then zy.getD i zeroE else subE oneE (zy.getD i zeroE))) oneE) =
    eqN (fo.rK - fo.iota.getD c 0) fo.dT (zOf ρ zx zy)
      (fo.first.getD c 0 / 2 ^ fo.iota.getD c 0)
  rw [foldl_mul_value]
  unfold Blocks.eqN
  refine prod_congr rfl fun t _ => ?_
  have hz : zOf ρ zx zy (fo.dT + t) = ρ.val (zy.getD t zeroE) := by
    unfold zOf
    rw [hsx, if_neg (by omega), Nat.add_sub_cancel_left]
  rw [hz]
  by_cases hb : (fo.first.getD c 0 / 2 ^ fo.iota.getD c 0).testBit
      (fo.rK - fo.iota.getD c 0 - 1 - t) = true
  · rw [if_pos hb, if_pos ((Inst.Model.FFSeg.IndexFacts.testBit_iff _ _).mp hb)]
  · rw [if_neg hb, if_neg (fun h => hb ((Inst.Model.FFSeg.IndexFacts.testBit_iff _ _).mpr h)),
      ρ.sub, ρ.one]

/-- (K2) The point of a call, as the lookup makes it, reads as the library's point of the block at
the point zOf, on all its coordinates. -/
theorem zCall_of_look (hsx : zx.size = fo.dT) (hsy : zy.size = fo.rK) {zk : Array (Array E)}
    (hzk : zk = (Array.range fo.NC).map fun c =>
      zy.extract (fo.rK - fo.iota.getD c 0) zy.size ++ zx) {c : ℕ} (hc : c < fo.NC)
    (hio : fo.iota.getD c 0 ≤ fo.rK) :
    ∀ j, j < fo.iota.getD c 0 + fo.dT →
      pt ρ (zk.getD c #[]) j = (foP P0 fo).zCall (foCall fo c) (zOf ρ zx zy) j := by
  intro j hj
  have hk : zk.getD c #[] = zy.extract (fo.rK - fo.iota.getD c 0) zy.size ++ zx := by
    rw [hzk, range_map_getD' _ _ _ hc]
  show pt ρ (zk.getD c #[]) j =
    if j < fo.iota.getD c 0 then zOf ρ zx zy (fo.dT + (fo.rK - fo.iota.getD c 0) + j)
    else zOf ρ zx zy (j - fo.iota.getD c 0)
  unfold pt zOf
  rw [hk, getD_append', Array.size_extract, hsx]
  generalize fo.iota.getD c 0 = i at *
  generalize fo.dT = k at *
  generalize fo.rK = σ at *
  have hs : min zy.size zy.size - (σ - i) = i := by omega
  rw [hs]
  by_cases hlt : j < i
  · have e : k + (σ - i) + j - k = σ - i + j := by omega
    rw [if_pos hlt, if_pos hlt, if_neg (by omega), getD_stretch zy (Nat.le_refl _) (by omega), e]
  · rw [if_neg hlt, if_neg hlt, if_pos (by omega)]

/-- (K3) The verifier's table of equality weights of its point over the trees' numbers reads as the
library's equality weights of the coordinates of zOf from dT on. -/
theorem ey_of_look (hsx : zx.size = fo.dT) (hsy : zy.size = fo.rK) {θ : ℕ}
    (hθ : θ < 2 ^ fo.rK) :
    ρ.val ((eqTab zy).getD θ zeroE) = eqN fo.rK fo.dT (zOf ρ zx zy) θ := by
  rw [eqTab_value ρ zy θ (by rw [hsy]; exact hθ), hsy, ← eqN_shift' fo.rK fo.dT (zOf ρ zx zy) θ]
  refine eqN_congr' fo.rK 0 (fun j _ => ?_) θ
  show pt ρ zy (0 + j) = zOf ρ zx zy (fo.dT + (0 + j))
  unfold pt zOf
  rw [hsx, if_neg (by omega), Nat.zero_add, Nat.add_sub_cancel_left]

/-- The sum over the calls in the lookup's join, for any calls. For keys of trees that are the keys
kc of the calls, the extension of the library's vector of leaves at the point zOf is the sum over
the calls of the verifier's weight of the call times: al less the extension of the call's keys at
the verifier's point of the call. The verifier's join has more: a term for the trees that belong to
no call, where the library's leaf is 0 (ext_leafAll), and each call's keys moved by the call's
number times a shift, which is a matter of kc here. -/
theorem leaf_shape {calls : Array Call} {lid : ℕ} (h : Model.Forest.shape calls lid = .ok fo)
    (hsx : zx.size = fo.dT) (hsy : zy.size = fo.rK)
    {zk : Array (Array E)} (hzk : zk = (Array.range fo.NC).map fun c =>
      zy.extract (fo.rK - fo.iota.getD c 0) zy.size ++ zx)
    {key : ℕ → ℕ → K} {kc : Fin calls.size → ℕ → K}
    (hk : (foP P0 fo).KeysOf (fun c : Fin calls.size => foCall fo c.val) key kc) (al : K) :
    ext (fo.dT + fo.rK) ((foP P0 fo).leafK key al) (zOf ρ zx zy) =
      ∑ c : Fin calls.size, ρ.val (Model.Forest.callWeight fo zy c.val) *
        (al - ext (fo.iota.getD c.val 0 + fo.dT) (kc c) (pt ρ (zk.getD c.val #[]))) := by
  have H := callsOK_shape P0 h
  have hnt : fo.NT ≤ 2 ^ fo.rK := by
    rw [(shape_numbers h).2.2.1]
    exact le_two_pow_ceilLog2 fo.NT
  refine (H.ext_leafK hnt hk al (zOf ρ zx zy)).trans (sum_congr rfl fun c _ => ?_)
  have e : ext (fo.iota.getD c.val 0 + fo.dT) (kc c)
      ((foP P0 fo).zCall (foCall fo c.val) (zOf ρ zx zy)) =
      ext (fo.iota.getD c.val 0 + fo.dT) (kc c) (pt ρ (zk.getD c.val #[])) :=
    ext_same_pt _ _ fun j hj =>
      (zCall_of_look P0 hsx hsy hzk (by rw [(shape_calls h).2]; exact c.isLt) (H.le c) j hj).symm
  show (foP P0 fo).wCall (foCall fo c.val) (zOf ρ zx zy) *
    (al - ext (fo.iota.getD c.val 0 + fo.dT) (kc c)
      ((foP P0 fo).zCall (foCall fo c.val) (zOf ρ zx zy))) = _
  rw [e, wCall_of_look P0 hsx c.val]

end Port

#print axioms ext_leafAll
#print axioms callsOK_tiles
#print axioms leaf_calls
#print axioms callsOK_ff
#print axioms nt_le
#print axioms keysOf_ff
#print axioms keysOf_tag
#print axioms leaf_ff
#print axioms callsOK_shape
#print axioms wCall_of_look
#print axioms zCall_of_look
#print axioms ey_of_look
#print axioms leaf_shape

end OnBytes.Road
