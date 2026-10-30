-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyPlanesRead.lean: the keys and the planes of E2E/KeyPlanes.lean, held against the library's
own two functions at a key file's lookups (Johnson/Desc/Key/KeyK3W.lean): `keyVec`, key number i of
a part, and `bitVec`, the reader of the multiplicities' bits off the main table of their oracle
message. Definitions, statements and proofs.

These two are typed on the programs' machine elements; E2E/KeyPlanes.lean on elements of the field.
The reading from the one to the other is the library's `readE` (OnBytes/Slice/ProgField.lean).

What is defined.
  `planesVal entry k lookups ell rb i`: entry number i of the main table of the oracle message of
    the multiplicities, as a machine element: main row i % 2^rb, place i / 2^rb, by `planesData`; 0
    where no block of planes lies.
  `Good lookups rb logEll Bs`: a test on a list of blocks: each within a row and aligned, with as
    many entries as its planes and its lookup's table ask; no two overlap.
What is shown.
  **`keyVec_read`**: key number c + 2^kCol · u of part f, read in the field, is `keyOfPlace` at the
    place u and the column c, at the reader of the same matrix.
  `blockPlace_eq`: for a block that passes the test, entry e of it has the library's index
    row + (first place + e) · 2^rb.
  `planes_at_block`: at that index `planesVal` is the bit of which the block's entry speaks.
  **`bitVec_read`**: where the library's layout is a list that passes the test: `bitVec` at
    `planesVal`, at the index j + 2^mu · u with j below 2^mu and u below 2^d, read in the field, is
    bit j of the multiplicity of u, as often as a block of the lookup holds plane j.
  **`bitVec_full`**: at the two lookups of the full size, two main rows of 2^18 places: it is bit j
    of the multiplicity of u for j below 40 (39), and 0 for the other j below 64.

  **`mid_parts`**: the relation after the first challenge at several parts, with the library's keys
    and the bits of E2E/KeyPlanes.lean: the product over the parts of (the product of alpha -
    `keyVec` over all keys of the part) is (alpha - padding key)^(padding positions) times the
    product over the planes j below W of (the product over t of 1 + bit · (alpha - 1 - t))^(2^j):
    under the four premises of `planes_valid` (E2E/KeyPlanes.lean), at every alpha of the extension
    field.

Limits. `bitVec_full` takes as premises that the item's lookups are the two written ones, that the
message has two main rows and that its code has messages of 2^18 entries: that these hold at any
public files is not shown here. Machine elements are compared after reading: two machine elements
with one reading need not be the same words.
Nothing on hiding follows from this file.


-/
import E2E.KeyPlanesAtFull
import Johnson.Desc.Key.KeyK3W
import OnBytes.Slice.ProgField

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.Key
open Finset
open OnBytes.Slice (GF GE toF readE)
open OnBytes.Params (WfRun WfPart WfLookup WfPublic)
open Johnson.Pack (runIn rowOf hasPl lk0Full lk1Full)
open VerifiableInference.Desc.Key (keyVec bitVec blockPlace)
open Inst.Model.Layout (kRef)

/-! ## 1. The keys -/

/-- A fold over a numbered list, read in the field. -/
theorem foldl_zipIdx_read (h : OnBytes.F → ℕ → OnBytes.E) :
    ∀ (L : List OnBytes.F) (n : ℕ) (z : OnBytes.E),
      readE ((L.zipIdx n).foldl (fun s q => OnBytes.addE s (h q.1 q.2)) z) =
        readE z + ∑ q ∈ range L.length, readE (h (L.getD q 0) (n + q))
  | [], n, z => by simp
  | a :: L, n, z => by
    rw [List.zipIdx_cons, List.foldl_cons, foldl_zipIdx_read h L (n + 1),
      OnBytes.Slice.readE_add, List.length_cons, Finset.sum_range_succ', add_assoc]
    refine congrArg (fun y => readE z + y) ?_
    rw [add_comm]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun q _ => ?_) rfl
    rw [List.getD_cons_succ, show n + 1 + q = n + (q + 1) by omega]

/-- The library's key at a place of a run, read in the field. -/
theorem keyAt_read (l : WfLookup) (mat : ℕ → ℕ → OnBytes.F) (r : WfRun) (t c : ℕ) :
    readE (VerifiableInference.Desc.Key.keyAt l mat r t c) =
      algebraMap GF GE (toF l.offset + ∑ q ∈ range l.digitWeight.length,
        toF (l.digitWeight.getD q 0) * toF (mat (r.firstRow + t + q * r.stride) c)) := by
  unfold VerifiableInference.Desc.Key.keyAt
  rw [foldl_zipIdx_read (fun w q => OnBytes.mulE (OnBytes.ofF w)
      (OnBytes.ofF (mat (r.firstRow + t + q * r.stride) c))) l.digitWeight 0 (OnBytes.ofF l.offset),
    OnBytes.Slice.readE_ofF, map_add, map_sum]
  refine congrArg (fun y => algebraMap GF GE (toF l.offset) + y)
    (Finset.sum_congr rfl fun q _ => ?_)
  rw [OnBytes.Slice.readE_mul, OnBytes.Slice.readE_ofF, OnBytes.Slice.readE_ofF, map_mul,
    Nat.zero_add]

/-- **The library's key number c + 2^kCol · u of part f is the key of E2E/KeyPlanes.lean.** -/
theorem keyVec_read (m : OnBytes.Wf.Matrix) (l : WfLookup) (mat : ℕ → ℕ → OnBytes.F)
    (f : Fin l.parts.length) (u c : ℕ) (hc : c < 2 ^ m.kCol) :
    readE (keyVec m l mat f.val (c + 2 ^ m.kCol * u)) =
      algebraMap GF GE (keyOfPlace (fun y x => toF (mat y x)) l (l.parts.get f) u c) := by
  have hp : 0 < 2 ^ m.kCol := Nat.two_pow_pos _
  have e1 : (c + 2 ^ m.kCol * u) % 2 ^ m.kCol = c := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  have e2 : (c + 2 ^ m.kCol * u) / 2 ^ m.kCol = u := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hc, Nat.zero_add]
  have e3 : ((l.parts[f.val]?).map (·.runs)).getD [] = (l.parts.get f).runs := by
    rw [List.getElem?_eq_getElem f.isLt]
    rfl
  have e4 : (fun r : WfRun => decide (r.firstPlace ≤ u) && decide (u < r.firstPlace + r.places)) =
      fun r : WfRun => decide (hasPl r u) := by
    funext r
    unfold hasPl
    rw [Bool.decide_and]
  unfold keyVec keyOfPlace
  simp only [e1, e2, e3, e4]
  show readE (match runIn (l.parts.get f).runs u with
    | some r => VerifiableInference.Desc.Key.keyAt l mat r (u - r.firstPlace) c
    | none => OnBytes.ofF l.paddingKey) = _
  cases runIn (l.parts.get f).runs u with
  | none => exact OnBytes.Slice.readE_ofF _
  | some r => exact keyAt_read l mat r (u - r.firstPlace) c

/-! ## 2. The planes: a test on a list of blocks -/

section
variable (entry : ℕ → ℕ → GF) (k : ℕ) (lookups : List WfLookup) (ell rb logEll : ℕ)

/-- **Entry number i of the main table of the oracle message of the multiplicities**, as a machine
element. -/
def planesVal (i : ℕ) : OnBytes.E :=
  OnBytes.ofF
    (OnBytes.Slice.ofF ((planesData entry k lookups ell (i % 2 ^ rb) (i / 2 ^ rb)).getD 0))

theorem planesVal_read (i : ℕ) : readE (planesVal entry k lookups ell rb i) =
    algebraMap GF GE ((planesData entry k lookups ell (i % 2 ^ rb) (i / 2 ^ rb)).getD 0) := by
  unfold planesVal
  rw [OnBytes.Slice.readE_ofF, OnBytes.Slice.toF_ofF]

/-- A block lies within a row, is aligned, and has as many entries as its planes and its lookup's
table ask. -/
def fitB (b : OnBytes.Wf.Block) : Bool :=
  decide (b.row < 2 ^ rb) && decide (b.bits ≤ logEll) && decide (b.firstPlace % 2 ^ b.bits = 0) &&
    decide (b.firstPlace + 2 ^ b.bits ≤ 2 ^ logEll) &&
    decide (b.bits = b.logPlanes + (lookups.getD b.lookup default).d)

/-- Two blocks do not overlap. -/
def apart (a b : OnBytes.Wf.Block) : Bool :=
  a.row != b.row || decide (a.firstPlace + 2 ^ a.bits ≤ b.firstPlace) ||
    decide (b.firstPlace + 2 ^ b.bits ≤ a.firstPlace)

/-- The test on a list of blocks. -/
def Good (Bs : List OnBytes.Wf.Block) : Bool :=
  Bs.all (fitB lookups rb logEll) && Bs.all fun a => Bs.all fun b => a == b || apart a b

end

/-- The library's index of entry e of a block that passes the test. -/
theorem blockPlace_eq (lookups : List WfLookup) (rb logEll : ℕ) (b : OnBytes.Wf.Block)
    (h : fitB lookups rb logEll b = true) (e : ℕ) (he : e < 2 ^ b.bits) :
    blockPlace rb logEll b e = b.row + (b.firstPlace + e) * 2 ^ rb := by
  unfold fitB at h
  simp only [decide_eq_true_eq, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩ := h
  have hp : 0 < 2 ^ b.bits := Nat.two_pow_pos _
  have hs : 2 ^ logEll = 2 ^ b.bits * 2 ^ (logEll - b.bits) := by
    rw [← pow_add, Nat.add_sub_cancel' h2]
  have hq : b.firstPlace / 2 ^ b.bits < 2 ^ (logEll - b.bits) :=
    Nat.div_lt_of_lt_mul (by rw [← hs]; omega)
  unfold blockPlace
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt he, Nat.div_eq_of_lt he, Nat.mod_eq_of_lt hq,
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h3), Nat.zero_mul, Nat.add_zero,
    Nat.add_comm e b.firstPlace]

/-- In a list, the one member that passes a test is the member that is found. -/
theorem find_unique {α : Type} (P : α → Bool) (Bs : List α) (b : α) (hb : b ∈ Bs)
    (hP : P b = true) (hu : ∀ a ∈ Bs, P a = true → a = b) : Bs.find? P = some b := by
  cases h : Bs.find? P with
  | none => exact absurd hP (List.find?_eq_none.1 h b hb)
  | some a => rw [hu a (List.mem_of_find?_eq_some h) (List.find?_some h)]

section
variable (entry : ℕ → ℕ → GF) (k : ℕ) (lookups : List WfLookup) (ell rb logEll : ℕ)
  (Bs : List OnBytes.Wf.Block) (hlay : OnBytes.Wf.layout lookups ell = Bs)
  (hg : Good lookups rb logEll Bs = true)
include hlay hg

/-- **What stands at entry e of a block.** -/
theorem planes_at_block (b : OnBytes.Wf.Block) (hb : b ∈ Bs) (e : ℕ) (he : e < 2 ^ b.bits) :
    readE (planesVal entry k lookups ell rb (blockPlace rb logEll b e)) =
      algebraMap GF GE (bitOf entry k (lookups.getD b.lookup default) (e / 2 ^ b.logPlanes)
        (b.first + e % 2 ^ b.logPlanes)) := by
  unfold Good at hg
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at hg
  have hf := hg.1 b hb
  have hr : b.row < 2 ^ rb := by
    unfold fitB at hf
    simp only [decide_eq_true_eq, Bool.and_eq_true] at hf
    exact hf.1.1.1.1
  have hp : 0 < 2 ^ rb := Nat.two_pow_pos _
  rw [planesVal_read, blockPlace_eq lookups rb logEll b hf e he, Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt hr, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hr, Nat.zero_add]
  unfold planesData
  rw [hlay, find_unique _ Bs b hb (by simp; omega) (fun a ha hPa => ?_)]
  · rw [Option.map_some, Option.getD_some, Nat.add_sub_cancel_left]
  · have hab := List.all_eq_true.1 (hg.2 a ha) b hb
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hPa
    rcases Bool.or_eq_true _ _ ▸ hab with h | h
    · exact beq_iff_eq.1 h
    · unfold apart at h
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
      omega

end

/-! ## 3. The library's reader of the bits -/

/-- A fold that adds where a test holds, read in the field. -/
theorem foldl_if_read {α : Type} (P : α → Prop) [DecidablePred P] (v : α → OnBytes.E) :
    ∀ (Bs : List α) (z : OnBytes.E),
      readE (Bs.foldl (fun s b => if P b then OnBytes.addE s (v b) else s) z) =
        readE z + (Bs.map fun b => if P b then readE (v b) else 0).sum
  | [], z => by simp
  | b :: Bs, z => by
    rw [List.foldl_cons, foldl_if_read P v Bs, List.map_cons, List.sum_cons, ← add_assoc]
    refine congrArg (fun y => y + _) ?_
    by_cases h : P b
    · rw [if_pos h, if_pos h, OnBytes.Slice.readE_add]
    · rw [if_neg h, if_neg h, add_zero]

/-- A sum of one value where a test holds. -/
theorem sum_if_const {α : Type} (P : α → Prop) [DecidablePred P] (c : GE) :
    ∀ Bs : List α, (Bs.map fun b => if P b then c else 0).sum =
      ((Bs.filter fun b => decide (P b)).length : GE) * c
  | [] => by simp
  | b :: Bs => by
    rw [List.map_cons, List.sum_cons, sum_if_const P c Bs]
    by_cases h : P b
    · rw [if_pos h, List.filter_cons_of_pos (by simpa using h), List.length_cons, Nat.cast_succ]
      ring
    · rw [if_neg h, List.filter_cons_of_neg (by simpa using h), zero_add]

/-- **The library's reader at the honest planes**: bit j of the multiplicity of u, as often as a
block of the lookup holds plane j. -/
theorem bitVec_read (entry : ℕ → ℕ → GF) (k : ℕ) (x : WfPublic) (codes : OnBytes.Codes) (l : ℕ)
    (Bs : List OnBytes.Wf.Block)
    (hlay : OnBytes.Wf.layout x.lookups (codes.base.getD x.message.shape.code default).ell = Bs)
    (hg : Good x.lookups (OnBytes.ceilLog2 x.message.shape.mainRows)
      (codes.base.getD x.message.shape.code default).logEll Bs = true)
    (j u : ℕ) (hj : j < 2 ^ (x.lookups.getD l default).mu)
    (hu : u < 2 ^ (x.lookups.getD l default).d) :
    readE (bitVec x codes l (planesVal entry k x.lookups
        (codes.base.getD x.message.shape.code default).ell
        (OnBytes.ceilLog2 x.message.shape.mainRows))
        (j + 2 ^ (x.lookups.getD l default).mu * u)) =
      (((Bs.filter (·.lookup == l)).filter fun b =>
        decide (b.first ≤ j ∧ j < b.first + 2 ^ b.logPlanes)).length : GE) *
        algebraMap GF GE (bitOf entry k (x.lookups.getD l default) u j) := by
  have hp : 0 < 2 ^ (x.lookups.getD l default).mu := Nat.two_pow_pos _
  have e1 :
      (j + 2 ^ (x.lookups.getD l default).mu * u) % 2 ^ (x.lookups.getD l default).mu = j := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  have e2 :
      (j + 2 ^ (x.lookups.getD l default).mu * u) / 2 ^ (x.lookups.getD l default).mu = u := by
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hj, Nat.zero_add]
  unfold bitVec
  simp only [e1, e2, hlay]
  rw [foldl_if_read (fun b : OnBytes.Wf.Block => b.first ≤ j ∧ j < b.first + 2 ^ b.logPlanes),
    OnBytes.Slice.readE_zero, zero_add, ← sum_if_const]
  refine congrArg List.sum (List.map_congr_left fun b hb => ?_)
  by_cases hP : b.first ≤ j ∧ j < b.first + 2 ^ b.logPlanes
  · rw [if_pos hP, if_pos hP]
    obtain ⟨hbB, hbl⟩ := List.mem_filter.1 hb
    have hl : b.lookup = l := beq_iff_eq.1 hbl
    have hq : 0 < 2 ^ b.logPlanes := Nat.two_pow_pos _
    have hd : j - b.first < 2 ^ b.logPlanes := by omega
    have hbits : b.bits = b.logPlanes + (x.lookups.getD l default).d := by
      have hf := hg
      unfold Good at hf
      rw [Bool.and_eq_true, List.all_eq_true] at hf
      have h1 := hf.1 b hbB
      unfold fitB at h1
      simp only [decide_eq_true_eq, Bool.and_eq_true] at h1
      rw [← hl]
      exact h1.2
    have he : j - b.first + 2 ^ b.logPlanes * u < 2 ^ b.bits := by
      rw [hbits, pow_add]
      calc j - b.first + 2 ^ b.logPlanes * u < 2 ^ b.logPlanes + 2 ^ b.logPlanes * u :=
            Nat.add_lt_add_right hd _
        _ = 2 ^ b.logPlanes * (u + 1) := by ring
        _ ≤ 2 ^ b.logPlanes * 2 ^ (x.lookups.getD l default).d := Nat.mul_le_mul_left _ hu
    rw [planes_at_block entry k x.lookups _ _ _ Bs hlay hg b hbB _ he, hl,
      Nat.add_mul_div_left _ _ hq, Nat.div_eq_of_lt hd, Nat.zero_add, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hd, Nat.add_sub_cancel' hP.1]
  · rw [if_neg hP, if_neg hP]

/-! ## 4. At the full size -/

set_option maxRecDepth 1000000 in
theorem good_full : Good [lk0Full, lk1Full] 1 18 sixBlocks = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Each real plane lies in just one block of its lookup, the other plane slots in none. -/
theorem holders_full : ∀ j < 64,
    ((sixBlocks.filter (·.lookup == 0)).filter fun b =>
        decide (b.first ≤ j ∧ j < b.first + 2 ^ b.logPlanes)).length = (if j < 40 then 1 else 0) ∧
      ((sixBlocks.filter (·.lookup == 1)).filter fun b =>
        decide (b.first ≤ j ∧ j < b.first + 2 ^ b.logPlanes)).length =
          (if j < 39 then 1 else 0) := by
  decide +kernel

/-- **At the two lookups of the full size.** -/
theorem bitVec_full (entry : ℕ → ℕ → GF) (x : WfPublic) (codes : OnBytes.Codes)
    (hx : x.lookups = [lk0Full, lk1Full]) (hrows : x.message.shape.mainRows = 2)
    (hell : (codes.base.getD x.message.shape.code default).ell = 2 ^ 18) (j : ℕ) (hj : j < 64) :
    (∀ u < 2 ^ 8, readE (bitVec x codes 0 (planesVal entry kRef [lk0Full, lk1Full] (2 ^ 18) 1)
        (j + 2 ^ 6 * u)) =
      if j < 40 then algebraMap GF GE (bitOf entry kRef lk0Full u j) else 0) ∧
    ∀ u < 2 ^ 13, readE (bitVec x codes 1 (planesVal entry kRef [lk0Full, lk1Full] (2 ^ 18) 1)
        (j + 2 ^ 6 * u)) =
      if j < 39 then algebraMap GF GE (bitOf entry kRef lk1Full u j) else 0 := by
  have hrb : OnBytes.ceilLog2 x.message.shape.mainRows = 1 := by rw [hrows]; decide
  have hle : (codes.base.getD x.message.shape.code default).logEll = 18 := by
    unfold OnBytes.Code.logEll
    rw [hell]
    decide
  have hlay : OnBytes.Wf.layout x.lookups (codes.base.getD x.message.shape.code default).ell =
      sixBlocks := by rw [hx, hell]; exact layout_full
  have hg : Good x.lookups (OnBytes.ceilLog2 x.message.shape.mainRows)
      (codes.base.getD x.message.shape.code default).logEll sixBlocks = true := by
    rw [hx, hrb, hle]; exact good_full
  constructor
  · intro u hu
    have h := bitVec_read entry kRef x codes 0 sixBlocks hlay hg j u (by rw [hx]; exact hj)
      (by rw [hx]; exact hu)
    rw [hx, hell, hrb, (holders_full j hj).1] at h
    rw [show (2 : ℕ) ^ 6 = 2 ^ ([lk0Full, lk1Full].getD 0 default).mu from rfl, h]
    by_cases h40 : j < 40
    · rw [if_pos h40, if_pos h40, Nat.cast_one, one_mul]
      rfl
    · rw [if_neg h40, if_neg h40, Nat.cast_zero, zero_mul]
  · intro u hu
    have h := bitVec_read entry kRef x codes 1 sixBlocks hlay hg j u (by rw [hx]; exact hj)
      (by rw [hx]; exact hu)
    rw [hx, hell, hrb, (holders_full j hj).2] at h
    rw [show (2 : ℕ) ^ 6 = 2 ^ ([lk0Full, lk1Full].getD 1 default).mu from rfl, h]
    by_cases h39 : j < 39
    · rw [if_pos h39, if_pos h39, Nat.cast_one, one_mul]
      rfl
    · rw [if_neg h39, if_neg h39, Nat.cast_zero, zero_mul]

/-! ## 5. The relation after the first challenge, at several parts, with the library's keys -/

/-- A product over places and columns is a product over the keys' numbers. -/
theorem prod_part (m n : ℕ) (H : ℕ → GE) :
    ∏ x : Fin m × Fin n, H (x.2.val + n * x.1.val) = ∏ i ∈ range (m * n), H i := by
  rw [← Fin.prod_univ_eq_prod_range]
  exact Fintype.prod_equiv finProdFinEquiv _ _ fun _ => rfl

/-- **The product of the parts' roots is the padding's factor times the planes' products, each to
its power of two**: at every alpha, for the library's `keyVec` and the honest bits. A part's root:
the product of alpha - key over all its keys, padding counted. -/
theorem mid_parts (m : OnBytes.Wf.Matrix) (l : WfLookup) (mat : ℕ → ℕ → OnBytes.F) {W : ℕ}
    (hin : KeysIn (fun y x => toF (mat y x)) m.kCol l)
    (hpad : ∃ t₀ : ℕ, t₀ < 2 ^ l.d ∧ toF l.paddingKey = (t₀ : GF))
    (hinj : ∀ t t' : ℕ, t < 2 ^ l.d → t' < 2 ^ l.d → (t : GF) = (t' : GF) → t = t')
    (hW : Fintype.card (Pos l m.kCol) < 2 ^ W) (al : GE) :
    ∏ f : Fin l.parts.length, ∏ i ∈ range (2 ^ (l.parts.get f).logPlaces * 2 ^ m.kCol),
        (al - readE (keyVec m l mat f.val i)) =
      (al - readE (OnBytes.ofF l.paddingKey)) ^ paddingCount m.kCol l *
        ∏ j ∈ range W, (∏ t : Fin (2 ^ l.d),
          (1 + algebraMap GF GE (bitOf (fun y x => toF (mat y x)) m.kCol l t.val j) *
            (al - 1 - algebraMap GF GE (t.val : GF)))) ^ 2 ^ j := by
  rw [OnBytes.Slice.readE_ofF,
    ← planes_valid (fun y x => toF (mat y x)) m.kCol l (algebraMap GF GE) hin hpad hinj hW al,
    Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun f _ => ?_
  rw [← prod_part]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [keyVec_read m l mat f x.1.val x.2.val x.2.isLt]
  rfl

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.foldl_zipIdx_read
#print axioms AtPublicFiles.Key.keyAt_read
#print axioms AtPublicFiles.Key.keyVec_read
#print axioms AtPublicFiles.Key.blockPlace_eq
#print axioms AtPublicFiles.Key.find_unique
#print axioms AtPublicFiles.Key.planes_at_block
#print axioms AtPublicFiles.Key.bitVec_read
#print axioms AtPublicFiles.Key.good_full
#print axioms AtPublicFiles.Key.holders_full
#print axioms AtPublicFiles.Key.bitVec_full
#print axioms AtPublicFiles.Key.prod_part
#print axioms AtPublicFiles.Key.mid_parts
