-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/KeysBridge.lean: FROM «THE EXTENSION OF ALL 2^v KEYS OF A PART AT A POINT» (the
lay's end claim: the library's MCl.Holds, Cb/Ld/LdLkpTree.lean:143-144) TO
«WEIGHTS 0 AT PADDING; THE PADDING's SHARE AND THE OFFSET's SHARE OUT OF THE TARGET» (the form of
the port's claim on a part's keys and
of its caller's pending row). Identities on multilinear extensions with a public padding value. No
protocol. It imports the library
and Letters.lean alone (nothing of the port).

LETTERS. v: a part has 2^v keys, key b. pt: a point in THE LIBRARY's LISTING (coordinate 0 belongs
to the TOP bit of a key's number:
Blocks.eqN). pad b: key number b is padding (a Bool, public). c: the public value that a place of
padding holds. off: a public
offset. lin b: what is left of a real key: key b = off + lin b.
  wCov v pt pad b    the weight of key b: the equality vector at pt, and 0 AT PADDING
  padW, covW         the equality vector's sum over the padding, over the real keys
  keyRow             the claim as a ROW on the entries (the library's Row), where a real key is off
                     + a linear form co b in the entries
  eqLow z j, lowPt v pt   the equality vector by a LIST that has bit t's coordinate at place t (the
  port's listing), and the
                     library's point so listed
THEOREMS.
  covW_add_padW      covW + padW = 1
  ext_split          padding holds c ⇒ ext v key pt = Σ_b wCov b * key b + c * padW
  holds_pad_iff      ... ⇒ (cl.Holds v key μ ⇔ Σ_b wCov b * key b + ⟨mf, μ⟩ = tg - c * padW)
  holds_off_iff      and key b = off + lin b at real keys ⇒ (cl.Holds v key μ ⇔ Σ_b wCov b * lin b +
                     ⟨mf, μ⟩ = tg - c * padW - off * covW)
  holds_row_iff      and lin b = ⟨co b, μ⟩ ⇒ (cl.Holds v key μ ⇔ (keyRow ..).Holds μ)
  wCov_place, padW_places, covW_places   padding BY PLACES (a key's number is (place | column), the
                                         column in the low k bits):
                     a weight is (the place's weight, 0 at padding) * (the column's weight); padW
                       and covW are sums over PLACES
  eqN_eq_eqLow       the two listings: Blocks.eqN v 0 pt j = eqLow (lowPt v pt) j, for every number
                     j
  Dat.cls_pad_iff        at the common letters, under A.PadIs: part i's end claim ⇔ the claim with
                         weights 0 at isPad's places and
                     tab padRow * padW out of the target
  Dat.LinIs, Dat.claimLin, Dat.claimLin_iff   THE BRIDGE AS CODE (no noncomputable mark: Lean makes
                                              code for wCov, padW, covW, keyRow, claimLin,
                     outRows at any field whose operations are code): where a real key is off + ⟨co
                       i b, μ⟩, part i's end claim ⇔ the ROW claimLin
  Dat.outRows, Dat.done_iff_rows   what the lookup leaves as m + (the rows) ROWS on the entries; the
                                   last joint Done ⇔ these rows hold
WHICH LISTING: claimLin takes cl.pt AS THE LIBRARY LISTS IT (MCl.pt: coordinate 0 = the TOP bit of a
key's number). The port's list of that point is
lowPt v cl.pt (bit t's coordinate at place t), and Letters' mleN lists as the port does.
PREMISES: what each statement says of the keys at padding and at real places. Nothing else.
NOT SAID: that a block ends with such a claim; which point; anything on the port.
The library has the like for keys that are affine in one column of a matrix, padding not set apart:
Cb.ldWfK_ext (Cb/Ld/LdWfKeys.lean).

-/
import Blocks.LookupCalls
import Cb.Pv.KeyLookup.Letters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Finset Blocks Cb.LdLkp

section
variable {E : Type} [Field E]

/-- The weight of key number b: the equality vector at the point, and 0 at padding. -/
def wCov (v : ℕ) (pt : ℕ → E) (pad : ℕ → Bool) (b : ℕ) : E :=
  if pad b = true then 0 else eqN v 0 pt b

/-- The equality vector's sum over the padding. -/
def padW (v : ℕ) (pt : ℕ → E) (pad : ℕ → Bool) : E :=
  ∑ b ∈ range (2 ^ v), if pad b = true then eqN v 0 pt b else 0

/-- The equality vector's sum over the real keys. -/
def covW (v : ℕ) (pt : ℕ → E) (pad : ℕ → Bool) : E := ∑ b ∈ range (2 ^ v), wCov v pt pad b

theorem sum_eqN_one (k off : ℕ) (pt : ℕ → E) : ∑ b ∈ range (2 ^ k), eqN k off pt b = 1 := by
  simp only [eqN_eq]
  exact Alg.sum_eqN _

theorem covW_add_padW (v : ℕ) (pt : ℕ → E) (pad : ℕ → Bool) :
    covW v pt pad + padW v pt pad = 1 := by
  unfold covW padW wCov
  rw [← sum_add_distrib, ← sum_eqN_one v 0 pt]
  refine sum_congr rfl fun b _ => ?_
  by_cases hp : pad b = true
  · rw [if_pos hp, if_pos hp, zero_add]
  · rw [if_neg hp, if_neg hp, add_zero]

/-- The extension of all keys: the real keys under their weights, and the padding's share. -/
theorem ext_split (v : ℕ) (key pt : ℕ → E) (pad : ℕ → Bool) (c : E)
    (h : ∀ b < 2 ^ v, pad b = true → key b = c) :
    Blocks.ext v key pt = ∑ b ∈ range (2 ^ v), wCov v pt pad b * key b + c * padW v pt pad := by
  unfold Blocks.ext padW wCov
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun b hb => ?_
  by_cases hp : pad b = true
  · rw [if_pos hp, if_pos hp, h b (mem_range.1 hb) hp]
    ring
  · rw [if_neg hp, if_neg hp]
    ring

/-- The real keys under their weights: the offset's share, and what is left. -/
theorem sum_off (v : ℕ) (key lin pt : ℕ → E) (pad : ℕ → Bool) (off : E)
    (h : ∀ b < 2 ^ v, pad b = false → key b = off + lin b) :
    ∑ b ∈ range (2 ^ v), wCov v pt pad b * key b =
      off * covW v pt pad + ∑ b ∈ range (2 ^ v), wCov v pt pad b * lin b := by
  unfold covW
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun b hb => ?_
  cases hp : pad b with
  | true => simp [wCov, hp]
  | false =>
    rw [h b (mem_range.1 hb) hp]
    ring

variable {N : Type} [Fintype N]

/-- The padding's share leaves the target; the weights are 0 at padding. -/
theorem holds_pad_iff (cl : MCl E N) (v : ℕ) (key : ℕ → E) (μ : N → E) (pad : ℕ → Bool) (c : E)
    (h : ∀ b < 2 ^ v, pad b = true → key b = c) :
    cl.Holds v key μ ↔
      ∑ b ∈ range (2 ^ v), wCov v cl.pt pad b * key b + ∑ i, cl.mf i * μ i =
        cl.tg - c * padW v cl.pt pad := by
  unfold MCl.Holds
  rw [ext_split v key cl.pt pad c h]
  constructor <;> intro h' <;> linear_combination h'

/-- The offset's share leaves the target too. -/
theorem holds_off_iff (cl : MCl E N) (v : ℕ) (key lin : ℕ → E) (μ : N → E) (pad : ℕ → Bool)
    (c off : E) (h : ∀ b < 2 ^ v, pad b = true → key b = c)
    (h2 : ∀ b < 2 ^ v, pad b = false → key b = off + lin b) :
    cl.Holds v key μ ↔
      ∑ b ∈ range (2 ^ v), wCov v cl.pt pad b * lin b + ∑ i, cl.mf i * μ i =
        cl.tg - c * padW v cl.pt pad - off * covW v cl.pt pad := by
  rw [holds_pad_iff cl v key μ pad c h, sum_off v key lin cl.pt pad off h2]
  constructor <;> intro h' <;> linear_combination h'

/-- The claim on a part's keys as a row on the entries. co b: the linear form of the real key b. -/
def keyRow (cl : MCl E N) (v : ℕ) (pad : ℕ → Bool) (c off : E) (co : ℕ → N → E) : Row E N :=
  ⟨fun i => ∑ b ∈ range (2 ^ v), wCov v cl.pt pad b * co b i + cl.mf i,
    cl.tg - c * padW v cl.pt pad - off * covW v cl.pt pad⟩

theorem holds_row_iff (cl : MCl E N) (v : ℕ) (key : ℕ → E) (μ : N → E) (pad : ℕ → Bool)
    (c off : E) (co : ℕ → N → E) (h : ∀ b < 2 ^ v, pad b = true → key b = c)
    (h2 : ∀ b < 2 ^ v, pad b = false → key b = off + ∑ i, co b i * μ i) :
    cl.Holds v key μ ↔ (keyRow cl v pad c off co).Holds μ := by
  rw [holds_off_iff cl v key (fun b => ∑ i, co b i * μ i) μ pad c off h h2]
  unfold Row.Holds keyRow
  have e : ∑ i, (∑ b ∈ range (2 ^ v), wCov v cl.pt pad b * co b i + cl.mf i) * μ i =
      ∑ b ∈ range (2 ^ v), wCov v cl.pt pad b * ∑ i, co b i * μ i + ∑ i, cl.mf i * μ i := by
    simp only [add_mul, sum_add_distrib, sum_mul, mul_sum]
    rw [sum_comm]
    congr 1
    exact sum_congr rfl fun b _ => sum_congr rfl fun i _ => by ring
  rw [e]

end

/-! ### padding by places -/

section
variable {E : Type} [Field E]

private theorem div_place (k u c : ℕ) (hc : c < 2 ^ k) : (u * 2 ^ k + c) / 2 ^ k = u := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt hc,
    Nat.zero_add]

/-- A weight at the key number (place u | column c). -/
theorem wCov_place (R k : ℕ) (pt : ℕ → E) (padP : ℕ → Bool) (u : ℕ) {c : ℕ} (hc : c < 2 ^ k) :
    wCov (R + k) pt (fun b => padP (b / 2 ^ k)) (u * 2 ^ k + c) =
      wCov R pt padP u * eqN k R pt c := by
  unfold wCov
  beta_reduce
  rw [div_place k u c hc, eqN_append' R k 0 pt u hc, Nat.zero_add]
  by_cases hp : padP u = true
  · rw [if_pos hp, if_pos hp, zero_mul]
  · rw [if_neg hp, if_neg hp]

theorem covW_places (R k : ℕ) (pt : ℕ → E) (padP : ℕ → Bool) :
    covW (R + k) pt (fun b => padP (b / 2 ^ k)) = covW R pt padP := by
  unfold covW
  rw [pow_add, Alg.sum_range_mul_add]
  refine sum_congr rfl fun u _ => ?_
  rw [sum_congr rfl fun c hc => wCov_place R k pt padP u (mem_range.1 hc), ← mul_sum,
    sum_eqN_one, mul_one]

theorem padW_places (R k : ℕ) (pt : ℕ → E) (padP : ℕ → Bool) :
    padW (R + k) pt (fun b => padP (b / 2 ^ k)) = padW R pt padP := by
  have h1 := covW_add_padW (R + k) pt fun b => padP (b / 2 ^ k)
  have h2 := covW_add_padW R pt padP
  rw [covW_places] at h1
  linear_combination h1 - h2

/-! ### the two listings of a point -/

/-- The equality vector by a list: the first coordinate goes with the lowest bit. -/
def eqLow : List E → ℕ → E
  | [], _ => 1
  | x :: xs, j => (if j % 2 = 1 then x else 1 - x) * eqLow xs (j / 2)

/-- The first v coordinates of a point in the library's listing, as a list with bit t's coordinate
at
place t. -/
def lowPt (v : ℕ) (pt : ℕ → E) : List E := (List.range v).map fun s => pt (v - 1 - s)

omit [Field E] in
theorem lowPt_length (v : ℕ) (pt : ℕ → E) : (lowPt v pt).length = v := by
  unfold lowPt
  rw [List.length_map, List.length_range]

omit [Field E] in
theorem lowPt_succ (v : ℕ) (pt : ℕ → E) : lowPt (v + 1) pt = pt v :: lowPt v pt := by
  unfold lowPt
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  refine List.map_congr_left fun s _ => ?_
  show pt (v + 1 - 1 - (s + 1)) = pt (v - 1 - s)
  congr 1
  omega

theorem eqN_succ_low (v : ℕ) (pt : ℕ → E) (j : ℕ) :
    eqN (v + 1) 0 pt j = (if j % 2 = 1 then pt v else 1 - pt v) * eqN v 0 pt (j / 2) := by
  unfold eqN
  rw [prod_range_succ, mul_comm]
  congr 1
  · have e : v + 1 - 1 - v = 0 := by omega
    rw [e, Nat.testBit_zero, Nat.zero_add]
    by_cases h : j % 2 = 1 <;> simp [h]
  · refine prod_congr rfl fun t ht => ?_
    have e : v + 1 - 1 - t = (v - 1 - t) + 1 := by
      have := mem_range.1 ht
      omega
    rw [e, Nat.testBit_succ]

/-- The two listings give one equality vector. -/
theorem eqN_eq_eqLow (pt : ℕ → E) : ∀ (v j : ℕ), eqN v 0 pt j = eqLow (lowPt v pt) j
  | 0, j => by simp [eqN, lowPt, eqLow]
  | v + 1, j => by
    rw [eqN_succ_low, lowPt_succ, eqN_eq_eqLow pt v (j / 2)]
    rfl

end

/-! ### at the common letters -/

/-- Part i's end claim, under «a place of padding holds the padding's row». -/
theorem Dat.cls_pad_iff {E : Type} [Field E] [Fintype E] (A : Dat E) (hP : A.PadIs) (st : A.St)
    (μ : A.J → E) (i : ℕ) (cl : MCl E A.J) :
    cl.Holds (A.v i) (A.key st μ i) μ ↔
      ∑ b ∈ range (2 ^ A.v i), wCov (A.v i) cl.pt (A.isPad i) b * A.key st μ i b +
          ∑ j, cl.mf j * μ j =
        cl.tg - A.tab st A.padRow * padW (A.v i) cl.pt (A.isPad i) :=
  holds_pad_iff cl (A.v i) (A.key st μ i) μ (A.isPad i) (A.tab st A.padRow)
    fun b _ hb => hP st μ i b hb

namespace Dat
variable {E : Type} [Field E] [Fintype E] (A : Dat E)

/-- A property of the data: a real key is a public offset plus a public linear form in the entries.
-/
def LinIs (off : E) (co : ℕ → ℕ → A.J → E) : Prop :=
  ∀ st μ i b, i < A.m → b < 2 ^ A.v i → A.isPad i b = false →
    A.key st μ i b = off + ∑ j, co i b j * μ j

/-- THE BRIDGE AS CODE: part i's end claim as a row on the entries: the weight of entry j is the sum
over the real keys b
of (the equality vector at the claim's point, in the library's listing) * co i b j, plus the mask
form; the padding's share and
the offset's share are out of the target. -/
def claimLin (off : E) (co : ℕ → ℕ → A.J → E) (st : A.St) (i : ℕ) (cl : MCl E A.J) : Row E A.J :=
  keyRow cl (A.v i) (A.isPad i) (A.tab st A.padRow) off (co i)

theorem claimLin_iff (hP : A.PadIs) {off : E} {co : ℕ → ℕ → A.J → E} (hL : A.LinIs off co)
    (st : A.St) (μ : A.J → E) {i : ℕ} (hi : i < A.m) (cl : MCl E A.J) :
    cl.Holds (A.v i) (A.key st μ i) μ ↔ (A.claimLin off co st i cl).Holds μ :=
  holds_row_iff cl (A.v i) (A.key st μ i) μ (A.isPad i) (A.tab st A.padRow) off (co i)
    (fun b _ hb => hP st μ i b hb) fun b hb hp => hL st μ i b hi hb hp

/-- What the lookup leaves, as rows alone: a row a part, in the parts' order, then the rows. -/
def outRows (off : E) (co : ℕ → ℕ → A.J → E) (o : A.Out) : List (Row E A.J) :=
  ((List.finRange A.m).map fun i : Fin A.m => A.claimLin off co o.1 i.val (o.2.1 i)) ++ o.2.2

theorem outRows_length (off : E) (co : ℕ → ℕ → A.J → E) (o : A.Out) :
    (A.outRows off co o).length = A.m + o.2.2.length := by
  unfold outRows
  rw [List.length_append, List.length_map, List.length_finRange]

/-- The last joint says that these rows hold. -/
theorem done_iff_rows (hP : A.PadIs) {off : E} {co : ℕ → ℕ → A.J → E} (hL : A.LinIs off co)
    (μ : A.J → E) (o : A.Out) : A.Done μ o ↔ RowsHold (A.outRows off co o) μ := by
  constructor
  · rintro ⟨h1, h2⟩ r hr
    rcases List.mem_append.1 hr with h | h
    · obtain ⟨i, _, rfl⟩ := List.mem_map.1 h
      exact (A.claimLin_iff hP hL o.1 μ i.2 (o.2.1 i)).1 (h1 i)
    · exact h2 r h
  · intro h
    refine ⟨fun i => (A.claimLin_iff hP hL o.1 μ i.2 (o.2.1 i)).2
      (h _ (List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))),
      fun r hr => h r (List.mem_append_right _ hr)⟩

end Dat

end Lk6

#print axioms Lk6.covW_add_padW
#print axioms Lk6.ext_split
#print axioms Lk6.holds_pad_iff
#print axioms Lk6.holds_off_iff
#print axioms Lk6.holds_row_iff
#print axioms Lk6.wCov_place
#print axioms Lk6.covW_places
#print axioms Lk6.padW_places
#print axioms Lk6.eqN_eq_eqLow
#print axioms Lk6.Dat.cls_pad_iff
#print axioms Lk6.Dat.claimLin_iff
#print axioms Lk6.Dat.done_iff_rows
