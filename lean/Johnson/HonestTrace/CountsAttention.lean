-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsAttention.lean

The multiplicities of the lookup of an attention sub-proof's own calls: which places of its key
vectors are padding places, which table row is chosen for a key, the matrix bA of the bits of the
counts, and the relation after the challenge (Cb.Lkp.MidP) at these bits. It is
Johnson/HonestTrace/CountsLaw.lean applied to the verifier's own shape of the sub-proof.

The setting. Attention.shapeHid (OnBytes/Model/AttentionShape.lean), a function of the Lean verifier
under OnBytes/, derives a pair (S, fs) from a configuration cf and a cap lid on a tree's depth: S is
the sub-proof's shape, with its calls and their pieces, and fs holds the numbers of the one lookup
in which these calls run. OnBytes/Tie/Pv/Lookup/Ends/A.lean writes the calls' key vectors (A.kvA),
the joint key vector and the joint table (A.keyA, A.tabA) and the planes of the counts (A.placeBA,
A.bitsA) as terms over a reading cell : NameA → K of named cells. A theorem of this file with the
premise "shapeHid lid cf = .ok (S, fs)" speaks of every cap lid and every configuration cf at which
shapeHid returns, and so of all sizes, every call list and every choice of shifts in such a
configuration.

What had to be shown. shapeHid counts the padding keys of a call as one run of places, from the sum
of its pieces' sizes (the field tot) to the call's last place, and adds that run to the public
numbers fs.pub tree by tree (Forest.pubRun). A.kvA holds the padding key at the places that no piece
holds. The verifier's own comparison of two descriptions of the padding (Attention.paddingLaid,
OnBytes/Model/Attention.lean) counts, call by call, the places of every piece that no key form
weighs and the places from the end of the last weighed piece on; by the docstring of its routine
paddingOfCall it "assumes, and does not test, that the pieces follow one another without a gap".
Here that is a theorem: Attention.layOff gives each piece the sum of the sizes of the pieces before
it as the number of its first key, so the places that no piece holds are the places from tot on
("padA_iff").

Main definitions:
* "padA S q X": place X of call q is a padding place: no piece of the call holds it.
* "hitsA": hitsOf at the tables of fs, the key vectors A.kvA and the padding places padA. "bA": the
  matrix of the bits of the counts at hitsA, by row and column, with values 0 and 1.
* "LaidBA S fs cell": cell holds, at the rows below 2^lmb and the columns below NC 2^(kT + 5 - lmb)
  of matrix number NAs + 2, the matrix bA of cell itself. "withBA": a reading with bA of that
  reading laid over matrix number NAs + 2.

Main theorems. (hs) stands for the premise "shapeHid lid cf = .ok (S, fs)".
* "padA_iff": under (hs), for q below S.calls.size: place X of call q is a padding place if and only
  if X is at least the call's field tot.
* "ok_A", "lmb_A", "size_A": under (hs): FoNums.ok fs = true; 5 ≤ S.cf.lmb ≤ fs.kT + 5; S and fs
  have fs.NC calls each. The first two are restatements of theorems under OnBytes/Tie/Pv/Lookup.
* "pubFits_A": under (hs): PubFits fs (padA S): for every tree y below fs.NT, entry y of fs.pub is
  the number of padding places among the 2^dT places of tree y.
* "kvA_pad": for q below both numbers of calls, A.kvA holds the value of the call's padding row at
  every padding place.
* "placeBA_cellRC": for u below 2^d with u % 2^cK below fs.NC, and j below 32, A.placeBA S fs u j is
  the cell of matrix number NAs + 2 at the row and column FoNums.cellRC. "bitsA_plane": under LaidBA
  and 5 ≤ lmb ≤ kT + 5, for u below 2^d and j below 32, A.bitsA at u * 32 + j is the cell of plane
  at that row and column.
* "fitsA": under (hs), if every key of every call is a row of the call's table: Fits.
* "lawA": under (hs), the same premise on the keys and LaidBA: Cb.Lkp.MidP at all elements θ and al
  of K, of A.keyA, A.tabA, FoNums.pads fs and A.bitsA, with the keys and the bits read at the one
  reading cell. θ is the element that separates the calls in the joint key vector and the joint
  table: call c's keys and rows are moved by c θ.
* "sum_bA": under (hs) and the same premise on the keys: the cells of bA in the rows r below 2^lmb
  and the columns below NC 2^(kT + 5 - lmb), weighted by 2^(r % 32), and fs.padding add up to 2^v.
* "Att.kvA_off": under (hs), two readings that agree at every cell outside matrix number NAs + 2
  give the same A.kvA, at every call number and every place. "kvA_withBA", "withBA_laid",
  "inTable_withBA": so laying bA moves no key, withBA meets LaidBA, and it keeps the premise on the
  keys.
The names under "Att" are steps of these proofs: "Att.ov" (the overlap of a run of places with a
block), "Att.pubLoop_getD", "Att.pubRun_getD", "Att.fold_getD" (what Forest.pubLoop, Forest.pubRun
and shapeHid's loop over the calls add to each tree's number), "Att.hid_placed", "Att.find_offsL"
(the pieces), "Att.Nums", "Att.nums_of_hid", "Att.segKey_off" (which cells a key reads).

Limits. These are specifications, not programs to run (Johnson/HonestTrace/Counts.lean, Limits). K
is any field with decidable equality; hitsA, and so bA, compare keys with table rows in K. That bA
is the same over two fields with a map between them is "bA_map",
Johnson/HonestTrace/CountsAttentionMap.lean. That every key is a row of its table is a premise here;
no theorem of this file supplies it. Where a key is in no row, firstRow gives 0 and bA counts the
key at row 0: a value without a meaning, of which no theorem here speaks. Ends/A.lean casts a table
row's 64-bit number into K; its head says in which rings that is what the verifier means.

Not claimed: that A.kvA, A.keyA, A.tabA and A.bitsA are what the verifier computes or tests (the
head of Ends/A.lean says the same); that the cells which a prover commits to are these; that the C++
prover chooses these rows; that a proof made from these cells is accepted; anything on a claim, a
round, a mask or a message; that Attention.paddingLaid passes, or that its count of padding places
is padA's; that shapeHid returns at any configuration.

-/
import Johnson.HonestTrace.CountsLaw
import Johnson.HonestTrace.CountsRect
import Johnson.Road.Lane5AttLaid
import OnBytes.Tie.Pv.Lookup.Ends.A
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPubA
import OnBytes.TieK.LinksEnd

set_option autoImplicit false

namespace OnBytes.HonestTrace

open Finset
open OnBytes.Model
open OnBytes.Ends (NameA)
open Cb.Lkp

/-- Place X of call q's key vector is a padding place: no piece of the call holds X. For a call q of
S this is the case in which A.kvSel, called with the padding, gives the value of the call's padding
row. For a number q that is no call's, padA says true at every X, while A.kvSel gives 0. -/
def padA (S : Attention.Shape) (q X : ℕ) : Bool :=
  match S.calls[q]? with
  | none => true
  | some c => (c.pcs.toList.find? fun p => decide (p.off ≤ X ∧ X < p.off + 2 ^ p.b)).isNone

namespace Att

open OnBytes.Road.L5 (offsL sizeL layOff_eq bind_ok refuse_ok hid_calls calls_of_shape mapM_cons_ok)

/-! ## Runs of places, block by block -/

/-- min (first + count) ((b + 1) D) less max first (b D), and 0 if that is negative: the number of
the places first, .., first + count - 1 that lie in block b, the places b D, .., (b + 1) D - 1. -/
def ov (D first count b : ℕ) : ℕ := min (first + count) ((b + 1) * D) - max first (b * D)

/-- A run of no places has the overlap 0 with every block. -/
theorem ov_zero (D first b : ℕ) : ov D first 0 b = 0 := by
  unfold ov
  omega

/-- If place first lies in block b0, then the overlap of the run of count places from first on with
block b is the sum of two numbers: the length of the run's part up to the end of block b0 if b0 = b,
and 0 if not; and the overlap of the rest of the run with block b. -/
theorem ov_step {D first count b0 : ℕ} (hlo : b0 * D ≤ first) (hhi : first < (b0 + 1) * D)
    (b : ℕ) :
    (if b0 = b then min count ((b0 + 1) * D - first) else 0) +
      ov D (first + min count ((b0 + 1) * D - first))
        (count - min count ((b0 + 1) * D - first)) b = ov D first count b := by
  have e0 : (b0 + 1) * D = b0 * D + D := Nat.succ_mul _ _
  have e1 : (b + 1) * D = b * D + D := Nat.succ_mul _ _
  unfold ov
  rcases lt_trichotomy b b0 with h | h | h
  · have h2 : (b + 1) * D ≤ b0 * D := Nat.mul_le_mul_right D h
    rw [if_neg (by omega)]
    omega
  · subst h
    rw [if_pos rfl]
    omega
  · have h2 : (b0 + 1) * D ≤ b * D := Nat.mul_le_mul_right D h
    rw [if_neg (by omega)]
    omega

/-- Of the numbers x below D, D - (t - m) satisfy t ≤ x + m (both subtractions truncated). -/
theorem card_from (D t m : ℕ) : ((range D).filter fun x => t ≤ x + m).card = D - (t - m) := by
  have e : ((range D).filter fun x => t ≤ x + m) = Ico (t - m) D := by
    ext x
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [e, Nat.card_Ico]

/-! ## Forest.pubLoop and Forest.pubRun, tree by tree -/

/-- For y inside an array of numbers: adding t to the entry at index j adds t to the entry at y if j
= y, and leaves it if not. -/
theorem getD_modify_add (pub : Array ℕ) (j t : ℕ) {y : ℕ} (hy : y < pub.size) :
    (pub.modify j (· + t)).getD y 0 = pub.getD y 0 + if j = y then t else 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h : j = y
  · subst h
    simp [hy]
  · simp [h]

/-- One step of Forest.pubLoop at a count that is not 0, written out. -/
theorem pubLoop_succ (dT base steps : ℕ) (pub : Array ℕ) (first : ℕ) {count : ℕ}
    (h0 : count ≠ 0) :
    Forest.pubLoop dT base (steps + 1) pub first count =
      Forest.pubLoop dT base steps
        (pub.modify (base + first / 2 ^ dT)
          (· + min count ((first / 2 ^ dT + 1) * 2 ^ dT - first)))
        (first + min count ((first / 2 ^ dT + 1) * 2 ^ dT - first))
        (count - min count ((first / 2 ^ dT + 1) * 2 ^ dT - first)) := by
  rw [Forest.pubLoop, if_neg h0]

/-- If count = 0, or the run of count places from first on ends within steps blocks of 2^dT places,
counted from the block of first, then Forest.pubLoop keeps the array's size, and for z inside the
array it adds to entry z the overlap of the run with block z - base if base ≤ z, and nothing if not.
-/
theorem pubLoop_getD (dT base : ℕ) : ∀ (steps : ℕ) (pub : Array ℕ) (first count : ℕ),
    (count = 0 ∨ first + count ≤ (first / 2 ^ dT + steps) * 2 ^ dT) →
    (Forest.pubLoop dT base steps pub first count).size = pub.size ∧ ∀ z < pub.size,
      (Forest.pubLoop dT base steps pub first count).getD z 0 =
        pub.getD z 0 + if base ≤ z then ov (2 ^ dT) first count (z - base) else 0
  | 0, pub, first, count, hf => by
    have h0 : count = 0 := by
      rcases hf with h | h
      · exact h
      · have h1 := Nat.div_mul_le_self first (2 ^ dT)
        rw [Nat.add_zero] at h
        omega
    subst h0
    refine ⟨rfl, fun z _ => ?_⟩
    rw [ov_zero]
    simp [Forest.pubLoop]
  | steps + 1, pub, first, count, hf => by
    by_cases h0 : count = 0
    · subst h0
      have e : Forest.pubLoop dT base (steps + 1) pub first 0 = pub := by
        rw [Forest.pubLoop, if_pos rfl]
      rw [e]
      refine ⟨rfl, fun z _ => ?_⟩
      rw [ov_zero]
      simp
    · rw [pubLoop_succ dT base steps pub first h0]
      have hD : 0 < 2 ^ dT := Nat.two_pow_pos _
      have hlo : first / 2 ^ dT * 2 ^ dT ≤ first := Nat.div_mul_le_self _ _
      have hhi : first < (first / 2 ^ dT + 1) * 2 ^ dT := by
        rw [Nat.mul_comm]
        exact Nat.lt_mul_div_succ first hD
      have hf' : first + count ≤ (first / 2 ^ dT + (steps + 1)) * 2 ^ dT := hf.resolve_left h0
      have key := fun b => ov_step (count := count) hlo hhi b
      generalize first / 2 ^ dT = b0 at hlo hhi hf' key ⊢
      generalize hT : min count ((b0 + 1) * 2 ^ dT - first) = take at key ⊢
      have pre : count - take = 0 ∨
          first + take + (count - take) ≤ ((first + take) / 2 ^ dT + steps) * 2 ^ dT := by
        by_cases hc : count ≤ (b0 + 1) * 2 ^ dT - first
        · left
          omega
        · right
          have e1 : first + take = (b0 + 1) * 2 ^ dT := by omega
          rw [e1, Nat.mul_div_cancel _ hD]
          have e2 : (b0 + 1 + steps) * 2 ^ dT = (b0 + (steps + 1)) * 2 ^ dT := by ring
          omega
      obtain ⟨s, g⟩ := pubLoop_getD dT base steps (pub.modify (base + b0) (· + take))
        (first + take) (count - take) pre
      refine ⟨by rw [s, Array.size_modify], fun z hz => ?_⟩
      rw [g z (by rw [Array.size_modify]; exact hz), getD_modify_add pub _ _ hz]
      by_cases hb : base ≤ z
      · rw [if_pos hb, if_pos hb, ← key (z - base)]
        by_cases hz0 : b0 = z - base
        · rw [if_pos hz0, if_pos (by omega), Nat.add_assoc]
        · rw [if_neg hz0, if_neg (by omega), Nat.add_assoc]
      · rw [if_neg hb, if_neg hb, if_neg (by omega)]

/-- Where Forest.pubRun h pub c first count returns pub': pub' has h.NT entries; first + count is at
most 2^(dT + iota_c); and for z below h.NT, entry z of pub' is entry z of pub plus the overlap of
the run with block z - first_c of 2^dT places if first_c ≤ z, and entry z of pub if not. Here iota_c
and first_c are FoNums.io h c and FoNums.fst h c. -/
theorem pubRun_getD {h : Forest.Shape} {pub pub' : Array ℕ} {c first count : ℕ}
    (hr : Forest.pubRun h pub c first count = .ok pub') :
    pub'.size = h.NT ∧ first + count ≤ 2 ^ (h.dT + FoNums.io h c) ∧ ∀ z < h.NT,
      pub'.getD z 0 = pub.getD z 0 +
        if FoNums.fst h c ≤ z then ov (2 ^ h.dT) first count (z - FoNums.fst h c) else 0 := by
  unfold Forest.pubRun at hr
  obtain ⟨c1, hr⟩ := Ends.ok_of_jp hr
  obtain ⟨c2, hr⟩ := Ends.ok_of_jp hr
  have e := (Except.ok.inj hr).symm
  subst e
  have s : pub.size = h.NT := by
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or, not_not] at c1
    exact c1.1
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt, gt_iff_lt] at c2
  have hle0 : first + count ≤ 2 ^ (h.dT + h.iota.getD c 0) := by omega
  have hle : first + count ≤ 2 ^ h.iota.getD c 0 * 2 ^ h.dT := by
    rw [← pow_add, Nat.add_comm (h.iota.getD c 0)]
    exact hle0
  obtain ⟨s', g⟩ := pubLoop_getD h.dT (h.first.getD c 0) (2 ^ h.iota.getD c 0 + 1) pub first count
    (Or.inr (Nat.le_trans hle (Nat.mul_le_mul_right _
      (Nat.le_trans (Nat.le_succ _) (Nat.le_add_left _ _)))))
  exact ⟨by rw [s', s], hle0, fun z hz => g z (by rw [s]; exact hz)⟩

/-! ## The loop of shapeHid over the calls -/

/-- The overlap of the run of places tot q, .., 2^(n q) - 1 with block z - first_q of 2^dT places,
if first_q ≤ z; 0 if not. -/
def share (h : Forest.Shape) (tot n : ℕ → ℕ) (q z : ℕ) : ℕ :=
  if FoNums.fst h q ≤ z then ov (2 ^ h.dT) (tot q) (2 ^ n q - tot q) (z - FoNums.fst h q) else 0

/-- The loop of shapeHid over the calls, on a list L, started at the array pub and the call number
k. If member number i of L has the fields tot = tot (k + i) and call.n = n (k + i), and the loop
returns r, then for every i below L.length, with q = k + i: tot q + (2^(n q) - tot q), the
subtraction truncated, is at most 2^(dT + iota_q); and for z below h.NT entry z of r.1 is entry z of
pub plus the shares of the calls k, .., k + L.length - 1 at z. -/
theorem fold_getD (h : Forest.Shape) (tot n : ℕ → ℕ) :
    ∀ (L : List Attention.ACall) (pub : Array ℕ) (k : ℕ) (r : Array ℕ × ℕ),
    (∀ i c, L[i]? = some c → c.tot = tot (k + i) ∧ c.call.n = n (k + i)) →
    L.foldlM (fun (st : Array ℕ × ℕ) c => do
      let pub ← Forest.pubRun h st.1 st.2 c.tot (2 ^ c.call.n - c.tot)
      pure (pub, st.2 + 1)) (pub, k) = Except.ok r →
    (∀ i < L.length,
      tot (k + i) + (2 ^ n (k + i) - tot (k + i)) ≤ 2 ^ (h.dT + FoNums.io h (k + i))) ∧
    ∀ z < h.NT, r.1.getD z 0 = pub.getD z 0 + ∑ i ∈ range L.length, share h tot n (k + i) z
  | [], pub, k, r, _, hr => by
    rw [List.foldlM_nil] at hr
    have e := Except.ok.inj hr
    subst e
    exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun z _ => by simp⟩
  | c :: L, pub, k, r, hL, hr => by
    rw [List.foldlM_cons] at hr
    obtain ⟨st, h1, hr⟩ := bind_ok hr
    obtain ⟨pub1, h2, h3⟩ := bind_ok h1
    have e := Except.ok.inj h3
    subst e
    obtain ⟨t1, t2⟩ := hL 0 c rfl
    rw [Nat.add_zero] at t1 t2
    have h2' : Forest.pubRun h pub k (tot k) (2 ^ n k - tot k) = .ok pub1 := by
      rw [← t1, ← t2]
      exact h2
    obtain ⟨-, p2, p3⟩ := pubRun_getD h2'
    obtain ⟨i1, i2⟩ := fold_getD h tot n L pub1 (k + 1) r (fun i c' hc' => by
      have := hL (i + 1) c' (by simpa using hc')
      rwa [show k + (i + 1) = k + 1 + i by omega] at this) hr
    refine ⟨fun i hi => ?_, fun z hz => ?_⟩
    · cases i with
      | zero => exact p2
      | succ j =>
        have := i1 j (by simpa using hi)
        rwa [show k + 1 + j = k + (j + 1) by omega] at this
    · rw [i2 z hz, p3 z hz, List.length_cons, Finset.sum_range_succ']
      have es : ∀ i, share h tot n (k + 1 + i) z = share h tot n (k + (i + 1)) z := fun i => by
        rw [show k + 1 + i = k + (i + 1) by omega]
      simp only [es, Nat.add_zero]
      unfold share
      omega

/-- Under FoNums.ok h, for q below h.NC with tot q + (2^(n q) - tot q) at most 2^(dT + iota_q), the
subtraction truncated: the share of call q at z is 0 if FoNums.co h z, the call of tree z, is not q.
-/
theorem share_off {h : Forest.Shape} (hok : FoNums.ok h = true) (tot n : ℕ → ℕ) {q z : ℕ}
    (hq : q < h.NC) (hne : FoNums.co h z ≠ q)
    (hle : tot q + (2 ^ n q - tot q) ≤ 2 ^ (h.dT + FoNums.io h q)) : share h tot n q z = 0 := by
  unfold share
  split_ifs with hz
  · have hb : 2 ^ FoNums.io h q ≤ z - FoNums.fst h q := by
      by_contra hlt
      have := (((Cb.Fo.ok_parts hok).2.2.1 q hq).2.2.2 (z - FoNums.fst h q) (by omega)).2.1
      rw [Nat.add_sub_cancel' hz] at this
      exact hne this
    have h2 : 2 ^ FoNums.io h q * 2 ^ h.dT ≤ (z - FoNums.fst h q) * 2 ^ h.dT :=
      Nat.mul_le_mul_right _ hb
    rw [← pow_add, Nat.add_comm] at h2
    unfold ov
    omega
  · rfl

/-! ## What shapeHid returns -/

/-- The field tot of call q, the sum of its pieces' sizes; 0 if the shape has no call q. -/
def totA (S : Attention.Shape) (q : ℕ) : ℕ := ((S.calls[q]?).map (·.tot)).getD 0

/-- Where shapeHid returns (S, fs): the loop that shapeHid runs over the calls, read at the calls of
S and with Forest.pubRun at fs, started at an array of fs.NT zeros and the call number 0, returns a
pair whose first part is fs.pub; and the calls of fs are the fields call of the calls of S.
(shapeHid runs Forest.pubRun at the shape from which it makes fs by setting pub and calls, two
fields that Forest.pubRun does not read.) -/
theorem hid_fold {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape}
    (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) :
    ∃ r : Array ℕ × ℕ,
      S.calls.toList.foldlM (fun (st : Array ℕ × ℕ) c => do
        let pub ← Forest.pubRun fs st.1 st.2 c.tot (2 ^ c.call.n - c.tot)
        pure (pub, st.2 + 1)) (Array.replicate fs.NT 0, 0) = Except.ok r ∧
      fs.pub = r.1 ∧ fs.calls = S.calls.map (·.call) := by
  unfold Attention.shapeHid at hs
  obtain ⟨A, -, h⟩ := bind_ok hs
  obtain ⟨f, -, h⟩ := bind_ok h
  obtain ⟨-, h⟩ := refuse_ok h
  obtain ⟨kbA, -, h⟩ := bind_ok h
  obtain ⟨counted, hc, h⟩ := bind_ok h
  obtain ⟨-, -, h⟩ := bind_ok h
  have e := Except.ok.inj h
  obtain ⟨e1, e2⟩ := Prod.mk.inj e
  subst e1
  subst e2
  refine ⟨counted, ?_, rfl, rfl⟩
  rw [Array.foldlM_toList]
  exact hc

/-- Where List.mapM f l returns r, every member of r is what f returns at some member of l. -/
theorem mapM_mem {α β : Type} {f : α → Except String β} :
    ∀ {l : List α} {r : List β}, l.mapM f = Except.ok r → ∀ y ∈ r, ∃ x ∈ l, f x = Except.ok y
  | [], r, h, y, hy => by
    rw [List.mapM_nil] at h
    have e := Except.ok.inj h
    subst e
    cases hy
  | x :: l, r, h, y, hy => by
    obtain ⟨k, r', h1, h2, rfl⟩ := mapM_cons_ok h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨x, List.mem_cons_self, h1⟩
    · obtain ⟨x', hx', hf⟩ := mapM_mem h2 y hy
      exact ⟨x', List.mem_cons_of_mem _ hx', hf⟩

/-- Where layCall returns k at x: the fields pcs and tot of k are the two parts of what placePieces
returns at the kind, the shift and the segment kinds of x. -/
theorem layCall_laid {cf : Attention.Cfg} {HA Sm : ℕ} {Tt : Array ℕ} {x : Attention.Listed}
    {k : Attention.ACall} (h : Attention.layCall cf HA Sm Tt x = Except.ok k) :
    k.pcs = (Attention.placePieces cf HA x.2.1 x.2.2.1 x.2.2.2).1 ∧
      k.tot = (Attention.placePieces cf HA x.2.1 x.2.2.1 x.2.2.2).2 := by
  obtain ⟨name, kind, sh, segs⟩ := x
  unfold Attention.layCall at h
  obtain ⟨-, h⟩ := refuse_ok h
  have e := Except.ok.inj h
  subst e
  exact ⟨rfl, rfl⟩

/-- Where shapeHid returns (S, fs): the fields pcs and tot of every call of S are the two parts of
what placePieces returns at cf, cf.H / 2^lgk and some kind, shift and list of segment kinds. -/
theorem hid_placed {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape}
    (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) {c : Attention.ACall}
    (hc : c ∈ S.calls.toList) :
    ∃ (kind : Attention.Table) (sh : ℕ) (segs : List Attention.Seg),
      c.pcs = (Attention.placePieces cf (cf.H / 2 ^ cf.lgk) kind sh segs).1 ∧
      c.tot = (Attention.placePieces cf (cf.H / 2 ^ cf.lgk) kind sh segs).2 := by
  obtain ⟨A, io, kbA, hA, eS, -⟩ := hid_calls hs
  obtain ⟨calls, hM, hcs, -, -⟩ := calls_of_shape hA
  subst eS
  have hc' : c ∈ (A.calls.mapIdx fun q c =>
      ({ c with call := { c.call with iota := io q } } : Attention.ACall)).toList := hc
  rw [Array.toList_mapIdx, List.mem_mapIdx] at hc'
  obtain ⟨i, hi, rfl⟩ := hc'
  have el : A.calls.toList = calls := by rw [hcs]
  have hm : A.calls.toList[i] ∈ calls := by
    rw [← el]
    exact List.getElem_mem hi
  obtain ⟨x, -, hx⟩ := mapM_mem hM _ hm
  obtain ⟨p1, p2⟩ := layCall_laid hx
  exact ⟨_, _, _, p1, p2⟩

/-- In the list offsL l off, whose pieces follow one another from place off on, no piece holds place
X if and only if X is below off or at least off plus the sum of the pieces' sizes. -/
theorem find_offsL (X : ℕ) : ∀ (l : List Attention.Piece) (off : ℕ),
    ((offsL l off).find? fun p => decide (p.off ≤ X ∧ X < p.off + 2 ^ p.b)).isNone = true ↔
      (X < off ∨ off + sizeL l ≤ X)
  | [], off => by
    simp only [offsL, sizeL, List.find?_nil, Option.isNone_none, List.map_nil, List.sum_nil,
      true_iff]
    omega
  | p :: l, off => by
    have ih := find_offsL X l (off + 2 ^ p.b)
    have es : sizeL (p :: l) = 2 ^ p.b + sizeL l := by simp [sizeL]
    have hp : 0 < 2 ^ p.b := Nat.two_pow_pos _
    rw [es]
    by_cases hX : off ≤ X ∧ X < off + 2 ^ p.b
    · have e : ((offsL (p :: l) off).find? fun p => decide (p.off ≤ X ∧ X < p.off + 2 ^ p.b)) =
          some { p with off := off } := by
        simp [offsL, hX]
      rw [e]
      simp only [Option.isNone_some, Bool.false_eq_true, false_iff]
      omega
    · have e : ((offsL (p :: l) off).find? fun p => decide (p.off ≤ X ∧ X < p.off + 2 ^ p.b)) =
          ((offsL l (off + 2 ^ p.b)).find? fun p => decide (p.off ≤ X ∧ X < p.off + 2 ^ p.b)) := by
        simp [offsL, hX]
      rw [e, ih]
      omega

end Att

open Att

/-- **The padding places of a call are the places from the sum of its pieces' sizes on.** Where
shapeHid returns (S, fs), for q below S.calls.size and every X: padA S q X = true if and only if
totA S q ≤ X. -/
theorem padA_iff {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape}
    (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) {q : ℕ} (hq : q < S.calls.size) (X : ℕ) :
    padA S q X = true ↔ totA S q ≤ X := by
  have e : S.calls[q]? = some S.calls[q] := Array.getElem?_eq_getElem hq
  obtain ⟨kind, sh, segs, p1, p2⟩ := hid_placed hs (c := S.calls[q]) (by simp)
  unfold padA totA
  rw [e]
  show ((S.calls[q].pcs.toList.find? fun p => decide (p.off ≤ X ∧ X < p.off + 2 ^ p.b)).isNone
    = true) ↔ S.calls[q].tot ≤ X
  rw [p1, p2]
  unfold Attention.placePieces
  rw [OnBytes.Road.L5.layOff_eq]
  show (((OnBytes.Road.L5.offsL _ 0).find? _).isNone = true) ↔ _
  rw [find_offsL]
  omega

/-- Where shapeHid returns (S, fs), the test FoNums.ok on the lookup's public numbers says true of
fs. -/
theorem ok_A {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape}
    (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) : FoNums.ok fs = true :=
  Fo.Pay.shapeOf_ok (Fo.Pub2.shapeOf_shapeHid hs).1

/-- Where shapeHid returns (S, fs): 5 ≤ S.cf.lmb ≤ fs.kT + 5. -/
theorem lmb_A {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape}
    (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) :
    5 ≤ S.cf.lmb ∧ S.cf.lmb ≤ fs.kT + 5 := by
  rw [(Fo.Pub2.shapeOf_shapeHid hs).2]
  exact Fo.Pay.shapeHid_lm hs

/-- Where shapeHid returns (S, fs), S and fs have fs.NC calls each. -/
theorem size_A {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape}
    (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) :
    S.calls.size = fs.NC ∧ fs.calls.size = fs.NC := by
  obtain ⟨r, -, -, ec⟩ := hid_fold hs
  have h2 := (calls_size (ok_A hs)).1
  refine ⟨?_, h2⟩
  rw [← h2, ec, Array.size_map]

/-- **The public numbers of padding keys count the padding places, tree by tree.** Where shapeHid
returns (S, fs): for every tree y below fs.NT, entry y of fs.pub is the number of the places x below
2^dT of tree y at which padA S says true of the tree's call (PubFits fs (padA S)). -/
theorem pubFits_A {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape}
    (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) : PubFits fs (padA S) := by
  intro y hy
  have hok := ok_A hs
  obtain ⟨sz, -⟩ := size_A hs
  obtain ⟨r, hf, ep, ec⟩ := hid_fold hs
  obtain ⟨-, hB, hC, -⟩ := Cb.Fo.ok_parts hok
  obtain ⟨hc, lo, hi⟩ := hB y hy
  obtain ⟨-, -, hn, hb⟩ := hC _ hc
  obtain ⟨f1, f2⟩ := fold_getD fs (totA S) (FoNums.nOf fs) S.calls.toList _ 0 r (fun i c hic => by
    rw [Nat.zero_add]
    have hic' : S.calls[i]? = some c := by simpa using hic
    refine ⟨by simp [totA, hic'], ?_⟩
    simp [FoNums.nOf, ec, hic']) hf
  simp only [Nat.zero_add, Array.length_toList, sz] at f1 f2
  obtain ⟨c, hcE⟩ : ∃ c, c = FoNums.co fs y := ⟨_, rfl⟩
  rw [← hcE] at hc lo hi hn hb ⊢
  have hsum : ∑ i ∈ range fs.NC, share fs (totA S) (FoNums.nOf fs) i y =
      share fs (totA S) (FoNums.nOf fs) c y := by
    refine Finset.sum_eq_single c (fun q hq hne => ?_) (fun h => absurd (mem_range.2 hc) h)
    exact share_off hok _ _ (mem_range.1 hq) (by rw [← hcE]; exact fun e => hne e.symm)
      (f1 q (mem_range.1 hq))
  have hz : (Array.replicate fs.NT 0 : Array ℕ).getD y 0 = 0 := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, if_pos hy]
    rfl
  rw [ep, f2 y hy, hz, hsum, Nat.zero_add]
  obtain ⟨b, hbE⟩ : ∃ b, b = y - FoNums.fst fs c := ⟨_, rfl⟩
  have hbl : b < 2 ^ FoNums.io fs c := by omega
  have hmod : y % 2 ^ FoNums.io fs c = b := by
    have := (hb b hbl).2.2
    rwa [show FoNums.fst fs c + b = y by omega] at this
  rw [hmod]
  have hcard : ((range (2 ^ fs.dT)).filter fun x => padA S c (x + 2 ^ fs.dT * b) = true) =
      (range (2 ^ fs.dT)).filter fun x => totA S c ≤ x + 2 ^ fs.dT * b :=
    Finset.filter_congr fun x _ => padA_iff hs (by rw [sz]; exact hc) _
  rw [hcard, card_from]
  unfold share
  rw [if_pos lo, ← hbE]
  unfold ov
  have q1 := f1 c hc
  rw [hn] at q1 ⊢
  have e1 : (b + 1) * 2 ^ fs.dT = b * 2 ^ fs.dT + 2 ^ fs.dT := Nat.succ_mul _ _
  have e2 : (b + 1) * 2 ^ fs.dT ≤ 2 ^ FoNums.io fs c * 2 ^ fs.dT := Nat.mul_le_mul_right _ hbl
  rw [← pow_add] at e2
  rw [Nat.add_comm fs.dT] at q1
  rw [Nat.mul_comm (2 ^ fs.dT) b]
  omega

/-! ## The keys do not read the planes' matrix -/

namespace Att

open OnBytes.Road.L5 (offsL layOff_eq bind_ok refuse_ok hid_calls shaped_of_hid tests_of_hid)
open OnBytes.Ends.A

/-- If a < A and b < B then a B + b < A B. -/
theorem radix {a A b B : ℕ} (ha : a < A) (hb : b < B) : a * B + b < A * B :=
  calc a * B + b < a * B + B := Nat.add_lt_add_left hb _
    _ = (a + 1) * B := (Nat.succ_mul a B).symm
    _ ≤ A * B := Nat.mul_le_mul_right B ha

/-- What the theorems of this section read of a shape's numbers: B, G and T are positive; T = nT B;
G hP nT B B = 2^nM and G nT B B = 2^nD; nM and nD are nMOf and nDOf of the shape's configuration;
and cell number n of the matrix "as", for n below 5 Lam HA (2^nM + 2^nD), lies in a matrix whose
number is not NAs + 2. -/
structure Nums (S : Attention.Shape) : Prop where
  B : 0 < S.B
  G : 0 < S.G
  T : 0 < S.T
  TB : S.T = S.nT * S.B
  nM : S.G * S.hP * S.nT * S.B * S.B = 2 ^ S.nM
  nD : S.G * S.nT * S.B * S.B = 2 ^ S.nD
  eM : S.nM = Attention.nMOf S.cf
  eD : S.nD = Attention.nDOf S.cf
  as : ∀ n < 5 * S.Lam * S.HA * (2 ^ S.nM + 2 ^ S.nD),
    n / 2 ^ S.cf.lmS / (S.kAs / S.cf.NAs) ≠ S.cf.NAs + 2

/-- Four numbers of the shape that Attention.shape returns. -/
theorem shape_more {cf : Attention.Cfg} {S : Attention.Shape}
    (h : Attention.shape cf = Except.ok S) :
    S.B = 2 ^ cf.lB ∧ S.nT = 2 ^ (cf.lt - cf.lB) ∧ S.hP = 2 ^ (cf.lt - cf.lB) / 2 ∧
      S.G = 2 ^ cf.lgk := by
  unfold Attention.shape at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  have e := Except.ok.inj h
  subst e
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- For n below cells: n / 2^lmS, divided by the number of columns of one part, is not NAs + 2. The
number of columns of all NAs parts is cells / (NAs 2^lmS), rounded up, times NAs. For NAs above 0
the quotient is below NAs. For NAs = 0 it is 0, because Lean's x / 0 is 0. -/
theorem as_inside (cells NAs lmS n : ℕ) (hn : n < cells) :
    n / 2 ^ lmS / ((cells + NAs * 2 ^ lmS - 1) / (NAs * 2 ^ lmS) * NAs / NAs) ≠ NAs + 2 := by
  rcases Nat.eq_zero_or_pos NAs with h0 | h0
  · subst h0
    simp
  · rw [Nat.mul_div_cancel _ h0]
    have hU : 0 < NAs * 2 ^ lmS := Nat.mul_pos h0 (Nat.two_pow_pos _)
    obtain ⟨U, hUe⟩ : ∃ U, U = NAs * 2 ^ lmS := ⟨_, rfl⟩
    rw [← hUe] at hU ⊢
    obtain ⟨W, hW⟩ : ∃ W, W = (cells + U - 1) / U := ⟨_, rfl⟩
    rw [← hW]
    have h1 : cells ≤ W * U := by
      have := Nat.lt_mul_div_succ (cells + U - 1) hU
      rw [← hW] at this
      have e : U * (W + 1) = W * U + U := by ring
      omega
    have h2 : n / 2 ^ lmS < W * NAs := by
      apply Nat.div_lt_of_lt_mul
      have e : 2 ^ lmS * (W * NAs) = W * U := by
        rw [hUe]
        ring
      omega
    have h3 : n / 2 ^ lmS / W < NAs := Nat.div_lt_of_lt_mul h2
    omega

/-- Where shapeHid returns (S, fs), Nums holds of S. -/
theorem nums_of_hid {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape}
    (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) : Nums S := by
  have P := shaped_of_hid hs
  obtain ⟨hlt, -⟩ := tests_of_hid hs
  obtain ⟨A, io, kbA, hA, eS, -⟩ := hid_calls hs
  obtain ⟨mB, mT, mP, mG⟩ := shape_more hA
  have eB : S.B = 2 ^ cf.lB := by rw [eS]; exact mB
  have eT : S.nT = 2 ^ (cf.lt - cf.lB) := by rw [eS]; exact mT
  have eG : S.G = 2 ^ cf.lgk := by rw [eS]; exact mG
  have eP : S.hP = 2 ^ (cf.lt - cf.lB - 1) := by
    rw [eS]
    show A.hP = _
    rw [mP]
    obtain ⟨d, hd⟩ : ∃ d, cf.lt - cf.lB = d + 1 := ⟨cf.lt - cf.lB - 1, by omega⟩
    rw [hd, pow_succ, Nat.mul_div_cancel _ (by norm_num), Nat.add_sub_cancel]
  refine ⟨by rw [eB]; positivity, by rw [eG]; positivity, by rw [P.T]; positivity, ?_, ?_, ?_,
    by rw [P.nM, P.cfg], by rw [P.nD, P.cfg], ?_⟩
  · rw [P.T, eT, eB, ← pow_add]
    congr 1
    omega
  · rw [eG, eP, eT, eB, P.nM, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    unfold Attention.nMOf
    omega
  · rw [eG, eT, eB, P.nD, ← pow_add, ← pow_add, ← pow_add]
    congr 1
    unfold Attention.nDOf
    omega
  · intro n hn
    rw [P.kAs, P.cfg]
    rw [P.Lam, P.HA, P.nM, P.nD] at hn
    exact as_inside _ _ _ _ hn

variable {R : Type} [CommRing R]

/-- A.sumN n reads its function below n alone. -/
theorem sumN_congr {n : ℕ} {f g : ℕ → R} (h : ∀ i < n, f i = g i) : sumN n f = sumN n g := by
  unfold sumN
  have key : ∀ (l : List ℕ) (s : R), (∀ i ∈ l, f i = g i) →
      l.foldl (fun s i => s + f i) s = l.foldl (fun s i => s + g i) s := by
    intro l
    induction l with
    | nil =>
      intro s _
      rfl
    | cons a l ih =>
      intro s hl
      rw [List.foldl_cons, List.foldl_cons, hl a List.mem_cons_self]
      exact ih _ fun i hi => hl i (List.mem_cons_of_mem _ hi)
  exact key _ _ fun i hi => h i (List.mem_range.1 hi)

/-- The readings cell and cell' agree at every cell outside matrix number NAs + 2. -/
def Off (S : Attention.Shape) (cell cell' : NameA → R) : Prop :=
  ∀ n : NameA, n.M ≠ S.cf.NAs + 2 → cell' n = cell n

variable {S : Attention.Shape} {cell cell' : NameA → R}

omit [CommRing R] in
/-- Under Off, A.featC in a matrix whose number is not NAs + 2 is the same at both readings. -/
theorem featC_off (h : Off S cell cell') {M : ℕ} (hM : M ≠ S.cf.NAs + 2) (wc F i : ℕ) :
    featC S cell' M wc F i = featC S cell M wc F i :=
  h ⟨M, F % wc * S.T + i, F / wc⟩ hM

/-- Under Off, the row maxima are the same at both readings. -/
theorem mx_off (h : Off S cell cell') : mx S cell' = mx S cell := by
  funext lam hd i
  simp only [mx, featC_off h (show S.cf.NAs ≠ S.cf.NAs + 2 by omega)]

/-- Under Off, the denominators are the same at both readings. -/
theorem den_off (h : Off S cell cell') : den S cell' = den S cell := by
  funext lam hd i
  simp only [den, featC_off h (show S.cf.NAs ≠ S.cf.NAs + 2 by omega)]

omit [CommRing R] in
/-- Under Off, the index bits are the same at both readings. -/
theorem ib_off (h : Off S cell cell') : ib S cell' = ib S cell := by
  funext lam k hd i
  simp only [ib, featC_off h (show S.cf.NAs ≠ S.cf.NAs + 2 by omega)]

/-- Under Off, the tensors of qa are the same at both readings. -/
theorem ten_off (h : Off S cell cell') : ten S cell' = ten S cell := by
  funext X lam f i
  simp only [ten, featC_off h (show S.cf.NAs + 3 ≠ S.cf.NAs + 2 by omega)]

omit [CommRing R] in
/-- Under Off, the high parts of the first remainder are the same at both readings. -/
theorem rh_off (h : Off S cell cell') : rh S cell' = rh S cell := by
  funext lam f i
  simp only [rh, featC_off h (show S.cf.NAs + 1 ≠ S.cf.NAs + 2 by omega)]

omit [CommRing R] in
/-- Under Off, the high parts of the second remainder are the same at both readings. -/
theorem rhp_off (h : Off S cell cell') : rhp S cell' = rhp S cell := by
  funext lam f i
  simp only [rhp, featC_off h (show S.cf.NAs + 1 ≠ S.cf.NAs + 2 by omega)]

/-- Under Off, the scores are the same at both readings. -/
theorem score_off (h : Off S cell cell') : score S cell' = score S cell := by
  funext lam hd g ti tj
  simp only [score, ten_off h]

/-- Under Off, A.ssAt is the same at both readings. -/
theorem ssAt_off (h : Off S cell cell') : ssAt S cell' = ssAt S cell := by
  funext isD lam a κ
  simp only [ssAt, score_off h]

/-- Under Off, A.gapAt is the same at both readings. -/
theorem gapAt_off (h : Off S cell cell') : gapAt S cell' = gapAt S cell := by
  funext sh isD lam a κ
  simp only [gapAt, mx_off h]

omit [CommRing R] in
/-- Under Nums and Off: for a plane x below 5, lam below Lam, a below HA and a place π below 2^nD
(on the diagonal tiles) or 2^nM (below them), A.asC is the same at both readings. -/
theorem asC_off (N : Nums S) (h : Off S cell cell') {x lam a π : ℕ} {isD : Bool} (hx : x < 5)
    (hl : lam < S.Lam) (ha : a < S.HA) (hπ : π < 2 ^ (if isD = true then S.nD else S.nM)) :
    asC S cell' x lam a isD π = asC S cell x lam a isD π := by
  have hn : (if isD = true then 5 * S.Lam * S.HA * 2 ^ S.nM else 0) +
      ((x * S.Lam + lam) * S.HA + a) * 2 ^ (if isD = true then S.nD else S.nM) + π <
      5 * S.Lam * S.HA * (2 ^ S.nM + 2 ^ S.nD) := by
    have := radix (radix (radix hx hl) ha) hπ
    rw [Nat.mul_add]
    cases isD
    · simp only [Bool.false_eq_true, if_false] at this ⊢
      omega
    · simp only [if_true] at this ⊢
      omega
  exact h _ (N.as _ hn)

/-- Under Nums and Off, for lam below Lam, a below HA and a place π below 2^nD (on the diagonal
tiles) or 2^nM (below them), the softmax weight is the same at both readings. -/
theorem wt_off (N : Nums S) (h : Off S cell cell') {lam a π : ℕ} {isD : Bool}
    (hl : lam < S.Lam) (ha : a < S.HA) (hπ : π < 2 ^ (if isD = true then S.nD else S.nM)) :
    wt S cell' lam a isD π = wt S cell lam a isD π := by
  unfold wt
  rw [asC_off N h (by norm_num) hl ha hπ, asC_off N h (by norm_num) hl ha hπ]

/-- Under Nums and Off, for lam below Lam, a below HA, g below G and a token i below T, the
accumulator is the same at both readings. -/
theorem acc_off (N : Nums S) (h : Off S cell cell') {lam a g i : ℕ} (n : ℕ) (hl : lam < S.Lam)
    (ha : a < S.HA) (hg : g < S.G) (hi : i < S.T) :
    acc S cell' lam a g i n = acc S cell lam a g i n := by
  have hiB : i % S.B < S.B := Nat.mod_lt _ N.B
  have hiT : i / S.B < S.nT := by
    apply Nat.div_lt_of_lt_mul
    rw [Nat.mul_comm, ← N.TB]
    exact hi
  unfold acc
  rw [ten_off h]
  congr 1
  · refine sumN_congr fun P hP => sumN_congr fun sg hsg => ?_
    by_cases hc : (S.cover P sg).1 = i / S.B
    · rw [if_pos hc, if_pos hc]
      refine sumN_congr fun j hj => ?_
      rw [wt_off N h hl ha]
      show codeM S g P sg (i % S.B) j < 2 ^ S.nM
      rw [← N.nM]
      exact radix (radix (radix (radix hg hP) (by omega)) hiB) hj
    · rw [if_neg hc, if_neg hc]
  · refine sumN_congr fun j hj => ?_
    rw [wt_off N h hl ha]
    show codeD S g (i / S.B) (i % S.B) j < 2 ^ S.nD
    rw [← N.nD]
    exact radix (radix (radix hg hiT) hiB) hj

/-- Under Nums and Off, for lam below Lam, a below HA and κ below the size of a piece of segment
kind s, key number κ of that piece is the same at both readings. -/
theorem segKey_off (N : Nums S) (h : Off S cell cell') (sh : ℕ) (s : Attention.Seg)
    {lam a κ : ℕ} (hl : lam < S.Lam) (ha : a < S.HA) (hκ : κ < 2 ^ Attention.segBits S.cf s) :
    segKey S cell' sh s lam a κ = segKey S cell sh s lam a κ := by
  have hM : Attention.segBits S.cf .rm = S.nM := N.eM.symm
  have hD : Attention.segBits S.cf .rd = S.nD := N.eD.symm
  cases s with
  | rm =>
    have hπ : κ < 2 ^ (if false = true then S.nD else S.nM) := by rw [hM] at hκ; exact hκ
    show asC S cell' 0 lam a false κ + 128 + _ * (asC S cell' 1 lam a false κ + 128) +
      _ * asC S cell' 2 lam a false κ = _
    rw [asC_off N h (by norm_num) hl ha hπ, asC_off N h (by norm_num) hl ha hπ,
      asC_off N h (by norm_num) hl ha hπ]
    rfl
  | rd =>
    have hπ : κ < 2 ^ (if true = true then S.nD else S.nM) := by rw [hD] at hκ; exact hκ
    show asC S cell' 0 lam a true κ + 128 + _ * (asC S cell' 1 lam a true κ + 128) +
      _ * asC S cell' 2 lam a true κ = _
    rw [asC_off N h (by norm_num) hl ha hπ, asC_off N h (by norm_num) hl ha hπ,
      asC_off N h (by norm_num) hl ha hπ]
    rfl
  | fm =>
    have hπ : κ < 2 ^ (if false = true then S.nD else S.nM) := by
      rw [show Attention.segBits S.cf .fm = S.nM from N.eM.symm] at hκ; exact hκ
    show gapAt S cell' sh false lam a κ - ssAt S cell' false lam a κ -
      (asC S cell' 0 lam a false κ + 128) - 256 * (asC S cell' 1 lam a false κ + 128) +
      _ * asC S cell' 2 lam a false κ + _ * wt S cell' lam a false κ = _
    rw [asC_off N h (by norm_num) hl ha hπ, asC_off N h (by norm_num) hl ha hπ,
      asC_off N h (by norm_num) hl ha hπ, wt_off N h hl ha hπ, gapAt_off h, ssAt_off h]
    rfl
  | fd =>
    have hπ : κ < 2 ^ (if true = true then S.nD else S.nM) := by
      rw [show Attention.segBits S.cf .fd = S.nD from N.eD.symm] at hκ; exact hκ
    show gapAt S cell' sh true lam a κ - ssAt S cell' true lam a κ -
      (asC S cell' 0 lam a true κ + 128) - 256 * (asC S cell' 1 lam a true κ + 128) +
      _ * asC S cell' 2 lam a true κ + _ * wt S cell' lam a true κ = _
    rw [asC_off N h (by norm_num) hl ha hπ, asC_off N h (by norm_num) hl ha hπ,
      asC_off N h (by norm_num) hl ha hπ, wt_off N h hl ha hπ, gapAt_off h, ssAt_off h]
    rfl
  | wl =>
    simp only [segKey, den_off h, ten_off h, rh_off h, rhp_off h,
      acc_off N h _ hl ha (Nat.mod_lt _ N.G) (Nat.mod_lt _ N.T)]
  | wh => simp only [segKey, rh_off h, rhp_off h]
  | ix => simp only [segKey, ib_off h]

/-- A member of offsL l off has the fields seg, lam, a and b of some member of l. -/
theorem mem_offsL {q : Attention.Piece} : ∀ {l : List Attention.Piece} {off : ℕ},
    q ∈ offsL l off → ∃ p ∈ l, q.seg = p.seg ∧ q.lam = p.lam ∧ q.a = p.a ∧ q.b = p.b
  | [], _, hq => by simp [offsL] at hq
  | p :: l, off, hq => by
    simp only [offsL, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨p, List.mem_cons_self, rfl, rfl, rfl, rfl⟩
    · obtain ⟨p', hp', e⟩ := mem_offsL hq
      exact ⟨p', List.mem_cons_of_mem _ hp', e⟩

/-- Every piece q that placePieces returns has q.lam below 2^ll, q.a below HA and q.b = segBits cf
q.seg. -/
theorem placed_piece {cf : Attention.Cfg} {HA : ℕ} {kind : Attention.Table} {sh : ℕ}
    {segs : List Attention.Seg} {q : Attention.Piece}
    (hq : q ∈ (Attention.placePieces cf HA kind sh segs).1.toList) :
    q.lam < 2 ^ cf.ll ∧ q.a < HA ∧ q.b = Attention.segBits cf q.seg := by
  unfold Attention.placePieces at hq
  rw [layOff_eq] at hq
  obtain ⟨p, hp, e1, e2, e3, e4⟩ := mem_offsL (show q ∈ offsL _ 0 from hq)
  rw [List.mem_mergeSort, List.mem_flatMap] at hp
  obtain ⟨s, -, hp⟩ := hp
  rw [List.mem_flatMap] at hp
  obtain ⟨lam, hlam, hp⟩ := hp
  split_ifs at hp
  · cases hp
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
    rw [e1, e2, e3, e4]
    exact ⟨List.mem_range.1 hlam, List.mem_range.1 ha, rfl⟩

/-- **No key reads a cell of matrix number NAs + 2**, at every shape that shapeHid returns: two
readings of the names that agree outside that matrix give the same key vectors. -/
theorem kvA_off {lid : ℕ} {cf : Attention.Cfg} {fs : Forest.Shape}
    (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) (h : Off S cell cell') (q X : ℕ) :
    kvA S fs cell' q X = kvA S fs cell q X := by
  have N := nums_of_hid hs
  have P := shaped_of_hid hs
  unfold kvA kvSel
  cases e : S.calls[q]? with
  | none => rfl
  | some c =>
    have hc : c ∈ S.calls.toList := by
      rw [Array.mem_toList_iff]
      exact Array.mem_of_getElem? e
    obtain ⟨kind, sh, segs, p1, -⟩ := hid_placed hs hc
    show (match c.pcs.toList.find? fun p => decide (p.off ≤ X ∧ X < p.off + 2 ^ p.b) with
      | some p => if true = true then segKey S cell' c.sh p.seg p.lam p.a (X - p.off) else 0
      | none => if true = true then ((Ends.tauN fs q (Ends.t0N fs q) : ℕ) : R) else 0) =
      (match c.pcs.toList.find? fun p => decide (p.off ≤ X ∧ X < p.off + 2 ^ p.b) with
      | some p => if true = true then segKey S cell c.sh p.seg p.lam p.a (X - p.off) else 0
      | none => if true = true then ((Ends.tauN fs q (Ends.t0N fs q) : ℕ) : R) else 0)
    cases ef : c.pcs.toList.find? fun p => decide (p.off ≤ X ∧ X < p.off + 2 ^ p.b) with
    | none => rfl
    | some p =>
      have hm : p ∈ c.pcs.toList := List.mem_of_find?_eq_some ef
      have hX := List.find?_some ef
      simp only [decide_eq_true_eq] at hX
      rw [p1] at hm
      obtain ⟨b1, b2, b3⟩ := placed_piece hm
      show (if true = true then segKey S cell' c.sh p.seg p.lam p.a (X - p.off) else 0) =
        if true = true then segKey S cell c.sh p.seg p.lam p.a (X - p.off) else 0
      rw [segKey_off N h c.sh p.seg (by rw [P.Lam]; exact b1) (by rw [P.HA]; exact b2)
        (by rw [P.cfg, ← b3]; omega)]

end Att

/-! ## The chosen rows, the matrix bA, the law -/

section Law
variable {K : Type} [Field K] [DecidableEq K]

/-- Padding places and chosen rows at attention: a padding place (padA) has the call's padding row;
every other place has the first row of the call's table, below 2^(k_c), that holds its key (A.kvA at
cell), and 0 if no row does. -/
def hitsA (S : Attention.Shape) (fs : Forest.Shape) (cell : NameA → K) : Hits :=
  hitsOf fs (tabOf K fs) (Ends.A.kvA S fs cell) (padA S)

/-- The matrix bA of a reading cell, by row and column, with values 0 and 1: the bits of the counts
at hitsA S fs cell, in a matrix of 2^lmb rows (plane). -/
def bA (S : Attention.Shape) (fs : Forest.Shape) (cell : NameA → K) (r col : ℕ) : ℕ :=
  plane fs S.cf.lmb (hitsA S fs cell) r col

/-- The reading cell holds, at every row below 2^lmb and column below NC 2^(kT + 5 - lmb) of matrix
number NAs + 2, the matrix bA of cell itself. Nothing is asked outside these rows and columns, where
bA is 0 (plane_outside). -/
def LaidBA (S : Attention.Shape) (fs : Forest.Shape) (cell : NameA → K) : Prop :=
  ∀ r < 2 ^ S.cf.lmb, ∀ c < fs.NC * 2 ^ (fs.kT + 5 - S.cf.lmb),
    cell ⟨S.cf.NAs + 2, r, c⟩ = (bA S fs cell r c : K)

/-- The reading cell with bA S fs cell laid over matrix number NAs + 2. -/
def withBA (S : Attention.Shape) (fs : Forest.Shape) (cell : NameA → K) : NameA → K := fun n =>
  if n.M = S.cf.NAs + 2 then (bA S fs cell n.r n.c : K) else cell n

omit [DecidableEq K] in
/-- For q below fs.calls.size and below S.calls.size: at a padding place X of call q, A.kvA holds
the value of the call's padding row, tabOf K fs q (FoNums.t0Of fs q). S and fs are any two values.
-/
theorem kvA_pad (S : Attention.Shape) (fs : Forest.Shape) (cell : NameA → K) {q X : ℕ}
    (hq : q < fs.calls.size) (hS : q < S.calls.size) (hp : padA S q X = true) :
    Ends.A.kvA S fs cell q X = tabOf K fs q (FoNums.t0Of fs q) := by
  have e : S.calls[q]? = some S.calls[q] := Array.getElem?_eq_getElem hS
  unfold padA at hp
  rw [e] at hp
  have hn := Option.isNone_iff_eq_none.1 hp
  unfold Ends.A.kvA Ends.A.kvSel
  rw [e]
  simp only [hn]
  rw [tabOf_eq K fs hq]
  rfl

/-- For u below 2^d with u % 2^cK below fs.NC, and j below 32: A.placeBA S fs u j is the cell of
matrix number NAs + 2 at the row and column FoNums.cellRC fs lmb (u / 2^cK, u % 2^cK, j). -/
theorem placeBA_cellRC (S : Attention.Shape) (fs : Forest.Shape) {u j : ℕ}
    (hc : u % 2 ^ fs.cK < fs.NC) (hj : j < 32) (hu : u < 2 ^ fs.d) :
    Ends.A.placeBA S fs u j = some ⟨S.cf.NAs + 2,
      (FoNums.cellRC fs S.cf.lmb (u / 2 ^ fs.cK, u % 2 ^ fs.cK, j)).1,
      (FoNums.cellRC fs S.cf.lmb (u / 2 ^ fs.cK, u % 2 ^ fs.cK, j)).2⟩ := by
  unfold Ends.A.placeBA
  exact if_pos ⟨hc, hj, hu⟩

/-- If 5 ≤ lmb ≤ kT + 5 and LaidBA S fs cell, then for u below 2^d and j below 32, A.bitsA S fs cell
at u * 32 + j is plane fs lmb (hitsA S fs cell) at the row and column FoNums.cellRC fs lmb (u /
2^cK, u % 2^cK, j), cast into K. For u % 2^cK from fs.NC on both are 0. -/
theorem bitsA_plane (S : Attention.Shape) (fs : Forest.Shape) (cell : NameA → K)
    (h5 : 5 ≤ S.cf.lmb) (hlm : S.cf.lmb ≤ fs.kT + 5) (hb : LaidBA S fs cell) {u j : ℕ}
    (hu : u < 2 ^ fs.d) (hj : j < 32) :
    Ends.A.bitsA S fs cell (u * 32 + j) =
      (plane fs S.cf.lmb (hitsA S fs cell)
        (FoNums.cellRC fs S.cf.lmb (u / 2 ^ fs.cK, u % 2 ^ fs.cK, j)).1
        (FoNums.cellRC fs S.cf.lmb (u / 2 ^ fs.cK, u % 2 ^ fs.cK, j)).2 : K) := by
  have e1 : (u * 32 + j) / 32 = u := by omega
  have e2 : (u * 32 + j) % 32 = j := by omega
  have ht : u / 2 ^ fs.cK < 2 ^ fs.kT := by
    apply Nat.div_lt_of_lt_mul
    rw [← pow_add, Nat.add_comm]
    exact hu
  unfold Ends.A.bitsA
  rw [e1, e2]
  by_cases hc : u % 2 ^ fs.cK < fs.NC
  · rw [placeBA_cellRC S fs hc hj hu]
    exact hb _ (cellRC_in _ h5 hlm ht hc hj).1 _ (cellRC_in _ h5 hlm ht hc hj).2
  · have hn : Ends.A.placeBA S fs u j = none := by
      unfold Ends.A.placeBA
      exact if_neg fun k => hc k.1
    have hf : bit fs (hitsA S fs cell) (u / 2 ^ fs.cK) (u % 2 ^ fs.cK) j = false := by
      simp [bit, hc]
    rw [hn, plane_cellRC _ _ _ h5 hlm ht hj, hf]
    simp

variable {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape}

/-- Where shapeHid returns (S, fs): if for every call c below fs.NC every key A.kvA S fs cell c i, i
below 2^(n_c), is a row below 2^(k_c) of tabOf K fs c, then Fits holds of fs, these tables, these
key vectors and hitsA S fs cell. -/
theorem fitsA (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) (cell : NameA → K)
    (hin : ∀ c < fs.NC, InTable (FoNums.nOf fs c) (FoNums.kOf fs c) (Ends.A.kvA S fs cell c)
      (tabOf K fs c)) :
    Fits fs (tabOf K fs) (Ends.A.kvA S fs cell) (hitsA S fs cell) := by
  obtain ⟨s1, s2⟩ := size_A hs
  exact fits_hitsOf fs _ _ _ (ok_A hs) hin
    (fun c hc i _ hp => kvA_pad S fs cell (by omega) (by omega) hp) (pubFits_A hs)

/-- **The relation after the challenge (MidP) at attention, at one reading of the cells.** Where
shapeHid returns (S, fs): if for every call c below fs.NC every key A.kvA S fs cell c i, i below
2^(n_c), is a row below 2^(k_c) of tabOf K fs c, and cell holds its own bA at matrix number NAs + 2
(LaidBA), then at all elements θ and al of K, MidP holds at fs.v, fs.d, 5, 32 of the joint key
vector A.keyA S fs cell θ, the joint table A.tabA fs θ, the list FoNums.pads fs and the bits A.bitsA
S fs cell (u * 32 + j). θ is the element by whose multiples the joint vectors keep the calls apart.
MidP has three clauses. Every bit b at u below 2^d and j below 32 has b (b - 1) = 0. The bits,
weighted by 2^j, add up in K to 2^v less the number of padding keys in the list. The product of (al
- key) over the 2^v keys is padFac times the product over j below 32 of (the product over u below
2^d of (1 + bit (al - 1 - the joint table's value at row u)))^(2^j), where padFac is the product
over the list's entries (row, number) of (al - the joint table's value at that row)^number. -/
theorem lawA (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) (cell : NameA → K)
    (hin : ∀ c < fs.NC, InTable (FoNums.nOf fs c) (FoNums.kOf fs c) (Ends.A.kvA S fs cell c)
      (tabOf K fs c))
    (hb : LaidBA S fs cell) (θ al : K) :
    MidP fs.v fs.d 5 32 (Ends.A.keyA S fs cell θ) (Ends.A.tabA fs θ) (FoNums.pads fs)
      (fun u j => Ends.A.bitsA S fs cell (u * 32 + j)) al := by
  obtain ⟨s1, s2⟩ := size_A hs
  obtain ⟨h5, hlm⟩ := lmb_A hs
  exact law_bits fs (Ends.A.kvA S fs cell) (padA S) (ok_A hs) hin
    (fun c hc i _ hp => kvA_pad S fs cell (by omega) (by omega) hp) (pubFits_A hs) h5 hlm _
    (fun u hu j hj => bitsA_plane S fs cell h5 hlm hb hu hj) θ al

/-- Where shapeHid returns (S, fs): if for every call c below fs.NC every key A.kvA S fs cell c i, i
below 2^(n_c), is a row below 2^(k_c) of tabOf K fs c, then the cells of bA S fs cell in the rows
below 2^lmb and the columns below NC 2^(kT + 5 - lmb), weighted by 2^(r % 32), and fs.padding add up
to 2^v, as natural numbers. -/
theorem sum_bA (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) (cell : NameA → K)
    (hin : ∀ c < fs.NC, InTable (FoNums.nOf fs c) (FoNums.kOf fs c) (Ends.A.kvA S fs cell c)
      (tabOf K fs c)) :
    ∑ col ∈ range (fs.NC * 2 ^ (fs.kT + 5 - S.cf.lmb)), ∑ r ∈ range (2 ^ S.cf.lmb),
        2 ^ (r % 32) * bA S fs cell r col + fs.padding = 2 ^ fs.v := by
  obtain ⟨h5, hlm⟩ := lmb_A hs
  exact sum_plane_all fs _ _ _ (ok_A hs) (fitsA hs cell hin) h5 hlm

/-! ## Laying bA over a reading of the names -/

/-- Where shapeHid returns (S, fs), laying bA over matrix number NAs + 2 moves no key: A.kvA at
withBA S fs cell is A.kvA at cell, at every call number and every place. -/
theorem kvA_withBA (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) (cell : NameA → K) :
    Ends.A.kvA S fs (withBA S fs cell) = Ends.A.kvA S fs cell := by
  funext q X
  exact Att.kvA_off hs (fun n hn => if_neg hn) q X

/-- Where shapeHid returns (S, fs), withBA S fs cell meets LaidBA, for every reading cell. -/
theorem withBA_laid (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) (cell : NameA → K) :
    LaidBA S fs (withBA S fs cell) := by
  intro r _ c _
  unfold bA hitsA
  rw [kvA_withBA hs cell]
  exact if_pos rfl

/-- Where shapeHid returns (S, fs): if every key of every call below fs.NC at the reading cell is a
row of the call's table, the same holds at the reading withBA S fs cell. -/
theorem inTable_withBA (hs : Attention.shapeHid lid cf = Except.ok (S, fs)) (cell : NameA → K)
    (hin : ∀ c < fs.NC, InTable (FoNums.nOf fs c) (FoNums.kOf fs c) (Ends.A.kvA S fs cell c)
      (tabOf K fs c)) :
    ∀ c < fs.NC, InTable (FoNums.nOf fs c) (FoNums.kOf fs c)
      (Ends.A.kvA S fs (withBA S fs cell) c) (tabOf K fs c) := by
  rw [kvA_withBA hs cell]
  exact hin

end Law

end OnBytes.HonestTrace


#print axioms OnBytes.HonestTrace.Att.ov_zero
#print axioms OnBytes.HonestTrace.Att.ov_step
#print axioms OnBytes.HonestTrace.Att.card_from
#print axioms OnBytes.HonestTrace.Att.getD_modify_add
#print axioms OnBytes.HonestTrace.Att.pubLoop_succ
#print axioms OnBytes.HonestTrace.Att.pubLoop_getD
#print axioms OnBytes.HonestTrace.Att.pubRun_getD
#print axioms OnBytes.HonestTrace.Att.fold_getD
#print axioms OnBytes.HonestTrace.Att.share_off
#print axioms OnBytes.HonestTrace.Att.hid_fold
#print axioms OnBytes.HonestTrace.Att.mapM_mem
#print axioms OnBytes.HonestTrace.Att.layCall_laid
#print axioms OnBytes.HonestTrace.Att.hid_placed
#print axioms OnBytes.HonestTrace.Att.find_offsL
#print axioms OnBytes.HonestTrace.padA_iff
#print axioms OnBytes.HonestTrace.ok_A
#print axioms OnBytes.HonestTrace.lmb_A
#print axioms OnBytes.HonestTrace.size_A
#print axioms OnBytes.HonestTrace.pubFits_A
#print axioms OnBytes.HonestTrace.Att.radix
#print axioms OnBytes.HonestTrace.Att.shape_more
#print axioms OnBytes.HonestTrace.Att.as_inside
#print axioms OnBytes.HonestTrace.Att.nums_of_hid
#print axioms OnBytes.HonestTrace.Att.sumN_congr
#print axioms OnBytes.HonestTrace.Att.featC_off
#print axioms OnBytes.HonestTrace.Att.mx_off
#print axioms OnBytes.HonestTrace.Att.den_off
#print axioms OnBytes.HonestTrace.Att.ib_off
#print axioms OnBytes.HonestTrace.Att.ten_off
#print axioms OnBytes.HonestTrace.Att.rh_off
#print axioms OnBytes.HonestTrace.Att.rhp_off
#print axioms OnBytes.HonestTrace.Att.score_off
#print axioms OnBytes.HonestTrace.Att.ssAt_off
#print axioms OnBytes.HonestTrace.Att.gapAt_off
#print axioms OnBytes.HonestTrace.Att.asC_off
#print axioms OnBytes.HonestTrace.Att.wt_off
#print axioms OnBytes.HonestTrace.Att.acc_off
#print axioms OnBytes.HonestTrace.Att.segKey_off
#print axioms OnBytes.HonestTrace.Att.mem_offsL
#print axioms OnBytes.HonestTrace.Att.placed_piece
#print axioms OnBytes.HonestTrace.Att.kvA_off
#print axioms OnBytes.HonestTrace.kvA_pad
#print axioms OnBytes.HonestTrace.placeBA_cellRC
#print axioms OnBytes.HonestTrace.bitsA_plane
#print axioms OnBytes.HonestTrace.fitsA
#print axioms OnBytes.HonestTrace.lawA
#print axioms OnBytes.HonestTrace.sum_bA
#print axioms OnBytes.HonestTrace.kvA_withBA
#print axioms OnBytes.HonestTrace.withBA_laid
#print axioms OnBytes.HonestTrace.inTable_withBA
