-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsLayers.lean

The multiplicities of the lookup of the calls of a layers' sub-proof (one group of layers): the
matrix b as a function bG of a reading of the group's cells, and the relation after the challenge
(Cb.Lkp.MidP) at it. That laying bG over b moves no key is KeysSkipB: a premise here, a theorem in
Johnson/HonestTrace/CountsLayersSkip.lean.

This file builds on OnBytes/Tie/Pv/Lookup/Ends/G.lean: the key vectors G.kvG, the joint vectors
G.keyG and G.tabG, the places G.placeG of the bits and their reading G.bitsG, as terms over a layout
P.y of the Lean verifier under OnBytes/Model/ and a reading cell : G.NameG → K of the cells. No size
is fixed but what S (below) fixes; the number of groups is arbitrary.

Notation. NC, kT, cK, dT, rK, NT are fields of the lookup's shape P.y.fo : Forest.Shape; d = kT +
cK; v = dT + rK; n_c = FoNums.nOf P.y.fo c and k_c = FoNums.kOf P.y.fo c; a place of call c is an
index below 2^(n_c); the matrix b has 2^lmb rows. See the head of Johnson/HonestTrace/Counts.lean.

Main definitions:
* "padG": the padding places of a call: G.kvOf's own two cases.
* "hitsG", "bG": hitsOf and plane (Johnson/HonestTrace/Counts.lean) at the layout's lookup shape
  P.y.fo, the tables tabOf, the key vectors G.kvG P g cell, the padding places padG and lm :=
  P.y.h.lmb.
* "LaidB P g cell": the cells of matrix number G.iB P.y are bG P g cell, cast into K, at every row
  below 2^lmb and column below NC 2^(kT + 5 - lmb).
* "withBG": cell with bG laid over matrix number G.iB P.y. "KeysSkipB": for every call q below NC
  and every place X below 2^(n_q), G.kvG reads the same value at withBG P g cell and at cell.

Main theorems. "hy" is: Layer.layout h pc returns the layout. "S" is: Road.Switches h
(Johnson/Road/FormsKeysFits.lean: routed experts, both clamps, five limbs, seven digit forms).
* "pubFits_G": under hy and S the public numbers of padding keys count padG's places, tree by tree:
  PubFits y.fo (padG y).
* "lawG": under hy and S, if for every call c below NC every place of G.kvG P g cell c holds the
  value of a row below 2^(k_c) of the call's table, and LaidB P g cell holds, then for all θ and al
  Cb.Lkp.MidP holds at G.keyG P g cell θ, G.tabG P θ, FoNums.pads P.y.fo and the bits G.bitsG P.y
  cell (u * 32 + j). Keys and bits are read at one and the same reading cell.
* "sum_bG": under hy, S and the same premise on the keys, the cells of bG in its 2^lmb rows and NC
  2^(kT + 5 - lmb) columns, weighted by 2^(r % 32), and the number of padding keys add up to 2^v.
* "fitsG": under hy, S and the same premise on the keys, Fits holds of hitsG.
* "kvG_pad": at a padding place of a call below P.y.fo.calls.size, G.kvG holds the value of the
  call's padding row. "placeG_cellRC": for u % 2^cK < NC, j < 32 and u < 2^d, G.placeG y u j is
  matrix number G.iB y at FoNums.cellRC. "ok_of_layout": under hy, FoNums.ok y.fo holds and 5 ≤ lmb
  ≤ kT + 5.
* "place_used_col", "call_facts": for segments of lengths below 2^41 the placing rule's mark of a
  column is the mark of the first segment that lists the column, 0 if none does; so under hy and S
  for the calls of the layout.
* "withBG_laid", "inTable_withBG": under KeysSkipB P g cell, LaidB holds of withBG P g cell, and the
  premise on the keys passes from cell to withBG P g cell.

Limits. S enters through the bound 2^41 on the segments' lengths and through the facts on the
layout's numbers, which the library has for shapes with routed experts
(Johnson/Road/FormsKeysLaid.lean). That two segments of a placed call share no column is taken from
Johnson/Road/HeadCallsLaid.lean. The premise on the keys is assumed, not proved. KeysSkipB is
assumed in this file; Johnson/HonestTrace/CountsLayersSkip.lean proves it under public premises. It
is stated for the places below 2^(n_q) alone: G.ten has no bound on a tensor's instance, and past
its family's last matrix G.cellAt steps into the next number of the list, which after ar is b. That
G.kvG, G.keyG and G.tabG are what a verifier checks is no theorem of this file, and by its own head
none of Ends/G.lean. bG depends on K through firstRow; hitsOf_map says that an injective map applied
to the tables' rows and to the keys does not move hitsOf; that G.kvG and tabOf commute with a map of
fields is not shown here. Road.Switches h is a premise on the shape's switches and no test of the
verifier: the verifier takes shapes that do not meet it, and of these the theorems under S say
nothing. These are specifications, not programs to run.

Not claimed: that a prover's committed cells meet LaidB; that MidP makes any claim of the protocol's
lookup argument hold; that hy, S and the premise on the keys hold of any parameter file or request;
completeness of the protocol.

-/
import Johnson.HonestTrace.CountsLaw
import Johnson.HonestTrace.CountsRect
import OnBytes.Tie.Pv.Lookup.Ends.G
import OnBytes.Tie.Pv.Lookup.Port.FoShape
import Johnson.Road.FormsKeysPub
import Johnson.Road.FormsKeysCap
import Johnson.Road.HeadCallsLaid

set_option autoImplicit false

namespace OnBytes.HonestTrace

open Finset
open OnBytes.Model OnBytes.Ends
open OnBytes.Model.Layer (Lay layout layoutLook)
open OnBytes.Road (Switches markOf)

/-! ## The padding places, the chosen rows and the matrix b of a group of layers -/

/-- Place X of call q's key vector is a padding place: G.kvOf's own two cases. For a number q that
is no call's the default call has no segment, so every place is a padding place. -/
def padG (y : Lay) (q X : ℕ) : Bool :=
  match G.colG y q (X / y.T % 2 ^ (y.calls.getD q default).lJ) with
  | some (s, _) => s.moe && (X / y.T / 2 ^ (y.calls.getD q default).lJ) % 2 == 0
  | none => true

section Defs
variable {K : Type} [Field K] [DecidableEq K]

/-- The padding places padG and the chosen rows of the calls' places: hitsOf at the layout's lookup
shape, the tables tabOf and the key vectors G.kvG P g cell. -/
def hitsG (P : Layer.Pub) (g : ℕ) (cell : G.NameG → K) : Hits :=
  hitsOf P.y.fo (tabOf K P.y.fo) (G.kvG P g cell) (padG P.y)

/-- The planes' matrix of group g as a function of row and column, with values 0 and 1: plane at
hitsG P g cell and lm := P.y.h.lmb. -/
def bG (P : Layer.Pub) (g : ℕ) (cell : G.NameG → K) (r col : ℕ) : ℕ :=
  plane P.y.fo P.y.h.lmb (hitsG P g cell) r col

/-- cell, with bG P g cell laid over matrix number G.iB P.y. -/
def withBG (P : Layer.Pub) (g : ℕ) (cell : G.NameG → K) : G.NameG → K
  | .cell m r c => if m = G.iB P.y then (bG P g cell r c : K) else cell (.cell m r c)
  | .w r c => cell (.w r c)

/-- For every call q below NC and every place X below 2^(n_q), G.kvG reads the same value at
withBG P g cell and at cell. -/
def KeysSkipB (P : Layer.Pub) (g : ℕ) (cell : G.NameG → K) : Prop :=
  ∀ q < P.y.fo.NC, ∀ X < 2 ^ FoNums.nOf P.y.fo q,
    G.kvG P g (withBG P g cell) q X = G.kvG P g cell q X

end Defs

/-! ## Padding places hold the padding row's value; the place of a bit -/

/-- For q below P.y.fo.calls.size: at a place X with padG P.y q X = true, G.kvG P g cell q X is the
value of the call's padding row. -/
theorem kvG_pad {K : Type} [Field K] (P : Layer.Pub) (g : ℕ) (cell : G.NameG → K) {q X : ℕ}
    (hq : q < P.y.fo.calls.size) (hp : padG P.y q X = true) :
    G.kvG P g cell q X = tabOf K P.y.fo q (FoNums.t0Of P.y.fo q) := by
  rw [tabOf_eq K _ hq]
  unfold padG at hp
  simp only [G.kvG, G.kvOf]
  split
  · rename_i s x hc
    rw [hc] at hp
    simp only at hp
    rw [if_pos hp]
    rfl
  · rfl

/-- For u % 2^cK < NC, j < 32 and u < 2^d: G.placeG y u j is the cell of matrix number G.iB y at
the row and column FoNums.cellRC y.fo y.h.lmb (u / 2^cK, u % 2^cK, j). -/
theorem placeG_cellRC (y : Lay) {u j : ℕ} (hc : u % 2 ^ y.fo.cK < y.fo.NC) (hj : j < 32)
    (hu : u < 2 ^ y.fo.d) :
    G.placeG y u j = some (.cell (G.iB y)
      (FoNums.cellRC y.fo y.h.lmb (u / 2 ^ y.fo.cK, u % 2 ^ y.fo.cK, j)).1
      (FoNums.cellRC y.fo y.h.lmb (u / 2 ^ y.fo.cK, u % 2 ^ y.fo.cK, j)).2) := by
  unfold G.placeG
  rw [if_pos ⟨hc, hj, hu⟩]
  rfl

/-! ## What the layout's second half gives -/

/-- If Layer.layoutLook y returns y', then FoNums.ok y'.fo holds and 5 ≤ lmb ≤ kT + 5 at y'. -/
theorem look_ok {y y' : Lay} (hy : layoutLook y = .ok y') :
    FoNums.ok y'.fo = true ∧ 5 ≤ y'.h.lmb ∧ y'.h.lmb ≤ y'.fo.kT + 5 := by
  unfold layoutLook at hy
  obtain ⟨u, hu, hy⟩ := Road.ok_of_bind hy
  obtain ⟨fo, hfo, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, hy⟩ := Road.ok_of_refuse hy
  obtain ⟨kbm, hk, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, -, hy⟩ := Road.ok_of_bind hy
  obtain ⟨pub, hpub, hy⟩ := Road.ok_of_bind hy
  obtain ⟨a, ha, hy⟩ := Road.ok_of_bind hy
  obtain ⟨-, hy⟩ := Road.ok_of_refuse hy
  cases hy
  refine ⟨Cb.Fo.shape_ok hfo ha, ?_⟩
  unfold Forest.planeCols at hk
  split at hk
  · cases hk
  · rename_i hn
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt] at hn
    exact hn

/-- If Layer.layout h pc returns y, then FoNums.ok y.fo holds and 5 ≤ y.h.lmb ≤ y.fo.kT + 5. (The
two bounds are also Fo.Pub2.layout_lm, OnBytes/Tie/Pv/Lookup/Ends/FoLookPubG.lean.) -/
theorem ok_of_layout {h : Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) :
    FoNums.ok y.fo = true ∧ 5 ≤ y.h.lmb ∧ y.h.lmb ≤ y.fo.kT + 5 := by
  unfold layout at hy
  obtain ⟨y0, -, h1⟩ := Road.ok_of_bind hy
  exact look_ok h1

/-! ## The marks of a placed call's columns -/

/-- A member of an array of numbers stands at an index below the size. -/
theorem getD_of_mem {a : Array ℕ} {j : ℕ} (h : j ∈ a.toList) :
    ∃ x, x < a.size ∧ a.getD x 0 = j := by
  obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 (Array.mem_def.2 h)
  exact ⟨i, hi, by simp [Array.getD, hi, e]⟩

/-- For segments of lengths below 2^(topBit + 1) and a column j below the placed call's J: the mark
used[j] is the mark of the first segment that lists j, and 0 if no segment lists j. -/
theorem place_used_col (name kind : String) (asks : List SegAsk) (fl : ℕ)
    (hlen : ∀ a ∈ asks, a.2.1 < 2 ^ (topBit + 1)) {j : ℕ}
    (hj : j < (place name kind asks fl).J) :
    (place name kind asks fl).used.getD j 0 =
      match (place name kind asks fl).segs.findSome? fun s =>
        (s.pos.findIdx? (· == j)).map fun x => (s, x) with
      | some (s, _) => markOf s
      | none => 0 := by
  have hu : (place name kind asks fl).used = (place name kind asks fl).segs.foldl markUsed
      (Array.replicate (place name kind asks fl).J 0) := rfl
  have hsz : j < (Array.replicate (place name kind asks fl).J 0).size := by
    rw [Array.size_replicate]
    exact hj
  rw [hu]
  split
  · rename_i s x hf
    obtain ⟨s0, hs, h0⟩ := List.exists_of_findSome?_eq_some hf
    cases hx0 : s0.pos.findIdx? (· == j) with
    | none =>
      rw [hx0] at h0
      cases h0
    | some x0 =>
      rw [hx0] at h0
      have e : (s0, x0) = (s, x) := Option.some.inj h0
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      obtain ⟨hi, hp0, _⟩ := Array.findIdx?_eq_some_iff_getElem.1 hx0
      have hmem : j ∈ s0.pos.toList := by
        have e1 : s0.pos[x0] = j := by simpa using hp0
        rw [← e1]
        exact Array.mem_def.1 (Array.getElem_mem hi)
      have hsame : ∀ s' ∈ (place name kind asks fl).segs, j ∈ s'.pos.toList →
          markOf s' = markOf s0 := by
        intro s' hs' hj'
        rw [Road.Hd.place_segs_eq] at hs hs'
        obtain ⟨z, hz, hzs⟩ := List.mem_map.mp hs
        obtain ⟨z', hz', hzs'⟩ := List.mem_map.mp hs'
        rw [← hzs] at hmem
        rw [← hzs'] at hj'
        obtain ⟨x1, hx1, e1⟩ := getD_of_mem hmem
        obtain ⟨x2, hx2, e2⟩ := getD_of_mem hj'
        obtain ⟨_, r1⟩ := Road.Hd.segAt_rising asks hlen z hz
        obtain ⟨_, r2⟩ := Road.Hd.segAt_rising asks hlen z' hz'
        have q1 := r1.inQ x1 hx1
        have q2 := r2.inQ x2 hx2
        rw [e1] at q1
        rw [e2] at q2
        have hidx : z.2 = z'.2 := by
          by_contra hne
          exact Road.Hd.inPiece_apart (Road.Hd.ranged_piecesBelow _ _ 0) hne q1 q2
        have m1 := (Road.mem_zipIdx_getD (fun a : SegAsk => if a.2.2 = true then 1 else 0)
          asks 0 z.1 z.2 hz).2.2
        have m2 := (Road.mem_zipIdx_getD (fun a : SegAsk => if a.2.2 = true then 1 else 0)
          asks 0 z'.1 z'.2 hz').2.2
        rw [hidx] at m1
        have m3 := m1.symm.trans m2
        rw [← hzs, ← hzs']
        show (if z'.1.2.2 = true then 2 else 1) = if z.1.2.2 = true then 2 else 1
        simp only at m3
        cases ha : z.1.2.2 <;> cases hb : z'.1.2.2 <;> simp [ha, hb] at m3 ⊢
      exact (Road.used_get (markOf s0) j _ _ hsz hsame).1 ⟨s0, hs, hmem⟩
  · rename_i hf
    have hno : ∀ s ∈ (place name kind asks fl).segs, j ∉ s.pos.toList := by
      intro s hs hjs
      have h1 := List.findSome?_eq_none_iff.1 hf s hs
      have h2 : s.pos.findIdx? (· == j) = none := by simpa using h1
      have h3 := Array.findIdx?_eq_none_iff.1 h2 j (Array.mem_def.2 hjs)
      simp at h3
    rw [(Road.used_get 0 j _ _ hsz (fun s hs hjs => absurd hjs (hno s hs))).2 hno]
    exact Road.Hd.getD_replicate_zero _ _

/-! ## The calls of a layout that the verifier returns -/

/-- Reading an array's list with a default is reading the array with that default. -/
theorem toList_getD {α : Type} [Inhabited α] (a : Array α) (q : ℕ) :
    a.toList.getD q default = a.getD q default := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

/-- If Layer.layout h pc returns y and Switches h holds, then for q below y.calls.size: call q has
2^lJ columns; FoNums.nOf y.fo q = ll + lJ + lt; and for every column j below J the mark used[j] is
the mark of the segment that G.colG y q j finds, 0 if it finds none. -/
theorem call_facts {h : Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (S : Switches h) {q : ℕ} (hq : q < y.calls.size) :
    (y.calls.getD q default).J = 2 ^ (y.calls.getD q default).lJ ∧
    FoNums.nOf y.fo q = y.h.ll + (y.calls.getD q default).lJ + y.h.lt ∧
    ∀ j < (y.calls.getD q default).J, (y.calls.getD q default).used.getD j 0 =
      match G.colG y q j with
      | some (s, _) => markOf s
      | none => 0 := by
  have A := Road.admitted_of_layout hy S.p3
  unfold G.colG
  obtain ⟨cd, hcdef⟩ : ∃ cd, cd = y.calls.getD q default := ⟨_, rfl⟩
  rw [← hcdef]
  have hcq : y.calls[q]? = some cd := by
    rw [hcdef, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hq]
    rfl
  have hn : FoNums.nOf y.fo q = y.h.ll + cd.lJ + y.h.lt := by
    have h2 : y.cl[q]? = some (y.callRecord q cd) := by
      rw [Road.cl_of_layout hy]
      simp [hcq]
    unfold FoNums.nOf
    rw [(Road.fo_of_layout hy).1, h2]
    rfl
  have hcd : cd ∈ y.calls := Array.mem_of_getElem? hcq
  obtain ⟨cl, taken, ht, -, hc⟩ := A.calls
  rw [hc] at hcd
  have hcd' : cd ∈ taken.1.map fun c => place c.1 c.2.1 c.2.2 (h.nmin - h.ll - h.lt) :=
    Array.mem_def.mp hcd
  obtain ⟨c, hcm, hce⟩ := List.mem_map.mp hcd'
  have hlen : ∀ a ∈ c.2.2, a.2.1 < 2 ^ (topBit + 1) := by
    intro a ha
    obtain ⟨q', hq', rfl⟩ := Road.takeCalls_mem _ cl [] [] taken ht c hcm a ha
    obtain ⟨fam, -, f2, -⟩ := Road.segmentList_fam h S q' hq'
    show q'.2.2.1 < _
    rw [f2]
    exact Road.len_lt A fam
  refine ⟨by rw [← hce]; rfl, hn, fun j hj => ?_⟩
  rw [← hce] at hj ⊢
  exact place_used_col _ _ _ _ hlen hj

/-- If Layer.layout h pc returns y and Switches h holds, then for q below y.calls.size and every X
the verifier's rule CallD.padding at layer X / T / J and column X / T % J is padG y q X. -/
theorem padding_padG {h : Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (S : Switches h) {q : ℕ} (hq : q < y.calls.size) (X : ℕ) :
    (y.calls.getD q default).padding (X / y.T / (y.calls.getD q default).J)
      (X / y.T % (y.calls.getD q default).J) = padG y q X := by
  obtain ⟨hJ, -, hU⟩ := call_facts hy S hq
  have hlt : X / y.T % (y.calls.getD q default).J < (y.calls.getD q default).J :=
    Nat.mod_lt _ (by rw [hJ]; positivity)
  unfold CallD.padding padG
  simp only [hU _ hlt]
  rw [hJ]
  cases G.colG y q (X / y.T % 2 ^ (y.calls.getD q default).lJ) with
  | none => rfl
  | some a =>
    obtain ⟨s, x⟩ := a
    show ((markOf s == 0) || (markOf s == 2 &&
      X / y.T / 2 ^ (y.calls.getD q default).lJ % 2 == 0)) =
      (s.moe && X / y.T / 2 ^ (y.calls.getD q default).lJ % 2 == 0)
    unfold markOf
    cases s.moe <;> simp

/-- If Layer.layout h pc returns y and Switches h holds, then for q below y.calls.size: what call q
adds to the count of tree θ (Road.pubOf) is the number of padG's places among the 2^dT places of
the tree, if θ is one of the call's 2^io trees, and 0 otherwise. -/
theorem pubOf_tree {h : Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (S : Switches h) {q : ℕ} (hq : q < y.calls.size) (θ : ℕ) :
    Road.pubOf y (FoNums.fst y.fo q) y.fo.dT (y.calls.getD q default) θ =
      if FoNums.fst y.fo q ≤ θ ∧ θ < FoNums.fst y.fo q + 2 ^ FoNums.io y.fo q then
        ((range (2 ^ y.fo.dT)).filter fun x =>
          padG y q (x + 2 ^ y.fo.dT * (θ - FoNums.fst y.fo q)) = true).card
      else 0 := by
  have A := Road.admitted_of_layout hy S.p3
  have L2 := Road.laid2_of_layout hy
  obtain ⟨hok, -, -⟩ := ok_of_layout hy
  obtain ⟨hJ, hn, -⟩ := call_facts hy S hq
  have hNC : y.fo.NC = y.calls.size :=
    (Road.fo_of_layout hy).2.1.trans (Road.fo_of_layout hy).2.2
  have hn2 : FoNums.nOf y.fo q = FoNums.io y.fo q + y.fo.dT :=
    ((Cb.Fo.ok_parts hok).2.2.1 q (by omega)).2.2.1
  have hla : y.h.la ≤ y.fo.dT := by
    have := (Road.dT_of_layout hy).1
    rw [← A.shape] at this
    exact this
  have hlt := L2.lt_la
  have hMT : 2 ^ (y.fo.dT - y.h.lt) * y.T = 2 ^ y.fo.dT := by
    rw [L2.T, ← pow_add]
    congr 1
    omega
  have hN : y.Lam * (y.calls.getD q default).J =
      2 ^ FoNums.io y.fo q * 2 ^ (y.fo.dT - y.h.lt) := by
    rw [A.laid.Lam, hJ, ← pow_add, ← pow_add]
    congr 1
    omega
  unfold Road.pubOf
  rw [hN]
  by_cases hb : FoNums.fst y.fo q ≤ θ ∧ θ < FoNums.fst y.fo q + 2 ^ FoNums.io y.fo q
  · rw [if_pos hb]
    obtain ⟨Q, hQ⟩ : ∃ Q : ℕ → Bool, ∀ x, Q x = (y.calls.getD q default).padding
        (x / (y.calls.getD q default).J) (x % (y.calls.getD q default).J) := ⟨_, fun _ => rfl⟩
    obtain ⟨t, ht⟩ : ∃ t, t = θ - FoNums.fst y.fo q := ⟨_, rfl⟩
    obtain ⟨M, hM⟩ : ∃ M, M = 2 ^ (y.fo.dT - y.h.lt) := ⟨_, rfl⟩
    obtain ⟨N, hNN⟩ : ∃ N, N = 2 ^ FoNums.io y.fo q := ⟨_, rfl⟩
    rw [← ht, ← hM, ← hNN]
    rw [← hM] at hMT
    have htN : t < N := by omega
    have hL : ((List.range (N * M)).map fun x =>
        if (y.calls.getD q default).padding (x / (y.calls.getD q default).J)
            (x % (y.calls.getD q default).J) = true ∧ FoNums.fst y.fo q + x / M = θ
        then y.T else 0).sum =
        ((List.range (N * M)).map fun x => if Q x = true ∧ x / M = t then y.T else 0).sum := by
      refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
      have e : (FoNums.fst y.fo q + x / M = θ) ↔ (x / M = t) := by omega
      rw [hQ]
      simp only [e]
    have hR : ((range (2 ^ y.fo.dT)).filter fun x =>
        padG y q (x + 2 ^ y.fo.dT * t) = true).card =
        ((range (M * y.T)).filter fun X => Q ((t * (M * y.T) + X) / y.T) = true).card := by
      rw [hMT]
      refine congrArg card (filter_congr fun x _ => ?_)
      rw [hQ, padding_padG hy S hq, Nat.add_comm x, Nat.mul_comm (2 ^ y.fo.dT)]
    rw [hL, hR, Road.card_block Q y.T M t, Road.sum_block Q y.T M htN]
  · rw [if_neg hb]
    refine List.sum_eq_zero fun a ha => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    refine if_neg fun k => hb ?_
    have hx' : x < 2 ^ FoNums.io y.fo q * 2 ^ (y.fo.dT - y.h.lt) := List.mem_range.mp hx
    have hq' : x / 2 ^ (y.fo.dT - y.h.lt) < 2 ^ FoNums.io y.fo q :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hx')
    obtain ⟨-, k2⟩ := k
    rw [← k2]
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hq' _⟩

/-- If Layer.layout h pc returns y and Switches h holds, then PubFits y.fo (padG y): for every tree
below NT the public number of padding keys is the number of padG's places in the tree. -/
theorem pubFits_G {h : Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) (S : Switches h) : PubFits y.fo (padG y) := by
  intro θ hθ
  obtain ⟨hok, -, -⟩ := ok_of_layout hy
  obtain ⟨-, hb, hc, -⟩ := Cb.Fo.ok_parts hok
  obtain ⟨b1, b2, b3⟩ := hb θ hθ
  have hNC : y.fo.NC = y.calls.size :=
    (Road.fo_of_layout hy).2.1.trans (Road.fo_of_layout hy).2.2
  have hlen : y.calls.toList.length = y.calls.size := by simp
  rw [(Road.pub_fold hy).2 θ hθ, Road.zipIdx_sum default _ y.calls.toList 0, hlen,
    Finset.sum_eq_single (FoNums.co y.fo θ)]
  · show Road.pubOf y (FoNums.fst y.fo (0 + FoNums.co y.fo θ)) y.fo.dT
      (y.calls.toList.getD (FoNums.co y.fo θ) default) θ = _
    rw [Nat.zero_add, toList_getD, pubOf_tree hy S (by omega) θ, if_pos ⟨b2, b3⟩]
    have e := ((hc _ b1).2.2.2 (θ - FoNums.fst y.fo (FoNums.co y.fo θ)) (by omega)).2.2
    have e2 : FoNums.fst y.fo (FoNums.co y.fo θ) + (θ - FoNums.fst y.fo (FoNums.co y.fo θ)) = θ :=
      by omega
    rw [e2] at e
    rw [e]
  · intro q hq hne
    have hq' := mem_range.1 hq
    show Road.pubOf y (FoNums.fst y.fo (0 + q)) y.fo.dT (y.calls.toList.getD q default) θ = 0
    rw [Nat.zero_add, toList_getD, pubOf_tree hy S hq' θ, if_neg]
    rintro ⟨k1, k2⟩
    have e := ((hc q (by omega)).2.2.2 (θ - FoNums.fst y.fo q) (by omega)).2.1
    have e2 : FoNums.fst y.fo q + (θ - FoNums.fst y.fo q) = θ := by omega
    rw [e2] at e
    exact hne e.symm
  · intro k
    exact absurd (mem_range.2 (by omega)) k

/-! ## The law of a group of layers -/

section Law
variable {K : Type} [Field K] [DecidableEq K]

/-- The cells of matrix number G.iB P.y are the planes' matrix bG of these very cells, cast into K,
at every row below 2^lmb and column below NC 2^(kT + 5 - lmb). Nothing is asked outside these rows
and columns, where bG is 0 (plane_outside). -/
def LaidB (P : Layer.Pub) (g : ℕ) (cell : G.NameG → K) : Prop :=
  ∀ r < 2 ^ P.y.h.lmb, ∀ c < P.y.fo.NC * 2 ^ (P.y.fo.kT + 5 - P.y.h.lmb),
    cell (.cell (G.iB P.y) r c) = (bG P g cell r c : K)

/-- If 5 ≤ lmb ≤ kT + 5 and LaidB P g cell holds, then for u < 2^d and j < 32 the bit
G.bitsG P.y cell (u * 32 + j) is the cell of plane at FoNums.cellRC (u / 2^cK, u % 2^cK, j), cast
into K. -/
theorem bitsG_plane (P : Layer.Pub) (g : ℕ) (cell : G.NameG → K) (h5 : 5 ≤ P.y.h.lmb)
    (hlm : P.y.h.lmb ≤ P.y.fo.kT + 5) (hb : LaidB P g cell) {u j : ℕ} (hu : u < 2 ^ P.y.fo.d)
    (hj : j < 32) :
    G.bitsG P.y cell (u * 32 + j) =
      (plane P.y.fo P.y.h.lmb (hitsG P g cell)
        (FoNums.cellRC P.y.fo P.y.h.lmb (u / 2 ^ P.y.fo.cK, u % 2 ^ P.y.fo.cK, j)).1
        (FoNums.cellRC P.y.fo P.y.h.lmb (u / 2 ^ P.y.fo.cK, u % 2 ^ P.y.fo.cK, j)).2 : K) := by
  have e1 : (u * 32 + j) / 32 = u := by omega
  have e2 : (u * 32 + j) % 32 = j := by omega
  have ht : u / 2 ^ P.y.fo.cK < 2 ^ P.y.fo.kT := by
    apply Nat.div_lt_of_lt_mul
    rw [← pow_add, Nat.add_comm]
    exact hu
  unfold G.bitsG
  rw [e1, e2]
  by_cases hc : u % 2 ^ P.y.fo.cK < P.y.fo.NC
  · rw [placeG_cellRC P.y hc hj hu]
    exact hb _ (cellRC_in _ h5 hlm ht hc hj).1 _ (cellRC_in _ h5 hlm ht hc hj).2
  · have hn : G.placeG P.y u j = none := by
      unfold G.placeG
      rw [if_neg fun k => hc k.1]
    have hf : bit P.y.fo (hitsG P g cell) (u / 2 ^ P.y.fo.cK) (u % 2 ^ P.y.fo.cK) j = false := by
      simp [bit, hc]
    rw [hn, plane_cellRC _ _ _ h5 hlm ht hj, hf]
    simp

/-- If Layer.layout h pc returns P.y, Switches h holds, and for every call c below NC every place of
G.kvG P g cell c holds the value of a row below 2^(k_c) of tabOf, then Fits holds of the tables
tabOf, the key vectors G.kvG P g cell and hitsG P g cell. -/
theorem fitsG {h : Layer.Shape} {pc : List (List String)} (P : Layer.Pub)
    (hy : layout h pc = .ok P.y) (S : Switches h) (g : ℕ) (cell : G.NameG → K)
    (hin : ∀ c < P.y.fo.NC, Cb.Lkp.InTable (FoNums.nOf P.y.fo c) (FoNums.kOf P.y.fo c)
      (G.kvG P g cell c) (tabOf K P.y.fo c)) :
    Fits P.y.fo (tabOf K P.y.fo) (G.kvG P g cell) (hitsG P g cell) := by
  obtain ⟨hok, -, -⟩ := ok_of_layout hy
  have hcs := (calls_size hok).1
  exact fits_hitsOf P.y.fo _ _ _ hok hin
    (fun c hc i _ hp => kvG_pad P g cell (by omega) hp) (pubFits_G hy S)

/-- If Layer.layout h pc returns P.y, Switches h holds, for every call c below NC every place of
G.kvG P g cell c holds the value of a row below 2^(k_c) of tabOf, and LaidB P g cell holds, then
for all θ and al Cb.Lkp.MidP holds at G.keyG P g cell θ, G.tabG P θ, FoNums.pads P.y.fo and the bits
G.bitsG P.y cell (u * 32 + j). -/
theorem lawG {h : Layer.Shape} {pc : List (List String)} (P : Layer.Pub)
    (hy : layout h pc = .ok P.y) (S : Switches h) (g : ℕ) (cell : G.NameG → K)
    (hin : ∀ c < P.y.fo.NC, Cb.Lkp.InTable (FoNums.nOf P.y.fo c) (FoNums.kOf P.y.fo c)
      (G.kvG P g cell c) (tabOf K P.y.fo c))
    (hb : LaidB P g cell) (θ al : K) :
    Cb.Lkp.MidP P.y.fo.v P.y.fo.d 5 32 (G.keyG P g cell θ) (G.tabG P θ) (FoNums.pads P.y.fo)
      (fun u j => G.bitsG P.y cell (u * 32 + j)) al := by
  obtain ⟨hok, h5, hlm⟩ := ok_of_layout hy
  have hcs := (calls_size hok).1
  exact law_bits P.y.fo (G.kvG P g cell) (padG P.y) hok hin
    (fun c hc i _ hp => kvG_pad P g cell (by omega) hp) (pubFits_G hy S) h5 hlm _
    (fun u hu j hj => bitsG_plane P g cell h5 hlm hb hu hj) θ al

/-- Under the premises of fitsG: the cells of bG P g cell in the rows below 2^lmb and the columns
below NC * 2^(kT + 5 - lmb), each weighted by 2^(r % 32), and P.y.fo.padding add up to 2^v. -/
theorem sum_bG {h : Layer.Shape} {pc : List (List String)} (P : Layer.Pub)
    (hy : layout h pc = .ok P.y) (S : Switches h) (g : ℕ) (cell : G.NameG → K)
    (hin : ∀ c < P.y.fo.NC, Cb.Lkp.InTable (FoNums.nOf P.y.fo c) (FoNums.kOf P.y.fo c)
      (G.kvG P g cell c) (tabOf K P.y.fo c)) :
    ∑ col ∈ range (P.y.fo.NC * 2 ^ (P.y.fo.kT + 5 - P.y.h.lmb)), ∑ r ∈ range (2 ^ P.y.h.lmb),
        2 ^ (r % 32) * bG P g cell r col + P.y.fo.padding = 2 ^ P.y.fo.v := by
  obtain ⟨hok, h5, hlm⟩ := ok_of_layout hy
  exact sum_plane_all P.y.fo _ _ _ hok (fitsG P hy S g cell hin) h5 hlm

/-! ## Laying the planes into the cells -/

/-- Under KeysSkipB P g cell, hitsG at withBG P g cell and at cell agree at all places of all calls
below NC. -/
theorem hitsG_withBG (P : Layer.Pub) (g : ℕ) (cell : G.NameG → K) (hs : KeysSkipB P g cell) :
    ∀ c < P.y.fo.NC, ∀ i < 2 ^ FoNums.nOf P.y.fo c,
      (hitsG P g (withBG P g cell)).pad c i = (hitsG P g cell).pad c i ∧
        (hitsG P g (withBG P g cell)).row c i = (hitsG P g cell).row c i := by
  intro c hc i hi
  refine ⟨rfl, ?_⟩
  show (if padG P.y c i = true then FoNums.t0Of P.y.fo c
      else firstRow (tabOf K P.y.fo c) (FoNums.kOf P.y.fo c)
        (G.kvG P g (withBG P g cell) c i)) =
    if padG P.y c i = true then FoNums.t0Of P.y.fo c
      else firstRow (tabOf K P.y.fo c) (FoNums.kOf P.y.fo c) (G.kvG P g cell c i)
  rw [hs c hc i hi]

/-- Under KeysSkipB P g cell, LaidB holds of withBG P g cell. -/
theorem withBG_laid (P : Layer.Pub) (g : ℕ) (cell : G.NameG → K) (hs : KeysSkipB P g cell) :
    LaidB P g (withBG P g cell) := by
  intro r _ c _
  show (if G.iB P.y = G.iB P.y then (bG P g cell r c : K) else cell (.cell (G.iB P.y) r c)) =
    (bG P g (withBG P g cell) r c : K)
  rw [if_pos rfl]
  exact congrArg Nat.cast (plane_congr _ _ (hitsG_withBG P g cell hs) r c).symm

/-- Under KeysSkipB P g cell: if for every call c below NC every place of G.kvG P g cell c holds the
value of a row below 2^(k_c) of tabOf, the same holds of G.kvG P g (withBG P g cell) c. -/
theorem inTable_withBG (P : Layer.Pub) (g : ℕ) (cell : G.NameG → K) (hs : KeysSkipB P g cell)
    (hin : ∀ c < P.y.fo.NC, Cb.Lkp.InTable (FoNums.nOf P.y.fo c) (FoNums.kOf P.y.fo c)
      (G.kvG P g cell c) (tabOf K P.y.fo c)) :
    ∀ c < P.y.fo.NC, Cb.Lkp.InTable (FoNums.nOf P.y.fo c) (FoNums.kOf P.y.fo c)
      (G.kvG P g (withBG P g cell) c) (tabOf K P.y.fo c) := by
  intro c hc b hb
  rw [hs c hc b hb]
  exact hin c hc b hb

end Law

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.kvG_pad
#print axioms OnBytes.HonestTrace.placeG_cellRC
#print axioms OnBytes.HonestTrace.look_ok
#print axioms OnBytes.HonestTrace.ok_of_layout
#print axioms OnBytes.HonestTrace.getD_of_mem
#print axioms OnBytes.HonestTrace.place_used_col
#print axioms OnBytes.HonestTrace.toList_getD
#print axioms OnBytes.HonestTrace.call_facts
#print axioms OnBytes.HonestTrace.padding_padG
#print axioms OnBytes.HonestTrace.pubOf_tree
#print axioms OnBytes.HonestTrace.pubFits_G
#print axioms OnBytes.HonestTrace.bitsG_plane
#print axioms OnBytes.HonestTrace.fitsG
#print axioms OnBytes.HonestTrace.lawG
#print axioms OnBytes.HonestTrace.sum_bG
#print axioms OnBytes.HonestTrace.hitsG_withBG
#print axioms OnBytes.HonestTrace.withBG_laid
#print axioms OnBytes.HonestTrace.inTable_withBG
