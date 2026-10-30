-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/StoredExt.lean: the compiled verifier's checks on the two stored tables.

The strict reader holds, for each stored table that a proof opens, one opening: the listed places,
a column and a salt for each place, and the digests that the walk to the root needs. The compiled
verifier sees the two tables as two strings under two roots. The library's typing of what was read
gives it a function from the strings' positions to openings (`Run.PQ.extOf`). This file shows what
that function has to satisfy, from `StoOK`, which states what the reader is to have checked of the
openings.

Main definitions: `tabsOf`, `askedOf`, `readOf`, `StoOK`. The proofs also use `rowsOf`, `tabAt`,
`TabOK` (one table at a time), `checkFor`, `chk` and `twoF` (the checks and the forest, written
out).
Main theorems: `famX_leaf`, `famX_node` (the typed hash functions are the format's calls),
`ext_forest` (the walk over both tables ends in the roots of the opened ones), `ext_strict` (an
opening is present only at a position that is read, with a salt of the right length), `ext_symbol`
(at a listed place the string that the verifier builds holds the place and the listed column).
Steps of `ext_forest`, for any interface: `two_strings` (on its way over all positions the verifier
collects the checks of the first table's rows in order, then of the second's), `run_two` (the walk).

Two things to know. In this file the positions that are "read" are those that the openings
themselves list (`readOf`). So "an opening is present only at a position that is read" holds by
construction here; that the verifier's own set of reads is this one is proved elsewhere
(`xWanted_asked`, OnBytes/Tie/StoredGlue.lean). And a table that is not opened is not walked: its
root is compared with nothing (`StoOK` holds of the empty list too).

Not claimed here: that the reader's checks give `StoOK`, nor that the compiled verifier as a
whole accepts.
-/
import Compile.CompleteStrict
import Run.PageIsProofs
import Run.PlanQXRun
import Run.Toy1TieChecks
import OnBytes.Tie.StoredWalk

set_option autoImplicit false

namespace OnBytes.Tie
open Rom Iop Compile Compile.Batch Run Run.PQ Run.Twin Run.Thin

/-- The stored tables' openings, each with whole paths, as the typing looks them up. -/
def tabsOf (sto : List (Bool × ℕ × OpenB)) : List (Bool × OpenB × List (List (Dig 256))) :=
  sto.map fun x => (x.1, x.2.2, x.2.2.paths)

/-- The places that the stored tables' openings list: (which table, place). -/
def askedOf (sto : List (Bool × ℕ × OpenB)) : List (Bool × ℕ) :=
  sto.flatMap fun e => e.2.2.idx.map fun x => (e.1, x)

/-- The positions of the two strings that the openings list. The theorems of this file take these
to be the positions that are read. -/
def readOf (a : ℕ) (sto : List (Bool × ℕ × OpenB)) : Finset (Fin (2 ^ a) ⊕ Fin (2 ^ a)) :=
  ((askedOf sto).filterMap (xPos (2 ^ a))).toFinset

/-- What is known of the stored tables' openings. Each of the two tables is opened at most once.
Each opening has the right form and depth, is not empty, and walks to its table's root. -/
structure StoOK (O : ByteArray → ByteArray) (cfg : ByteArray) (a salt : ℕ) (r0 r1 : ByteArray)
    (sto : List (Bool × ℕ × OpenB)) : Prop where
  /-- no table is opened twice -/
  once : (sto.map (·.1)).Nodup
  /-- each opening has the right form -/
  ok : ∀ e ∈ sto, e.2.2.ok salt e.2.1 = true
  /-- each opening has the tables' depth -/
  depth : ∀ e ∈ sto, e.2.2.a = a
  /-- no opening is empty -/
  ne : ∀ e ∈ sto, e.2.2.idx ≠ []
  /-- each opening walks to its table's root -/
  walk : ∀ e ∈ sto, (Octopus.octF (fun l r => Fmt.HO O 166 0 0 cfg (l ++ r)) a e.2.2.idx
    (WalkTie.leafV (Fmt.HO O) ⟨a, e.2.1, true, 0⟩ cfg e.2.2.idx (e.2.2.cols.zip e.2.2.salts))
    e.2.2.given).headD default = (if e.1 then r1 else r0)

/-! ### Lookups in a list of pairs -/

/-- What a lookup finds is listed under the key. -/
theorem mem_of_lookup_some {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List (α × β)) (k : α) (v : β), l.lookup k = some v → (k, v) ∈ l
  | [], _, _, h => by cases h
  | (k', v') :: l, k, v, h => by
    rw [List.lookup_cons] at h
    cases hk : k == k' with
    | true =>
      rw [hk] at h
      have hv : v' = v := Option.some.inj h
      have hkk : k = k' := eq_of_beq hk
      rw [hkk, hv]
      exact List.mem_cons_self
    | false =>
      rw [hk] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup_some l k v h)

/-- If no key occurs twice, a lookup finds what is listed under the key. -/
theorem lookup_some_of_mem {α β : Type} [BEq α] [LawfulBEq α] :
    ∀ (l : List (α × β)) (k : α) (v : β), (l.map Prod.fst).Nodup → (k, v) ∈ l →
      l.lookup k = some v
  | [], _, _, _, h => by cases h
  | (k', v') :: l, k, v, hn, hm => by
    rw [List.map_cons, List.nodup_cons] at hn
    rw [List.lookup_cons]
    rcases List.mem_cons.1 hm with e | hm'
    · cases e
      rw [beq_self_eq_true]
    · have hne : (k == k') = false := by
        refine beq_false_of_ne fun e => hn.1 ?_
        rw [← e]
        exact List.mem_map.2 ⟨(k, v), hm', rfl⟩
      rw [hne]
      exact lookup_some_of_mem l k v hn.2 hm'

/-! ### A position of the two strings, and the pair (which table, place) -/

/-- A position of the two strings comes from its own table and place. -/
theorem xPos_back (n : ℕ) (p : Fin n ⊕ Fin n) :
    xPos n (p.elim (fun _ => false) fun _ => true, p.elim (·.val) (·.val)) = some p := by
  cases p with
  | inl q => simp [xPos]
  | inr q => simp [xPos]

/-- A place below the strings' length gives a position with that table and that place. -/
theorem xPos_at (n : ℕ) (b : Bool) (x : ℕ) (h : x < n) :
    ∃ p, xPos n (b, x) = some p ∧ p.elim (fun _ => false) (fun _ => true) = b ∧
      p.elim (·.val) (·.val) = x := by
  cases b
  · exact ⟨.inl ⟨x, h⟩, by simp [xPos, h], rfl, rfl⟩
  · exact ⟨.inr ⟨x, h⟩, by simp [xPos, h], rfl, rfl⟩

/-- A listed place of an opened table is among the positions that are read. -/
theorem mem_readOf (a : ℕ) (sto : List (Bool × ℕ × OpenB)) (e : Bool × ℕ × OpenB) (he : e ∈ sto)
    (x : ℕ) (hx : x ∈ e.2.2.idx) (p : Fin (2 ^ a) ⊕ Fin (2 ^ a))
    (hp : xPos (2 ^ a) (e.1, x) = some p) : p ∈ readOf a sto := by
  have hask : (e.1, x) ∈ askedOf sto :=
    List.mem_flatMap.2 ⟨e, he, List.mem_map.2 ⟨x, hx, rfl⟩⟩
  exact List.mem_toFinset.2 (List.mem_filterMap.2 ⟨(e.1, x), hask, hp⟩)

/-! ### The opening that the typing puts at a position -/

/-- The typed salt has eight bits for each byte of the run's value and of the file's salt. -/
theorem length_leafSalt (run s : ByteArray) :
    (leafSalt run s).length = 8 * run.size + 8 * s.size := by
  rw [leafSalt, List.length_append, length_bytesToBits, length_bytesToBits]

/-- An opening at a place comes from a row that is listed under that place. -/
theorem atP_found {σ : Type} (sym : List UInt64 → Option σ) (run : ByteArray) (Ob : OpenB)
    (paths : List (List (Dig 256))) (x : ℕ) (op : Opening 256 σ)
    (h : Ob.atP sym run paths x = some op) :
    ∃ c s pt y, (x, c, s, pt) ∈ Ob.idx.zip (Ob.cols.zip (Ob.salts.zip paths)) ∧
      sym c = some y ∧ op = ⟨y, leafSalt run s, pt⟩ := by
  unfold OpenB.atP at h
  split at h
  · cases h
  · rename_i c s pt hl
    obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 h
    exact ⟨c, s, pt, y, mem_of_lookup_some _ _ _ hl, hy, e.symm⟩

/-- The opening at a position: find the table, then the place in it. -/
theorem extOf_unfold (a : ℕ) (cfg : ByteArray)
    (tabs : List (Bool × OpenB × List (List (Dig 256)))) (p : Fin (2 ^ a) ⊕ Fin (2 ^ a)) :
    extOf a cfg tabs p = (tabs.lookup (p.elim (fun _ => false) fun _ => true)).bind fun T =>
      T.1.atP (fun c => some (p.elim (·.val) (·.val), c)) cfg T.2 (p.elim (·.val) (·.val)) :=
  rfl

/-- The keys of the typed tables are the Booleans of the openings. -/
theorem tabsOf_keys (sto : List (Bool × ℕ × OpenB)) :
    (tabsOf sto).map Prod.fst = sto.map (·.1) := by
  rw [tabsOf, List.map_map]
  rfl

/-- Backwards: an opening at a position comes from a row of an opened table. The row is listed
under the position's place, and the table is the position's. -/
theorem extOf_found (a : ℕ) (cfg : ByteArray) (sto : List (Bool × ℕ × OpenB))
    (p : Fin (2 ^ a) ⊕ Fin (2 ^ a)) (op : Opening 256 SgX)
    (h : extOf a cfg (tabsOf sto) p = some op) :
    ∃ e ∈ sto, e.1 = p.elim (fun _ => false) (fun _ => true) ∧ ∃ c s pt,
      (p.elim (·.val) (·.val), c, s, pt)
        ∈ e.2.2.idx.zip (e.2.2.cols.zip (e.2.2.salts.zip e.2.2.paths)) ∧
      op = ⟨(p.elim (·.val) (·.val), c), leafSalt cfg s, pt⟩ := by
  rw [extOf_unfold] at h
  obtain ⟨T, hT, hat⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨e, he, eT⟩ := List.mem_map.1 (mem_of_lookup_some _ _ _ hT)
  obtain ⟨e1, e2⟩ := Prod.mk.inj eT
  subst e2
  obtain ⟨c, s, pt, y, hm, hy, hop⟩ := atP_found _ _ _ _ _ _ hat
  have hy' : (p.elim (·.val) (·.val), c) = y := Option.some.inj hy
  subst hy'
  exact ⟨e, he, e1, c, s, pt, hm, hop⟩

/-- Forwards: at the position of a listed place of an opened table there is an opening that holds
the place and the listed column. -/
theorem extOf_at_listed (a : ℕ) (cfg : ByteArray) (salt : ℕ) (sto : List (Bool × ℕ × OpenB))
    (once : (sto.map (·.1)).Nodup) (e : Bool × ℕ × OpenB) (he : e ∈ sto)
    (hok : e.2.2.ok salt e.2.1 = true) (x : ℕ) (col : List UInt64)
    (hx : (x, col) ∈ e.2.2.idx.zip e.2.2.cols) (p : Fin (2 ^ a) ⊕ Fin (2 ^ a))
    (hw : p.elim (fun _ => false) (fun _ => true) = e.1) (hp : p.elim (·.val) (·.val) = x) :
    ∃ s pt, extOf a cfg (tabsOf sto) p = some ⟨(x, col), leafSalt cfg s, pt⟩ := by
  have hl : (tabsOf sto).lookup e.1 = some (e.2.2, e.2.2.paths) :=
    lookup_some_of_mem _ _ _ (by rw [tabsOf_keys]; exact once) (List.mem_map.2 ⟨e, he, rfl⟩)
  obtain ⟨s, pt, hat⟩ := at_listed (fun c => some (x, c)) cfg e.2.2 salt e.2.1 hok x col hx
  refine ⟨s, pt, ?_⟩
  rw [extOf_unfold, hw, hp, hl]
  exact hat

/-! ### One table at a time -/

/-- One row of an opening: the place, its column, its salt, its whole path. -/
abbrev Row : Type := ℕ × List UInt64 × ByteArray × List (Dig 256)

/-- The rows of an opening, in the order of its list of places. -/
def rowsOf (Ob : OpenB) : List Row := Ob.idx.zip (Ob.cols.zip (Ob.salts.zip Ob.paths))

/-- A width and an opening of depth a that opens nothing. -/
def noOpen (a : ℕ) : ℕ × OpenB := (0, ⟨a, [], [], [], []⟩)

/-- The width and the opening of table w. If that table is not opened: an opening of nothing. -/
def tabAt (a : ℕ) (sto : List (Bool × ℕ × OpenB)) (w : Bool) : ℕ × OpenB :=
  (sto.lookup w).getD (noOpen a)

/-- What is known of one table's opening: it has the right form and depth, and it opens nothing or
walks to the root. -/
structure TabOK (O : ByteArray → ByteArray) (cfg : ByteArray) (a salt : ℕ) (root : ByteArray)
    (T : ℕ × OpenB) : Prop where
  /-- the opening has the right form -/
  ok : T.2.ok salt T.1 = true
  /-- it has the tables' depth -/
  depth : T.2.a = a
  /-- it opens nothing, or it walks to the root -/
  walk : T.2.idx = [] ∨ (Octopus.octF (fun l r => Fmt.HO O 166 0 0 cfg (l ++ r)) a T.2.idx
    (WalkTie.leafV (Fmt.HO O) ⟨a, T.1, true, 0⟩ cfg T.2.idx (T.2.cols.zip T.2.salts))
    T.2.given).headD default = root

/-- A walk from no vertex takes no digest. -/
theorem need_nil : ∀ d : ℕ, Octopus.need d [] = 0
  | 0 => rfl
  | d + 1 => by
    show Octopus.need1 [] + Octopus.need d (Octopus.up []) = 0
    rw [show Octopus.up [] = [] from rfl, need_nil d]
    rfl

/-- The opening of nothing has the right form. -/
theorem noOpen_ok (a salt : ℕ) : (noOpen a).2.ok salt (noOpen a).1 = true := by
  simp [noOpen, OpenB.ok, incr, need_nil]

/-- The opening of table w is the opening of nothing, or it is listed under w. -/
theorem tabAt_cases (a : ℕ) (sto : List (Bool × ℕ × OpenB)) (w : Bool) :
    tabAt a sto w = noOpen a ∨ (w, tabAt a sto w) ∈ sto := by
  unfold tabAt
  cases h : sto.lookup w with
  | none => exact Or.inl rfl
  | some y => exact Or.inr (mem_of_lookup_some sto w y h)

/-- If no table is opened twice, a listed opening is the opening of its table. -/
theorem tabAt_of_mem (a : ℕ) (sto : List (Bool × ℕ × OpenB)) (once : (sto.map (·.1)).Nodup)
    (e : Bool × ℕ × OpenB) (he : e ∈ sto) : tabAt a sto e.1 = e.2 := by
  unfold tabAt
  rw [lookup_some_of_mem sto e.1 e.2 once he]
  rfl

/-- What is known of all openings is known of each table's opening. -/
theorem tabOK_of {O : ByteArray → ByteArray} {cfg : ByteArray} {a salt : ℕ} {r0 r1 : ByteArray}
    {sto : List (Bool × ℕ × OpenB)} (hs : StoOK O cfg a salt r0 r1 sto) (w : Bool) :
    TabOK O cfg a salt (if w then r1 else r0) (tabAt a sto w) := by
  rcases tabAt_cases a sto w with h | h
  · rw [h]
    exact ⟨noOpen_ok a salt, rfl, Or.inl rfl⟩
  · exact ⟨hs.ok _ h, hs.depth _ h, Or.inr (hs.walk _ h)⟩

/-- A sum over the listed openings is the sum over the two tables. -/
theorem sum_two (a : ℕ) (f : ℕ × OpenB → ℕ) (hf : f (noOpen a) = 0) :
    ∀ sto : List (Bool × ℕ × OpenB), (sto.map (·.1)).Nodup →
      (sto.map fun e => f e.2).sum = f (tabAt a sto false) + f (tabAt a sto true)
  | [], _ => by
    show 0 = f (noOpen a) + f (noOpen a)
    rw [hf]
  | (w, y) :: sto, hn => by
    rw [List.map_cons, List.nodup_cons] at hn
    have ih := sum_two a f hf sto hn.2
    have hno : tabAt a sto w = noOpen a := by
      rcases tabAt_cases a sto w with h | h
      · exact h
      · exact absurd (List.mem_map.2 ⟨_, h, rfl⟩) hn.1
    rw [List.map_cons, List.sum_cons, ih]
    cases w
    · have e1 : tabAt a ((false, y) :: sto) false = y := rfl
      have e2 : tabAt a ((false, y) :: sto) true = tabAt a sto true := rfl
      rw [e1, e2, hno, hf, Nat.zero_add]
    · have e1 : tabAt a ((true, y) :: sto) true = y := rfl
      have e2 : tabAt a ((true, y) :: sto) false = tabAt a sto false := rfl
      rw [e1, e2, hno, hf, Nat.add_zero, Nat.add_comm]

/-- The rows' places are the listed places. -/
theorem rows_fst (Ob : OpenB) (salt W : ℕ) (hok : Ob.ok salt W = true) :
    (rowsOf Ob).map Prod.fst = Ob.idx := by
  obtain ⟨hc, hs, -, -, -⟩ := TieTree.ok_spec Ob salt W hok
  have hpl : Ob.paths.length = Ob.idx.length := Octopus.length_fill _ _ _
  exact List.map_fst_zip (by simp only [List.length_zip]; omega)

/-- There are as many rows as listed places. -/
theorem rows_length (Ob : OpenB) (salt W : ℕ) (hok : Ob.ok salt W = true) :
    (rowsOf Ob).length = Ob.idx.length := by
  have h := congrArg List.length (rows_fst Ob salt W hok)
  rwa [List.length_map] at h

/-- The rows' places and paths are the listed places, each with its path. -/
theorem rows_ends (Ob : OpenB) (salt W : ℕ) (hok : Ob.ok salt W = true) :
    (rowsOf Ob).map (fun e => (e.1, e.2.2.2)) = Ob.idx.zip Ob.paths := by
  obtain ⟨hc, hs, -, -, -⟩ := TieTree.ok_spec Ob salt W hok
  have hpl : Ob.paths.length = Ob.idx.length := Octopus.length_fill _ _ _
  exact TieTree.zip4_ends Ob.idx Ob.cols Ob.salts Ob.paths (by omega) (by omega)

/-- The rows' places, columns and salts are the listed ones. -/
theorem rows_three (Ob : OpenB) (salt W : ℕ) (hok : Ob.ok salt W = true) :
    (rowsOf Ob).map (fun e => (e.1, e.2.1, e.2.2.1)) = Ob.idx.zip (Ob.cols.zip Ob.salts) := by
  obtain ⟨hc, hs, -, -, -⟩ := TieTree.ok_spec Ob salt W hok
  have hpl : Ob.paths.length = Ob.idx.length := Octopus.length_fill _ _ _
  exact TieTree.zip4_three Ob.idx Ob.cols Ob.salts Ob.paths (by omega)

/-- What is known of one table's opening gives `WalkOK`, which the walk over two trees asks for. -/
theorem walkOK_of {O : ByteArray → ByteArray} (hO : ∀ s, (O s).size = 32) {cfg : ByteArray}
    {a salt : ℕ} {root : ByteArray} (hr : root.size = 32) {T : ℕ × OpenB}
    (k : TabOK O cfg a salt root T) :
    WalkOK (fun l r => Fmt.HO O 166 0 0 cfg (l ++ r)) a T.2.idx
      (WalkTie.leafV (Fmt.HO O) ⟨a, T.1, true, 0⟩ cfg T.2.idx (T.2.cols.zip T.2.salts))
      T.2.given root := by
  obtain ⟨hc, hs, -, hg, hg32⟩ := TieTree.ok_spec T.2 salt T.1 k.ok
  obtain ⟨hp, hb, -⟩ := TieTree.ok_list T.2 salt T.1 k.ok
  rw [k.depth] at hg hb
  by_cases hne : T.2.idx = []
  · left
    refine ⟨hne, ?_⟩
    rw [TieTree.leafV_eq, hne]
    rfl
  · right
    refine ⟨hne, hp, hb, WalkTie.length_leafV _ _ _ _ _ (by rw [List.length_zip]; omega), hg, ?_,
      hg32, hr, k.walk.resolve_left hne⟩
    intro x hx
    rw [TieTree.leafV_eq] at hx
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx
    exact hO _

/-! ### What is at a position of the two strings -/

/-- A position that comes from a table and a place has that table and that place. -/
theorem xPos_some (n : ℕ) (b : Bool) (x : ℕ) (p : Fin n ⊕ Fin n) (h : xPos n (b, x) = some p) :
    p.elim (fun _ => false) (fun _ => true) = b ∧ p.elim (·.val) (·.val) = x := by
  unfold xPos at h
  split at h
  · obtain rfl := Option.some.inj h
    cases b <;> exact ⟨rfl, rfl⟩
  · cases h

/-- A lookup among the typed tables is a lookup among the openings. -/
theorem lookup_tabsOf : ∀ (sto : List (Bool × ℕ × OpenB)) (w : Bool),
    (tabsOf sto).lookup w = (sto.lookup w).map fun y => (y.2, y.2.paths)
  | [], _ => rfl
  | (k, y) :: sto, w => by
    show List.lookup w ((k, y.2, y.2.paths) :: tabsOf sto)
      = (List.lookup w ((k, y) :: sto)).map fun y => (y.2, y.2.paths)
    rw [List.lookup_cons, List.lookup_cons]
    cases w == k with
    | true => rfl
    | false => exact lookup_tabsOf sto w

/-- The opening at a position is made of the row that the position's table lists under the
position's place. -/
theorem extOf_rows (a : ℕ) (cfg : ByteArray) (sto : List (Bool × ℕ × OpenB))
    (p : Fin (2 ^ a) ⊕ Fin (2 ^ a)) :
    extOf a cfg (tabsOf sto) p
      = ((rowsOf (tabAt a sto (p.elim (fun _ => false) fun _ => true)).2).lookup
          (p.elim (·.val) (·.val))).map
          fun r => ⟨(p.elim (·.val) (·.val), r.1), leafSalt cfg r.2.1, r.2.2⟩ := by
  rw [extOf_unfold, lookup_tabsOf]
  unfold tabAt
  cases sto.lookup (p.elim (fun _ => false) fun _ => true) with
  | none => rfl
  | some y =>
    show y.2.atP (fun c => some (p.elim (·.val) (·.val), c)) cfg y.2.paths
        (p.elim (·.val) (·.val))
      = ((rowsOf y.2).lookup (p.elim (·.val) (·.val))).map
          fun r => ⟨(p.elim (·.val) (·.val), r.1), leafSalt cfg r.2.1, r.2.2⟩
    unfold OpenB.atP rowsOf
    cases (y.2.idx.zip (y.2.cols.zip (y.2.salts.zip y.2.paths))).lookup
        (p.elim (·.val) (·.val)) with
    | none => rfl
    | some r => rfl

/-- Each table's opening has the right form. -/
theorem tabAt_ok (a salt : ℕ) (sto : List (Bool × ℕ × OpenB))
    (ok : ∀ e ∈ sto, e.2.2.ok salt e.2.1 = true) (w : Bool) :
    (tabAt a sto w).2.ok salt (tabAt a sto w).1 = true := by
  rcases tabAt_cases a sto w with h | h
  · rw [h]
    exact noOpen_ok a salt
  · exact ok _ h

/-- Each table's opening has the tables' depth. -/
theorem tabAt_depth (a : ℕ) (sto : List (Bool × ℕ × OpenB)) (depth : ∀ e ∈ sto, e.2.2.a = a)
    (w : Bool) : (tabAt a sto w).2.a = a := by
  rcases tabAt_cases a sto w with h | h
  · rw [h]
    rfl
  · exact depth _ h

/-- A position is read exactly if its table's opening lists its place. -/
theorem mem_readOf_iff (a : ℕ) (sto : List (Bool × ℕ × OpenB)) (once : (sto.map (·.1)).Nodup)
    (p : Fin (2 ^ a) ⊕ Fin (2 ^ a)) :
    p ∈ readOf a sto ↔ p.elim (·.val) (·.val)
      ∈ (tabAt a sto (p.elim (fun _ => false) fun _ => true)).2.idx := by
  constructor
  · intro hp
    obtain ⟨wx, hask, hpos⟩ := List.mem_filterMap.1 (List.mem_toFinset.1 hp)
    obtain ⟨e, he, hex⟩ := List.mem_flatMap.1 hask
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hex
    obtain ⟨hw, hv⟩ := xPos_some (2 ^ a) e.1 x p hpos
    rw [hw, hv, tabAt_of_mem a sto once e he]
    exact hx
  · intro hx
    rcases tabAt_cases a sto (p.elim (fun _ => false) fun _ => true) with h | h
    · rw [h] at hx
      cases hx
    · exact mem_readOf a sto _ h _ hx p (xPos_back (2 ^ a) p)

/-- There is an opening exactly at the positions that are read. -/
theorem read_law (a salt : ℕ) (cfg : ByteArray) (sto : List (Bool × ℕ × OpenB))
    (once : (sto.map (·.1)).Nodup) (ok : ∀ e ∈ sto, e.2.2.ok salt e.2.1 = true)
    (p : Fin (2 ^ a) ⊕ Fin (2 ^ a)) :
    decide (p ∈ readOf a sto) = (extOf a cfg (tabsOf sto) p).isSome := by
  have hfst := rows_fst _ salt _ (tabAt_ok a salt sto ok (p.elim (fun _ => false) fun _ => true))
  rw [extOf_rows, Option.isSome_map]
  by_cases hx : p.elim (·.val) (·.val)
      ∈ (tabAt a sto (p.elim (fun _ => false) fun _ => true)).2.idx
  · obtain ⟨v, hv, -⟩ := TieTree.lookup_isSome_of_mem _ _ (hfst.symm ▸ hx)
    rw [hv, decide_eq_true ((mem_readOf_iff a sto once p).2 hx)]
    rfl
  · rw [TieTree.lookup_none_of_not_mem _ _ (hfst.symm ▸ hx),
      decide_eq_false fun hp => hx ((mem_readOf_iff a sto once p).1 hp)]
    rfl

/-! ### The walk over all positions of the two strings -/

section
variable {I X : Type} {lam : ℕ} (Lf : Unit → BatchProtocol I X) {E : ExtSpec} (we : WireE E)
  (emb : E.Sym → Body (Lf ())) (cms : List (Dig lam)) (isRead : E.Pos → Bool)
  (g : E.Pos → Option (Opening lam E.Sym))

/-- The tree's number and the check that the walk makes of the opening at a position, if one is
there. -/
def checkFor (p : E.Pos) : Option (ℕ × Check lam (Lf ())) :=
  (g p).map fun op => (we.which p, ⟨⟨emb op.sym, op.salt⟩, we.leaf p, op.path,
    cms.getD (we.which p) default, we.depth⟩)

/-- If there is an opening exactly at the positions that are read, the walk does not fail, and it
gives the checks of the openings in the order of the positions. -/
theorem extWP_listed : ∀ ps : List E.Pos, (∀ p ∈ ps, isRead p = (g p).isSome) →
    extWP Lf we emb cms isRead g ps = some (ps.filterMap (checkFor Lf we emb cms g))
  | [], _ => rfl
  | p :: ps, h => by
    have ih := extWP_listed ps fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hp : isRead p = (g p).isSome := h p List.mem_cons_self
    cases hg : g p with
    | none =>
      have hr : isRead p = false := by rw [hp, hg]; rfl
      have hc : checkFor Lf we emb cms g p = none := by unfold checkFor; rw [hg]; rfl
      rw [List.filterMap_cons_none hc, extWP, hr, ← ih]
      rfl
    | some op =>
      have hr : isRead p = true := by rw [hp, hg]; rfl
      have hc : checkFor Lf we emb cms g p = some (we.which p, ⟨⟨emb op.sym, op.salt⟩, we.leaf p,
          op.path, cms.getD (we.which p) default, we.depth⟩) := by
        unfold checkFor
        rw [hg]
        rfl
      rw [List.filterMap_cons_some hc, extWP, hr, hg, ih]
      rfl

end

/-! ### The checks of the two tables, for any interface -/

section
variable {I X : Type} (Lf : Unit → BatchProtocol I X) (emb : SgX → Body (Lf ()))

/-- The check that a row of tree number t calls for, with the tree's number. -/
def chk (cfg : ByteArray) (a t : ℕ) (rt : Dig 256) (e : Row) : ℕ × Check 256 (Lf ()) :=
  (t, ⟨⟨emb (e.1, e.2.1), leafSalt cfg e.2.2.1⟩, e.1, e.2.2.2, rt, a⟩)

/-- The forest of two trees of depth a with the checks that two openings call for. -/
def twoF (cfg : ByteArray) (a : ℕ) (R : ℕ → Dig 256) (A B : OpenB) : Forest 256 (Lf ()) :=
  ⟨a, R, (rowsOf A).map (chk Lf emb cfg a 0 (R 0)) ++ (rowsOf B).map (chk Lf emb cfg a 1 (R 1))⟩

/-- One of the two strings: the checks at its positions, in order, are the checks of its table's
rows. Here inj makes a position of the two strings of a place in string number t. -/
theorem one_string (cms : List (Dig 256)) (a salt : ℕ) (cfg : ByteArray)
    (sto : List (Bool × ℕ × OpenB)) (ok : ∀ e ∈ sto, e.2.2.ok salt e.2.1 = true)
    (depth : ∀ e ∈ sto, e.2.2.a = a) (b : Bool) (t : ℕ)
    (inj : Fin (2 ^ a) → Fin (2 ^ a) ⊕ Fin (2 ^ a))
    (h1 : ∀ i, (inj i).elim (fun _ => false) (fun _ => true) = b)
    (h2 : ∀ i, (inj i).elim (·.val) (·.val) = i.val) (h3 : ∀ i, (weX a).which (inj i) = t)
    (h4 : ∀ i, (weX a).leaf (inj i) = i.val) :
    ((List.finRange (2 ^ a)).map inj).filterMap
        (checkFor Lf (weX a) emb cms (extOf a cfg (tabsOf sto)))
      = (rowsOf (tabAt a sto b).2).map (chk Lf emb cfg a t (cms.getD t default)) := by
  have hok := tabAt_ok a salt sto ok b
  have hfst := rows_fst _ salt _ hok
  obtain ⟨hsorted, hbound, -⟩ := TieTree.ok_list _ salt _ hok
  rw [tabAt_depth a sto depth b] at hbound
  -- At the position of place i is the check of the row that is listed under i.
  have hat : checkFor Lf (weX a) emb cms (extOf a cfg (tabsOf sto)) ∘ inj
      = (fun j : ℕ => ((rowsOf (tabAt a sto b).2).lookup j).map
          fun r => chk Lf emb cfg a t (cms.getD t default) (j, r)) ∘ Fin.val := by
    funext i
    show checkFor Lf (weX a) emb cms (extOf a cfg (tabsOf sto)) (inj i)
      = ((rowsOf (tabAt a sto b).2).lookup i.val).map
          fun r => chk Lf emb cfg a t (cms.getD t default) (i.val, r)
    unfold checkFor
    rw [extOf_rows, h1, h2, h3, h4, Option.map_map]
    rfl
  -- The places in order are the numbers below 2 ^ a, and the rows' places increase.
  rw [List.filterMap_map, hat, ← List.filterMap_map, List.map_coe_finRange_eq_range,
    List.range_eq_range', TieTree.filterMap_lookup _ (2 ^ a) 0 _ (hfst.symm ▸ hsorted)]
  intro e he
  have hm : e.1 ∈ (rowsOf (tabAt a sto b).2).map Prod.fst := List.mem_map.2 ⟨e, he, rfl⟩
  rw [hfst] at hm
  exact ⟨Nat.zero_le _, by rw [Nat.zero_add]; exact hbound e.1 hm⟩

/-- The compiled verifier walks all positions of both strings. If each table is opened at most once,
every opening has the right form and the depth a, and "read" is what the openings list (`readOf`),
it collects the checks of the first table's rows in order, then those of the second table's. -/
theorem two_strings (cms : List (Dig 256)) (a salt : ℕ) (cfg : ByteArray)
    (sto : List (Bool × ℕ × OpenB)) (once : (sto.map (·.1)).Nodup)
    (ok : ∀ e ∈ sto, e.2.2.ok salt e.2.1 = true) (depth : ∀ e ∈ sto, e.2.2.a = a) :
    extWP Lf (weX a) emb cms (fun p => decide (p ∈ readOf a sto)) (extOf a cfg (tabsOf sto))
        (weX a).all
      = some ((rowsOf (tabAt a sto false).2).map (chk Lf emb cfg a 0 (cms.getD 0 default)) ++
          (rowsOf (tabAt a sto true).2).map (chk Lf emb cfg a 1 (cms.getD 1 default))) := by
  rw [extWP_listed Lf (weX a) emb cms _ _ (weX a).all
    fun p _ => read_law a salt cfg sto once ok p]
  show some (((List.finRange (2 ^ a)).map Sum.inl ++ (List.finRange (2 ^ a)).map Sum.inr).filterMap
    (checkFor Lf (weX a) emb cms (extOf a cfg (tabsOf sto)))) = _
  rw [List.filterMap_append,
    one_string Lf emb cms a salt cfg sto ok depth false 0 Sum.inl (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl),
    one_string Lf emb cms a salt cfg sto ok depth true 1 Sum.inr (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl)]

/-- Of the two tables' openings the compiled verifier forms one forest, `twoF`. -/
theorem forest_two (cms : List (Dig 256)) (a salt : ℕ) (cfg : ByteArray)
    (sto : List (Bool × ℕ × OpenB)) (once : (sto.map (·.1)).Nodup)
    (ok : ∀ e ∈ sto, e.2.2.ok salt e.2.1 = true) (depth : ∀ e ∈ sto, e.2.2.a = a) :
    forestExtP Lf (weX a) emb cms (fun p => decide (p ∈ readOf a sto)) (extOf a cfg (tabsOf sto))
      = some [twoF Lf emb cfg a (fun t => cms.getD t default) (tabAt a sto false).2
          (tabAt a sto true).2] := by
  unfold forestExtP
  rw [two_strings Lf emb cms a salt cfg sto once ok depth]
  rfl

/-- Flattening one forest gives its checks. -/
theorem flat_one (F : Forest 256 (Lf ())) : flatP Lf [F] = F.cs.map Prod.snd := by
  simp [flatP]

/-- The forest has as many checks as the two openings list places. -/
theorem length_two (cfg : ByteArray) (a salt : ℕ) (R : ℕ → Dig 256) (A B : ℕ × OpenB)
    (hA : A.2.ok salt A.1 = true) (hB : B.2.ok salt B.1 = true) :
    (flatP Lf [twoF Lf emb cfg a R A.2 B.2]).length = A.2.idx.length + B.2.idx.length := by
  rw [flat_one, List.length_map]
  show ((rowsOf A.2).map _ ++ (rowsOf B.2).map _).length = _
  rw [List.length_append, List.length_map, List.length_map, rows_length A.2 salt A.1 hA,
    rows_length B.2 salt B.1 hB]

/-- The check of a row is well formed and has the tables' depth. -/
theorem well_chk (cfg : ByteArray) (a salt t : ℕ) (rt : Dig 256) (T : ℕ × OpenB)
    (hok : T.2.ok salt T.1 = true) (ha : T.2.a = a) (e : Row) (he : e ∈ rowsOf T.2) :
    wellP Lf (chk Lf emb cfg a t rt e).2 = true ∧ (chk Lf emb cfg a t rt e).2.depth = a := by
  obtain ⟨-, hb, -⟩ := TieTree.ok_list T.2 salt T.1 hok
  have h1 : e.1 < 2 ^ a := ha ▸ hb e.1 (List.of_mem_zip he).1
  have hp : e.2.2.2 ∈ T.2.paths :=
    (List.of_mem_zip (List.of_mem_zip (List.of_mem_zip he).2).2).2
  have h2 : e.2.2.2.length = a := ha ▸ Octopus.length_of_mem_fill _ _ _ _ hp
  refine ⟨?_, rfl⟩
  show (decide (e.2.2.2.length = a) && decide (e.1 < 2 ^ a)) = true
  rw [decide_eq_true h2, decide_eq_true h1]
  rfl

/-- Each check of the forest is well formed and has the tables' depth. -/
theorem well_two (cfg : ByteArray) (a salt : ℕ) (R : ℕ → Dig 256) (A B : ℕ × OpenB)
    (hA : A.2.ok salt A.1 = true) (hB : B.2.ok salt B.1 = true) (aA : A.2.a = a)
    (aB : B.2.a = a) :
    ∀ c ∈ flatP Lf [twoF Lf emb cfg a R A.2 B.2], wellP Lf c = true ∧ c.depth = a := by
  intro c hc
  rw [flat_one] at hc
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
  rcases List.mem_append.1 hx with h | h
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    exact well_chk Lf emb cfg a salt 0 (R 0) A hA aA e he
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    exact well_chk Lf emb cfg a salt 1 (R 1) B hB aB e he

/-- In the forest, one tree's opened leaves have the listed places with t * 2 ^ a added. -/
theorem idx_part (cfg : ByteArray) (a salt t : ℕ) (rt : Dig 256) (T : ℕ × OpenB)
    (hok : T.2.ok salt T.1 = true) :
    ((rowsOf T.2).map (chk Lf emb cfg a t rt)).map (fun e => e.1 * 2 ^ a + e.2.j)
      = T.2.idx.map (t * 2 ^ a + ·) := by
  conv_rhs => rw [← rows_fst T.2 salt T.1 hok]
  rw [List.map_map, List.map_map]
  rfl

/-- The same with their paths, which `Octopus.fill` makes from the given digests. -/
theorem path_part (cfg : ByteArray) (a salt t : ℕ) (rt : Dig 256) (T : ℕ × OpenB)
    (hok : T.2.ok salt T.1 = true) (ha : T.2.a = a) :
    ((rowsOf T.2).map (chk Lf emb cfg a t rt)).map (fun e => (e.1 * 2 ^ a + e.2.j, e.2.path))
      = (T.2.idx.zip (Octopus.fill a T.2.idx (T.2.given.map bytesToDig))).map
          fun x => (t * 2 ^ a + x.1, x.2) := by
  have h := rows_ends T.2 salt T.1 hok
  unfold OpenB.paths at h
  rw [ha] at h
  rw [← h, List.map_map, List.map_map]
  rfl

variable {K : ℕ} (g : Fam (spec 256 K (Lf ())))

/-- The typed leaf function's answer at a check, as a digest. -/
def leafD (e : ℕ × Check 256 (Lf ())) : Dig 256 := g OracleName.leaf e.2.inp

/-- If the typed leaf function is the format's call 174, one tree's opened leaves have the digests
from which the reader's walk starts. -/
theorem leaf_part (O : ByteArray → ByteArray) (cfg : ByteArray) (a salt t : ℕ) (rt : Dig 256)
    (hleaf : ∀ (x : ℕ) (col : List UInt64) (s : ByteArray),
      (g OracleName.leaf (⟨emb (x, col), leafSalt cfg s⟩ : LeafIn (Lf ())) : Dig 256)
        = bytesToDig (Fmt.HO O 174 (Fmt.leafPlace 0 col.length (s.size / 8)) (2 ^ a + x) cfg
            (Fmt.leafBytes col s)))
    (T : ℕ × OpenB) (hok : T.2.ok salt T.1 = true) :
    ((rowsOf T.2).map (chk Lf emb cfg a t rt)).map (leafD Lf g)
      = (WalkTie.leafV (Fmt.HO O) ⟨a, T.1, true, 0⟩ cfg T.2.idx
          (T.2.cols.zip T.2.salts)).map bytesToDig := by
  rw [TieTree.leafV_eq, ← rows_three T.2 salt T.1 hok, List.map_map, List.map_map, List.map_map]
  exact List.map_congr_left fun e _ => hleaf e.1 e.2.1 e.2.2.1

/-- The compiled verifier's walk through a forest, written out. -/
theorem run_mk (a : ℕ) (R : ℕ → Dig 256) (cs : List (ℕ × Check 256 (Lf ()))) :
    runForestP Lf g ⟨a, R, cs⟩ (readsOneP Lf ⟨a, R, cs⟩)
      = ((Octopus.upN a (cs.map fun e => e.1 * 2 ^ a + e.2.j)).zip
          (Octopus.octF (nodeP Lf g) a (cs.map fun e => e.1 * 2 ^ a + e.2.j)
            (cs.map (leafD Lf g))
            (Octopus.reads a (cs.map fun e => (e.1 * 2 ^ a + e.2.j, e.2.path))))).all
          fun m => decide (m.2 = R m.1) :=
  rfl

/-- The compiled verifier's walk through the forest of the two tables ends in the roots of the
tables that are opened, if both openings have `TabOK`, O's answers and the roots have 32 bytes, R
gives the roots at 0 and 1, and the typed node and leaf functions are the format's calls 166 and
174. A table that is not opened is not walked. -/
theorem run_two (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (cfg : ByteArray)
    (a salt : ℕ) (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hnode : nodeP Lf g = TieTree.digFn (fun l r => Fmt.HO O 166 0 0 cfg (l ++ r)))
    (hleaf : ∀ (x : ℕ) (col : List UInt64) (s : ByteArray),
      (g OracleName.leaf (⟨emb (x, col), leafSalt cfg s⟩ : LeafIn (Lf ())) : Dig 256)
        = bytesToDig (Fmt.HO O 174 (Fmt.leafPlace 0 col.length (s.size / 8)) (2 ^ a + x) cfg
            (Fmt.leafBytes col s)))
    (R : ℕ → Dig 256) (hR0 : R 0 = bytesToDig r0) (hR1 : R 1 = bytesToDig r1) (A B : ℕ × OpenB)
    (kA : TabOK O cfg a salt r0 A) (kB : TabOK O cfg a salt r1 B) :
    runForestP Lf g (twoF Lf emb cfg a R A.2 B.2) (readsOneP Lf (twoF Lf emb cfg a R A.2 B.2))
      = true := by
  have i0 : ∀ l : List ℕ, l.map (0 * 2 ^ a + ·) = l := fun l => by simp
  have i1 : ∀ l : List ℕ, l.map (1 * 2 ^ a + ·) = l.map (2 ^ a + ·) := fun l => by
    simp only [Nat.one_mul]
  have p0 : ∀ l : List (ℕ × List (Dig 256)), l.map (fun x => (0 * 2 ^ a + x.1, x.2)) = l :=
    fun l => by simp
  have p1 : ∀ l : List (ℕ × List (Dig 256)),
      l.map (fun x => (1 * 2 ^ a + x.1, x.2)) = l.map fun x => (2 ^ a + x.1, x.2) := fun l => by
    simp only [Nat.one_mul]
  unfold twoF
  rw [run_mk]
  simp only [List.map_append]
  rw [idx_part Lf emb cfg a salt 0 (R 0) A kA.ok, idx_part Lf emb cfg a salt 1 (R 1) B kB.ok,
    path_part Lf emb cfg a salt 0 (R 0) A kA.ok kA.depth,
    path_part Lf emb cfg a salt 1 (R 1) B kB.ok kB.depth,
    leaf_part Lf emb g O cfg a salt 0 (R 0) hleaf A kA.ok,
    leaf_part Lf emb g O cfg a salt 1 (R 1) hleaf B kB.ok, i0, i1, p0, p1, hnode]
  exact walk_two (fun l r => Fmt.HO O 166 0 0 cfg (l ++ r)) (fun _ _ => hO _) a A.2.idx B.2.idx
    _ _ A.2.given B.2.given r0 r1 R hR0 hR1 (walkOK_of hO h0 kA) (walkOK_of hO h1 kB)

end

section
variable (D : XD) (dec : View → Bool) (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)

/-- If the configuration's digest has 32 bytes, the typed leaf function at a symbol of a stored
table, with the typed salt `leafSalt cfg s`, is the format's call 174. Nothing is said of another
typed salt. -/
theorem famX_leaf (x : ℕ) (col : List UInt64) (s : ByteArray) (hc : D.base.cfg.size = 32) :
    (famX D dec O (D.K + 1) .leaf
        (⟨some (.inl (x, col)), leafSalt D.base.cfg s⟩ : LeafIn (D.L dec)) : Dig 256)
      = bytesToDig (Fmt.HO O 174 (Fmt.leafPlace 0 col.length (s.size / 8)) (2 ^ D.a + x)
          D.base.cfg (Fmt.leafBytes col s)) := by
  -- The typed salt is the 256 bits of cfg and then the bits of s.
  have hl : (bytesToBits D.base.cfg).length = 256 := by rw [length_bytesToBits, hc]
  have hfront : bitsToBytes ((leafSalt D.base.cfg s).take 256) = D.base.cfg := by
    unfold leafSalt
    rw [List.take_left' hl, bitsToBytes_bytesToBits]
  have hback : bitsToBytes ((leafSalt D.base.cfg s).drop 256) = s := by
    unfold leafSalt
    rw [List.drop_left' hl, bitsToBytes_bytesToBits]
  -- The number of the salt's words of 64 bits is the number of its words of 8 bytes.
  have hwords : ((leafSalt D.base.cfg s).length - 256) / 64 = s.size / 8 := by
    unfold leafSalt
    rw [List.length_append, hl, length_bytesToBits]
    omega
  -- So the test on the salt's front holds, and the leaf is spelled as call 174.
  have hcall : leafX D dec ⟨some (.inl (x, col)), leafSalt D.base.cfg s⟩
      = some ⟨0, 174, Fmt.leafPlace 0 col.length (s.size / 8), 2 ^ D.a + x, D.base.cfg,
          Fmt.leafBytes col s⟩ := by
    show (if bitsToBytes ((leafSalt D.base.cfg s).take 256) == D.base.cfg then
        some (⟨0, 174,
          Fmt.leafPlace 0 col.length (((leafSalt D.base.cfg s).length - 256) / 64),
          2 ^ D.a + x, D.base.cfg,
          Fmt.leafBytes col (bitsToBytes ((leafSalt D.base.cfg s).drop 256))⟩ : Fmt.OQ)
      else none) = _
    rw [hfront, hback, hwords, if_pos (bytes_beq_self D.base.cfg)]
  show ansOf O (leafX D dec ⟨some (.inl (x, col)), leafSalt D.base.cfg s⟩) = _
  rw [hcall]
  -- `Fmt.HO` asks O once under every number but 162.
  rfl

/-- A typed node query on two bit strings is the format's call 166 on their bytes. -/
theorem node_call (cfg : ByteArray) (u v : Bits) :
    ansOf O (nodeCallC cfg (u, v))
      = bytesToDig (Fmt.HO O 166 0 0 cfg (bitsToBytes u ++ bitsToBytes v)) :=
  rfl

/-- The typed node function is the format's call 166. -/
theorem famX_node :
    nodeP (fun _ => D.L dec) (famX D dec O (D.K + 1))
      = TieTree.digFn (fun l r => Fmt.HO O 166 0 0 D.base.cfg (l ++ r)) := by
  funext l r
  -- Both sides are the answer of O at the string of call 166 on the bytes of l and then of r.
  show ansOf O (nodeCallC D.base.cfg (List.ofFn l, List.ofFn r))
    = bytesToDig (Fmt.HO O 166 0 0 D.base.cfg (digToBytes l ++ digToBytes r))
  exact node_call O D.base.cfg (List.ofFn l) (List.ofFn r)

include hO in
/-- The forest of the two stored tables, given `StoOK`, with O's answers, the roots and the
configuration's digest of 32 bytes, and "read" taken to be what the openings list (`readOf`): there
is one; it has as many checks as places are listed; each check is well formed and of the tables'
depth; its walk ends in the roots of the tables that are opened. A table that is not opened is not
walked. -/
theorem ext_forest (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hc : D.base.cfg.size = 32) (sto : List (Bool × ℕ × OpenB))
    (hs : StoOK O D.base.cfg D.a D.base.plan.salt r0 r1 sto) :
    ∃ Fx : Forest 256 (D.L dec),
      forestExtP (fun _ => D.L dec) (weX D.a) (fun s => some (.inl s))
        [bytesToDig r0, bytesToDig r1] (fun p => decide (p ∈ readOf D.a sto))
        (extOf D.a D.base.cfg (tabsOf sto)) = some [Fx] ∧
      (flatP (fun _ => D.L dec) [Fx]).length = (sto.map (·.2.2.idx.length)).sum ∧
      (∀ c ∈ flatP (fun _ => D.L dec) [Fx], wellP (fun _ => D.L dec) c = true ∧ c.depth = D.a) ∧
      runForestP (fun _ => D.L dec) (famX D dec O (D.K + 1)) Fx
        (readsOneP (fun _ => D.L dec) Fx) = true := by
  have k0 : TabOK O D.base.cfg D.a D.base.plan.salt r0 (tabAt D.a sto false) := tabOK_of hs false
  have k1 : TabOK O D.base.cfg D.a D.base.plan.salt r1 (tabAt D.a sto true) := tabOK_of hs true
  refine ⟨twoF (fun _ => D.L dec) (fun s => some (.inl s)) D.base.cfg D.a
    (fun t => [bytesToDig r0, bytesToDig r1].getD t default) (tabAt D.a sto false).2
    (tabAt D.a sto true).2, ?_, ?_, ?_, ?_⟩
  · exact forest_two (fun _ => D.L dec) (fun s => some (.inl s)) [bytesToDig r0, bytesToDig r1]
      D.a D.base.plan.salt D.base.cfg sto hs.once hs.ok hs.depth
  · rw [length_two (fun _ => D.L dec) (fun s => some (.inl s)) D.base.cfg D.a D.base.plan.salt _
      (tabAt D.a sto false) (tabAt D.a sto true) k0.ok k1.ok]
    exact (sum_two D.a (fun T => T.2.idx.length) rfl sto hs.once).symm
  · exact well_two (fun _ => D.L dec) (fun s => some (.inl s)) D.base.cfg D.a D.base.plan.salt _
      (tabAt D.a sto false) (tabAt D.a sto true) k0.ok k1.ok k0.depth k1.depth
  · exact run_two (fun _ => D.L dec) (fun s => some (.inl s)) (famX D dec O (D.K + 1)) O hO
      D.base.cfg D.a D.base.plan.salt r0 r1 h0 h1 (famX_node D dec O)
      (fun x col s => famX_leaf D dec O x col s hc) _ rfl rfl (tabAt D.a sto false)
      (tabAt D.a sto true) k0 k1

/-- The strict format of the stored tables' openings, given `StoOK` and a configuration's digest of
32 bytes. "Read" is taken here to be what the openings themselves list (`readOf`), so "an opening
is present only where the verifier reads" holds by construction. What the theorem adds is the salt's
length. -/
theorem ext_strict (r0 r1 : ByteArray) (hc : D.base.cfg.size = 32)
    (sto : List (Bool × ℕ × OpenB))
    (hs : StoOK O D.base.cfg D.a D.base.plan.salt r0 r1 sto) :
    sExtP (256 + 8 * D.base.plan.salt) (weX D.a) (fun p => decide (p ∈ readOf D.a sto))
      (extOf D.a D.base.cfg (tabsOf sto)) = true := by
  refine Compile.Cmpl.strictExt_of (weX D.a) fun p op hop => ?_
  obtain ⟨e, he, hw, c, s, pt, hm, rfl⟩ := extOf_found D.a D.base.cfg sto p op hop
  have hidx : p.elim (·.val) (·.val) ∈ e.2.2.idx := (List.of_mem_zip hm).1
  have hsalt : s ∈ e.2.2.salts :=
    (List.of_mem_zip (List.of_mem_zip (List.of_mem_zip hm).2).2).1
  have hsize : s.size = D.base.plan.salt :=
    (TieTree.ok_spec e.2.2 D.base.plan.salt e.2.1 (hs.ok e he)).2.2.1 s hsalt
  have hpos : xPos (2 ^ D.a) (e.1, p.elim (·.val) (·.val)) = some p := by
    rw [hw]
    exact xPos_back (2 ^ D.a) p
  refine ⟨decide_eq_true (mem_readOf D.a sto e he _ hidx p hpos), ?_⟩
  show (leafSalt D.base.cfg s).length = 256 + 8 * D.base.plan.salt
  rw [length_leafSalt, hc, hsize]

/-- Given `StoOK`: at a place that an opening of sto lists, the string that the verifier builds
holds the place and the listed column. -/
theorem ext_symbol (r0 r1 : ByteArray) (sto : List (Bool × ℕ × OpenB))
    (hs : StoOK O D.base.cfg D.a D.base.plan.salt r0 r1 sto) (e : Bool × ℕ × OpenB)
    (he : e ∈ sto) (x : ℕ) (col : List UInt64) (hx : (x, col) ∈ e.2.2.idx.zip e.2.2.cols) :
    ∃ p, xPos (2 ^ D.a) (e.1, x) = some p ∧
      (twoExternalStrings (2 ^ D.a) SgX).rd ((weX D.a).build fun p =>
                      (extOf D.a D.base.cfg (tabsOf sto) p).map Opening.sym) p = (x, col) := by
  have hlt : x < 2 ^ D.a := by
    rw [← hs.depth e he]
    exact (TieTree.ok_list e.2.2 D.base.plan.salt e.2.1 (hs.ok e he)).2.1 x (List.of_mem_zip hx).1
  obtain ⟨p, hp, hw, hv⟩ := xPos_at (2 ^ D.a) e.1 x hlt
  obtain ⟨s, pt, hat⟩ := extOf_at_listed D.a D.base.cfg D.base.plan.salt sto hs.once e he
    (hs.ok e he) x col hx p hw hv
  have hsym : (extOf D.a D.base.cfg (tabsOf sto) p).map Opening.sym = some (x, col) := by
    rw [hat]
    rfl
  exact ⟨p, hp, (WireE.two_ok (2 ^ D.a) SgX (0, [])).build_rd
    (fun p => (extOf D.a D.base.cfg (tabsOf sto) p).map Opening.sym) p (x, col) hsym⟩

end

end OnBytes.Tie

#print axioms OnBytes.Tie.two_strings
#print axioms OnBytes.Tie.run_two
#print axioms OnBytes.Tie.famX_leaf
#print axioms OnBytes.Tie.famX_node
#print axioms OnBytes.Tie.ext_forest
#print axioms OnBytes.Tie.ext_strict
#print axioms OnBytes.Tie.ext_symbol
