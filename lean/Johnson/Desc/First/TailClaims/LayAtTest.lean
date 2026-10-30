-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/LayAtTest.lean: a test with code for InSig (LayAt.lean): that every
early cell which has a seat has it at a place of a member of the sending's signature. The members
are handed in as a plain list (each: the message's number, its shape, its tree and tenant); the test
goes array by array and block by block, not cell by cell.

Definitions with code, statements and proofs.
What of a code's record is read: one number, ell, the message's length (Johnson.Pack.pMain cs
s).ell, as a bound on an index: a member's main places are Fin s.mainRows × Fin ell
(Johnson/Pack/Port.lean). Nothing is stated or proved on encoding, distance, radius, lists or
decoders. A radius for each member (the letter rad) is handed on into LayAt.lean's letter l, unread.
Main names:
  Mem: a member: the message's number; its shape; (tree, tenant).
  lOf rad mem, seatAt rad mem, copyOf mem: LayAt.lean's letters l, seat' and copy, read off the
    list.
  blockIn s ell b: the block b of an array lies inside a message of the shape s: its last row is
    below s.mainRows and its places end at or below ell.
  inSigB cs layout num own arr mem ts: for every array t of ts that the layout has: a member has the
    number of its message; arr at that member's tree and tenant is that number; every block of the
    array lies inside.
  inSigAllB: the strict form: ts is not empty, the layout has every array of it, and inSigB says
    yes.
  arraysOf tl, early_arraysOf: the arrays whose cells are early, as a list; every early cell's array
    is in it.
  laidIn_bound: where a block holds an element, inside which row and places.
  **inSig_of_test**: the test's yes, with "every early cell's array is in ts", gives InSig at these
    letters.
  inSig_of_test_early: the same at ts := arraysOf tl0, without that premise.
Limits. An array of ts that the layout does not have passes: its cells have no seat, and InSig asks
nothing of them. So a yes of inSigB can be a yes on nothing: at ts = [], or where own gives names
that the layout lacks (two examples at the file's end): whoever wants a member at a real plan asks
inSigAllB. The test is sufficient, not necessary: it bounds a block by its whole size, used or not.
Where two members have one number, the first is taken. layout, num, own, arr, rad, cs, maskSeat, J
and Y stay letters: that they are the plan's is asked by nothing here. The test has been run at a
toy alone (nine examples at the file's end): at no real plan. All limits of LayAt.lean stand.


Sources. The three lines that prove mul_add_lt are equal, but for names or language, to lines of
the Lean library ArkLib (https://github.com/Verified-zkEVM/ArkLib; Apache-2.0),
ArkLib/Commitments/Functional/Hachi/ZeroCheck/Constraints.lean, lines 420 to 422 (Copyright (c)
2024-2026 ArkLib Contributors), and of VCV-io (Apache-2.0),
LatticeCrypto/MLDSA/Concrete/Encoding.lean, lines 448 to 450 and 306 to 309 (Copyright (c) 2026
Quang Dao). The lemma with its statement takes the same steps, in other statements, as
batteries' Batteries/Data/Nat/Lemmas.lean, lines 216 to 221
(Copyright (c) 2016 Microsoft Corporation), and Mathlib's Mathlib/Logic/Equiv/Fin/Basic.lean, lines
332 to 336 (Copyright (c) 2018 Kenny Lau). The writer of this file, an AI system, had seen
ArkLib's source.
On these works: lean/CREDITS.md, sections 2, 3 and 4.

-/
import Johnson.Desc.First.TailClaims.LayAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Road.Rows Johnson.Pack OnBytes.Tie.Pv.Tail
open OnBytes.Params (LaidBlock ReqArray ReqLayout)
open VerifiableInference.Desc VerifiableInference.Desc.Sound

/-- A member: the message's number; its shape; (tree, tenant). -/
abbrev Mem : Type := ℕ × OnBytes.OracleShape × (ℕ × ℕ)

/-- The members' shapes, each with a radius. -/
def lOf (rad : OnBytes.OracleShape → ℕ) (mem : List Mem) : List (OnBytes.OracleShape × ℕ) :=
  mem.map fun m => (m.2.1, rad m.2.1)

theorem lOf_length (rad : OnBytes.OracleShape → ℕ) (mem : List Mem) :
    (lOf rad mem).length = mem.length := by simp [lOf]

/-- Their trees and tenants. -/
def seatAt (rad : OnBytes.OracleShape → ℕ) (mem : List Mem) (i : Fin (lOf rad mem).length) :
    ℕ × ℕ :=
  (mem.get ⟨i.1, (lOf_length rad mem) ▸ i.2⟩).2.2

/-- The copy of a message's number: the first member that has it. -/
def copyOf (mem : List Mem) (n : ℕ) : OnBytes.OracleShape × ℕ × ℕ :=
  match mem.find? fun m => m.1 == n with
  | some m => (m.2.1, m.2.2.1, m.2.2.2)
  | none => (default, 0, 0)

/-- The block lies inside a message of the shape s whose main rows have ell places. -/
def blockIn (s : OnBytes.OracleShape) (ell : ℕ) (b : LaidBlock) : Bool :=
  decide (b.firstRow + (2 ^ (b.bitsI + b.bitsC) - 1) / 2 ^ b.placeBits < s.mainRows) &&
    decide (b.firstPlace + 2 ^ b.placeBits ≤ ell)

/-- **The test.** -/
def inSigB (cs : OnBytes.Codes) (layout : ReqLayout) (num : ℕ → ℕ → ℕ) (own : ℕ → ℕ × String)
    (arr : ℕ → ℕ → ℕ) (mem : List Mem) (ts : List ℕ) : Bool :=
  ts.all fun t =>
    match arrayOf layout (own t).1 (own t).2 with
    | none => true
    | some a =>
      match mem.find? fun m => m.1 == num (own t).1 a.message with
      | none => false
      | some m => arr m.2.2.1 m.2.2.2 == m.1 && a.blocks.all (blockIn m.2.1 (pMain cs m.2.1).ell)

/-- The arrays whose cells are early: the matrices' symbol arrays and the vectors that are there. -/
def arraysOf (tl : HTailF2) : List ℕ :=
  tl.gtTree.toList ++ (List.range 4).filterMap fun n => tl.ix.U.getD n none

/-- Every early cell's array is among them. -/
theorem early_arraysOf {tl : HTailF2} {t r c : ℕ} (h : early tl (.cell t r c) = true) :
    t ∈ arraysOf tl := by
  unfold early at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  unfold arraysOf
  rcases h with h | h
  · exact List.mem_append_left _ h
  · refine List.mem_append_right _ (List.mem_filterMap.2 ?_)
    obtain ⟨i, hi, e⟩ := List.mem_take_iff_getElem.1 h
    refine ⟨i, List.mem_range.2 (by omega), ?_⟩
    have hlt : i < tl.ix.U.size := by
      have := hi
      simp only [Array.length_toList] at this
      omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
    simpa using e

/-- The strict form: the list is not empty, and the layout has every array of it. -/
def inSigAllB (cs : OnBytes.Codes) (layout : ReqLayout) (num : ℕ → ℕ → ℕ) (own : ℕ → ℕ × String)
    (arr : ℕ → ℕ → ℕ) (mem : List Mem) (ts : List ℕ) : Bool :=
  !ts.isEmpty && (ts.all fun t => (arrayOf layout (own t).1 (own t).2).isSome) &&
    inSigB cs layout num own arr mem ts

theorem inSigB_of_all {cs : OnBytes.Codes} {layout : ReqLayout} {num : ℕ → ℕ → ℕ}
    {own : ℕ → ℕ × String} {arr : ℕ → ℕ → ℕ} {mem : List Mem} {ts : List ℕ}
    (h : inSigAllB cs layout num own arr mem ts = true) :
    inSigB cs layout num own arr mem ts = true := by
  unfold inSigAllB at h
  exact (Bool.and_eq_true _ _ ▸ h).2

theorem mul_add_lt {a b A B : ℕ} (ha : a < A) (hb : b < B) : a * B + b < A * B :=
  calc a * B + b < a * B + B := by omega
    _ = (a + 1) * B := by ring
    _ ≤ A * B := Nat.mul_le_mul_right B ha

/-- Where a block holds an element: inside which row and places. -/
theorem laidIn_bound {b : LaidBlock} {i c p q : ℕ} (h : laidIn b i c = some (p, q)) :
    p ≤ b.firstRow + (2 ^ (b.bitsI + b.bitsC) - 1) / 2 ^ b.placeBits ∧
      q < b.firstPlace + 2 ^ b.placeBits := by
  unfold laidIn at h
  split at h
  · rename_i hc
    obtain ⟨h1, h2, h3, h4⟩ := hc
    have hi : i - b.firstI < 2 ^ b.bitsI := by omega
    have hcc : c - b.firstC < 2 ^ b.bitsC := by omega
    have hx : (if b.iIsLow then (c - b.firstC) * 2 ^ b.bitsI + (i - b.firstI)
        else (i - b.firstI) * 2 ^ b.bitsC + (c - b.firstC)) < 2 ^ (b.bitsI + b.bitsC) := by
      rw [pow_add]
      split
      · rw [Nat.mul_comm (2 ^ b.bitsI)]
        exact mul_add_lt hcc hi
      · exact mul_add_lt hi hcc
    have e := Option.some.inj h
    have e1 : p = _ := (congrArg Prod.fst e).symm
    have e2 : q = _ := (congrArg Prod.snd e).symm
    have hpos : 0 < 2 ^ b.placeBits := Nat.pow_pos (by omega)
    refine ⟨?_, ?_⟩
    · rw [e1]
      exact Nat.add_le_add_left (Nat.div_le_div_right (by omega)) _
    · rw [e2]
      exact Nat.add_lt_add_left (Nat.mod_lt _ hpos) _
  · cases h

/-- **The test's yes gives InSig.** -/
theorem inSig_of_test {J : Type} (cs : OnBytes.Codes) (layout : ReqLayout) (num : ℕ → ℕ → ℕ)
    (own : ℕ → ℕ × String) (arr : ℕ → ℕ → ℕ) (rad : OnBytes.OracleShape → ℕ) (mem : List Mem)
    (ts : List ℕ) (maskSeat : ℕ → Option Seat) (Y : Lay J) (tl0 : HTailF2)
    (hts : ∀ t r c, early tl0 (.cell t r c) = true → t ∈ ts)
    (h : inSigB cs layout num own arr mem ts = true) :
    InSig cs (seatOf layout num own (copyOf mem) maskSeat) Y (lOf rad mem) (seatAt rad mem) arr
      tl0 := by
  intro j a he hs
  cases hA : Y.addr j with
  | mask s => rw [hA] at he; exact absurd he (by simp [early])
  | cell t r c =>
    rw [hA] at he hs
    have ht := List.all_eq_true.1 h t (hts t r c he)
    unfold seatOf at hs
    obtain ⟨⟨n, p, q⟩, hsi, rfl⟩ := Option.map_eq_some_iff.1 hs
    unfold seatIn at hsi
    obtain ⟨A, hAr, hl⟩ := Option.bind_eq_some_iff.1 hsi
    obtain ⟨⟨p', q'⟩, hla, e⟩ := Option.map_eq_some_iff.1 hl
    obtain ⟨rfl, rfl, rfl⟩ : num (own t).1 A.message = n ∧ p' = p ∧ q' = q := by
      simpa [Prod.ext_iff] using e
    simp only [hAr] at ht
    cases hm : mem.find? (fun m => m.1 == num (own t).1 A.message) with
    | none => simp [hm] at ht
    | some m =>
      simp only [hm, Bool.and_eq_true, beq_iff_eq] at ht
      obtain ⟨harr, hbl⟩ := ht
      have hn : m.1 = num (own t).1 A.message := by simpa using List.find?_some hm
      obtain ⟨b, hb, hbi⟩ := List.exists_of_findSome?_eq_some hla
      have hin := List.all_eq_true.1 hbl b hb
      unfold blockIn at hin
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
      obtain ⟨b1, b2⟩ := laidIn_bound hbi
      obtain ⟨i, hi⟩ := List.mem_iff_get.1 (List.mem_of_find?_eq_some hm)
      have hlen : i.1 < (lOf rad mem).length := (lOf_length rad mem).symm ▸ i.2
      have hget : (lOf rad mem).get ⟨i.1, hlen⟩ = (m.2.1, rad m.2.1) := by
        simp only [lOf, List.get_eq_getElem, List.getElem_map]
        rw [← List.get_eq_getElem, hi]
      have hseat : seatAt rad mem ⟨i.1, hlen⟩ = m.2.2 := by
        unfold seatAt
        exact congrArg (fun x : Mem => x.2.2) hi
      have hp : p' < ((lOf rad mem).get ⟨i.1, hlen⟩).1.mainRows := by
        rw [hget]
        exact Nat.lt_of_le_of_lt b1 hin.1
      have hq : q' < (pMain cs ((lOf rad mem).get ⟨i.1, hlen⟩).1).ell := by
        rw [hget]
        exact Nat.lt_of_lt_of_le b2 hin.2
      refine ⟨⟨⟨i.1, hlen⟩, (Sum.inl (⟨p', hp⟩, ⟨q', hq⟩) :
        (Fin _ × Fin _) ⊕ (Fin _ × Fin _))⟩, ?_⟩
      show ((((lOf rad mem).get ⟨i.1, hlen⟩).1, arr (seatAt rad mem ⟨i.1, hlen⟩).1
        (seatAt rad mem ⟨i.1, hlen⟩).2, (seatAt rad mem ⟨i.1, hlen⟩).1,
        (seatAt rad mem ⟨i.1, hlen⟩).2, false, p', q') : Seat) = _
      rw [hget, hseat, harr, hn]
      simp only [copyOf, hm]

/-- The same at the list of the early arrays. -/
theorem inSig_of_test_early {J : Type} (cs : OnBytes.Codes) (layout : ReqLayout) (num : ℕ → ℕ → ℕ)
    (own : ℕ → ℕ × String) (arr : ℕ → ℕ → ℕ) (rad : OnBytes.OracleShape → ℕ) (mem : List Mem)
    (maskSeat : ℕ → Option Seat) (Y : Lay J) (tl0 : HTailF2)
    (h : inSigB cs layout num own arr mem (arraysOf tl0) = true) :
    InSig cs (seatOf layout num own (copyOf mem) maskSeat) Y (lOf rad mem) (seatAt rad mem) arr
      tl0 :=
  inSig_of_test cs layout num own arr rad mem _ maskSeat Y tl0 (fun _ _ _ he => early_arraysOf he) h

/-! ## A toy: the test says yes, and it can say no -/

section Toy

/-- One code of messages of 8 places; one shape of 4 main rows. -/
def toyCs : OnBytes.Codes :=
  { (default : OnBytes.Codes) with base := #[{ (default : OnBytes.Code) with ell := 8 }] }
def toyShape : OnBytes.OracleShape :=
  { (default : OnBytes.OracleShape) with code := 0, mainRows := 4 }
/-- An array of 4 rows and 8 columns in one block: rows 0 to 3, places 0 to 7. -/
def toyBlock : LaidBlock :=
  { firstI := 0, firstC := 0, firstRow := 0, firstPlace := 0, bitsI := 2, bitsC := 3, rowBits := 2,
    placeBits := 3, iIsLow := false }
def toyLayout (b : LaidBlock) : ReqLayout :=
  { link := [[{ name := "M", message := 0, sizeI := 4, sizeC := 8, blocks := [b] }]] }
def toyMem : List Mem := [(7, toyShape, (2, 1))]
/-- The test at the toy: the block b; the array's name; n: the number of its message; a: the number
that the book has at every tree and tenant. -/
def toyB (b : LaidBlock) (name : String) (n a : ℕ) (mem : List Mem) (ts : List ℕ) : Bool :=
  inSigB toyCs (toyLayout b) (fun _ _ => n) (fun _ => (0, name)) (fun _ _ => a) mem ts
def toyAllB (b : LaidBlock) (name : String) (n a : ℕ) (mem : List Mem) (ts : List ℕ) : Bool :=
  inSigAllB toyCs (toyLayout b) (fun _ _ => n) (fun _ => (0, name)) (fun _ _ => a) mem ts

/-- Yes: the message has the number 7; the member has it, at tree 2, tenant 1; the block fits. -/
example : toyB toyBlock "M" 7 7 toyMem [5] = true := by decide
/-- The strict form says yes there too. -/
example : toyAllB toyBlock "M" 7 7 toyMem [5] = true := by decide
/-- No: the block begins one row lower: its last row is row 4. -/
example : toyB { toyBlock with firstRow := 1 } "M" 7 7 toyMem [5] = false := by decide
/-- No: the block begins one place further: its places end at 9. -/
example : toyB { toyBlock with firstPlace := 1 } "M" 7 7 toyMem [5] = false := by decide
/-- No: no member has the message's number. -/
example : toyB toyBlock "M" 6 7 toyMem [5] = false := by decide
/-- No: the book has another message at the member's tree and tenant. -/
example : toyB toyBlock "M" 7 6 toyMem [5] = false := by decide
/-- A YES ON NOTHING: a name that the layout lacks, and no member at all. -/
example : toyB toyBlock "N" 7 7 [] [5] = true := by decide
/-- The strict form says no there; -/
example : toyAllB toyBlock "N" 7 7 [] [5] = false := by decide
/-- and at the empty list, where the plain form says yes. -/
example : toyB toyBlock "M" 7 7 toyMem [] = true ∧ toyAllB toyBlock "M" 7 7 toyMem [] = false := by
  decide

end Toy

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.early_arraysOf
#print axioms VerifiableInference.Desc.First.TailClaims.Law.inSig_of_test_early
#print axioms VerifiableInference.Desc.First.TailClaims.Law.laidIn_bound
#print axioms VerifiableInference.Desc.First.TailClaims.Law.inSig_of_test
