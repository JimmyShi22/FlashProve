-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidSeatsOf.lean: the seats that the plan's item "layout" gives are a function
of the label.

The sums means_follows (Johnson/Goal/Meaning/HidPlanFit.lean) and means_followsF
(Johnson/Goal/Meaning/HidFamily.lean) take the seats in the form seatBy f X s: a function f of the
entry's label. The verifier's public record X holds the 25 plans and no laying: in which oracle
message, row and place an array's element lies stands in the plan's item "layout"
(OnBytes/Params/Items.lean: ReqLayout), which seatIn (Johnson/Desc/LaidAt.lean) reads: link, array's
name, row and column ↦ the message's number in the witness, its main row, its place. An array that a
later link borrows stands in its OWNER's link's list.

This file makes the seats of all 25 sub-proofs from that reader, the owner taken STRUCTURALLY, off
the 24 pairs of reader and owner, and proves, in scope, that they are seatBy f at one f.

Main names:
  ownerOf X k a   the sub-proof that owns entry a of sub-proof k's list, and the entry's number
    there: the stream that comes into a later group: the stream that goes out of the group before;
    attention's copy of qa: the group's qa; the head's copy of the stream: the stream that goes out
    of group 11; every other entry: itself.
  owner_label   IN SCOPE THE LABEL NAMES THAT OWNER: (ownerK lab, ownerA lab) = ownerOf X k a at lab
    := labAt X k a.
  nameOf a   the array's name in the layout: "M" and its number.
  seatsOf X s layout num k   the seats of sub-proof k: seatIn at the owner's link and the owner's
    array.
  fLay layout num   the one function of the label.
  seatsOf_eq   IN SCOPE, at sizes that follow the plans: seatsOf X s layout num k = seatBy (fLay
    layout num) X s k for k < 25.
  laidThere X s layout   A TEST ON PUBLIC LETTERS, with code: for every entry of the 25 lists the
    array that its label names is there, has the entry's rows of symbols and columns, and is laid at
    all its elements.
  seat_of_laidThere   under that test no default is read: within the sizes every seat is what seatIn
    gives.

What is not claimed. That the programs read a borrowed array at its owner's seat; that sub-proof k
is link k of the layout, and that entry a's array bears the name "M" and a: these three are read in
the format's pages, not proved. num is a letter. seatIn gives an Option: WHERE IT GIVES NOTHING THE
SEAT HERE IS (0, 0, 0), IN SILENCE: laidThere is the test that bars it; IT HAS RUN AT NO LAYOUT.
That an array's blocks overlap nobody and miss the pad is the library's test reqLayoutOk
(OnBytes/Iop/ReqRows.lean), not said again here. The full size alone. The program does not import
this file.
-/
import Johnson.Goal.Meaning.HidOwner
import Johnson.Desc.LaidAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay matIx)
open OnBytes.Params (ReqLayout)
open VerifiableInference.Desc (seatIn arrayOf laidAt)
open Cb.Pv.Tail (Size)

/-- The sub-proof that owns entry a of sub-proof k's list, and the entry's number there. -/
def ownerOf (X : Model.Verify.Public) (k a : ℕ) : ℕ × ℕ :=
  if k = 24 then (if a = X.hS.NHf + 3 then (22, (matIx X.y).iXO) else (k, a))
  else if k % 2 = 1 then
    (if a = (Hd.shapeA X (k / 2)).cf.NAs + 3 then (k - 1, (matIx X.y).iQA) else (k, a))
  else if a = (matIx X.y).iXI ∧ 0 < k then (k - 2, (matIx X.y).iXO) else (k, a)

section Core
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **In scope the label names the owner.** -/
theorem owner_label (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {k a : ℕ}
    (hk : k < 25) (ha : a < (matsAt X k).size) :
    (ownerK (labAt X k a), ownerA (labAt X k a)) = ownerOf X k a := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  have hN : X.hS.NHf = 4 := (Hd.numH_of_layout B.full B.head).NHf
  obtain ⟨i6, i7, i8⟩ := ix_of_core h C
  unfold ownerOf
  by_cases h24 : k = 24
  · subst h24
    rw [if_pos rfl]
    rw [size_head h C] at ha
    by_cases e : a = 7
    · subst e
      have L : labAt X 24 7 = (1 + 11) * 256 + 7 := by
        rw [lab_head h C ha]
        unfold Hd.labH labA
        rw [hN, B.groups, i7, i8, if_pos rfl, if_neg (by omega)]
      obtain ⟨o1, o2⟩ := owner_of (1 + 11) 7 (by norm_num)
      rw [if_pos (by rw [hN]), L, o1, o2, linkOf_group (by norm_num), i7]
    · have L : labAt X 24 a = 13 * 256 + a := by
        rw [lab_head h C ha]
        unfold Hd.labH
        rw [hN, B.groups, if_neg (by omega)]
      obtain ⟨o1, o2⟩ := owner_of 13 a (by omega)
      rw [if_neg (by rw [hN]; omega), L, o1, o2]
      rfl
  · rw [if_neg h24]
    by_cases hev : k % 2 = 1
    · rw [if_pos hev]
      obtain ⟨g, rfl⟩ : ∃ g, k = 2 * g + 1 := ⟨k / 2, by omega⟩
      have hg : g < 12 := by omega
      rw [size_odd h C hg] at ha
      obtain ⟨i, -, n1, -⟩ := matsAt_att_gid h C hg
      rw [show (2 * g + 1) / 2 = g by omega, n1]
      by_cases e : a = 4
      · subst e
        obtain ⟨M, a1, -, -, a4⟩ := entryA h C hg
        rw [n1] at a1
        have L : labAt X (2 * g + 1) 4 = (1 + g) * 256 + 6 := by
          unfold labAt
          rw [getD_of a1, a4]
          unfold labA
          rw [i6, i8, if_neg (by omega)]
        obtain ⟨o1, o2⟩ := owner_of (1 + g) 6 (by norm_num)
        rw [if_pos rfl, L, o1, o2, linkOf_group hg, i6]
        rfl
      · obtain ⟨o1, o2⟩ := owner_of (14 + g) a (by omega)
        rw [if_neg (by omega), lab_odd h C hg (by omega : a < 4), o1, o2, linkOf_att]
    · rw [if_neg hev]
      obtain ⟨g, rfl⟩ : ∃ g, k = 2 * g := ⟨k / 2, by omega⟩
      have hg : g < 12 := by omega
      rw [size_even h C hg] at ha
      rw [i7, i8]
      by_cases e : a = 8 ∧ g ≠ 0
      · have L : labAt X (2 * g) a = (1 + (g - 1)) * 256 + 7 := by
          rw [lab_even h C hg ha]
          unfold labA
          rw [i7, i8, if_pos e, show 1 + (g - 1) = g by omega]
        obtain ⟨o1, o2⟩ := owner_of (1 + (g - 1)) 7 (by norm_num)
        rw [if_pos ⟨e.1, by omega⟩, L, o1, o2, linkOf_group (by omega)]
        congr 1
        omega
      · have L : labAt X (2 * g) a = (1 + g) * 256 + a := by
          rw [lab_even h C hg ha]
          unfold labA
          rw [i8, if_neg e]
        obtain ⟨o1, o2⟩ := owner_of (1 + g) a (by omega)
        rw [if_neg (fun k => e ⟨k.1, by omega⟩), L, o1, o2, linkOf_group hg]

end Core

/-- The array's name in the layout. -/
def nameOf (a : ℕ) : String := "M" ++ toString a

/-- **The seats of sub-proof k, off the layout**: the reader seatIn at the owner's link and the
owner's array. (0, 0, 0) where the reader gives nothing. -/
def seatsOf (X : Model.Verify.Public) (s : ℕ → Size) (layout : ReqLayout) (num : ℕ → ℕ → ℕ)
    (k : ℕ) : Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ := fun μ i c =>
  (seatIn layout num (ownerOf X k μ.val).1 (nameOf (ownerOf X k μ.val).2) i c).getD (0, 0, 0)

/-- The one function of the label. -/
def fLay (layout : ReqLayout) (num : ℕ → ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ := fun lab i c =>
  (seatIn layout num (ownerK lab) (nameOf (ownerA lab)) i c).getD (0, 0, 0)

/-- **In scope the seats off the layout are a function of the label.** -/
theorem seatsOf_eq {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {s : ℕ → Size} (F : Follows X s)
    (layout : ReqLayout) (num : ℕ → ℕ → ℕ) {k : ℕ} (hk : k < 25) :
    seatsOf X s layout num k = seatBy (fLay layout num) X s k := by
  funext μ i c
  have e := owner_label h C hk (a := μ.val) (by rw [← F.NM k hk]; exact μ.isLt)
  unfold seatsOf seatBy fLay
  rw [← e]

/-! ## The fence of the silent (0, 0, 0) -/

/-- **A test on public letters alone** (the record X, the sizes s, the layout): for every entry of
the 25 lists the array that its label names is there in the layout, has the entry's rows of symbols
and columns, and is laid at every one of its elements. -/
def laidThere (X : Model.Verify.Public) (s : ℕ → Size) (layout : ReqLayout) : Bool :=
  (List.range 25).all fun k => (List.range (s k).NM).all fun a =>
    match arrayOf layout (ownerK (labAt X k a)) (nameOf (ownerA (labAt X k a))) with
    | none => false
    | some A => A.sizeI == Alg.symRows ((s k).m a) && A.sizeC == (s k).k a &&
        (List.range A.sizeI).all fun i => (List.range A.sizeC).all fun c => (laidAt A i c).isSome

/-- **Under that test no default is read**: within the sizes every seat is what the layout's reader
gives. -/
theorem seat_of_laidThere {X : Model.Verify.Public} {s : ℕ → Size} {layout : ReqLayout}
    (T : laidThere X s layout = true) (num : ℕ → ℕ → ℕ) {k : ℕ} (hk : k < 25) (μ : Fin (s k).NM)
    {i c : ℕ} (hi : i < Alg.symRows ((s k).m μ)) (hc : c < (s k).k μ) :
    ∃ A x, arrayOf layout (ownerK (labAt X k μ.val)) (nameOf (ownerA (labAt X k μ.val))) = some A ∧
      A.sizeI = Alg.symRows ((s k).m μ) ∧ A.sizeC = (s k).k μ ∧ laidAt A i c = some x ∧
      seatBy (fLay layout num) X s k μ i c =
        (num (ownerK (labAt X k μ.val)) A.message, x.1, x.2) := by
  unfold laidThere at T
  rw [List.all_eq_true] at T
  have T1 := T k (List.mem_range.2 hk)
  rw [List.all_eq_true] at T1
  have T2 := T1 μ.val (List.mem_range.2 μ.isLt)
  cases hA : arrayOf layout (ownerK (labAt X k μ.val)) (nameOf (ownerA (labAt X k μ.val))) with
  | none =>
    simp only [hA] at T2
    cases T2
  | some A =>
    simp only [hA, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at T2
    obtain ⟨⟨e1, e2⟩, T3⟩ := T2
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (T3 i (e1 ▸ hi) c (e2 ▸ hc))
    refine ⟨A, x, rfl, e1, e2, hx, ?_⟩
    unfold seatBy fLay seatIn
    rw [hA]
    simp [hx]

end Meaning

#print axioms Meaning.owner_label
#print axioms Meaning.seatsOf_eq
#print axioms Meaning.seat_of_laidThere
