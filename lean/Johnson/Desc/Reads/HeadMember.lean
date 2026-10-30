-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/HeadMember.lean: the statement of the row claim_read_same_index at the output
head's link has a member, with a state at which the tables are closed; and it fails of the same
letters with the bytes of the number paid turned in the form clip.

All of this file is a tool: the letters here are a toy and name no description of the protocol. The
toy shows that the statement at the head (`HeadClaimByDecls`, Reads/HeadStated.lean) can be met, so
that the cases in which it fails are cases of a statement that is not empty; and that the premises
of `head_of_parts` (Reads/HeadAddressed.lean) can be met together.

The toy.
  `memberToy`: the kind's sizes are the full size's (1,024 positions, blocks of 64 features, 5,120
    features, 202,048 vocabulary entries). `verify-on-bytes`'s records h and L have the numbers that
    `NumH` (Johnson/Road/HeadPlace.lean) asks. The record of the smallness test has six matrices:
    four parts of wide, then act, then row, with these rows and columns. The seat lays the five
    reads one behind the other from place 0 on. The reading is the library's `Reading.gl`. The
    request covers all positions; no point is heard. There is one state, and the tables are closed
    at it.
  `memberFuns`: the list of tables is made from the five declarations (`funsOf`, Reads/FunsOf.lean):
    eleven tables. The record holds that list as its own. So the join is true by make here: the toy
    says nothing on a list that a verifier lays.

What is shown of it.
  `member_num`, `member_seat`: `NumH` and `SeatFits` hold.
  `member_hf`, `member_allU3B`: the two premises of Reads/Bridge.lean on the list of tables hold:
    the letter funs is the list of the state's record, and every table of it lies in the third
    vector.
  `member_laid`: the equation of Reads/DeclRow.lean and the test on lengths hold.
  `member_whole`, `member_fit`, `member_joined`: each of the five declarations is whole, its parts
    fit the record, and it is joined.
  `member_ne`, `member_notEmpty`, `member_sane`: the letters are not empty, and sane.
  `head_member`, `head_member_claim`, `head_member_sane`: `HeadClaimByDecls`, `HeadClaim` and
    `ClaimSane` (Reads/Sane.lean) hold of it.
  `head_sane`: for all letters at the head, `HeadClaimByDecls` gives `ClaimSane`.
  `tooth_turned_row`: for all letters at the head: with the bytes of paid turned in clip
    (Reads/HeadTied.lean), under `IsReading` and `NotEmpty`, the row of Reads/Stated.lean fails.
  `tooth_member_turned`: so it fails at the toy's letters with the turned form.
  Tools. `mem_usesH`: what a use is. `bytesAt_ind`: `bytesAt` at the values 1 at one place and 0
    elsewhere.

Of OnBytes/Model/ this file names what Reads/HeadStated.lean names, and `Reading.gl`.

Limits. The toy is not a run's object: its seat, its number of U3, its rows of 64 entries, its
policy and its empty points are no plan's. Its tables are made from the declarations. Four forms of
35 are read. Nothing is said on what a verifier would say. Nothing on soundness.


-/
import Johnson.Desc.Reads.HeadAddressed
import Johnson.Desc.Reads.Join
import Johnson.Desc.Reads.FunsOf
import Johnson.Desc.Reads.Sane
import Johnson.Desc.Reads.SpentWorld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtHead

open Finset
open Cb.Pv.Tail
open OnBytes (E zeroE)
open OnBytes.Model (HTailF2 HFun Aff Reading)
open OnBytes.Road.Hd (NumH)
open VerifiableInference.Desc.Kinds
open Inst.Model.Head (nT nV)

/-! ## 1. Tools -/

/-- A use is a byte of a hidden number, below the number of its bytes, or a limb below 3 of a block
of table values. -/
theorem mem_usesH [iS : Head.Sizes] {u : Use} (h : u ∈ usesH) :
    (∃ cl x l, u = .byte cl x l ∧ l < x.bytes.2) ∨
      ∃ l blk, u = .ex l blk ∧ l < 3 ∧ blk < nV / Norm.S2 := by
  unfold usesH at h
  rcases List.mem_append.1 h with h | h
  · obtain ⟨cl, -, h⟩ := List.mem_flatMap.1 h
    obtain ⟨x, -, h⟩ := List.mem_flatMap.1 h
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 h
    exact Or.inl ⟨cl, x, l, rfl, List.mem_range.1 hl⟩
  · obtain ⟨l, hl, h⟩ := List.mem_flatMap.1 h
    obtain ⟨blk, hb, rfl⟩ := List.mem_map.1 h
    exact Or.inr ⟨l, blk, rfl, List.mem_range.1 hl, List.mem_range.1 hb⟩

/-- bytesAt at the values 1 at the place st + (NR + q) and 0 elsewhere. -/
theorem bytesAt_ind {K : Type} [CommRing K] (st d m q : ℕ) :
    bytesAt (fun p => if p = st + (NR + q) then (1 : K) else 0) st d m =
      if d ≤ q ∧ q < d + m then ((256 ^ (q - d) : ℕ) : K) else 0 := by
  show ∑ l ∈ range m, ((256 ^ l : ℕ) : K) *
    (if st + (NR + d + l) = st + (NR + q) then (1 : K) else 0) = _
  by_cases h : d ≤ q ∧ q < d + m
  · rw [if_pos h, Finset.sum_eq_single_of_mem (q - d) (Finset.mem_range.2 (by omega))
      (fun l _ hl => by rw [if_neg (by omega), mul_zero]), if_pos (by omega), mul_one]
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun l hl => by
      have hl' := Finset.mem_range.1 hl
      rw [if_neg (by omega), mul_zero]

/-- **With the bytes of paid turned in clip the row fails**, under IsReading and NotEmpty. -/
theorem tooth_turned_row {K : Type} [CommRing K] (P : HeadLetters K)
    (hR : IsReading (P.lettersWith fun l => 256 ^ (4 - l)))
    (hN : NotEmpty (P.lettersWith fun l => 256 ^ (4 - l))) :
    ¬ ClaimReadSameIndex (P.lettersWith fun l => 256 ^ (4 - l)) := by
  intro H
  obtain ⟨s, hs, -⟩ := hN.2 () (List.mem_singleton.2 rfl)
  exact tooth_turned_reading P hR (ne_of_notEmpty _ hN) s
    (H () (List.mem_singleton.2 rfl) s hs).2.2

/-! ## 2. The toy -/

/-- `verify-on-bytes`'s two records of the head's sizes, at the full size's numbers. -/
def memberH : OnBytes.Model.Head.Shape :=
  { (default : OnBytes.Model.Head.Shape) with lt := 10, NHf := 4, d := 5120 }
@[inherit_doc memberH]
def memberL : OnBytes.Model.Head.HL :=
  { m := 65536, k := 4816, mD := 16384, kD := 640, mR := 8192, kR := 15 }

/-- The smallness test's record without its list of tables: four parts of wide, then act, then
row. -/
def memberTl0 : HTailF2 :=
  { NM := 6,
    mats := #[{ m := 65536, k := 4816 }, { m := 65536, k := 4816 }, { m := 65536, k := 4816 },
      { m := 65536, k := 4816 }, { m := 16384, k := 640 }, { m := 8192, k := 15 }] }

/-- The seat: the five reads one behind the other. -/
def memberSeat : Seat where
  iU3 := 5
  cols := 64
  first := fun r => some (match r with
    | .wideAtKeys => 0 | .wideAtCosts => 19264 | .actAtLogits => 38528 | .rowAtCosts => 48768
    | .rowCount => 48888)
  count := fun r => match r with
    | .wideAtKeys => 19264 | .wideAtCosts => 19264 | .actAtLogits => 10240 | .rowAtCosts => 120
    | .rowCount => 120
  mat := fun M => match M with
    | .wide => (0, 4) | .act => (4, 1) | .row => (5, 1)

/-- The toy's letters, with a given record and a given list of tables. -/
noncomputable def toyWith (tl : HTailF2) (funs : Array HFun) : HeadLetters Cb.Gl.E where
  val := Reading.gl.val
  h := memberH
  L := memberL
  sizes :=
    { lt := 10, ls := 6, d := 5120, MF := 0, KF := 0, epsF := 0, V := 202048, sh := 7, F := 24 }
  policy := ⟨128, 128, 0⟩
  seat := memberSeat
  State := Unit
  AtClose := fun _ => True
  req := fun _ => ⟨0, 1024, fun _ => 0, ⟨128, 128, 0⟩⟩
  request := fun _ => ⟨fun _ => 0, 0, 1024⟩
  points := fun _ => ⟨#[], #[], fun _ _ => zeroE, fun _ _ => zeroE, fun _ => zeroE⟩
  heard := fun _ => ⟨{}⟩
  tl := fun _ => tl
  funs := fun _ => funs

/-- The five declarations; they do not read the list of tables. -/
noncomputable def memberDecls : List (ReadDecl E) := (toyWith memberTl0 #[]).decls ()

/-- The list of tables, made from the declarations. -/
noncomputable def memberFuns : Array HFun :=
  funsOf (OnBytes.Tie.Pv.Tail.sizeOf memberTl0) memberDecls

/-- The smallness test's record, with that list as its own. -/
noncomputable def memberTl : HTailF2 := { memberTl0 with funs := memberFuns }

/-- The toy. -/
noncomputable def memberToy : HeadLetters Cb.Gl.E := toyWith memberTl memberFuns

theorem member_decls : memberToy.decls () = memberDecls := rfl

/-- The letter funs is the list of the state's record. -/
theorem member_hf : memberToy.letters.funs () () = (memberToy.letters.tl () ()).funs := rfl

/-- Every table of that list lies in the third vector. -/
theorem member_allU3B : allU3B (memberToy.letters.tl () ()).funs = true :=
  allU3B_of (funsOf_tree _ _)

/-- The equation at the row's sizes and weights, and the test on lengths. -/
theorem member_laid :
    TablesAre (sizeU3 memberTl memberFuns) (phiU3 Reading.gl.val memberFuns) Reading.gl.val
        memberDecls ∧ lensB memberFuns = true :=
  tables_of_funs Reading.gl.val
    (funsAre_funsOf (OnBytes.Tie.Pv.Tail.sizeOf memberTl0) (sizeU3 memberTl memberFuns) rfl rfl
      memberDecls)

/-! ## 3. What is shown of it -/

theorem member_num : NumH memberToy.h memberToy.L where
  T := rfl
  NHf := rfl
  d := rfl
  m := rfl
  k := rfl
  fc := rfl
  mD := rfl
  kD := rfl
  fcD := rfl
  mR := rfl
  kR := rfl
  fcR := rfl

theorem member_seat : SeatFits memberToy () where
  T := rfl
  S2 := rfl
  d := rfl
  JV := rfl
  row := rfl
  wide := rfl
  mR := rfl
  kR := rfl
  m := rfl
  k := rfl
  count := fun u hu => by
    rcases mem_usesH (iS := memberToy.sizes) hu with ⟨cl, x, l, rfl, hl⟩ | ⟨l, blk, rfl, hl, hb⟩
    · have key : x.number.digits.1 + x.bytes.2 ≤ 21 := by cases x <;> decide
      have hc : memberToy.seat.count (Use.read (.byte cl x l)) = 120 := by cases cl <;> rfl
      rw [hc]
      show NR + x.number.digits.1 + l < 120
      have hN : NR = 99 := rfl
      omega
    · have hb' : blk < 202048 / 64 := hb
      show (4 * 5120 + (3 + l) * 202048) / 64 + blk < 19264
      omega

theorem member_whole (r : Head.Read) :
    (memberToy.decl () r).Whole ((memberToy.letters.size () ()).m (memberToy.decl () r).mat)
      ((memberToy.letters.size () ()).k (memberToy.decl () r).mat) := by
  cases r
  · exact ⟨(by decide : (0 : ℕ) < 2 ^ 6 * 2 ^ 10),
      (by decide : (19264 : ℕ) = 4 * (4816 * (65536 / (2 ^ 6 * 2 ^ 10)))),
      (by decide : 2 ^ 6 * (2 ^ 6 * 2 ^ 10 / 2 ^ 6) = 2 ^ 6 * 2 ^ 10),
      (by decide : 65536 / (2 ^ 6 * 2 ^ 10 / 2 ^ 6) = 65536 / (2 ^ 6 * 2 ^ 10) * 2 ^ 6)⟩
  · exact ⟨(by decide : (0 : ℕ) < 2 ^ 6 * 2 ^ 10),
      (by decide : (19264 : ℕ) = 4 * (4816 * (65536 / (2 ^ 6 * 2 ^ 10)))),
      (by decide : 2 ^ 6 * (2 ^ 6 * 2 ^ 10 / 2 ^ 6) = 2 ^ 6 * 2 ^ 10),
      (by decide : 65536 / (2 ^ 6 * 2 ^ 10 / 2 ^ 6) = 65536 / (2 ^ 6 * 2 ^ 10) * 2 ^ 6)⟩
  · exact ⟨(by decide : (0 : ℕ) < 2 ^ 10),
      (by decide : (10240 : ℕ) = 1 * (640 * (16384 / 2 ^ 10))), True.intro⟩
  · exact ⟨(by decide : (0 : ℕ) < 2 ^ 10),
      (by decide : (120 : ℕ) = 1 * (15 * (8192 / 2 ^ 10))), True.intro⟩
  · exact ⟨(by decide : (0 : ℕ) < 2 ^ 10),
      (by decide : (120 : ℕ) = 1 * (15 * (8192 / 2 ^ 10))), True.intro⟩

theorem fit_four (q : ℕ) (hq : q < 4) :
    (memberToy.letters.size () ()).m (0 + q) = (memberToy.letters.size () ()).m 0 ∧
      (memberToy.letters.size () ()).k (0 + q) = (memberToy.letters.size () ()).k 0 := by
  rcases q with _ | _ | _ | _ | q
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · omega

theorem member_fit (r : Head.Read) :
    PartsFit (memberToy.letters.size () ()) (memberToy.decl () r) := by
  cases r
  · exact ⟨(by decide : (0 : ℕ) + 4 ≤ 6), fit_four⟩
  · exact ⟨(by decide : (0 : ℕ) + 4 ≤ 6), fit_four⟩
  · refine ⟨(by decide : (4 : ℕ) + 1 ≤ 6), fun q hq => ?_⟩
    have hq' : q < 1 := hq
    obtain rfl : q = 0 := by omega
    exact ⟨rfl, rfl⟩
  · refine ⟨(by decide : (5 : ℕ) + 1 ≤ 6), fun q hq => ?_⟩
    have hq' : q < 1 := hq
    obtain rfl : q = 0 := by omega
    exact ⟨rfl, rfl⟩
  · refine ⟨(by decide : (5 : ℕ) + 1 ≤ 6), fun q hq => ?_⟩
    have hq' : q < 1 := hq
    obtain rfl : q = 0 := by omega
    exact ⟨rfl, rfl⟩

theorem member_joined (r : Head.Read) :
    Joined (memberToy.letters.size () ()) (memberToy.letters.phi () ()) memberToy.val
      (memberToy.decl () r) :=
  joined_of_tables member_laid.1
    (List.mem_map.2 ⟨r, read_mem r, rfl⟩) (member_fit r) (member_whole r)

/-- The part in U3 of the form mean is not the zero form: at the values 1 at the place of the low
byte of paid and 0 elsewhere it is 1. -/
theorem member_ne :
    u3Value Reading.gl.val memberToy.seat.iU3 memberToy.seat.cols (memberToy.form () .B2)
      (fun p => if p = memberToy.seat.start .rowCount + (NR + 0) then 1 else 0) ≠ 0 := by
  have e := (u3Value_part (ρ := Reading.gl) memberToy.seat.iU3 memberToy.seat.cols
    (fun p => if p = memberToy.seat.start .rowCount + (NR + 0) then 1 else 0)
    (memberToy.form () .B2)).trans
    (mean_part (iS := memberToy.sizes) (iP := memberToy.policy) (iR := memberToy.request ())
      Reading.gl memberToy.seat
      (fun p => if p = memberToy.seat.start .rowCount + (NR + 0) then 1 else 0))
  refine ne_of_eq_of_ne e ?_
  rw [bytesAt_ind, bytesAt_ind, bytesAt_ind, if_pos (by decide), if_neg (by decide),
    if_neg (by decide)]
  simp

theorem member_notEmpty : NotEmpty memberToy.letters :=
  ⟨List.cons_ne_nil _ _, fun _ _ => ⟨(), trivial, memberToy.form () .B2,
    List.mem_cons.2 (Or.inl rfl),
    fun p => if p = memberToy.seat.start .rowCount + (NR + 0) then 1 else 0, member_ne⟩⟩

theorem member_sane : memberToy.Sane :=
  ⟨fun r => by cases r <;> rfl, member_num, member_notEmpty, ⟨Reading.gl, rfl⟩⟩

/-- **The statement at the head has a member.** -/
theorem head_member : HeadClaimByDecls memberToy :=
  head_of_parts memberToy member_sane fun s _ => by
    cases s
    refine ⟨member_laid.2, fun d hd => ?_, member_seat,
      (by decide : (0 : ℕ) < 64), rfl⟩
    obtain ⟨r, -, rfl⟩ := List.mem_map.1 hd
    exact ⟨member_whole r, member_joined r⟩

theorem head_member_claim : HeadClaim memberToy := headClaim_of_decls _ head_member

/-- The statement at the head gives the row over declarations with what is owed beside it, for all
letters at the head. -/
theorem head_sane {K : Type} [CommRing K] (P : HeadLetters K) (H : HeadClaimByDecls P) :
    ClaimSane P.letters fun _ s => P.decls s :=
  ⟨H.2, H.1.2.2.1, H.1.2.2.2⟩

theorem head_member_sane : ClaimSane memberToy.letters fun _ s => memberToy.decls s :=
  head_sane memberToy head_member

/-- With the bytes of paid turned in clip, the toy's letters fail the row. -/
theorem tooth_member_turned :
    ¬ ClaimReadSameIndex (memberToy.lettersWith fun l => 256 ^ (4 - l)) := by
  refine tooth_turned_row memberToy ⟨Reading.gl, rfl⟩ ⟨List.cons_ne_nil _ _, fun _ _ => ?_⟩
  exact ⟨(), trivial, memberToy.form () .B2, List.mem_cons.2 (Or.inl rfl),
    fun p => if p = memberToy.seat.start .rowCount + (NR + 0) then 1 else 0, member_ne⟩

end VerifiableInference.Reads.AtHead

#print axioms VerifiableInference.Reads.AtHead.mem_usesH
#print axioms VerifiableInference.Reads.AtHead.bytesAt_ind
#print axioms VerifiableInference.Reads.AtHead.tooth_turned_row
#print axioms VerifiableInference.Reads.AtHead.member_decls
#print axioms VerifiableInference.Reads.AtHead.member_hf
#print axioms VerifiableInference.Reads.AtHead.member_allU3B
#print axioms VerifiableInference.Reads.AtHead.member_laid
#print axioms VerifiableInference.Reads.AtHead.member_num
#print axioms VerifiableInference.Reads.AtHead.member_seat
#print axioms VerifiableInference.Reads.AtHead.member_whole
#print axioms VerifiableInference.Reads.AtHead.fit_four
#print axioms VerifiableInference.Reads.AtHead.member_fit
#print axioms VerifiableInference.Reads.AtHead.member_joined
#print axioms VerifiableInference.Reads.AtHead.member_ne
#print axioms VerifiableInference.Reads.AtHead.member_notEmpty
#print axioms VerifiableInference.Reads.AtHead.member_sane
#print axioms VerifiableInference.Reads.AtHead.head_member
#print axioms VerifiableInference.Reads.AtHead.head_member_claim
#print axioms VerifiableInference.Reads.AtHead.head_sane
#print axioms VerifiableInference.Reads.AtHead.head_member_sane
#print axioms VerifiableInference.Reads.AtHead.tooth_member_turned
