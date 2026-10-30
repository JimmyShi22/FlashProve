-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/HeadAddressed.lean: at the output head's link: every use is addressed in the
declared read of the name that its clause means, under named premises on the seat; and what is then
left of the row at the head.

What is shown is a step of the row at the head: it speaks of the kind's written declarations and
forms, and of the relation's own addresses, at letters.
  `addressed_head`: the third clause of `ClaimByDecls` (Reads/DeclRow.lean) at the head's letters:
    for every use there is one of the five declarations, of the name that the use's clause means, in
    which the use is addressed: the place, the number of cells, each cell's address, each weight.
  `head_of_parts`: what is left. `HeadClaimByDecls P` (Reads/HeadStated.lean) follows from `P.Sane`
    and, at every state with closed tables: the test on lengths; each of the five declarations is
    whole and joined; `SeatFits`; a row of U3 has an entry; the request's C is the policy's C in K.

The premises on the seat, at a state s.
  `SeatFits P s`: the kind's sizes are the full size's (1,024 positions, blocks of 64 features,
    5,120 features, 202,048 padded vocabulary entries); the seat has the matrix wide first and the
    matrix row at the number NHf + 1, behind the parts of wide and the matrix act, as `cellsH`
    (Johnson/Road/HeadPlace.lean) has them; the smallness test's record has, at these two matrices,
    the rows and columns by which the relation's cells are addressed; and every use's index lies
    below the number of its read's entries.
None of this is shown here of any description. With `NumH`, which `P.Sane` holds, it ties the three
texts' sizes to one another.

Tools. `byte_cells`, `ex_cells`: the relation's address of a use's cell is the address that the
declaration's make gives at the use's index. `read_mem`: the five reads are all reads.

Of OnBytes/Model/ this file names what Reads/HeadStated.lean names.

Limits. That the declarations are whole and joined, and the test on lengths, stand on the smallness
test's side and are not shown. That the clauses of `SeatFits` can be met together, with `NumH`, is
shown at a toy in Reads/HeadMember.lean (`member_seat`), not here. Four forms of 35 are read.
Nothing on soundness.


-/
import Johnson.Desc.Reads.HeadTiedFour

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtHead

open OnBytes (E)
open OnBytes.Road.Hd (NumH)
open VerifiableInference.Desc.Kinds
open Inst.Model.Head (nT nV fEx)

/-! ## 1. The relation's address is the declaration's -/

section Sized
variable [iS : Head.Sizes] [iR : Head.Request] [iI : FinalNorm.In] [iH : Head.Heard]

/-- A byte of a hidden number: the relation's address of cell j is the address that the make short
gives at the use's index. -/
theorem byte_cells (S : Seat) (h : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL)
    (m k : ℕ) (cl : Clause) (x : Hid) (l j : ℕ) (hT : Norm.T = nT) (hhT : h.T = nT)
    (hrow : (S.mat .row).1 = h.NHf + 1) (hm : m = L.mR) (hk : k = L.kR) :
    Use.cell h L (.byte cl x l) j = (declOf S cl.read).cells m k (Use.index (.byte cl x l)) j := by
  have hb : x.bytes.1 = NR + x.number.digits.1 := congrArg Prod.fst (bytes_eq_digits x)
  cases cl <;>
    (show addrHr h L (x.bytes.1 + l) j =
        cellOf (S.mat .row).1 m k Norm.T (NR + x.number.digits.1 + l) j
     rw [hrow, hm, hk, hT, ← hhT, hb]
     rfl)

/-- A limb of the table values of a block: the relation's address of cell j is the address that the
make long gives at the use's index. -/
theorem ex_cells (S : Seat) (h : OnBytes.Model.Head.Shape) (L : OnBytes.Model.Head.HL)
    (m k l blk j : ℕ) (hT : Norm.T = nT) (hhT : h.T = nT) (hS2 : Norm.S2 = 64)
    (hd : Norm.d = 5120) (hJV : Head.JV = 202048) (hw : (S.mat .wide).1 = 0) (hm : m = L.m)
    (hk : k = L.k) :
    Use.cell h L (.ex l blk) j = (declOf S .wideAtCosts).cells m k (Use.index (.ex l blk)) j := by
  show addrHf h L (fEx l (Norm.S2 * blk + j / nT)) (j % nT) =
    cellOf (S.mat .wide).1 m k (Norm.S2 * Norm.T / Norm.S2)
      (Norm.S2 * ((4 * Norm.d + (3 + l) * Head.JV) / Norm.S2 + blk) +
        j / (Norm.S2 * Norm.T / Norm.S2)) (j % (Norm.S2 * Norm.T / Norm.S2))
  rw [hS2, hT, hd, hJV, hw, hm, hk]
  have e1 : 64 * nT / 64 = nT := Nat.mul_div_cancel_left _ (by decide)
  rw [e1]
  have e2 : fEx l (64 * blk + j / nT) =
      64 * ((4 * 5120 + (3 + l) * 202048) / 64 + blk) + j / nT := by
    show 626624 + 202048 * l + (64 * blk + j / nT) = _
    generalize j / nT = q
    omega
  rw [e2, ← hhT]
  rfl

end Sized

/-- The five reads are all reads. -/
theorem read_mem (r : Head.Read) :
    r ∈ [Head.Read.wideAtKeys, .wideAtCosts, .actAtLogits, .rowAtCosts, .rowCount] := by
  cases r <;> simp

/-! ## 2. The premises on the seat, and the address -/

variable {K : Type} [CommRing K]

/-- The kind's sizes, the seat and the smallness test's record agree with the sizes by which the
relation's cells are addressed. -/
structure SeatFits (P : HeadLetters K) (s : P.State) : Prop where
  /-- the kind's sizes are the full size's -/
  T : (letI := P.sizes; Norm.T) = nT
  S2 : (letI := P.sizes; Norm.S2) = 64
  d : (letI := P.sizes; Norm.d) = 5120
  JV : (letI := P.sizes; Head.JV) = 202048
  /-- the first parts of the matrices row and wide in the link's list -/
  row : (P.seat.mat .row).1 = P.h.NHf + 1
  wide : (P.seat.mat .wide).1 = 0
  /-- the record's rows and columns at these two -/
  mR : (P.letters.size () s).m (P.h.NHf + 1) = P.L.mR
  kR : (P.letters.size () s).k (P.h.NHf + 1) = P.L.kR
  m : (P.letters.size () s).m 0 = P.L.m
  k : (P.letters.size () s).k 0 = P.L.k
  /-- every use's index lies below the number of its read's entries -/
  count : ∀ u : Use, u ∈ (letI := P.sizes; usesH) →
    (letI := P.sizes; u.index) < P.seat.count u.read

/-- **Every use is addressed in the declared read of the name that its clause means.** -/
theorem addressed_head (P : HeadLetters K) (s : P.State) (hN : NumH P.h P.L)
    (hF : SeatFits P s) :
    ∀ u ∈ P.letters.uses (), ∃ d ∈ P.decls s, d.name = P.letters.read () u ∧
      Addressed (P.letters.size () s) P.val d (P.letters.meant () s u) := by
  intro u hu
  have hmR : (P.letters.size () s).m (P.seat.mat .row).1 = P.L.mR := by
    rw [hF.row]
    exact hF.mR
  have hkR : (P.letters.size () s).k (P.seat.mat .row).1 = P.L.kR := by
    rw [hF.row]
    exact hF.kR
  have hm : (P.letters.size () s).m (P.seat.mat .wide).1 = P.L.m := by
    rw [hF.wide]
    exact hF.m
  have hk : (P.letters.size () s).k (P.seat.mat .wide).1 = P.L.k := by
    rw [hF.wide]
    exact hF.k
  refine ⟨P.decl s (Use.read u), List.mem_map.2 ⟨Use.read u, read_mem _, rfl⟩,
    (means_is_read u).symm, @Use.index P.sizes u, hF.count u hu, rfl, ?_, fun j _ => ⟨?_, rfl⟩⟩
  · rcases u with ⟨cl, x, l⟩ | ⟨l, blk⟩
    · cases cl <;> exact hF.T.symm
    · exact congrArg (HMul.hMul _) hF.T.symm
  · rcases u with ⟨cl, x, l⟩ | ⟨l, blk⟩
    · have hb := fun cl : Clause =>
        byte_cells (iS := P.sizes) (iR := P.request s) (iI := P.points s) (iH := P.heard s)
          P.seat P.h P.L _ _ cl x l j hF.T hN.T hF.row hmR hkR
      cases cl
      · exact hb .B2
      · exact hb .B3
      · exact hb .B4
      · exact hb .Z
    · exact ex_cells (iS := P.sizes) (iR := P.request s) (iI := P.points s) (iH := P.heard s)
        P.seat P.h P.L _ _ l blk j hF.T hN.T hF.S2 hF.d hF.JV hF.wide hm hk

/-! ## 3. What is left of the row at the head -/

/-- **What is left.** The row at the head, in the form in which it is to be shown, from: the letters
are sane; and at every state with closed tables: the test on lengths, the five declarations whole
and joined, the premises on the seat, a row of U3 with an entry, one C. -/
theorem head_of_parts (P : HeadLetters K) (hS : P.Sane)
    (h : ∀ s, P.AtClose s →
      lensB (P.funs s) = true ∧
      (∀ d ∈ P.decls s,
        d.Whole ((P.letters.size () s).m d.mat) ((P.letters.size () s).k d.mat) ∧
        Joined (P.letters.size () s) (P.letters.phi () s) P.val d) ∧
      SeatFits P s ∧ 0 < P.seat.cols ∧ ((P.req s).pol.C : K) = (P.policy.C : K)) :
    HeadClaimByDecls P := by
  refine ⟨hS, fun _ _ s hs => ?_⟩
  obtain ⟨hL, hJ, hF, hcols, hC⟩ := h s hs
  refine ⟨hL, hJ, addressed_head P s hS.2.1 hF, tied_of_reading P hS.2.2.2 s hcols hC ?_⟩
  rw [hF.S2, hF.JV]
  rfl

end VerifiableInference.Reads.AtHead

#print axioms VerifiableInference.Reads.AtHead.byte_cells
#print axioms VerifiableInference.Reads.AtHead.ex_cells
#print axioms VerifiableInference.Reads.AtHead.read_mem
#print axioms VerifiableInference.Reads.AtHead.addressed_head
#print axioms VerifiableInference.Reads.AtHead.head_of_parts
