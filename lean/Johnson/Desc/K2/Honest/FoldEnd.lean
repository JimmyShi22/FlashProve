-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/FoldEnd.lean: the honest prover of the code switch between two segments: WHAT
THE FOLD THAT CLOSES A GROUP LEAVES (`Left`, Johnson/Desc/K2/Honest/Carrying.lean), of the group's
oracle messages in full, the mask that is sent ahead of the fold in full, and the fold's challenges.
It defines part of the honest prover. Definitions with code; no theorem. It hangs on no frame: no
round is typed here.

What is called. THE FOLDING ITSELF IS NOT TYPED HERE: it is `foldMsg` and `foldTl`
(Johnson/Prover/Link/FoldEnc.lean): the main rows at the fold's point, the group's mask rows and the
rows of the mask sent ahead at its first h coordinates. The group's layout is the description's own
(`layoutOf`, Johnson/Desc/Own/Layout.lean), at a statement that holds the members' shapes alone.
What is this file's own: which row of the two tables holds which member's row (`tableRow`); and that
the kept members pass by the fold as they were sent.

  `GroupMember` what is public of a member: its shape; whether it is kept
  `groupLayout` the layout of a group of such members
  `tableRow` the row number ρ of a group's table: the member and its own row's number
  `stageOf` the sizes as the fold's public letter
  `foldEndAt` WHAT THE FOLD LEAVES, THE LAYOUT A LETTER: THE ONE TEXT
  `foldEnd` what the fold leaves: `foldEndAt` at the layout that `groupLayout` makes of the members'
                    shapes

Rows. A member that is not kept stands in the main table from the layout's `mainFirst` on, every
member's mask rows in the mask table from `maskFirst` on; a row that nobody has sent is 0. A row
over the base field is laid into the extension field before it is folded, and a tail folds as its
row does (OnBytes/Iop/Fold.lean, at `SingleRows`).

Limits. Meant for a layout with h ≤ k and for as many challenges as the layout has row variables: a
challenge that lacks counts as 0. `foldEndAt` asks nothing of its layout: neither that its lists are
as long as the list of members, nor that it fits their shapes. THE MASK SENT AHEAD IS READ AT EVERY
ROW BELOW 2 ^ h, whether or not it has so many rows. Slow: each entry is a sum over all 2 ^ k rows.
That `foldMsg` is the program's `foldLow` on the same tables is not proved here. Nothing on any
property.
-/
import Johnson.Desc.K2.Honest.Carrying
import Johnson.Desc.Own.Layout
import Johnson.Prover.Send.Core
import Johnson.Prover.Link.FoldEnc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open Johnson.Prover.Send (Rows)

/-- What is public of a group's member. -/
structure GroupMember where
  shape : OracleShape
  kept : Bool

/-- The layout of a group whose members, in the order of sending, are these. -/
def groupLayout (codes : Codes) (code maskCode : Nat) (ms : List GroupMember) : GroupLayout :=
  Own.layoutOf { codes := codes, oracles := (ms.map fun m => { shape := m.shape }).toArray }
    { code := code, maskCode := maskCode, members := Array.range ms.length
      kept := (ms.map (·.kept)).toArray }

/-- Whose row the row number ρ of a group's table is: the member's number, and the row's number in
the member. first: each member's first row, nothing where it has none there. rows: how many rows
each has. Nothing at a row that nobody has sent. -/
def tableRow (first : Array (Option Nat)) (rows : Nat → Nat) (ρ : Nat) : Option (Nat × Nat) :=
  (List.range first.size).findSome? fun w =>
    (first.getD w none).bind fun f =>
      if decide (f ≤ ρ) && decide (ρ < f + rows w) then some (w, ρ - f) else none

/-- The sizes as the fold's public letter. No position is drawn here. -/
def stageOf (codes : Codes) (code maskCode : Nat) (L : GroupLayout) : OnBytes.Slice.Sg :=
  ⟨OnBytes.Slice.codeOf (codes.base.getD code default),
    OnBytes.Slice.codeOf (codes.mask.getD maskCode default), L.h, L.k - L.h, 0⟩

/-- **What the fold that closes a group leaves, THE LAYOUT A LETTER.** L: the group's layout. ms:
the members, in the order of sending. M: each member in full. fresh: the mask that is sent ahead of
the fold, in full. γ: the fold's challenges, in the order of its rounds. -/
def foldEndAt (L : GroupLayout) (codes : Codes) (code maskCode : Nat) (ms : List GroupMember)
    (M : Nat → Rows) (fresh : Rows) (γ : List Cb.Gl.E) : Left :=
  let s := stageOf codes code maskCode L
  let shape (w : Nat) : OracleShape := ((ms[w]?).map (·.shape)).getD {}
  let mainOf (get : Rows → Bool → Nat → Nat → Cb.Gl.E) (ρ j : Nat) : Cb.Gl.E :=
    match tableRow L.mainFirst (fun w => (shape w).mainRows) ρ with
    | some (w, b) => get (M w) ((shape w).mainDeg == 3) b j
    | none => zeroG
  let maskOf (get : Rows → Nat → Nat → Cb.Gl.E) (ρ j : Nat) : Cb.Gl.E :=
    match tableRow L.maskFirst (fun w => (shape w).maskRows) ρ with
    | some (w, b) => get (M w) b j
    | none => zeroG
  let tailOf (R : Rows) (overE : Bool) (b q : Nat) : Cb.Gl.E :=
    if overE then R.mainTlE b q else OnBytes.Slice.toE (OnBytes.Slice.ofF (R.mainTlF b q), 0, 0)
  let pt : Fin (s.h + s.g) → Cb.Gl.E := fun i => γ.getD i.val zeroG
  let μ : s.cIn.J → Cb.Gl.E :=
    Sum.elim (fun x => mainOf (fun R e => R.main e) (OnBytes.Slice.Sz.rowNo x.1) x.2.val)
      (fun x => maskOf (·.mask) (OnBytes.Slice.Sz.rowNo x.1) x.2.val)
  let ρ : s.cIn.Q → Cb.Gl.E :=
    Sum.elim (fun x => mainOf tailOf (OnBytes.Slice.Sz.rowNo x.1) x.2.val)
      (fun x => maskOf (·.maskTl) (OnBytes.Slice.Sz.rowNo x.1) x.2.val)
  let φ : s.cFr.J → Cb.Gl.E := fun x => fresh.mask (OnBytes.Slice.Sz.rowNo x.1) x.2.val
  let ψ : s.cFr.Q → Cb.Gl.E := fun x => fresh.maskTl (OnBytes.Slice.Sz.rowNo x.1) x.2.val
  let msg := Johnson.Prover.Link.foldMsg s μ φ pt
  let tl := Johnson.Prover.Link.foldTl s ρ ψ pt
  let keptNos := (List.range ms.length).filter fun w => ((ms[w]?).map (·.kept)).getD false
  { main := fun j => if h : j < s.C.l then msg (.inl ⟨j, h⟩) else zeroG
    mainTail := fun q => if h : q < s.C.r then tl (.inl ⟨q, h⟩) else zeroG
    mask := fun r i =>
      if h : i < s.Z.l then (if r == 0 then msg (.inr (.inl ⟨i, h⟩)) else msg (.inr (.inr ⟨i, h⟩)))
      else zeroG
    maskTail := fun r q =>
      if h : q < s.Z.r then (if r == 0 then tl (.inr (.inl ⟨q, h⟩)) else tl (.inr (.inr ⟨q, h⟩)))
      else zeroG
    kept := fun i =>
      let w := keptNos.getD i ms.length
      ⟨(M w).main ((shape w).mainDeg == 3), tailOf (M w) ((shape w).mainDeg == 3)⟩ }

/-- **What the fold that closes a group leaves**: at the layout that is made of the members'
shapes. -/
def foldEnd (codes : Codes) (code maskCode : Nat) (ms : List GroupMember) (M : Nat → Rows)
    (fresh : Rows)
    (γ : List Cb.Gl.E) : Left :=
  foldEndAt (groupLayout codes code maskCode ms) codes code maskCode ms M fresh γ

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.GroupMember
#print axioms VerifiableInference.Desc.K2.Honest.groupLayout
#print axioms VerifiableInference.Desc.K2.Honest.tableRow
#print axioms VerifiableInference.Desc.K2.Honest.stageOf
#print axioms VerifiableInference.Desc.K2.Honest.foldEndAt
#print axioms VerifiableInference.Desc.K2.Honest.foldEnd
