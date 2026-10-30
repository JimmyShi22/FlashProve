-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/HeldTab.lean: "held": what ties the cells that are made of a decoded table to the matrix of
which the claim in front of "LIN point" speaks. Definitions, and statements with their proofs. It
stands over the shared chain's kind's law's Johnson/Desc/K14/Law/CellsTie.lean.
Main names:
  `tabU p … U`: a decoded table by numbers: row r, place k; 0 beyond a row's message: the arm of
    `TabX2` (Johnson/Desc/K14/Law/PointKey2.lean) where the decoder gives U.
  `tabX2_of_dcd`: where the library's decoder with the record gives U, `TabX2` is `tabU U`.
  `HeldTie p … held matC`: **"held"**: held: what is made of a decoded table, the cells, or nothing;
    matC: the matrix that cells hold, by numbers. The tie: the matrix that the cells held U hold is
    `matOf kLo (tabU U)`, at the rows below matrixRows and the columns below 2^kCol.
  `heldTie_plain`: a member: the cells are the decoded table itself.
  `heldWords`, `heldTie_words`: a second member: the cells are machine words of the base field that
    read as the decoded table; nothing where there are none.
  `not_heldTie`: a try: cells that forget the table do not meet the tie, where two decoded tables
    part at a place that the matrix reads.

What is not claimed. Which cells the protocol's witness has. That an honest stored table decodes to
a table that machine words of the base field read as. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.CellsTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain

/-- A decoded table by numbers: row r, place k; 0 beyond a row's message. -/
def tabU (p : Par) (err₂ eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (U : (ixOf2 p.S.fold err₂ eM rank).Row × Fin p.S.fold.index.code.ell → GE) (r k : Nat) : GE :=
  if h : k < p.S.fold.index.code.ell then U (bitsOf p.S.fold.index.v r, ⟨k, h⟩) else 0

/-- Where the library's decoder gives U, what the stored table decodes to is U by numbers. -/
theorem tabX2_of_dcd (p : Par) (err₂ eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (c : Nat → Option (Nat × List UInt64)) (s : St)
    (U : (ixOf2 p.S.fold err₂ eM rank).Row × Fin p.S.fold.index.code.ell → GE)
    (hU : dcdAt p err₂ eM rank c (recAt p err₂ eM rank s) = some U) :
    TabX2 p err₂ eM rank (colsOf c) s.loc.key = tabU p err₂ eM rank U := by
  funext r k
  unfold TabX2
  split
  · rename_i U' hU'
    have e : some U' = some U := hU'.symm.trans hU
    obtain rfl := Option.some.inj e
    rfl
  · rename_i hn
    have e : none = some U := hn.symm.trans hU
    cases e

/-- **"held"**: the matrix that the cells hold is the decoded table's. -/
def HeldTie {Cells : Type} (p : Par) (err₂ eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (held : ((ixOf2 p.S.fold err₂ eM rank).Row × Fin p.S.fold.index.code.ell → GE) → Option Cells)
    (matC : Cells → Nat → Nat → GE) : Prop :=
  ∀ U c, held U = some c → ∀ y < p.S.matrixRows, ∀ col < 2 ^ p.S.kCol,
    matC c y col = matOf p.S.kLo (tabU p err₂ eM rank U) y col

/-- **A member**: the cells are the decoded table itself, by numbers. -/
theorem heldTie_plain (p : Par) (err₂ eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat) :
    HeldTie p err₂ eM rank (fun U => some (tabU p err₂ eM rank U)) (matOf p.S.kLo) := by
  intro U c h y _ col _
  have e : tabU p err₂ eM rank U = c := Option.some.inj h
  rw [e]

open Classical in
/-- The cells as machine words of the base field that read as the decoded table; nothing where there
are none. -/
noncomputable def heldWords (p : Par) (err₂ eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (U : (ixOf2 p.S.fold err₂ eM rank).Row × Fin p.S.fold.index.code.ell → GE) :
    Option (Nat → Nat → UInt64) :=
  if h : ∃ c : Nat → Nat → UInt64,
      ∀ r k, OnBytes.Model.Reading.gl.val (ofF (c r k)) = tabU p err₂ eM rank U r k
  then some (Classical.choose h) else none

/-- **A second member**: the cells are machine words of the base field. -/
theorem heldTie_words (p : Par) (err₂ eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat) :
    HeldTie p err₂ eM rank (heldWords p err₂ eM rank)
      (fun c => matOf p.S.kLo fun r k => OnBytes.Model.Reading.gl.val (ofF (c r k))) := by
  intro U c h y _ col _
  unfold heldWords at h
  split at h
  · rename_i hx
    have e : Classical.choose hx = c := Option.some.inj h
    rw [← e]
    exact Classical.choose_spec hx _ _
  · cases h

/-- **A try**: cells that forget the table do not meet the tie, where two decoded tables part at a
place that the matrix reads. -/
theorem not_heldTie (p : Par) (err₂ eM : Nat)
    (rank : ((Fin p.S.fold.index.v → Bool) →
      Fin (p.S.fold.index.code.r + p.S.fold.index.code.ell) → GE) → Nat)
    (matC : Unit → Nat → Nat → GE)
    (U U' : (ixOf2 p.S.fold err₂ eM rank).Row × Fin p.S.fold.index.code.ell → GE) (y col : Nat)
    (hy : y < p.S.matrixRows) (hc : col < 2 ^ p.S.kCol)
    (hne : matOf p.S.kLo (tabU p err₂ eM rank U) y col ≠
      matOf p.S.kLo (tabU p err₂ eM rank U') y col) :
    ¬ HeldTie p err₂ eM rank (fun _ => some ()) matC := by
  intro H
  exact hne ((H U () rfl y hy col hc).symm.trans (H U' () rfl y hy col hc))

end Desc.K14.Law
