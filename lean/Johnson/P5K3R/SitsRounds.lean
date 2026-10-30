-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5K3R/SitsRounds.lean: the declared rounds of the kind "lookup"'s constant, and of the block
that is seated: they are the plan's rounds at the lookup's place. Two small theorems.

Why. The laws of the kind ask of a piece that its written rounds go along the rounds of the plan's
place (`P.rounds` at `placeAt`). What the tiling hands of a piece goes along the rounds that the
piece's own block declares. Here the two lists are shown to be one.

Main names:
  `theStated_rounds`: where `K3.theStated` returns a block B at an address a: a lies in a link i,
    its piece is that of one of the link's two lookups, the plan has a place p for that lookup, and
    B.rounds = p.rounds.
  `k03_rounds`: the like for the seated block b of `k03_sits`, from `IM.LaidAlone`.
  `k03_place`: at the driver's address of link l's lookup on the calls, or on the digits: which of
    the two it is comes out right: the address's piece is `pieceAt X l digits`, and the place is
    `placeAt X l digits`. No fact on the scope is spent: the four numbers 2, 3, 7, 8 tell the two
    lookups apart.

Limits: equations of lists of declared rounds. In the first two, which of the two lookups it is
comes out under "there is", with the equation on the piece's number. Nothing on soundness; nothing
on hiding.


-/
import Johnson.P5K3R.Sits
import Johnson.Desc.First.Look.K3OwnIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K3Lot

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (theStated theStated_is theWhole_is theOwn_is pieceAt isHead
  Readers)

/-- **The constant's declared rounds are the plan's at the lookup's place.** -/
theorem theStated_rounds {Cl : Type} (claim : Aff → Cl) (readers : Nat → Option (Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape)
    (a : Place) (B : Block S Cl) (h : theStated claim readers X codes shape a = some B) :
    ∃ i digits p, a.link = some i ∧ a.piece = pieceAt X i digits ∧
      VerifiableInference.Desc.First.Look.placeAt X i digits = some p ∧ B.rounds = p.rounds := by
  obtain ⟨B₁, h1, hr, -⟩ := theStated_is claim readers X codes shape a B h
  obtain ⟨b, hb, hB⟩ := theWhole_is claim true X codes shape a B₁ h1
  obtain ⟨i, digits, p, sent, laid, e1, e2, e3, -, -, e6, -⟩ :=
    theOwn_is claim true X codes shape a b hb
  refine ⟨i, digits, p, e1, e2, e3, ?_⟩
  rw [hr]
  rcases hB with ⟨-, rfl⟩ | ⟨f, -, rfl⟩
  · exact e6
  · show b.rounds ++ [] = p.rounds
    rw [List.append_nil]
    exact e6

/-- The like for a block that is seated alone over the constant. -/
theorem k03_rounds {X : Verify.Public} {codes : Codes}
    {shape : Params.ReqShape} {a : Place} {b b' : Block S ProofFile.Cl} {name : String}
    (h : theStated K3Lot.ofForm (K3Lot.readersAt X) X codes shape a = some b')
    (hA : IM.LaidAlone ProofFile.sameReply b b' name a) :
    ∃ i digits p, a.link = some i ∧ a.piece = pieceAt X i digits ∧
      VerifiableInference.Desc.First.Look.placeAt X i digits = some p ∧ b.rounds = p.rounds := by
  obtain ⟨i, digits, p, e1, e2, e3, e4⟩ := theStated_rounds _ _ X codes shape a b' h
  exact ⟨i, digits, p, e1, e2, e3, (IM.alone_rounds hA).trans e4⟩

/-- **At the driver's address the lookup is the one that the address names.** -/
theorem k03_place {Cl : Type} (claim : Aff → Cl) (readers : Nat → Option (Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (l : ℕ) (digits : Bool)
    (B : Block S Cl)
    (h : theStated claim readers X codes shape (IM.k3Place l digits) = some B) :
    (IM.k3Place l digits).piece = pieceAt X l digits ∧
      ∃ p, VerifiableInference.Desc.First.Look.placeAt X l digits = some p ∧
        B.rounds = p.rounds := by
  obtain ⟨i, dg, p, e1, e2, e3, e4⟩ := theStated_rounds claim readers X codes shape _ B h
  have ei : l = i := Option.some.inj e1
  subst ei
  have e2' : (if digits then 6 else 1) + (if l = 24 then 1 else 0) + 1 =
      if isHead X l then (if dg then 8 else 3) else (if dg then 7 else 2) := e2
  have hc : (if l = 24 then 1 else 0 : ℕ) ≤ 1 := by
    split <;> omega
  have hd : dg = digits := by
    generalize (if l = 24 then 1 else 0 : ℕ) = c at e2' hc
    rcases Bool.eq_false_or_eq_true (isHead X l) with hH | hH <;> cases dg <;> cases digits <;>
      simp only [hH, if_true, if_false, Bool.false_eq_true] at e2' <;> first | rfl | omega
  subst hd
  exact ⟨e2, p, e3, e4⟩

end K3Lot
