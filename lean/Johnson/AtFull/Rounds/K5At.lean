-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rounds/K5At.lean: K5's LOT's ROW FOR THE ROUNDS AT THE FULL SIZE: IF THREE PREMISES
HOLD, EACH BLOCK OF THE LOT (H2K5.lotN, Johnson/Desc/ProofFile/Lot/K5.lean) DECLARES THE WRITTEN
LIST THAT THE TABLE listAt (Johnson/AtFull/Rounds/ListAt.lean) HAS AT THE NAME OF THE BLOCK's PLACE.
A law (Johnson/AtFull/Rounds/K5.lean: the rounds read the work and the record own alone) and five
closed facts by Lean's kernel: the fact itself, its length, two bent twins, a look at the written
cut.

  k5OwnW rows   the written record of an attention segment's own rounds; its field rows is a letter:
      the rounds do not read it. WHENCE THE ELEVEN NUMBERS: typed off the written arms of the twelve
      attention groups (Johnson/AtFull/Rows/ArmsOfFields.lean: ownA); no theorem here ties the two;
      were a number wrong, k5_list_closed would be red.
  k5Names   twelve names, "A0:3" to "A11:3".
  k5_list_closed   BY LEAN's KERNEL: at each of the twelve names the table's list is
      k5RoundsOf 0 (k5OwnW 0). 162 rounds: k5_list_len.
  k5_list   so at every value of rows.
  k5_list_bits, k5_list_work   BENT TWINS: with 16 bits for 17, and with one bit of work, none of
      the twelve lists is met. Of own's eleven fields that are read ONE is bent.
  k5_cut_names   BY LEAN's KERNEL: in the written cut of the first chain the rows of the kind K5
      bear just these twelve names, in this order. Nothing here calls it: it shows whence the names
      are.
  k5_member   a block of the lot: its segment, its group's plan, its place, its rounds.
  **k5_row_by**   THE ROW: hw · hA · hN ⊢ for every block b of the lot: b.rounds = listAt (name
      b.place). General in name, a function from places to names: whoever joins the lots' rows lays
      the written name at a place there.

THE THREE PREMISES. hw: the policy's work at a round of the request's scope that draws field
elements is 0. hA: every plan of an attention segment's group has the written own, whatever its
rows. hN: at the third place of every attention segment name gives one of the twelve names. NONE IS
SHOWN HERE AT ANY PUBLIC FILES. k5_cut_names speaks of the written cut, not of name.

Limits. The full size alone. Both sides of the closed fact are written values or this library's own
routines at written values.
Of the laws that whoever
joins the rows of all lots calls this file imports none.
Raised limit: maxRecDepth 1000000. Nothing on soundness.

-/
import Johnson.AtFull.Rounds.K5
import Johnson.AtFull.Rounds.ListAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Rounds
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block KindName Place)
open VerifiableInference.Desc.First
open VerifiableInference.PlanWritten (cutFirstFull)

/-- The written record of an attention segment's own rounds at the full size; rows is a letter. -/
def k5OwnW (rows : Nat) : Params.AttentionRounds :=
  { lt := 10, lgk := 3, pairs := 20, Lam := 4, planeMessages := 2, score := [(17, 20), (14, 20)]
    e := 13, valueM := 16, valueD := 13, attained := 20, bits := 17, rows := rows }

/-- Twelve names: those of the written cut's rows of the kind K5 (k5_cut_names). -/
def k5Names : List String :=
  ["A0:3", "A1:3", "A2:3", "A3:3", "A4:3", "A5:3", "A6:3", "A7:3", "A8:3", "A9:3", "A10:3", "A11:3"]

/-- **At each of the twelve names the table's list is the maker's at the written values.** -/
theorem k5_list_closed :
    k5Names.all (fun n => decide (listAt n = k5RoundsOf 0 (k5OwnW 0))) = true := by decide +kernel

/-- They are 162 rounds. -/
theorem k5_list_len : (k5RoundsOf 0 (k5OwnW 0)).length = 162 := by decide +kernel

/-- A BENT TWIN: with 16 bits for 17 none of the twelve lists is met. -/
theorem k5_list_bits :
    k5Names.all
      (fun n => !decide (listAt n = k5RoundsOf 0 { k5OwnW 0 with bits := 16 })) = true := by
  decide +kernel

/-- A BENT TWIN: with one bit of work none of the twelve lists is met. -/
theorem k5_list_work :
    k5Names.all (fun n => !decide (listAt n = k5RoundsOf 1 (k5OwnW 0))) = true := by decide +kernel

/-- In the written cut of the first chain the rows of the kind K5 bear just these names. -/
theorem k5_cut_names :
    (cutFirstFull.filter fun r => r.2.1.kind == KindName.K5).map (·.1) = k5Names := by
  decide +kernel

/-- The closed fact at every value of rows. -/
theorem k5_list (r : Nat) {n : String} (hn : n ∈ k5Names) :
    k5RoundsOf 0 (k5OwnW r) = listAt n := by
  have h := of_decide_eq_true (List.all_eq_true.1 k5_list_closed n hn)
  have e : k5RoundsOf 0 (k5OwnW 0) = k5RoundsOf 0 (k5OwnW r) := k5RoundsOf_no_rows 0 (k5OwnW r) 0
  rw [h, e]

/-- A block of the lot: its segment, its group's plan, its place, its rounds. -/
theorem k5_member {Z : ProofFile.Pub} {G : ProofFile.Ground} {b : Block S ProofFile.Cl}
    (hb : b ∈ (H2K5.lotN Z).blocks G) :
    ∃ x ∈ H2K5.k5Places G, ∃ a, G.W.A[x.2.2]? = some a ∧ b.place = ⟨1, some x.1, 3, .K5⟩ ∧
      b.rounds = k5RoundsOf (k5Work G.W) a.own := by
  have hb' : b ∈ H2K5.k5OwnN Z G := hb
  unfold H2K5.k5OwnN at hb'
  obtain ⟨x, hx, h⟩ := List.mem_filterMap.1 hb'
  obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨a, ha, hr⟩ := k5AtN_rounds h0
  exact ⟨x, hx, a, ha, (Att.P.k5AtN_states h0).2.2, hr⟩

/-- **THE ROW: under hw, hA and hN each block of K5's lot declares the table's list at its place's
name.** -/
theorem k5_row_by (Z : ProofFile.Pub) (G : ProofFile.Ground) (name : Place → String)
    (hw : k5Work G.W = 0)
    (hA : ∀ x ∈ H2K5.k5Places G, ∀ a, G.W.A[x.2.2]? = some a → a.own = k5OwnW a.own.rows)
    (hN : ∀ x ∈ H2K5.k5Places G, name ⟨1, some x.1, 3, .K5⟩ ∈ k5Names) :
    ∀ b ∈ (H2K5.lotN Z).blocks G, b.rounds = listAt (name b.place) := by
  intro b hb
  obtain ⟨x, hx, a, ha, hpl, hr⟩ := k5_member hb
  rw [hr, hw, hA x hx a ha, hpl]
  exact k5_list _ (hN x hx)

end Johnson.AtFull.Rounds

#print axioms Johnson.AtFull.Rounds.k5_list_closed
#print axioms Johnson.AtFull.Rounds.k5_list_len
#print axioms Johnson.AtFull.Rounds.k5_list_bits
#print axioms Johnson.AtFull.Rounds.k5_list_work
#print axioms Johnson.AtFull.Rounds.k5_cut_names
#print axioms Johnson.AtFull.Rounds.k5_list
#print axioms Johnson.AtFull.Rounds.k5_member
#print axioms Johnson.AtFull.Rounds.k5_row_by
