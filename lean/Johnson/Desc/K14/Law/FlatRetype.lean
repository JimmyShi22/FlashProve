-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/FlatRetype.lean: THE SHARED CHAIN CARRIED TO ANOTHER TYPE OF CLAIMS HOLDS, AT
ITS PLACE 1 + k, THE k-TH OF THE KIND's EIGHT BLOCKS CARRIED THERE; AND THE CARRIED BLOCK DECIDES AS
THE BLOCK ITSELF. Theorems.

WHY. chainOf is typed at the claims Unit. A file's description has one type of claims for its three
chains, and lays a later chain by Chain.retype (Johnson/Desc/Block.lean): each block by
Block.retype. So the block that is seated is not b but b.retype. A law on b's decision is owed at
the seated block.

  retype_decide    (b.retype).decide = b.decide; so are its rounds. By the text.
  bare_retype      a block that states no run stays so.
  flat_retype_get  **general in the place**: the carried chain's flat list holds b.retype at 1 + k.
  piece_retype_at  at any row of pieces with the equation that OfDesc asks of the shared chain, at
                   the carried chain: the piece number 1 + k holds b.retype in the wrap in which a
                   description's pieces hold blocks.
What is not claimed. That a file's description lays chainOf c P tests last carried so: the maker's
text. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.FlatAt
import Johnson.Desc.Sound.DescThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.Sound (Frame Piece below)

variable {Cl' : Type}

/-- The carried block decides as the block itself. -/
theorem retype_decide {S Cl : Type} (b : Block S Cl) :
    (b.retype (Cl' := Cl')).decide = b.decide ∧ (b.retype (Cl' := Cl')).rounds = b.rounds :=
  ⟨rfl, rfl⟩

/-- A block that states no run stays so. -/
theorem bare_retype {S Cl : Type} (b : Block S Cl) (h : b.hasNoClaimsAndNothingAfter = true) :
    (b.retype (Cl' := Cl')).hasNoClaimsAndNothingAfter = true := by
  unfold Block.hasNoClaimsAndNothingAfter at h ⊢
  rw [Bool.and_eq_true] at h
  show (([] : List _).isEmpty && b.after.isEmpty) = true
  rw [h.2]
  rfl

/-- **General in the place.** -/
theorem flat_retype_get (c : Model.Verify.Chains) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (k : Nat) (b : Block St Unit)
    (hk : [b1, b2, b3, b4, b5, b6, b7, b8][k]? = some b) :
    ((chainOf c P tests last).retype (Cl' := Cl')).blocksInOrder[1 + k]? = some b.retype := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := own_bare P b1 b2 b3 b4 b5 b6 b7 b8 hb
  have hall : ∀ x ∈ [b1, b2, b3, b4, b5, b6, b7, b8], x.hasNoClaimsAndNothingAfter = true := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hbb : b.hasNoClaimsAndNothingAfter = true := hall b (List.mem_of_getElem? hk)
  have hc : chainOf c P tests last =
      { first := frontBlock c, front := [], links := []
        back := [b1, b2, b3, b4, b5, b6, b7, b8] ++ tests
        last := last ([b1, b2, b3, b4, b5, b6, b7, b8] ++ tests) } := by
    simp [chainOf, blocksOr, hb]
  rw [hc]
  show (_ :: (([] : List (Block St Cl')) ++ [] ++
    (([b1, b2, b3, b4, b5, b6, b7, b8] ++ tests).map Block.retype).map bareOf ++ [_]))[1 + k]? = _
  rw [Nat.add_comm, List.getElem?_cons_succ, List.nil_append, List.nil_append, List.map_append,
    List.map_append, List.append_assoc,
    List.getElem?_append_left (by simpa using (List.getElem?_eq_some_iff.1 hk).1),
    List.getElem?_map, List.getElem?_map, hk]
  show some (bareOf b.retype) = some b.retype
  rw [bareOf_self _ (bare_retype b hbb)]

variable {C : CK} {F : Frame} {P₁ W : Type}

/-- **At any row of pieces that holds the carried chain's blocks as a description's pieces do.** -/
theorem piece_retype_at (ps : List (Piece C F (P₁ × St) Cl' W)) (c : Model.Verify.Chains) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (h : ps.map (·.b) = (((chainOf c P tests last).retype (Cl' := Cl')).blocksInOrder.map below).map
      (Block.lift Prod.snd fun t s => (t.1, s)))
    (k : Nat) (b : Block St Unit) (hk : [b1, b2, b3, b4, b5, b6, b7, b8][k]? = some b) :
    ∃ q, ps[1 + k]? = some q ∧
      q.b = (below (b.retype (Cl' := Cl'))).lift Prod.snd fun t s => (t.1, s) := by
  have e : (ps.map (·.b))[1 + k]? =
      some ((below (b.retype (Cl' := Cl'))).lift Prod.snd fun t s => (t.1, s)) := by
    rw [h, List.getElem?_map, List.getElem?_map,
      flat_retype_get c P b1 b2 b3 b4 b5 b6 b7 b8 tests last hb k b hk]
    rfl
  rw [List.getElem?_map] at e
  cases hq : ps[1 + k]? with
  | none => rw [hq] at e; cases e
  | some q => rw [hq] at e; exact ⟨q, rfl, Option.some.inj e⟩

end Desc.K14.Law
