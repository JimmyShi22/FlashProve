-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/KeyToldFirst.lean: THEOREMS. **WHAT Key.descriptionFromSource (the key file's IOP as written in Lean) TELLS OF ITS FIRST TREES: the list of oracle messages that chain 1's blocks (sub-protocols) send begins with what K1.oracles tells at the index masks' sending and goes on with what it tells at the lookups' own
message's sending; so FileDescription.oracleAt, behind the first sending's trees, reads the second sending's.** No name string of a sending is spelled in a proof.
OBJECT. VerifiableInference.Desc.oraclesOf (Key.descriptionFromSource X N P).first.blocksInOrder · FileDescription.oracleAt (Johnson/Desc/Msg.lean) · K1.oracles (Johnson/Desc/K1/Send.lean) at KeySendAtDesc.lean's parIdx X | parMsg X. USER. ShapeIs at border 15 (the book's tree at message 1's place has the shape that the description tells), beneath the seam's
clause on the word. LETTERS. X · N · P · τ.
  two_heads            a list with its entries 0 and 1 known begins with them
  idx_told | msg_told  the two blocks' own lists, flattened, are K1.oracles' at their parameters
  par_facts            parIdx X | parMsg X: the codes are the plan's; what is sent is #[the index masks] | Wf.messageOf the ranges
  fk_told              **∃ rest, oraclesOf first.blocksInOrder = (K1.oracles (parIdx X)).flatMap id ++ ((K1.oracles (parMsg X)).flatMap id ++ rest)**
  oracleAt_idx | oracleAt_own      **oracleAt τ | oracleAt (the first list's length + τ) read the first | second list at τ**
What is not claimed. What K1.oracles tells (other files'). Anything on the rest of the list. Nothing on soundness.

-/
import Johnson.RunOne.KeySendAtDesc
import Johnson.Desc.Msg

set_option autoImplicit false

namespace Johnson.RunOne.Law.KeyToldFirst

open OnBytes OnBytes.Params VerifiableInference.Desc.Key Johnson.RunOne.KeySendGood
open VerifiableInference.Desc (Block oraclesOf FileDescription)

theorem two_heads {α : Type} (l : List α) (a b : α) (h0 : l[0]? = some a) (h1 : l[1]? = some b) : ∃ tl, l = a :: b :: tl := by
  cases l with
  | nil => cases h0
  | cons x t =>
    cases t with
    | nil => cases h1
    | cons y tl =>
      obtain rfl : x = a := Option.some.inj h0
      obtain rfl : y = b := Option.some.inj h1
      exact ⟨tl, rfl⟩

theorem told_cons₂ {S Cl : Type} (a b : Block S Cl) (tl : List (Block S Cl)) : oraclesOf (a :: b :: tl) = a.oracles.flatMap id ++ (b.oracles.flatMap id ++ oraclesOf tl) := by
  simp [oraclesOf, List.flatMap_cons]

variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)

theorem idx_told : (bareOf (sendIndexMasks (β := LookupRecord) (Cl := Claim) X.Y.k.oneTime pieces (gIdx X))).oracles.flatMap id = (VerifiableInference.Desc.K1.oracles (parIdx X)).flatMap id := by
  show (VerifiableInference.Desc.K1.oracles (parIdx X) ++ []).flatMap id = _
  rw [List.append_nil]

theorem msg_told : (bareOf (sendOwnMessage (β := LookupRecord) (Cl := Claim) X.Y.k.oneTime pieces (gMsg X))).oracles.flatMap id = (VerifiableInference.Desc.K1.oracles (parMsg X)).flatMap id := by
  show (VerifiableInference.Desc.K1.oracles (parMsg X) ++ []).flatMap id = _
  rw [List.append_nil]

theorem par_facts : (parIdx X).codes = X.Y.k.oneTime.codes ∧ (parIdx X).sent = #[X.Y.k.oneTime.indexMasks] ∧ (parMsg X).codes = X.Y.k.oneTime.codes ∧ (parMsg X).sent = Wf.messageOf X.Y.k.oneTime.ranges :=
  ⟨rfl, by simp [parIdx, sendingPar, VerifiableInference.Desc.K1.Par.sent], rfl, by simp [parMsg, sendingPar, VerifiableInference.Desc.K1.Par.sent]⟩

/-- **Chain 1's list of oracle messages begins with the two sendings'.** -/
theorem fk_told : ∃ rest, oraclesOf (descriptionFromSource X N P).first.blocksInOrder =
    (VerifiableInference.Desc.K1.oracles (parIdx X)).flatMap id ++ ((VerifiableInference.Desc.K1.oracles (parMsg X)).flatMap id ++ rest) := by
  obtain ⟨tl, h⟩ := two_heads _ _ _ (idx_at X N P) (msg_at X N P)
  refine ⟨oraclesOf tl, ?_⟩
  rw [h]
  exact (told_cons₂ _ _ tl).trans (congrArg₂ (· ++ ·) (idx_told X) (congrArg (· ++ oraclesOf tl) (msg_told X)))

/-- **At the first sending's trees.** -/
theorem oracleAt_idx (τ : ℕ) (hτ : τ < ((VerifiableInference.Desc.K1.oracles (parIdx X)).flatMap id).length) :
    (descriptionFromSource X N P).oracleAt τ = ((VerifiableInference.Desc.K1.oracles (parIdx X)).flatMap id)[τ]? := by
  obtain ⟨rest, h⟩ := fk_told X N P
  unfold FileDescription.oracleAt
  rw [h, List.append_assoc, List.append_assoc, List.getElem?_append_left hτ]

/-- **Behind them: at the second sending's.** -/
theorem oracleAt_own (τ : ℕ) (hτ : τ < ((VerifiableInference.Desc.K1.oracles (parMsg X)).flatMap id).length) :
    (descriptionFromSource X N P).oracleAt (((VerifiableInference.Desc.K1.oracles (parIdx X)).flatMap id).length + τ) = ((VerifiableInference.Desc.K1.oracles (parMsg X)).flatMap id)[τ]? := by
  obtain ⟨rest, h⟩ := fk_told X N P
  unfold FileDescription.oracleAt
  rw [h, List.append_assoc, List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left, List.append_assoc, List.getElem?_append_left hτ]

end Johnson.RunOne.Law.KeyToldFirst
