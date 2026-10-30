-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeyBattSays.lean: THE KEY FILE's ROW 1.16: WHAT THE SEAT's YES SAYS OF THE STATE, OUTRIGHT (Key.batchTableRows, Johnson/Desc/Key/One.lean): for the book-keeping's facts (SeatFacts116).
  layPile_says   layPile's yes writes the pile alone
  batt_takes     the kind K13's batching leaves as its state what takeMasksP leaves: IT TAKES MASK ENTRIES OFF ONE MESSAGE's LEDGER, AND NOTHING ELSE (batt_keeps's docstring, as an equation)
  seat_says      the seat's yes from s to s': s had not come to its end; s' is s with: the pile laid · the end's mark · no debt · what W's sending announces · the claim made of the batching's row · the batching's state
  seat_rounds    the seat's declared rounds ARE K13.battRounds at its numbers
Definitions are other files'. Nothing on soundness.
-/
import Johnson.Desc.Key.KeyBattBy
import Johnson.Desc.K13.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open VerifiableInference.Desc.ChainEnd (bind_ok)
open VerifiableInference.Desc.K13 (there_ok pure_ok)
open VerifiableInference.Desc.K13.Law (ebind_ok battB_ok quietB_ok frontB_fit)

variable {β Cl : Type}

theorem layPile_says (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (s t : ChainState β) (h : layPile keysOf one s = .ok t) :
    ∃ rows, t = { s with pile := rows } := by
  unfold layPile at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨rows, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  exact ⟨rows.flatten, (pure_ok h).symm⟩

theorem batt_takes (owed : Johnson.Desc.First.ForkGround.RowsOwed) (kCol n : Nat) (pile : List TensorRow) (ledger : Nat) (d : K13.St) (rs : List Fmt.RoundView)
    (y : TensorRow × K13.St) (h : K13.batt owed kCol n pile ledger d rs = .ok y) :
    ∃ r, Ground.takeMasksP d ledger (Batt.masksOf kCol) = some (r, y.2) := by
  unfold K13.batt at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases rs with
  | nil => cases h
  | cons r rs' =>
    dsimp only at h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨t, ht, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    obtain ⟨_, _, h⟩ := bind_ok h
    have := pure_ok h
    subst this
    exact ⟨t.1, there_ok ht⟩

theorem seat_says (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (N : Pieces) (sent : Nat) (s s' : ChainState β) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (batchTableRows (Cl := Cl) keysOf one N sent).decide s rs gs = .ok s') :
    ∃ (rows : List TensorRow) (out : TensorRow × K13.St) (msg : Array OracleNotice) (rs' : List Fmt.RoundView),
      layPile keysOf one s = .ok { s with pile := rows } ∧ s.atEnd = false ∧
      K13.batt s.debt (batchWhere one N sent).lin.kCol (batchWhere one N sent).rows rows s.idx s.d rs' = .ok out ∧
      s' = { s with pile := rows, atEnd := true, owed := none, msgW := msg, lin := some { claim := memberClaim out.1 }, d := out.2 } := by
  unfold batchTableRows at h
  dsimp only at h
  rw [decide_andThen] at h
  obtain ⟨t₃, h3, hq⟩ := ebind_ok.1 h
  rw [decide_andThen] at h3
  obtain ⟨t₂, h2, hb⟩ := ebind_ok.1 h3
  rw [decide_andThen] at h2
  obtain ⟨t₁, h1, hf⟩ := ebind_ok.1 h2
  have h1' : layPile keysOf one s = .ok t₁ := h1
  obtain ⟨rows, rfl⟩ := layPile_says keysOf one s t₁ h1'
  obtain ⟨p, he, _, _⟩ := frontB_fit batchLens _ hf
  obtain ⟨hend, rfl⟩ := (lens_enter _ _).1 he
  obtain ⟨p₂, out, hp₂, hbt, rfl⟩ := battB_ok batchLens _ hb
  obtain ⟨_, rfl⟩ := (lens_get _ _).1 hp₂
  obtain ⟨p₃, msg, hp₃, rfl⟩ := quietB_ok batchLens _ hq
  obtain ⟨_, rfl⟩ := (lens_get _ _).1 hp₃
  exact ⟨rows, out, msg, _, h1', hend, hbt, rfl⟩

/-- **The seat declares the kind's own rounds of the batching, and no other**: sigma's · epsilon's · kCol variables' rounds. -/
theorem seat_rounds (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (N : Pieces) (sent : Nat) :
    (batchTableRows (Cl := Cl) keysOf one N sent).rounds = K13.battRounds (batchWhere one N sent) := by
  simp [batchTableRows, rounds_andThen, quietAt, K13.frontB, K13.still, K13.claimCombinationBlock, K13.quietB]

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.seat_rounds
#print axioms VerifiableInference.Desc.Key.layPile_says
#print axioms VerifiableInference.Desc.Key.batt_takes
#print axioms VerifiableInference.Desc.Key.seat_says
