-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyStep16.lean: THE KEY FILE's FIRST CHAIN: WHAT THE BATCHING's SEAT's YES DOES TO A STATE ALONE: A LIGHT FILE: it stands over the book-keeping's facts (KeyBattFacts.lean) and KeyYes.lean, NOT over row 1.16's law (RowBatt.lean and what stands on it), WHICH ALONE SPENDS THE MENDED PREMISE OF THE KIND K13's goodIn_any: so that whoever carries the state's side of the promise over block 16 does not inherit it. Johnson/Desc/K13/Law/GoodAny.lean ITSELF LIES BENEATH BY IMPORT (KeyBattBy.lean takes its DEFINITIONS ByBatt · LensLaw · partIn · rowOut · byBatt_joined, which are one in its two forms).
  idx0_of_shape   (from Row116Whole.lean) the book-keeping at 16 holds «the index masks' number is 0»
  pinned_16       (from Row116Book.lean) by the kernel: pinned (open₁ 2 16) = [0]
  bareOf · block16 (from Row116.lean) a block as Chain.blocksInOrder lays it outside the links · under hl the first chain's sixteenth block IS the batching's seat so laid
  step16_state    (from RowASteps.lean) the book-keeping at 16 gives that at 17 · the book is unturned · the statement stays in order. seatFacts116_paid (Row116Whole.lean) CALLS IT.
Nothing on soundness.
-/
import Johnson.RunOne.KeyBattFacts
import Johnson.RunOne.KeyYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key (FirstState Claim Lookup)
open VerifiableInference.Desc.Key (Xi)
open Johnson.RunOne.KeyRows1

theorem pinned_16 : pinned (open₁ 2 16) = [0] := by decide +kernel

/-- A block as Chain.blocksInOrder (Johnson/Desc/Block.lean:463-465) lays it outside the links: its test on the plan asks besides that it has neither claims nor runs behind a batching. ITS DECISION IS THE BLOCK's OWN. -/
def bareOf {S Cl : Type} (b : Block S Cl) : Block S Cl := { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }

/-- **The first chain's sixteenth block is the batching's seat, AS Chain.blocksInOrder LAYS IT.** -/
theorem block16 (one : OneTime) (D : List Fmt.DeclaredRound) (told : List ProofFile.Root) (set : Setting) (N : H2U.PlaceNums) (x₀ x₁ : Lookup)
    (hl : lookupsOf one = [x₀, x₁]) (b : Block FirstState Claim) (h : (firstChain one D told set N).blocksInOrder[16]? = some b) :
    b = bareOf (batchTableRows (fun x : LookupRecord => x.keys) one pieces (rootsBefore D (batchRound D))) := by
  simp only [firstChain, hl] at h
  have e : _ = b := Option.some.inj h
  exact e.symm

theorem idx0_of_shape (one : OneTime) (s : FirstState) (h : shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 16 s = true) : s.idx = 0 := by
  have ht : ties₁ one 16 s = true := ((shape₁_iff _ _ _ _ _ _ _).1 h).1
  unfold ties₁ tiesA at ht
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at ht
  rcases ht.1.1.1.2 with h | h
  · exact absurd h (by decide)
  · exact h

theorem step16_state (one : OneTime) (N : Pieces) (sent : ℕ) (hst : one.ranges.stages.length ≤ noId) (HP : PubPile one) (s s' : FirstState) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (hs : (batchTableRows (Cl := Claim) (fun x : LookupRecord => x.keys) one N sent).decide s rs gs = .ok s') :
    (shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 16 s = true → shape₁ (plan₁ one) (readers₁ one) (book₁ one) 2 (slots₁ one) 17 s' = true) ∧
      s'.d.book = s.d.book ∧ (Means.InOrder s.d.st → Means.InOrder s'.d.st) := by
  obtain ⟨rows, out, msg, rs', hlay, _, hbt, rfl⟩ := seat_says (Cl := Claim) (fun x : LookupRecord => x.keys) one N sent s s' rs gs hs
  have hfit := seat_fit (Cl := Claim) (fun x : LookupRecord => x.keys) one N sent s _ rs gs hs rows hlay
  obtain ⟨r, htk⟩ := batt_takes _ _ _ _ _ _ _ _ hbt
  obtain ⟨g, hbk⟩ := takeMasksP_gnd htk
  have H : CallGround s out.2 := ⟨g.tables, g.codes, g.groups, hbk, g.oracle, VerifiableInference.Desc.Book.takeMasksP_roots _ _ _ _ _ htk⟩
  refine ⟨fun hsh => ?_, H.book, order_call s out.2 H⟩
  have h0 := idx0_of_shape one s hsh
  have hK : (memberClaim out.1).g.all (·.ok) = true := claim_ok hbt (pile_ok _ _ HP _ _ hlay)
  have hM : listOfT ((memberClaim out.1).masks.toList.map (·.oracle)) = [0] := by
    rw [h0] at hbt hfit
    exact claim_masks0 hbt (K13.Law.onLedger_of_fit hfit)
  have hsz : s.d.st.groups.size ≤ noId := by
    have ht : ties₁ one 16 s = true := ((shape₁_iff _ _ _ _ _ _ _).1 hsh).1
    unfold ties₁ sizesB at ht
    simp only [Bool.and_eq_true, beq_iff_eq] at ht
    have e : s.d.st.groups.size = (counts₁ one 16).2.1 := ht.2.1.1.1.1.1.1.2
    rw [e]
    exact hst
  exact shape₁_step _ _ _ 2 _ 16 17 s (afterBatt s rows msg out.1 out.2) (t_16_17 one s rows msg out.1 out.2 H hM hK)
    (c_16_17 one s rows msg out.1 out.2 H hsz) hsh

end LPFD

#print axioms LPFD.pinned_16
#print axioms LPFD.block16
#print axioms LPFD.idx0_of_shape
#print axioms LPFD.step16_state
