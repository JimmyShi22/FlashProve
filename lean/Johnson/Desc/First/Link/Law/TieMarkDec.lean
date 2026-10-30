-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/TieMarkDec.lean: TWO OF THE FIVE DEBTS A PIECE THAT ARE LEFT OF A TIE AT
THE TABLE (`TieRest`, LinkTiedAt.lean; `TieRestR`, LinkTiedR.lean): «a mark stays» and «the
committed table decodes with the verifier's state» rides: AT A LINK's THREE PIECES (the batching;
the frame's sub-protocol behind it; the one equation). Both are asked at EVERY accepting transcript,
promise or none. Theorems, each ending in the field's own type.

What is said.
  `mark_batch`, `mark_behind`, `mark_eq`: **the field mark at the three pieces**: an accepting step
    of each leaves «failed» as it was. `dec_at`: **the field dec at any piece over the verifier's
    state**, at a meaning whose «decodes» is the library's own notion at a decoder that reads
    nothing of the state.

Limits. `mark_batch` and `mark_behind` stand under `TwoBlocks` (the runs' share). `dec_at` stands
under «the decoder reads nothing of the verifier's state»: a sentence on a parameter.
The three other debts (what the row opens gives the
kind's relation behind; the kind's relation in front gives what the row closes; what rides) are not
here. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.OracleRides
import Johnson.Desc.First.Link.Law.LinkAtSort
import Johnson.Desc.First.Link.Law.EqLays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.JoinAtBlocks
open _root_.Run.PQ (CK)

variable {C : CK} {F : Frame} {P W : Type}

/-- **mark, at the batching's piece.** -/
theorem mark_batch (z : P) (L : Link S Claim) (pp : Where) (T : TwoBlocks L pp)
    (pb : Piece C F S Claim W) (hpb : pb.b = below L.batchB) :
    ∀ a τ b, pb.ior.red.out a τ = some b → ((fun s : S => (z, s)) a.1).2.failed ≠ none →
      ((fun s : S => (z, s)) b.1).2.failed ≠ none := by
  intro a τ b hout hm
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpb hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  show b.1.failed ≠ none
  rw [(T.1 _ _ _ _ _ j hstep).1.failed]
  exact hm

/-- **mark, at the piece of the frame's sub-protocol behind the batching.** -/
theorem mark_behind (z : P) (L : Link S Claim) (pp : Where) (T : TwoBlocks L pp)
    (pq : Piece C F S Claim W) (hpq : pq.b = below L.behindB) :
    ∀ a τ b, pq.ior.red.out a τ = some b → ((fun s : S => (z, s)) a.1).2.failed ≠ none →
      ((fun s : S => (z, s)) b.1).2.failed ≠ none := by
  intro a τ b hout hm
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpq hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  show b.1.failed ≠ none
  rw [(T.2 _ _ _ _ _ j hstep).1.failed]
  exact hm

/-- **mark, at the one equation's piece.** -/
theorem mark_eq (z : P) (pw : Where) (b₃ : Block S Claim)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Claim) atS pw).step ft s rs cols = .ok x)
    (pe : Piece C F S Claim W) (hpe : pe.b = below b₃) :
    ∀ a τ b, pe.ior.red.out a τ = some b → ((fun s : S => (z, s)) a.1).2.failed ≠ none →
      ((fun s : S => (z, s)) b.1).2.failed ≠ none := by
  intro a τ b hout hm
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpe hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  obtain ⟨_, _, _, _, _, El⟩ := eq_lays pw b₃ hb₃ _ _ _ _ _ j hstep
  show b.1.failed ≠ none
  rw [El.failed]
  exact hm

/-- **dec, at any piece over the verifier's state.** -/
theorem dec_at {Cells Tok Cl : Type} (Mg : Meaning P (Wit Cells Tok MsgT))
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option Cells)
    (hD : Mg.decodes = decodesOf decT) (z : P)
    (hd : ∀ c (s s' : S), decT c (z, s') = decT c (z, s))
    (q : Piece C F S Cl (Wit Cells Tok MsgT)) :
    ∀ a τ b, q.ior.red.out a τ = some b →
      Mg.decodes ((fun s : S => (z, s)) a.1) (strsOf F a.2) →
      Mg.decodes ((fun s : S => (z, s)) b.1) (strsOf F b.2) := by
  intro a τ b hout h
  rw [hD] at h ⊢
  rw [out_strs hout]
  exact dec_rides decT z a.1 b.1 q.base q.ds a.2 τ (fun c => hd c a.1 b.1) h

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.mark_batch
#print axioms VerifiableInference.Desc.LinkJoin.mark_behind
#print axioms VerifiableInference.Desc.LinkJoin.mark_eq
#print axioms VerifiableInference.Desc.LinkJoin.dec_at
