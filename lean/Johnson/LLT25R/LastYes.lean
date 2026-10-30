-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastYes.lean: A PIECE THAT HOLDS A BLOCK AS THE MAKER LAYS IT SAYS YES ONLY
WHERE THE BLOCK DOES, AND HANDS ON WHAT WAS HANDED TO THE CHAIN: general; and at the first, second
and fourth piece of the proof file's own last chain.

Why. The rules for the promise behind the last chain's quiet blocks (`rowZero_prom`,
`rowOne_prom`, `rowThree_owed`, Johnson/Desc/Last/ShapeRows.lean) ask of the piece one condition,
`YesAtOwn x b`: where x hands a statement on, what was handed to the chain is as it was, and b's
decision says yes from the chain's own record in front to the one behind, at some rounds and groups.
Its head names that as owed by "a law: the piece's out is its block's yes" and the seat. Here it is,
IN THAT CONDITION's OWN WORDS (the file is not imported):
`YesAtOwn x b` unfolds to the statements below.
  `held_yes`: general: a piece x with `x.b = held b` (Johnson/Desc/Sound/PaidAtDesc.lean).
  `yes_zero_pure`, `yes_one_pure`, `yes_three_pure`: at `pieceZeroAt`, `pieceOneAt`, `pieceThreeAt`
    of FL (LastSeat.lean), at b := `batchLinearConstraintsSecondPart (p14At Z)`, `takenSources (c2 N)`, `end₃
    [batchLinearConstraintsSecondPart (p14At Z), takenSources (c2 N), c2 N]`, ALL AT THE FILE's OWN TYPE OF CLAIMS:
    carrying a block to another type of claims turns no sign of its decision.
Every "there is": rs, gs: the rounds and the groups of opened leaves at which the block says yes:
those that the fold shows it.
Limits. Nothing on what the blocks' yes is worth. Nothing on soundness.
Here it is, in that condition's own words (lines 86-88 of ShapeRows.lean). This file does not import
that one; LastQuiet.lean imports both and hands these statements over as `YesAtOwn`: so
Lean holds there that they are that condition.
  `held_yes`: general: a piece x with `x.b = held b` (Johnson/Desc/Sound/PaidAtDesc.lean).
  `yes_zero_pure`, `yes_one_pure`, `yes_three_pure`: at `pieceZeroAt`, `pieceOneAt`, `pieceThreeAt`
    of FL (LastSeat.lean), at b := `batchLinearConstraintsSecondPart (p14At Z)`, `takenSources (c2 N)`, `end₃
    [batchLinearConstraintsSecondPart (p14At Z), takenSources (c2 N), c2 N]`, ALL AT THE FILE's OWN TYPE OF CLAIMS:
    carrying a block to another type of claims turns no sign of its decision.
Every "there is": rs, gs: the rounds and the groups of opened leaves at which the block says yes:
those that the fold shows it.
Limits. Nothing on what the blocks' yes is worth. Nothing on soundness.
-/
import Johnson.LLT25R.LastSeat
import Johnson.Desc.Sound.ExtHeardProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace LLT25
open OnBytes OnBytes.Maker
open _root_.Run
open _root_.Run.PQ (CK)
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Third (S₃ takenSources batchLinearConstraintsSecondPart end₃)
open VerifiableInference.Desc.First (S)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At ownAt)

/-- **A held piece's yes is its block's yes, and it hands on what was handed.** -/
theorem held_yes {P σ Cl' W : Type} {C : CK} {F : Frame} (b : Block σ Cl')
    (x : Piece C F (P × σ) Cl' W) (hx : x.b = held b) :
    ∀ a τ c, x.ior.red.out a τ = some c →
      c.1.1 = a.1.1 ∧ ∃ rs gs, b.decide a.1.2 rs gs = .ok c.1.2 := by
  intro a τ c hb
  obtain ⟨s', k, hst, hrest⟩ := foldConsOk (chainAtOk (pieceOk x a τ c hb))
  obtain ⟨gs, hd⟩ := stepOk hst
  rw [hx] at hd
  obtain ⟨s, hs, he⟩ := mapOk (x := (below b).decide a.1.2 _ gs) hd
  have e' : s' = c.1 := by
    have h0 := hrest
    simp only [foldBlocks] at h0
    exact congrArg Prod.fst (Except.ok.inj h0)
  have hs' : (if viewWordsBelowPrime ⟨_, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩
      then b.decide a.1.2 _ gs else .error "a word is not below the prime") = .ok s := hs
  split at hs'
  · subst e'
    have he' : (a.1.1, s) = c.1 := he
    have e2 : c.1.2 = s := (congrArg Prod.snd he').symm
    exact ⟨(congrArg Prod.fst he').symm, _, gs, e2 ▸ hs'⟩
  · exact nomatch hs'

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (A : SharedSeat) (N : H2U.Places4)
  (c : Chain S Cl) {Cells Tok : Type} (D : WholeD)
  (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two) (frameAt D (allOf D) D.key₃ (FL o mk Z A N
      c).lastChainFirstTreeNumber) (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) × (FL
                    o mk Z A N c).S₃) (Wit Cells Tok MsgT) ds)

/-- At the first piece: K14's second part. -/
theorem yes_zero_pure : ∀ a τ e, (pieceZeroAt (FL o mk Z A N c) D (c0 Z) rest₃).ior.red.out a τ =
    some e →
    e.1.1 = a.1.1 ∧ ∃ rs gs, (batchLinearConstraintsSecondPart (p14At Z) : Block S₃ Cl).decide a.1.2 rs gs = .ok e.1.2 :=
  held_yes (c0 Z) (pieceZeroAt (FL o mk Z A N c) D (c0 Z) rest₃) rfl

/-- At the second piece: the taken trees' sources. -/
theorem yes_one_pure : ∀ a τ e, (pieceOneAt (FL o mk Z A N c) D (c0 Z) (c1 N) rest₃).ior.red.out a τ
    = some e →
    e.1.1 = a.1.1 ∧ ∃ rs gs, (takenSources (c2 N)).decide a.1.2 rs gs = .ok e.1.2 :=
  held_yes (c1 N) (pieceOneAt (FL o mk Z A N c) D (c0 Z) (c1 N) rest₃) rfl

/-- At the fourth piece: the chain's end. -/
theorem yes_three_pure : ∀ a τ e, (pieceThreeAt (FL o mk Z A N c) D (c0 Z) (c1 N) (c2 N) (c3 Z N)
    rest₃).ior.red.out a τ = some e →
    e.1.1 = a.1.1 ∧ ∃ rs gs, (end₃ [batchLinearConstraintsSecondPart (p14At Z), takenSources (c2 N), c2 N] : Block S₃
        Cl).decide a.1.2 rs gs = .ok e.1.2 :=
  held_yes (c3 Z N) (pieceThreeAt (FL o mk Z A N c) D (c0 Z) (c1 N) (c2 N) (c3 Z N) rest₃) rfl

end LLT25

#print axioms LLT25.yes_zero_pure
#print axioms LLT25.yes_one_pure
#print axioms LLT25.yes_three_pure
#print axioms LLT25.held_yes
