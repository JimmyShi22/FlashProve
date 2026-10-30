-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PieceOut.lean: from a piece's reduction to its block's own decision. One
statement and its proof.

A piece (`Piece`, Johnson/Desc/Sound/ChainRule.lean) is a block of the description with its stretch
of rounds; its reduction `p.ior.red` is the chain's own fold at the list that holds this one block,
behind the stage's tests. What is owed for a block (`Piece.GoodIn`, Johnson/Desc/Sound/GoodIn.lean)
speaks of `p.ior.red.out a τ = some a'`. A lemma on a kind's plain functions speaks of
`b.decide`. This file is the step between the two, for every block.
  `Piece.out_decide`: where the reduction puts out a', the stage's tests passed; the stretch's
    rounds, as the stage makes them of the transcript, fit the block's declared rounds; the block's
    `decide` said yes on these rounds, shown without the sealed digest, at some groups of columns,
    and returned the record of a'; and the oracles of a' are those that the stage leaves.
Limits. One direction. Which groups of columns `decide` was handed is not said (they are the view's
next columns, regrouped as the declared rounds read them: see the proof's witness). Nothing on runs
of claims.

-/
import Johnson.Desc.Sound.GoodIn
import Johnson.Desc.Sound.FoldLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- **Where a piece's reduction puts out, its block's own decision said yes**: on the stretch's
rounds as `sView` makes them of the transcript (with the rounds put behind), shown without the
sealed digest; the tests in front passed; the rounds fit the block's declared rounds; and what is
put out is the record that the decision returned, with the oracles that the stage leaves. -/
theorem Piece.out_decide (p : Piece C F S Cl W) (a a' : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (h : p.ior.red.out a τ = some a') :
    sTests C p.stage a.2 τ = true ∧
    roundsFit p.b.rounds ((sView C p.stage a.2 τ).rounds ++ p.back) = true ∧
    (∃ gs, p.b.decide a.1 (((sView C p.stage a.2 τ).rounds ++ p.back).map noDigest) gs = .ok a'.1) ∧
    a'.2 = p.ior.imp a.2 τ := by
  have h1 : (p.ior.out a.1 a.2 τ).map (fun x => (x, p.ior.imp a.2 τ)) = some a' := h
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h1
  have h2 : (if sTests C p.stage a.2 τ then p.run a.1 (sView C p.stage a.2 τ) else none) =
      some x := hx
  split at h2
  · rename_i ht
    refine ⟨ht, ?_⟩
    unfold Piece.run foldRun at h2
    rw [chainAt_toOption] at h2
    simp only [List.isEmpty_cons, Bool.false_eq_true, if_false] at h2
    -- the fold at the one block
    generalize hR : (sView C p.stage a.2 τ).rounds ++ p.back = R at h2 ⊢
    generalize hc : (sView C p.stage a.2 τ).opened = c at h2
    simp only [foldBlocks] at h2
    split at h2
    · cases h2
    · rename_i hlen
      have hlen' : (R.splitAt p.b.rounds.length).1.length = p.b.rounds.length := by
        by_contra hne
        exact hlen hne
      cases hs : p.b.step F.ft a.1 (R.splitAt p.b.rounds.length).1 c with
      | error e => simp only [hs] at h2; cases h2
      | ok y =>
        simp only [hs] at h2
        -- nothing is left over: so the block's rounds are all the rounds
        have hrest : (R.splitAt p.b.rounds.length).2 = [] ∧ y.1 = x := by
          cases hr : (R.splitAt p.b.rounds.length).2 with
          | nil =>
            rw [hr] at h2
            cases hd : c.drop y.2 with
            | nil => rw [hd] at h2; exact ⟨rfl, Option.some.inj h2⟩
            | cons _ _ => rw [hd] at h2; cases h2
          | cons _ _ => rw [hr] at h2; cases h2
        have hall : (R.splitAt p.b.rounds.length).1 = R := by
          have := List.take_append_drop p.b.rounds.length R
          rw [List.splitAt_eq] at hrest ⊢
          simp only at hrest ⊢
          rw [hrest.1, List.append_nil] at this
          exact this
        rw [hall, Block.step_eq] at hs
        split at hs
        · rename_i hfit
          split at hs
          · refine ⟨hfit, ⟨regroup ((groupsOf F.ft p.b.rounds (R.map (·.drawn))).map (·.length))
              (c.take ((groupsOf F.ft p.b.rounds (R.map (·.drawn))).flatMap id).length), ?_⟩, rfl⟩
            cases hdz : p.b.decide a.1 (R.map noDigest)
                (regroup ((groupsOf F.ft p.b.rounds (R.map (·.drawn))).map (·.length))
                  (c.take ((groupsOf F.ft p.b.rounds (R.map (·.drawn))).flatMap id).length)) with
            | error e => rw [hdz] at hs; cases hs
            | ok z =>
              rw [hdz] at hs
              have : (Except.ok (z, _) : Except String (S × Nat)) = .ok y := hs
              cases this
              rw [← hrest.2]
          · cases hs
        · cases hs
  · cases h2

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.Piece.out_decide
