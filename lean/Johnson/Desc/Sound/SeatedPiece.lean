-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/SeatedPiece.lean: a law on a piece passes to the piece that holds, at the same
stretch, a block which says yes only where the piece's own block does. Statements with their
proofs. General in the piece and in the carried record.

Why. A kind's law (`Piece.GoodIn`, Johnson/Desc/Sound/GoodIn.lean) speaks of the piece that holds
the kind's own block b. Whoever lays b into a chain may lay another block c: b with a refusal at a
marked record behind its decision; that again behind a driver's guard. The law then speaks of a
piece that no chain holds. All such c have `c.UnderR b` (Johnson/Desc/Sound/SeatGuardChain.lean):
b's rounds; where c says yes, b says the same yes.
Main names:
  `Piece.seat p c`: p with the block c in the place of its own: the same stretch, extractor, errors.
  `chainAt_one`: a chain of one block says yes just where its fold ends with nothing left over.
  `run_seat`, `out_seat`: a yes of c, on the stretch and as a reduction, is a yes of b with the same
    record and oracles.
  `goodIn_seat`: **the law passes.**
  `andThen_underR`: two such blocks joined say yes only where the two bare blocks joined do: so a
    joined block whose halves are guarded one by one is covered.

What is not claimed. That a given chain lays a block with `UnderR`: to be seen at that chain's text
(a driver's guard: `guarded_underR`; a refusal at a mark: Johnson/Desc/Sound/SeatedGuards.lean).
Nothing in the other direction: a yes of b need not be a yes of c. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SeatGuardChain
import Johnson.Desc.Sound.GoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Doomed)

variable {T Cl W : Type} {C : CK} {F : Frame}

/-- Joined, half by half. -/
theorem andThen_underR {c₁ b₁ c₂ b₂ : Block T Cl} (h₁ : c₁.UnderR b₁) (h₂ : c₂.UnderR b₂)
    (n n' : String) : (c₁.andThen n c₂).UnderR (b₁.andThen n' b₂) := by
  have ho : c₁.openings = b₁.openings := by
    unfold Block.openings
    rw [h₁.1]
  refine ⟨?_, fun s rs gs s' h => ?_⟩
  · show c₁.rounds ++ c₂.rounds = b₁.rounds ++ b₂.rounds
    rw [h₁.1, h₂.1]
  · have h' : (c₁.decide s (rs.take c₁.rounds.length) (gs.take c₁.openings)).bind (fun m =>
        c₂.decide m (rs.drop c₁.rounds.length) (gs.drop c₁.openings)) = .ok s' := h
    rw [h₁.1, ho] at h'
    show (b₁.decide s (rs.take b₁.rounds.length) (gs.take b₁.openings)).bind (fun m =>
      b₂.decide m (rs.drop b₁.rounds.length) (gs.drop b₁.openings)) = .ok s'
    cases hm : c₁.decide s (rs.take b₁.rounds.length) (gs.take b₁.openings) with
    | error e =>
      rw [hm] at h'
      cases h'
    | ok m =>
      rw [hm] at h'
      rw [h₁.2 _ _ _ _ hm]
      exact h₂.2 _ _ _ _ h'

/-- The piece with another block at the same stretch. -/
def Piece.seat (p : Piece C F T Cl W) (c : Block T Cl) : Piece C F T Cl W :=
  ⟨c, p.base, p.ds, p.back, p.ext, p.err⟩

/-- A chain of one block says yes just where its fold ends with nothing left over. -/
theorem chainAt_one (name : String) (ft : ℕ) (b : Block T Cl) (s s' : T) (v : Fmt.View) :
    (chainAt name ft [b] s v).toOption = some s' ↔
      foldBlocks ft [b] s v.rounds v.opened = .ok (s', [], []) := by
  unfold chainAt
  simp only [List.isEmpty_cons, Bool.false_eq_true, if_false]
  cases hfb : foldBlocks ft [b] s v.rounds v.opened with
  | error e => simp [Except.toOption]
  | ok z =>
    obtain ⟨s1, rs1, c1⟩ := z
    cases rs1 with
    | cons _ _ => simp [Except.toOption]
    | nil =>
      cases c1 with
      | cons _ _ => simp [Except.toOption]
      | nil => simp [Except.toOption]

/-- On the stretch. -/
theorem run_seat (p : Piece C F T Cl W) (c : Block T Cl) (h : c.UnderR p.b) (s s' : T)
    (v : Fmt.View) (hr : (p.seat c).run s v = some s') : p.run s v = some s' :=
  (chainAt_one p.b.name F.ft p.b s s' ⟨v.rounds ++ p.back, v.opened⟩).2
    (fold_under (.cons h .nil)
      ((chainAt_one c.name F.ft c s s' ⟨v.rounds ++ p.back, v.opened⟩).1 hr))

/-- As a reduction. -/
theorem out_seat (p : Piece C F T Cl W) (c : Block T Cl) (h : c.UnderR p.b) (a b : T × F.E.Str)
    (τ : Iop.Tr (uLT C p.ds)) (hb : (p.seat c).ior.red.out a τ = some b) :
    p.ior.red.out a τ = some b := by
  have hb' : (if sTests C p.stage a.2 τ then (p.seat c).run a.1 (sView C p.stage a.2 τ)
      else none).map (fun xo => (xo, p.ior.imp a.2 τ)) = some b := hb
  show (if sTests C p.stage a.2 τ then p.run a.1 (sView C p.stage a.2 τ)
      else none).map (fun xo => (xo, p.ior.imp a.2 τ)) = some b
  split at hb'
  · rename_i ht
    rw [if_pos ht]
    cases hrun : (p.seat c).run a.1 (sView C p.stage a.2 τ) with
    | none =>
      rw [hrun] at hb'
      cases hb'
    | some s' =>
      rw [hrun] at hb'
      rw [run_seat p c h _ _ _ hrun]
      exact hb'
  · cases hb'

/-- **The law passes to the piece that holds c.** -/
theorem goodIn_seat (p : Piece C F T Cl W) (c : Block T Cl) (h : c.UnderR p.b)
    (on on' : T × F.E.Str → Prop) (R R' : T × F.E.Str → W → Prop) (hl : p.GoodIn on on' R R') :
    (p.seat c).GoodIn on on' R R' := by
  intro a ha
  refine Doomed.mono _ _ ?_ (hl a ha)
  intro τ hτ b hb
  exact hτ b (out_seat p c h a b τ hb)

end VerifiableInference.Desc.Sound
