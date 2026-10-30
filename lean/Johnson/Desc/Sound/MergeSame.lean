-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MergeSame.lean: A PIECE'S DEBT DOES NOT SEE A BLOCK'S NAME, PLACE, LISTS OR TEST
ON THE PLAN: two blocks with the same declared rounds and the same `decide` owe the same. Small
lemmas.

Why. A seat may dress a joined block: `{ b with name := …, place := …, before := …, planOk := … }`.
To the fold it is the same block: `foldBlocks` reads a block's rounds, its `step` (rounds and
`decide`) and, for the words of a refusal alone, its name. By syntax it is no `Block.andThen`, so
`Merges` (Johnson/Desc/Sound/MergeFold.lean) does not reach it. Here: what a piece owes at the one
block it owes at the other.

Main names:
  `Block.Same b b'`: the same declared rounds, the same `decide`.
  `step_same`, `foldBlocks_same`, `chainAt_same`, `foldRun_same`: the fold says yes at the same
    views and leaves the same record, under whatever names.
  **`goodIn_same`**: `p.GoodIn …` gives `{ p with b := B' }.GoodIn …` at the same promises,
    relations, extractor and errors.

Limits: of a piece's debt alone: a description's test on the plan (`planOk`, `before`, `oracles`)
and a link's runs of claims DO read the fields that `Same` leaves free. Nothing on acceptance;
nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MergeFuse

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl : Type}

/-- Two blocks that the fold cannot tell apart but by the words of a refusal. -/
def Block.Same (b b' : Block S Cl) : Prop := b.rounds = b'.rounds ∧ b.decide = b'.decide

theorem step_same {b b' : Block S Cl} (h : b.Same b') (ft : Nat) : b.step ft = b'.step ft := by
  funext s rs cols
  unfold Block.step
  rw [h.1, h.2]

theorem foldBlocks_same (ft : Nat) {b b' : Block S Cl} (h : b.Same b') (l : List (Block S Cl))
    (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn) :
    foldBlocks ft (b :: l) s rs cols = .ok r ↔ foldBlocks ft (b' :: l) s rs cols = .ok r := by
  rw [Merges.foldCons_iff, Merges.foldCons_iff, h.1, step_same h]

theorem chainAt_same (n n' : String) (ft : Nat) {b b' : Block S Cl} (h : b.Same b')
    (l : List (Block S Cl)) (s s' : S) (v : Fmt.View) :
    chainAt n ft (b :: l) s v = .ok s' ↔ chainAt n' ft (b' :: l) s v = .ok s' := by
  rw [Merges.chainAt_iff, Merges.chainAt_iff, foldBlocks_same ft h]
  exact Iff.rfl

end VerifiableInference.Desc

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed BadFam Tr)

variable {S Cl W : Type} {C : CK} {F : Frame}

theorem foldRun_same (F : Frame) (n n' : String) {b b' : Block S Cl} (h : b.Same b')
    (l : List (Block S Cl)) (back : List Fmt.RoundView) :
    foldRun F n (b :: l) back = foldRun F n' (b' :: l) back := by
  funext s v
  exact toOption_congr fun a => chainAt_same n n' F.ft h l s a _

/-- **WHAT A PIECE OWES AT A BLOCK IT OWES AT EVERY BLOCK WITH THE SAME ROUNDS AND `decide`.** -/
theorem goodIn_same (p : Piece C F S Cl W) (B' : Block S Cl) (h : p.b.Same B')
    (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop) (g : p.GoodIn on on' R R') :
    ({ p with b := B' } : Piece C F S Cl W).GoodIn on on' R R' := by
  have hr : ({ p with b := B' } : Piece C F S Cl W).run = p.run :=
    (foldRun_same F p.b.name B'.name h [] p.back).symm
  have key : ∀ r : S → Fmt.View → Option S, r = p.run →
      ∀ a, on a → Doomed (uLT C p.ds) p.err fun τ =>
        ∀ b, (stageIOR C p.stage r).red.out a τ = some b →
          on' b ∧ ∀ w, R' b w → R a (p.ext a τ w) := by
    intro r e
    subst e
    exact g
  exact key _ hr


end VerifiableInference.Desc.Sound
