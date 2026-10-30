-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MergeSameYes.lean: TWO BLOCKS WITH THE SAME DECLARED ROUNDS AND THE SAME YES OWE
THE SAME, whatever the words of their refusals. Small lemmas; the wider form of
Johnson/Desc/Sound/MergeSame.lean.

Why. Two wrappers laid around a block in either order (the strict reading `below` and
`Block.liftPart`; a guard and a lift) give two blocks that say yes at the same arguments, with the
same record, and refuse under other names: so they are not one term, and `Block.Same` (an equation
of the two `decide`) does not hold of them. The chain's decision drops a refusal's words
(`foldRun`): a piece's debt cannot tell the two apart.

Main names:
  `Block.SameYes b b'`: the same declared rounds; `decide` gives `.ok s'` at the one just where it
    does at the other.
  `Block.Same.yes`: `Same` gives it.
  `step_sameYes`, `foldBlocks_sameYes`, `chainAt_sameYes`, `foldRun_sameYes`.
  **`goodIn_sameYes`**: `p.GoodIn …` gives `{ p with b := B' }.GoodIn …` at the same promises,
    relations, extractor and errors.

Limits: as MergeSame.lean's: of a piece's debt alone: the fields that the test on the plan and a
link's runs of claims read are left free. Nothing on acceptance; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MergeSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl : Type}

/-- The same declared rounds, and the same yes. -/
def Block.SameYes (b b' : Block S Cl) : Prop :=
  b.rounds = b'.rounds ∧ ∀ s rs gs s', b.decide s rs gs = .ok s' ↔ b'.decide s rs gs = .ok s'

theorem Block.Same.yes {b b' : Block S Cl} (h : b.Same b') : b.SameYes b' :=
  ⟨h.1, fun s rs gs s' => by rw [h.2]⟩

theorem step_sameYes {b b' : Block S Cl} (h : b.SameYes b') (ft : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (k : Nat) :
    b.step ft s rs cols = .ok (s', k) ↔ b'.step ft s rs cols = .ok (s', k) := by
  rw [step_iff, step_iff]
  unfold Block.Fits Block.shown Block.want
  rw [h.1, h.2]

theorem foldBlocks_sameYes (ft : Nat) {b b' : Block S Cl} (h : b.SameYes b')
    (l : List (Block S Cl)) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (r : S × List Fmt.RoundView × List OpenedColumn) :
    foldBlocks ft (b :: l) s rs cols = .ok r ↔ foldBlocks ft (b' :: l) s rs cols = .ok r := by
  rw [Merges.foldCons_iff, Merges.foldCons_iff, h.1]
  constructor
  · rintro ⟨hl, s', k, hs, hr⟩
    exact ⟨hl, s', k, (step_sameYes h ft _ _ _ _ _).1 hs, hr⟩
  · rintro ⟨hl, s', k, hs, hr⟩
    exact ⟨hl, s', k, (step_sameYes h ft _ _ _ _ _).2 hs, hr⟩

theorem chainAt_sameYes (n n' : String) (ft : Nat) {b b' : Block S Cl} (h : b.SameYes b')
    (l : List (Block S Cl)) (s s' : S) (v : Fmt.View) :
    chainAt n ft (b :: l) s v = .ok s' ↔ chainAt n' ft (b' :: l) s v = .ok s' := by
  rw [Merges.chainAt_iff, Merges.chainAt_iff, foldBlocks_sameYes ft h]
  exact Iff.rfl

end VerifiableInference.Desc

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed BadFam Tr)

variable {S Cl W : Type} {C : CK} {F : Frame}

theorem foldRun_sameYes (F : Frame) (n n' : String) {b b' : Block S Cl} (h : b.SameYes b')
    (l : List (Block S Cl)) (back : List Fmt.RoundView) :
    foldRun F n (b :: l) back = foldRun F n' (b' :: l) back := by
  funext s v
  exact toOption_congr fun a => chainAt_sameYes n n' F.ft h l s a _

/-- **WHAT A PIECE OWES AT A BLOCK IT OWES AT EVERY BLOCK WITH THE SAME ROUNDS AND THE SAME YES.**
-/
theorem goodIn_sameYes (p : Piece C F S Cl W) (B' : Block S Cl) (h : p.b.SameYes B')
    (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop) (g : p.GoodIn on on' R R') :
    ({ p with b := B' } : Piece C F S Cl W).GoodIn on on' R R' := by
  have hr : ({ p with b := B' } : Piece C F S Cl W).run = p.run :=
    (foldRun_sameYes F p.b.name B'.name h [] p.back).symm
  have key : ∀ r : S → Fmt.View → Option S, r = p.run →
      ∀ a, on a → Doomed (uLT C p.ds) p.err fun τ =>
        ∀ b, (stageIOR C p.stage r).red.out a τ = some b →
          on' b ∧ ∀ w, R' b w → R a (p.ext a τ w) := by
    intro r e
    subst e
    exact g
  exact key _ hr


end VerifiableInference.Desc.Sound
