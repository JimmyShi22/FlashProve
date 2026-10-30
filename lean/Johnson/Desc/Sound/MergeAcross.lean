-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MergeAcross.lean: A PIECE'S DEBT DOES NOT SEE THE TYPE OF A BLOCK'S CLAIMS: two
blocks at one record, with the same declared rounds and the same yes, owe the same, though the one
states claims of one type and the other of another, or none. The form of
Johnson/Desc/Sound/MergeSameYes.lean across two types of claims.

Why. A kind's block states its runs of claims at the kind's own type; a seat can lay the block into
a chain whose blocks state none (a maker that keeps name, place, rounds and `decide` and strikes the
lists of claims). The two blocks have two types: no relation between blocks of one type reaches from
the one to the other. The chain's decision reads rounds and `decide` alone.

Main names:
  `Block.YesAcross b b'`: the same declared rounds; `decide` gives `.ok s'` at the one just where it
    does at the other.
  `step_across`, `chainAt_across`, `foldRun_across`.
  **`goodIn_across`**: `p.GoodIn on on' R R'` gives
    `⟨B', p.base, p.ds, p.back, p.ext, p.err⟩.GoodIn on on' R R'`.

Limits: of a piece's debt alone: what a link's runs of claims add is another matter, and the second
block may state none. One block; a list behind it would have to change its type too. Nothing on
acceptance; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MergeSameYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl Cl' : Type}

/-- The same declared rounds, and the same yes; the types of claims may part. -/
def Block.YesAcross (b : Block S Cl) (b' : Block S Cl') : Prop :=
  b.rounds = b'.rounds ∧ ∀ s rs gs s', b.decide s rs gs = .ok s' ↔ b'.decide s rs gs = .ok s'

theorem step_across {b : Block S Cl} {b' : Block S Cl'} (h : b.YesAcross b') (ft : Nat) (s s' : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (k : Nat) :
    b.step ft s rs cols = .ok (s', k) ↔ b'.step ft s rs cols = .ok (s', k) := by
  rw [step_iff, step_iff]
  unfold Block.Fits Block.shown Block.want
  rw [h.1, h.2]

theorem chainAt_across (n n' : String) (ft : Nat) {b : Block S Cl} {b' : Block S Cl'}
    (h : b.YesAcross b') (s s' : S) (v : Fmt.View) :
    chainAt n ft [b] s v = .ok s' ↔ chainAt n' ft [b'] s v = .ok s' := by
  rw [Merges.chainAt_iff, Merges.chainAt_iff, Merges.foldCons_iff, Merges.foldCons_iff, h.1]
  constructor
  · rintro ⟨-, hl, s₁, k, hs, hr⟩
    refine ⟨rfl, hl, s₁, k, (step_across h ft _ _ _ _ _).1 hs, ?_⟩
    rw [foldBlocks] at hr ⊢
    exact hr
  · rintro ⟨-, hl, s₁, k, hs, hr⟩
    refine ⟨rfl, hl, s₁, k, (step_across h ft _ _ _ _ _).2 hs, ?_⟩
    rw [foldBlocks] at hr ⊢
    exact hr

end VerifiableInference.Desc

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed BadFam Tr)

variable {S Cl Cl' W : Type} {C : CK} {F : Frame}

theorem foldRun_across (F : Frame) (n n' : String) {b : Block S Cl} {b' : Block S Cl'}
    (h : b.YesAcross b') (back : List Fmt.RoundView) :
    foldRun F n [b] back = foldRun F n' [b'] back := by
  funext s v
  exact toOption_congr fun a => chainAt_across n n' F.ft h s a _

/-- **WHAT A PIECE OWES AT A BLOCK IT OWES AT A BLOCK OF ANOTHER TYPE OF CLAIMS WITH THE SAME ROUNDS
AND THE SAME YES.** -/
theorem goodIn_across (p : Piece C F S Cl W) (B' : Block S Cl') (h : p.b.YesAcross B')
    (on on' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop) (g : p.GoodIn on on' R R') :
    (⟨B', p.base, p.ds, p.back, p.ext, p.err⟩ : Piece C F S Cl' W).GoodIn on on' R R' := by
  have hr : (⟨B', p.base, p.ds, p.back, p.ext, p.err⟩ : Piece C F S Cl' W).run = p.run :=
    (foldRun_across F p.b.name B'.name h p.back).symm
  have key : ∀ r : S → Fmt.View → Option S, r = p.run →
      ∀ a, on a → Doomed (uLT C p.ds) p.err fun τ =>
        ∀ b, (stageIOR C p.stage r).red.out a τ = some b →
          on' b ∧ ∀ w, R' b w → R a (p.ext a τ w) := by
    intro r e
    subst e
    exact g
  exact key _ hr


end VerifiableInference.Desc.Sound
