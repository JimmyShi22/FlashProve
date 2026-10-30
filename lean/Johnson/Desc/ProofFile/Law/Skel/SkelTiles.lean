-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/SkelTiles.lean: THE ROUNDS' COLUMN, THE WINDOWS: where every block's
rounds are a window of one list D, at a start that hangs on the block's name, the blocks' rounds in
a row are what the skeletons say; and where the starts are the running sums of the skeletons'
numbers of rounds, and the sum is D's length, they are D. Definitions, statements and proofs.
  `Win D W n r`    r is D's window of r's own length at the start W n. `win_nil`: true of no round
  `flat_rounds`    from `Win` at every block: the rounds in a row, off the skeletons
  `tilesB W ks s`  a test with code: each skeleton that has a round starts where the ones before end
  `tiles_flat`, `rounds_are`
Limits. That a block's rounds are a window of D is a premise: it is the content; the law carries the
places alone. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Skel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk
open VerifiableInference.Desc

variable {S Cl : Type}

/-- r is D's window of r's own length at the start W n. -/
def Win (D : List Fmt.DeclaredRound) (W : String → Nat) (n : String) (r : List Fmt.DeclaredRound) : Prop :=
  r = (D.drop (W n)).take r.length

theorem win_nil (D : List Fmt.DeclaredRound) (W : String → Nat) (n : String) : Win D W n [] := rfl

theorem flatMap_congr_mem {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a (List.mem_cons_self ..),
      flatMap_congr_mem fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem flat_rounds {D : List Fmt.DeclaredRound} {W : String → Nat} {bs : List (Block S Cl)}
    (h : ∀ b ∈ bs, Win D W b.name b.rounds) :
    bs.flatMap (·.rounds) =
      (bs.map skel).flatMap fun k => (D.drop (W k.name)).take k.nRounds := by
  rw [List.flatMap_map]
  exact flatMap_congr_mem h

/-- Each skeleton that has a round starts where the ones before it end. -/
def tilesB (W : String → Nat) : List Skel → Nat → Bool
  | [], _ => true
  | k :: r, s => (k.nRounds == 0 || W k.name == s) && tilesB W r (s + k.nRounds)

theorem tiles_flat (D : List Fmt.DeclaredRound) (W : String → Nat) :
    ∀ (ks : List Skel) (s : Nat), tilesB W ks s = true →
      (ks.flatMap fun k => (D.drop (W k.name)).take k.nRounds) =
        (D.drop s).take (ks.map (·.nRounds)).sum
  | [], s, _ => by simp
  | k :: r, s, h => by
    rw [tilesB, Bool.and_eq_true, Bool.or_eq_true] at h
    have ih := tiles_flat D W r (s + k.nRounds) h.2
    rw [List.flatMap_cons, ih, List.map_cons, List.sum_cons, List.take_add, List.drop_drop]
    congr 1
    rcases h.1 with h0 | hs
    · rw [eq_of_beq h0, List.take_zero, List.take_zero]
    · rw [eq_of_beq hs]

theorem rounds_are {D : List Fmt.DeclaredRound} {W : String → Nat} {bs : List (Block S Cl)}
    {ks : List Skel} (h : ∀ b ∈ bs, Win D W b.name b.rounds) (hk : bs.map skel = ks)
    (ht : tilesB W ks 0 = true) (hn : (ks.map (·.nRounds)).sum = D.length) :
    bs.flatMap (·.rounds) = D := by
  rw [flat_rounds h, hk, tiles_flat D W ks 0 ht, hn, List.drop_zero, List.take_length]

end ProofFile.Sk

#print axioms ProofFile.Sk.win_nil
#print axioms ProofFile.Sk.flatMap_congr_mem
#print axioms ProofFile.Sk.flat_rounds
#print axioms ProofFile.Sk.tiles_flat
#print axioms ProofFile.Sk.rounds_are
