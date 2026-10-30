-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/CarryRoots.lean: THE SECOND INSTANCE of Johnson/Goal/Meaning/CarryDriver.lean's
Carried: RootsStep (Johnson/Desc/K12/Law/RootsFold.lean: the block's test on the plan · a yes
of its decision from s to s' ⇒ roots s' = roots s + rootsOf b.rounds), with R₀ := "the count is as
it was". General in the record and in the reader "roots".

  Same roots: roots t = roots s.
  carried_roots: **Carried (RootsStep roots) (Same roots).**
  wholeP_of_quiet: a block whose rounds declare no root and all of whose functions leave the count.
  roots_at_take: at every cut of a list all of whose blocks have the sentence: from the fold's
      return alone, at any first record: roots r.1 = roots s + rootsOf (declOf (l.take k));
      the tests on the plan of the blocks of l.take k are a premise.
      By foldBlocks_roots.
OBJECT: any list of blocks.
USER: Johnson/IMR/RootsCut.lean.
LETTERS: T, Cl, roots: free.

Compiled with the whole library.
Limits. Book-keeping. Nothing on soundness.
-/
import Johnson.Goal.Meaning.CarryDriver
import Johnson.Desc.K12.Law.RootsFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open VerifiableInference.Desc
open VerifiableInference.Desc.Keeps (Decides Fn FnCl)
open H2K.First (RootsStep rootsOf_append declOf foldBlocks_roots rootsStep_quiet)
open Johnson.G.OfPlan (rootsOf)

variable {T Cl : Type}

/-- The count is as it was. -/
def Same (roots : T → Nat) : T → T → Prop := fun s t => roots t = roots s

/-- **The second instance: a yes of the block adds to the count just what its declared rounds
send.** -/
theorem carried_roots (roots : T → Nat) :
    Carried (Cl := Cl) (RootsStep roots) (Same roots) where
  refl _ := rfl
  trans _ _ _ h₁ h₂ := Eq.trans h₂ h₁
  under u W := fun hp s s' rs gs h => by
    rw [u.1.1]
    exact W (u.2.1 hp) s s' rs gs (u.1.2 s rs gs s' h)
  quiet h0 _ W := rootsStep_quiet roots _ (by rw [h0]; rfl) fun s s' rs gs h => W s rs gs s' h
  andThen {n p q} W₁ W₂ := fun hp s s' rs gs h => by
    have hp' : (p.planOk && q.planOk) = true := hp
    rw [Bool.and_eq_true] at hp'
    obtain ⟨m, h1, h2⟩ := Keeps.ebind_ok h
    show roots s' = roots s + rootsOf (p.rounds ++ q.rounds)
    rw [rootsOf_append, W₂ hp'.2 _ _ _ _ h2, W₁ hp'.1 _ _ _ _ h1, Nat.add_assoc]

/-- A block that sends nothing and leaves the count, with its runs. -/
theorem wholeP_of_quiet (roots : T → Nat) {b : Block T Cl} (h0 : rootsOf b.rounds = 0)
    (W : Keeps.Whole (Same roots) b) : WholeP (RootsStep roots) (Same roots) b :=
  ⟨rootsStep_quiet roots b h0 fun s s' rs gs h => W.1 s rs gs s' h, W.2.1, W.2.2⟩

/-- **At every cut of a list all of whose blocks have the sentence**: from the fold's return alone,
at any first record; the blocks' tests on the plan are a premise. -/
theorem roots_at_take (roots : T → Nat) (ft : Nat) (l : List (Block T Cl))
    (hl : ∀ b ∈ l, RootsStep roots b) (k : Nat) (hp : ∀ b ∈ l.take k, b.planOk = true) (s : T)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r : T × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft (l.take k) s rs cols = .ok r) :
    roots r.1 = roots s + rootsOf (declOf (l.take k)) :=
  foldBlocks_roots roots ft (l.take k) (fun b hb => hl b (List.mem_of_mem_take hb)) hp s rs cols r h

#print axioms carried_roots
#print axioms roots_at_take

end Meaning.Carry
