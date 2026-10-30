-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Keys.lean: where a part's rounds are in its chain's list of
keys (Honest/Law/Rule/Dry.lean: `chainKeys`, `rowKeys`): lemmas on lists of addresses. No coin, no
message and no run of a protocol occurs here.

  1  `takeWhile_split`   before the first entry with a given address
  2  `rowKeys_mem`, `chainKeys_mem`   whose addresses the keys of a list of parts and of a chain
     have
  3  `chainKeys_cons`, `chainKeys_append`   a chain's keys over two consecutive lists of
     sub-protocols
  4  `dryFold_append`   the fold over two consecutive lists

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Dry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place Oracle)

variable {S Cl V W X : Type}

/-! ## 1 Before an address -/

/-- After a list that does not have the address, at an entry that has it, that list is what comes
before the address. -/
theorem takeWhile_split {β : Type} (a : Addr) (h : β) (l₂ : List (Addr × β)) :
    ∀ l₁ : List (Addr × β), (∀ y ∈ l₁, y.1 ≠ a) →
    ((l₁ ++ (a, h) :: l₂).takeWhile fun y => y.1 != a) = l₁
  | [], _ => by
    rw [List.nil_append, List.takeWhile_cons]
    simp
  | y :: l₁, hl => by
    have hy : (y.1 != a) = true := by simpa using hl y (List.mem_cons.2 (Or.inl rfl))
    rw [List.cons_append, List.takeWhile_cons, if_pos hy,
      takeWhile_split a h l₂ l₁ fun z hz => hl z (List.mem_cons_of_mem _ hz)]

/-! ## 2 Whose addresses -/

theorem rowKeys_mem (a : Place) : ∀ (ps : List (Part V W X)) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)), ∀ y ∈ rowKeys a ps j rs,
    y.1.place = a ∧ j ≤ y.1.part
  | [], _, _, y, hy => by cases hy
  | p :: ps, j, rs, y, hy => by
    rw [rowKeys, List.mem_append] at hy
    rcases hy with hy | hy
    · obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy
      exact ⟨rfl, Nat.le_refl _⟩
    · obtain ⟨h1, h2⟩ := rowKeys_mem a ps (j + 1) _ y hy
      exact ⟨h1, by omega⟩

theorem chainKeys_mem (hs : List (Placed V W X)) : ∀ (bs : List (Block S Cl)),
    ∀ y ∈ chainKeys bs hs, y.1.place ∈ bs.map (·.place) := by
  intro bs y hy
  unfold chainKeys at hy
  obtain ⟨b, hb, hy⟩ := List.mem_flatMap.1 hy
  refine List.mem_map.2 ⟨b, hb, ?_⟩
  cases hf : hs.find? fun h => h.place == b.place with
  | none =>
    rw [hf] at hy
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy
    rfl
  | some g =>
    rw [hf] at hy
    exact (rowKeys_mem b.place g.parts 0 _ y hy).1.symm

/-! ## 3 Two consecutive lists -/

theorem chainKeys_append (l₁ l₂ : List (Block S Cl)) (hs : List (Placed V W X)) :
    chainKeys (l₁ ++ l₂) hs = chainKeys l₁ hs ++ chainKeys l₂ hs := by
  unfold chainKeys
  rw [List.flatMap_append]

theorem chainKeys_cons (b : Block S Cl) (bs : List (Block S Cl)) (hs : List (Placed V W X)) :
    chainKeys (b :: bs) hs = chainKeys [b] hs ++ chainKeys bs hs :=
  chainKeys_append [b] bs hs

/-! ## 4 The fold -/

theorem dryFold_append (h₂ : List (Option (State W X → X))) (d₂ : List Fmt.Drawn) :
    ∀ (h₁ : List (Option (State W X → X))) (d₁ : List Fmt.Drawn) (t : State W X),
    d₁.length = h₁.length →
    dryFold (h₁ ++ h₂) (d₁ ++ d₂) t = dryFold h₂ d₂ (dryFold h₁ d₁ t)
  | [], [], _, _ => by
    rw [List.nil_append, List.nil_append]
    rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: h₁, d :: d₁, t, h => by
    show dryFold (h₁ ++ h₂) (d₁ ++ d₂) (dryStep a d t) =
      dryFold h₂ d₂ (dryFold h₁ d₁ (dryStep a d t))
    exact dryFold_append h₂ d₂ h₁ d₁ (dryStep a d t) (by simpa using h)

end ProofFile.Honest

#print axioms ProofFile.Honest.takeWhile_split
#print axioms ProofFile.Honest.rowKeys_mem
#print axioms ProofFile.Honest.chainKeys_mem
#print axioms ProofFile.Honest.chainKeys_append
#print axioms ProofFile.Honest.chainKeys_cons
#print axioms ProofFile.Honest.dryFold_append
