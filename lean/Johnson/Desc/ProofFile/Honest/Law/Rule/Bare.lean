-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/Bare.lean: what declared rounds read at given challenges
(`readsOf`, Honest/Frame.lean), apart from the tables. A read's key, position, item, source and
width are computed from the declared rounds and the challenges alone. So which positions are read of
which tree, and of which stored item, is the same whatever tables are supplied (`treeAsks_any`,
`storedAsks_any`). No part, no coin and no run of a protocol occurs here.

  1  `Read.bare`, `readsOf_bare`, `readsOf_form`   a read without what depends on a table; the reads
     at any tables, so reduced, are the reads with no table supplied; what a read's words are.
     (`Read.bare` is not `bare` of Honest/Law/Play.lean, a challenge without the sealed digest, nor
     `Bare` of Honest/Law/NoHouse/Bare.lean, a sub-protocol without a prover's side.)
  2  `bareReads`, `allBare`, `storedAsks`, `treeAsks`   definitions: the reads of a description's
     three chains with no table supplied; the stored positions; a tree's positions
  3  `pos_bare`, `item_bare`, `allBare_any`, `treeAsks_any`, `storedAsks_any`   at any tables the
     same positions

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription Place)

variable {Xi : Type}

/-! ## 1 A read without its table -/

/-- A read without what depends on a table: its sender and its words. -/
def Read.bare (q : Read) : Read := { q with sender := none, words := none }

theorem readsOf_bare (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    (readsOf chain ft stored tree ds Rs).map Read.bare =
      readsOf chain ft (fun _ _ => none) (fun _ => none) ds Rs
  | [], _ => by simp [readsOf]
  | _ :: _, [] => by simp [readsOf]
  | d :: ds, R :: Rs => by
    have ih := readsOf_bare chain ft stored tree ds Rs
    simp only [readsOf, List.map_append, ih]
    congr 1
    congr 1
    · simp only [List.map_flatMap, List.map_map]
      exact List.flatMap_congr fun s _ => List.map_congr_left fun x _ => rfl
    · simp only [List.map_flatMap, List.map_map]
      exact List.flatMap_congr fun o _ => List.map_congr_left fun x _ => rfl

/-- What a read is: of a stored table, with that table's words at its position; or of a tree, with
the column of the table behind its source. -/
theorem readsOf_form (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn), ∀ q ∈ readsOf chain ft stored tree ds Rs,
    (∃ i, q.item = some i ∧ q.src = none ∧ q.words = stored i q.pos) ∨
      ∃ o : Fmt.TreeSource, q.item = none ∧ q.src = some (srcOf chain o) ∧
        q.words = (tree o).map (·.2.col q.pos)
  | [], _, q, hq => by simp [readsOf] at hq
  | _ :: _, [], q, hq => by simp [readsOf] at hq
  | d :: ds, R :: Rs, q, hq => by
    simp only [readsOf, List.mem_append, List.mem_flatMap, List.mem_map] at hq
    rcases hq with (⟨s, _, x, _, rfl⟩ | ⟨o, _, x, _, rfl⟩) | hq
    · exact Or.inl ⟨s.item, rfl, rfl, rfl⟩
    · exact Or.inr ⟨o.2, rfl, rfl, rfl⟩
    · exact readsOf_form chain ft stored tree ds Rs q hq

/-! ## 2 The reads of three chains, with no table supplied -/

/-- What the three chains' declared rounds read at given challenges, with no table supplied. -/
def bareReads (F : FileDescription Xi) (ρ : Draws) : List Read × List Read × List Read :=
  (readsOf 0 0 (fun _ _ => none) (fun _ => none) F.roundsDeclaredByBlocks.1 ρ.first,
    readsOf 1 0 (fun _ _ => none) (fun _ => none) F.roundsDeclaredByBlocks.2.1 ρ.shared,
    readsOf 2 F.lastChainFirstTreeNumber (fun _ _ => none) (fun _ => none) F.roundsDeclaredByBlocks.2.2 ρ.second)

/-- The three lists, concatenated. -/
def allBare (F : FileDescription Xi) (ρ : Draws) : List Read :=
  (bareReads F ρ).1 ++ (bareReads F ρ).2.1 ++ (bareReads F ρ).2.2

/-- The reads of stored tables: the statement's item, the position. A position that two rounds read
is listed twice. -/
def storedAsks (F : FileDescription Xi) (ρ : Draws) : List (Nat × Nat) :=
  (allBare F ρ).filterMap fun q => q.item.map fun i => (i, q.pos)

/-- The positions read, in any round of the three chains, of tree number `n`, from 0, that chain
number `ch`, from 0, sends: in the order of the views. A position that two rounds read is listed
twice. -/
def treeAsks (F : FileDescription Xi) (ρ : Draws) (ch n : Nat) : List Nat :=
  ((allBare F ρ).filter fun q => q.src == some (ch, n)).map (·.pos)

/-! ## 3 At any tables the same positions -/

theorem pos_bare (s : Option (Nat × Nat)) : ∀ l : List Read,
    ((l.map Read.bare).filter fun q => q.src == s).map (·.pos) =
      (l.filter fun q => q.src == s).map (·.pos)
  | [] => rfl
  | q :: l => by
    have ih := pos_bare s l
    have hq : (q.bare.src == s) = (q.src == s) := rfl
    cases h : q.src == s with
    | true =>
      have h' : (q.bare.src == s) = true := hq.trans h
      simp only [List.map_cons, List.filter_cons, h, h', if_true, ih]
      rfl
    | false =>
      have h' : (q.bare.src == s) = false := hq.trans h
      simp only [List.map_cons, List.filter_cons, h, h', Bool.false_eq_true, if_false, ih]

theorem item_bare : ∀ l : List Read,
    ((l.map Read.bare).filterMap fun q => q.item.map fun i => (i, q.pos)) =
      l.filterMap fun q => q.item.map fun i => (i, q.pos)
  | [] => rfl
  | q :: l => by
    have ih := item_bare l
    have hq : (q.bare.item.map fun i => (i, q.bare.pos)) = q.item.map fun i => (i, q.pos) := rfl
    simp only [List.map_cons, List.filterMap_cons, hq, ih]

section
variable (F : FileDescription Xi) (ρ : Draws) (s₁ s₂ s₃ : Nat → Nat → Option (List UInt64))
  (t₁ t₂ t₃ : Fmt.TreeSource → Option (Place × Table))

/-- The three chains' reads at any tables, so reduced, are the reads with no table supplied. -/
theorem allBare_any :
    (readsOf 0 0 s₁ t₁ F.roundsDeclaredByBlocks.1 ρ.first ++ readsOf 1 0 s₂ t₂ F.roundsDeclaredByBlocks.2.1 ρ.shared ++
      readsOf 2 F.lastChainFirstTreeNumber s₃ t₃ F.roundsDeclaredByBlocks.2.2 ρ.second).map Read.bare = allBare F ρ := by
  rw [List.map_append, List.map_append, readsOf_bare, readsOf_bare, readsOf_bare]
  rfl

/-- **Which positions are read of a tree is the same at any tables.** -/
theorem treeAsks_any (ch n : Nat) :
    ((readsOf 0 0 s₁ t₁ F.roundsDeclaredByBlocks.1 ρ.first ++ readsOf 1 0 s₂ t₂ F.roundsDeclaredByBlocks.2.1 ρ.shared ++
      readsOf 2 F.lastChainFirstTreeNumber s₃ t₃ F.roundsDeclaredByBlocks.2.2 ρ.second).filter fun q =>
        q.src == some (ch, n)).map (·.pos) = treeAsks F ρ ch n := by
  unfold treeAsks
  rw [← allBare_any F ρ s₁ s₂ s₃ t₁ t₂ t₃, pos_bare]

/-- **Which stored positions are read is the same at any tables.** -/
theorem storedAsks_any :
    ((readsOf 0 0 s₁ t₁ F.roundsDeclaredByBlocks.1 ρ.first ++ readsOf 1 0 s₂ t₂ F.roundsDeclaredByBlocks.2.1 ρ.shared ++
      readsOf 2 F.lastChainFirstTreeNumber s₃ t₃ F.roundsDeclaredByBlocks.2.2 ρ.second).filterMap fun q =>
        q.item.map fun i => (i, q.pos)) = storedAsks F ρ := by
  unfold storedAsks
  rw [← allBare_any F ρ s₁ s₂ s₃ t₁ t₂ t₃, item_bare]

end

end ProofFile.Honest

#print axioms ProofFile.Honest.readsOf_bare
#print axioms ProofFile.Honest.readsOf_form
#print axioms ProofFile.Honest.pos_bare
#print axioms ProofFile.Honest.item_bare
#print axioms ProofFile.Honest.allBare_any
#print axioms ProofFile.Honest.treeAsks_any
#print axioms ProofFile.Honest.storedAsks_any
