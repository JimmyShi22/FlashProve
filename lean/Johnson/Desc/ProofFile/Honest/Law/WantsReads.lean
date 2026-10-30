-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/WantsReads.lean: a `Want` of a tree is a read of the description,
and a read of a stored table is a `Want`: one direction each (both lemmas are on the declared
rounds' `wantsDecl`). A `Want` names what is read: a tree and a leaf, or a stored table and a
position. The library's reduction reads by `Want`s (`wantsOf`, OnBytes/Maker/Whole.lean), which at
fitting data are the declared rounds' (`wantsDecl`, `WantsAre`, Johnson/Desc/BlockSlot.lean).
Honest/Frame.lean reads by `readsOf`. Both go through the declared rounds in the same order and cut
the drawn positions in the same way. So a `Want` of a tree's leaf is a read of that tree at that
position (`want_tree`). And a read of a stored table is a `Want` of that table at that position; and
the position is below the depth of some declared stored entry (not tied to that table)
(`read_table`).

  1  `want_tree`   a `Want` of a tree is a read of it
  2  `read_table`   a read of a stored table is a `Want` of it
  3  `numAt_src`   a tree's number over the file, from the chain that sent it and its number there
  4  `bare_first`   the first chain without its sealing round

Limits.
  * Lists are compared by their members alone.
  * The lemmas prove no property of a prover or a protocol.
-/
import Fmt.Rules6Laws
import Johnson.Desc.BlockSlot
import Johnson.Desc.ProofFile.Honest.Law.StratRun
import Johnson.Desc.ProofFile.Honest.Law.Rule.Bare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (Want)

variable {Xi : Type}

/-! ## 1 A `Want` of a tree is a read of it -/

theorem want_tree (num : Fmt.TreeSource → Nat) (chain ft : Nat)
    (stored : Nat → Nat → Option (List UInt64)) (tree : Fmt.TreeSource → Option (Place × Table)) :
    ∀ (l : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn) (j x : Nat),
    Want.tree j x ∈ wantsDecl num l Rs → ∃ r ∈ l, ∃ o ∈ r.opens, j = num o.2 ∧
      ∃ q ∈ readsOf chain ft stored tree l Rs, q.src = some (srcOf chain o.2) ∧ q.pos = x
  | [], _, _, _, h => by simp [wantsDecl] at h
  | _ :: _, [], _, _, h => by simp [wantsDecl] at h
  | d :: ds, R :: Rs, j, x, h => by
    have h' : Want.tree j x ∈ (d.stored.flatMap fun s =>
        (Fmt.listOf ((Fmt.partOf s R.poss).map (· % 2 ^ s.sh.a))).map fun x =>
          Want.table s.item x) ++
      (d.opens.flatMap fun o =>
        (Fmt.listOf (R.poss.map (· % 2 ^ o.1.a))).map fun x => Want.tree (num o.2) x) ++
      wantsDecl num ds Rs := h
    rcases List.mem_append.1 h' with g | g
    · rcases List.mem_append.1 g with g | g
      · obtain ⟨s, -, hs⟩ := List.mem_flatMap.1 g
        obtain ⟨y, -, e⟩ := List.mem_map.1 hs
        cases e
      · obtain ⟨o, ho, hs⟩ := List.mem_flatMap.1 g
        obtain ⟨y, hy, e⟩ := List.mem_map.1 hs
        cases e
        refine ⟨d, List.mem_cons_self, o, ho, rfl,
          (⟨o.1.tree - ft, x, none, some (srcOf chain o.2), (tree o.2).map (·.1),
            (tree o.2).map (·.2.col x), o.1.W⟩ : Read), ?_, rfl, rfl⟩
        show _ ∈ (d.stored.flatMap fun s =>
            (Fmt.listOf ((Fmt.partOf s R.poss).map (· % 2 ^ s.sh.a))).map fun x =>
              (⟨Fmt.storedKey s.item, x, some s.item, none, none, stored s.item x, s.sh.W⟩ :
                Read)) ++
          (d.opens.flatMap fun o =>
            (Fmt.listOf (R.poss.map (· % 2 ^ o.1.a))).map fun x =>
              (⟨o.1.tree - ft, x, none, some (srcOf chain o.2), (tree o.2).map (·.1),
                (tree o.2).map (·.2.col x), o.1.W⟩ : Read)) ++
          readsOf chain ft stored tree ds Rs
        exact List.mem_append_left _ (List.mem_append_right _
          (List.mem_flatMap.2 ⟨o, ho, List.mem_map.2 ⟨x, hy, rfl⟩⟩))
    · obtain ⟨r, hr, o, ho, e, q, hq, e1, e2⟩ := want_tree num chain ft stored tree ds Rs j x g
      exact ⟨r, List.mem_cons_of_mem _ hr, o, ho, e, q, List.mem_append_right _ hq, e1, e2⟩

/-! ## 2 A read of a stored table is a `Want` of it -/

theorem read_table (num : Fmt.TreeSource → Nat) (chain ft : Nat)
    (stored : Nat → Nat → Option (List UInt64)) (tree : Fmt.TreeSource → Option (Place × Table)) :
    ∀ (l : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn) (q : Read),
    q ∈ readsOf chain ft stored tree l Rs → ∀ i, q.item = some i →
    Want.table i q.pos ∈ wantsDecl num l Rs ∧ ∃ r ∈ l, ∃ s ∈ r.stored, q.pos < 2 ^ s.sh.a
  | [], _, _, h, _, _ => by simp [readsOf] at h
  | _ :: _, [], _, h, _, _ => by simp [readsOf] at h
  | d :: ds, R :: Rs, q, h, i, hi => by
    have h' : q ∈ (d.stored.flatMap fun s =>
        (Fmt.listOf ((Fmt.partOf s R.poss).map (· % 2 ^ s.sh.a))).map fun x =>
          (⟨Fmt.storedKey s.item, x, some s.item, none, none, stored s.item x, s.sh.W⟩ :
            Read)) ++
      (d.opens.flatMap fun o =>
        (Fmt.listOf (R.poss.map (· % 2 ^ o.1.a))).map fun x =>
          (⟨o.1.tree - ft, x, none, some (srcOf chain o.2), (tree o.2).map (·.1),
            (tree o.2).map (·.2.col x), o.1.W⟩ : Read)) ++
      readsOf chain ft stored tree ds Rs := h
    have hW : wantsDecl num (d :: ds) (R :: Rs) = (d.stored.flatMap fun s =>
        (Fmt.listOf ((Fmt.partOf s R.poss).map (· % 2 ^ s.sh.a))).map fun x =>
          Want.table s.item x) ++
      (d.opens.flatMap fun o =>
        (Fmt.listOf (R.poss.map (· % 2 ^ o.1.a))).map fun x => Want.tree (num o.2) x) ++
      wantsDecl num ds Rs := rfl
    rcases List.mem_append.1 h' with g | g
    · rcases List.mem_append.1 g with g | g
      · obtain ⟨s, hs, hq⟩ := List.mem_flatMap.1 g
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hq
        cases hi
        refine ⟨?_, d, List.mem_cons_self, s, hs, ?_⟩
        · rw [hW]
          exact List.mem_append_left _ (List.mem_append_left _
            (List.mem_flatMap.2 ⟨s, hs, List.mem_map.2 ⟨y, hy, rfl⟩⟩))
        · obtain ⟨u, -, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ y).1 hy)
          exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · obtain ⟨o, -, hq⟩ := List.mem_flatMap.1 g
        obtain ⟨y, -, rfl⟩ := List.mem_map.1 hq
        cases hi
    · obtain ⟨a, r, hr, s, hs, b⟩ := read_table num chain ft stored tree ds Rs q g i hi
      rw [hW]
      exact ⟨List.mem_append_right _ a, r, List.mem_cons_of_mem _ hr, s, hs, b⟩

/-! ## 3 A tree's number over the file -/

theorem numAt_src (t₁ t₂ chain : Nat) (o : Fmt.TreeSource) : numAt t₁ t₂ chain o =
    (if (srcOf chain o).1 = 0 then 0 else if (srcOf chain o).1 = 1 then t₁ else t₁ + t₂) +
      (srcOf chain o).2 := by
  cases o <;> rfl

/-! ## 4 The first chain without its sealing round -/

/-- The first chain's reads without the sealing round are among its reads. -/
theorem bare_first (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (l : List Fmt.DeclaredRound)
    (dr tail : List Fmt.Drawn) (hl : l.dropLast.length = dr.length) (q : Read)
    (hq : q ∈ readsOf chain ft stored tree l.dropLast dr) :
    q ∈ readsOf chain ft stored tree l (dr ++ tail) := by
  have e : l = l.dropLast ++ l.drop l.dropLast.length := by
    have h1 : l.dropLast = l.take l.dropLast.length := by
      rw [List.length_dropLast, List.dropLast_eq_take]
    conv_lhs => rw [← List.take_append_drop l.dropLast.length l, ← h1]
  rw [e, readsOf_append _ _ _ _ _ _ _ _ hl]
  exact List.mem_append_left _ hq

end ProofFile.Honest

#print axioms ProofFile.Honest.want_tree
#print axioms ProofFile.Honest.read_table
#print axioms ProofFile.Honest.numAt_src
#print axioms ProofFile.Honest.bare_first
