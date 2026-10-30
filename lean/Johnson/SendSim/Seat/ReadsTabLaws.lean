-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/ReadsTabLaws.lean: the public test on queried positions of ReadsTest.lean is
the test on the two short tables of ReadsTab.lean.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. F is any description, bs any list of sub-protocols.
  readsWithinB_tab  readsWithinB F P n₀ = readsWithinT (readsTab F.roundsDeclaredByBlocks) P n₀, for all public
                    numbers P and all n₀.
  treesOf_cut       If every member of bs has as many lists of oracle messages as rounds, then for
                    every place p the number of trees in front of the first member at p (treesOf bs
                    at the members in front) is treesAt (cutOf bs) p.
  drawnFor_tab      drawnFor F n = drawnTab (readsTab F.roundsDeclaredByBlocks) n.

How it fits. With these two laws the test at a description depends on its table of openings and on
its first chain's rows alone. ReadsAtWritten.lean evaluates the test where both are the library's
written values. Statements on public data: no distribution is named. Meant as steps toward index
privacy (Johnson/WholeKey/Statement.lean); nothing in this folder derives index privacy from them.
Not one of the release's goal statements.

The other names.
  one_round, opensIn_tab, drawnTab_append
                    the steps for one round, one chain, and two tables in a row.
  told_sum          the rounds that tell a tree tell as many trees as all rounds.
  zip_flat_len, zip_flat_sum
                    lengths and sums along a list of sub-protocols.

Limits. General laws on lists; no public file is named. All limits of ReadsTab.lean.
-/
import Johnson.SendSim.Seat.ReadsTab

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc OnBytes.SendSim.At
open Johnson.Prover.Send (shapeAt)
open VerifiableInference.PlanWritten (cutOf toldRounds)

variable {Xi : Type}

/-! ## The positions that are sampled for a tree -/

/-- One round's openings. -/
theorem one_round (c n p : Nat) : ∀ l : List (Fmt.Shape × Fmt.TreeSource),
    (((l.map fun o => (srcOf c o.2, p)).filter fun x => x.1 == (0, n)).map (·.2)).sum =
      (l.filter fun o => srcOf c o.2 == (0, n)).length * p
  | [] => by simp
  | o :: l => by
    have ih := one_round c n p l
    rw [List.map_cons, List.filter_cons, List.filter_cons]
    cases h : srcOf c o.2 == (0, n)
    · simpa [h] using ih
    · simp only [h, if_true, List.map_cons, List.sum_cons, List.length_cons, ih, Nat.succ_mul]
      omega

theorem drawnTab_append (A B : List ((Nat × Nat) × Nat)) (n : Nat) :
    drawnTab (A ++ B) n = drawnTab A n + drawnTab B n := by
  unfold drawnTab
  rw [List.filter_append, List.map_append, List.sum_append]

/-- One chain's rounds. -/
theorem opensIn_tab (c n : Nat) : ∀ ds : List Fmt.DeclaredRound,
    opensIn c n ds = drawnTab (opensTab c ds) n
  | [] => rfl
  | d :: ds => by
    have ih := opensIn_tab c n ds
    have e : opensTab c (d :: ds) =
        (d.opens.map fun o => (srcOf c o.2, d.entry.poss)) ++ opensTab c ds := by
      unfold opensTab
      rw [List.flatMap_cons]
    rw [e, drawnTab_append, ← ih]
    show _ + _ = _
    congr 1
    exact (one_round c n d.entry.poss d.opens).symm

/-- **The positions that are sampled for a tree, off the table.** -/
theorem drawnFor_tab (F : FileDescription Xi) (n : Nat) : drawnFor F n = drawnTab (readsTab F.roundsDeclaredByBlocks) n := by
  unfold drawnFor readsTab
  rw [drawnTab_append, drawnTab_append, opensIn_tab, opensIn_tab, opensIn_tab]

/-- **The test of ReadsTest.lean is the test on the table.** -/
theorem readsWithinB_tab (F : FileDescription Xi) (P : K1.Par) (n₀ : Nat) :
    readsWithinB F P n₀ = readsWithinT (readsTab F.roundsDeclaredByBlocks) P n₀ := by
  unfold readsWithinB readsWithinT
  congr 1
  funext k
  cases ((Own.treesMade P.codes P.sent).getD {}).tree[k]? with
  | none => rfl
  | some τ => simp only [drawnFor_tab]

/-! ## The trees in front of a place -/

/-- The rounds that tell a tree tell as many trees as all rounds. -/
theorem told_sum {α : Type} : ∀ (l : List (List α)) (k : Nat),
    ((((l.zipIdx k).filter fun x => !x.1.isEmpty).map fun x => (x.2, x.1)).map
      (·.2.length)).sum = (l.map (·.length)).sum
  | [], _ => rfl
  | a :: l, k => by
    have ih := told_sum l (k + 1)
    rw [List.zipIdx_cons, List.filter_cons]
    cases a with
    | nil =>
      simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, if_false, List.map_cons,
        List.length_nil, List.sum_cons, Nat.zero_add]
      exact ih
    | cons x xs =>
      simp only [List.isEmpty_cons, Bool.not_false, if_true, List.map_cons, List.sum_cons]
      rw [ih]

variable {S Cl : Type}

theorem zip_flat_len : ∀ (pre : List (Block S Cl)),
    (∀ b ∈ pre, b.oracles.length = b.rounds.length) →
    (pre.flatMap fun b => b.rounds.zip b.oracles).length = (pre.flatMap (·.rounds)).length
  | [], _ => rfl
  | b :: pre, h => by
    rw [List.flatMap_cons, List.flatMap_cons, List.length_append, List.length_append,
      zip_flat_len pre fun x hx => h x (List.mem_cons_of_mem _ hx), List.length_zip,
      h b (List.mem_cons_self ..), Nat.min_self]

theorem zip_flat_sum : ∀ (pre : List (Block S Cl)),
    (∀ b ∈ pre, b.oracles.length = b.rounds.length) →
    ((pre.flatMap fun b => b.rounds.zip b.oracles).map (·.2.length)).sum =
      (pre.map fun b => (b.oracles.map (·.length)).sum).sum
  | [], _ => rfl
  | b :: pre, h => by
    have e : (b.rounds.zip b.oracles).map (·.2.length) = b.oracles.map (·.length) := by
      have := List.map_snd_zip (l₁ := b.rounds) (l₂ := b.oracles)
        (Nat.le_of_eq (h b (List.mem_cons_self ..)))
      rw [← this, List.map_map, this]
      rfl
    rw [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, e,
      zip_flat_sum pre fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- **The trees in front of a place, off the rows.** -/
theorem treesOf_cut (bs : List (Block S Cl)) (h : ∀ b ∈ bs, b.oracles.length = b.rounds.length)
    (p : Place) :
    treesOf bs (bs.takeWhile (·.place != p)) = treesAt (cutOf bs) p := by
  have hpre : ∀ b ∈ bs.takeWhile (·.place != p), b.oracles.length = b.rounds.length :=
    fun b hb => h b ((List.takeWhile_prefix _).subset hb)
  have e : (bs.flatMap fun b => b.rounds.zip b.oracles) =
      ((bs.takeWhile (·.place != p)).flatMap fun b => b.rounds.zip b.oracles) ++
        ((bs.dropWhile (·.place != p)).flatMap fun b => b.rounds.zip b.oracles) := by
    rw [← List.flatMap_append, List.takeWhile_append_dropWhile]
  unfold treesOf
  rw [e, ← zip_flat_len _ hpre, List.take_left' rfl, zip_flat_sum _ hpre]
  unfold treesAt cutOf
  rw [List.takeWhile_map, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun b _ => (told_sum b.oracles 0).symm)

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.readsWithinB_tab
#print axioms OnBytes.SendSim.Seat.treesOf_cut
