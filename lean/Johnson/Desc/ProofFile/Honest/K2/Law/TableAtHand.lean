-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/TableAtHand.lean: UNDER A THREAD's INVARIANT AT A BORDER
(`Thr`, Johnson/Desc/ProofFile/Honest/Thread/Thr.lean): BEHIND ANY ROUNDS PLAYED, THE TABLE AT HAND
OF AN OWN TREE THAT WAS SENT IN FRONT OF THE BORDER SHOWS, BELOW ITS LENGTH, THE COLUMNS OF THE
THREAD's OWN TABLE (`Thread.tableAt`). One lemma; NONE OF THE LIBRARY's GOALS. Nothing on
completeness, soundness or hiding.

  **`table_at_hand`**  the statement
How. A JOIN: clause (H) of the invariant at the source `.own n`; the frame's authors' sealed
`Thread.col_of_handAt` (Honest/Thread/Sent.lean), which does the work; clause (X)'s count of the
trees sent; the text of `Env.add`.
Kin. `add_old` (Honest/Small/ColGroups.lean): the last step, as a lemma of its own; not
called.
Limits. «NOT IN FRONT OF A LAW OVER COINS». THE GROUND: s, m and E stand under hA beside the run's
coins k: of the first kind; hA's clause on the input (`valid`) is of the second. Made term and lemma
that lift the bar: none: the bar is flat. The invariant is a premise; it is taken apart by the
places of its clauses.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Sent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc (Block Place OpenedColumn)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **The table at hand of an earlier own tree.** NOT IN FRONT OF A LAW OVER COINS: the ground
stands in this file's head. -/
theorem table_at_hand (T : Thread Bk S Cl V W X Pb) {b : Nat} {k : Coins Bk} {s : S} {m : Mid W X}
    {E : Env} (hA : Thr T b k s m E) (ps : List Played) (n : Nat) (hn : n < treesTo T.bs b) :
    ∃ u, (E.add ps).tree (.own n) = some u ∧
      ∀ x, x < 2 ^ (T.tableAt (.own n) k m).2.logLength →
        u.2.col x = (T.tableAt (.own n) k m).2.col x := by
  obtain ⟨⟨-, hTr⟩, -, -, -, ⟨-, -, hsent, -, -⟩, -, -⟩ := hA
  obtain ⟨u, hu, hc⟩ := T.col_of_handAt (hTr _
    (List.mem_append.2 (Or.inr (List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩))))
  refine ⟨u, ?_, hc⟩
  show (if n < E.sent then E.tree (.own n) else _) = _
  rw [if_pos (hsent ▸ hn), hu]

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.table_at_hand
