-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/RowsHeldAt.lean: code switching (the kind K2): THE TABLE OF JOINTS' FIXED
TEST ON THE GROUPS' LISTS OF OPEN ROWS (rowsHeld, Johnson/Desc/First/Borders.lean) ACCEPTS BEHIND
A SWITCH, where the three classes that the switch opens are the only classes of rows that are open
there. NO BLOCK IMPORTS THIS FILE.
  switchRowsOpen m   the three: row m carried · row m (sample 0) · row m position
  all_slice          a stretch of a list all of whose rows are of one kind passes the test's
                     clause on kinds
  rowsHeld_switch    a state whose group number N.groupAt m has not begun its proximity test and
                     has the rows carried :: samples ++ gens, of the kinds plain · plain ·
                     generator; N.rowsAt m carried = (0, 1 + samples.length) · N.rowsAt m position
                     = (1 + samples.length, gens.length): rowsHeld N (switchRowsOpen m) s = true
  rowsHeld_behind    the same at any open set whose classes of rows are these three
                     (rowsHeld_of_filter, BordersKeep.lean)
LIMITS. The two equations on N and «these three alone» are premises: the first two on the list of
rounds, the third a closed fact on the written list of places. No soundness is claimed.

-/
import Johnson.Desc.First.BordersKeep
import Johnson.Top.H0.Tw.K2C.RowKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes

/-- The three classes of rows that the switch into group m opens. -/
def switchRowsOpen (m : Nat) : List Item :=
  [.row m .carried, .row m (.sample 0), .row m .position]

theorem all_slice (l : List OnBytes.Row) (a n : Nat) (h : a + n ≤ l.length) (K : RowKind)
    (hk : ∀ r ∈ (l.drop a).take n, r.kind = K) :
    ((List.range n).all fun j => (l.toArray[a + j]?).any fun r => r.kind == K) = true := by
  rw [List.all_eq_true]
  intro j hj
  have hj' := List.mem_range.1 hj
  have hlt : a + j < l.length := by omega
  rw [List.getElem?_toArray, List.getElem?_eq_getElem hlt, Option.any_some, beq_iff_eq]
  refine hk _ (List.mem_iff_getElem.2 ⟨j, by simp; omega, by simp⟩)

theorem rowsHeld_switch (N : Numbers) (m : Nat) (s : S) {G' : Group} {carried : OnBytes.Row}
    {samples gens : List OnBytes.Row} (hG : s.st.groups[N.groupAt m]? = some G')
    (hrun : G'.inRun = false) (hR : G'.rows = (carried :: samples ++ gens).toArray)
    (kc : carried.kind = .plain) (ks : ∀ r ∈ samples, r.kind = .plain)
    (kg : ∀ r ∈ gens, r.kind = .generator)
    (hc : N.rowsAt m .carried = (0, 1 + samples.length))
    (hq : N.rowsAt m .position = (1 + samples.length, gens.length)) :
    rowsHeld N (switchRowsOpen m) s = true := by
  have hseg : rowSegs (switchRowsOpen m) = [m] := by
    simp [rowSegs, switchRowsOpen, List.eraseDups_cons]
  have hdue : rowsDue N (switchRowsOpen m) m = 1 + samples.length + gens.length := by
    simp [rowsDue, switchRowsOpen, RowClass.inList, hc, hq]
  have h1 : ((List.range (1 + samples.length)).all fun j =>
      (G'.rows[0 + j]?).any fun r => r.kind == RowKind.plain) = true := by
    rw [hR]
    refine all_slice _ 0 _ (by simp; omega) _ fun r hr => ?_
    have e : ((carried :: samples ++ gens).drop 0).take (1 + samples.length) =
        carried :: samples := by
      rw [List.drop_zero, show carried :: samples ++ gens = (carried :: samples) ++ gens from rfl]
      exact List.take_left' (by simp; omega)
    rw [e] at hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact kc
    · exact ks r hr
  have h2 : ((List.range gens.length).all fun j =>
      (G'.rows[1 + samples.length + j]?).any fun r => r.kind == RowKind.generator) = true := by
    rw [hR]
    refine all_slice _ _ _ (by simp; omega) _ fun r hr => ?_
    have e : (carried :: samples ++ gens).drop (1 + samples.length) = gens := by
      rw [show carried :: samples ++ gens = (carried :: samples) ++ gens from rfl]
      exact List.drop_left' (by simp; omega)
    rw [e, List.take_length] at hr
    exact kg r hr
  have hsz : G'.rows.size = 1 + samples.length + gens.length := by
    rw [hR]
    simp
    omega
  unfold rowsHeld
  rw [hseg]
  simp only [List.all_cons, List.all_nil, Bool.and_true, hG, hdue, hrun, hsz]
  simp only [switchRowsOpen, List.all_cons, List.all_nil, beq_self_eq_true,
    RowClass.inList, RowClass.kind, hc, hq, h1, h2, Bool.not_false, Bool.and_self,
    Bool.not_true, Bool.false_or, Bool.and_false, Bool.true_or]

theorem rowsHeld_behind (N : Numbers) (m : Nat) (s : S) (O' : List Item)
    (hO : O'.filter Item.isRow = switchRowsOpen m) {G' : Group} {carried : OnBytes.Row}
    {samples gens : List OnBytes.Row} (hG : s.st.groups[N.groupAt m]? = some G')
    (hrun : G'.inRun = false) (hR : G'.rows = (carried :: samples ++ gens).toArray)
    (kc : carried.kind = .plain) (ks : ∀ r ∈ samples, r.kind = .plain)
    (kg : ∀ r ∈ gens, r.kind = .generator)
    (hc : N.rowsAt m .carried = (0, 1 + samples.length))
    (hq : N.rowsAt m .position = (1 + samples.length, gens.length)) :
    rowsHeld N O' s = true := by
  rw [rowsHeld_of_filter N (switchRowsOpen m) O' (by rw [hO]; rfl)]
  exact rowsHeld_switch N m s hG hrun hR kc ks kg hc hq

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.rowsHeld_switch
#print axioms VerifiableInference.Desc.First.K2.rowsHeld_behind
