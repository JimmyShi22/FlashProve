-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/HeadQuietSame.lean: THE OUTPUT HEAD's QUIET STEP ("H.1.quiet",
`K2.headOpenQ`) LEAVES THE TABLES AND EVERY GROUP's ROWS. No premise but the step's yes.

  TabRowsSame S S'    the two sentences as one relation; reflexive, transitive; `tabRowsSame_fold`
  behindAsks_same  what `firstBehind`'s yes asks and hands on (`BehindAsks`) gives it
  headOpenQ_same   from `headOpenQ P s = .ok s'`: `SameTables s.st s'.st` (the same codes; message
                   by message the same shape and sample rows) and, group by group, the same rows

Why not by `headOpenQ_keeps`. That theorem carries every relation that ALL TEN of the ground's plain
functions keep (`GroundKeeps`). "Every group's rows stay" is no such relation: adding a row breaks
it. So the step's own text is read: it writes the statement by the own messages' joins alone
(`headOpenQ_iff`, `firstBehind_iff`: the field joins), and a join keeps both (`same_join`,
K2Hears/BehindSame.lean; `join_rows`, K2Hears/RowsKept.lean).

THE RELATION IS NAMED TabRowsSame, NOT SameRows (with .refl · .trans;
tabRowsSame_fold): Johnson/Top/H0/K2Hands/SampleChain.lean declares
K2.SameRows for ANOTHER relation (the codes and every message's shape and stored rows): the two
could not be imported together.
Limits. That the step accepts at any state is not shown. Nothing on the ledgers, nor on which
messages a group holds: these the joins turn. No soundness statement.

-/
import Johnson.Top.H0.Tw.K2C.Asks
import Johnson.Top.H0.K2Hears.BehindSame
import Johnson.Top.H0.K2Hears.RowsKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model

/-- The two sentences, as one relation on statements. -/
def TabRowsSame (S S' : Statement) : Prop :=
  SameTables S S' ∧ ∀ g : Nat, (S'.groups[g]?).map (·.rows) = (S.groups[g]?).map (·.rows)

theorem TabRowsSame.refl (S : Statement) : TabRowsSame S S := ⟨SameTables.refl S, fun _ => rfl⟩

theorem TabRowsSame.trans {A B C : Statement} (h : TabRowsSame A B) (k : TabRowsSame B C) :
    TabRowsSame A C :=
  ⟨h.1.trans k.1, fun g => (k.2 g).trans (h.2 g)⟩

/-- Steps of which each keeps the relation, one behind the other, keep it. -/
theorem tabRowsSame_fold {α : Type} (step : Statement → α → Except String Statement)
    (hs : ∀ S p S', step S p = .ok S' → TabRowsSame S S') : ∀ (l : List α) (S S' : Statement),
    l.foldlM step S = .ok S' → TabRowsSame S S'
  | [], S, S', h => by
    cases h
    exact TabRowsSame.refl S
  | p :: l, S, S', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨S1, h1, h2⟩ := bindOk h
    exact (hs S p S1 h1).trans (tabRowsSame_fold step hs l S1 S' h2)

/-- What stands behind a first switch's front writes the statement by the own messages' joins alone:
so it leaves the tables and every group's rows. -/
theorem behindAsks_same {S S' : Statement} {x : _root_.Tw.K2.Front} {w : OnBytes.Switched}
    {plain : List E} {f : ReqFrame} {mine : Array Nat} {mask : Nat}
    (B : _root_.Tw.K2.BehindAsks S x w plain S' f mine mask) : TabRowsSame S S' :=
  tabRowsSame_fold _ (fun _ _ _ e => ⟨same_join e, join_rows e⟩) _ _ _ B.joins

/-- **THE HEAD's QUIET STEP LEAVES THE TABLES AND EVERY GROUP's ROWS.** -/
theorem headOpenQ_same {P : HeadPar} {s s' : S} (h : headOpenQ P s = .ok s') :
    SameTables s.st s'.st ∧
      ∀ g : Nat, (s'.st.groups[g]?).map (·.rows) = (s.st.groups[g]?).map (·.rows) := by
  obtain ⟨a, st, f, mine, L, out, y, cov, s₁, b, k⟩ := (headOpenQ_iff P s s').1 h
  obtain ⟨mask, B⟩ := (_root_.Tw.K2.firstBehind_iff _ _ _ _ _ _ _).1 k.behind
  have e : s'.st = st := by rw [k.out']
  rw [e]
  exact behindAsks_same B

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.TabRowsSame.refl
#print axioms VerifiableInference.Desc.First.K2.TabRowsSame.trans
#print axioms VerifiableInference.Desc.First.K2.tabRowsSame_fold
#print axioms VerifiableInference.Desc.First.K2.behindAsks_same
#print axioms VerifiableInference.Desc.First.K2.headOpenQ_same
