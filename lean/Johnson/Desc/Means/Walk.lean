-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/Walk.lean: the four invariants on a statement (Tidy); ten plain functions of the
ground, each of which keeps them and loses no claim; and walks, which carry tidiness along a chain
and no more.

A walk leads from a statement to a later one by steps of two sorts: a quiet step, which keeps the
four invariants and loses no claim (Claims behind gives Claims in front), and the beginning of a
proximity test. Ten plain functions of Johnson/Desc/First/Base/Ground.lean are quiet steps where
they return a state: newGroupP, recvP, adoptP, admitP (if the rows handed in are on the message),
joinP, addRowP, takeMaskP, closeLedgerP, spendAsMaskP and elsewhereP (if the other statement is in
order). beginRunP is the beginning of a test. The two functions that repeat a step, addRowsP and
takeMasksP, have no such lemma here. Walks can be joined, so a chain whose blocks change the
statement by these eleven functions alone is a walk.

LIMIT. As a proposition, Walk ρ S Z says no more than "if S is tidy then Z is tidy": the two are
equivalent (by reading, not by a theorem here). The type keeps neither the statements between S and
Z nor the tests that were begun: both fields of Quiet stand under "S is tidy", the statement behind
a quiet step may be any statement, and Walk.begun asks only that the group is there. So "no claim is
lost", which holds of each quiet step of a real chain, is forgotten when the steps are joined into a
walk. A walk is to be used for Walk.tidy alone. (Below, "a run" means a verifier's run over a proof,
not a proximity test, which the names runRows, beginRunP and inRun mean.)

This file also shows: on a walk from a tidy statement of which Claims is false to a statement of
which Claims is true, there is a beginning of a test in front of which Claims is false and behind
which it is true (Walk.locate), and there the batched row holds at few multipliers (Walk.catches).
IN BOTH, THE PREMISES ON THE WORDS ARE NOT NEEDED: over a ring in which 0 ≠ 1, what they conclude
follows from "Z is tidy" alone, for all words.
THAT IS NOT PROVED IN THIS FILE.
Walk.catches is stated over a domain, where 0 ≠ 1.
Walk.locate is stated over any commutative ring, and 0 ≠ 1 is all that hbad gives there: where 0 = 1
every claim holds. So, where 0 ≠ 1, the two theorems tell nothing beyond what Walk.tidy tells.
They locate nothing of a run: the statement, the group and the beginning that they return are tied
to S and Z by walks alone, that is by tidiness alone, and the count is on no multiplier that a
verifier drew. For a claim on one batching use claims_catches (Johnson/Desc/Means/Claims.lean) or
begin_catches (Johnson/Desc/Means/Holds.lean) at that batching's own statement and group.

Main definitions: Tidy, Quiet, Walk.
Main theorems: Walk.trans, Walk.tidy, Walk.locate, Walk.catches; quiet_newGroupP, quiet_recvP,
quiet_adoptP, quiet_admitP, quiet_joinP, quiet_addRowP, quiet_takeMaskP, quiet_closeLedgerP,
quiet_spendAsMaskP, quiet_elsewhereP, Walk.of_beginRunP.

What is not claimed. That a block of a chain gives a walk: that is each kind's to show of its own
text. That along a walk no claim is lost, or that a false claim is caught at a batching of the run:
see LIMIT. No chance is named: the count is for one batching, and a chain has several. Nothing on
soundness.

-/
import Johnson.Desc.Means.Entry
import Johnson.Desc.Means.Kinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)
open VerifiableInference.Desc.Ground Desc.Plain

/-- The four invariants on a statement that the laws on claims spend. -/
structure Tidy (S : Statement) : Prop where
  inOrder : InOrder S
  kinds : OpenKinds S
  noneYet : NoneYet S
  members : SampledMembers S

theorem Tidy.start (codes : Codes) : Tidy { codes := codes, oracles := #[], groups := #[] } :=
  ⟨InOrder.start codes, OpenKinds.start codes, NoneYet.start codes, SampledMembers.start codes⟩

theorem Tidy.begun {S : Statement} (h : Tidy S) (g : Nat) (G : Group)
    (hG : S.groups[g]? = some G) : Tidy (Slice.begun S g G) :=
  ⟨h.inOrder.begun g G hG, h.kinds.begun g G,
    (h.noneYet.closeLedgers G.members.toList).sameOracles rfl, h.members.begun g G⟩

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- A quiet step: from a tidy statement it leads to a tidy one and loses no claim. -/
structure Quiet (S S' : Statement) : Prop where
  tidy : Tidy S → Tidy S'
  back : Tidy S → ∀ m : Words K, Claims ρ S' m → Claims ρ S m

/-- A walk: quiet steps and beginnings of proximity tests. As a proposition it says no more than
"if S is tidy then Z is tidy" (by reading, not by a theorem here). -/
inductive Walk : Statement → Statement → Prop
  | nil (S : Statement) : Walk S S
  | quiet {S S' Z : Statement} : Quiet ρ S S' → Walk S' Z → Walk S Z
  | begun {S Z : Statement} (g : Nat) (G : Group) : S.groups[g]? = some G →
      Walk (Slice.begun S g G) Z → Walk S Z

variable {ρ}

theorem Walk.trans {A B C : Statement} (h : Walk ρ A B) (k : Walk ρ B C) : Walk ρ A C := by
  induction h with
  | nil _ => exact k
  | quiet q _ ih => exact Walk.quiet q (ih k)
  | begun g G hG _ ih => exact Walk.begun g G hG (ih k)

/-- A walk from a tidy statement ends at a tidy one. -/
theorem Walk.tidy {S Z : Statement} (h : Walk ρ S Z) (hT : Tidy S) : Tidy Z := by
  induction h with
  | nil _ => exact hT
  | quiet q _ ih => exact ih (q.tidy hT)
  | begun g G hG _ ih => exact ih (hT.begun g G hG)

/-- Some beginning of a test on some walk takes the false claim off the statement. The premises on
the words are not needed: over a ring in which 0 ≠ 1, which is all that hbad gives, the conclusion
follows from "Z is tidy" alone (not proved in this file): see LIMIT in this file's head. -/
theorem Walk.locate {S Z : Statement} (h : Walk ρ S Z) (hT : Tidy S) {m : Words K}
    (hbad : ¬ Claims ρ S m) (hend : Claims ρ Z m) :
    ∃ (J : Statement) (g : Nat) (G : Group), Walk ρ S J ∧ Tidy J ∧ J.groups[g]? = some G ∧
      Walk ρ (Slice.begun J g G) Z ∧ ¬ Claims ρ J m ∧ Claims ρ (Slice.begun J g G) m := by
  induction h with
  | nil _ => exact absurd hend hbad
  | @quiet S S' Z q _ ih =>
    obtain ⟨J, g, G, w1, t, hG, w2, b1, b2⟩ :=
      ih (q.tidy hT) (fun c => hbad (q.back hT m c)) hend
    exact ⟨J, g, G, Walk.quiet q w1, t, hG, w2, b1, b2⟩
  | @begun S Z g G hG w ih =>
    by_cases c : Claims ρ (Slice.begun S g G) m
    · exact ⟨S, g, G, Walk.nil S, hT, hG, w, hbad, c⟩
    · obtain ⟨J, g', G', w1, t, hG', w2, b1, b2⟩ := ih (hT.begun g G hG) c hend
      exact ⟨J, g', G', Walk.begun g G hG w1, t, hG', w2, b1, b2⟩

/-- At a beginning of a test on some walk the elements of K as which x reads, for some x at which
the batched row holds of tables that hold the words on the blocks, are fewer than the rows that the
test takes in. The premises on the words are not needed: the conclusion follows from "Z is tidy"
alone (not proved in this file): see LIMIT in this file's head. -/
theorem Walk.catches [IsDomain K] [Finite K] {S Z : Statement} (h : Walk ρ S Z) (hT : Tidy S)
    {m : Words K} (hbad : ¬ Claims ρ S m) (hend : Claims ρ Z m) :
    ∃ (J : Statement) (g : Nat) (G : Group), Walk ρ S J ∧ J.groups[g]? = some G ∧
      Walk ρ (Slice.begun J g G) Z ∧
      Nat.card {y : K // ∃ (x : E) (out : GroupRow) (T : Tables K), ρ.val x = y ∧
        Bat.combine (Slice.begun J g G) g ⟨layoutOf J G, Slice.runRows J G⟩ x = some out ∧
        LaidOn (Slice.begun J g G) (layoutOf J G) m T ∧
        GroupSays ρ (Slice.begun J g G) (layoutOf J G) out T} ≤ (Slice.runRows J G).size - 1 := by
  obtain ⟨J, g, G, w1, t, hG, w2, b1, b2⟩ := h.locate hT hbad hend
  rcases claims_catches ρ t.inOrder t.kinds g G hG b1 with c | c
  · exact absurd b2 c
  · exact ⟨J, g, G, w1, hG, w2, c⟩

/-! ## The plain functions are steps of a walk -/

variable (ρ) {Lc : Type}

theorem quiet_newGroupP {d d' : DState Lc} {a b g : Nat} (h : newGroupP d a b = some (g, d')) :
    Quiet ρ d.st d'.st :=
  ⟨fun t => ⟨newGroupP_keeps h t.inOrder, newGroupP_kinds h t.kinds, newGroupP_none h t.noneYet,
    newGroupP_members h t.members⟩, fun t _ c => newGroupP_claims ρ h t.inOrder c⟩

theorem quiet_recvP {d d' : DState Lc} {first : Nat} {sent : Array OracleNotice} {ids : Array Nat}
    (h : recvP first d sent = some (ids, d')) : Quiet ρ d.st d'.st :=
  ⟨fun t => ⟨recvP_keeps h t.inOrder, recvP_kinds h t.kinds, recvP_none h t.noneYet,
    recvP_members h t.members⟩, fun t _ c => recvP_claims ρ h t.inOrder c⟩

theorem quiet_adoptP {d d' : DState Lc} {sent : Array OracleNotice}
    {given : Array (Nat × Fmt.Src)} {ids : Array Nat}
    (h : adoptP d sent given = some (ids, d')) : Quiet ρ d.st d'.st :=
  ⟨fun t => ⟨adoptP_keeps h t.inOrder, adoptP_kinds h t.kinds, adoptP_none h t.noneYet,
    adoptP_members h t.members⟩, fun t _ c => adoptP_claims ρ h t.inOrder c⟩

/-- The admitting, if the rows handed in are on the message. -/
theorem quiet_admitP {d d' : DState Lc} {o : Nat} {rows : Array Row}
    (h : admitP d o rows = some d') (hr : ∀ r ∈ rows.toList, RowOn d.st o r) :
    Quiet ρ d.st d'.st :=
  ⟨fun t => ⟨admitP_keeps h t.inOrder hr, admitP_kinds h t.kinds, admitP_none h t.noneYet,
    admitP_members h t.members⟩, fun t _ c => admitP_claims ρ h t.inOrder t.noneYet c⟩

theorem quiet_joinP {d d' : DState Lc} {g o : Nat} {kept : Bool}
    (h : joinP d g o kept = some d') : Quiet ρ d.st d'.st :=
  ⟨fun t => ⟨joinP_keeps h t.inOrder, joinP_kinds h t.kinds, joinP_none h t.noneYet,
    joinP_members h t.members⟩, fun t _ c => joinP_claims ρ h t.inOrder c⟩

theorem quiet_addRowP {d d' : DState Lc} {g : Nat} {row : Row} (h : addRowP d g row = some d') :
    Quiet ρ d.st d'.st :=
  ⟨fun t => ⟨(addRowP_keeps h t.inOrder).1, addRowP_kinds h t.kinds, addRowP_none h t.noneYet,
    addRowP_members h t.members⟩, fun t _ c => (addRowP_claims ρ h t.inOrder c).1⟩

theorem quiet_takeMaskP {d d' : DState Lc} {o n : Nat} (h : takeMaskP d o = some (n, d')) :
    Quiet ρ d.st d'.st :=
  ⟨fun t => ⟨takeMaskP_keeps h t.inOrder, takeMaskP_kinds h t.kinds, takeMaskP_none h t.noneYet,
    takeMaskP_members h t.members⟩, fun t _ c => takeMaskP_claims ρ h t.inOrder c⟩

theorem quiet_closeLedgerP {d d' : DState Lc} {o : Nat} (h : closeLedgerP d o = some d') :
    Quiet ρ d.st d'.st :=
  ⟨fun t => ⟨closeLedgerP_keeps h t.inOrder, closeLedgerP_kinds h t.kinds,
    closeLedgerP_none h t.noneYet, closeLedgerP_members h t.members⟩,
    fun t _ c => closeLedgerP_claims ρ h t.inOrder c⟩

theorem quiet_spendAsMaskP {d d' : DState Lc} {o : Nat} (h : spendAsMaskP d o = some d') :
    Quiet ρ d.st d'.st :=
  ⟨fun t => ⟨spendAsMaskP_keeps h t.inOrder, spendAsMaskP_kinds h t.kinds,
    spendAsMaskP_none h t.noneYet, spendAsMaskP_members h t.members⟩,
    fun t _ c => spendAsMaskP_claims ρ h t.inOrder c⟩

/-- The copying from another statement, if that statement is in order. -/
theorem quiet_elsewhereP {d d' : DState Lc} {mine theirs : Nat} {other : Statement}
    (h : elsewhereP d mine other theirs = some d') (hO : InOrder other) : Quiet ρ d.st d'.st :=
  ⟨fun t => ⟨elsewhereP_keeps h t.inOrder hO, elsewhereP_kinds h t.kinds,
    elsewhereP_none h t.noneYet, elsewhereP_members h t.members⟩,
    fun t _ c => elsewhereP_claims ρ h t.inOrder t.noneYet c⟩

/-- A quiet step is a walk. -/
theorem Quiet.walk {S S' : Statement} (q : Quiet ρ S S') : Walk ρ S S' :=
  Walk.quiet q (Walk.nil S')

/-- The beginning of a test is a walk. -/
theorem Walk.of_beginRunP {d d' : DState Lc} {g : Nat} {input : RunInput}
    (h : beginRunP d g = some (input, d')) : Walk ρ d.st d'.st := by
  obtain ⟨G, hG, _, e⟩ := beginRunP_inv h
  rw [e]
  exact Walk.begun g G hG (Walk.nil _)

end OnBytes.Means
