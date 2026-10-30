-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ground/Linked.lean: a property of a statement and a relation between statements, beside
"a statement only grows" and "no new mark" (Johnson/Desc/Grows.lean, Johnson/Desc/Marks.lean).
Theorems.

WHY. The chain's end reads a sampled message's LIST OF GROUPS; a proximity test takes in the sample
rows of its group's MEMBERS. "Grows" and "no new mark" do not tie the two. Nor do they forbid that a
member or an open row comes to a group whose test has begun; such a one is tested by nobody.

  Linked T         a message's list names only groups that hold the message as a member.
  KeepsLinked      the relation: if Linked holds in front it holds behind.
  Frozen T T'      a group that bears the mark in T stands in T' at that number, bears the mark, and
                   has the same members and the same open rows.
  linked_… , frozen_…   each plain change of a statement keeps them (a message's change that leaves
                   its list; a group's that loses no member, or that bears no mark; messages sent; a
                   new group; a joining, WHICH WRITES BOTH SIDES; ledgers closed).
That the ground's ten functions keep them: Johnson/Desc/Ground/LinkedKeeps.lean.
What is not claimed. Nothing on the beginning of a proximity test, which lays the mark and empties
the open rows of a group that did not bear it. That Linked holds of the statement at which a chain
starts: KeepsLinked is an implication and yields nothing without that. Frozen holds a marked group's
mark, members and open rows ALONE: its field "kept" is held by no relation here. THESE RELATIONS,
WITH "grows", "no new mark" AND "a sampled message's sample rows stay", DO NOT EXCLUDE A MESSAGE
THAT IS MADE A MEMBER BEFORE IT IS SAMPLED: its sample rows then enter no test. That members are
sampled is a further property, stated and kept elsewhere (SampledMembers,
Johnson/Desc/Means/Entry.lean).

-/
import Johnson.Desc.GroundKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
open OnBytes OnBytes.Slice

/-- A message's list of groups names only groups that hold the message as a member. -/
def Linked (T : Statement) : Prop :=
  ∀ (o : Nat) x (g : Nat), T.oracles[o]? = some x → g ∈ x.groups →
    ∃ G, T.groups[g]? = some G ∧ o ∈ G.members

/-- The relation of the invariant. -/
def KeepsLinked (T T' : Statement) : Prop := Linked T → Linked T'

/-- A group that bears the mark keeps its mark, its members and its open rows. -/
def Frozen (T T' : Statement) : Prop :=
  ∀ (i : Nat) G, T.groups[i]? = some G → G.inRun = true →
    ∃ G', T'.groups[i]? = some G' ∧ G'.inRun = true ∧ G'.members = G.members ∧ G'.rows = G.rows

theorem KeepsLinked.refl (T : Statement) : KeepsLinked T T := id

theorem KeepsLinked.trans {A B C : Statement} (h : KeepsLinked A B) (k : KeepsLinked B C) :
    KeepsLinked A C := fun a => k (h a)

theorem Frozen.refl (T : Statement) : Frozen T T := fun _ G h m => ⟨G, h, m, rfl, rfl⟩

theorem Frozen.trans {A B C : Statement} (h : Frozen A B) (k : Frozen B C) : Frozen A C := by
  intro i G hG m
  obtain ⟨G1, h1, m1, a1, b1⟩ := h i G hG m
  obtain ⟨G2, h2, m2, a2, b2⟩ := k i G1 h1 m1
  exact ⟨G2, h2, m2, a2.trans a1, b2.trans b1⟩

/-! ## Linked: the plain changes of a statement -/

/-- A change of one message that leaves its list of groups. -/
theorem linked_modOracle (T : Statement) (k : Nat) (f : OnBytes.Oracle → OnBytes.Oracle)
    (hf : ∀ x, (f x).groups = x.groups) :
    KeepsLinked T { T with oracles := T.oracles.modify k f } := by
  intro h o x g hx hg
  have hx' : (T.oracles.modify k f)[o]? = some x := hx
  rw [Array.getElem?_modify] at hx'
  split at hx'
  · cases ho : T.oracles[o]? with
    | none => simp [ho] at hx'
    | some y =>
      simp only [ho, Option.map_some, Option.some.injEq] at hx'
      subst hx'
      exact h o y g ho ((hf y) ▸ hg)
  · exact h o x g hx' hg

/-- A change of one group that loses no member. -/
theorem linked_modGroup (T : Statement) (k : Nat) (f : Group → Group)
    (hf : ∀ G o, o ∈ G.members → o ∈ (f G).members) :
    KeepsLinked T { T with groups := T.groups.modify k f } := by
  intro h o x g hx hg
  obtain ⟨G, hG, hm⟩ := h o x g hx hg
  show ∃ G', (T.groups.modify k f)[g]? = some G' ∧ o ∈ G'.members
  rw [Array.getElem?_modify]
  split
  · exact ⟨f G, by simp [hG], hf G o hm⟩
  · exact ⟨G, hG, hm⟩

theorem linked_stSent (T : Statement) (sent : Array OracleNotice) :
    KeepsLinked T (stSent T sent) := by
  intro h o x g hx hg
  have hx' :
      (T.oracles ++ sent.map fun n => ({ shape := n.shape } : OnBytes.Oracle))[o]? = some x := hx
  rw [Array.getElem?_append] at hx'
  split at hx'
  · exact h o x g hx' hg
  · rw [Array.getElem?_map] at hx'
    cases hs : sent[o - T.oracles.size]? with
    | none => simp [hs] at hx'
    | some n =>
      simp only [hs, Option.map_some, Option.some.injEq] at hx'
      subst hx'
      cases hg

theorem linked_withGroup (T : Statement) (code maskCode : Nat) :
    KeepsLinked T (withGroup T code maskCode) := by
  intro h o x g hx hg
  obtain ⟨G, hG, hm⟩ := h o x g hx hg
  obtain ⟨hi, _⟩ := Array.getElem?_eq_some_iff.1 hG
  refine ⟨G, ?_, hm⟩
  show (T.groups.push _)[g]? = some G
  rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hi), hG]

theorem mem_insertSelf {α : Type} (xs : Array α) (i : Nat) (a : α) (h : i ≤ xs.size) :
    a ∈ xs.insertIdxIfInBounds i a := by
  unfold Array.insertIdxIfInBounds
  rw [dif_pos h]
  exact Array.mem_insertIdx.2 (Or.inl rfl)

/-- A message that joins the group G, which stands at g: BOTH SIDES ARE WRITTEN. -/
theorem linked_joined (T : Statement) (g o : Nat) (kept : Bool) (G : Group)
    (hG : T.groups[g]? = some G) : KeepsLinked T (withMessageInGroup T g o kept G) := by
  intro h o' x' g' hx hg
  let f : Group → Group := fun G' => { G' with
    members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
    kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size kept }
  have grp : ∀ (a b : Nat) (A : Group), T.groups[a]? = some A → b ∈ A.members →
      ∃ G', (T.groups.modify g f)[a]? = some G' ∧ b ∈ G'.members := by
    intro a b A hA hb
    rw [Array.getElem?_modify]
    split
    · exact ⟨f A, by simp [hA], mem_insertIfIn _ _ _ _ hb⟩
    · exact ⟨A, hA, hb⟩
  have hx' : (T.oracles.modify o fun x => { x with groups := x.groups ++ [g] })[o']? = some x' := hx
  show ∃ G', (T.groups.modify g f)[g']? = some G' ∧ o' ∈ G'.members
  rw [Array.getElem?_modify] at hx'
  split at hx'
  · rename_i ho
    subst ho
    cases hy : T.oracles[o]? with
    | none => simp [hy] at hx'
    | some y =>
      simp only [hy, Option.map_some, Option.some.injEq] at hx'
      subst hx'
      rcases List.mem_append.1 hg with hg | hg
      · obtain ⟨A, hA, hb⟩ := h o y g' hy hg
        exact grp g' o A hA hb
      · rcases List.mem_singleton.1 hg with rfl
        refine ⟨f G, by rw [Array.getElem?_modify]; simp [hG], ?_⟩
        exact mem_insertSelf _ _ _ (Array.size_filter_le)
  · obtain ⟨A, hA, hb⟩ := h o' x' g' hx' hg
    exact grp g' o' A hA hb

theorem linked_closeLedgers (l : List Nat) : ∀ T : Statement, KeepsLinked T (closeLedgers T l) := by
  induction l with
  | nil => exact KeepsLinked.refl
  | cons o l ih =>
    intro T
    exact (linked_modOracle T o
      (fun x => { x with ledger := x.ledger.map fun l => { l with closed := true } })
      fun _ => rfl).trans (ih _)

/-! ## Frozen: the plain changes of a statement -/

/-- A change of the oracle messages alone. -/
theorem frozen_oracles (T : Statement) (os : Array OnBytes.Oracle) :
    Frozen T { T with oracles := os } := fun _ G h m => ⟨G, h, m, rfl, rfl⟩

/-- A change of one group that does not bear the mark. -/
theorem frozen_modGroup (T : Statement) (k : Nat) (f : Group → Group)
    (hk : ∀ G, T.groups[k]? = some G → G.inRun = false) :
    Frozen T { T with groups := T.groups.modify k f } := by
  intro i G hG m
  show ∃ G', (T.groups.modify k f)[i]? = some G' ∧ _
  rw [Array.getElem?_modify]
  split
  · rename_i hi
    subst hi
    rw [hk G hG] at m
    cases m
  · exact ⟨G, hG, m, rfl, rfl⟩

theorem frozen_withGroup (T : Statement) (code maskCode : Nat) :
    Frozen T (withGroup T code maskCode) := by
  intro i G hG m
  obtain ⟨hi, _⟩ := Array.getElem?_eq_some_iff.1 hG
  refine ⟨G, ?_, m, rfl, rfl⟩
  show (T.groups.push _)[i]? = some G
  rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hi), hG]

theorem frozen_closeLedgers (l : List Nat) : ∀ T : Statement, Frozen T (closeLedgers T l) := by
  induction l with
  | nil => exact Frozen.refl
  | cons o l ih =>
    intro T
    exact (frozen_oracles T _).trans (ih _)

end VerifiableInference.Desc
