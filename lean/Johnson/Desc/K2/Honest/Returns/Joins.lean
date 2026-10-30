-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/Joins.lean: ORACLE MESSAGES JOIN A GROUP, ONE AFTER THE OTHER
(`joinG`, Johnson/Top/H0/Tw/K2/Switch.lean): THE LOOP RETURNS wherever premises on the make of the
statement in front hold; with what is behind. Statements and proofs.

  `joinG_returns`   one message joins: the eight clauses of the ground's test, as premises
  `group_joined`, `oracle_joined`, `mem_joined`   the group and a message behind a join; the members
  `Core`, `core`    what a join leaves of a message: shape, sampled, stored sample rows, pad
  `MayJoin`, `MayJoin.of_core`   the premises on one message; they hang on its core alone
  `joinedAll`       the statement behind the joins, as a term
  `joins_return`    the loop returns `joinedAll`; behind it: the group is there, its test has not
                    begun, its codes and open rows are as before, its members are those before and
                    the list's; the codes and every message's core are as before

Limits. Nothing on any property.

-/
import Johnson.Top.H0.Tw.K2.Switch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.Slice (withMessageInGroup)
open VerifiableInference.Desc.Ground (joinL joinP ok has)
open _root_.Tw.K2 (joinG dOf)

/-- **One message joins.** -/
theorem joinG_returns (S : Statement) (g o : Nat) (kept : Bool) (G : Group) (x : OnBytes.Oracle)
    (hG : S.groups[g]? = some G) (hx : S.oracles[o]? = some x) (hs : x.sampled = true)
    (hr : G.inRun = false) (hc : x.shape.mainRows = 0 ∨ x.shape.code = G.code)
    (hm : x.shape.maskRows = 0 ∨ x.shape.maskCode = G.maskCode)
    (hn : G.members.contains o = false) (hk : kept = true → 0 < x.shape.mainRows) :
    joinG S g o kept = .ok (withMessageInGroup S g o kept G) := by
  have c5 : (x.shape.mainRows == 0 || x.shape.code == G.code) = true := by
    rcases hc with h | h <;> simp [h]
  have c6 : (x.shape.maskRows == 0 || x.shape.maskCode == G.maskCode) = true := by
    rcases hm with h | h <;> simp [h]
  have c8 : (!kept || decide (0 < x.shape.mainRows)) = true := by
    cases kept
    · rfl
    · simp [hk rfl]
  have hok : ok (joinL (dOf S).st g o kept) = true := by
    show ok (joinL S g o kept) = true
    unfold ok joinL has
    simp only [hG, hx, List.all_cons, List.all_nil, Option.isSome_some, Option.map_some,
      Option.getD_some, hs, hr, c5, c6, hn, c8, Bool.not_false, Bool.and_self]
  unfold joinG joinP
  rw [if_pos hok]
  show (match ((S.groups[g]?).map fun G => { dOf S with st := withMessageInGroup S g o kept G }) with
    | some d => Except.ok d.st
    | none => _) = _
  rw [hG]
  rfl

/-- The group behind a join. -/
theorem group_joined (S : Statement) (g o : Nat) (kept : Bool) (G : Group) :
    (withMessageInGroup S g o kept G).groups[g]? = (S.groups[g]?).map fun G' => { G' with
                  members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
                  kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size kept } := by
  unfold withMessageInGroup
  simp [Array.getElem?_modify]

/-- What a join leaves of a message. -/
abbrev Core : Type := OracleShape × Bool × Array OnBytes.Row × List (Part × Nat)

def core (x : OnBytes.Oracle) : Core := (x.shape, x.sampled, x.sampleRows, x.pad)

/-- A message behind a join. -/
theorem oracle_joined (S : Statement) (g o : Nat) (kept : Bool) (G : Group) (o' : Nat) :
    ((withMessageInGroup S g o kept G).oracles[o']?).map core = (S.oracles[o']?).map core := by
  unfold withMessageInGroup
  simp only [Array.getElem?_modify]
  split
  · cases S.oracles[o']? <;> rfl
  · rfl

/-- The members behind a join. -/
theorem mem_joined (a : Array Nat) (o o' : Nat) :
    o' ∈ (a.insertIdxIfInBounds (a.filter (· < o)).size o).toList ↔ o' ∈ a.toList ∨ o' = o := by
  have hle : (a.filter (· < o)).size ≤ a.size := Array.size_filter_le
  unfold Array.insertIdxIfInBounds
  rw [dif_pos hle, Array.toList_insertIdx, List.mem_insertIdx (by simpa using hle)]
  exact Or.comm

/-- The premises on one message that is to join a group with these two codes. -/
def MayJoin (S : Statement) (code maskCode o : Nat) (kept : Bool) : Prop :=
  ∃ x, S.oracles[o]? = some x ∧ x.sampled = true ∧
    (x.shape.mainRows = 0 ∨ x.shape.code = code) ∧
    (x.shape.maskRows = 0 ∨ x.shape.maskCode = maskCode) ∧ (kept = true → 0 < x.shape.mainRows)

/-- They hang on the message's core alone. -/
theorem MayJoin.of_core {S S' : Statement} {code maskCode o : Nat} {kept : Bool}
    (h : MayJoin S code maskCode o kept)
    (e : (S'.oracles[o]?).map core = (S.oracles[o]?).map core) :
    MayJoin S' code maskCode o kept := by
  obtain ⟨x, hx, h1, h2, h3, h4⟩ := h
  rw [hx] at e
  obtain ⟨x', hx', ec⟩ := Option.map_eq_some_iff.1 e
  have es : x'.shape = x.shape := congrArg (·.1) ec
  have ea : x'.sampled = x.sampled := congrArg (·.2.1) ec
  exact ⟨x', hx', by rw [ea]; exact h1, by rw [es]; exact h2, by rw [es]; exact h3, by
    rw [es]; exact h4⟩

/-- **The statement behind the joins, as a term**: the messages of a list join the group one after
the other (`withMessageInGroup`, OnBytes/Slice/BlkCalls.lean). Where the group lacks: the statement as it is. -/
def joinedAll {α : Type} (grp : Nat) (no : α → Nat) (kp : α → Bool) :
    List α → Statement → Statement
  | [], S => S
  | p :: l, S =>
    match S.groups[grp]? with
    | some G => joinedAll grp no kp l (withMessageInGroup S grp (no p) (kp p) G)
    | none => S

/-- **The loop returns**, and what it returns is `joinedAll`. no, kp: a list entry's message and
whether it is kept. -/
theorem joins_return {α : Type} (grp : Nat) (no : α → Nat) (kp : α → Bool) :
    ∀ (l : List α) (S : Statement) (G : Group), S.groups[grp]? = some G → G.inRun = false →
    (∀ p ∈ l, MayJoin S G.code G.maskCode (no p) (kp p)) →
    (∀ p ∈ l, no p ∉ G.members.toList) → (l.map no).Nodup →
    ∃ S' G', S' = joinedAll grp no kp l S ∧
      l.foldlM (fun S p => joinG S grp (no p) (kp p)) S = .ok S' ∧
      S'.groups[grp]? = some G' ∧ G'.inRun = false ∧ G'.code = G.code ∧
      G'.maskCode = G.maskCode ∧ G'.rows = G.rows ∧
      (∀ o, o ∈ G'.members.toList ↔ o ∈ G.members.toList ∨ o ∈ l.map no) ∧
      S'.codes = S.codes ∧ ∀ o : Nat, (S'.oracles[o]?).map core = (S.oracles[o]?).map core
  | [], S, G, hG, hr, _, _, _ =>
    ⟨S, G, rfl, rfl, hG, hr, rfl, rfl, rfl, fun o => by simp, rfl, fun _ => rfl⟩
  | p :: l, S, G, hG, hr, hj, hn, hd => by
    obtain ⟨x, hx, h1, h2, h3, h4⟩ := hj p (List.mem_cons_self ..)
    have hc : G.members.contains (no p) = false := by
      have := hn p (List.mem_cons_self ..)
      simpa using this
    have j := joinG_returns S grp (no p) (kp p) G x hG hx h1 hr h2 h3 hc h4
    have hG1 := group_joined S grp (no p) (kp p) G
    rw [hG] at hG1
    rw [List.map_cons, List.nodup_cons] at hd
    obtain ⟨S', G', f0, f1, f2, f3, f4, f5, f9, f6, f7, f8⟩ := joins_return grp no kp l
      (withMessageInGroup S grp (no p) (kp p) G) _ hG1 hr
      (fun q hq => (hj q (List.mem_cons_of_mem _ hq)).of_core (oracle_joined S grp _ _ G _))
      (fun q hq hm => by
        rcases (mem_joined G.members (no p) (no q)).1 hm with h | h
        · exact hn q (List.mem_cons_of_mem _ hq) h
        · exact hd.1 (h ▸ List.mem_map.2 ⟨q, hq, rfl⟩))
      hd.2
    refine ⟨S', G', ?_, ?_, f2, f3, f4, f5, f9, fun o => ?_, f7, fun o => ?_⟩
    · rw [f0]
      show _ = (match S.groups[grp]? with
        | some G => joinedAll grp no kp l (withMessageInGroup S grp (no p) (kp p) G)
        | none => S)
      rw [hG]
    · rw [List.foldlM_cons, j]
      exact f1
    · rw [f6 o, mem_joined, List.map_cons, List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
    · rw [f8 o, oracle_joined]

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.joinG_returns
#print axioms VerifiableInference.Desc.K2.Honest.Returns.mem_joined
#print axioms VerifiableInference.Desc.K2.Honest.Returns.joins_return
