-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/GroupsStay.lean: code switching (the kind K2): WHAT EACH CALL OF THE
SWITCH's TEXT DOES TO THE STATEMENT's GROUPS, as far as their number and each group's members and
flags «kept» go. NO BLOCK IMPORTS THIS FILE. Why. A sentence on the verifier's state along the
whole chain («the open group's members, in order, are the frame's lists») wants of every
sub-protocol that writes the statement: which group it pushes, which members it joins, and that
every other group stays. THE RELATION GS (as many groups; at every number the same members and the
same flags) IS NOT TYPED HERE: it is called from the light file
Johnson/Desc/First/Link/Law/GsDef.lean, which is kept light so that other files can call it
(GS · GS.refl · GS.trans · gs_push: called).
  GainsAt g l S S'   GS but at the group number g, whose members and flags gain the list l AT THE
                     END
  gs_of_groups · GainsAt.nil · GainsAt.trans · GainsAt.left | right   the rules
  push_at_end        inserting at the place «how many members are smaller» is pushing, where all
                     are smaller
  join_gains         one join of a message whose number is above all members': the group gains it
                     at the end
  joins_gains        a row of joins by rising numbers: the group gains them in that order
  ledger_gs · rows_gs   closing a ledger and adding open rows leave GS
No soundness is claimed.
-/
import Johnson.Top.H0.K2Hears.RowsKept
import Johnson.Desc.First.Link.Law.GsDef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (closeLedgerG joinG addRowsG dOf)
open VerifiableInference.Desc.Ground (joinP addRowsP)
open VerifiableInference.Desc.LinkJoin

/-- GS but at the group number g, which gains the list l at the end. -/
def GainsAt (g : Nat) (l : List (Nat × Bool)) (S S' : Statement) : Prop :=
  S'.groups.size = S.groups.size ∧
    (∀ i : Nat, i ≠ g → (S'.groups[i]?).map (fun G => (G.members, G.kept)) =
      (S.groups[i]?).map (fun G => (G.members, G.kept))) ∧
    ∃ G G', S.groups[g]? = some G ∧ S'.groups[g]? = some G' ∧
      G'.members = G.members ++ (l.map (·.1)).toArray ∧ G'.kept = G.kept ++ (l.map (·.2)).toArray

theorem gs_of_groups {S S' : Statement} (h : S'.groups = S.groups) : GS S S' := by
  unfold GS
  rw [h]
  exact ⟨rfl, fun _ => rfl⟩

theorem GainsAt.nil {S S' : Statement} (h : GS S S') {g : Nat} {G : Group}
    (hG : S.groups[g]? = some G) : GainsAt g [] S S' := by
  have e := h.2 g
  rw [hG] at e
  obtain ⟨G', hG', e'⟩ := Option.map_eq_some_iff.1 e
  refine ⟨h.1, fun i _ => h.2 i, G, G', hG, hG', ?_, ?_⟩
  · simpa using congrArg Prod.fst e'
  · simpa using congrArg Prod.snd e'

theorem GainsAt.trans {g : Nat} {l₁ l₂ : List (Nat × Bool)} {S S₁ S₂ : Statement}
    (a : GainsAt g l₁ S S₁) (b : GainsAt g l₂ S₁ S₂) : GainsAt g (l₁ ++ l₂) S S₂ := by
  obtain ⟨a1, a2, G, G₁, hG, hG₁, am, ak⟩ := a
  obtain ⟨b1, b2, G₁', G₂, hG₁', hG₂, bm, bk⟩ := b
  obtain rfl : G₁ = G₁' := Option.some.inj (hG₁.symm.trans hG₁')
  refine ⟨b1.trans a1, fun i hi => (b2 i hi).trans (a2 i hi), G, G₂, hG, hG₂, ?_, ?_⟩
  · rw [bm, am]
    simp
  · rw [bk, ak]
    simp

theorem GainsAt.left {g : Nat} {l : List (Nat × Bool)} {S S₁ S₂ : Statement} (a : GS S S₁)
    (b : GainsAt g l S₁ S₂) : GainsAt g l S S₂ := by
  obtain ⟨G₁, _, hG₁, _⟩ := b.2.2
  have e := a.2 g
  rw [hG₁] at e
  obtain ⟨G, hG, _⟩ := Option.map_eq_some_iff.1 e.symm
  exact (GainsAt.nil a hG).trans b

theorem GainsAt.right {g : Nat} {l : List (Nat × Bool)} {S S₁ S₂ : Statement}
    (a : GainsAt g l S S₁) (b : GS S₁ S₂) : GainsAt g l S S₂ := by
  obtain ⟨_, G₁, _, hG₁, _⟩ := a.2.2
  have := a.trans (GainsAt.nil b hG₁)
  rwa [List.append_nil] at this

theorem push_at_end {α : Type} (xs : Array α) (a : α) :
    xs.insertIdxIfInBounds xs.size a = xs ++ #[a] := by
  apply Array.toList_inj.1
  simp [Array.insertIdxIfInBounds]

theorem join_gains {S S' : Statement} {g o : Nat} {kept : Bool} (h : joinG S g o kept = .ok S')
    {G : Group} (hG : S.groups[g]? = some G) (hk : G.kept.size = G.members.size)
    (hlt : ∀ m ∈ G.members, m < o) : GainsAt g [(o, kept)] S S' := by
  unfold joinG at h
  split at h
  · rename_i d hd
    cases h
    unfold joinP at hd
    split at hd
    · obtain ⟨G₀, hG₀, rfl⟩ := Option.map_eq_some_iff.1 hd
      obtain rfl : G₀ = G := Option.some.inj (hG₀.symm.trans hG)
      have hf : (G₀.members.filter (· < o)).size = G₀.members.size := by
        rw [Array.filter_eq_self.2 fun m hm => by simpa using hlt m hm]
      refine ⟨?_, fun i hi => ?_, G₀,
        { G₀ with
          members := G₀.members.insertIdxIfInBounds (G₀.members.filter (· < o)).size o
          kept := G₀.kept.insertIdxIfInBounds (G₀.members.filter (· < o)).size kept },
        hG, ?_, ?_, ?_⟩
      · show (OnBytes.Slice.withMessageInGroup S g o kept G₀).groups.size = _
        unfold OnBytes.Slice.withMessageInGroup
        exact Array.size_modify ..
      · show ((OnBytes.Slice.withMessageInGroup S g o kept G₀).groups[i]?).map _ = _
        unfold OnBytes.Slice.withMessageInGroup
        simp only [Array.getElem?_modify]
        rw [if_neg fun e => hi e.symm]
      · show (OnBytes.Slice.withMessageInGroup S g o kept G₀).groups[g]? = _
        unfold OnBytes.Slice.withMessageInGroup
        simp only [Array.getElem?_modify, if_true]
        rw [hG]
        rfl
      · show G₀.members.insertIdxIfInBounds _ o = _
        rw [hf]
        exact push_at_end _ _
      · show G₀.kept.insertIdxIfInBounds _ kept = _
        rw [hf, ← hk]
        exact push_at_end _ _
    · cases hd
  · cases h

theorem joins_gains {α : Type} (g : Nat) (f : α → Nat) (k : α → Bool) : ∀ (l : List α)
    (S S' : Statement), l.foldlM (fun S p => joinG S g (f p) (k p)) S = .ok S' →
    l.Pairwise (fun a b => f a < f b) → ∀ G : Group, S.groups[g]? = some G →
    G.kept.size = G.members.size → (∀ m ∈ G.members, ∀ p ∈ l, m < f p) →
    GainsAt g (l.map fun p => (f p, k p)) S S'
  | [], S, S', h, _, G, hG, _, _ => by
    cases h
    exact GainsAt.nil (GS.refl S) hG
  | p :: l, S, S', h, hp, G, hG, hk, hlt => by
    rw [List.foldlM_cons] at h
    obtain ⟨S1, h1, h2⟩ := bindOk h
    have a := join_gains h1 hG hk fun m hm => hlt m hm p (by simp)
    obtain ⟨G₀, G₁, hG₀, hG₁, em, ek⟩ := a.2.2
    obtain rfl : G₀ = G := Option.some.inj (hG₀.symm.trans hG)
    obtain ⟨hp1, hp2⟩ := List.pairwise_cons.1 hp
    have b := joins_gains g f k l S1 S' h2 hp2 G₁ hG₁ (by rw [em, ek]; simp [hk]) fun m hm q hq =>
        by
      rw [em] at hm
      rcases Array.mem_append.1 hm with hm | hm
      · exact hlt m hm q (by simp [hq])
      · have : m = f p := by simpa using hm
        rw [this]
        exact hp1 q hq
    exact a.trans b

theorem ledger_gs {S S' : Statement} {o : Nat} (h : closeLedgerG S o = .ok S') : GS S S' := by
  unfold closeLedgerG at h
  split at h
  · rename_i d hd
    cases h
    unfold VerifiableInference.Desc.Ground.closeLedgerP at hd
    split at hd
    · cases hd
      exact GS.refl _
    · cases hd
  · cases h

theorem withRows_gs (g : Nat) : ∀ (l : List OnBytes.Row) (S : Statement),
    GS S (OnBytes.Slice.withRows S g l)
  | [], S => GS.refl S
  | r :: l, S => by
    have a : GS S (OnBytes.Slice.withRow S g r) := gs_push S _ g r rfl
    exact a.trans (withRows_gs g l _)

theorem rows_gs {S S' : Statement} {g : Nat} {rows : List OnBytes.Row}
    (h : addRowsG S g rows = .ok S') : GS S S' := by
  unfold addRowsG at h
  split at h
  · rename_i d hd
    cases h
    unfold addRowsP at hd
    split at hd
    · rw [from_rows g rows _ d hd]
      exact withRows_gs g rows _
    · cases hd
  · cases h

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.join_gains
#print axioms VerifiableInference.Desc.First.K2.joins_gains
#print axioms VerifiableInference.Desc.First.K2.ledger_gs
#print axioms VerifiableInference.Desc.First.K2.rows_gs
