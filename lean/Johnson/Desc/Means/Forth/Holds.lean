--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Means/Forth/Holds.lean: all that a statement claims goes FORWARDS over five of the
plain functions that change a statement (Johnson/Desc/First/Base/Ground.lean): newGroupP, joinP,
takeMaskP, addRowP and addRowsP (with addRowsFrom), if what is newly claimed holds.

Holds (Johnson/Desc/Means/Holds.lean) says of a statement and words: every open row of every group
and every sample row of every oracle message holds of the words. The files beside it show how it
goes backwards along a chain, which is what soundness asks. An honest prover needs the converse: its
words meet all that is claimed in front of a step; the step claims something more, which its words
meet too; so they meet all that is claimed behind the step.

  elem_of_modify  what stands in an array behind a change of one entry; for oracle messages
                  getElem?_modify_some (Johnson/Desc/Means/Page.lean) says more: which case holds
  holds_forth     the general form, Holds.back (Johnson/Desc/Means/Holds.lean) turned round: the
                  earlier statement is in order and all that it claims holds; the later one is a
                  later statement; each row behind was there in front, or holds
  newGroupP_forth, joinP_forth, takeMaskP_forth   these three claim nothing new
  addRowP_forth, addRowsFrom_forth, addRowsP_forth   new open rows, which hold

That a statement stays in order over these functions is Johnson/Desc/Means/Page.lean's. The two as
one proposition, with one lemma for each function: Johnson/Desc/Means/Forth/AllMet.lean.

In each lemma the words m are the same in front and behind. A caller can hand one family of words
for a whole run from the first step on: a row in order has no coefficient at a message that is not
there yet (RowIn.off, Johnson/Desc/Means/Keeps.lean). A caller whose words grow with each message
goes from one family to the next by allMet_agree (Johnson/Desc/Means/Forth/AllMet.lean).

What is not claimed. That any of the functions returns a state. The eight other plain functions are
not here: recvP and admitP: Forth/Send.lean; takeMasksP (with takeMasksInto), closeLedgerP,
spendAsMaskP, adoptP, elsewhereP and beginRunP: Forth/More.lean. Nothing on a verifier's decision,
on soundness or on hiding.

-/
import Johnson.Desc.Means.ClaimsP

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means
open VerifiableInference.Desc.Ground Desc.Plain

variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K) {m : Words K} {Lc : Type}

/-- What stands at a place of an array of which one entry has been changed: what stood there, or its
image. The statement does not say at which place the second case holds. -/
theorem elem_of_modify {α : Type} {A : Array α} {g : Nat} {f : α → α} (g' : Nat) (y : α)
    (h : (A.modify g f)[g']? = some y) : ∃ x, A[g']? = some x ∧ (y = x ∨ y = f x) := by
  rw [Array.getElem?_modify] at h
  by_cases c : g = g'
  · rw [if_pos c] at h
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨x, hx, Or.inr rfl⟩
  · rw [if_neg c] at h
    exact ⟨y, h, Or.inl rfl⟩

/-- **Forwards along a chain.** The earlier statement S is in order, and all that it claims holds of
the words; S' is a later statement; each open row and each sample row of S' was there in S, at the
same group or message, or holds at S'. Then all that S' claims holds of the words. -/
theorem holds_forth {S S' : Statement} (hI : InOrder S) (hE : Extends S S')
    (hr : ∀ (g : Nat) (G' : Group), S'.groups[g]? = some G' → ∀ r ∈ G'.rows.toList,
      (∃ G, S.groups[g]? = some G ∧ r ∈ G.rows.toList) ∨ Says ρ S' r m)
    (hs : ∀ (o : Nat) (x' : Oracle), S'.oracles[o]? = some x' → ∀ r ∈ x'.sampleRows.toList,
      (∃ x, S.oracles[o]? = some x ∧ r ∈ x.sampleRows.toList) ∨ Says ρ S' r m)
    (h : Holds ρ S m) : Holds ρ S' m := by
  refine ⟨fun g G' hG' r hr' => ?_, fun o x' hx' r hr' => ?_⟩
  · rcases hr g G' hG' r hr' with ⟨G, hG, hm⟩ | hsay
    · exact (says_extends ρ hE (hI.rows g G hG r hm) m).2 (h.rows g G hG r hm)
    · exact hsay
  · rcases hs o x' hx' r hr' with ⟨x, hx, hm⟩ | hsay
    · exact (says_extends ρ hE (hI.samples o x hx r hm) m).2 (h.samples o x hx r hm)
    · exact hsay

/-- If newGroupP returns a state, the statement in front is in order and all that it claims holds,
all that the statement behind claims holds: a new group has no row. -/
theorem newGroupP_forth {d d' : DState Lc} {a b g : Nat} (h : newGroupP d a b = some (g, d'))
    (hI : InOrder d.st) (hH : Holds ρ d.st m) : Holds ρ d'.st m := by
  unfold newGroupP at h
  split at h
  · obtain rfl : _ = d' := congrArg Prod.snd (Option.some.inj h)
    refine holds_forth ρ hI (extends_withGroup d.st a b) (fun g' G' hG' r hr => ?_)
      (fun o x hx r hr => Or.inl ⟨x, hx, hr⟩) hH
    have hG'' : (d.st.groups.push { code := a, maskCode := b })[g']? = some G' := hG'
    rw [Array.getElem?_push] at hG''
    by_cases c : g' = d.st.groups.size
    · rw [if_pos c] at hG''
      obtain rfl := Option.some.inj hG''
      simp at hr
    · rw [if_neg c] at hG''
      exact Or.inl ⟨G', hG'', hr⟩
  · cases h

/-- The like for joinP: a joining makes and loses no row. -/
theorem joinP_forth {d d' : DState Lc} {g o : Nat} {kept : Bool} (h : joinP d g o kept = some d')
    (hI : InOrder d.st) (hH : Holds ρ d.st m) : Holds ρ d'.st m := by
  unfold joinP at h
  split at h
  · obtain ⟨G, _, rfl⟩ := Option.map_eq_some_iff.1 h
    refine holds_forth ρ hI (extends_withMessageInGroup d.st g o kept G) (fun g' G' hG' r hr => ?_)
      (fun o' x' hx' r hr => ?_) hH
    · have hG'' : (d.st.groups.modify g fun G' => { G' with
          members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
          kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size kept })[g']? =
          some G' := hG'
      obtain ⟨G0, hG0, c⟩ := elem_of_modify g' G' hG''
      rcases c with rfl | rfl
      · exact Or.inl ⟨_, hG0, hr⟩
      · exact Or.inl ⟨G0, hG0, hr⟩
    · have hx'' : (d.st.oracles.modify o fun x => { x with groups := x.groups ++ [g] })[o']? =
          some x' := hx'
      obtain ⟨x0, hx0, c⟩ := elem_of_modify o' x' hx''
      rcases c with rfl | rfl
      · exact Or.inl ⟨_, hx0, hr⟩
      · exact Or.inl ⟨x0, hx0, hr⟩
  · cases h

/-- The like for takeMaskP: it turns a ledger alone. -/
theorem takeMaskP_forth {d d' : DState Lc} {o n : Nat} (h : takeMaskP d o = some (n, d'))
    (hI : InOrder d.st) (hH : Holds ρ d.st m) : Holds ρ d'.st m := by
  unfold takeMaskP at h
  split at h
  · obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    refine holds_forth ρ hI
      (Extends.of_shapes rfl fun o' => map_modify _ _ _ _ _ fun _ => rfl)
      (fun g G hG r hr => Or.inl ⟨G, hG, hr⟩) (fun o' x' hx' r hr => ?_) hH
    obtain ⟨x0, hx0, c⟩ := elem_of_modify o' x' hx'
    rcases c with rfl | rfl
    · exact Or.inl ⟨_, hx0, hr⟩
    · exact Or.inl ⟨x0, hx0, hr⟩
  · cases h

/-- **If addRowP returns a state, the statement in front is in order, all that it claims holds, and
the new open row holds AT THE STATEMENT IN FRONT, all that the statement behind claims holds.** At
the one group this is the right-to-left half of addRow_means (Johnson/Desc/Means/Keeps.lean). -/
theorem addRowP_forth {d d' : DState Lc} {g : Nat} {row : Row} (h : addRowP d g row = some d')
    (hI : InOrder d.st) (hH : Holds ρ d.st m) (hs : Says ρ d.st row m) : Holds ρ d'.st m := by
  obtain ⟨_, G, _, hin, e⟩ := addRowP_keeps h hI
  rw [e]
  have hE := extends_withRow d.st g row
  refine holds_forth ρ hI hE (fun g' G' hG' r hr => ?_) (fun o x hx r hr => Or.inl ⟨x, hx, hr⟩) hH
  have hG'' : (d.st.groups.modify g fun G => { G with rows := G.rows.push row })[g']? = some G' :=
    hG'
  obtain ⟨G0, hG0, c⟩ := elem_of_modify g' G' hG''
  rcases c with rfl | rfl
  · exact Or.inl ⟨_, hG0, hr⟩
  · have hr' : r ∈ (G0.rows.push row).toList := hr
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hr'
    rcases hr' with c | rfl
    · exact Or.inl ⟨G0, hG0, c⟩
    · exact Or.inr ((says_extends ρ hE hin m).2 hs)

/-- The like for a list of rows, added one by one: each holds AT THE STATEMENT IN FRONT OF THE FIRST
ADDING, so a caller shows all its rows once. -/
theorem addRowsFrom_forth (g : Nat) : ∀ (l : List Row) (d d' : DState Lc),
    addRowsFrom g l d = some d' → InOrder d.st → Holds ρ d.st m → (∀ r ∈ l, Says ρ d.st r m) →
    Holds ρ d'.st m
  | [], d, d', h, _, hH, _ => by
    obtain rfl := Option.some.inj h
    exact hH
  | row :: l, d, d', h, hI, hH, hs => by
    unfold addRowsFrom at h
    obtain ⟨d1, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨hI1, _, _, _, e⟩ := addRowP_keeps h1 hI
    refine addRowsFrom_forth g l d1 d' h2 hI1
      (addRowP_forth ρ h1 hI hH (hs row List.mem_cons_self)) fun r hr => ?_
    have hv : value ρ d1.st r m = value ρ d.st r m := by
      rw [e]
      exact value_congr ρ rfl rfl r m
    show value ρ d1.st r m = ρ.val r.target
    rw [hv]
    exact hs r (List.mem_cons_of_mem _ hr)

@[inherit_doc addRowsFrom_forth]
theorem addRowsP_forth {d d' : DState Lc} {g : Nat} {rows : List Row}
    (h : addRowsP d g rows = some d') (hI : InOrder d.st) (hH : Holds ρ d.st m)
    (hs : ∀ r ∈ rows, Says ρ d.st r m) : Holds ρ d'.st m := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_forth ρ g rows d d' h hI hH hs
  · cases h

end OnBytes.Means

#print axioms OnBytes.Means.elem_of_modify
#print axioms OnBytes.Means.holds_forth
#print axioms OnBytes.Means.newGroupP_forth
#print axioms OnBytes.Means.joinP_forth
#print axioms OnBytes.Means.takeMaskP_forth
#print axioms OnBytes.Means.addRowP_forth
#print axioms OnBytes.Means.addRowsFrom_forth
#print axioms OnBytes.Means.addRowsP_forth
