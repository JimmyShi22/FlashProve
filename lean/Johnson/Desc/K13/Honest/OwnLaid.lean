--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/OwnLaid.lean: what kind K13's text behind W's commitment does to the
statement's groups and to the messages' lists of groups, wherever it returns a state. Definitions,
and statements with their proofs.

The first chain's last sub-protocol (Johnson/Desc/K13/FirstEnd.lean) asks of the statement which
groups there are, on which a proximity test has begun, and in which groups each message is. The text
behind W's commitment (`rows`, Johnson/Desc/K13/Text.lean) makes one group, the last, lets messages
join it and adds a row to it. This file says just that of the statement behind, from the text's
return alone.
Main names:
  `OwnLaid S₀ S g M`: S comes from S₀ so: g is the number of S₀'s groups, and S has one group more;
    the elder groups are as they were; the members of g are the numbers with M; there are as many
    messages; a message with M has its mark `sampled` as before and g at the end of its list of
    groups; every other message is as it was.
  `OwnLaid.start`, `OwnLaid.step`, `OwnLaid.row`: behind the making of the group, behind one
    joining, behind the adding of a row.
  `joinP_inv`, `newGroupP_inv`: what a joining, and a making of a group, have done where they
    return.
  `ownMember Sh claim l o`: o is W, a message of the claim's masks, or, where the shape asks for a
    split, the split's message.
  `joinAll_ownLaid`, `rows_ownLaid`: **wherever the text returns**, `OwnLaid` holds of the
    statements in front and behind, at the own group's number, with just these members.
`Built` (Johnson/Desc/K13/Honest/OwnGroup.lean) says the like forward, from conditions under which
the text returns; here the return is the premise.

What is not claimed. That the text returns (Johnson/Desc/K13/Honest/RowsAccept.lean). Nothing on the
rows of a group, on codes or on tables. "Accepts" is `Block.decide`'s answer `.ok` and no more; of a
plain function it is said that it returns. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Law.M4
import Johnson.Desc.K13.Law.TextIs
import OnBytes.Slice.BlkStLaws
import Johnson.Desc.Means.Page

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Slice
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.K13.Law

/-- **How the statement behind the text comes from the statement in front.** g: the own group's
number. M: which numbers are its members. -/
structure OwnLaid (S₀ S : Statement) (g : ℕ) (M : ℕ → Prop) : Prop where
  num : g = S₀.groups.size
  size : S.groups.size = g + 1
  elder : ∀ g' < g, S.groups[g']? = S₀.groups[g']?
  own : ∃ G : Group, S.groups[g]? = some G ∧ ∀ o, o ∈ G.members.toList ↔ M o
  count : S.oracles.size = S₀.oracles.size
  inn : ∀ (o : ℕ) (x : OnBytes.Oracle), S₀.oracles[o]? = some x → M o →
    ∃ x' : OnBytes.Oracle, S.oracles[o]? = some x' ∧ x'.sampled = x.sampled ∧
      x'.groups = x.groups ++ [g]
  out : ∀ o, ¬ M o → S.oracles[o]? = S₀.oracles[o]?

/-- Behind the making of the group: no member. -/
theorem OwnLaid.start (S : Statement) (c z : ℕ) :
    OwnLaid S (Ground.withGroup S c z) S.groups.size fun _ => False :=
  ⟨rfl, by simp [Ground.withGroup],
    fun g' h => by simp [Ground.withGroup, Array.getElem?_push, Nat.ne_of_lt h],
    ⟨{ code := c, maskCode := z }, by simp [Ground.withGroup], fun o => by simp⟩, rfl,
    fun _ _ _ h => h.elim, fun _ _ => rfl⟩

/-- Behind one joining of a message that is no member. -/
theorem OwnLaid.step {S₀ S : Statement} {g : ℕ} {M : ℕ → Prop} (h : OwnLaid S₀ S g M) {G : Group}
    (hG : S.groups[g]? = some G) {o : ℕ} (k : Bool) (hn : ¬ M o) :
    OwnLaid S₀ (withMessageInGroup S g o k G) g fun o' => o' = o ∨ M o' := by
  obtain ⟨G', hG', hm⟩ := h.own
  rw [hG] at hG'
  obtain rfl := Option.some.inj hG'
  have hpos : (G.members.filter (· < o)).size ≤ G.members.toList.length := by
    rw [Array.length_toList]
    exact Array.size_filter_le
  refine ⟨h.num, by simpa [withMessageInGroup] using h.size, fun g' hg' => ?_, ?_,
    by simpa [withMessageInGroup] using h.count, fun o' x hx hM => ?_, fun o' hM => ?_⟩
  · rw [← h.elder g' hg']
    simp [withMessageInGroup, Array.getElem?_modify, Nat.ne_of_gt hg']
  · refine ⟨_, joined_group _ _ _ _ _ hG, fun o' => ?_⟩
    show o' ∈ (G.members.insertIdxIfInBounds (G.members.filter (· < o)).size o).toList ↔ _
    rw [OnBytes.Means.toList_insertIdxIfInBounds, List.mem_insertIdx hpos, hm o']
  · by_cases e : o' = o
    · subst e
      have hx' : S.oracles[o']? = some x := (h.out o' hn).trans hx
      exact ⟨_, joined_same _ _ _ _ _ _ hx', rfl, rfl⟩
    · obtain ⟨x', h1, h2, h3⟩ := h.inn o' x hx (hM.resolve_left e)
      exact ⟨x', (joined_other _ _ _ _ _ _ (Ne.symm e)).trans h1, h2, h3⟩
  · have e : o ≠ o' := fun e => hM (Or.inl e.symm)
    exact (joined_other _ _ _ _ _ _ e).trans (h.out o' fun m => hM (Or.inr m))

/-- Behind the adding of a row to the group. -/
theorem OwnLaid.row {S₀ S : Statement} {g : ℕ} {M : ℕ → Prop} (h : OwnLaid S₀ S g M)
    (r : OnBytes.Row) : OwnLaid S₀ (withRow S g r) g M := by
  obtain ⟨G, hG, hm⟩ := h.own
  refine ⟨h.num, by simpa [withRow] using h.size, fun g' hg' => ?_,
    ⟨_, withRow_group _ _ _ _ hG, hm⟩, h.count, h.inn, h.out⟩
  rw [← h.elder g' hg']
  simp [withRow, Array.getElem?_modify, Nat.ne_of_gt hg']

/-- The members may be said in other words. -/
theorem OwnLaid.iff {S₀ S : Statement} {g : ℕ} {M M' : ℕ → Prop} (h : OwnLaid S₀ S g M)
    (e : ∀ o, M o ↔ M' o) : OwnLaid S₀ S g M' := by
  obtain ⟨G, hG, hm⟩ := h.own
  exact ⟨h.num, h.size, h.elder, ⟨G, hG, fun o => (hm o).trans (e o)⟩, h.count,
    fun o x hx hM => h.inn o x hx ((e o).2 hM), fun o hM => h.out o fun m => hM ((e o).1 m)⟩

/-- What a joining has done where it returns. -/
theorem joinP_inv {d d' : St} {g o : ℕ} {k : Bool} (h : Ground.joinP d g o k = some d') :
    ∃ G : Group, d.st.groups[g]? = some G ∧ G.members.contains o = false ∧
      d'.st = withMessageInGroup d.st g o k G := by
  unfold Ground.joinP at h
  split at h
  · rename_i hok
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
    simp only [Ground.ok, Ground.joinL, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true] at hok
    rw [hG] at hok
    obtain ⟨_, _, _, _, _, _, h7, _⟩ := hok
    have h7' : (!G.members.contains o) = true := h7
    exact ⟨G, hG, by simpa using h7', rfl⟩
  · cases h

/-- What a making of a group has done where it returns. -/
theorem newGroupP_inv {d : St} {c z : ℕ} {b : ℕ × St} (h : Ground.newGroupP d c z = some b) :
    b.1 = d.st.groups.size ∧ b.2.st = Ground.withGroup d.st c z := by
  unfold Ground.newGroupP at h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl⟩
  · cases h

/-- One joining that returns. -/
theorem join_ownLaid {S₀ : Statement} {g o : ℕ} {k : Bool} {M : ℕ → Prop} {d d' : St}
    (h : OwnLaid S₀ d.st g M) (hj : Ground.joinP d g o k = some d') :
    OwnLaid S₀ d'.st g fun o' => o' = o ∨ M o' := by
  obtain ⟨G, hG, hc, e⟩ := joinP_inv hj
  obtain ⟨G', hG', hm⟩ := h.own
  rw [hG] at hG'
  obtain rfl := Option.some.inj hG'
  rw [e]
  refine h.step hG k fun hM => ?_
  have : G.members.contains o = true := by simpa using (hm o).2 hM
  rw [hc] at this
  cases this

/-- Joinings in a row that return. -/
theorem joinAll_ownLaid {S₀ : Statement} {g : ℕ} : ∀ (l : List ℕ) (M : ℕ → Prop) (d d' : St),
    OwnLaid S₀ d.st g M → K13.joinAll g l d = .ok d' →
    OwnLaid S₀ d'.st g fun o' => o' ∈ l ∨ M o'
  | [], _, d, d', h, hj => by
    obtain rfl : d = d' := Except.ok.inj hj
    exact h.iff fun _ => ⟨Or.inr, fun x => x.elim (fun y => absurd y List.not_mem_nil) id⟩
  | o :: l, M, d, d', h, hj => by
    simp only [K13.joinAll, Law.bind_ok, Law.there_ok] at hj
    obtain ⟨d₁, h1, h2⟩ := hj
    refine (joinAll_ownLaid l _ d₁ d' (join_ownLaid h h1) h2).iff fun o' => ?_
    show (o' ∈ l ∨ (o' = o ∨ M o')) ↔ (o' ∈ o :: l ∨ M o')
    rw [List.mem_cons]
    tauto

/-- The members of the own group, by the text: W, the messages of the claim's masks, and, where the
shape asks for a split, the split's message. -/
def ownMember (Sh : LinShape) (claim : LinClaim) (l : LinFirst) (o : ℕ) : Prop :=
  o = l.w ∨ o ∈ claim.masks.toList.map (·.oracle) ∨ (Sh.ownSplitNeeded = true ∧ o = l.split)

/-- **Wherever the text behind W's commitment returns.** -/
theorem rows_ownLaid {Sh : LinShape} {claim : LinClaim} {ids : Array ℕ} {d : St}
    {o : LinFirst × St} (h : rows Sh claim ids d = .ok o) :
    OwnLaid d.st o.2.st o.1.own (ownMember Sh claim o.1) := by
  simp only [rows_is, Law.bind_ok, Law.there_ok, Law.pure_ok] at h
  obtain ⟨w, _, b, hb, d₁, h1, d₂, h2, split, _, d₃, h3, mask, _, row, _, d₄, h4, rfl⟩ := h
  obtain ⟨e1, e2⟩ := newGroupP_inv hb
  have B0 : OwnLaid d.st b.2.st b.1 fun _ => False := by
    rw [e1, e2]
    exact OwnLaid.start d.st _ _
  have B1 := joinAll_ownLaid _ _ _ _ B0 h1
  have B2 := join_ownLaid B1 h2
  obtain ⟨_, _, _, e4⟩ := addRows_one h4
  have hmem : ∀ o', o' ∈ listOfT (claim.masks.toList.map (·.oracle)) ↔
      o' ∈ claim.masks.toList.map (·.oracle) := by
    intro o'
    rw [listOfT_eq, Fmt.listOf_mem _ o']
  show OwnLaid d.st d₄.st b.1 _
  rw [e4]
  by_cases hs : Sh.ownSplitNeeded = true
  · rw [if_pos hs] at h3
    refine ((join_ownLaid B2 h3).row row).iff fun o' => ?_
    show (o' = split ∨ (o' = w ∨ (o' ∈ listOfT (claim.masks.toList.map (·.oracle)) ∨ False))) ↔
      (o' = w ∨ o' ∈ claim.masks.toList.map (·.oracle) ∨ (Sh.ownSplitNeeded = true ∧ o' = split))
    rw [hmem o']
    constructor
    · rintro (a | a | a | a)
      · exact Or.inr (Or.inr ⟨hs, a⟩)
      · exact Or.inl a
      · exact Or.inr (Or.inl a)
      · exact a.elim
    · rintro (a | a | ⟨_, a⟩)
      · exact Or.inr (Or.inl a)
      · exact Or.inr (Or.inr (Or.inl a))
      · exact Or.inl a
  · rw [if_neg hs] at h3
    obtain rfl := Option.some.inj h3
    refine (B2.row row).iff fun o' => ?_
    show (o' = w ∨ (o' ∈ listOfT (claim.masks.toList.map (·.oracle)) ∨ False)) ↔
      (o' = w ∨ o' ∈ claim.masks.toList.map (·.oracle) ∨ (Sh.ownSplitNeeded = true ∧ o' = split))
    rw [hmem o']
    constructor
    · rintro (a | a | a)
      · exact Or.inl a
      · exact Or.inr (Or.inl a)
      · exact a.elim
    · rintro (a | a | ⟨a, _⟩)
      · exact Or.inl a
      · exact Or.inr (Or.inl a)
      · exact absurd a hs

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.OwnLaid.start
#print axioms VerifiableInference.Desc.K13.Honest.OwnLaid.step
#print axioms VerifiableInference.Desc.K13.Honest.OwnLaid.row
#print axioms VerifiableInference.Desc.K13.Honest.OwnLaid.iff
#print axioms VerifiableInference.Desc.K13.Honest.joinP_inv
#print axioms VerifiableInference.Desc.K13.Honest.newGroupP_inv
#print axioms VerifiableInference.Desc.K13.Honest.join_ownLaid
#print axioms VerifiableInference.Desc.K13.Honest.joinAll_ownLaid
#print axioms VerifiableInference.Desc.K13.Honest.rows_ownLaid
