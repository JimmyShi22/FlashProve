-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Laid/Joined.lean: the yes of the shared chain's "joins" gives `Joined`
(Johnson/Desc/Key/Laid/JoinedDef.lean). Theorems.

Main names.
  `joinP_eq`: the plain ground's joinP's yes: the group is there, the message is no member of it
    yet, and the record behind is the record in front with `Slice.withMessageInGroup` as its
    statement.
  `joined_joins`: `joins p d rs = some d'`, where the shape splits, gives the two groups in front
    with all of `Joined`'s fields. That G_u and G_omega are two groups, and o_omega and o_sp two
    messages, comes out of the yes: joinP enters no member twice.
  `joined_irrefl`: `Joined` holds of no record and itself: so a function that says yes to all and
    hands the record on does not give it. One that says no to all gives it, as it gives whatever is
    stated in the form "a yes gives".

Who joins `joined_joins` to a table at a shape S owes `p.S = S`. `rs` is idle, as in the text.

Limits. The block's own test ("o_omega has a tree to itself") is carried as the field `alone`. Of
joinP's eight tests two are carried ("the group is there", "no member twice"); that "in order" is
kept (the field `order`) is joinP_keeps (Johnson/Desc/Means/Page.lean), thrice. Of the
function `joins`; of the block that decides by it: Johnson/Desc/Key/Laid/AtBlocks.lean. Nothing on
soundness or on hiding.
-/
import Johnson.Desc.Key.Laid.JoinedDef
import OnBytes.Slice.BlkStLaws
import Johnson.Desc.Means.Page

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes OnBytes.Slice
open Desc.Plain (DState Par)
open VerifiableInference.Desc.Ground (joinP joinL ok has)
open _root_.Desc.K14 (St joins joinsL)

namespace VerifiableInference.Desc.Key

/-- joinP's yes, whole, with one of its tests. -/
theorem joinP_eq {L : Type} (d d' : DState L) (g o : Nat) (kept : Bool)
    (h : joinP d g o kept = some d') :
    ∃ G, d.st.groups[g]? = some G ∧ G.members.contains o = false ∧
      d' = { d with st := withMessageInGroup d.st g o kept G } := by
  unfold joinP at h
  split at h
  · rename_i hok
    cases hG : d.st.groups[g]? with
    | none =>
      rw [hG] at h
      cases h
    | some G =>
      rw [hG] at h
      simp only [ok, joinL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hok
      obtain ⟨_, _, _, _, _, _, c7, _⟩ := hok
      rw [hG] at c7
      exact ⟨G, rfl, by simpa [has] using c7, (Option.some.inj h).symm⟩
  · cases h

theorem joined_groupAt (S : Statement) (g o : Nat) (k : Bool) (G : Group)
    (h : S.groups[g]? = some G) : (withMessageInGroup S g o k G).groups[g]? = some (entered G o k) :=
  joined_group S g o k G h

theorem joined_groupOff (S : Statement) (g o : Nat) (k : Bool) (G : Group) (i : Nat) (h : g ≠ i) :
    (withMessageInGroup S g o k G).groups[i]? = S.groups[i]? := by
  simp [withMessageInGroup, Array.getElem?_modify, h]

/-- What is entered is a member. -/
theorem entered_has (G : Group) (o : Nat) (k : Bool) :
    (entered G o k).members.contains o = true := by
  have hle : (G.members.filter (· < o)).size ≤ G.members.size := Array.size_filter_le
  have hm : o ∈ G.members.insertIdxIfInBounds (G.members.filter (· < o)).size o := by
    unfold Array.insertIdxIfInBounds
    split
    · exact Array.mem_insertIdx.2 (Or.inl rfl)
    · rename_i hn
      exact absurd hle hn
  exact Array.contains_iff_mem.2 hm

/-- **The joinings' yes gives Joined.** -/
theorem joined_joins (p : Par) (d d' : St) (rs : List Fmt.RoundView) (hS : p.S.sharedSplitNeeded = true)
    (h : joins p d rs = some d') : ∃ GU GO, Joined d d' GU GO := by
  unfold joins at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨u0, hg, d1, h1, h2⟩ := h
  have hok : ok (joinsL d) = true := by
    by_contra hno
    simp [guard, hno] at hg
  have hal : Own.aloneIn d.book d.loc.oOmega = true := by
    simpa [ok, joinsL] using hok
  rw [if_pos hS] at h2
  simp only [Option.bind_eq_some_iff] at h2
  obtain ⟨d2, h3, h4⟩ := h2
  obtain ⟨G0, g0, _, e1⟩ := joinP_eq _ _ _ _ _ h1
  obtain ⟨G1, g1, n1, e2⟩ := joinP_eq _ _ _ _ _ h3
  obtain ⟨G2, g2, n2, e3⟩ := joinP_eq _ _ _ _ _ h4
  -- the three statements
  have s1 : d1.st = withMessageInGroup d.st d.loc.gOmega d.loc.oOmega false G0 := by rw [e1]
  have s2 : d2.st = withMessageInGroup d1.st d.loc.gOmega d.loc.oSp false G1 := by rw [e2]
  have s3 : d'.st = withMessageInGroup d2.st d.loc.gU d.loc.oSp false G2 := by rw [e3]
  have a1 : d1.st.groups[d.loc.gOmega]? = some (entered G0 d.loc.oOmega false) := by
    rw [s1]
    exact joined_groupAt _ _ _ _ _ g0
  have eG1 : G1 = entered G0 d.loc.oOmega false := Option.some.inj (g1.symm.trans a1)
  have a2 : d2.st.groups[d.loc.gOmega]? = some (entered G1 d.loc.oSp false) := by
    rw [s2]
    exact joined_groupAt _ _ _ _ _ g1
  -- two messages: o_sp was no member of the group that o_omega had entered
  have hap : d.loc.oOmega ≠ d.loc.oSp := by
    intro e
    have t := entered_has G0 d.loc.oOmega false
    rw [← eG1, e, n1] at t
    cases t
  -- two groups: o_sp was no member of G_u when it entered it; it had entered G_omega
  have hne : d.loc.gU ≠ d.loc.gOmega := by
    intro e
    rw [e] at g2
    have e' : G2 = entered G1 d.loc.oSp false := Option.some.inj (g2.symm.trans a2)
    have t := entered_has G1 d.loc.oSp false
    rw [← e', n2] at t
    cases t
  have hne' : d.loc.gOmega ≠ d.loc.gU := Ne.symm hne
  have u1 : d1.st.groups[d.loc.gU]? = d.st.groups[d.loc.gU]? := by
    rw [s1]
    exact joined_groupOff _ _ _ _ _ _ hne'
  have u2 : d2.st.groups[d.loc.gU]? = d1.st.groups[d.loc.gU]? := by
    rw [s2]
    exact joined_groupOff _ _ _ _ _ _ hne'
  have gU0 : d.st.groups[d.loc.gU]? = some G2 := (u1.symm.trans u2.symm).trans g2
  refine ⟨G2, G0, ?_, ?_, ?_, ?_, ?_, ?_, hne, hap, ?_, ?_, ?_, ?_, gU0, g0, ?_, ?_, ?_, hal,
    fun hI => Means.joinP_keeps h4 (Means.joinP_keeps h3 (Means.joinP_keeps h1 hI))⟩
  · rw [e3, e2, e1]
  · rw [e3, e2, e1]
  · rw [e3, e2, e1]
  · rw [e3, e2, e1]
  · rw [s3, s2, s1]
    rfl
  · rw [s3, s2, s1]
    simp [withMessageInGroup]
  · intro x hx
    rw [s3, joined_other _ _ _ _ _ _ (Ne.symm hap), s2, joined_other _ _ _ _ _ _ (Ne.symm hap), s1]
    exact joined_same _ _ _ _ _ x hx
  · intro x hx
    have m1 : d1.st.oracles[d.loc.oSp]? = some x := by
      rw [s1, joined_other _ _ _ _ _ _ hap]
      exact hx
    have m2 : d2.st.oracles[d.loc.oSp]? = some { x with groups := x.groups ++ [d.loc.gOmega] } := by
      rw [s2]
      exact joined_same _ _ _ _ _ x m1
    rw [s3, joined_same _ _ _ _ _ _ m2]
    simp [noted]
  · intro o ho1 ho2
    rw [s3, joined_other _ _ _ _ _ _ (Ne.symm ho2), s2, joined_other _ _ _ _ _ _ (Ne.symm ho2), s1,
      joined_other _ _ _ _ _ _ (Ne.symm ho1)]
  · rw [s3, s2, s1]
    simp [withMessageInGroup]
  · rw [s3]
    exact joined_groupAt _ _ _ _ _ g2
  · rw [s3, joined_groupOff _ _ _ _ _ _ hne, a2, eG1]
  · intro i hU hO
    rw [s3, joined_groupOff _ _ _ _ _ _ (Ne.symm hU), s2, joined_groupOff _ _ _ _ _ _ (Ne.symm hO),
      s1, joined_groupOff _ _ _ _ _ _ (Ne.symm hO)]

/-- Entering makes the list of members longer by one. -/
theorem entered_size (G : Group) (o : Nat) (k : Bool) :
    (entered G o k).members.size = G.members.size + 1 := by
  have hle : (G.members.filter (· < o)).size ≤ G.members.size := Array.size_filter_le
  simp [entered, Array.insertIdxIfInBounds, hle]

/-- Joined holds of no record and itself: G_u has a member more behind. -/
theorem joined_irrefl (d : St) (GU GO : Group) : ¬ Joined d d GU GO := by
  intro h
  have e := Option.some.inj (h.gU.symm.trans h.gU')
  have t := entered_size GU d.loc.oSp false
  rw [← e] at t
  omega

end VerifiableInference.Desc.Key
