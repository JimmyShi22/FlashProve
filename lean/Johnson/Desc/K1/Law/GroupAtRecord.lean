-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GroupAtRecord.lean: WHAT A SENDING OF KIND K1 DOES TO THE STATEMENT's GROUPS:
the first segment's opening makes one group more, which has no row, stands in no test, and has as
members just the segment's own messages of the first moment. Definitions and statements with their
proofs. It names no table of joints.
Main names:
  `Joins st st' g ids`: the groups are as many; every group but g is as it was; group g keeps its
    rows and its mark "in a test", and its members are those that it had and ids.
  `joinP_joins`, `joinAll_joins`, `joinOwnP_joins`: the ground's joining, one message, a list, a
    moment's own messages.
  `newGroupP_group`: one more group: its number is the number of groups in front; no member, no row,
    in no test; the older groups are as they were.
  `Opened st own st'`: one group more; the older ones as they were; the new one has no row, stands
    in no test, and has as members just the own messages' numbers: those of the first `own` new
    messages.
  `firstOwn_group`: **the opening's decision.** `firstAtS_group`: **the block at the record.** Both
    say too that the frame's group behind is the new group's number, and that the place sends more
    messages than the segment's own.

What is not claimed. The order of the members. What a later moment joins (the frame's own group: its
number is the record's word). Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.OpeningZero
import Johnson.Desc.K1.Law.KeptAtRecord
import Johnson.Desc.Third.Law.Later

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.First.Send (joinOwnP joinAll)
open VerifiableInference.Desc.First (S)

variable {L Cl : Type}

/-- **What a joining does to the groups.** -/
structure Joins (st st' : Statement) (g : Nat) (ids : List Nat) : Prop where
  size : st'.groups.size = st.groups.size
  other : ∀ j, j ≠ g → st'.groups[j]? = st.groups[j]?
  here : ∀ G, st.groups[g]? = some G → ∃ G', st'.groups[g]? = some G' ∧ G'.inRun = G.inRun ∧
    G'.rows = G.rows ∧ ∀ o, o ∈ G'.members.toList ↔ (o ∈ G.members.toList ∨ o ∈ ids)

theorem Joins.refl (st : Statement) (g : Nat) : Joins st st g [] :=
  ⟨rfl, fun _ _ => rfl, fun G h => ⟨G, h, rfl, rfl, fun o => by simp⟩⟩

theorem Joins.trans {a b c : Statement} {g : Nat} {l m : List Nat} (h : Joins a b g l)
    (k : Joins b c g m) : Joins a c g (l ++ m) := by
  refine ⟨k.size.trans h.size, fun j hj => (k.other j hj).trans (h.other j hj), fun G hG => ?_⟩
  obtain ⟨G₁, h1, a1, a2, a3⟩ := h.here G hG
  obtain ⟨G₂, h2, b1, b2, b3⟩ := k.here G₁ h1
  refine ⟨G₂, h2, b1.trans a1, b2.trans a2, fun o => ?_⟩
  rw [b3, a3, List.mem_append, or_assoc]

/-- One message joins. -/
theorem joinP_joins (d d' : DState L) (g o : Nat) (kept : Bool)
    (h : Ground.joinP d g o kept = some d') : Joins d.st d'.st g [o] := by
  obtain ⟨G, hG, _, e⟩ := Later.joinP_inv d d' g o kept h
  rw [e]
  refine ⟨by simp [withMessageInGroup], fun j hj => ?_, fun G₀ hG₀ => ?_⟩
  · show (d.st.groups.modify g _)[j]? = _
    rw [Array.getElem?_modify, if_neg (fun e => hj e.symm)]
  · obtain rfl : G = G₀ := Option.some.inj (hG.symm.trans hG₀)
    refine ⟨{ G with
      members := G.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
      kept := G.kept.insertIdxIfInBounds (G.members.filter (· < o)).size kept }, ?_, rfl, rfl,
      fun x => ?_⟩
    · show (d.st.groups.modify g _)[g]? = _
      rw [Array.getElem?_modify, if_pos rfl, hG]
      rfl
    · show x ∈ (G.members.insertIdxIfInBounds (G.members.filter (· < o)).size o).toList ↔ _
      have hle : (G.members.filter (· < o)).size ≤ G.members.size := Array.size_filter_le
      unfold Array.insertIdxIfInBounds
      rw [dif_pos hle, Array.mem_toList_iff, Array.mem_insertIdx, Array.mem_toList_iff,
        List.mem_singleton, or_comm]

/-- A list of messages joins. -/
theorem joinAll_joins (p : GPar) (g : Nat) : ∀ (l : List (ReqMessage × Nat)) (d d' : DState L),
    joinAll groundG p g l d = some d' → Joins d.st d'.st g (l.map Prod.snd)
  | [], d, d', h => by
    obtain rfl := Option.some.inj h
    exact Joins.refl _ _
  | x :: l, d, d', h => by
    obtain ⟨e, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact (joinP_joins d e g x.2 _ h1).trans (joinAll_joins p g l e d' h2)

/-- A moment's own messages join the frame's group. -/
theorem joinOwnP_joins (p : GPar) (d : DState L) (f : ReqFrame) (sent : List ReqMessage)
    (ids : Array Nat) (y : ReqFrame × DState L) (h : joinOwnP groundG p d f sent ids = some y) :
    Joins d.st y.2.st f.group ids.toList ∧ y.1 = { f with own := f.own ++ ids } := by
  unfold joinOwnP at h
  split at h
  · rename_i hl
    obtain ⟨d', h1, rfl⟩ := Option.map_eq_some_iff.1 h
    have hj := joinAll_joins p f.group _ d d' h1
    have hlen : ids.toList.length ≤ sent.length := by
      rw [Array.length_toList]
      exact Nat.le_of_eq (eq_of_beq hl).symm
    rw [zipT_eq, List.map_snd_zip hlen] at hj
    exact ⟨hj, rfl⟩
  · cases h

/-- One more group. -/
theorem newGroupP_group (d d' : DState L) (code maskCode n : Nat)
    (h : Ground.newGroupP d code maskCode = some (n, d')) :
    n = d.st.groups.size ∧ d'.st.groups.size = d.st.groups.size + 1 ∧
      (∀ j, j < d.st.groups.size → d'.st.groups[j]? = d.st.groups[j]?) ∧
      ∃ G, d'.st.groups[n]? = some G ∧ G.inRun = false ∧ G.rows = #[] ∧ G.members = #[] := by
  unfold Ground.newGroupP at h
  split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨rfl, by simp [Ground.withGroup], fun j hj => ?_,
      { code := code, maskCode := maskCode }, ?_, rfl, rfl, rfl⟩
    · show (d.st.groups.push _)[j]? = _
      rw [Array.getElem?_push_lt hj, Array.getElem?_eq_getElem hj]
    · show (d.st.groups.push _)[d.st.groups.size]? = _
      rw [Array.getElem?_push_size]
  · cases h

/-- The first k of the numbers n₀, n₀ + 1, … -/
theorem mem_firstIds (n n₀ k o : Nat) (hk : k ≤ n) :
    o ∈ (((Array.range n).map (· + n₀)).extract 0 k).toList ↔ (n₀ ≤ o ∧ o < n₀ + k) := by
  rw [Array.toList_extract, List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero,
    Array.toList_map, Array.toList_range, ← List.map_take, List.take_range, Nat.min_eq_left hk,
    List.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have := List.mem_range.1 hi
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨o - n₀, List.mem_range.2 (by omega), by omega⟩

/-- **What the first segment's opening does to the groups.** st, n₀: the statement and its number of
messages in front; own: how many messages of its own the segment has at the first moment. -/
structure Opened (st : Statement) (own : Nat) (st' : Statement) : Prop where
  size : st'.groups.size = st.groups.size + 1
  older : ∀ j, j < st.groups.size → st'.groups[j]? = st.groups[j]?
  made : ∃ G, st'.groups[st.groups.size]? = some G ∧ G.inRun = false ∧ G.rows = #[] ∧
    ∀ o, o ∈ G.members.toList ↔ (st.oracles.size ≤ o ∧ o < st.oracles.size + own)

/-- **The opening's decision.** -/
theorem firstOwn_group (P : Par) (owed : Option Nat) (c c' : ChainCheck) (d d' : DState Unit)
    (r₁ r₂ : Fmt.RoundView) (h : firstOwn P owed c d [r₁, r₂] = .ok (c', d')) :
    Opened d.st (c.frame.atMoment 0).length d'.st ∧ c'.frame.group = d.st.groups.size ∧
      (c.frame.atMoment 0).length < P.sent.size := by
  unfold firstOwn at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨g, d₁⟩, h1, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨ids, d₂⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨mask, hmask, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨f₂, d₃⟩, h3, hfin⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, hids, _⟩ := (decideSend_iff P owed d₁ d₂ r₁ r₂ ids).1 h2
  have hg := (named_ok _ _ _).1 h1
  obtain ⟨rfl, n1, n2, G, n3, n4, n5, n6⟩ := newGroupP_group _ _ _ _ _ hg
  have hn := (newGroupP_book _ _ _ _ _ hg).2
  have hk : d₂.st.groups = d₁.st.groups := (decideSend_kept P owed d₁ d₂ _ ids h2).2.1
  obtain ⟨hj, hf⟩ := joinOwnP_joins _ _ _ _ _ _ ((named_ok _ _ _).1 h3)
  have hlt : (c.frame.atMoment 0).length < ids.size := by
    have hm := (named_ok _ _ _).1 hmask
    by_contra hx
    rw [Array.getElem?_eq_none (by omega)] at hm
    cases hm
  have hsz : ids.size = P.sent.size := by rw [hids]; simp
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hfin)
  refine ⟨⟨by rw [hj.size, hk, n1], fun j hjlt => ?_, ?_⟩, ?_, by omega⟩
  · rw [hj.other j (by show j ≠ d.st.groups.size; omega), hk, n2 j hjlt]
  · obtain ⟨G', g1, g2, g3, g4⟩ := hj.here G (by rw [hk]; exact n3)
    refine ⟨G', g1, g2.trans n4, g3.trans n5, fun o => ?_⟩
    rw [g4, n6, hids, mem_firstIds _ _ _ _ (by omega), hn]
    simp
  · have hf' : f₂ = _ := hf
    show f₂.group = _
    rw [hf']

/-- **The block at the record.** -/
theorem firstAtS_group (q : Params.First) (gp : GPar) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    Opened s.st (s.check.frame.atMoment 0).length s'.st ∧
      s'.check.frame.group = s.st.groups.size ∧
      (s.check.frame.atMoment 0).length < (firstPar q gp).sent.size := by
  unfold firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨c, d'⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  obtain rfl := Except.ok.inj h
  exact firstOwn_group _ _ _ c _ d' r₁ r₂ h2

end VerifiableInference.Desc.K1
