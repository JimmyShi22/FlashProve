-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GroupsAtLater.lean: KIND K1's LATER SENDINGS JOIN FRESH MESSAGES ALONE TO A
GROUP: so a message that is there already, and is a member of no group, is a member of none behind.

  OutOf i T        message number i is a member of no group of the statement T.
  decideSend_ids   the numbers that the sending's decision returns: the statement's old size and
                   upward, on whatever rounds.
  outOf_join, outOf_joinAll, outOf_joinOwn   a joining of other numbers leaves OutOf i.
  commitAtS_outOf, later_outOf   a segment's later moment; both sub-protocols of a segment's later
                   places (Later, Johnson/Desc/K1/Law/InOrderAtLater.lean), on any rounds.
  later_hands      THE TWO CLAUSES TOGETHER, at the index masks' message: where its ledger is there,
                   not closed, with n entries left (leftIsB,
                   Johnson/Top/H0/Walk/FrameEntriesDefs.lean), and it is a member of no group: both
                   hold behind.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.SameLedgersAtLater
import Johnson.Top.H0.Walk.FrameEntriesDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.First.Send (joinOwnP joinAll)
open VerifiableInference.Desc.First (S)
open OnBytes.Model.Stages (LinkH)
open IM (k1Reads k1Quiet)

variable {L Cl : Type}

/-- Message number i is a member of no group. -/
def OutOf (i : ℕ) (T : Statement) : Prop := ∀ G ∈ T.groups, i ∉ G.members

theorem decideSend_ids (P : Par) (owed : Option Nat) (d d' : DState L) (rs : List Fmt.RoundView)
    (ids : Array Nat) (h : decideSend P owed d rs = .ok (ids, d')) :
    ids = (Array.range P.sent.size).map (· + d.st.oracles.size) := by
  match rs, h with
  | [r₁, r₂], h => exact ((decideSend_iff P owed d d' r₁ r₂ ids).1 h).2.1

theorem outOf_join {i : ℕ} (d d' : DState L) (g o : Nat) (kept : Bool)
    (h : Ground.joinP d g o kept = some d') (hne : i ≠ o) (hO : OutOf i d.st) :
    OutOf i d'.st := by
  obtain ⟨G, _, _, e⟩ := Later.joinP_inv d d' g o kept h
  intro G' hG' hmem
  rw [e] at hG'
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 hG'
  have hk' : (d.st.groups.modify g fun G' => { G' with
      members := G'.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
      kept := G'.kept.insertIdxIfInBounds (G.members.filter (· < o)).size kept })[k]? =
      some G' := hk
  rw [Array.getElem?_modify] at hk'
  by_cases e2 : g = k
  · rw [if_pos e2] at hk'
    obtain ⟨G₀, hG₀, rfl⟩ := Option.map_eq_some_iff.1 hk'
    have hm : i ∈ G₀.members.insertIdxIfInBounds (G.members.filter (· < o)).size o := hmem
    unfold Array.insertIdxIfInBounds at hm
    split at hm
    · rcases Array.mem_insertIdx.1 hm with r | r
      · exact hne r
      · exact hO G₀ (Array.mem_of_getElem? hG₀) r
    · exact hO G₀ (Array.mem_of_getElem? hG₀) hm
  · rw [if_neg e2] at hk'
    exact hO G' (Array.mem_of_getElem? hk') hmem

theorem outOf_joinAll {i : ℕ} (p : GPar) (g : Nat) : ∀ (l : List (ReqMessage × Nat))
    (d d' : DState L), joinAll groundG p g l d = some d' → (∀ x ∈ l, i ≠ x.2) →
    OutOf i d.st → OutOf i d'.st
  | [], d, d', h, _, hO => by
    obtain rfl := Option.some.inj h
    exact hO
  | x :: l, d, d', h, hn, hO => by
    obtain ⟨e, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    exact outOf_joinAll p g l e d' h2 (fun y hy => hn y (List.mem_cons_of_mem _ hy))
      (outOf_join d e g x.2 _ h1 (hn x List.mem_cons_self) hO)

theorem outOf_joinOwn {i : ℕ} (p : GPar) (d : DState L) (f : ReqFrame) (sent : List ReqMessage)
    (ids : Array Nat) (y : ReqFrame × DState L) (h : joinOwnP groundG p d f sent ids = some y)
    (hn : ∀ j ∈ ids.toList, i ≠ j) (hO : OutOf i d.st) : OutOf i y.2.st := by
  unfold joinOwnP at h
  split at h
  · obtain ⟨d', h1, rfl⟩ := Option.map_eq_some_iff.1 h
    refine outOf_joinAll p f.group _ d d' h1 (fun x hx => hn x.2 ?_) hO
    rw [zipT_eq] at hx
    exact (List.of_mem_zip hx).2
  · cases h

/-- **A segment's later moment.** -/
theorem commitAtS_outOf {i : ℕ} (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS (Cl := Cl) P link moment arrays).decide s rs gs = .ok s')
    (hi : i < s.st.oracles.size) (hO : OutOf i s.st) : OutOf i s'.st := by
  unfold commitAtS at h
  dsimp only at h
  split at h
  · obtain ⟨y, hy, rfl⟩ := Keeps.emap_ok h
    obtain ⟨ids, d₁, f', h2, h3⟩ := commitOwn_ok P link moment arrays _ y _ gs hy
    show OutOf i (((laid s y.held.w).putLink y.held.L).putFork y.held.F).st
    rw [Rel.putFork_st, Rel.putLink_st]
    have hk := decideSend_kept P _ _ d₁ rs ids h2
    have hids := decideSend_ids P _ _ d₁ rs ids h2
    refine outOf_joinOwn _ _ _ _ _ _ h3 (fun j hj => ?_) (fun G hG => hO G (hk.2.1 ▸ hG))
    rw [hids] at hj
    simp only [Array.toList_map, Array.toList_range, List.mem_map, List.mem_range] at hj
    obtain ⟨a, _, rfl⟩ := hj
    have hi' : i < s.st.oracles.size := hi
    exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hi' (Nat.le_add_left _ _))
  · cases h

/-- **At both sub-protocols of a segment's later places**, on any rounds. -/
theorem later_outOf {i : ℕ} {B own : Block S Unit} (hB : Later B own) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (h : B.decide s rs gs = .ok s')
    (hi : i < s.st.oracles.size) (hO : OutOf i s.st) : OutOf i s'.st := by
  cases hB with
  | digits q gp l piece digits => exact commitAtS_outOf _ l 2 digits s s' rs gs h hi hO
  | reads Z G l X pr reads =>
    have h' : ((laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).decide s
        (rs.take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
        (gs.take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)).bind (fun s₁ =>
        (k1Quiet G l X).decide s₁
          (rs.drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
          (gs.drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)) = .ok s' := h
    obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
    rw [k1Quiet_st G l X _ _ _ _ h2]
    exact commitAtS_outOf _ l 1 reads s s₁ _ _ h1 hi hO

open Johnson.Desc.First.Walk.Tied (leftIsB) in
/-- **THE TWO CLAUSES TOGETHER, at the index masks' message.** -/
theorem later_hands {B own : Block S Unit} (hB : Later B own) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : B.decide s rs gs = .ok s') {n : ℕ}
    (hn : leftIsB n s = true) (hO : OutOf s.out.indexMasks s.st) :
    leftIsB n s' = true ∧ OutOf s'.out.indexMasks s'.st := by
  unfold leftIsB Johnson.Desc.First.Walk.Law.ledgerAt at hn
  cases hl : (s.st.oracles[s.out.indexMasks]?).bind (·.ledger) with
  | none =>
    rw [hl] at hn
    cases hn
  | some l =>
    obtain ⟨hi, hl'⟩ := later_ledgerAtMasks hB h hl
    obtain ⟨x, hx, -⟩ := Option.bind_eq_some_iff.1 hl
    refine ⟨?_, ?_⟩
    · unfold leftIsB Johnson.Desc.First.Walk.Law.ledgerAt
      rw [hl']
      rw [hl] at hn
      exact hn
    · rw [hi]
      exact later_outOf hB h (Array.getElem?_eq_some_iff.1 hx).1 hO

end VerifiableInference.Desc.K1
