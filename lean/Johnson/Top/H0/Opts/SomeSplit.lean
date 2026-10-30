-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/SomeSplit.lean: THE NAMED TEST «some» (P5T.someB,
Johnson/P5J/Rad3Seat3At.lean) AT MEMBERS THAT ARE MADE OFF THE PLAN's SEATS (P5T.memberListsR,
Johnson/P5T/MembersByMake.lean), SPLIT IN TWO: what it asks of the plan's seats, and what it asks
of the radii. General: no scope, no pin, no file is read. NO BLOCK IMPORTS THIS FILE.
  mem_made       the member at (sending k, place j) of the made lists is a member of msOf
  some_of_seats  THE CORE: where each place i of the list L has a seat p of the plan, with a
                 sample, at (sending k < n, place j), with L's shape at i, the seat «seat i» and
                 rad k j = L's radius at i: the test accepts
  idx_of_mine    a seat with a sample of sending k stands at some place of that sending's list
  some_split     (A) each place of L has a seat of the plan with a sample, of a sending below n,
                 with its shape and seat · (B) at every made member the radius is R of its shape ·
                 hL: L's radius at i is R of L's shape at i ⟹ the test accepts
  rad_of_one     where one shape has one radius over the first chain's rows (radOneB) and
                 the rows' entry (k, j) is (sh, ρ): radOf rows k j is the radius of the FIRST
                 entry of the shape sh: rad3At's own text
WHY. callsSomeB | digSomeB (Johnson/P5J/Rad3Seat3Tests.lean) compare (shape, radius) pairs; (A)
reads the public part alone; (B) is one fact on the rows for all links and both lists.
LIMITS. (A), (B), radOneB are shown nowhere here. No soundness is claimed.
-/
import Johnson.P5J.Rad3Seat3At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1Opts
open OnBytes
open VerifiableInference.Desc.Sound (Mem Sending msOf sendsOf membersOf)
open P5T (PSeat mineAt memberListsR someB radOf rad? radOneB firstRows)

theorem mem_made (n : ℕ) (rad : ℕ → ℕ → ℕ) (ps : List PSeat) {k : ℕ} (hk : k < n)
    (j : Fin (Sending.ofLists ((mineAt ps k).zipIdx.map fun x => (x.1.shape, rad k x.2))
      ((mineAt ps k).map (·.seat))).l.length) :
    (⟨Sending.ofLists ((mineAt ps k).zipIdx.map fun x => (x.1.shape, rad k x.2))
      ((mineAt ps k).map (·.seat)), j⟩ : Mem) ∈ msOf (memberListsR n rad ps) := by
  unfold msOf membersOf sendsOf memberListsR
  refine List.mem_flatMap.2 ⟨_, ?_, List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩⟩
  rw [List.map_map]
  exact List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩

theorem some_of_seats (n : ℕ) (rad : ℕ → ℕ → ℕ) (ps : List PSeat) (L : List (OracleShape × ℕ))
    (seat : ℕ → ℕ × ℕ)
    (h : ∀ i : Fin L.length, ∃ k j p, k < n ∧ (mineAt ps k)[j]? = some p ∧
      p.shape = (L.get i).1 ∧ p.seat = seat i.1 ∧ rad k j = (L.get i).2) :
    someB (msOf (memberListsR n rad ps)) L seat = true := by
  unfold someB
  apply List.all_eq_true.2
  intro i _
  obtain ⟨k, j, p, hk, hp, e1, e2, e3⟩ := h i
  have hj : j < (mineAt ps k).length := (List.getElem?_eq_some_iff.1 hp).1
  have hpj : (mineAt ps k)[j] = p := (List.getElem?_eq_some_iff.1 hp).2
  have hlen : ((mineAt ps k).zipIdx.map fun x => (x.1.shape, rad k x.2)).length =
      (mineAt ps k).length := by simp
  refine List.any_eq_true.2 ⟨_, mem_made n rad ps hk ⟨j, hlen ▸ hj⟩, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨decide_eq_true ?_, decide_eq_true ?_⟩
  · show ((mineAt ps k).zipIdx.map fun x => (x.1.shape, rad k x.2)).get ⟨j, hlen ▸ hj⟩ = L.get i
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_zipIdx, Nat.zero_add, hpj]
    exact Prod.ext e1 e3
  · show ((mineAt ps k).map (·.seat)).getD j (0, 0) = seat i.1
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hp]
    exact e2

theorem idx_of_mine {ps : List PSeat} {p : PSeat} (hp : p ∈ ps) (hs : p.smpd = true) :
    ∃ j : ℕ, (mineAt ps p.send)[j]? = some p := by
  have hm : p ∈ mineAt ps p.send := by
    unfold mineAt
    refine List.mem_filter.2 ⟨hp, ?_⟩
    rw [Bool.and_eq_true]
    exact ⟨beq_self_eq_true _, hs⟩
  obtain ⟨j, hj, e⟩ := List.getElem_of_mem hm
  exact ⟨j, List.getElem?_eq_some_iff.2 ⟨hj, e⟩⟩

theorem some_split (n : ℕ) (rad : ℕ → ℕ → ℕ) (ps : List PSeat) (L : List (OracleShape × ℕ))
    (seat : ℕ → ℕ × ℕ) (R : OracleShape → ℕ)
    (hL : ∀ i : Fin L.length, (L.get i).2 = R (L.get i).1)
    (A : ∀ i : Fin L.length, ∃ p ∈ ps, p.smpd = true ∧ p.send < n ∧ p.shape = (L.get i).1 ∧
      p.seat = seat i.1)
    (B : ∀ k j p, (mineAt ps k)[j]? = some p → rad k j = R p.shape) :
    someB (msOf (memberListsR n rad ps)) L seat = true := by
  refine some_of_seats n rad ps L seat fun i => ?_
  obtain ⟨p, hp, hs, hn, e1, e2⟩ := A i
  obtain ⟨j, hj⟩ := idx_of_mine hp hs
  exact ⟨p.send, j, p, hn, hj, e1, e2, by rw [B _ _ _ hj, e1, hL i]⟩

theorem rad_of_one (rows : List Johnson.G.SendRow)
    (h1 : radOneB ((firstRows rows).flatMap (·.sampled)) = true) {k j : ℕ} {sh : OracleShape}
    {ρ : ℕ} (he : ((firstRows rows)[k]?).bind (·.sampled[j]?) = some (sh, ρ)) :
    radOf rows k j =
      ((((firstRows rows).flatMap (·.sampled)).find? (·.1 == sh)).map (·.2)).getD 0 := by
  have e0 : radOf rows k j = ρ := by
    unfold radOf rad?
    rw [he]
    rfl
  obtain ⟨row, hrow, hent⟩ := Option.bind_eq_some_iff.1 he
  have hmem : (sh, ρ) ∈ (firstRows rows).flatMap (·.sampled) :=
    List.mem_flatMap.2 ⟨row, List.mem_of_getElem? hrow, List.mem_of_getElem? hent⟩
  cases hf : ((firstRows rows).flatMap (·.sampled)).find? (·.1 == sh) with
  | none =>
    have := List.find?_eq_none.1 hf (sh, ρ) hmem
    simp at this
  | some y =>
    have hy := List.mem_of_find?_eq_some hf
    have hys : (y.1 == sh) = true := by
      have h3 := List.find?_some hf
      exact h3
    have h2 := List.all_eq_true.1 (List.all_eq_true.1 h1 y hy) (sh, ρ) hmem
    rw [Bool.or_eq_true] at h2
    rw [e0]
    rcases h2 with h2 | h2
    · rw [bne_iff_ne] at h2
      exact absurd (eq_of_beq hys) h2
    · exact (eq_of_beq h2).symm

end P1Opts

#print axioms P1Opts.some_of_seats
#print axioms P1Opts.some_split
#print axioms P1Opts.rad_of_one
