-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/MembersSplit.lean: the code switch: THE NAMED TEST
membersK2B | membersPlanB (Johnson/Top/H0/K2Caller/MembersAtK2.lean | MembersAtPlan.lean), SPLIT IN
TWO. The test compares, at each listed tenant, the (shape, radius) entry of every member of the
table that sits there with the typed row's entry by place (Johnson/Desc/Sound/MembersAtB.lean's
sitsB). SO IT READS THE RADII.
  strike · SwRow.struck  an entry, and a typed row, with every radius struck
  mem_pairs    the pairs (entry, tenant) of the lists by the make (P5T.memberListsR): one for each
               seat of the plan with a sample, at (sending k, place j): ((its shape, rad k j), its
               tenant)
  sits_split   sitsB at rad from sitsB with the radii struck on both sides and the radii's own
               clause
  snd_of_entry · pairs_seats · once_same  the pairs' tenants, and so onceB, hang on no radius
  kept_struck  the struck row's kept entries are the row's, struck
  members_split · membersPlan_split  THE SPLIT: the test accepts where (A) THE SAME TEST ACCEPTS
               WITH EVERY RADIUS STRUCK ON BOTH SIDES and (B) at each seat of the plan with a sample
               that sits at a listed tenant: the radius at its sending and place is the typed
               entry's
(B) IS A PREMISE (a Prop), NO NEW NAMED TEST. A NOTE FOR LATER. The test is kept by any map on radii
applied on both sides: so at the MADE table's row, whose entries are the rows' own, it could be had
with no value of a radius: lay a tag (k, j) in each radius's place, evaluate once, map the tags. Not
typed.
LIMITS. General in the plan's seats and the radii. No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.MembersAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes
open VerifiableInference.Desc.Sound (pairsOf sitsB onceB)
open VerifiableInference.Desc.First.K2Caller (SwRow membersK2B membersPlanB keptEntries)
open P5T (PSeat mineAt memberListsR)

/-- An entry with its radius struck. -/
def strike (e : OracleShape × ℕ) : OracleShape × ℕ := (e.1, 0)

/-- A typed row with every radius struck. -/
def SwRow.struck (r : SwRow) : SwRow := { r with lo := r.lo.map strike, l := r.l.map strike }

/-- **The pairs of the lists by the make.** -/
theorem mem_pairs {n : ℕ} {rad : ℕ → ℕ → ℕ} {ps : List PSeat}
    {x : (OracleShape × ℕ) × (ℕ × ℕ)} :
    x ∈ pairsOf (memberListsR n rad ps) ↔ ∃ k j p, k < n ∧ (mineAt ps k)[j]? = some p ∧
      x = ((p.shape, rad k j), p.seat) := by
  unfold pairsOf memberListsR
  simp only [List.mem_flatMap, List.mem_map, List.mem_range, List.mem_finRange, true_and]
  constructor
  · rintro ⟨e, ⟨k, hk, rfl⟩, i, rfl⟩
    have hi : i.val < (mineAt ps k).length := by
      have := i.isLt
      simpa using this
    refine ⟨k, i.val, (mineAt ps k)[i.val], hk, List.getElem?_eq_getElem hi, ?_⟩
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  · rintro ⟨k, j, p, hk, hp, rfl⟩
    obtain ⟨hj, e⟩ := List.getElem?_eq_some_iff.1 hp
    refine ⟨_, ⟨k, hk, rfl⟩, ⟨j, by simpa using hj⟩, ?_⟩
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, e]

/-- **One half of the test, split.** -/
theorem sits_split {n : ℕ} {rad : ℕ → ℕ → ℕ} {ps : List PSeat} {qs : List (ℕ × ℕ)}
    {es : List (OracleShape × ℕ)}
    (hA : sitsB (memberListsR n (fun _ _ => 0) ps) qs (es.map strike) = true)
    (hB : ∀ k j p, k < n → (mineAt ps k)[j]? = some p → ∀ qe ∈ qs.zip es, p.seat = qe.1 →
      rad k j = qe.2.2) :
    sitsB (memberListsR n rad ps) qs es = true := by
  unfold sitsB at hA ⊢
  rw [Bool.and_eq_true, decide_eq_true_eq] at hA ⊢
  obtain ⟨h1, h2⟩ := hA
  refine ⟨by simpa using h1, List.all_eq_true.2 fun qe hqe => ?_⟩
  have hz : (qe.1, strike qe.2) ∈ qs.zip (es.map strike) := by
    rw [List.zip_map_right]
    exact List.mem_map.2 ⟨qe, hqe, rfl⟩
  have h3 := List.all_eq_true.1 h2 _ hz
  rw [Bool.and_eq_true] at h3 ⊢
  obtain ⟨ha, hb⟩ := h3
  constructor
  · obtain ⟨x, hx, e⟩ := List.any_eq_true.1 ha
    obtain ⟨k, j, p, hk, hp, rfl⟩ := mem_pairs.1 hx
    exact List.any_eq_true.2 ⟨((p.shape, rad k j), p.seat), mem_pairs.2 ⟨k, j, p, hk, hp, rfl⟩, e⟩
  · refine List.all_eq_true.2 fun x hx => ?_
    obtain ⟨k, j, p, hk, hp, rfl⟩ := mem_pairs.1 hx
    have h4 := List.all_eq_true.1 hb ((p.shape, 0), p.seat) (mem_pairs.2 ⟨k, j, p, hk, hp, rfl⟩)
    rw [Bool.or_eq_true] at h4 ⊢
    rcases h4 with h4 | h4
    · exact Or.inl h4
    · by_cases hs : p.seat = qe.1
      · right
        have e1 : ((p.shape, 0) : OracleShape × ℕ) = strike qe.2 := eq_of_beq h4
        have e2 : p.shape = qe.2.1 := congrArg Prod.fst e1
        rw [beq_iff_eq]
        show (p.shape, rad k j) = qe.2
        exact Prod.ext e2 (hB k j p hk hp qe hqe hs)
      · left
        exact bne_iff_ne.2 hs

/-- The tenants of an entry of the lists. -/
theorem snd_of_entry {α : Type} (l : List α) (s : List (ℕ × ℕ)) (h : s.length = l.length) :
    ((List.finRange l.length).map fun i => (l.get i, s.getD i.val (0, 0))).map (·.2) = s := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- The pairs' tenants hang on no radius. -/
theorem pairs_seats (n : ℕ) (rad : ℕ → ℕ → ℕ) (ps : List PSeat) :
    (pairsOf (memberListsR n rad ps)).map (·.2) =
      (List.range n).flatMap fun k => (mineAt ps k).map (·.seat) := by
  unfold pairsOf memberListsR
  rw [List.map_flatMap, List.flatMap_map]
  refine List.flatMap_congr fun k _ => ?_
  exact snd_of_entry _ _ (by simp)

theorem once_same (n : ℕ) (rad rad' : ℕ → ℕ → ℕ) (ps : List PSeat) (qs : List (ℕ × ℕ)) :
    onceB (memberListsR n rad ps) qs = onceB (memberListsR n rad' ps) qs := by
  unfold onceB
  rw [pairs_seats, pairs_seats]

theorem kept_struck (r : SwRow) : keptEntries (SwRow.struck r) = (keptEntries r).map strike := by
  unfold keptEntries SwRow.struck
  rw [List.map_map]
  refine List.map_congr_left fun i _ => ?_
  show (r.lo.map strike).getD i default = strike (r.lo.getD i default)
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases r.lo[i]? <;> rfl

/-- **THE TEST, SPLIT**: (A) the test with every radius struck, on both sides · (B) at each seat of
the plan with a sample that sits at a listed tenant: the radius at its sending and place is the
typed entry's. -/
theorem members_split {n : ℕ} {rad : ℕ → ℕ → ℕ} {ps : List PSeat} {kq nq : List (ℕ × ℕ)}
    {r : SwRow}
    (hA : membersK2B (memberListsR n (fun _ _ => 0) ps) kq nq (SwRow.struck r) = true)
    (hB : ∀ k j p, k < n → (mineAt ps k)[j]? = some p →
      ∀ qe ∈ kq.zip (keptEntries r) ++ nq.zip r.l, p.seat = qe.1 → rad k j = qe.2.2) :
    membersK2B (memberListsR n rad ps) kq nq r = true := by
  unfold membersK2B at hA ⊢
  simp only [Bool.and_eq_true] at hA ⊢
  obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := hA
  rw [kept_struck] at a1
  refine ⟨⟨⟨sits_split a1 fun k j p hk hp qe hq => hB k j p hk hp qe (List.mem_append_left _ hq),
    by rw [once_same n rad fun _ _ => 0]; exact a2⟩,
    sits_split a3 fun k j p hk hp qe hq => hB k j p hk hp qe (List.mem_append_right _ hq)⟩, ?_⟩
  have e : (SwRow.struck r).l.length = r.l.length := List.length_map _
  rw [← e]
  exact a4

/-- **The same at the composed meaning's terms.** -/
theorem membersPlan_split {Z : ProofFile.Pub} {rad : ℕ → ℕ → ℕ} {N : Numbers} {l : ℕ} {r : SwRow}
    (hA : membersPlanB Z (fun _ _ => 0) N l (SwRow.struck r) = true)
    (hB : ∀ k j p, k < Z.made.proof.1.sends.length →
      (mineAt (P5T.planSeats Z Z.D.1) k)[j]? = some p →
      ∀ qe ∈ (N.keptOf (l - 1)).zip (keptEntries r) ++ (N.sent l 0).zip r.l, p.seat = qe.1 →
        rad k j = qe.2.2) :
    membersPlanB Z rad N l r = true :=
  members_split hA hB

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.sits_split
#print axioms VerifiableInference.Desc.First.K2Ties.snd_of_entry
#print axioms VerifiableInference.Desc.First.K2Ties.pairs_seats
#print axioms VerifiableInference.Desc.First.K2Ties.once_same
#print axioms VerifiableInference.Desc.First.K2Ties.kept_struck
#print axioms VerifiableInference.Desc.First.K2Ties.members_split
#print axioms VerifiableInference.Desc.First.K2Ties.membersPlan_split

#print axioms VerifiableInference.Desc.First.K2Ties.mem_pairs
