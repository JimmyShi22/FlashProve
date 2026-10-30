-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5T/MembersByMake.lean: THE TYPED ORACLE MESSAGES' LISTS WITH THEIR SHAPES AND
(tree, tenant)s OFF THE FIRST CHAIN's ENTRIES (`planSeats`, Johnson/P5T/PlanSeats.lean) BY THE MAKE,
AND THE RADII AS AN ARGUMENT. Definitions with code, and nine theorems.

Why. `memberLists` (Johnson/P5T/MemberLists.lean) takes the shapes, with the radii, from the
sendings' rows: so two tests on the rows must tie the typed oracle messages to `planSeats`
(Johnson/P5T/MemsSame.lean). Here nothing of a shape or a (tree, tenant) is read off the rows.
  `mineAt ps k`: the entries with a sample of sending k.
  `memberListsR n rad ps`: one entry a sending k < n: these entries' shapes, each with the radius
    rad k i (i: its place among them), and their (tree, tenant)s.
  `rad? rows`, `radOf rows`: the rows' radius at (sending, place); `radOf`: 0 WHERE THE ROWS
    HAVE NONE.
  `radIsB rows n rad ps`: A NAMED TEST: at every entry with a sample the rows HAVE a radius, and it
    is rad's. WHOEVER SPENDS A RADIUS OWES IT: without it a radius may be a silent 0 (by one
    reading of the laws on committed words, not held here: "no second code word nearby" is then
    easier to hold, and nothing rejects).
  `shapesR`, `plain_membersR`, `mems_sameR`: the pairs (shape, (tree, tenant)) of the typed oracle
    messages are the entries' with a sample: NO TEST ON THE ROWS: under "every such entry's
    sending's number is below n" alone.
  `planSeats_send_lt`: that holds of `planSeats` at n := the number of the first chain's sendings.
  `seatsFitB_R`, `mem_allSeatsR`, `groups_R`: the two tests of Johnson/P5T/MembersPlain.lean
    likewise.
  `memberListsR_is`: WHERE `membersFault` FINDS NOTHING, at n := the number of the first chain's
    ROWS and rad := `radOf rows`, IT IS `memberLists rows ps`.
  `msAtR Z rad`: the term for the composed meaning's parameter ms, at n := the number of the first
    chain's SENDINGS. `memsSame_atR`: at it the pairs are `planSeats`' own: no premise.

Limits. THAT THE ROWS' NUMBER IS THE SENDINGS' NUMBER IS NOT SHOWN: so `msAtR Z (radOf rows)` is not
shown to be the elder `msAt`: what was evaluated at the elder term carries over only with that (or
with "an entry without members yields no typed oracle message"). Nothing says that a radius is the
right one. Nothing on soundness.

-/
import Johnson.P5T.MembersPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open VerifiableInference.Desc (FileDescription MemberLists seatFaultAt seatsFitB allSeats)
open VerifiableInference.Desc.First (Numbers groupsAreMembers)
open VerifiableInference.Desc.Sound (Mem Sending msOf sendsOf membersOf seatOf)

/-- The entries with a sample of sending k. -/
def mineAt (ps : List PSeat) (k : Nat) : List PSeat := ps.filter fun p => p.send == k && p.smpd

/-- **The lists, shapes and (tree, tenant)s by the make.** -/
def memberListsR (n : Nat) (rad : Nat → Nat → Nat) (ps : List PSeat) : MemberLists :=
  (List.range n).map fun k =>
    ((mineAt ps k).zipIdx.map fun x => (x.1.shape, rad k x.2), (mineAt ps k).map (·.seat))

/-- The radius in the sendings' rows at (sending, place), if any. -/
def rad? (rows : List Johnson.G.SendRow) (k i : Nat) : Option Nat :=
  (((firstRows rows)[k]?).bind (·.sampled[i]?)).map (·.2)

/-- The same; 0 where the rows have none. -/
def radOf (rows : List Johnson.G.SendRow) (k i : Nat) : Nat := (rad? rows k i).getD 0

/-- **At every entry with a sample the rows have a radius, and it is rad's.** -/
def radIsB (rows : List Johnson.G.SendRow) (n : Nat) (rad : Nat → Nat → Nat) (ps : List PSeat) :
    Bool :=
  (List.range n).all fun k => (List.range (mineAt ps k).length).all fun i =>
    rad? rows k i == some (rad k i)

/-- The shapes of an entry of the lists are its entries'. -/
theorem shapesR (mine : List PSeat) (r : Nat → Nat) :
    mine.map (·.shape) = (mine.zipIdx.map fun x => (x.1.shape, r x.2)).map (·.1) := by
  rw [List.map_map]
  have e : ((fun x : OnBytes.OracleShape × Nat => x.1) ∘
      fun x : PSeat × Nat => (x.1.shape, r x.2)) = (fun p : PSeat => p.shape) ∘ Prod.fst := rfl
  rw [e, ← List.map_map, List.zipIdx_map_fst]

theorem plain_membersR (n : Nat) (rad : Nat → Nat → Nat) (ps : List PSeat) :
    (msOf (memberListsR n rad ps)).map (fun x => ((x.1.l.get x.2).1, seatOf x)) =
      (List.range n).flatMap fun k => (mineAt ps k).map fun p => (p.shape, p.seat) := by
  unfold msOf sendsOf memberListsR
  rw [List.map_map]
  generalize List.range n = T
  induction T with
  | nil => rfl
  | cons k T ih =>
    simp only [membersOf, List.map_cons, List.flatMap_cons, List.map_append] at ih ⊢
    rw [ih, List.map_map]
    congr 1
    exact pairs_of_sending _ (mineAt ps k) (shapesR (mineAt ps k) (rad k))

/-- **The two lists of pairs have the same members: no test on the rows.** -/
theorem mems_sameR (n : Nat) (rad : Nat → Nat → Nat) (ps : List PSeat)
    (hn : ∀ p ∈ ps, p.smpd = true → p.send < n) (y : OnBytes.OracleShape × (Nat × Nat)) :
    y ∈ (msOf (memberListsR n rad ps)).map (fun x => ((x.1.l.get x.2).1, seatOf x)) ↔
      y ∈ (ps.filter (·.smpd)).map fun p => (p.shape, p.seat) := by
  rw [plain_membersR]
  unfold mineAt
  simp only [List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨k, _, p, ⟨hp, hq⟩, rfl⟩
    exact ⟨p, ⟨hp, (Bool.and_eq_true_iff.1 hq).2⟩, rfl⟩
  · rintro ⟨p, ⟨hp, hs⟩, rfl⟩
    exact ⟨p.send, hn p hp hs, p, ⟨hp, by simp [hs]⟩, rfl⟩

/-- An entry's sending's number is below the number of the first chain's sendings. -/
theorem planSeats_send_lt (Z : ProofFile.Pub) (dl : List Fmt.DeclaredRound) (p : PSeat)
    (hp : p ∈ planSeats Z dl) : p.send < Z.made.proof.1.sends.length := by
  unfold planSeats at hp
  simp only [List.mem_flatMap] at hp
  obtain ⟨s, hs, hp⟩ := hp
  have hlt : s.2 < Z.made.proof.1.sends.length := by
    have := List.mem_zipIdx hs
    omega
  split at hp
  · simp at hp
  · simp only [List.mem_map] at hp
    obtain ⟨i, _, rfl⟩ := hp
    exact hlt

theorem seatsFitB_R {Xi : Type} (F : FileDescription Xi) (cs : OnBytes.Codes) (n : Nat)
    (rad : Nat → Nat → Nat) (ps : List PSeat) (hn : ∀ p ∈ ps, p.smpd = true → p.send < n) :
    seatsFitB F cs (memberListsR n rad ps) = seatsFitP F cs ps := by
  have e : seatsFitB F cs (memberListsR n rad ps) = (List.range n).all fun k =>
      (mineAt ps k).all fun p => (seatFaultAt F cs "" p.shape p.seat.1 p.seat.2).isNone := by
    unfold seatsFitB memberListsR
    rw [List.all_map]
    refine all_congr_mem _ _ _ fun k _ => ?_
    exact fit_of_sending (fun sh s => (seatFaultAt F cs "" sh s.1 s.2).isNone) _ _
      (shapesR (mineAt ps k) (rad k))
  rw [e, Bool.eq_iff_iff]
  unfold seatsFitP mineAt
  simp only [List.all_eq_true, List.mem_filter, List.mem_range]
  constructor
  · intro h p ⟨hp, hsm⟩
    exact h p.send (hn p hp hsm) p ⟨hp, by simp [hsm]⟩
  · intro h k _ p ⟨hp, hq⟩
    exact h p ⟨hp, (Bool.and_eq_true_iff.1 hq).2⟩

theorem mem_allSeatsR (n : Nat) (rad : Nat → Nat → Nat) (ps : List PSeat)
    (hn : ∀ p ∈ ps, p.smpd = true → p.send < n) (s : Nat × Nat) :
    s ∈ allSeats (memberListsR n rad ps) ↔ s ∈ (ps.filter (·.smpd)).map (·.seat) := by
  unfold allSeats memberListsR
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨x, hx, hs⟩
    obtain ⟨k, _, rfl⟩ := List.mem_map.1 hx
    have hs' : s ∈ (mineAt ps k).map (·.seat) := hs
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs'
    have hp' := List.mem_filter.1 hp
    exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp'.1, (Bool.and_eq_true_iff.1 hp'.2).2⟩, rfl⟩
  · intro hs
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hs
    have hp' := List.mem_filter.1 hp
    have hsm : p.smpd = true := hp'.2
    refine ⟨_, List.mem_map.2 ⟨p.send, List.mem_range.2 (hn p hp'.1 hsm), rfl⟩, ?_⟩
    show p.seat ∈ (mineAt ps p.send).map (·.seat)
    exact List.mem_map.2 ⟨p, List.mem_filter.2 ⟨hp'.1, by simp [hsm]⟩, rfl⟩

theorem groups_R (N : Numbers) (m n : Nat) (rad : Nat → Nat → Nat) (ps : List PSeat)
    (hn : ∀ p ∈ ps, p.smpd = true → p.send < n) :
    groupsAreMembers N m (memberListsR n rad ps) = groupsP N m ps := by
  unfold groupsAreMembers groupsP
  refine all_congr_mem _ _ _ fun s _ => ?_
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
  exact mem_allSeatsR n rad ps hn s

/-- **Where `membersFault` finds nothing it is the elder term.** -/
theorem memberListsR_is (rows : List Johnson.G.SendRow) (ps : List PSeat)
    (ha : membersFault rows ps = []) :
    memberListsR (firstRows rows).length (radOf rows) ps = memberLists rows ps := by
  have hs := shapes_of_noFault rows ps ha
  unfold memberListsR memberLists
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    have hk : k < (firstRows rows).length := by simpa using h1
    have hm : ((firstRows rows)[k], k) ∈ (firstRows rows).zipIdx :=
      List.mem_zipIdx_iff_getElem?.2 (by simp [hk])
    have h0 : (mineAt ps k).map (·.shape) = (firstRows rows)[k].sampled.map (·.1) := hs _ hm
    have hl : (mineAt ps k).length = (firstRows rows)[k].sampled.length := by
      simpa using congrArg List.length h0
    simp only [List.getElem_map, List.getElem_range, List.getElem_zipIdx, Nat.zero_add]
    refine Prod.ext ?_ rfl
    apply List.ext_getElem
    · simpa using hl
    · intro i g1 g2
      have hi : i < (mineAt ps k).length := by simpa using g1
      have hi' : i < (firstRows rows)[k].sampled.length := hl ▸ hi
      have e := congrArg (fun L => L[i]?) h0
      simp [hi, hi'] at e
      simp only [List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
      refine Prod.ext e ?_
      simp [radOf, rad?, hk, hi']

/-- **The term for the composed meaning's parameter ms.** -/
def msAtR (Z : ProofFile.Pub) (rad : Nat → Nat → Nat) : List Mem :=
  msOf (memberListsR Z.made.proof.1.sends.length rad (planSeats Z Z.D.1))

/-- At that term the pairs are `planSeats`' own: no premise. -/
theorem memsSame_atR (Z : ProofFile.Pub) (rad : Nat → Nat → Nat)
    (y : OnBytes.OracleShape × (Nat × Nat)) :
    y ∈ (msAtR Z rad).map (fun x => ((x.1.l.get x.2).1, seatOf x)) ↔
      y ∈ ((planSeats Z Z.D.1).filter (·.smpd)).map fun p => (p.shape, p.seat) :=
  mems_sameR _ rad _ (fun p hp _ => planSeats_send_lt Z Z.D.1 p hp) y

end P5T

#print axioms P5T.shapesR
#print axioms P5T.plain_membersR
#print axioms P5T.mems_sameR
#print axioms P5T.planSeats_send_lt
#print axioms P5T.seatsFitB_R
#print axioms P5T.mem_allSeatsR
#print axioms P5T.groups_R
#print axioms P5T.memberListsR_is
#print axioms P5T.memsSame_atR
