-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/SpotsAtAll.lean:
CODE SWITCHING (the kind
K2) ON THE PROOF FILE's FIRST CHAIN: THE TEST ON THE PUBLIC PART spotsFitB (PAtSeated.lean: the
places of the kind K2 with numbers bear pairwise different groups, and each stands in the dress that
its link asks) ACCEPTS, UNDER THE ONE HEAD (AtMgA, Johnson/P5J/MgAtAll.lean) AND "THE FIRST CHAIN's
CUT IS THE WRITTEN ONE". Definitions, statements and proofs.
WHY IT IS NOT A CALL. The test speaks of every place of the kind in the plan's list, also of one for
which the driver never asks; the laws that lie go from a sub-protocol of the chain to a place.
THE ROAD.
  §1 head_cancel     a place's head comes back from its name where the piece is known.
  §2 entry_own, places_apart, made_sub   K2's lot lays one sub-protocol a place of the kind
                     (pureTable, Johnson/Desc/ProofFile/Lot/K2.lean). Where the table's addresses
                     are apart, each stands at its own place's address, arm by arm of the table's
                     text; so the places' addresses are apart.
  §3 nodup_of_counts, sub_flatMap   two facts on lists.
  §4 k2W, k2W_is, k2W_groups, k2W_cases, standBy, headsW   the 25 written addresses of the kind, by
                     Lean's kernel; k2W_groups_no: a line that shows that the evaluation can fail.
  §5 made_is, prep_is, grps_apart, made_le, rowsOkB, stands_fit, row_of_mem, fitB, fit_core   group
                     and dress of a place with numbers; at most 25 of them; the test's own text at
                     letters, and that it accepts.
  §6 own_count, table_apart   the seat's test on faults (faultsAt = [], the opening's field sound,
                     Johnson/IMR/SeatOpen.lean) says: every lot's sub-protocol stands at a place of
                     the shape (stands_in_shape, Johnson/IMR/LinkSeat.lean), and at
                     most one stands at each, by count. So the table's addresses are apart.
     k2_places_written   in scope the shape's places are the written ones (shape_places there;
                     subs_full, Johnson/LPFK9R/SubsFull.lean): SO EVERY PLACE OF THE KIND STANDS AT
                     ONE OF THE 25 WRITTEN ADDRESSES: THE DRIVER ASKS FOR EACH. No entry test is
                     spent up to here.
     head_at         name and dress by the head (spot_head, Johnson/IMR/K2Seat.lean).
     rows_written, rows_written_no   by the kernel, on the written cut's 25 rows of the kind.
     spots_open, spots_le_open   at an opening of the IOP as written in Lean.
Main names:
  spots_atAll        the head, the written cut ⊢ spotsFitB Zp = true.
  spots_le_atAll     the head alone ⊢ (ProofFile.k2SpotsAt Zp).length ≤ 25.
WHERE THE WRITTEN CUT IS SPENT: to make the 25 names closed; a place's name is the name of the flat
list's sub-protocol at its address (k2_name_at, H2K12/K2NameAt.lean).
Limits. (1) THE TEST ACCEPTS AN EMPTY OR SHORT LIST: that the list has 25 members is not shown
here; at most 25 is. (2) THE WRITTEN CUT RESTS ON PRINTS OF LEAN's EVALUATOR
(Johnson/Desc/First/CutWritten.lean, its own Limits); that it is the chain's cut at any public files
is no theorem. (3) A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY
AtFullSide/Top/). (4) At the concrete second hash function alone; the full
size alone. (5) It imports Johnson/Top/H0/Opts/PlannerRequestHas25Links.lean
for "25 links in scope". No soundness statement. Nothing on hiding.

-/
import Johnson.Desc.ProofFile.Lot.K2
import Johnson.Desc.Ok.PlanWritten.CutTest
import Johnson.Desc.Sound.AtDriver
import Johnson.Top.H0.Tw.K2C.GroupAtNums
import Johnson.Top.H0.K2Caller.PAtSeated
import Johnson.Top.H0.Opts.PlannerRequestHas25Links
import Johnson.IMR.K2Seat
import Johnson.IMR.LinkSeat
import Johnson.IMR.PureJoin
import Johnson.LPFK9R.SubsFull
import Johnson.P5J.MgAtAll
import Johnson.Loose.H2K12.K2NameAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 At)
open ProofFile (Spot Ground Pub)

/-! ## 1 A place's head comes back from its name -/

/-- Where the count is known, the head comes back: what stands behind it cancels on the right. -/
theorem head_cancel {h h₀ : String} {n : Nat} (e : s!"{h}:{n}" = s!"{h₀}:{n}") : h = h₀ := by
  have e' : (h ++ ":" ++ toString n).toList = (h₀ ++ ":" ++ toString n).toList := congrArg _ e
  simp only [String.toList_append] at e'
  exact String.toList_injective (List.append_cancel_right (List.append_cancel_right e'))

/-! ## 2 K2's lot's table: every block stands at its own place's address -/

/-- K2's lot's block at one place of the kind: the text of pureTable
(Johnson/Desc/ProofFile/Lot/K2.lean). -/
def entryK2 (q : Ground → Nat → Option (Option (Block S Unit))) (Z : Pub) (G : Ground)
    (sp : Spot) : Block S Unit :=
  match (P1K2.pureSpots Z G).find? fun x => x.1.name == sp.name with
  | none => P1K2.pureMute sp "N0: the place's numbers cannot be made of the plan's public records"
  | some x => (P1K2.pureAt q G x).getD (P1K2.pureMute sp "N0: the place's letters cannot be made")

theorem table_is (q : Ground → Nat → Option (Option (Block S Unit))) (Z : Pub) (G : Ground) :
    P1K2.pureTable q Z G = (P1K2.purePlaces Z).map (entryK2 q Z G) := rfl

/-- What pureAt makes bears the place's address. -/
theorem pureAt_place {q : Ground → Nat → Option (Option (Block S Unit))} {G : Ground}
    {x : Spot × P2} {b : Block S Unit} (h : P1K2.pureAt q G x = some b) : b.place = x.1.place := by
  unfold P1K2.pureAt at h
  dsimp only at h
  split at h
  · obtain rfl := Option.some.inj h
    rfl
  · obtain ⟨P, _, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  · obtain ⟨o, _, rfl⟩ := Option.map_eq_some_iff.1 h
    split <;> rfl

/-- A place with numbers is a place of the kind. -/
theorem made_mem {Z : Pub} {G : Ground} {y : Spot × P2} (hy : y ∈ P1K2.pureSpots Z G) :
    y.1 ∈ P1K2.purePlaces Z := by
  unfold P1K2.pureSpots at hy
  unfold P1K2.purePlaces
  cases hs : ProofFile.spotsOf Z.cuts with
  | none => rw [hs] at hy; cases hy
  | some sps =>
    rw [hs] at hy
    simp only [Option.map_some, Option.getD_some] at hy ⊢
    unfold P1K2.p2All at hy
    split at hy
    · cases hy
    · obtain ⟨sp, hsp, e⟩ := List.mem_filterMap.1 hy
      obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 e
      exact hsp

theorem entry_some {q : Ground → Nat → Option (Option (Block S Unit))} {Z : Pub} {G : Ground}
    {sp : Spot} {x : Spot × P2}
    (hf : ((P1K2.pureSpots Z G).find? fun x => x.1.name == sp.name) = some x) :
    entryK2 q Z G sp =
      (P1K2.pureAt q G x).getD (P1K2.pureMute sp "N0: the place's letters cannot be made") := by
  unfold entryK2
  rw [hf]

/-- The address of a block of the table is a place's of the kind. -/
theorem entry_kind {q : Ground → Nat → Option (Option (Block S Unit))} {Z : Pub} {G : Ground}
    {sp : Spot} (hsp : sp ∈ P1K2.purePlaces Z) :
    (entryK2 q Z G sp).place.kind = KindName.K2 := by
  have hk : ∀ p ∈ P1K2.purePlaces Z, p.place.kind = KindName.K2 := fun p hp => by
    unfold P1K2.purePlaces at hp
    simpa using (List.mem_filter.1 hp).2
  cases hf : (P1K2.pureSpots Z G).find? fun x => x.1.name == sp.name with
  | none =>
    unfold entryK2
    rw [hf]
    exact hk sp hsp
  | some x =>
    rw [entry_some hf]
    cases hp : P1K2.pureAt q G x with
    | none => exact hk sp hsp
    | some b =>
      show b.place.kind = _
      rw [pureAt_place hp]
      exact hk _ (made_mem (List.mem_of_find?_eq_some hf))

/-- **Where the table's addresses are apart, every block of the table stands at its own place's
address.** In the arm in which the block is made, off the first place x with numbers of that name:
that place's own block is the same block, so the two places are one. In the two arms of a mute: the
mute is laid off the place itself. -/
theorem entry_own {q : Ground → Nat → Option (Option (Block S Unit))} {Z : Pub} {G : Ground}
    (hN : ((P1K2.pureTable q Z G).map (·.place)).Nodup) :
    ∀ sp ∈ P1K2.purePlaces Z, (entryK2 q Z G sp).place = sp.place := by
  rw [table_is, List.map_map] at hN
  intro sp hsp
  cases hf : (P1K2.pureSpots Z G).find? fun x => x.1.name == sp.name with
  | none =>
    unfold entryK2
    rw [hf]
    rfl
  | some x =>
    rw [entry_some hf]
    cases hp : P1K2.pureAt q G x with
    | none => rfl
    | some b =>
      have hx : x.1 ∈ P1K2.purePlaces Z := made_mem (List.mem_of_find?_eq_some hf)
      have hn : x.1.name = sp.name := by simpa using List.find?_some hf
      have e1 : (entryK2 q Z G sp).place = b.place := by
        rw [entry_some hf, hp]
        rfl
      have hf' : ((P1K2.pureSpots Z G).find? fun y => y.1.name == x.1.name) = some x := by
        rw [hn]
        exact hf
      have e2 : (entryK2 q Z G x.1).place = b.place := by
        rw [entry_some hf', hp]
        rfl
      have : sp = x.1 := List.inj_on_of_nodup_map hN hsp hx (e1.trans e2.symm)
      show b.place = sp.place
      rw [this]
      exact pureAt_place hp

/-- So the places' addresses are apart. -/
theorem places_apart {q : Ground → Nat → Option (Option (Block S Unit))} {Z : Pub} {G : Ground}
    (hN : ((P1K2.pureTable q Z G).map (·.place)).Nodup) :
    ((P1K2.purePlaces Z).map (·.place)).Nodup := by
  have h := hN
  rw [table_is, List.map_map] at h
  have e : (P1K2.purePlaces Z).map ((·.place) ∘ entryK2 q Z G) =
      (P1K2.purePlaces Z).map (·.place) :=
    List.map_congr_left fun sp hsp => entry_own hN sp hsp
  rwa [e] at h

/-- The places with numbers, without the numbers, are a sublist of the places of the kind. -/
theorem made_sub (Z : Pub) (G : Ground) :
    ((P1K2.pureSpots Z G).map (·.1)).Sublist (P1K2.purePlaces Z) := by
  unfold P1K2.pureSpots P1K2.purePlaces
  cases hs : ProofFile.spotsOf Z.cuts with
  | none => simp
  | some sps =>
    simp only [Option.map_some, Option.getD_some]
    unfold P1K2.p2All
    split
    · simp
    · rename_i P _
      generalize (sps.filter fun sp => sp.place.kind == KindName.K2) = l
      induction l with
      | nil => simp
      | cons a t ih =>
        rw [List.filterMap_cons]
        cases hp : (P1K2.p2With P Z a).map fun p => (a, p) with
        | none => exact ih.cons a
        | some y =>
          obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 hp
          exact ih.cons₂ a

/-! ## 3 Two facts on lists -/

/-- A sublist of a list in which at most one member bears each of the listed marks, all of whose own
members bear listed marks, bears no mark twice. -/
theorem nodup_of_counts {β : Type} (pl : β → Place) {own T : List β} (hsub : T.Sublist own)
    (sh : List Place) (hin : ∀ x ∈ T, pl x ∈ sh)
    (hcnt : ∀ a ∈ sh, (own.filter fun o => pl o == a).length ≤ 1) : (T.map pl).Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro a
  by_cases ha : a ∈ T.map pl
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
    have h1 := hcnt _ (hin x hx)
    have h2 : (T.filter fun o => pl o == pl x).length ≤ (own.filter fun o => pl o == pl x).length :=
      (hsub.filter _).length_le
    have h3 : List.count (pl x) (T.map pl) = (T.filter fun o => pl o == pl x).length := by
      rw [List.count, List.countP_map, List.countP_eq_length_filter]
      rfl
    omega
  · rw [List.count_eq_zero_of_not_mem ha]
    omega

theorem sub_flatMap.{u, v} {α : Type u} {β : Type v} (f : α → List β) :
    ∀ {l : List α} {a : α}, a ∈ l →
    (f a).Sublist (l.flatMap f)
  | b :: t, a, h => by
    rw [List.flatMap_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact List.sublist_append_left _ _
    · exact (sub_flatMap f h).trans (List.sublist_append_right _ _)

/-! ## 4 The written addresses and names of the kind K2 -/

/-- The 25 written addresses of the kind K2. -/
def k2W : List Place :=
  (List.range' 1 23).map (fun l => (⟨1, some l, 1, .K2⟩ : Place)) ++
    [⟨1, some 24, 2, .K2⟩, ⟨1, none, 1, .K2⟩]

set_option maxRecDepth 1000000 in
/-- By the kernel: they are the addresses of that kind in the driver's table at the written list of
the segments' sorts, at either value of its second letter. -/
theorem k2W_is : ∀ s : Bool, ((VerifiableInference.Desc.First.flatPlacesOf
    VerifiableInference.Desc.Sound.linksFull s).filter fun a => a.kind == .K2) = k2W := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- By the kernel: they bear 25 groups. -/
theorem k2W_groups : (k2W.map fun a => a.link.getD 25).Nodup := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The line can fail: with the finish counted as group 24 two addresses bear one group. -/
theorem k2W_groups_no : ¬ (k2W.map fun a => a.link.getD 24).Nodup := by decide +kernel

/-- Where a place of the kind stands, by its head (P1K2.standsOf's own three lines). -/
def standBy (h : String) : At := if h == "F" then .finish else if h == "H" then .head else .link

/-- The heads of the 25 written names. -/
def headsW : List String :=
  ["A0", "G1", "A1", "G2", "A2", "G3", "A3", "G4", "A4", "G5", "A5", "G6", "A6", "G7", "A7", "G8",
    "A8", "G9", "A9", "G10", "A10", "G11", "A11", "H", "F"]

/-! ## 5 The places with numbers: group and dress -/

/-- What a place with numbers is: its group is the numbers'; its dress goes by the place. -/
theorem made_is {Z : Pub} {G : Ground} {y : Spot × P2} (hy : y ∈ P1K2.pureSpots Z G) :
    ∃ Q n, P1K2.prepOf Z G = some Q ∧ P1K2.numsAt Q y.1.place.link = some n ∧ y.2.grp = n.grp ∧
      y.2.stands = P1K2.standsOf y.1 := by
  unfold P1K2.pureSpots at hy
  cases hs : ProofFile.spotsOf Z.cuts with
  | none => rw [hs] at hy; cases hy
  | some sps =>
    rw [hs] at hy
    have hm : y ∈ P1K2.p2All Z G sps := hy
    unfold P1K2.p2All at hm
    split at hm
    · cases hm
    · rename_i Q hQ
      obtain ⟨sp', -, e⟩ := List.mem_filterMap.1 hm
      obtain ⟨p, hpw, rfl⟩ := Option.map_eq_some_iff.1 e
      unfold P1K2.p2With at hpw
      obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.1 hpw
      exact ⟨Q, n, hQ, hn, rfl, rfl⟩

/-- What is made once holds the planner's own sizes, and their request's shape is the first state's
frame's. -/
theorem prep_is {Z : Pub} {G : Ground} {Q : P1K2.Prep} (h : P1K2.prepOf Z G = some Q) :
    Q.z = Z.p.chains.made.sized.proof ∧ Z.s₀.check.frame.shape = Q.z.request := by
  unfold P1K2.prepOf P1K2.prepareAt at h
  dsimp only at h
  split at h
  · cases h
  · rename_i ht
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, _, trees, _, rfl⟩ := h
    refine ⟨rfl, ?_⟩
    have ht' : P1K2.tied Z.p.chains.made.sized.proof G.first Z.s₀.st.codes
        Z.s₀.check.frame.shape Z.P.samples = true := by simpa using ht
    unfold P1K2.tied at ht'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
    exact ht'.1.2

/-- **The groups are apart.** -/
theorem grps_apart {Z : Pub} {G : Ground} {Q : P1K2.Prep} (hQ : P1K2.prepOf Z G = some Q)
    (h25 : Q.z.request.link.length = 25) (hA : ((P1K2.purePlaces Z).map (·.place)).Nodup)
    (hW : ∀ sp ∈ P1K2.purePlaces Z, sp.place ∈ k2W) :
    ((P1K2.pureSpots Z G).map (·.2.grp)).Nodup := by
  have e : (P1K2.pureSpots Z G).map (·.2.grp) =
      ((P1K2.pureSpots Z G).map (·.1)).map fun sp => sp.place.link.getD 25 := by
    rw [List.map_map]
    refine List.map_congr_left fun y hy => ?_
    obtain ⟨Q', n, hQ', hn, hg, _⟩ := made_is hy
    obtain rfl : Q' = Q := Option.some.inj (hQ'.symm.trans hQ)
    show y.2.grp = y.1.place.link.getD 25
    rw [hg, P1K2.numsAt_grp hn, h25]
  rw [e]
  have h1 : ((P1K2.purePlaces Z).map fun sp => sp.place.link.getD 25).Nodup := by
    have e2 : ((P1K2.purePlaces Z).map fun sp => sp.place.link.getD 25) =
        ((P1K2.purePlaces Z).map (·.place)).map fun a => a.link.getD 25 := by
      rw [List.map_map]
      rfl
    rw [e2]
    refine List.Nodup.map_on (fun a ha b hb hab => ?_) hA
    obtain ⟨sa, hsa, rfl⟩ := List.mem_map.1 ha
    obtain ⟨sb, hsb, rfl⟩ := List.mem_map.1 hb
    exact List.inj_on_of_nodup_map k2W_groups (hW sa hsa) (hW sb hsb) hab
  exact ((made_sub Z G).map _).nodup h1

/-- The test on the written cut's rows of the kind K2: each name is ‹a listed head›:‹the address's
piece›, and the dress by that head is the dress that the address's link asks at 25 links. -/
def rowsOkB (dress : Nat → Option Nat → At) : Bool :=
  VerifiableInference.PlanWritten.cutFirstFull.all fun r =>
    r.2.1.kind != .K2 || headsW.any fun h₀ =>
      r.1 == s!"{h₀}:{r.2.1.piece}" && decide (standBy h₀ = dress 25 r.2.1.link)

/-- **The dress is the one that the link asks**, where a place's name is its head and piece, its
dress goes by that head, and name and address stand in a row of the written cut. -/
theorem stands_fit {Z : Pub} {G : Ground} {dress : Nat → Option Nat → At}
    (hrows : rowsOkB dress = true)
    (hhead : ∀ sp ∈ P1K2.purePlaces Z, ∃ hd : String, sp.name = s!"{hd}:{sp.place.piece}" ∧
      P1K2.standsOf sp = standBy hd)
    (hrow : ∀ sp ∈ P1K2.purePlaces Z, ∃ r ∈ VerifiableInference.PlanWritten.cutFirstFull,
      r.1 = sp.name ∧ r.2.1 = sp.place) :
    ∀ y ∈ P1K2.pureSpots Z G, y.2.stands = dress 25 y.1.place.link := by
  intro y hy
  have hsp := made_mem hy
  obtain ⟨_, _, _, _, _, hst⟩ := made_is hy
  obtain ⟨hd, hn, hs⟩ := hhead _ hsp
  obtain ⟨r, hr, e1, e2⟩ := hrow _ hsp
  have hk : y.1.place.kind = KindName.K2 := by
    unfold P1K2.purePlaces at hsp
    simpa using (List.mem_filter.1 hsp).2
  have h1 := List.all_eq_true.1 hrows r hr
  rw [e2, hk] at h1
  simp only [bne_self_eq_false, Bool.false_or, List.any_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h1
  obtain ⟨h₀, _, en, ed⟩ := h1
  have : hd = h₀ := head_cancel (hn.symm.trans (e1.symm.trans en))
  rw [hst, hs, this, ed]

/-- The 25 written addresses, in three families. -/
theorem k2W_cases {a : Place} (h : a ∈ k2W) :
    (∃ l, 1 ≤ l ∧ l < 24 ∧ a = ⟨1, some l, 1, .K2⟩) ∨ a = ⟨1, some 24, 2, .K2⟩ ∨
      a = ⟨1, none, 1, .K2⟩ := by
  unfold k2W at h
  rcases List.mem_append.1 h with h | h
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 h
    have := List.mem_range'_1.1 hl
    exact Or.inl ⟨l, this.1, by omega, rfl⟩
  · rcases List.mem_cons.1 h with rfl | h
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (List.mem_singleton.1 h))

/-- **There are at most 25 places with numbers**, where the places of the kind stand apart at the
written addresses. -/
theorem made_le {Z : Pub} {G : Ground} (hA : ((P1K2.purePlaces Z).map (·.place)).Nodup)
    (hW : ∀ sp ∈ P1K2.purePlaces Z, sp.place ∈ k2W) : (P1K2.pureSpots Z G).length ≤ 25 := by
  have h1 : ((P1K2.purePlaces Z).map (·.place)).length ≤ k2W.length :=
    (hA.subperm fun a ha => by
      obtain ⟨sp, hsp, rfl⟩ := List.mem_map.1 ha
      exact hW sp hsp).length_le
  have h2 := (made_sub Z G).length_le
  have h3 : k2W.length = 25 := by decide
  simp only [List.length_map] at h1 h2
  omega

/-- A sub-protocol's name and address stand in a row of the written cut, where the list's cut is the
written one. -/
theorem row_of_mem {σ C : Type} {bs : List (Block σ C)}
    (hc : VerifiableInference.PlanWritten.cutOf bs =
      VerifiableInference.PlanWritten.cutFirstFull) {b : Block σ C} (hb : b ∈ bs) :
    ∃ r ∈ VerifiableInference.PlanWritten.cutFirstFull, r.1 = b.name ∧ r.2.1 = b.place := by
  refine ⟨(b.name, b.place, b.rounds.length, b.oracles.length,
    VerifiableInference.PlanWritten.toldRounds b, b.before), ?_, rfl, rfl⟩
  rw [← hc]
  unfold VerifiableInference.PlanWritten.cutOf
  exact List.mem_map.2 ⟨b, hb, rfl⟩

/-- The text of spotsFitB (PAtSeated.lean), at a ground and a dress as letters. -/
def fitB (Z : Pub) (G : Ground) (dress : Nat → Option Nat → At) : Bool :=
  decide (((P1K2.pureSpots Z G).map (·.2.grp)).Nodup) &&
    (P1K2.pureSpots Z G).all fun y =>
      decide (y.2.stands = dress Z.s₀.check.frame.shape.link.length y.1.place.link)

/-- **The test accepts**, from what §§ 2, 4 and 5 ask. -/
theorem fit_core {Z : Pub} {G : Ground} {dress : Nat → Option Nat → At}
    (h25 : Z.p.chains.made.sized.proof.request.link.length = 25)
    (hA : ((P1K2.purePlaces Z).map (·.place)).Nodup)
    (hW : ∀ sp ∈ P1K2.purePlaces Z, sp.place ∈ k2W) (hrows : rowsOkB dress = true)
    (hhead : ∀ sp ∈ P1K2.purePlaces Z, ∃ hd : String, sp.name = s!"{hd}:{sp.place.piece}" ∧
      P1K2.standsOf sp = standBy hd)
    (hrow : ∀ sp ∈ P1K2.purePlaces Z, ∃ r ∈ VerifiableInference.PlanWritten.cutFirstFull,
      r.1 = sp.name ∧ r.2.1 = sp.place) : fitB Z G dress = true := by
  unfold fitB
  cases hQ : P1K2.prepOf Z G with
  | none =>
    have e : P1K2.pureSpots Z G = [] := by
      refine List.eq_nil_iff_forall_not_mem.2 fun y hy => ?_
      obtain ⟨Q, _, hQ', _⟩ := made_is hy
      rw [hQ] at hQ'
      cases hQ'
    rw [e]
    simp
  | some Q =>
    obtain ⟨ez, es⟩ := prep_is hQ
    have hq : Q.z.request.link.length = 25 := by
      rw [ez]
      exact h25
    rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨grps_apart hQ hq hA hW, fun y hy => decide_eq_true ?_⟩
    rw [es, hq]
    exact stands_fit hrows hhead hrow y hy

/-! ## 6 Off the seat's test on faults: the table's addresses are apart and stand in the shape -/

/-- At most one of all lots' blocks stands at a place of the shape: the count that the seat's test
on faults asks (its last clause in faultsOf, Johnson/Desc/ProofFile/Frames1.lean). -/
theorem own_count {T : ProofFile.PureSeat} {Bq : ProofFile.PureBase} (hf : ProofFile.faultsAt T Bq = [])
    {e : String × Place} (he : e ∈ Bq.shape) :
    ((Bq.all.flatMap fun x => x.2).filter fun o => o.place == e.2).length ≤ 1 := by
  simp only [ProofFile.faultsAt, ProofFile.faultsOf, List.append_eq_nil_iff, List.map_eq_nil_iff] at hf
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, h3⟩, -⟩, -⟩, -⟩, -⟩ := hf
  have h4 := List.filter_eq_nil_iff.1 h3 e he
  simpa using h4

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **The addresses of K2's lot's table are apart, and each is a place of the shape.** At every o;
no premise on scope. -/
theorem table_apart (O : IM.Open o pol lay KL F Z Bs base c A B) :
    ((P1K2.pureTable (fun _ _ => some none) Z Bs.G₀).map (·.place)).Nodup ∧
      ∀ x ∈ P1K2.pureTable (fun _ _ => some none) Z Bs.G₀, x.place ∈ Bs.shape.map (·.2) := by
  obtain ⟨-, -, -, hall⟩ := IM.base_made O.made
  have hL : ProofFile.k2Pure Z ∈ (ProofFile.pureSeat o Z).lots := by
    show ProofFile.k2Pure Z ∈ ProofFile.onlineFirstChainBlockTables Z
    unfold ProofFile.onlineFirstChainBlockTables
    simp
  have hsub : ((P1K2.pureTable (fun _ _ => some none) Z Bs.G₀).map
      fun b => (b.retype : Block S ProofFile.Cl)).Sublist (Bs.all.flatMap fun x => x.2) := by
    have h1 : ((P1K2.pureTable (fun _ _ => some none) Z Bs.G₀).map
        fun b => (b.retype : Block S ProofFile.Cl)).Sublist ((ProofFile.k2Pure Z).blocks Bs.G₀) := by
      show List.Sublist _ (ProofFile.asCl (ProofFile.k2Pure Z).own Bs.G₀ ++ (ProofFile.k2Pure Z).hearC Bs.G₀)
      exact List.sublist_append_left _ _
    have h2 : (ProofFile.k2Pure Z, (ProofFile.k2Pure Z).blocks Bs.G₀) ∈ Bs.all := by
      rw [hall]
      exact List.mem_map.2 ⟨_, hL, rfl⟩
    exact h1.trans (sub_flatMap (fun x : ProofFile.Lot × List (Block S ProofFile.Cl) => x.2) h2)
  have hin : ∀ x ∈ (P1K2.pureTable (fun _ _ => some none) Z Bs.G₀).map
      fun b => (b.retype : Block S ProofFile.Cl), x.place ∈ Bs.shape.map (·.2) := by
    intro x hx
    have hx' := hsub.subset hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    rw [table_is] at hy
    obtain ⟨sp, hsp, rfl⟩ := List.mem_map.1 hy
    have hk : ((entryK2 (fun _ _ => some none) Z Bs.G₀ sp).retype : Block S ProofFile.Cl).place.kind ≠
        KindName.frame := by
      show (entryK2 (fun _ _ => some none) Z Bs.G₀ sp).place.kind ≠ KindName.frame
      rw [entry_kind hsp]
      decide
    obtain ⟨e, he, ee⟩ := IM.stands_in_shape O.sound hx' hk
    exact List.mem_map.2 ⟨e, he, ee⟩
  have hcnt : ∀ a ∈ Bs.shape.map (·.2),
      ((Bs.all.flatMap fun x => x.2).filter fun o => o.place == a).length ≤ 1 := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 ha
    exact own_count O.sound he
  have hN := nodup_of_counts (fun b : Block S ProofFile.Cl => b.place) hsub _ hin hcnt
  rw [List.map_map] at hN
  exact ⟨hN, fun x hx => hin _ (List.mem_map_of_mem hx)⟩

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {F : FileDescription ProofFile.Inst} {Z : Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **In scope: the places of the kind K2 stand apart, each at one of the 25 written addresses**:
none is a place that the driver does not ask for. -/
theorem k2_places_written (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) :
    ((P1K2.purePlaces Z).map (·.place)).Nodup ∧ ∀ sp ∈ P1K2.purePlaces Z, sp.place ∈ k2W := by
  obtain ⟨hN, hin⟩ := table_apart O
  refine ⟨places_apart hN, fun sp hsp => ?_⟩
  have h1 : (entryK2 (fun _ _ => some none) Z Bs.G₀ sp).place ∈ Bs.shape.map (·.2) :=
    hin _ (by rw [table_is]; exact List.mem_map_of_mem hsp)
  rw [entry_own hN sp hsp] at h1
  obtain ⟨s, hs⟩ := IM.shape_places (IM.base_made O.made).2.1
  rw [hs, LPFK9.subs_full hS hR O] at h1
  rw [← k2W_is s]
  refine List.mem_filter.2 ⟨h1, ?_⟩
  unfold P1K2.purePlaces at hsp
  exact (List.mem_filter.1 hsp).2

/-- A place of the kind K2: its name is its head and piece; its dress goes by that head
(IM.spot_head, Johnson/IMR/K2Seat.lean). -/
theorem head_at (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) :
    ∀ sp ∈ P1K2.purePlaces Z, ∃ hd : String, sp.name = s!"{hd}:{sp.place.piece}" ∧
      P1K2.standsOf sp = standBy hd := by
  intro sp hsp
  have hs := (IM.base_made O.made).1
  unfold P1K2.purePlaces at hsp
  rw [hs] at hsp
  obtain ⟨hm, hk⟩ := List.mem_filter.1 hsp
  have hk' : sp.place.kind = KindName.K2 := by simpa using hk
  unfold ProofFile.spotsOf at hs
  obtain ⟨hd, m, ⟨hn, hp, -, est⟩ | ⟨h9, -⟩⟩ := IM.spot_head _ _ _ _ _ hs sp hm
  · rw [hk'] at hp
    have hp' : sp.place.piece = m := hp
    exact ⟨hd, by rw [hp']; exact hn, est⟩
  · rw [hk'] at h9
    cases h9

set_option maxRecDepth 1000000 in
/-- **By the kernel: the written cut's 25 rows of the kind K2 pass the test** at the dress that a
link asks (K2Caller.dressOf, Johnson/Top/H0/K2Caller/PAtSeated.lean). -/
theorem rows_written : rowsOkB VerifiableInference.Desc.First.K2Caller.dressOf = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The line can fail: were every link to ask the dress «link», it rejects. -/
theorem rows_written_no : rowsOkB (fun _ _ => .link) = false := by decide +kernel

/-- **The test on the places of the kind K2 accepts**, at an opening of the IOP as written in Lean,
in scope, where the first chain's cut is the written one. -/
theorem spots_open (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B)
    (hc : VerifiableInference.PlanWritten.cutOf c.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull) :
    VerifiableInference.Desc.First.K2Caller.spotsFitB Z = true := by
  obtain ⟨hA, hW⟩ := k2_places_written hS hR O
  have hk2 : ProofFile.k2SpotsAt Z = P1K2.pureSpots Z Bs.G₀ := by
    unfold ProofFile.k2SpotsAt
    rw [O.blank]
    rfl
  have hrow : ∀ sp ∈ P1K2.purePlaces Z, ∃ r ∈ VerifiableInference.PlanWritten.cutFirstFull,
      r.1 = sp.name ∧ r.2.1 = sp.place := by
    intro sp hsp
    obtain ⟨b, hb, e1, e2⟩ := k2_name_at hS hR O hA hsp (k2W_cases (hW sp hsp))
    obtain ⟨r, hr, r1, r2⟩ := row_of_mem hc hb
    exact ⟨r, hr, r1.trans e2, r2.trans e1⟩
  have h := fit_core (G := Bs.G₀) (VerifiableInference.Desc.First.K2Caller.pub_links hS O.pub) hA hW
    rows_written (head_at O) hrow
  unfold fitB at h
  unfold VerifiableInference.Desc.First.K2Caller.spotsFitB
  rw [hk2]
  exact h

/-- **At most 25 places of the kind have numbers**: in scope, at an opening; no entry test. -/
theorem spots_le_open (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) :
    (ProofFile.k2SpotsAt Z).length ≤ 25 := by
  obtain ⟨hA, hW⟩ := k2_places_written hS hR O
  have hk2 : ProofFile.k2SpotsAt Z = P1K2.pureSpots Z Bs.G₀ := by
    unfold ProofFile.k2SpotsAt
    rw [O.blank]
    rfl
  rw [hk2]
  exact made_le hA hW

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The test on the places of the kind K2 accepts: under the head and the written cut.** -/
theorem spots_atAll (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder =
      VerifiableInference.PlanWritten.cutFirstFull) :
    VerifiableInference.Desc.First.K2Caller.spotsFitB Zp = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact spots_open h.scope h.reads O hc

/-- **At most 25 places of the kind have numbers: under the head alone.** -/
theorem spots_le_atAll (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (ProofFile.k2SpotsAt Zp).length ≤ 25 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact spots_le_open h.scope h.reads O

end

end H2K12

#print axioms H2K12.head_cancel
#print axioms H2K12.table_is
#print axioms H2K12.pureAt_place
#print axioms H2K12.made_mem
#print axioms H2K12.entry_some
#print axioms H2K12.entry_kind
#print axioms H2K12.entry_own
#print axioms H2K12.places_apart
#print axioms H2K12.made_sub
#print axioms H2K12.nodup_of_counts
#print axioms H2K12.sub_flatMap
#print axioms H2K12.k2W_is
#print axioms H2K12.k2W_groups
#print axioms H2K12.k2W_groups_no
#print axioms H2K12.made_is
#print axioms H2K12.prep_is
#print axioms H2K12.grps_apart
#print axioms H2K12.stands_fit
#print axioms H2K12.k2W_cases
#print axioms H2K12.made_le
#print axioms H2K12.row_of_mem
#print axioms H2K12.fit_core
#print axioms H2K12.own_count
#print axioms H2K12.table_apart
#print axioms H2K12.k2_places_written
#print axioms H2K12.head_at
#print axioms H2K12.rows_written
#print axioms H2K12.rows_written_no
#print axioms H2K12.spots_open
#print axioms H2K12.spots_le_open
#print axioms H2K12.spots_atAll
#print axioms H2K12.spots_le_atAll
