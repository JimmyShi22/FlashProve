-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MergeEndsAt.lean: CONDITIONAL. THE NUMBER BEHIND THE INDEX
SIDE's BASE: IN FRONT OF THE LAYERS' OWN ROUNDS (kind K4) OF GROUP g THE BOOK's MAKER COUNTS JUST g
END VALUES OF MERGES, AT AN OPENED DESCRIPTION IN THE GOALS' SCOPE.

What is here. PUBLIC DATA ALONE: places, names of rounds, counts. Law/W/LockAtMember.lean's top has
the index side's name at idx.base.e + `mergeEndsOf` (`mergesByName` c.blocksInOrder).ends (the parts in
front) (Honest/BookMergeStretch.lean; Honest/BookWhole.lean). Here that second summand is worked
out. The parts in front are the parts of a list of sub-protocols in front, and the summand is a sum,
one term a sub-protocol. A sub-protocol whose kind is neither K4 nor K11 gives 0: a listed address
bears a listed kind. K4's own gives 1 (Law/W/MergesByName.lean). Which sub-protocols stand in front
hangs on their places alone, and in the goals' scope the places are the library's closed term
`IM.placesW` (Johnson/IMR/WrittenList.lean: `flatPlacesOf` at 25 written sorts of links: 358 places
when it is evaluated; `IM.places_scope`, Johnson/IMR/PlacesScope.lean). Definitions, statements and
proofs.

  `snd_lt_zipIdx`, `mem_of_takeWhile`, `mergeEnds_flatMap`, `mergeEnds_none`: small tools.
  `blocksInFront`, `front_parts`, `front_sub`: the sub-protocols in front, in the maker's order;
      the parts in front are theirs; each is one of the list.
  `placesInFront`, `front_places`: the same cut on a list of places; the sub-protocols' places
      are that cut of the places.
  `mergeEnds_other`: a sub-protocol of another kind than K4 and K11 gives 0. No hypothesis on
      the list.
  `mergeEnds_k4`: K4's sub-protocol gives 1.
  `cntK4`, `frontCount`, `frontNoK11`, `k4Places`: THREE EVALUATIONS ON THAT TERM: for each g
      below 12: of the places in front of K4's place of group g just g are of the kind K4; none of
      them is of the kind K11; and every place of the kind K4 is K4's place of a group below 12.
      `frontCount_no`, `noK11_no`, `k4Places_no`: a wrong count, the whole list, and eleven groups
      are refused.
  `term_at`: **the step that bears the count**: in the goals' scope a sub-protocol of the first
      chain of another kind than K11 gives 1 if its kind is K4, else 0.
  `k4_mergeEnds_at_group`: **the number is g.** Four hypotheses, all the scope's: no book, no
      public data of K4's.
  `k4Names_at_record_gk`: **Law/W/LockAtMember.lean's top with idx.base.e + g.**

Not shown here. THE SIX EVALUATIONS ARE BY LEAN's KERNEL (`decide +kernel`), REPLAYED BY NO
INDEPENDENT CHECKER. `frontNoK11` IS A COUNT ON THE PLACES IN FRONT OF K4's TWELVE, NO LAW ON THE
KIND K11. hS, hR and O: SO THE FULL SIZE ALONE, AND THE FORMAT's EARLIER HASH ALONE
(`OnBytes.secondHashFunction`). That the three can hold together: they are what the library's head `P5J.AtMgA`
holds in its fields scope, reads and laid.opened (Johnson/P5J/AtMg.lean;
Johnson/P5J/LaidOpens.lean), and the side library AtFullSide proves, with no hypothesis, that this
head has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth); no file here lays that
out. THAT `mergesByName` IS THE FORMAT's LIST OF MERGES IS NOT SPOKEN OF. NOT IN THIS FILE: THE JOIN
WITH THE LEDGER's COUNT `k4IndexTakes` (Lot/IndexNum.lean). Side by side: here, under hS, hR, O and
g < 12: the maker's count = g. In Law/W/IndexApart.lean, `k4IndexTakes_is`, under `AtMgA
OnBytes.secondHashFunction Z D r Zp Np cF xh` and g < 12: `k4IndexTakes Zp g` = g. Law/W/LockAtHead.lean lays
the two together under that head. All that Law/W/LockAtMember.lean's head names as left stays left.
No example of the hypotheses together has been through Lean.
No property is claimed.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one:
its imports reach modules under Johnson/Goal/.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LockAtMember
import Johnson.IMR.PlacesScope
import Johnson.IMR.BorderW

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The default instance `Inst.Model.Scl.ref` (a table of scales) is switched off in this file, so
that no statement picks a table of scales silently. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Desc.First.K4 (entries k0)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)

/-! ## 1 Small tools -/

/-- A member of a numbered list bears a number below the list's end. -/
theorem snd_lt_zipIdx {α : Type} : ∀ (l : List α) (k : Nat) (x : α × Nat),
    x ∈ l.zipIdx k → x.2 < k + l.length
  | [], _, _, h => by simp at h
  | a :: l, k, x, h => by
    rw [List.zipIdx_cons] at h
    rw [List.length_cons]
    rcases List.mem_cons.1 h with rfl | h
    · show k < k + (l.length + 1)
      omega
    · have := snd_lt_zipIdx l (k + 1) x h
      omega

/-- What stands in a list's front stretch stands in the list. -/
theorem mem_of_takeWhile {α : Type} (p : α → Bool) : ∀ (l : List α) (x : α),
    x ∈ l.takeWhile p → x ∈ l
  | [], _, h => by simp at h
  | a :: l, x, h => by
    rw [List.takeWhile_cons] at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact List.mem_cons.2 (Or.inl rfl)
      · exact List.mem_cons.2 (Or.inr (mem_of_takeWhile p l x h))
    · simp at h

variable {σ C : Type}

/-- The number over the parts of a list of sub-protocols is the sum, one term a sub-protocol. -/
theorem mergeEnds_flatMap (M : List Addr) : ∀ bs : List (Block σ C),
    mergeEndsOf M (bs.flatMap planParts) = (bs.map fun b => mergeEndsOf M (planParts b)).sum
  | [] => rfl
  | b :: bs => by
    rw [List.flatMap_cons, BookRow.mergeEndsOf_append, mergeEnds_flatMap M bs, List.map_cons,
      List.sum_cons]

/-- CONDITIONAL: on h. Parts of which none is listed give 0. -/
theorem mergeEnds_none (M : List Addr) : ∀ ps : List PartAt,
    (∀ p ∈ ps, M.contains p.addr = false) → mergeEndsOf M ps = 0
  | [], _ => rfl
  | p :: ps, h => by
    have h1 := h p (List.mem_cons.2 (Or.inl rfl))
    have h2 := mergeEnds_none M ps fun q hq => h q (List.mem_cons.2 (Or.inr hq))
    simp only [BookRow.mergeEndsOf_cons, h1, h2, Bool.false_and, Bool.false_eq_true, if_false,
      Nat.add_zero]

/-! ## 2 The sub-protocols in front -/

/-- The sub-protocols that the maker goes through before the place a of link l, in its order. -/
def blocksInFront (bs : List (Block σ C)) (l : Nat) (a : Place) : List (Block σ C) :=
  (((bs.filterMap (·.place.link)).eraseDups.takeWhile (· != l)).flatMap fun l' =>
      bs.filter fun b => b.place.link == some l') ++
    (bs.filter fun b => b.place.link == some l).takeWhile fun b => b.place != a

/-- The parts in front are these sub-protocols' parts. -/
theorem front_parts (bs : List (Block σ C)) (l : Nat) (a : Place) :
    linksInFront bs l ++ partsInFront bs l a = (blocksInFront bs l a).flatMap planParts := by
  unfold linksInFront partsInFront blocksInFront
  rw [List.flatMap_append, List.flatMap_assoc]

/-- Each of them is one of the list. -/
theorem front_sub {bs : List (Block σ C)} {l : Nat} {a : Place} {b : Block σ C}
    (h : b ∈ blocksInFront bs l a) : b ∈ bs := by
  unfold blocksInFront at h
  rcases List.mem_append.1 h with h | h
  · obtain ⟨l', -, h'⟩ := List.mem_flatMap.1 h
    exact (List.mem_filter.1 h').1
  · exact (List.mem_filter.1 (mem_of_takeWhile _ _ _ h)).1

/-- The same cut on a list of places. -/
def placesInFront (ps : List Place) (l : Nat) (a : Place) : List Place :=
  (((ps.filterMap (·.link)).eraseDups.takeWhile (· != l)).flatMap fun l' =>
      ps.filter fun p => p.link == some l') ++
    (ps.filter fun p => p.link == some l).takeWhile fun p => p != a

/-- The places of the sub-protocols in front are that cut of the places. -/
theorem front_places (bs : List (Block σ C)) (l : Nat) (a : Place) :
    (blocksInFront bs l a).map (·.place) = placesInFront (bs.map (·.place)) l a := by
  simp only [blocksInFront, placesInFront, List.map_append, List.map_flatMap, List.filter_map,
    List.filterMap_map, List.takeWhile_map, Function.comp_def]

/-! ## 3 One sub-protocol's term -/

/-- CONDITIONAL: on h4 and h11. **A sub-protocol of another kind gives 0**: a listed address bears a
listed kind. -/
theorem mergeEnds_other (bs : List (Block σ C)) {b : Block σ C} (h4 : b.place.kind ≠ .K4)
    (h11 : b.place.kind ≠ .K11) : mergeEndsOf (mergesByName bs).ends (planParts b) = 0 := by
  refine mergeEnds_none _ _ fun p hp => ?_
  cases hc : (mergesByName bs).ends.contains p.addr
  · rfl
  · exfalso
    obtain ⟨p', hp', ea⟩ := List.mem_map.1 (List.contains_iff_mem.1 hc)
    have ht := (List.mem_filter.1 hp').2
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at ht
    have hpl : p.addr.place = b.place := BookRow.planParts_place hp
    rw [ea, hpl] at ht
    rcases ht.2 with h | h
    · exact h4 h
    · exact h11 h

variable {b : Block σ C} {Q : K4Pub}

/-- CONDITIONAL: on all five hypotheses. **K4's SUB-PROTOCOL GIVES 1**: its last part's one end
value. -/
theorem mergeEnds_k4 {bs : List (Block σ C)} (hnd : (bs.map (·.place)).Nodup) (hb : b ∈ bs)
    (hpl : b.place = k4Place Q)
    (hr : b.rounds = (entries Q.P Q.hp Q.g).map fun e => ({ entry := e } : Fmt.DeclaredRound))
    (hE : K4Ends Q) : mergeEndsOf (mergesByName bs).ends (planParts b) = 1 := by
  obtain ⟨hf, hm⟩ := k4_merges_byName hnd hb hpl hr hE
  have hlast := (merges_of hf hm).2
  have hs : (⟨k4Addr Q (k0 Q.g + 15), maskedP Q.P.wsLay.lk 1 1 1⟩ : PartAt).isSum = true := by
    show ((some "PSC epsilon" : Option String) == some "PSC epsilon") = true
    decide
  have ho : ((1 + 2 * Q.P.wsLay.lk + 1 + 1 != 0) = true) := by
    rw [bne_iff_ne]
    omega
  rw [k4_planParts hpl hr, k4PlanRow_split, BookRow.mergeEndsOf_append, BookRow.mergeEndsOf_cons,
    hlast, hs, ownScalars_masked, ho, endScalars_masked, mergeEnds_none]
  · rfl
  · intro p hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hp
    have hlt := snd_lt_zipIdx _ _ _ hx
    rw [k4FrontUnits_len] at hlt
    have hn := hf x.2 (by rw [k4RowIn_len]; omega)
    show (mergesByName bs).ends.contains (k4Addr Q x.2) = false
    cases hc : (mergesByName bs).ends.contains (k4Addr Q x.2)
    · rfl
    · exact absurd (List.contains_iff_mem.1 hc) hn

/-! ## 4 Three evaluations on the written list, each with a refusal -/

/-- How many places of a list are of the kind K4. -/
def cntK4 (ps : List Place) : Nat := (ps.map fun p => if p.kind == KindName.K4 then 1 else 0).sum

set_option maxRecDepth 1000000 in
/-- **Of the places in front of K4's place of group g just g are of the kind K4**, for g below 12.
By the kernel. -/
theorem frontCount : ((List.range 12).all fun g =>
    cntK4 (placesInFront IM.placesW (2 * g) (IM.k4Place g)) == g) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A wrong count is refused. -/
theorem frontCount_no :
    (cntK4 (placesInFront IM.placesW 2 (IM.k4Place 1)) == 2) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **None of these places is of the kind K11.** By the kernel. -/
theorem frontNoK11 : ((List.range 12).all fun g =>
    (placesInFront IM.placesW (2 * g) (IM.k4Place g)).all fun p => p.kind != KindName.K11) =
      true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Of the whole list that is refused: a place of the kind K11 stands on it. -/
theorem noK11_no : (IM.placesW.all fun p => p.kind != KindName.K11) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **Every place of the kind K4 on the list is K4's place of a group below 12.** By the kernel. -/
theorem k4Places : (IM.placesW.all fun p =>
    p.kind != KindName.K4 || (List.range 12).any fun g => p == IM.k4Place g) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- With eleven groups that is refused. -/
theorem k4Places_no : (IM.placesW.all fun p =>
    p.kind != KindName.K4 || (List.range 11).any fun g => p == IM.k4Place g) = false := by
  decide +kernel

/-! ## 5 The number -/

open VerifiableInference.Desc.First (S)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat} {gk : ℕ}

/-- CONDITIONAL: on hS, hR, O, hb and h11. A sub-protocol of the first chain of another kind than
K11 gives 1 if its kind is K4, else 0. -/
theorem term_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {b : Block S ProofFile.Cl}
    (hb : b ∈ c.blocksInOrder) (h11 : b.place.kind ≠ .K11) :
    mergeEndsOf (mergesByName c.blocksInOrder).ends (planParts b) =
      if b.place.kind == KindName.K4 then 1 else 0 := by
  have hps := IM.places_scope hS hR O
  have hnd : (c.blocksInOrder.map (·.place)).Nodup := by
    rw [hps]
    exact IM.places_nodup
  by_cases h4 : b.place.kind = .K4
  · rw [if_pos (beq_iff_eq.2 h4)]
    have hmem : b.place ∈ IM.placesW := by
      rw [← hps]
      exact List.mem_map.2 ⟨b, hb, rfl⟩
    have hk : (b.place.kind != KindName.K4 ||
        (List.range 12).any fun g => b.place == IM.k4Place g) = true :=
      List.all_eq_true.1 k4Places _ hmem
    rw [Bool.or_eq_true, bne_iff_ne] at hk
    rcases hk with hk | hk
    · exact absurd h4 hk
    · obtain ⟨g, hg, eg⟩ := List.any_eq_true.1 hk
      have hg' : g < 12 := List.mem_range.1 hg
      have epl : b.place = IM.k4Place g := beq_iff_eq.1 eg
      obtain ⟨-, -, x, -, -, -, -, -, -, -, ehp, -, -⟩ := IM.k4_of hS hR O g hg'
      obtain ⟨b', hb', hpl, hpl', hr⟩ := k4_member_there
        (Q := { P := Bs.G₀.W.layers, hp := x.2.hp, g := g, link := 2 * g, piece := 3, r0 := 0,
                seg := 0 }) hS hR O hg' ⟨rfl, ehp, rfl, rfl, rfl⟩
      obtain rfl : b' = b := List.inj_on_of_nodup_map hnd hb' hb (hpl'.trans epl.symm)
      exact mergeEnds_k4 hnd hb hpl hr (k4Ends_of_public O.public rfl)
  · rw [if_neg (fun h => h4 (beq_iff_eq.1 h))]
    exact mergeEnds_other _ h4 h11

/-- CONDITIONAL: on all four hypotheses. **IN FRONT OF K4's ROUNDS OF GROUP g THE MAKER COUNTS JUST
g END VALUES OF MERGES.** -/
theorem k4_mergeEnds_at_group (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) (hk : gk < 12) :
    mergeEndsOf (mergesByName c.blocksInOrder).ends
      (linksInFront c.blocksInOrder (2 * gk) ++ partsInFront c.blocksInOrder (2 * gk) (IM.k4Place gk)) = gk := by
  have hps := IM.places_scope hS hR O
  have hfp := front_places c.blocksInOrder (2 * gk) (IM.k4Place gk)
  rw [hps] at hfp
  have hw : ∀ b ∈ blocksInFront c.blocksInOrder (2 * gk) (IM.k4Place gk),
      mergeEndsOf (mergesByName c.blocksInOrder).ends (planParts b) =
        if b.place.kind == KindName.K4 then 1 else 0 := by
    intro b hb
    refine term_at hS hR O (front_sub hb) ?_
    have hm : b.place ∈ placesInFront IM.placesW (2 * gk) (IM.k4Place gk) := by
      rw [← hfp]
      exact List.mem_map.2 ⟨b, hb, rfl⟩
    have h0 : ((placesInFront IM.placesW (2 * gk) (IM.k4Place gk)).all fun p =>
        p.kind != KindName.K11) = true := List.all_eq_true.1 frontNoK11 gk (List.mem_range.2 hk)
    have h1 : (b.place.kind != KindName.K11) = true := List.all_eq_true.1 h0 _ hm
    exact bne_iff_ne.1 h1
  have hc0 : (cntK4 (placesInFront IM.placesW (2 * gk) (IM.k4Place gk)) == gk) = true :=
    List.all_eq_true.1 frontCount gk (List.mem_range.2 hk)
  have hc : cntK4 (placesInFront IM.placesW (2 * gk) (IM.k4Place gk)) = gk := beq_iff_eq.1 hc0
  rw [front_parts, mergeEnds_flatMap, List.map_congr_left hw]
  refine Eq.trans ?_ hc
  rw [← hfp]
  simp only [cntK4, List.map_map, Function.comp_def]

variable {p0 p1 p2 : Johnson.G.ChainSends} {B : ProverCoinCounts}

/-- CONDITIONAL: on all eight hypotheses. **BOTH NAMES OF K4's LOCK, AT THE MAKER's OWN LETTERS, AT
THE LIST OF MERGES THAT `onlineProverFromPublicFiles` HANDS, THE INDEX SIDE's AT idx.base.e + g.** -/
theorem k4Names_at_record_gk (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) (hk : gk < 12)
    (hQ : Q.P = Bs.G₀.W.layers ∧ Bs.G₀.W.G[gk]? = some Q.hp ∧ Q.g = gk ∧ Q.link = 2 * gk ∧
      Q.piece = 3)
    (h : bookWhole F p0 p1 p2 (mergesByName c.blocksInOrder) = .ok B) (hp : F.placesOk = true) {e : ℕ}
    (he : e = ownScalarsOf (partsInFront c.blocksInOrder (2 * gk) (IM.k4Place gk))) :
    ∃ row idx,
      ownerOf maskRowRun c.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds))
          s!"link {2 * gk}, moment 0" isMaskRowMsg = some row ∧
        ownerOf indexMaskRun c.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
          isIndexMaskMsg = some idx ∧
        K4MaskLockAt B Q e row.owner row.base.e ∧
        K4LastEntryAt B Q idx.owner (idx.base.e + gk) := by
  obtain ⟨row, idx, h1, h2, h3, h4⟩ := k4Names_at_record hS hR O hk hQ h hp he
  rw [k4_mergeEnds_at_group hS hR O hk] at h4
  exact ⟨row, idx, h1, h2, h3, h4⟩

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.snd_lt_zipIdx
#print axioms ProofFile.Honest.K4.W.mem_of_takeWhile
#print axioms ProofFile.Honest.K4.W.mergeEnds_flatMap
#print axioms ProofFile.Honest.K4.W.mergeEnds_none
#print axioms ProofFile.Honest.K4.W.front_parts
#print axioms ProofFile.Honest.K4.W.front_sub
#print axioms ProofFile.Honest.K4.W.front_places
#print axioms ProofFile.Honest.K4.W.mergeEnds_other
#print axioms ProofFile.Honest.K4.W.mergeEnds_k4
#print axioms ProofFile.Honest.K4.W.frontCount
#print axioms ProofFile.Honest.K4.W.frontCount_no
#print axioms ProofFile.Honest.K4.W.frontNoK11
#print axioms ProofFile.Honest.K4.W.noK11_no
#print axioms ProofFile.Honest.K4.W.k4Places
#print axioms ProofFile.Honest.K4.W.k4Places_no
#print axioms ProofFile.Honest.K4.W.term_at
#print axioms ProofFile.Honest.K4.W.k4_mergeEnds_at_group
#print axioms ProofFile.Honest.K4.W.k4Names_at_record_gk
