-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/PAtSeated.lean: code switching: THE NUMBERS OF THE PLACE AT WHICH THE
SENTENCE ON THE CARRIED CLAIM IS SPENT (ProofFile.pAtK2 Z m, Johnson/Desc/ProofFile/CarryAt.lean) ARE THE
NUMBERS OF THE SUB-PROTOCOL THAT THE LOT LAYS THERE (IM.k2P Z a nm st n, Johnson/IMR/K2Seat.lean),
AND ITS DRESS st GOES BY THE PLACE's LINK: under one test with code on the public part Z. NO
SUB-PROTOCOL IMPORTS THIS FILE.
WHY. In the ties one letter stands for both. They come from two makers: pAtK2? Z m is the FIRST
place of the lot's list whose switch opens group m + 1; a live member of the lot's table is made of
SOME member of that list. And the table's member is known so far in «one of three dresses».
  numsAt_pos      the numbers of a place name a group that is not group 0
  dressOf L link  the dress that a link asks: none: the finish · the last link: the head · else: a
                  link
  spotsFitB Z     THE TEST: no two places of the lot's list open one group; each has the dress that
                  its link asks
  pAt_of_mem      where no two open one group: a member of the list that opens group m + 1 is what
                  pAtK2? Z m finds
  table_live · spot_is · pureAt_is   a live member of the lot's table is made of a member of the
                  list; what such a member is; what is made of it, dress by dress
  seated_is_pAt   THE STATEMENT: at the ground at which the description asks its lots, under the
                  test: a live member x of the table is the kind's sub-protocol at
                  p := ProofFile.pAtK2 Z (n.grp - 1), in p's own dress; and
                  p = k2P Z x.place x.name (dressOf … x.place.link) n
LIMITS. THE TEST HAS BEEN EVALUATED AT NO Z. No theorem stands in its place: that the places of the
kind have pairwise different links, and that a place's first step's name begins with the letter
that its link asks, is said by no lemma that I know.
(Where this and lean/THEOREM.md differ, the page
holds.) n.grp at the finish is the number of links:
what that number is in scope is other files' to show. No soundness is claimed.
-/
import Johnson.Desc.ProofFile.CarryAt
import Johnson.IMR.K2Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 At codeSwitchKind finishPlace headOpened)
open IM (k2P under)

/-- The numbers of a place name a group that is not group 0. -/
theorem numsAt_pos {P : P1K2.Prep} {link : Option Nat} {n : P1K2.Nums}
    (h : P1K2.numsAt P link = some n) : n.grp ≠ 0 := by
  unfold P1K2.numsAt at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hl
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, _, f, _, lay, _, rd, _, rfl⟩ := h
    show link.getD P.z.request.link.length ≠ 0
    simpa using hl

/-- The dress that a link asks. L: the number of links. -/
def dressOf (L : Nat) (link : Option Nat) : At :=
  match link with
  | none => .finish
  | some l => if l + 1 == L then .head else .link

/-- **The test**, on the public part alone. -/
def spotsFitB (Z : ProofFile.Pub) : Bool :=
  decide (((ProofFile.k2SpotsAt Z).map (·.2.grp)).Nodup) &&
    (ProofFile.k2SpotsAt Z).all fun y =>
      decide (y.2.stands = dressOf Z.s₀.check.frame.shape.link.length y.1.place.link)

theorem pAt_of_mem {Z : ProofFile.Pub} {m : Nat} {y : ProofFile.Spot × P2}
    (hU : ((ProofFile.k2SpotsAt Z).map (·.2.grp)).Nodup) (hy : y ∈ ProofFile.k2SpotsAt Z)
    (hg : y.2.grp = m + 1) : ProofFile.pAtK2? Z m = some y.2 := by
  unfold ProofFile.pAtK2?
  cases hf : (ProofFile.k2SpotsAt Z).find? (fun x => x.2.grp == m + 1) with
  | none =>
    have c := List.find?_eq_none.1 hf y hy
    simp [hg] at c
  | some y' =>
    have h1 : y'.2.grp = m + 1 := by simpa using List.find?_some hf
    have e : y' = y :=
      List.inj_on_of_nodup_map hU (List.mem_of_find?_eq_some hf) hy (h1.trans hg.symm)
    rw [e]
    rfl

/-- A live member of the lot's table is made of a member of the lot's list. -/
theorem table_live {q : ProofFile.Ground → Nat → Option (Option (Block S Unit))} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} {x : Block S Unit} (h : x ∈ P1K2.pureTable q Z G) (hp : x.planOk = true) :
    ∃ y ∈ P1K2.pureSpots Z G, P1K2.pureAt q G y = some x := by
  unfold P1K2.pureTable at h
  obtain ⟨sp, -, rfl⟩ := List.mem_map.1 h
  revert hp
  split
  · intro hp
    exact Bool.noConfusion (show false = true from hp)
  · rename_i y hy
    intro hp
    cases hq : P1K2.pureAt q G y with
    | none =>
      rw [hq] at hp
      exact Bool.noConfusion (show false = true from hp)
    | some c => exact ⟨y, List.mem_of_find?_eq_some hy, hq⟩

/-- What a member of the lot's list is. -/
theorem spot_is {Z : ProofFile.Pub} {G : ProofFile.Ground} {y : ProofFile.Spot × P2}
    (hy : y ∈ P1K2.pureSpots Z G) :
    ∃ P n, P1K2.prepOf Z G = some P ∧ P1K2.numsAt P y.1.place.link = some n ∧
      y.2 = k2P Z y.1.place y.1.name (P1K2.standsOf y.1) n := by
  unfold P1K2.pureSpots at hy
  cases hs : ProofFile.spotsOf Z.cuts with
  | none => rw [hs] at hy; cases hy
  | some sps =>
    rw [hs] at hy
    have hm : y ∈ P1K2.p2All Z G sps := hy
    unfold P1K2.p2All at hm
    split at hm
    · cases hm
    · rename_i P hP
      obtain ⟨sp', -, e⟩ := List.mem_filterMap.1 hm
      obtain ⟨p, hpw, rfl⟩ := Option.map_eq_some_iff.1 e
      unfold P1K2.p2With at hpw
      obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.1 hpw
      exact ⟨P, n, hP, hn, rfl⟩

/-- What the lot makes of a member of its list, dress by dress. -/
theorem pureAt_is {G : ProofFile.Ground} {y : ProofFile.Spot × P2} {x : Block S Unit}
    (h : P1K2.pureAt (fun _ _ => some none) G y = some x) :
    x.place = y.1.place ∧ x.name = y.1.name ∧
      ((y.2.stands = .finish ∧ x = under y.1.name y.1.place (finishPlace y.2)) ∨
        (y.2.stands = .head ∧ ∃ l HP, y.1.place.link = some l ∧ P1K2.pureLetters G l = some HP ∧
          x = under y.1.name y.1.place
            ((codeSwitchKind y.2 : Block S Unit).andThen y.1.name (headOpened y.1.name y.1.place HP))) ∨
        (y.2.stands = .link ∧ x = under y.1.name y.1.place (codeSwitchKind y.2))) := by
  unfold P1K2.pureAt at h
  dsimp only at h
  split at h
  · rename_i hst
    obtain rfl := Option.some.inj h
    exact ⟨rfl, rfl, Or.inl ⟨hst, rfl⟩⟩
  · rename_i hst
    obtain ⟨HP, hHP, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨l, hl, hHP⟩ := Option.bind_eq_some_iff.1 hHP
    exact ⟨rfl, rfl, Or.inr (Or.inl ⟨hst, l, HP, hl, hHP, rfl⟩)⟩
  · rename_i hst
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨l, -, ho⟩ := Option.bind_eq_some_iff.1 ho
    obtain rfl : none = o := Option.some.inj ho
    exact ⟨rfl, rfl, Or.inr (Or.inr ⟨hst, rfl⟩)⟩

/-- **The sentence's numbers are the laid sub-protocol's, and the dress goes by the link.** -/
theorem seated_is_pAt {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {x : Block S Unit}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G₀) (hT : spotsFitB Z = true)
    (hx : x ∈ P1K2.pureTable (fun _ _ => some none) Z G₀) (hp : x.planOk = true) :
    ∃ P n, P1K2.prepOf Z G₀ = some P ∧ P1K2.numsAt P x.place.link = some n ∧
      ProofFile.pAtK2 Z (n.grp - 1) = k2P Z x.place x.name
        (dressOf Z.s₀.check.frame.shape.link.length x.place.link) n ∧
      (((ProofFile.pAtK2 Z (n.grp - 1)).stands = .finish ∧
          x = under x.name x.place (finishPlace (ProofFile.pAtK2 Z (n.grp - 1)))) ∨
        ((ProofFile.pAtK2 Z (n.grp - 1)).stands = .head ∧ ∃ l HP, x.place.link = some l ∧
          P1K2.pureLetters G₀ l = some HP ∧ x = under x.name x.place
            ((codeSwitchKind (ProofFile.pAtK2 Z (n.grp - 1)) : Block S Unit).andThen x.name
              (headOpened x.name x.place HP))) ∨
        ((ProofFile.pAtK2 Z (n.grp - 1)).stands = .link ∧
          x = under x.name x.place (codeSwitchKind (ProofFile.pAtK2 Z (n.grp - 1))))) := by
  obtain ⟨y, hy, hq⟩ := table_live hx hp
  obtain ⟨P, n, hP, hn, e⟩ := spot_is hy
  obtain ⟨e1, e2, arms⟩ := pureAt_is hq
  have hk : ProofFile.k2SpotsAt Z = P1K2.pureSpots Z G₀ := by
    unfold ProofFile.k2SpotsAt
    rw [hG]
    rfl
  have hy' : y ∈ ProofFile.k2SpotsAt Z := by rw [hk]; exact hy
  unfold spotsFitB at hT
  rw [Bool.and_eq_true] at hT
  have hD := of_decide_eq_true (List.all_eq_true.1 hT.2 y hy')
  have hg0 := numsAt_pos hn
  have hgy : y.2.grp = n.grp := by rw [e]; rfl
  have hpA : ProofFile.pAtK2? Z (n.grp - 1) = some y.2 :=
    pAt_of_mem (of_decide_eq_true hT.1) hy' (by rw [hgy]; omega)
  have hpB : ProofFile.pAtK2 Z (n.grp - 1) = y.2 := by
    unfold ProofFile.pAtK2
    rw [hpA]
    rfl
  have hst : P1K2.standsOf y.1 = dressOf Z.s₀.check.frame.shape.link.length y.1.place.link := by
    rw [e] at hD
    exact hD
  refine ⟨P, n, hP, by rw [e1]; exact hn, ?_, ?_⟩
  · rw [hpB, e1, e2, ← hst]
    exact e
  · rw [hpB, e1, e2]
    exact arms

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.pAt_of_mem
#print axioms VerifiableInference.Desc.First.K2Caller.table_live
#print axioms VerifiableInference.Desc.First.K2Caller.spot_is
#print axioms VerifiableInference.Desc.First.K2Caller.pureAt_is
#print axioms VerifiableInference.Desc.First.K2Caller.seated_is_pAt
