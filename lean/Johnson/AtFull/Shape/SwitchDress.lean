-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/SwitchDress.lean: WHICH DRESS THE CODE SWITCH's BLOCK WEARS IN A LINK (kind
K2). The library's IM.K2Is (Johnson/IMR/K2Seat.lean) leaves "the head's | the link's" open. A
general law; nothing is evaluated.

By what. The lot's text (P1K2.pureTable | pureAt, Johnson/Desc/ProofFile/Lot/K2.lean) chooses the
dress by the word "stands" of the place's numbers. The library has a test on the public part that
says of each place with numbers that this word is the one that its link asks (K2Caller.spotsFitB |
dressOf, Johnson/Top/H0/K2Caller/PAtSeated.lean).

  **`link_arm`**: where every place with numbers of the lot stands in K2Caller.dressOf 25 ‹its
    link›: a block of the lot's table that passes its test on the plan and stands in a link l with l
    + 1 ≠ 25 is the kind's block in the link's dress, at the plan's numbers for l, under its own
    name and place.

Limits. The premise is a letter here; SwitchReturns.lean (stands_at) pays it under the head
P5J.AtMgA. The number 25 is the premise's. Nothing on soundness, completeness or hiding.
-/
import Johnson.Loose.H2K12.SpotsAtAll
import Johnson.AtFull.Shape.SwitchAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 At codeSwitchKind finishPlace headOpened)
open VerifiableInference.Desc.First.K2Caller (dressOf spotsFitB)
open OnBytes.Maker (WholeD)
open IM (k2P under)
open P5J (AtMgA)

/-- **GENERAL: the link's dress.** -/
theorem link_arm {Z : ProofFile.Pub} {G : ProofFile.Ground} {x : Block S Unit}
    (h : x ∈ P1K2.pureTable (fun _ _ => some none) Z G) (hp : x.planOk = true)
    (hst : ∀ y ∈ P1K2.pureSpots Z G, y.2.stands = dressOf 25 y.1.place.link) {l : Nat}
    (hl : x.place.link = some l) (h24 : l + 1 ≠ 25) :
    ∃ P n, P1K2.prepOf Z G = some P ∧ P1K2.numsAt P (some l) = some n ∧
      x = under x.name x.place (codeSwitchKind (k2P Z x.place x.name .link n)) := by
  unfold P1K2.pureTable at h
  obtain ⟨sp, -, hx⟩ := List.mem_map.1 h
  cases hy : (P1K2.pureSpots Z G).find? (fun x => x.1.name == sp.name) with
  | none =>
    simp only [hy] at hx
    subst hx
    cases hp
  | some y =>
    simp only [hy] at hx
    have hm := List.mem_of_find?_eq_some hy
    have hs := hst y hm
    cases hpa : P1K2.pureAt (fun _ _ => some none) G y with
    | none =>
      rw [hpa] at hx
      subst hx
      cases hp
    | some c =>
      rw [hpa] at hx
      obtain rfl : c = x := hx
      unfold P1K2.pureSpots at hm
      cases hsp : ProofFile.spotsOf Z.cuts with
      | none => rw [hsp] at hm; cases hm
      | some sps =>
        rw [hsp] at hm
        have hm' : y ∈ P1K2.p2All Z G sps := hm
        unfold P1K2.p2All at hm'
        split at hm'
        · cases hm'
        · rename_i P hP
          obtain ⟨sp', -, e⟩ := List.mem_filterMap.1 hm'
          obtain ⟨p, hpw, rfl⟩ := Option.map_eq_some_iff.1 e
          unfold P1K2.p2With at hpw
          obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.1 hpw
          unfold P1K2.pureAt at hpa
          dsimp only at hpa hs
          split at hpa
          · rename_i hst'
            obtain rfl := Option.some.inj hpa
            have hl' : sp'.place.link = some l := hl
            rw [hst', hl'] at hs
            unfold dressOf at hs
            dsimp only at hs
            by_cases e : (l + 1 == 25) = true
            · rw [if_pos e] at hs
              cases hs
            · rw [if_neg e] at hs
              cases hs
          · rename_i hst'
            obtain ⟨HP, -, rfl⟩ := Option.map_eq_some_iff.1 hpa
            have hl' : sp'.place.link = some l := hl
            rw [hst', hl'] at hs
            unfold dressOf at hs
            dsimp only at hs
            rw [if_neg (by simpa using h24)] at hs
            cases hs
          · rename_i hst'
            obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hpa
            obtain ⟨l', hl', ho⟩ := Option.bind_eq_some_iff.1 ho
            obtain rfl : none = o := Option.some.inj ho
            have hl'' : sp'.place.link = some l := hl
            refine ⟨P, n, hP, by rw [← hl'']; exact hn, ?_⟩
            show _ = under sp'.name sp'.place (codeSwitchKind (k2P Z sp'.place sp'.name .link n))
            unfold k2P
            rw [← hst']
            rfl

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.link_arm
