-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/GoodLayShares.lean: FOR K9's FALL ON THE FREE SLOT, AT A FEED-FORWARD SEGMENT: "GOOD"
(`GoodLayers`, Honest/K9/LayersFree.lean) CUT BY HOUSE: WHAT EACH OF FOUR KINDS' HOUSES WOULD HAVE TO BRING, AS ONE
THEOREM's BINDERS. Statements and proofs ON THE VERIFIER's DATA; no prover is in this file, and no goal is stated. No
probability is in this file.
  `unnamedAt_blanks`, `plainOf_own`, `four8_own`   the claims without form name no slot; a form laid as a plain claim,
      and each of K8's first four claims, takes its own number
**`goodCut_of_shares`** on written lists: the Bool `goodCut` (Honest/K9/CutLaw.lean) is true of plainOf rC ++ plainOf lf
++ plainOf rD, FOUR, N, plainOf bk IF: every slot below n but M lies in one of four sets WC, W4, WD, W8 (cover) · each
slot of a set is live in that share's own list (liveC: rC · live4: lf and bk · liveD: rD · live8: FOUR) · none of the
lists names M, where M lies below n (unC, un4, unD, un8) · the whole list is no longer than the plan's number (len).
"PLAIN" IS ASKED OF NO SHARE: every claim of the list takes its own number (own4, which `four8_own` pays)
  **`goodLayers_of_shares`**   so `GoodLayers p4 s a₀ n`, at the lists written off what the state holds as heard: rC :=
      the rows of what the lookup on the calls heard · lf, bk := K4's forms in front and behind · rD := the rows of what
      the lookup on the digits heard · FOUR := K8's first four claims · M := the merge's slot of s
WHOSE EACH BINDER IS MEANT TO BE. liveC, unC: the lookups' (the calls) · liveD, unD: the lookups' (the digits) · live4,
un4: K4's; it has all four things heard in hand (`Heard4`), so a slot of the calls' stretch that K4's forms
alone name can stand in W4 · live8, un8: K8's · cover: numbers at the plan · len: from the lengths that each text fixes.
 THE FOUR SETS ARE LETTERS: which slots each share answers for is not
said here; overlap does no harm.
WHAT A SHARE's LAW WOULD LOOK LIKE, in words: "my mark is silent at my member's own draws, and the state holds what my
member heard of them: so my list is live on my set, and names no slot outside my stretch". From there to these binders:
the carriage of what was heard to the state in front of the batching: not here.
IS IT EMPTY? `goodCut_of_shares` has a member at which every share answers for a slot of its own, and five bent twins
(Honest/K9/GoodLaySharesToy.lean [not in this library; so here read: not proved in this library]).
OF `goodLayers_of_shares` NO MEMBER IS SHOWN: `Heard4` is shown of no state; where
nothing was heard `GoodLayers` holds idly.
WHAT IS NOT CLAIMED. Any binder at any state. That sets exist which cover the slots below n, but the merge's; nor that
the list is within the plan's number. That a mark's silence gives any share. What Honest/K9/LayersFree.lean does not
claim. `goodW` follows from `GoodLayers` and `Walk` in Honest/K9/GoodLay.lean. No member of a run;
`goodLayers_of_shares` is called by no line; `goodCut_of_shares` by it and by the toy. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.LayersFree
import Johnson.Desc.K9.Honest.SlotsJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.K8.Honest (layersFront layersBack plainOf)
open VerifiableInference.Desc.K9 (mergeOf)
open VerifiableInference.Desc.K9H (liveAt plainAt unnamedAt slotsLive liveAt_append unnamedAt_append)

/-- The claims without form name no slot. -/
theorem unnamedAt_blanks (N j : Nat) : unnamedAt (List.replicate N blank) j = true := by
  unfold unnamedAt
  rw [List.all_eq_true]
  intro c hc
  rw [List.eq_of_mem_replicate hc]
  rfl

/-- A form laid as a plain claim takes its own number. -/
theorem plainOf_own (l : List Aff) : ∀ c ∈ plainOf l, c.eqFirst = none := by
  intro c hc
  obtain ⟨f, -, rfl⟩ := List.mem_map.1 hc
  rfl

/-- **THE BOOL "good" ON A WRITTEN LIST, FROM FOUR SHARES.** rC, lf, rD, bk: forms; FOUR: claims that take their own
number. WC, W4, WD, W8: which slots each share answers for: letters. -/
theorem goodCut_of_shares (n : Nat) (M : Option Nat) (rC lf rD : List Aff) (FOUR : List Claim) (N : Nat)
    (bk : List Aff) (plan : Nat) (own4 : ∀ c ∈ FOUR, c.eqFirst = none) (WC W4 WD W8 : Nat → Prop)
    (cover : ∀ j < n, M ≠ some j → WC j ∨ W4 j ∨ WD j ∨ W8 j)
    (liveC : ∀ j, WC j → liveAt (plainOf rC) j = true)
    (live4 : ∀ j, W4 j → liveAt (plainOf lf ++ plainOf bk) j = true)
    (liveD : ∀ j, WD j → liveAt (plainOf rD) j = true) (live8 : ∀ j, W8 j → liveAt FOUR j = true)
    (unC : ∀ j < n, M = some j → unnamedAt (plainOf rC) j = true)
    (un4 : ∀ j < n, M = some j → unnamedAt (plainOf lf ++ plainOf bk) j = true)
    (unD : ∀ j < n, M = some j → unnamedAt (plainOf rD) j = true)
    (un8 : ∀ j < n, M = some j → unnamedAt FOUR j = true)
    (len : (cutList (plainOf rC ++ plainOf lf ++ plainOf rD) FOUR N (plainOf bk)).length ≤ plan) :
    goodCut n M (plainOf rC ++ plainOf lf ++ plainOf rD) FOUR N (plainOf bk) plan = true := by
  unfold goodCut
  rw [Bool.and_eq_true]
  refine ⟨?_, decide_eq_true len⟩
  unfold slotsLive
  rw [List.all_eq_true]
  intro j hj
  have hjn : j < n := List.mem_range.1 hj
  by_cases hM : M = some j
  · have c2 := un4 j hjn hM
    rw [unnamedAt_append, Bool.and_eq_true] at c2
    have hb : (M == some j) = true := by rw [hM]; exact beq_self_eq_true _
    rw [if_pos hb]
    unfold cutList
    simp only [unnamedAt_append, Bool.and_eq_true]
    exact ⟨⟨⟨⟨unC j hjn hM, c2.1⟩, unD j hjn hM⟩, un8 j hjn hM, unnamedAt_blanks _ j⟩, c2.2⟩
  · have hb : ¬ (M == some j) = true := fun h => hM (eq_of_beq h)
    rw [if_neg hb, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · unfold cutList
      simp only [liveAt_append, Bool.or_eq_true]
      rcases cover j hjn hM with h | h | h | h
      · exact Or.inl (Or.inl (Or.inl (Or.inl (liveC j h))))
      · have c := live4 j h
        rw [liveAt_append, Bool.or_eq_true] at c
        rcases c with c | c
        · exact Or.inl (Or.inl (Or.inl (Or.inr c)))
        · exact Or.inr c
      · exact Or.inl (Or.inl (Or.inr (liveD j h)))
      · exact Or.inl (Or.inr (Or.inl (live8 j h)))
    · unfold plainAt
      rw [List.all_eq_true]
      intro c hc
      have e : c.eqFirst = none := by
        unfold cutList at hc
        simp only [List.mem_append] at hc
        rcases hc with (((h | h) | h) | (h | h)) | h
        · exact plainOf_own _ c h
        · exact plainOf_own _ c h
        · exact plainOf_own _ c h
        · exact own4 c h
        · rw [List.eq_of_mem_replicate h]
          rfl
        · exact plainOf_own _ c h
      rw [e]
      rfl

/-- K8's first four claims take their own number. -/
theorem four8_own (tl : HTailF2) (g : Forest.Heard) : ∀ c ∈ K9L.four8 tl g, c.eqFirst = none := by
  intro c hc
  unfold K9L.four8 at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> rfl

/-- **"GOOD" AT A FEED-FORWARD SEGMENT FROM FOUR HOUSES' SHARES.** WC, W4, WD, W8: which slots the lookup on the calls,
K4, the lookup on the digits and K8 answer for: letters. -/
theorem goodLayers_of_shares (p4 : OnBytes.Desc.First.K4.Par) (s : S) (a₀ : LayOwn) (n : Nat)
    (WC W4 WD W8 : Nat → Prop)
    (cover : ∀ j < n, mergeOf s ≠ some j → WC j ∨ W4 j ∨ WD j ∨ W8 j)
    (liveC : ∀ gC, a₀.lookHeard = some gC → ∀ j, WC j → liveAt (plainOf gC.rows.toList) j = true)
    (live4 : ∀ gC gD o lf, Heard4 p4 a₀ gC gD o lf → ∀ j, W4 j → liveAt (plainOf lf ++ layersBack o) j = true)
    (liveD : ∀ gD, a₀.tl.heard = some gD → ∀ j, WD j → liveAt (plainOf gD.rows.toList) j = true)
    (live8 : ∀ gD, a₀.tl.heard = some gD → ∀ j, W8 j → liveAt (K9L.four8 a₀.tl gD) j = true)
    (unC : ∀ gC, a₀.lookHeard = some gC → ∀ j < n, mergeOf s = some j →
      unnamedAt (plainOf gC.rows.toList) j = true)
    (un4 : ∀ gC gD o lf, Heard4 p4 a₀ gC gD o lf → ∀ j < n, mergeOf s = some j →
      unnamedAt (plainOf lf ++ layersBack o) j = true)
    (unD : ∀ gD, a₀.tl.heard = some gD → ∀ j < n, mergeOf s = some j →
      unnamedAt (plainOf gD.rows.toList) j = true)
    (un8 : ∀ gD, a₀.tl.heard = some gD → ∀ j < n, mergeOf s = some j →
      unnamedAt (K9L.four8 a₀.tl gD) j = true)
    (len : ∀ gC gD o lf, Heard4 p4 a₀ gC gD o lf →
      (cutList (layersFront gC gD lf) (K9L.four8 a₀.tl gD) (k8Len a₀.tl o.funs) (layersBack o)).length ≤
        a₀.F.planClaimsF) :
    GoodLayers p4 s a₀ n := fun gC gD o lf H =>
  goodCut_of_shares n (mergeOf s) gC.rows.toList lf gD.rows.toList (K9L.four8 a₀.tl gD) (k8Len a₀.tl o.funs)
    (K4Values.backForms o) a₀.F.planClaimsF (four8_own a₀.tl gD) WC W4 WD W8 cover (liveC gC H.calls)
    (live4 gC gD o lf H) (liveD gD H.digits) (live8 gD H.digits) (unC gC H.calls) (un4 gC gD o lf H)
    (unD gD H.digits) (un8 gD H.digits) (len gC gD o lf H)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.unnamedAt_blanks
#print axioms ProofFile.Honest.K9.plainOf_own
#print axioms ProofFile.Honest.K9.goodCut_of_shares
#print axioms ProofFile.Honest.K9.four8_own
#print axioms ProofFile.Honest.K9.goodLayers_of_shares
