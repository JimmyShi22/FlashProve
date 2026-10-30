-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/MergeRounds.lean: FROM A RETURN OF A MERGE OF THE CLAIMS ON THE WEIGHTS TO
`mergeDraws` (PileDefs.lean of this folder) AT A CHAIN's ROUNDS; AND THE HEAD's MERGING
SUB-PROTOCOL. Statements with their proofs. It stands on PileDefs.lean, SampledRV.lean,
MergeTape.lean and the library alone.

MergeTape.lean says, from a return of a merge, what its tape's rounds sampled (`MergeSampled`). A
sub-protocol is handed rounds (`Fmt.RoundView`), of which its text makes the tape. At the head:
`mergeTapeE` (Johnson/Desc/First/Fork/MergeKind.lean). The library has that maker and the decision
both ways, and what such a tape holds of what was sampled: `tape_iff`, `decide_iff`
(Johnson/Top/H0/MergeLaw/Asks.lean), `tapeS_zip` (MergeLaw/Law.lean), `tape_drawn`
(MergeLaw/Beta.lean): all four are called.
Kin in the library of `headMerge_draws`: `claim_says_pinned` (MergeLaw/Pinned.lean: from the same
return: the whole tape of rs written out; without wo.rm, wo.recs, the claim), `decide_view`
(MergeLaw/Out.lean: at the rounds of a typed transcript, without digests), `decide_inv`. None ties
the batching element and wo.rm to the challenges of any rounds.
Main names:
  `mergeTapeE_sampled`: wherever the head's maker returns a tape, its rounds sampled what the rounds
    sampled (`sampledRV`).
  `sampled_flat`, `mergeDraws_of_sampled`: where the challenges hold sigma, one more, then rm's
    elements, one each, `mergeDraws` returns (sigma, rm).
  `mergeDraws_of_tape`: **the joint**: of `MergeSampled` at a tape t, and rounds rs that sampled
    what t's rounds sampled: `mergeDraws` at the challenges of the first 2 + lk of rs returns
    (sigma, rm).
  `mergeDraws_at_chain`: the same at a chain's rounds, where the merge ran on the tape of a whole
    slice, as the step hands it on.
  `headMerge_draws`: **the head's merging sub-protocol**: from a return of `headMergeDecide` on
    rounds rs AS THE DECISION IS HANDED THEM: the one claim that it has merged is the state in
    front's; what it leaves stands in the state behind; there are just lk + 4 rounds; `mergeDraws`
    returns at the first 2 + lk; what it leaves of the claim is `mergeRecs` at these.
  `headMerge_at_chain`: **the same AT THE CHAIN's OWN ROUNDS**, digests and all: from a return of
    the decision on a slice of the chain's rounds as `Block.step` hands it on (without the digests):
    what the merge left is read off the state behind by `leftHead`
    (Johnson/Desc/First/Close/TailHead.lean); `mergeDraws` at the 2 + lk challenges from the slice's
    first number on: THE SECOND, THIRD AND FOURTH CLAUSES OF `ClaimsIs` at sigmaAt := that number
    and cl := the one claim that the state in front holds.

What is not claimed. That the sub-protocol at any number of a chain decides by `headMergeDecide`.
The layers' sites: MergeLayers.lean. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.K13.Honest.MergeTape
import Johnson.Desc.K13.Honest.SampledRV
import Johnson.Top.H0.MergeLaw.Asks
import Johnson.Top.H0.MergeLaw.Beta
import Johnson.Desc.First.Close.TailHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc (noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.MergeLaw (tape_iff decide_iff tapeS_zip tape_drawn)
open Johnson.Desc.First.ForkMerge (mergeTapeE HeadMergeP headMergeDecide)
open VerifiableInference.Desc.First.Close (leftHead)

/-- The head's merge's maker of a tape, wherever it returns one. -/
theorem mergeTapeE_sampled {rs : List Fmt.RoundView} {es : List Fmt.Entry} {t : Tape}
    (h : mergeTapeE rs es = .ok t) : tapeSampled t = sampledRV rs := by
  obtain ⟨r, rs', e, es', t', rfl, rfl, _, _, ht, rfl⟩ := (tape_iff rs es t).1 h
  obtain ⟨hl, rfl⟩ := tapeS_zip rs' es' t' ht
  show (flatOf r (some e)).drawn ::
    ((rs'.zip es').map fun x => flatOf x.1 (some x.2)).map (·.drawn) = _
  rw [tape_drawn hl]
  rfl

/-! ## From what a merge's tape sampled to `mergeDraws` -/

/-- Where each challenge of a list holds just the one element that ys names: the elements in a row
are ys, and each challenge has one element. -/
theorem sampled_flat : ∀ (own : List Fmt.Drawn) (ys : List E),
    (own.map fun d => d.elems.map E.ofTriple) = ys.map ([·]) →
    (own.flatMap fun d => d.elems.map E.ofTriple) = ys ∧
      own.all (fun d => d.elems.length == 1) = true
  | [], [], _ => ⟨rfl, rfl⟩
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | d :: own, y :: ys, h => by
    rw [List.map_cons, List.map_cons] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    obtain ⟨e0, e2⟩ := sampled_flat own ys h2
    cases hd : d.elems with
    | nil => rw [hd] at h1; cases h1
    | cons z zs =>
      rw [hd, List.map_cons] at h1
      obtain ⟨hz, hzs⟩ := List.cons.inj h1
      obtain rfl : zs = [] := List.map_eq_nil_iff.1 hzs
      refine ⟨?_, ?_⟩
      · rw [List.flatMap_cons, e0, hd, ← hz]
        rfl
      · rw [List.all_cons, e2, hd]
        rfl

/-- **Where the challenges hold sigma, one more, then rm's elements, one each**, `mergeDraws`
returns (sigma, rm). -/
theorem mergeDraws_of_sampled {lk : Nat} {own : List Fmt.Drawn} {sigma e : E} {rm : Array E}
    (hs : rm.size = lk)
    (h : (own.map fun d => d.elems.map E.ofTriple) = [sigma] :: [e] :: rm.toList.map ([·])) :
    mergeDraws lk own = some (sigma, rm) := by
  obtain ⟨e0, e2⟩ := sampled_flat own (sigma :: e :: rm.toList) h
  have hl : own.length = 2 + lk := by
    have := congrArg List.length h
    simp only [List.length_map, List.length_cons, Array.length_toList, hs] at this
    omega
  unfold mergeDraws
  rw [e2, e0, hl]
  simp

/-- **THE JOINT.** t: the tape on which a merge has run. rs: rounds that sampled what t's rounds
sampled. Then `mergeDraws` at the challenges of the first 2 + lk of rs returns the merge's own
batching element and column challenges. -/
theorem mergeDraws_of_tape {lk : Nat} {t u : Tape} {sigma : E} {rm : Array E} {rs : List Fmt.RoundView}
    (h : MergeSampled lk t u sigma rm) (ht : tapeSampled t = sampledRV rs) :
    mergeDraws lk ((rs.take (2 + lk)).map (·.drawn)) = some (sigma, rm) := by
  obtain ⟨hs, e, beta, q⟩ := h
  have q' : sampledRV rs =
      ([sigma] :: [e] :: rm.toList.map ([·])) ++ ([beta] :: [] :: tapeSampled u) := by
    rw [← ht, q]
    rfl
  have hl : ([sigma] :: [e] :: rm.toList.map ([·])).length = 2 + lk := by
    simp only [List.length_cons, List.length_map, Array.length_toList, hs]
    omega
  refine mergeDraws_of_sampled (e := e) hs ?_
  have a : (((rs.take (2 + lk)).map (·.drawn)).map fun d => d.elems.map E.ofTriple) =
      (sampledRV rs).take (2 + lk) := by
    unfold sampledRV
    rw [List.map_map, List.map_take]
    rfl
  rw [a, q', List.take_left' hl]

/-- **THE JOINT AT A CHAIN's ROUNDS.** rs: the chain's rounds. a, len: where a sub-protocol's own
slice begins, and its length. The merge has run on a tape that sampled what that slice sampled, as
the step hands it on (without the rounds' digests). -/
theorem mergeDraws_at_chain {lk a len : Nat} {t u : Tape} {sigma : E} {rm : Array E}
    {rs : List Fmt.RoundView} (h : MergeSampled lk t u sigma rm)
    (ht : tapeSampled t = sampledRV (((rs.drop a).take len).map noDigest)) :
    mergeDraws lk (((rs.drop a).take (2 + lk)).map (·.drawn)) = some (sigma, rm) := by
  have hle : 2 + lk ≤ len := by
    have h1 := h.closes
    have h2 := congrArg List.length ht
    simp only [tapeSampled, sampledRV, List.length_map, List.length_take] at h2
    omega
  have q := mergeDraws_of_tape h (ht.trans (sampledRV_noDigest _))
  rw [List.take_take, Nat.min_eq_left hle] at q
  exact q

/-! ## The head's merging sub-protocol -/

/-- **WHERE THE HEAD's MERGING SUB-PROTOCOL's DECISION RETURNS**, on rounds rs as the decision is
handed them. -/
theorem headMerge_draws {P : HeadMergeP} {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') :
    ∃ (a a' : First.HeadOwn) (claim : WsClaim) (wo : WsForkOut) (sigma : E),
      s.here = .head a ∧ a.claim = some claim ∧ s'.here = .head a' ∧ a'.wo = some wo ∧
      rs.length = P.lay.lk + 4 ∧
      mergeDraws P.lay.lk ((rs.take (2 + P.lay.lk)).map (·.drawn)) = some (sigma, wo.rm) ∧
      wo.recs = mergeRecs P.lay #[claim] sigma wo.rm := by
  obtain ⟨a, tp, claim, x, wo, F, ha, _, _, ht, hc, _, hm, _, rfl⟩ := (decide_iff P s s' rs).1 h
  obtain ⟨sigma, hS, hr⟩ := mergeHear_recs hm
  have e := mergeTapeE_sampled ht
  have hl : rs.length = P.lay.lk + 4 := by
    have h1 := hS.closes
    have h2 := congrArg List.length e
    simp only [tapeSampled, sampledRV, List.length_map] at h2
    rw [← h2, h1]
    rfl
  exact ⟨a, _, claim, wo, sigma, ha, hc, rfl, rfl, hl, mergeDraws_of_tape hS e, hr⟩

/-- **THE SAME AT THE CHAIN's OWN ROUNDS.** rs: the chain's rounds. a, len: where the sub-protocol's
slice begins, and its length. The decision is handed the slice as `Block.step` hands it on. -/
theorem headMerge_at_chain {P : HeadMergeP} {s s' : S} {rs : List Fmt.RoundView} {a len : Nat}
    (h : headMergeDecide P s (((rs.drop a).take len).map noDigest) = .ok s') :
    ∃ (o o' : First.HeadOwn) (claim : WsClaim) (wo : WsForkOut) (sigma : E),
      s.here = .head o ∧ o.claim = some claim ∧ s'.here = .head o' ∧ o'.wo = some wo ∧
      leftHead s' = some wo ∧
      mergeDraws P.lay.lk (((rs.drop a).take (2 + P.lay.lk)).map (·.drawn)) =
        some (sigma, wo.rm) ∧
      wo.recs = mergeRecs P.lay #[claim] sigma wo.rm := by
  obtain ⟨o, o', claim, wo, sigma, h1, h2, h3, h4, hl, h5, h6⟩ := headMerge_draws h
  have hL : leftHead s' = some wo := by
    unfold leftHead
    rw [h3]
    exact h4
  refine ⟨o, o', claim, wo, sigma, h1, h2, h3, h4, hL, ?_, h6⟩
  have hle : 2 + P.lay.lk ≤ len := by
    simp only [List.length_map, List.length_take] at hl
    omega
  rw [← List.map_take, mergeDraws_noDigest, List.take_take, Nat.min_eq_left hle] at h5
  exact h5

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.mergeTapeE_sampled
#print axioms VerifiableInference.Desc.K13.Honest.sampled_flat
#print axioms VerifiableInference.Desc.K13.Honest.mergeDraws_of_sampled
#print axioms VerifiableInference.Desc.K13.Honest.mergeDraws_of_tape
#print axioms VerifiableInference.Desc.K13.Honest.mergeDraws_at_chain
#print axioms VerifiableInference.Desc.K13.Honest.headMerge_draws
#print axioms VerifiableInference.Desc.K13.Honest.headMerge_at_chain
