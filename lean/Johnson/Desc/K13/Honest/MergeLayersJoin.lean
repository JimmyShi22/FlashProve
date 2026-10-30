-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/MergeLayersJoin.lean: THE LAYERS' SITES: WHAT A LAW ON THE CLAIMS THAT RUNS
FROM THE HEARING's OWN RETURN WANTS BESIDE `layers_at_chain` (MergeLayers.lean of this folder): the
tape's rounds against the challenges, round by round; the number in another writing; the challenges
in front of the batching round, cut at the sub-protocol's first round; the slots' number. Statements
with their proofs. It stands on MergeLayers.lean and the library alone.

Why. The first clause of `ClaimsIs` (PileDefs.lean) asks that the claims be a function of the
instance and of the challenges in front of the merge's batching round. A law toward it that runs
from a return of `hear engFl` on a tape t asks of t: "round number n of t has sampled the elements
of challenge number n", in the library's `drawnOf` (OnBytes/Desc/First/P1/TapeCut.lean); and it
reads the challenges as a list h in front of the sub-protocol, then a prefix of the sub-protocol's
own.
Main names:
  `drawnOf_of_sampled`: **where a tape's rounds sampled what rs sampled (`tapeSampled t = sampledRV
    rs`): for each n, `drawnOf (t.drop n)` is the elements of challenge number n of rs.**
  `layersSigmaAt_eq`: the number, written as the sum of the stretches in front: `k0 g` + 2, then the
    six masked sumchecks' stretches.
  `heard_split`: the challenges of the chain's first a + n rounds are those of its first a, then the
    first n of the slice's.
  `mergeDraws_length`: where `mergeDraws` returns it was handed just 2 + lk challenges.
  `mergeSlots_size`: from a return of the hearing: the merge was handed as many slots as the plan
    has claims.
  `layers_join`: **all of it from one return of the decision of the layers' own sub-protocol at the
    verifier's state (`blockAtS`) on a slice of the chain's rounds as `Block.step` hands it on**:
    ONE o, ONE tape: the hearing's own equation; the tape against the slice's challenges; the slice
    reaches behind the merge's first 2 + lk rounds; the cut of the challenges; and the second, third
    and fourth clauses of `ClaimsIs`.

What is not claimed. The first clause of `ClaimsIs`. Of what such a law may ask besides, nothing is
shown here: that the ledger in front has its sizes; that as many rounds stand in front of the slice
as public data say; what the lookup returned; that the state's tokens are the instance's. Nothing on
soundness, completeness or hiding.

-/
import Johnson.Desc.K13.Honest.MergeLayers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Fork WsClaim)
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.Desc.First.P1 (drawnOf)
open OnBytes.Road.K4 (own_callsG ksOf)
open VerifiableInference.Desc (noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.MergeLaw (hear_of_flat hear_tests)
open Johnson.Desc.First.Walk (leftLay)

/-- **The tape's rounds against the challenges, round by round.** -/
theorem drawnOf_of_sampled {t : Tape} {rs : List Fmt.RoundView} (h : tapeSampled t = sampledRV rs)
    (n : ℕ) (d : Fmt.Drawn) (hn : (rs.map (·.drawn))[n]? = some d) :
    drawnOf (t.drop n) = d.elems.map E.ofTriple := by
  have e1 : drawnOf (t.drop n) = ((tapeSampled t)[n]?).getD [] := by
    unfold drawnOf tapeSampled
    rw [List.head?_drop, List.getElem?_map]
  rw [List.getElem?_map] at hn
  obtain ⟨r, hr, rfl⟩ := Option.map_eq_some_iff.1 hn
  rw [e1, h]
  unfold sampledRV
  rw [List.getElem?_map, hr]
  rfl

/-- The number, written as the sum of the stretches in front. -/
theorem layersSigmaAt_eq (P : Pub) (hp : HPlan2) (g : Nat) :
    layersSigmaAt P hp g =
      k0 g + 2 + (P.rd.muV + 5) + (P.y.h.lt + 3) + (P.y.h.lt + 4) + (hp.lamS + 3) +
        (P.rd.muH + 5) + (P.rd.muH2 + 4) := by
  show k0 g + (P.rd.muV + P.y.h.lt + P.y.h.lt + hp.lamS + P.rd.muH + P.rd.muH2 + 26) = _
  omega

/-- The challenges of the chain's first a + n rounds: those of its first a, then the first n of the
slice's. -/
theorem heard_split (rs : List Fmt.RoundView) (a len n : Nat) (h : n ≤ len) :
    (rs.take (a + n)).map (·.drawn) =
      (rs.take a).map (·.drawn) ++ (((rs.drop a).take len).map (·.drawn)).take n := by
  rw [List.take_add, List.map_append, ← List.map_take, List.take_take, Nat.min_eq_left h]

/-- Where it returns it was handed just 2 + lk challenges. -/
theorem mergeDraws_length {lk : Nat} {own : List Fmt.Drawn} {y : E × Array E}
    (h : mergeDraws lk own = some y) : own.length = 2 + lk := by
  unfold mergeDraws at h
  split at h
  · rename_i h0
    rw [Bool.and_eq_true] at h0
    simpa using h0.1
  · cases h

/-- **From a return of the hearing: as many slots as the plan has claims.** -/
theorem mergeSlots_size {P : Pub} {hp : HPlan2} {g : Nat} {fo : OnBytes.Model.Forest.Heard}
    {F G : Fork} {t0 u : Tape} {o : Own} (h : hear engFl P hp g fo F t0 = some (o, G, u)) :
    (mergeSlots hp g o).size = hp.NCL := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, cl, _, _, _, _, _, _, _, _, _,
    _, _, _, _, hsz, hff, _, _⟩ := own_callsG h
  have h2 := (hear_tests (hear_of_flat hff)).1
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  rw [h2.2, hsz]

/-- **ALL OF IT FROM ONE RETURN.** rs: the chain's rounds. a, len: where the sub-protocol's slice
begins, and its length. ONE o and ONE tape throughout. -/
theorem layers_join {p : Par} {s s' : S} {rs : List Fmt.RoundView} {a len : Nat}
    {cols : List (List (Nat × List UInt64))}
    (h : (blockAtS p).decide s (((rs.drop a).take len).map noDigest) cols = .ok s') :
    ∃ (y : First.LayOwn) (fo : OnBytes.Model.Forest.Heard) (G : Fork) (o : Own)
      (cl : Array WsClaim) (sigma : E),
      s.here = .lay y ∧ y.fo = some fo ∧ s'.own? = some o ∧
      hear engFl { p.P with tokv := s.tokv } p.hp p.g fo y.F
        (paired (((rs.drop a).take len).map noDigest) (entries p.P p.hp p.g)) = some (o, G, []) ∧
      (∀ (n : ℕ) (d : Fmt.Drawn), (((rs.drop a).take len).map (·.drawn))[n]? = some d →
        drawnOf ((paired (((rs.drop a).take len).map noDigest) (entries p.P p.hp p.g)).drop n) =
          d.elems.map E.ofTriple) ∧
      layersSigmaAt p.P p.hp p.g + (2 + p.P.wsLay.lk) ≤
        (((rs.drop a).take len).map (·.drawn)).length ∧
      (rs.take (a + layersSigmaAt p.P p.hp p.g)).map (·.drawn) =
        (rs.take a).map (·.drawn) ++
          (((rs.drop a).take len).map (·.drawn)).take (layersSigmaAt p.P p.hp p.g) ∧
      mergeClaims { p.P with tokv := s.tokv } p.g o = some cl ∧ cl.size = p.hp.NCL ∧
      mergeDraws p.P.wsLay.lk
        (((rs.drop (a + layersSigmaAt p.P p.hp p.g)).take (2 + p.P.wsLay.lk)).map (·.drawn)) =
          some (sigma, o.wo.rm) ∧
      leftLay s' = some o.wo ∧ o.wo.recs = mergeRecs p.P.wsLay cl sigma o.wo.rm := by
  obtain ⟨o, cl, sigma, ho, ⟨y, fo, G, hy, hfo, hh⟩, h1, h2, h3, h4, h5⟩ := layers_at_chain h
  have hs : tapeSampled (paired (((rs.drop a).take len).map noDigest) (entries p.P p.hp p.g)) =
      sampledRV ((rs.drop a).take len) := (paired_sampled _ _).trans (sampledRV_noDigest _)
  obtain ⟨_, _, _, _, h3', _⟩ := hear_draws (rs := (rs.drop a).take len) hh hs
  have hl := mergeDraws_length h3'
  have hl' : layersSigmaAt p.P p.hp p.g + (2 + p.P.wsLay.lk) ≤ ((rs.drop a).take len).length := by
    have e : layersSigmaAt { p.P with tokv := s.tokv } p.hp p.g = layersSigmaAt p.P p.hp p.g := rfl
    have e' : ({ p.P with tokv := s.tokv } : Pub).wsLay.lk = p.P.wsLay.lk := rfl
    rw [e, e'] at hl
    simp only [List.length_map, List.length_take, List.length_drop] at hl ⊢
    omega
  have hlen : layersSigmaAt p.P p.hp p.g ≤ len := by
    simp only [List.length_take] at hl'
    omega
  exact ⟨y, fo, G, o, cl, sigma, hy, hfo, ho, hh, drawnOf_of_sampled hs,
    by rw [List.length_map]; exact hl', heard_split rs a len _ hlen, h1, h2, h3, h4, h5⟩

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.drawnOf_of_sampled
#print axioms VerifiableInference.Desc.K13.Honest.layersSigmaAt_eq
#print axioms VerifiableInference.Desc.K13.Honest.heard_split
#print axioms VerifiableInference.Desc.K13.Honest.mergeDraws_length
#print axioms VerifiableInference.Desc.K13.Honest.mergeSlots_size
#print axioms VerifiableInference.Desc.K13.Honest.layers_join
