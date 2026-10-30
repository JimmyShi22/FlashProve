-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/MergeLayers.lean: THE LAYERS' SITES: WHERE ON THE ROUNDS OF THE LAYERS' OWN
SUB-PROTOCOL (kind K4) THE MERGE OF THE CLAIMS ON THE WEIGHTS STANDS: A NUMBER MADE OF PUBLIC
NUMBERS; and `mergeDraws` (PileDefs.lean of this folder) there. Two definitions with code, and
statements with their proofs.

THE LIBRARY HAS THE PLACE. `own_callsG` (Johnson/Road/K4/OwnRecsG.lean): from a return of the
hearing `hear engFl`, in every group: the tape behind the gated layers is the cut `Ks.tcW` of the
tape less its first `k0 g` rounds: drops by public numbers alone
(OnBytes/Desc/First/P1/TailTape.lean); between that and the merge the text takes, in the first
group, one sent element off the merge's batching round itself (`mergeFront`; `claimsIn_spec`,
P1/BatchPoint.lean); then the merge's call `flatForkEnd` at the claims `mergeClaims P g o`.
`heard_reads` (Johnson/Desc/First/K4/ReadsAtS.lean): a return of the decision of the layers' own
sub-protocol at the verifier's state (`blockAtS`) is such a return, on the tape `paired rs …`, used
up. All are called. What is added: the sum of the drops as one number, and the meeting with
`MergeSampled` and `mergeDraws`.
Kin in the library of `leftLay_of_own`: the same step stands inside the proofs of `leftOf_of_own`
(Johnson/Road/K4/WoRowAt.lean) and of `kept_atS` (Road/K4/KeptAtS.lean), whose `KeptAtS` holds
leftLay s' = some o.wo from the same return, with the tape under "there are".
Main names:
  `tcWAt k`, `tcW_drop`: the cut `Ks.tcW` drops just k1 + … + k6 + 26 rounds.
  `layersSigmaAt P hp g`: **the number, from 0, of the merge's batching round among the rounds of
    the layers' own sub-protocol**: `k0 g` + that sum at K4's own numbers (`ksOf`): PUBLIC.
  `paired_sampled`, `putBack_sampled`: the layers' maker of a tape lays what the rounds sampled as
    it is; laying sent elements back leaves what was sampled.
  `hear_draws`: **from a return of the hearing on a tape whose rounds sampled what rs sampled**: the
    claims that the merge was handed are `mergeClaims P g o`; `mergeDraws` at the 2 + lk challenges
    of rs from number `layersSigmaAt` on returns the merge's batching element and o.wo.rm; o.wo.recs
    is `mergeRecs` at these.
  `leftLay_of_own`: what the merge left, off a state that holds what the layers' own rounds
    returned.
  `layers_at_chain`: **the same from a return of `blockAtS`'s decision on a slice of the chain's
    rounds as `Block.step` hands it on**: o IS WHAT THE STATE BEHIND HOLDS (s'.own? = some o) and
    what the hearing's own equation returns: so whoever shows the first clause of `ClaimsIs` of that
    o speaks of the same claims; what the merge left stands in the state behind (`leftLay`);
    `mergeDraws` at the chain's own rounds from number a + `layersSigmaAt` on: THE SECOND, THIRD AND
    FOURTH CLAUSES OF `ClaimsIs` at sigmaAt := that number and cl := `mergeClaims` at the state in
    front's tokens and at o.

What is not claimed. That `mergeClaims` at what was heard is any function of the instance and the
challenges: the first clause of `ClaimsIs`. That the sub-protocol at any number of a chain is
`blockAtS`. That what the merge left stays until the segment is cleared: kin in the library:
Johnson/Desc/First/Link/Law/OwnStay.lean (`SameOwn`, its keepers, `sameOwn_stretch`, `own_from_k4`),
`wrote_reads` (K4/ReadsAtS.lean). Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.K13.Honest.MergeRounds
import Johnson.Road.K4.OwnRecsG
import Johnson.Desc.First.K4.ReadsAtS
import Johnson.Desc.First.Walk.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Fork WsClaim)
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.Desc.First.P1 (Ks putBack claimsIn_spec)
open OnBytes.Road.K4 (own_callsG ksOf)
open VerifiableInference.Desc (noDigest)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk (leftLay)

/-- How many rounds the cut `Ks.tcW` drops. -/
def tcWAt (k : Ks) : Nat := k.k1 + k.k2 + k.k3 + k.k4 + k.k5 + k.k6 + 26

/-- The cut is one drop. -/
theorem tcW_drop (k : Ks) (t : Tape) : k.tcW t = t.drop (tcWAt k) := by
  unfold Ks.tcW Ks.tc6 Ks.tc5 Ks.tc4 Ks.tcP Ks.tc1 tcWAt
  simp only [List.drop_drop]
  congr 1
  omega

/-- **The number, from 0, of the merge's batching round among the rounds of the layers' own
sub-protocol.** -/
def layersSigmaAt (P : Pub) (hp : HPlan2) (g : Nat) : Nat := k0 g + tcWAt (ksOf P hp)

/-- The layers' maker of a tape, at every list of rounds and of entries. -/
theorem paired_sampled : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry),
    tapeSampled (paired rs es) = sampledRV rs
  | [], _ => rfl
  | r :: rs, [] => by
    show (flatOf r none).drawn :: tapeSampled (paired rs []) =
      r.drawn.elems.map E.ofTriple :: sampledRV rs
    rw [paired_sampled rs []]
    rfl
  | r :: rs, e :: es => by
    show (flatOf r (some e)).drawn :: tapeSampled (paired rs es) =
      r.drawn.elems.map E.ofTriple :: sampledRV rs
    rw [paired_sampled rs es]
    rfl

/-- Laying sent elements back leaves what was sampled. -/
theorem putBack_sampled (l : List E) : ∀ u : Tape, tapeSampled (putBack l u) = tapeSampled u
  | [] => rfl
  | _ :: _ => rfl

/-- **FROM A RETURN OF THE HEARING**, on a tape whose rounds sampled what rs sampled. -/
theorem hear_draws {P : Pub} {hp : HPlan2} {g : Nat} {fo : OnBytes.Model.Forest.Heard} {F G : Fork}
    {t0 u : Tape} {o : Own} (h : hear engFl P hp g fo F t0 = some (o, G, u)) {rs : List Fmt.RoundView}
    (ht : tapeSampled t0 = sampledRV rs) :
    ∃ (cl : Array WsClaim) (sigma : E), mergeClaims P g o = some cl ∧ cl.size = hp.NCL ∧
      mergeDraws P.wsLay.lk
        (((rs.drop (layersSigmaAt P hp g)).take (2 + P.wsLay.lk)).map (·.drawn)) =
          some (sigma, o.wo.rm) ∧
      o.wo.recs = mergeRecs P.wsLay cl sigma o.wo.rm := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, G4, G5, _, _, _, u4, u5, cl, _, _, _, _, _, _, _, _, _,
    _, hu4, hmf, hcl, hsz, hff, _, _⟩ := own_callsG h
  obtain ⟨sigma, hS, hr⟩ := flatForkEnd_recs hff
  have e5 : tapeSampled u5 = tapeSampled u4 := by
    unfold mergeFront at hmf
    split at hmf
    · obtain ⟨_, v, _, hv, _⟩ := claimsIn_spec hmf
      rw [hv, putBack_sampled]
    · rw [hmf.2.2]
  have e4 : tapeSampled u4 = sampledRV (rs.drop (layersSigmaAt P hp g)) := by
    rw [hu4, tcW_drop, List.drop_drop, sampledRV_drop, ← ht]
    unfold tapeSampled layersSigmaAt
    rw [List.map_drop]
  exact ⟨cl, sigma, hcl, hsz, mergeDraws_of_tape hS (e5.trans e4), hr⟩

/-- What the merge left, off a state that holds what the layers' own rounds returned. -/
theorem leftLay_of_own {s : S} {o : Own} (h : s.own? = some o) : leftLay s = some o.wo := by
  unfold VerifiableInference.Desc.First.S.own? at h
  unfold leftLay
  split at h
  · rename_i a ha
    rw [ha]
    show a.own.map (·.wo) = _
    rw [h]
    rfl
  · cases h

/-- **FROM A RETURN OF THE DECISION OF THE LAYERS' OWN SUB-PROTOCOL AT THE VERIFIER's STATE, AT THE
CHAIN's OWN ROUNDS.** rs: the chain's rounds. a, len: where the sub-protocol's slice begins, and its
length. o IS WHAT THE STATE BEHIND HOLDS, and what the hearing's own equation returns. -/
theorem layers_at_chain {p : Par} {s s' : S} {rs : List Fmt.RoundView} {a len : Nat}
    {cols : List (List (Nat × List UInt64))}
    (h : (blockAtS p).decide s (((rs.drop a).take len).map noDigest) cols = .ok s') :
    ∃ (o : Own) (cl : Array WsClaim) (sigma : E),
      s'.own? = some o ∧
      (∃ (y : First.LayOwn) (fo : OnBytes.Model.Forest.Heard) (G : Fork), s.here = .lay y ∧
        y.fo = some fo ∧
        hear engFl { p.P with tokv := s.tokv } p.hp p.g fo y.F
          (paired (((rs.drop a).take len).map noDigest) (entries p.P p.hp p.g)) =
            some (o, G, [])) ∧
      mergeClaims { p.P with tokv := s.tokv } p.g o = some cl ∧ cl.size = p.hp.NCL ∧
      mergeDraws p.P.wsLay.lk
        (((rs.drop (a + layersSigmaAt p.P p.hp p.g)).take (2 + p.P.wsLay.lk)).map (·.drawn)) =
          some (sigma, o.wo.rm) ∧
      leftLay s' = some o.wo ∧ o.wo.recs = mergeRecs p.P.wsLay cl sigma o.wo.rm := by
  obtain ⟨y, fo, o, G, hy, hfo, hh, ho, _⟩ := heard_reads h
  obtain ⟨cl, sigma, h1, h2, h3, h4⟩ := hear_draws (rs := (rs.drop a).take len) hh
    ((paired_sampled _ _).trans (sampledRV_noDigest _))
  refine ⟨o, cl, sigma, ho, ⟨y, fo, G, hy, hfo, hh⟩, h1, h2, ?_, leftLay_of_own ho, h4⟩
  have h3' : mergeDraws p.P.wsLay.lk
      (((((rs.drop a).take len).drop (layersSigmaAt p.P p.hp p.g)).take
        (2 + p.P.wsLay.lk)).map (·.drawn)) = some (sigma, o.wo.rm) := h3
  -- the slice's cut is the chain's: mergeDraws returns, so the 2 + lk rounds are there
  have hlen : ((((rs.drop a).take len).drop (layersSigmaAt p.P p.hp p.g)).take
      (2 + p.P.wsLay.lk)).length = 2 + p.P.wsLay.lk := by
    unfold mergeDraws at h3'
    split at h3'
    · rename_i h0
      rw [Bool.and_eq_true] at h0
      simpa using h0.1
    · cases h3'
  have hcut : (((rs.drop a).take len).drop (layersSigmaAt p.P p.hp p.g)).take
      (2 + p.P.wsLay.lk) =
      (rs.drop (a + layersSigmaAt p.P p.hp p.g)).take (2 + p.P.wsLay.lk) := by
    simp only [List.length_take, List.length_drop] at hlen
    rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]
  rw [← hcut]
  exact h3'

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.tcW_drop
#print axioms VerifiableInference.Desc.K13.Honest.paired_sampled
#print axioms VerifiableInference.Desc.K13.Honest.putBack_sampled
#print axioms VerifiableInference.Desc.K13.Honest.hear_draws
#print axioms VerifiableInference.Desc.K13.Honest.leftLay_of_own
#print axioms VerifiableInference.Desc.K13.Honest.layers_at_chain
