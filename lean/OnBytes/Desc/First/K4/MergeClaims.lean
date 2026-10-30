-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/K4/MergeClaims.lean: WHICH CLAIMS, UNDER WHICH SLOTS, THE LAYERS' OWN ROUNDS HAND
TO THE MERGE: as two plain functions of the public part and of what was heard; and the hearing
`hear` (OnBytes/Desc/First/K4/Hear.lean) over the plain engine, WHERE IT RETURNS: ITS CALLS THAT
HEAR, IN EVERY GROUP, ONE CHAIN OF LEDGERS AND TAPES, with these two functions at its end.
Definitions, two statements and their proofs.

  `mergeClaims P g o`: the claims, in the merge's order: what `weightClaims` returns at the plan's
    calls (OnBytes/Model/LayerPanels.lean:518), then, in the first group alone, what `claimE`
    returns (:494) at the two points o.H.ZE and o.H.tkh, the vocabulary's size and the request's
    tokens. none where one of these functions refuses. It follows K4/Hear.lean:186-190 line for
    line.
  `mergeSlots hp g o`: the slots, in the same order: o.K.sV + i for each of the panels' claims,
    then, in the first group alone, o.sVE. After K4/Hear.lean:192-193.
  WHAT THEY READ: of the public part: P.y through o.v, P.rd.tscCalls, P.wsLay, P.rope, P.V, P.tokv;
  hp.NCL. Of what was heard: o.v (`envOf`, HearParts.lean), o.K.rs, the end point of the second
  token sumcheck (o.H.tT), o.H.ZE, o.H.tkh; o.K.sV and o.sVE are numbers of slots.
  `mergeFront g o G4 u4 G5 u5`: what the text does between the gated layers and the merge: in the
    first group `Fl.claimsIn 1` takes (G4, u4) to (G5, u5) and returns o.sVE; in a later group
    nothing is done: o.sVE is 0, G5 is G4 and u5 is u4.
  `hear_parts`: in every group: if `hear engFl P hp g fo F t` returns (o, G, u), then the text
    covers the public record; o.v has the plan's layout and scales and the group's number; and, each
    from the ledger and the tape that the one in front has left: the norms' stretch from (F, t), the
    terms' sumcheck, the batched sumcheck, the two gated layers, `mergeFront`, and `flatForkEnd
    P.wsLay cl (mergeSlots hp g o)`, which returns (o.wo, G, u); cl is `mergeClaims P g o`, of
    hp.NCL claims.
  `hear_merge`: its last part alone; the ledger and the tape in front of the merge stand under
    "there are".

No new argument: `hear_parts_first`, `hear_parts_later` (HearParts.lean), told as one. One
direction: from a return. Nothing is said of what a claim or a part means. The ledgers and tapes
between the parts stand under "there are", ONE OF EACH FOR THE WHOLE CHAIN.
-/
import OnBytes.Desc.First.K4.HearParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated

/-- The claims that the layers' own rounds hand to the merge, in its order. -/
def mergeClaims (P : Pub) (g : Nat) (o : Own) : Option (Array WsClaim) :=
  (callsTS P).bind fun TS => ((envOf P o).weightClaims TS).bind fun cp =>
    (if (g == 0) = true then ((envOf P o).claimE o.H.ZE o.H.tkh P.V P.tokv).map ([·])
      else some []).map fun ce => (cp ++ ce).toArray

/-- The slots of their values, in the same order. -/
def mergeSlots (hp : HPlan2) (g : Nat) (o : Own) : Array Nat :=
  (Array.range (hp.NCL - (if (g == 0) = true then 1 else 0))).map (o.K.sV + ·) ++
    (if (g == 0) = true then #[o.sVE] else #[])

/-- What the text does between the gated layers and the merge. -/
def mergeFront (g : Nat) (o : Own) (G4 : Fork) (u4 : Tape) (G5 : Fork) (u5 : Tape) : Prop :=
  if (g == 0) = true then Fl.claimsIn 1 G4 u4 = some (o.sVE, G5, u5)
  else o.sVE = 0 ∧ G5 = G4 ∧ u5 = u4

/-- **The hearing's chain of calls, in every group**, where it returns. The text's public steps
that leave ledger and tape as they are go unsaid here, as in HearParts.lean. -/
theorem hear_parts {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {o : Own} (h : hear engFl P hp g fo F t = some (o, G, u)) :
    covers P = true ∧ o.v.y = P.y ∧ o.v.sc = P.sc ∧ o.v.g = g ∧
      ∃ (H1 : Heard) (hd2 : Level) (cl : Array WsClaim)
        (G1 G2 G3 G4 G5 : Fork) (u1 u2 u3 u4 u5 : Tape),
        hearNorms engFl P g fo F t = some (H1, G1, u1) ∧
        hearTerms engFl P H1 G1 u1 = some (o.H, G2, u2) ∧
        hearStack engFl P o.v o.H hp.lamS (hp.NCL - (if (g == 0) = true then 1 else 0)) G2 u2 =
          some (o.K, G3, u3) ∧
        hearGated engFl P o.H o.K G3 u3 = some ((o.hd, hd2), G4, u4) ∧ o.hd2 = some hd2 ∧
        mergeFront g o G4 u4 G5 u5 ∧
        mergeClaims P g o = some cl ∧ cl.size = hp.NCL ∧
        flatForkEnd P.wsLay cl (mergeSlots hp g o) G5 u5 = some (o.wo, G, u) := by
  by_cases hg : (g == 0) = true
  · obtain ⟨hc, ey, es, eg, H1, hd2, TS, cp, cE, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, h1, h2, h3,
      h4, e5, e7, e8, hcE, hs, d2, d3⟩ := hear_parts_first h hg
    refine ⟨hc, ey, es, eg, H1, hd2, (cp ++ [cE]).toArray, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5,
      h1, h2, ?_, h4, e5, ?_, ?_, hs, ?_⟩
    · rw [if_pos hg]
      exact h3
    · unfold mergeFront
      rw [if_pos hg]
      exact d2
    · unfold mergeClaims
      rw [e7, Option.bind_some, e8, Option.bind_some, if_pos hg, hcE]
      rfl
    · unfold mergeSlots
      rw [if_pos hg, if_pos hg]
      exact d3
  · have hg' : (g == 0) = false := by simpa using hg
    obtain ⟨hc, ey, es, eg, e0, H1, hd2, TS, cp, G1, G2, G3, G4, u1, u2, u3, u4, h1, h2, h3, h4, e5,
      e7, e8, hs, d3⟩ := hear_parts_later h hg'
    refine ⟨hc, ey, es, eg, H1, hd2, (cp ++ []).toArray, G1, G2, G3, G4, G4, u1, u2, u3, u4, u4,
      h1, h2, ?_, h4, e5, ?_, ?_, hs, ?_⟩
    · rw [if_neg hg]
      exact h3
    · unfold mergeFront
      rw [if_neg hg]
      exact ⟨e0, rfl, rfl⟩
    · unfold mergeClaims
      rw [e7, Option.bind_some, e8, Option.bind_some, if_neg hg]
      rfl
    · unfold mergeSlots
      rw [if_neg hg, if_neg hg]
      exact d3

/-- **What the layers' own rounds hand to the merge.** -/
theorem hear_merge {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {o : Own} (h : hear engFl P hp g fo F t = some (o, G, u)) :
    ∃ (cl : Array WsClaim) (G5 : Fork) (u5 : Tape),
      mergeClaims P g o = some cl ∧ cl.size = hp.NCL ∧
        flatForkEnd P.wsLay cl (mergeSlots hp g o) G5 u5 = some (o.wo, G, u) := by
  obtain ⟨_, _, _, _, _, _, cl, _, _, _, _, G5, _, _, _, _, u5, _, _, _, _, _, _, e, hs, d⟩ :=
    hear_parts h
  exact ⟨cl, G5, u5, e, hs, d⟩

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.hear_parts
#print axioms OnBytes.Desc.First.K4.hear_merge
