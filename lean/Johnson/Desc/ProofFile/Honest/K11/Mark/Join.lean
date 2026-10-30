-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Mark/Join.lean: the proofs of `HeadMergeLaterFit` and
`HeadMergeLiveOfSilent` (Honest/K11/Mark/JoinStatement.lean), to the letter. Lemmas; none of the
library's goals.

How. The last two of the kind's lk + 4 entries are written out. A drawn value that fits a round has
as many elements as the entry draws (`drawFit`, Honest/Frame.lean): one at the round in the further
variable, which reads other than 0 (`elemOf_ne_zero`, `firstMarked_of`,
Honest/SumLaw/BetaMarked.lean); none at the round of the end value. Then `headMergeMarkSilent`
(Proofs.lean of this folder) and `headMergeLiveBehind` (Johnson/Desc/K11/Live/Behind.lean).

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Mark.JoinStatement
import Johnson.Desc.ProofFile.Honest.K11.Mark.Proofs
import Johnson.Desc.K11.Live.Behind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (E)
open OnBytes.Model (Reading RoundName)
open ProofFile.Honest.SumLaw (elemOf elemOf_ne_zero firstMarked_of drawsFit_at)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind mergeEntries)
open Johnson.Desc.First.ForkMerge.Live (headMergeLiveBehind)

/-- Lists that fit are of one length: beyond the rounds there is no drawn value. -/
theorem fit_none : ∀ (Ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn), drawsFit Ds Rs = true →
    ∀ (i : Nat), Ds[i]? = none → ∀ (R : Fmt.Drawn), Rs[i]? = some R → False
  | [], [], _, _, _, _, h => by simp at h
  | [], _ :: _, h, _, _, _, _ => by simp [drawsFit] at h
  | _ :: _, [], h, _, _, _, _ => by simp [drawsFit] at h
  | _ :: _, _ :: _, _, 0, hn, _, _ => by cases hn
  | _ :: Ds, _ :: Rs, h, i + 1, hn, _, hR => by
    simp only [drawsFit, Bool.and_eq_true] at h
    exact fit_none Ds Rs h.2 i (by simpa using hn) _ (by simpa using hR)

/-- The kind's declared rounds from number lk + 2 on. -/
theorem rounds_drop (P : HeadMergeP) : (headClaimMergeKind P).rounds.drop (P.lay.lk + 2) =
    [{ entry := { name := RoundName.pscY.name, work := P.work, msg := 24, drawE := 1,
                  drawNZ := 1 } },
     { entry := { name := RoundName.pscValues.name, msg := 24 } }] := by
  show ((mergeEntries P.lay.lk 1 P.work).map fun e => ({ entry := e } : Fmt.DeclaredRound)).drop _ = _
  unfold mergeEntries
  rw [← List.map_drop]
  show ((List.replicate P.lay.lk _ ++ [_, _]).drop P.lay.lk).map _ = _
  rw [List.drop_left' (List.length_replicate ..)]
  rfl

/-- **The last two rounds' elements read other than 0.** -/
theorem headMergeLaterFit : HeadMergeLaterFit := by
  intro P rs hf i r hr hi e he
  obtain ⟨k, rfl⟩ : ∃ k, i = P.lay.lk + 2 + k := ⟨i - (P.lay.lk + 2), by omega⟩
  have hd : ((headClaimMergeKind P).rounds.drop (P.lay.lk + 2))[k]? =
      (headClaimMergeKind P).rounds[P.lay.lk + 2 + k]? := List.getElem?_drop
  rw [rounds_drop] at hd
  have hR : (rs.map (·.drawn))[P.lay.lk + 2 + k]? = some r.drawn := by
    rw [List.getElem?_map, hr]
    rfl
  match k, hd, hR with
  | 0, hd, hR =>
    obtain ⟨R, hR', hfit⟩ := drawsFit_at _ _ hf _ _ hd.symm
    obtain rfl : R = r.drawn := Option.some.inj (hR'.symm.trans hR)
    have hz := elemOf_ne_zero _ _ hfit (firstMarked_of _ rfl rfl rfl)
    have hlen : r.drawn.elems.length = 1 := by
      simp only [drawFit, Bool.and_eq_true, beq_iff_eq] at hfit
      exact hfit.1.1.1.1.1.1.1
    obtain ⟨t, ht⟩ := List.length_eq_one_iff.1 hlen
    rw [ht] at he
    obtain rfl := List.mem_singleton.1 he
    have e1 : elemOf r.drawn = E.ofTriple t := by
      unfold elemOf
      rw [ht]
      rfl
    rw [← e1]
    exact hz
  | 1, hd, hR =>
    obtain ⟨R, hR', hfit⟩ := drawsFit_at _ _ hf _ _ hd.symm
    obtain rfl : R = r.drawn := Option.some.inj (hR'.symm.trans hR)
    have hlen : r.drawn.elems.length = 0 := by
      simp only [drawFit, Bool.and_eq_true, beq_iff_eq] at hfit
      exact hfit.1.1.1.1.1.1.1
    rw [List.length_eq_zero_iff.1 hlen] at he
    simp at he
  | k + 2, hd, hR =>
    exfalso
    have hnone : (headClaimMergeKind P).rounds[P.lay.lk + 2 + (k + 2)]? = none := hd.symm
    exact fit_none _ _ hf _ hnone _ hR

/-- **The condition behind the decision's yes, where the mark says nothing.** -/
theorem headMergeLiveOfSilent : HeadMergeLiveOfSilent := by
  intro P fr s s' rs a x hs hf h ha hx hsv
  exact headMergeLiveBehind P s s' rs a x h ha hx hsv
    (headMergeMarkSilent P fr rs hs (headMergeLaterFit P rs hf))

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.headMergeLaterFit
#print axioms ProofFile.Honest.K11.headMergeLiveOfSilent
