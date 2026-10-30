-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/GoodAll.lean: the proofs of `MergeShapeOk`, `MergeStated`,
`MergeBetaMarked`, `MergeSumMember` and `HeadMergeGoodAll`
(Honest/K11/Plays/GoodAllStatement.lean), to the letter. Lemmas; none of the library's goals.

How. The shape: by evaluation at a list of lk like variables. What the rounds state, and the mark:
the merge's entries behind the batching round agree with the call's own entries in what each test
reads (`statedBy_like`, Honest/SumLaw/Fits.lean, with `sumEntries_like`,
Honest/K11/Plays/Proofs.lean; `betaMarked_of_like`, Honest/SumLaw/BetaMarked.lean). The members: the
block's rounds beside as many empty lists of oracle messages (`zip_none`, Proofs.lean), cut as the
frame cuts a row. `Good`: `headMergeGood` (Good.lean of this folder), its premise on the row's
member number 1 by `exact_sumPart_field` (Honest/SumLaw/SumExact.lean) at that member; the lens is
the unit's: its two laws hold by definition.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.GoodAllStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.Good
import Johnson.Desc.ProofFile.Honest.SumLaw.SumExact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Claim Oracle)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Part.MaskedSum (shapeOk entries)
open Johnson.Desc.First.ForkMerge (HeadMergeP headClaimMergeKind mergeEntries)
open ProofFile.Honest.SumLaw (StatedBy statedBy_like betaMarked betaMarked_of_like lift_moves_count
  exact_sumPart_field)

/-- **The shape passes.** -/
theorem mergeShapeOk : MergeShapeOk := by
  intro lk
  simp [shapeOk, headMergeShape, List.all_replicate]
  exact Or.inr (by decide)

/-- **The rounds state just the call's scalars.** -/
theorem mergeStated : MergeStated := by
  intro lk work
  exact statedBy_like (headMergeShape lk) _ (sumEntries_like lk work) (by
    intro r hr
    obtain ⟨e, _, rfl⟩ := List.mem_map.1 hr
    rfl)

/-- **The further variable's challenge is marked as never 0.** -/
theorem mergeBetaMarked : MergeBetaMarked := by
  intro lk work
  refine betaMarked_of_like (headMergeShape lk) _ ?_
  simp [sumRounds, mergeEntries, entries, headMergeShape,
    VerifiableInference.Desc.Part.MaskedSum.entry, List.map_replicate]
  exact ⟨rfl, rfl⟩

/-- **The side's members.** -/
theorem mergeSumMember : MergeSumMember := by
  intro W₀ Rc Xi Tr X σ P claims weights name hb hr
  have hmv : (headMergeSum (Rc := Rc) (Tr := Tr) (X := X) P claims weights).moves.length =
      P.lay.lk + 3 := by
    show ((sumPart (V := Unit) _ _ (headMergeJob P.lay)).lift _ _ _ _).moves.length = _
    rw [lift_moves_count]
    show (List.replicate P.lay.lk _).length + 3 = _
    rw [List.length_replicate]
  have hlen : (sumRounds P.lay.lk P.work).length = P.lay.lk + 3 := by
    have := mergeEntries_length P.lay.lk 1 P.work
    simp only [sumRounds, List.length_map, List.length_tail]
    omega
  have hz : σ.block.rounds.zip σ.block.oracles =
      (headMergeFirst P, []) :: sumRounds P.lay.lk P.work := by
    rw [hb]
    show ((mergeEntries P.lay.lk 1 P.work).map fun e => ({ entry := e } : Fmt.DeclaredRound)).zip
      (List.replicate (P.lay.lk + 4) ([] : List Oracle)) = _
    rw [← mergeEntries_length P.lay.lk 1 P.work, zip_none]
    rfl
  refine ⟨headMergeFirst P, by simp [headMergeFirst, Fmt.DeclaredRound.items, Fmt.Entry.cut], ?_⟩
  unfold Side.members
  rw [hz, hr]
  show [_, (⟨1, (sumRounds P.lay.lk P.work).take
    (headMergeSum (Rc := Rc) (Tr := Tr) (X := X) P claims weights).moves.length, _, _⟩ :
      Member _ _ _ _)] = _
  rw [hmv, ← hlen, List.take_length]
  rfl

/-- **`Good`, with no premise on the sumcheck's part.** -/
theorem headMergeGoodAll : HeadMergeGoodAll := by
  intro W₀ Rc Xi Tr X σ φ Bk ord chain firstTree pre P claims weights name hb hr hown
  refine headMergeGood W₀ Rc Xi Tr X σ φ Bk ord chain firstTree pre P claims weights name hb hr hown
    ?_
  intro u hu hn
  obtain ⟨d₀, _, hm⟩ := mergeSumMember W₀ Rc Xi Tr X σ P claims weights name hb hr
  rw [hm] at hu
  rcases List.mem_cons.1 hu with rfl | h1
  · cases hn
  · obtain rfl := List.mem_singleton.1 h1
    intro ca m front ds asks hseen hd hh hs
    exact exact_sumPart_field φ σ chain firstTree (fun _ _ _ _ => True) (fun _ _ _ => True)
      (fun _ => ()) _ (fun _ => ()) (fun x _ => x) (fun _ _ => rfl) (fun _ => rfl) _ _
      (headMergeJob P.lay) (mergeShapeOk P.lay.lk) (sumRounds P.lay.lk P.work)
      (mergeStated P.lay.lk P.work) (mergeBetaMarked P.lay.lk P.work) 1 ⟨headMergePlace P, 1⟩
      ca m front ds asks trivial hseen hd trivial hh hs

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.mergeShapeOk
#print axioms ProofFile.Honest.K11.mergeStated
#print axioms ProofFile.Honest.K11.mergeBetaMarked
#print axioms ProofFile.Honest.K11.mergeSumMember
#print axioms ProofFile.Honest.K11.headMergeGoodAll
