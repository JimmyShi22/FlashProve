-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadKeepsJ.lean: the column `hK` of the gathering
(`owesS_head_cells`, GatherHeadCells.lean) at `f := fHead` (FHead.lean), for the code switch (K2):
the first places of segments 1 to 23, number 339 and number 353. 25 of the 358 numbers.
K2AtHead.lean and K2AtHeadH.lean say what an accepting step gives there. Here that is brought into
the arm of `fHead`. At the 23 first places `keepsOpenedR_of` (OpenedKeepsR.lean) gives the second
half of the arm. Each lemma has the form that `head_hK_of_families` (SteppedYes.lean) takes. No
definition.

  1  `fHead_keeps_k2_link`, `fHead_keeps_k2_head`, `fHead_keeps_k2_finish`   the three lemmas

Limits.
  * No hypothesis beside the library's `AtMgA` and the range of the segment's number. That a
    `StepYes` exists at any state is not shown.
  * Full size only, at the hash function `secondHashFunction` (FirstAt.lean says which that is).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FHead
import Johnson.Desc.ProofFile.Honest.Thread.HeadPlaceAt
import Johnson.Desc.ProofFile.Honest.Thread.K2AtHead
import Johnson.Desc.ProofFile.Honest.Thread.K2AtHeadH
import Johnson.IMR.SendsK2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Place KindName)
open VerifiableInference.Desc.First (kindsBeforeBatching blockPlaces)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open Johnson.Desc.First.Walk.Tied (StepYes)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) (take : Nat → Bool)
  (P11 : Johnson.Desc.First.ForkMerge.HeadMergeP) (p12 : VerifiableInference.Desc.K12.P12)
  (P13 : VerifiableInference.Desc.K13.Where)

include h

/-- At the first place of segment `l`, for `l` from 1 to 23. -/
theorem fHead_keeps_k2_link {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24) :
    ∀ blk, cF.blocksInOrder[14 * l + 0 + 2]? = some blk → ∀ s s', StepYes 0 blk s s' →
      fHead Zp cF G take P11 p12 P13 blk.place.kind blk.place s s' := by
  intro blk hb s s' hy
  have hk : (kindsBeforeBatching (IM.subAt l) (l == 0))[0]? = some KindName.K2 := by
    have hl0 : (l == 0) = false := beq_eq_false_iff_ne.2 (by omega)
    rw [hl0]
    unfold IM.subAt
    rw [if_neg (by omega)]
    split <;> rfl
  rw [head_place_hear h (by omega) hk hb]
  obtain ⟨m, q, fs, f, hq, hK, hfs, hf, ho, h0⟩ := k2_link_head h h1 h24 blk hb s s' hy
  exact (fHead_K2_link Zp cF G take P11 p12 P13
    (p := { chain := 1, link := some l, piece := 0 + 1, kind := .K2 }) (l := l) rfl (by omega) s
    s').2 ⟨m, ⟨q, hq, hK⟩, keepsOpenedR_of hfs hf ho h0⟩

/-- At number 339, in the output head's segment. -/
theorem fHead_keeps_k2_head :
    ∀ blk, cF.blocksInOrder[339]? = some blk → ∀ s s', StepYes 0 blk s s' →
      fHead Zp cF G take P11 p12 P13 blk.place.kind blk.place s s' := by
  intro blk hb s s' hy
  have hb' : cF.blocksInOrder[14 * 24 + 1 + 2]? = some blk := hb
  rw [head_place_hear h (l := 24) (i := 1) (k := .K2) (by decide) rfl hb']
  exact (fHead_K2_head Zp cF G take P11 p12 P13
    (p := { chain := 1, link := some 24, piece := 1 + 1, kind := .K2 }) rfl s s').2
    (k2_head_head h blk hb s s' hy)

/-- At number 353, after the last segment. -/
theorem fHead_keeps_k2_finish :
    ∀ blk, cF.blocksInOrder[353]? = some blk → ∀ s s', StepYes 0 blk s s' →
      fHead Zp cF G take P11 p12 P13 blk.place.kind blk.place s s' := by
  intro blk hb s s' hy
  have e : blockPlaces cF.blocksInOrder = P5J.At.ps := P5J.At.places_paid h.scope h.reads h.laid
  have e' : IM.placesW = P5J.At.ps := HashBuild.placesW_full
  have hp : (blockPlaces cF.blocksInOrder)[353]? = some blk.place := by
    unfold blockPlaces
    rw [List.getElem?_map, hb]
    rfl
  rw [e, ← e', IM.place_353] at hp
  rw [← Option.some.inj hp]
  exact (fHead_K2_finish Zp cF G take P11 p12 P13
    (p := { chain := 1, link := none, piece := 1, kind := .K2 }) rfl s s').2
    (k2_finish_head h blk hb s s' hy)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.fHead_keeps_k2_link
#print axioms ProofFile.Honest.FirstThread.fHead_keeps_k2_head
#print axioms ProofFile.Honest.FirstThread.fHead_keeps_k2_finish
