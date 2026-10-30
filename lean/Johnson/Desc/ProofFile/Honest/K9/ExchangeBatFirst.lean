-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/ExchangeBatFirst.lean: `ExchangeS` AT THE 25 BATCHINGS OF THE FIRST CHAIN's THREAD (`firstThread`, Honest/Thread/TheFirstThread.lean), WHOLE, under the head at
the return alone. It is `k9_exchangeS_bat` (Honest/K9/ExchangeAtHead.lean) at the thread's own letters. That theorem's one named premise, a condition on the letter test, is paid here: at the
member behind a batching the thread's test is the list of falls at that place, and K9's fall and the smallness test's stand in that list.

  `behind_places`     the written list's place at the member behind each batching
  `first_tests`       where the thread's test is silent at a segment, K9's share and the smallness test's are
  **`k9_exchangeS_bat_first`**   `ExchangeS (firstThread h parts w) Said (14 l + IM.nAt l + 2)`, l < 25, where Said gives SaidOk

Limits. An implication. That the thread stands in front of a batching at a run is not shown here. No property of a prover or a protocol is proved here.
-/
import Johnson.Desc.ProofFile.Honest.K9.ExchangeAtHead
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K8 (k8Share)

set_option maxRecDepth 1000000 in
/-- The written list's place at the member behind each batching. -/
theorem behind_places : ((List.range 25).all fun l =>
    P5J.At.ps[14 * l + IM.nAt l + 3]? == some (K8.quietPlace l (oAt l))) = true := by
  decide +kernel

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **Where the thread's test is silent at a segment, K9's share and the smallness test's are.** -/
theorem first_tests (h : HeadAtReturn files A) (parts : FirstThreadParts A) (l : ℕ)
    (ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere) (Bs : ProofFile.PureBase) (Xl : OnBytes.Model.Stages.LinkH) (hl : l < 25)
    (hw : Desc.K9.testsWhere A.Z.p.X l 0 = some ww)
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs) (hX : Bs.G₀.built[l]? = some Xl) (e : P5J.TS)
    (he : fallsAfterBatching (firstFalls A parts.numbers) h.firstChain l e = none) :
    freeSlotShare ww.2.2.filled e = none ∧ k8Share (ProofFile.k8NU Bs.G₀ Xl) e = none := by
  have eG := seatGround_of_base hB
  obtain ⟨Lk, p, w', Qc, bE, bS, Sd, -⟩ := seats_at_head h.head hl
  obtain ⟨b, hb, hp, -⟩ := Sd.behind
  have hk : P5J.At.ps[14 * l + IM.nAt l + 3]? = some (K8.quietPlace l (oAt l)) :=
    beq_iff_eq.1 (List.all_eq_true.1 behind_places l (List.mem_range.2 hl))
  have ep : blockPlaces h.firstChain.blocksInOrder = P5J.At.ps := P5J.At.places_paid h.head.scope h.head.reads h.head.laid
  have hq : P5J.At.ps[14 * l + IM.nAt l + 3]? = some b.place := by
    rw [← ep]
    unfold blockPlaces
    rw [List.getElem?_map, hb]
    rfl
  have hk8 : K8.quietPlace l (oAt l) = b.place := Option.some.inj (hk.symm.trans hq)
  refine ⟨quiet_of_fallsAfterBatching hl hb Sd.numbers hw hp.symm he, ?_⟩
  have hX' : (seatGround A).built[l]? = some Xl := by
    rw [eG]
    exact hX
  have hs := share_of_fallsAfterBatching hl hb hX' hk8 he
  rw [eG] at hs
  exact hs

/-- **`ExchangeS` whole at each batching of the first thread.** -/
theorem k9_exchangeS_bat_first (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (l : ℕ) (hl : l < 25) : ExchangeS (firstThread h parts w) Said (14 * l + IM.nAt l + 2) :=
  k9_exchangeS_bat h.head A.H parts.script _ _ _ _ _ _ w _ _ _ _
    (fun _ _ _ hK hFo => ⟨⟨⟨⟨⟨hK, hFo⟩, trivial⟩, trivial⟩, trivial⟩, trivial⟩)
    (fun _ _ _ _ hK => hK.1.1.1.1.1) Said hSaid
    (fun l ww Bs Xl hl hw hB hX e he => first_tests h parts l ww Bs Xl hl hw hB hX e he) l hl

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.behind_places
#print axioms ProofFile.Honest.K9.first_tests
#print axioms ProofFile.Honest.K9.k9_exchangeS_bat_first
