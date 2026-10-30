-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/BehindValuesFirst.lean: the table's test at the member behind the batching, at the first
thread itself, with the falls that the first thread's own list holds: so the letter fall of
BehindValuesAt.lean is paid by the list, at every challenge list.

  silent_of_falls           a fall seated at a member says nothing where the list says nothing there
  quiet_place               the two names of the place behind a batching are one
  k8_behind_valuesJ_first   ValuesJ at the member behind the batching of segment l

Limits. Said is read through hOk. That a thread comes to such a stand is not shown. The fall's silence
stays a premise inside ValuesJ: that the fall is silent often is the falls' measure, not shown here.
-/
import AtFullSide.K8.BehindValuesAt
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8.Term
open VerifiableInference.Desc (Chain Place Block)
open P5J (TS)
open ProofFile.Honest
open ProofFile.Honest.FirstThread
open Johnson.AtFull.Shape (firstZA)

/-- **A fall seated at a member says nothing where the list says nothing there.** -/
theorem silent_of_falls {falls : List (Fall TS)} {bs : List (Block TS ProofFile.Cl)} {n : Nat} {s : TS}
    {ds : List Fmt.Drawn} {blk : Block TS ProofFile.Cl} (hb : bs[n]? = some blk)
    (h : fallsBy falls bs n s ds = none) {F : Fall TS} (hF : F ∈ falls)
    (hp : F.place = blk.place) : F.test s ds = none := by
  unfold fallsBy at h
  rw [hb] at h
  unfold fallOf at h
  rw [List.findSome?_eq_none_iff] at h
  exact h F (List.mem_filter.2 ⟨hF, by simp [hp]⟩)

set_option maxRecDepth 1000000 in
/-- The batching of each segment stands at its place in the written list. -/
theorem batch_places : ((List.range 25).all fun l =>
    P5J.At.ps[14 * l + (if l = 24 then 9 else 7) + 2]? == some (K8.batchPlace l (oAt l))) = true := by
  decide +kernel

/-- **The two names of the place behind a batching are one.** -/
theorem quiet_place {l : Nat} (hl : l < 25) {p : VerifiableInference.Desc.K9.Where}
    (hs : P5J.At.ps[14 * l + (if l = 24 then 9 else 7) + 2]? =
      some ⟨p.chain, some p.link, p.piece, .K9⟩) :
    K8.quietPlace l (oAt l) = K9.quietPlace p := by
  have t := List.all_eq_true.1 batch_places l (List.mem_range.2 hl)
  rw [hs] at t
  have e : (⟨p.chain, some p.link, p.piece, .K9⟩ : Place) = K8.batchPlace l (oAt l) := by
    simpa using t
  unfold K8.batchPlace at e
  simp only [Place.mk.injEq, Option.some.injEq] at e
  obtain ⟨e1, e2, e3, -⟩ := e
  unfold K8.quietPlace K9.quietPlace
  rw [e1, e2, e3]
  show (⟨1, some l, 9 + 2 * oAt l, _⟩ : Place) = ⟨1, some l, 8 + 2 * oAt l + 1, _⟩
  congr 1
  omega

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- **The table's test at the member behind the batching, at the first thread, at its own falls.** -/
theorem k8_behind_valuesJ_first (h : HeadAtReturn files A) (parts : FirstThreadParts A)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hOk : ∀ b k m, Said b k m → SaidOk b k m) (J : Nat → TS → Prop) {l : Nat} (hl : l < 25) :
    ValuesJ (firstThread h parts w) Said J
      (firstZA (Johnson.AtFull.Shape.Tab.g A.Z (seatGround A))
        (Johnson.AtFull.Shape.Tab.vals A.Z (seatGround A)))
      (fallsBy (firstFalls A parts.numbers) h.firstChain.blocksInOrder)
      (14 * l + (if l = 24 then 11 else 9) + 1) := by
  obtain ⟨Bs, base, O⟩ := h.head.laid.opened
  have eG : seatGround A = Bs.G₀ := seatGround_of_base O.made
  obtain ⟨Lk, p, u, Sd⟩ := K9.seated_at_head h.head l hl
  obtain ⟨blk, hblk, hpl, -⟩ := Sd.behind
  have en : 14 * l + (if l = 24 then 9 else 7) + 3 = 14 * l + (if l = 24 then 11 else 9) + 1 := by
    split <;> omega
  rw [en] at hblk
  have hs : P5J.At.ps[14 * l + (if l = 24 then 9 else 7) + 2]? =
      some ⟨p.chain, some p.link, p.piece, .K9⟩ := by
    have e := head_place h.head A.H parts.script (fun _ _ => none) (fun _ _ _ _ => True) 0 0 0 0
      (fun _ => True) (fun _ _ _ => True) (fun _ _ _ => True) w (b := _) Sd.batching
    rw [e, Sd.seat]
  have hq := quiet_place hl hs
  rw [firstThread_is]
  rw [show (firstZA (Johnson.AtFull.Shape.Tab.g A.Z (seatGround A))
      (Johnson.AtFull.Shape.Tab.vals A.Z (seatGround A))) =
      firstZA (Johnson.AtFull.Shape.Tab.g A.Z Bs.G₀) (Johnson.AtFull.Shape.Tab.vals A.Z Bs.G₀) by
    rw [eG]]
  refine k8_behind_valuesJ h.head O.made A.H parts.script _ _ _ _ _ _ _ _ _ _ w Said hOk J _ hl
    (fun u' hu' s ds hf => ?_) (fun Xl hX s ds hf => ?_)
  · obtain rfl : u = u' := Option.some.inj (Sd.tested.symm.trans hu')
    exact silent_of_falls hblk hf (fallsHead_quiet hl Sd.numbers Sd.tested) hpl.symm
  · have hX' : (seatGround A).built[l]? = some Xl := by
      rw [eG]
      exact hX
    have r := silent_of_falls hblk hf (fallsHead_share hl hX') (hq.trans hpl.symm)
    rw [← eG]
    exact r

end AtFullSide.K8.Term

#print axioms AtFullSide.K8.Term.silent_of_falls
#print axioms AtFullSide.K8.Term.batch_places
#print axioms AtFullSide.K8.Term.quiet_place
#print axioms AtFullSide.K8.Term.k8_behind_valuesJ_first
