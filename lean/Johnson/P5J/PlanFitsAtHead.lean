-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/PlanFitsAtHead.lean (kind K9): `PlanFits` (Johnson/Desc/First/Link/Law/PartFitsReached.lean: the closed sentence under K9's inSeg · inRun · inTot), WHOLE, AT THE CONSTANT's OWN LETTERS, AT THE THREE BORDERS A SEGMENT, FROM THE HEAD ALONE. Theorems: a join.

THE SEARCH FIRST. PlanSixAtMg.lean (beside this file) leaves one of the seven parts: «room»: ns + the answers ≤ the mask code's length, ns the planning program's number of slots of the BUILT segment, which no pin fixes. BUT THE PLANNER ITSELF TESTS JUST THAT OF EVERY SEGMENT (`linkLaid`, OnBytes/Model/StagesLinks.lean: "plan-mask-row"), AND
THE STONES LAY: `ProofFile.Law.built_head_ns` (Johnson/Desc/ProofFile/Law/HeadNs.lean): where the public part is computed, its built segments have passed `linksFit` at the first chain's parameters · `linksFit_ns` (Johnson/Desc/Kinds/Law/LinksFitNs.lean): so each has ns + answers ≤ the mask code's length. No pin, no written value, no kernel line.

What is said.
  `AtMg.room_of_built`: at any o: a built segment X at number m ⊢ X.ns + the answers ≤ the mask code's length, at At.foldD's own letters.
  `AtMgA.room_at`: m < 25 ⊢ the same at ns := At.nsAt Zp m (the wider head's option «built» says that the segment is there).
  `AtMgA.planFits_at`: **k ∈ bordersW · At.ps[k]? = some p · p.link = some m · m < 25 ⊢ PlanFits (At.foldD Zp cF LFull) (At.ms Zp Z.lay) ((At.N Zp cF).group m) m (the place's moment) ((At.N Zp cF).msgsAt At.ps[k]?) (At.nsAt Zp m).**

Limits. AtMgA is a premise («the head»: WITH THE FOURTEEN ENTRY TESTS; its options are paid at the top by others). AT THE SECOND HASH FUNCTION. The full size alone. One bent twin (the listed seats reversed: still accepted at 26 of 50 borders): the test is blind to something. Nothing on soundness.

-/
import Johnson.P5J.PlanSixAtMg
import Johnson.P5J.FoldMoreAt
import Johnson.P5J.MgAtAll
import Johnson.Desc.ProofFile.Law.HeadNs
import Johnson.Desc.Kinds.Law.LinksFitNs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Model
open VerifiableInference
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.First (momentAt shiftAt)
open VerifiableInference.Desc.LinkJoin (PlanFits)
open VerifiableInference.Desc.K13.Law (LFull)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **«room» OF A BUILT SEGMENT: THE PLANNER HAS TESTED IT.** -/
theorem AtMg.room_of_built {o : ProofFile.SecondHashFunctionArgument} (h : AtMg o Z D r Zp Np cF)
    (Ld : Desc.K12.Door.Laid) {m : ℕ} {X : Stages.LinkH}
    (hX : Zp.made.p.built.links[m]? = some X) :
    X.ns + (At.foldD Zp cF Ld).sent.shape.answers ≤
      ((At.foldD Zp cF Ld).sent.codes.mask.getD (At.foldD Zp cF Ld).sent.shape.maskCode
        default).ell := by
  obtain ⟨zk, hz, H⟩ := VerifiableInference.Desc.Kinds.Head.Law.OffPad.linksFit_ns
    (ProofFile.Law.built_head_ns h.laid.pub).1
  have hm : X ∈ Zp.p.built.links.toList := by
    have h1 : Zp.p.built.links[m]? = some X := hX
    rw [← Array.getElem?_toList] at h1
    exact List.mem_of_getElem? h1
  have h2 := H X hm
  show X.ns + Zp.first.shape.answers ≤
    (Zp.first.codes.mask.getD Zp.first.shape.maskCode default).ell
  have e : Zp.first.codes.mask.getD Zp.first.shape.maskCode default = zk := by
    rw [Array.getD_eq_getD_getElem?, hz]
    rfl
  rw [e]
  exact h2

/-- **«room» AT THE PLAN's OWN NUMBER OF SLOTS.** -/
theorem AtMgA.room_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Ld : Desc.K12.Door.Laid)
    {m : ℕ} (hm : m < 25) :
    At.nsAt Zp m + (At.foldD Zp cF Ld).sent.shape.answers ≤
      ((At.foldD Zp cF Ld).sent.codes.mask.getD (At.foldD Zp cF Ld).sent.shape.maskCode
        default).ell := by
  obtain ⟨X, hX⟩ := Option.isSome_iff_exists.1 (h.opts.builtAt m hm)
  have e : At.nsAt Zp m = X.ns := At.nsAt_of Zp (by unfold At.nsOf; rw [hX]; rfl)
  rw [e]
  exact h.toAtMg.room_of_built Ld hX

/-- **PlanFits, WHOLE, FROM THE HEAD ALONE.** -/
theorem AtMgA.planFits_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {k : ℕ}
    (hk : k ∈ P5T.bordersW) {p : Place} (hp : At.ps[k]? = some p) {m : ℕ} (hl : p.link = some m)
    (hm : m < 25) :
    PlanFits (At.foldD Zp cF LFull) (At.ms Zp Z.lay) ((At.N Zp cF).group m) m
      (momentAt (shiftAt At.links m) p.piece) ((At.N Zp cF).msgsAt At.ps[k]?) (At.nsAt Zp m) :=
  h.toAtMg.planFits_of_room hk hp hl (At.nsAt Zp m) (h.room_at LFull hm)

end P5J

#print axioms P5J.AtMg.room_of_built
#print axioms P5J.AtMgA.room_at
#print axioms P5J.AtMgA.planFits_at
