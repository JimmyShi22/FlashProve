-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/TypedV.lean: THE SEATED LINK AT THE TYPED PARAMETERS: callers for what
Johnson/Desc/K15/HsemAtV.lean proves, with every premise on the parameters paid (for the entry
file's condition):
  H_fullV_typed | H_smallV_typed     H_fullV | H_smallV at frP | srP: samples · S · codes by rfl;
  PubAt · OpensAt by Johnson/Desc/K15/PubAtTyped.lean (the kernel): TWO PREMISES ARE LEFT: the
  statement on codes (BCHKS46At, Cb/Gen/CodeListRSAt.lean) and the tie's SendPOfDecide
  fr_rounds | sr_rounds              the written rounds that a compiler takes of the description at
  frP | srP ARE the library's written constants frFmt | srFmt: evaluated by the kernel
  fr_ds | sr_ds · fr_xs | sr_xs      so its rounds' data and stored openings are the slot's letters
  dsFull | dsSmall · frD.xs | srD.xs
  linkOfFilesV_full | _small         at the root: a link made at the typed parameters IS linkDescriptionAt frP |
  srP … with these letters
NOT SHOWN HERE: that the parameters that RUN (p15Of c of the public files) are frP | srP: AT THE
FULL SIZE IT IS A LAW IN SCOPE: Johnson/Goal/Conditions/LinkTypedAtLines.lean (inScope_typed); at the
small example it is evaluated at one stored set; no theorem.
-/
import Johnson.Desc.K15.PubAtTyped
import Johnson.Desc.K15.HsemAtV
import Johnson.Desc.Link.OneSlotAt
import Johnson.Desc.Link.LinkVariantLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open H2K.Sw H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Cb Cb.Ood _root_.Run Blocks
open OnBytes.Params (recordRead smallRecordRead)
open VerifiableInference.Desc VerifiableInference.Desc.K12

section
open OnBytes.Flat TypedOracleCompiler.Slice OnBytes.Tie

set_option maxRecDepth 100000 in
theorem H_fullV_typed (hSP : SendPOfDecide) (hA : BCHKS46At GF GE) (plan : List Fmt.DeclaredRound)
    (ok : Bool) :
    ∀ x, (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) frD.xs
        (decDescFullV frP plan ok x)).Sound
      (fun _ y => frS.LangE2T frZ 402653181 (recOf frS 29 1 (anT frS.P.v 1) x) y)
      (0, coreErrR frS frZ (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frS.badJ frS.e0)
        (frS.badJ frS.e1)
        (fun _ => Cb.listMax (2 ^ frS.P.C.a) (2 ^ frS.P.C.a - (frS.P.C.r + frS.P.C.l) + 1) frS.eU)
        (batErrR frN ((frS.sg 97).lstJ frC.rad) (frRd 5), frC.errL)) :=
  H_fullV hSP hA frP plan ok rfl rfl rfl fr_pubAt fr_opensAt

set_option maxRecDepth 100000 in
theorem H_smallV_typed (hSP : SendPOfDecide) (hA : BCHKS46At GF GE) (plan : List Fmt.DeclaredRound)
    (ok : Bool) :
    ∀ x, (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) srD.xs
        (decDescSmallV srP plan ok x)).Sound
      (fun _ y => srS.LangE2T srZ 524285 (recOf srS 19 1 (anT srS.P.v 1) x) y)
      (0, coreErrR srS srZ (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srS.badJ srS.e0)
        (srS.badJ srS.e1)
        (fun _ => Cb.listMax (2 ^ srS.P.C.a) (2 ^ srS.P.C.a - (srS.P.C.r + srS.P.C.l) + 1) srS.eU)
        (batErrR srN ((srS.sg 97).lstJ srC.rad) (srRd 5), srC.errL)) :=
  H_smallV hSP hA srP plan ok rfl rfl rfl sr_pubAt sr_opensAt

end

theorem roundsOf_free (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool) (file : String) :
    (linkDescriptionAt P plan ok).roundsOf file = (linkDescriptionAt P [] true).roundsOf file := rfl

theorem xsTyped_free (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool) :
    (linkDescriptionAt P plan ok).xsTyped = (linkDescriptionAt P [] true).xsTyped := rfl

theorem ok_of_toOption {α : Type} (e : Except String α) (a : α) (h : e.toOption = some a) : e = .ok
    a := by
  cases e with
  | error _ => cases h
  | ok b => cases h; rfl

set_option maxRecDepth 100000 in
theorem fr_rounds (plan : List Fmt.DeclaredRound) (ok : Bool) :
    (linkDescriptionAt frP plan ok).roundsOf "entry file" = .ok OnBytes.Slice.frFmt := by
  rw [roundsOf_free]
  exact ok_of_toOption _ _ (by decide +kernel)

set_option maxRecDepth 100000 in
theorem sr_rounds (plan : List Fmt.DeclaredRound) (ok : Bool) :
    (linkDescriptionAt srP plan ok).roundsOf "entry file" = .ok OnBytes.Slice.srFmt := by
  rw [roundsOf_free]
  exact ok_of_toOption _ _ (by decide +kernel)

theorem xo_inj : Function.Injective (fun o : _root_.Run.PQ.XO =>
  (o.round, o.which, o.from_, o.count)) := by
  rintro ⟨a1, a2, a3, a4⟩ ⟨b1, b2, b3, b4⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rfl

set_option maxRecDepth 100000 in
theorem fr_xs (plan : List Fmt.DeclaredRound) (ok : Bool) : (linkDescriptionAt frP plan ok).xsTyped =
    OnBytes.Slice.frD.xs := by
  rw [xsTyped_free]
  exact List.map_injective_iff.2 xo_inj (by decide +kernel)

set_option maxRecDepth 100000 in
theorem sr_xs (plan : List Fmt.DeclaredRound) (ok : Bool) : (linkDescriptionAt srP plan ok).xsTyped =
    OnBytes.Slice.srD.xs := by
  rw [xsTyped_free]
  exact List.map_injective_iff.2 xo_inj (by decide +kernel)

theorem fr_ds (plan : List Fmt.DeclaredRound) (ok : Bool) : (linkDescriptionAt frP plan ok).dsOf "entry file" = .ok
    OnBytes.Flat.dsFull :=
  dsOf_full _ _ (fr_rounds plan ok)

theorem sr_ds (plan : List Fmt.DeclaredRound) (ok : Bool) : (linkDescriptionAt srP plan ok).dsOf "entry file" = .ok
    OnBytes.Flat.dsSmall :=
  dsOf_small _ _ (sr_rounds plan ok)

/-- **At the maker, full size**: whoever holds a link out of the root, made at the typed parameters,
holds the slot's three letters. -/
theorem linkOfFilesV_full (pol lay KL : ByteArray) (L : Link3) (h : linkOfFilesV pol lay KL = .ok L)
    :
    ∃ p plan, OnBytes.Model.Verify.planned pol KL (some lay) = .ok p ∧ Johnson.G.OfPlan.declLOf pol
        lay KL = .ok plan ∧
      (sameP (p15Of p.chains) frP = true →
        L.F = linkDescriptionAt frP plan (VerifiableInference.Desc.entryOk p.chains.made && tiesOk p.chains
                        plan) ∧
          L.ds = OnBytes.Flat.dsFull ∧ L.xs = OnBytes.Slice.frD.xs) := by
  obtain ⟨p, plan, hp, hplan, hF, _, hds, hxs⟩ := linkOfFilesV_ok pol lay KL L h
  refine ⟨p, plan, hp, hplan, fun hP => ?_⟩
  have hF' := hF.trans (linkDescV_frP p.chains plan hP)
  rw [hF'] at hds hxs
  refine ⟨hF', ?_, hxs.trans (fr_xs _ _)⟩
  rw [fr_ds] at hds
  injection hds with hds
  exact hds.symm

/-- **At the maker, the small example.** -/
theorem linkOfFilesV_small (pol lay KL : ByteArray) (L : Link3)
    (h : linkOfFilesV pol lay KL = .ok L) :
    ∃ p plan, OnBytes.Model.Verify.planned pol KL (some lay) = .ok p ∧ Johnson.G.OfPlan.declLOf pol
        lay KL = .ok plan ∧
      (sameP (p15Of p.chains) srP = true →
        L.F = linkDescriptionAt srP plan (VerifiableInference.Desc.entryOk p.chains.made && tiesOk p.chains
                        plan) ∧
          L.ds = OnBytes.Flat.dsSmall ∧ L.xs = OnBytes.Slice.srD.xs) := by
  obtain ⟨p, plan, hp, hplan, hF, _, hds, hxs⟩ := linkOfFilesV_ok pol lay KL L h
  refine ⟨p, plan, hp, hplan, fun hP => ?_⟩
  have hF' := hF.trans (linkDescV_srP p.chains plan hP)
  rw [hF'] at hds hxs
  refine ⟨hF', ?_, hxs.trans (sr_xs _ _)⟩
  rw [sr_ds] at hds
  injection hds with hds
  exact hds.symm

end Desc.K15

#print axioms Desc.K15.linkOfFilesV_full
#print axioms Desc.K15.linkOfFilesV_small
#print axioms Desc.K15.H_fullV_typed
#print axioms Desc.K15.H_smallV_typed
#print axioms Desc.K15.fr_rounds
#print axioms Desc.K15.sr_rounds
#print axioms Desc.K15.fr_xs
#print axioms Desc.K15.sr_xs
