-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Link/LinkVariantLaw.lean: the seated link (Johnson/Desc/Link/LinkDesc.lean |
LinkOfFiles.lean; its names bear the letter V) at the files: what the middle term's small laws say
(Johnson/Desc/Link/LinkOfFilesLaw.lean · Johnson/Desc/K15/TypedP.lean), of the seated link;
and the tie at the files:
  descV_decl · descV_dsOf · descV_xsTyped     the two texts declare the same rounds: so the written
  rounds and the stored openings that a compiler takes are the same
  linkOfFilesV_ok                             what a yes of linkOfFilesV says: linkOfFiles_ok's
  words, of the root
  linkOfFilesV_under                          **where linkOfFilesV makes a link, linkOfFiles makes
  one, with the same written rounds and stored openings, and says yes wherever the root's says yes**
  plans_pricedV                               the declared rounds' entries of the seated text are
  the priced plan's: plans_priced's words, of the seated text; no premise
  linkDescV_frP | linkDescV_srP               at the typed parameters
linkOfFilesV_under stands UNDER THE TIE's ONE NAMED PREMISE SendPOfDecide; the others under none.
ONE DIRECTION ALONE.
-/
import Johnson.Desc.K15.SendOwnLaw
import Johnson.Desc.Link.LinkOfFilesLaw
import Johnson.Desc.K15.TypedP

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open OnBytes VerifiableInference.Desc

theorem descV_decl (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool) :
    (linkDescriptionAt P plan ok).roundsDeclaredByBlocks = (descOf P plan ok).roundsDeclaredByBlocks := alike_rounds _ _ (flat_alike P)

theorem descV_dsOf (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool) (file : String) :
    (linkDescriptionAt P plan ok).dsOf file = (descOf P plan ok).dsOf file := by
  unfold OneChainFileDescription.dsOf OneChainFileDescription.roundsOf OneChainFileDescription.written
  rw [descV_decl]

theorem descV_xsTyped (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool) :
    (linkDescriptionAt P plan ok).xsTyped = (descOf P plan ok).xsTyped := by
  unfold OneChainFileDescription.xsTyped
  rw [descV_decl]

theorem linkOfFilesV_ok (pol lay KL : ByteArray) (L : Link3) (h : linkOfFilesV pol lay KL = .ok L) :
    ∃ p plan, OnBytes.Model.Verify.planned pol KL (some lay) = .ok p ∧ Johnson.G.OfPlan.declLOf pol
        lay KL = .ok plan ∧
      L.F = linkDescV p.chains plan ∧ L.F.planOk = true ∧ L.F.dsOf "entry file" = .ok L.ds ∧ L.xs =
          L.F.xsTyped := by
  unfold linkOfFilesV at h
  split at h
  · cases h
  · cases h
  · rename_i p plan hp hplan
    dsimp only at h
    split at h
    · cases h
    · cases h
    · rename_i ds hw hds
      cases h
      exact ⟨p, plan, hp, hplan, rfl, OneChainFileDescription.planWord_none _ hw, hds, rfl⟩

/-- **The tie at the files.** -/
theorem linkOfFilesV_under (hSP : SendPOfDecide) (pol lay KL : ByteArray) (L : Link3)
    (h : linkOfFilesV pol lay KL = .ok L) :
    ∃ L', linkOfFiles pol lay KL = .ok L' ∧ L'.ds = L.ds ∧ L'.xs = L.xs ∧
      ∀ x v, L.F.run x v = true → L'.F.run x v = true := by
  obtain ⟨p, plan, hp, hplan, hF, hok, hds, hxs⟩ := linkOfFilesV_ok pol lay KL L h
  obtain ⟨F, ds, xs⟩ := L
  simp only at hF hok hds hxs
  subst hF
  have hO : (linkDesc p.chains plan).planOk = true := descV_planOk _ _ _ hok
  have hw : (linkDesc p.chains plan).planWord = none := by
    unfold OneChainFileDescription.planWord
    simp [hO]
  have hd : (linkDesc p.chains plan).dsOf "entry file" = .ok ds := by
    rw [← hds]
    exact (descV_dsOf _ _ _ _).symm
  refine ⟨⟨linkDesc p.chains plan, ds, (linkDesc p.chains plan).xsTyped⟩, ?_, rfl, ?_, ?_⟩
  · unfold linkOfFiles
    rw [hp, hplan]
    dsimp only
    clear hok hds hxs hO h
    generalize linkDesc p.chains plan = G at hw hd ⊢
    split
    · rename_i _ _ w hw'
      rw [hw] at hw'
      cases hw'
    · rename_i _ _ e hd' _
      rw [hd] at hd'
      cases hd'
    · rename_i _ _ ds' _ hd'
      rw [hd] at hd'
      cases hd'
      rfl
  · show (linkDesc p.chains plan).xsTyped = xs
    exact (descV_xsTyped (p15Of p.chains) plan _).symm.trans hxs.symm
  · intro x v hv
    exact linkDescV_run hSP _ _ x v hv

/-- **plans_are_the_priced_plan, at the entry file, OF THE SEATED TEXT** (fewest
letters; no premise): where the tests on the plan of the seated link's description pass: the
entries of its declared rounds ARE the rounds'
entries of the finished plan whose prices its own public test has tested; that test has said yes;
and the shape, the codes and the plan's entries that a reader of an entry file is handed are the
made ones. BY TESTS, not by a law on the planner. -/
theorem plans_pricedV (c : Model.Verify.Chains) (plan : List Fmt.DeclaredRound)
    (h : (linkDescV c plan).planOk = true) :
    (linkDescV c plan).roundsDeclaredByBlocks.map (·.entry) = c.made.entry.plan.rounds ∧
        VerifiableInference.Desc.entryOk c.made = true ∧
      c.link.given.plan.entries = c.made.entry.plan.entries ∧ c.link.link = (p15Of c).S ∧
          c.link.codes = (p15Of c).codes := by
  rw [show (linkDescV c plan).roundsDeclaredByBlocks = (linkDesc c plan).roundsDeclaredByBlocks from descV_decl _ _ _]
  exact plans_priced c plan (descV_planOk _ _ _ h)

theorem linkDescV_frP (c : Model.Verify.Chains) (plan : List Fmt.DeclaredRound)
    (h : sameP (p15Of c) frP = true) :
    linkDescV c plan = linkDescriptionAt frP plan (VerifiableInference.Desc.entryOk c.made && tiesOk c plan) :=
        by
  unfold linkDescV
  rw [sameP_eq h]

theorem linkDescV_srP (c : Model.Verify.Chains) (plan : List Fmt.DeclaredRound)
    (h : sameP (p15Of c) srP = true) :
    linkDescV c plan = linkDescriptionAt srP plan (VerifiableInference.Desc.entryOk c.made && tiesOk c plan) :=
        by
  unfold linkDescV
  rw [sameP_eq h]

end Desc.K15

#print axioms Desc.K15.descV_decl
#print axioms Desc.K15.linkOfFilesV_ok
#print axioms Desc.K15.linkOfFilesV_under
#print axioms Desc.K15.plans_pricedV
#print axioms Desc.K15.linkDescV_frP
#print axioms Desc.K15.linkDescV_srP
