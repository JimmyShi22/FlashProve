-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/NotTakenAtTheReturn.lean: the members' batching (kind K13): two of the propositions
of E2E/TheHonestProverNotTaken.lean on fixed values that the honest prover's term lays, proved at a
return of the maker from which the honest prover for a request is made. Statements with their
proofs; no definition.

  `q0_is_idle`   **`Q0IsIdle`**, at every return, with no premise: the pile's filler is the same
     function at every value of the parameter in whose place the term lays `q0Idle`
  `links_at_scope`   in the goals' scope, where the description can be opened: the public part has
     25 built links, and the group's number of each is below 12
  `plans_at_scope`   there every link's group has its plan
  `layers_plans_are_there`   **`LayersPlansAreThere`**, under the library's head (`P5J.AtMgA`) and
     the maker's return: so the blank plan, the default where a group has no plan, is read at no
     segment

Limits.
  * Both are on public data alone: no run, coin or input is read.
  * `PileIsMade`, the third proposition on this kind's filler, speaks of a run's stand and is not
    treated here. At a stand of the first chain's thread in front of the kind's member the filler
    yields all its rows: `k13_pile_made_at_355` (Johnson/Desc/ProofFile/Honest/K13/FiveAt355.lean).
  * The head and the return are hypotheses.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import E2E.TheHonestProverNotTaken
import Johnson.Desc.ProofFile.Honest.K13.DefaultsIdle
import Johnson.Desc.ProofFile.Honest.K13.SitesOfLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K13
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest ProofFile.Honest.K13
open ProofFile.Honest.Term (OnlineReturn onlineMaker)
open AtPublicFiles.AtFiles.HonestTerm (Q0IsIdle LayersPlansAreThere)
open P5J (AtMgA TS)

/-- **The filler's parameter of the pile's claims is read by nothing.** No premise. -/
theorem q0_is_idle {files : VerifierAndGoals.PublicFiles} (returned : OnlineReturn files) : Q0IsIdle returned :=
  fun firstChain head other _ => pileAtChain_any_q0 firstChain returned.Z head _ other

section
variable {Pp : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- In scope the public part has 25 built links, and each one's group's number is below 12. -/
theorem links_at_scope (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) :
    Z.p.built.links.size = 25 ∧ ∀ l, l < 25 → groupOfSeg Z l < 12 := by
  have hX := O.public
  obtain ⟨hq, hN, -, -⟩ := Meaning.scope_plans hS hR hX
  have hb := IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
          (show ProofFile.pubBy (ProofFile.PlainG.madeOf OnBytes.secondHashFunction) ProofFile.plainStarts Pp.pol lay Pp.KL = .ok Z
            from O.pub)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hb
  obtain ⟨ls, hl, -, -, -⟩ := IM.blank_ground O.blank
  unfold ProofFile.Plain.linksPlain at h₀ hl
  rw [O.W] at hq hN
  have hq' : Z.made.p.X.p4 = true := hq
  have hN' : Z.made.p.X.NGr = 12 := hN
  rw [hq', hN'] at h₀ hB
  first
    | rw [hq', hN'] at hl
    | rw [hq, hN] at hl
  obtain ⟨-, -, z0, -, -⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  obtain ⟨-, alt, l24, e24, I24⟩ := Meaning.links_alternate h₀ hB hl
  refine ⟨(Meaning.built_at hB).1.trans z0, fun l hl25 => ?_⟩
  have key : ∀ (x : OnBytes.Model.Stages.LinkH) (g : Nat),
      (OnBytes.L5.LinksOrder.zipped Z.p.built ls)[l]? = some x → x.g = g → groupOfSeg Z l = g := by
    intro x g hx hg
    obtain ⟨b, hb', -, gb⟩ := VerifiableInference.OnPublicFiles.zipped_g hx
    unfold groupOfSeg
    rw [hb']
    exact gb.trans hg
  by_cases h24 : l = 24
  · subst h24
    rw [key l24 0 e24 I24.g]
    exact Nat.zero_lt_succ 11
  · obtain ⟨s, a, x, x', -, -, e, I, e', I'⟩ := alt (l / 2) (by omega)
    rcases Nat.mod_two_eq_zero_or_one l with hm | hm
    · rw [show 2 * (l / 2) = l by omega] at e
      rw [key x _ e I.g]
      omega
    · rw [show 2 * (l / 2) + 1 = l by omega] at e'
      rw [key x' _ e' I'.g]
      omega

/-- In scope every link's group has its plan. -/
theorem plans_at_scope (hS : VerifierAndGoals.InScope Pp = true) (hR : VerifierAndGoals.readFiles Pp = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pp.pol lay Pp.KL F Z Bs base c A B) (l : Nat)
    (hl : l < Z.p.built.links.size) : (Z.p.X.G[groupOfSeg Z l]?).isSome = true := by
  obtain ⟨hz, hg⟩ := links_at_scope hS hR O
  obtain ⟨⟨hp, e⟩, -⟩ := Meaning.scope_plans24 hS hR O.public (groupOfSeg Z l) (hg l (hz ▸ hl))
  rw [← O.W, e]
  rfl

end

/-- **Every link's group has its plan**, at the maker's return under the library's head. -/
theorem layers_plans_are_there {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place} {returned : OnlineReturn files}
    (h : AtMgA OnBytes.secondHashFunction files D r Zp Np cF x) (hA : onlineMaker files = .ok returned) :
    LayersPlansAreThere returned := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  intro segment hs
  rw [(atPure_at_laid h.laid hA).1] at hs ⊢
  exact plans_at_scope h.scope h.reads O segment hs

end AtFullSide.K13

#print axioms AtFullSide.K13.q0_is_idle
#print axioms AtFullSide.K13.links_at_scope
#print axioms AtFullSide.K13.plans_at_scope
#print axioms AtFullSide.K13.layers_plans_are_there
