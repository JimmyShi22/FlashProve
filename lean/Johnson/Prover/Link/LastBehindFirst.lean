-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LastBehindFirst.lean: a proximity test of two stages: behind its first stage,
whatever trees its group's members stand in, the invariant of the induction over the stages
(`BodyInv`, Johnson/Prover/Link/BodyInv.lean) holds at the last stage.

The companion of `bodyInv_first` (Johnson/Prover/Link/BodyBehindFirst.lean), which serves a first
switch behind which a further stage follows. `stages_accept_body` (there) takes either.

Main name (namespace `Johnson.Prover.Link`).
  `bodyInv_first_last`   `FirstYes` (Johnson/Desc/K12/Honest/FirstYes.lean) · `LastSwitchPlan`
      (Johnson/Prover/Link/LastBehindAny.lean) · `SwitchIn` (Johnson/Prover/Link/FormBehindAny.lean)
      · the plan and the fit at the last stage: then the claim behind the switch true
      (`ClaimTrue`, Johnson/Desc/K12/Honest/ClaimTrue.lean) gives `BodyInv` at the last stage

Limits. Every premise is asked. AT A FIRST STAGE WHOSE MEMBERS STAND IN SEVERAL TREES NOTHING HERE
MEETS `FirstYes`, `SwitchIn` OR `LastSwitchPlan`: until an instance meets them this statement may be
idle there. Nothing on soundness; nothing on what a shown value shows or does not show.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LastBehindAny
import Johnson.Prover.Link.BodyCloseB
import Johnson.Desc.K12.Honest.FirstYes
import Johnson.Desc.K12.Honest.ClaimTrue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw H2K.JointK
open H2K.Pub (sgOf)
open ProofFile.Honest.K12

/-- **The joint at a test of two stages.** -/
theorem bodyInv_first_last (p : P12) (K : BCoins) (j : ℕ) (a next : Fmt.M1.Stage) (l : Laid)
    (o : ℕ) (t : T12) (P : PS) (trees : List ProofFile.Honest.K12.Tree) (D : ℕ → Fmt.Drawn)
    (n : IoppStage) (gp : ℕ) (rows : SingleRows)
    (Y : FirstYes p K [] j a next l o t P trees D)
    (Pl : LastSwitchPlan p (t1At p K j a l o t P D).st.codes j a next n)
    (In : SwitchIn p j a next n gp (t1At p K j a l o t P D) rows
      (noDigest ⟨[.answer (ofE (aAns p j a next o D (t1At p K j a l o t P D)
        (qAt K [] j a next o P D)))], D (o + 2 + ((sgOf a).h + (sgOf a).g))⟩))
    (hPlan : PlanAll p [] (j + 1) next (l.drop (a.k + 3)) (t1At p K j a l o t P D).st.codes)
    (hF : FitFrom D (l.drop (a.k + 3)) (o + ((sgOf a).h + (sgOf a).g) + 3)) :
    ClaimTrue (sgOf next) (t3At p K [] j a next l o t P trees D) (qAt K [] j a next o P D) →
      BodyInv p K (PlanAll p) D [] (j + 1) next (l.drop (a.k + 3))
        (o + ((sgOf a).h + (sgOf a).g) + 3) (t3At p K [] j a next l o t P trees D)
        (qAt K [] j a next o P D)
        (aCol ([] : List Fmt.M1.Stage).isEmpty next (qAt K [] j a next o P D)) := by
  intro hcl
  obtain ⟨t₂, hs2⟩ := Y.switch
  obtain ⟨t₃, hs3⟩ := Y.behind
  have e2 : aRec2 p K [] j a next l o t P trees D = t₂ := getD_of_ok hs2
  have e3 : t3At p K [] j a next l o t P trees D = t₃ := getD_of_ok hs3
  rw [e2] at hs3
  have h2 := (ranged_ok _ _ _ _ _ _ hs2).1
  have h3 : (behindJ p (j + 1) next (((l.drop (1 + a.k)).take 2).map (·.1))).decide t₂ [] [] =
      .ok t₃ := hs3
  obtain ⟨⟨c, d₁, d₂, Lp⟩, -, -, -⟩ := hPlan.1
  obtain rfl : c = n := Option.some.inj (Lp.stage.symm.trans Pl.stageN)
  have hcodes : t₃.st.codes = (t1At p K j a l o t P D).st.codes := by
    obtain ⟨_, _, _, _, _, -, -, hd, -, -⟩ := switchUnfolds p j a next true _ _ t₂ t₃ _ _ _ rows _
      c Pl.early Pl.one In.pass Pl.stageN h2 h3
    exact hd.codes
  obtain ⟨row', lay, hp3, ek, eh, F⟩ := lastForm_any Pl In h2 h3 Lp
  rw [e3] at hcl ⊢
  have hh := hcl row' lay hp3
  rw [ek, eh] at hh
  refine ⟨?_, hF, row', lay, c, _, _, _, _, F, hh, rfl⟩
  rw [hcodes]
  exact hPlan

end Johnson.Prover.Link
