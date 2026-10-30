-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyBehindFirst.lean: behind a proximity test's first stage, whatever trees its
group's members stand in, the invariant of the induction over the stages (`BodyInv`,
Johnson/Prover/Link/BodyInv.lean) holds at the next stage; and so the stages accept.

It joins two texts: the first stage's term and acceptances at a group of any layout (`FirstYes`,
`t1At`, `t3At`, `qAt`, Johnson/Desc/K12/Honest/FirstYes.lean; `ClaimTrue`,
Johnson/Desc/K12/Honest/ClaimTrue.lean) and the later stages' induction, which asks no acceptance
(`body_yes`, Johnson/Prover/Link/BodyCloseS.lean).

Main names (namespace `Johnson.Prover.Link`).
  `bodyInv_first`   `FirstYes` · `SwitchPlan` · `SwitchIn` (Johnson/Prover/Link/FormBehindAny.lean)
      · the plan and the fit from the next stage on: then the claim behind the first switch true
      gives `BodyInv` at the next stage. A further stage follows that one
  `stages_accept_body`   `FirstYes` · `FitAll` · `BodyInv` at the next stage: the stages'
      sub-protocol accepts all that the term shows
  `stages_left_body`   the same, and nothing is left untested behind the first switch (`left_any`,
      FormBehindAny.lean, pays that): then nothing is left untested at the end

Limits. Every premise is asked. AT A FIRST STAGE WHOSE MEMBERS STAND IN SEVERAL TREES NOTHING HERE
MEETS `FirstYes`, `SwitchIn` OR `SwitchPlan`: until an instance meets them these statements may be
idle there. The switch into the last stage is not served by `bodyInv_first`. Nothing on soundness;
nothing on what a shown value shows or does not show.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormBehindAny
import Johnson.Prover.Link.BodyCloseS
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

/-- **The joint**: the claim behind the first switch true gives `BodyInv` at the next stage. -/
theorem bodyInv_first (p : P12) (K : BCoins) (nx : Fmt.M1.Stage) (rest' : List Fmt.M1.Stage)
    (j : ℕ) (a next : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS)
    (trees : List ProofFile.Honest.K12.Tree)
    (D : ℕ → Fmt.Drawn) (n : IoppStage) (gp : ℕ) (rows : SingleRows)
    (Y : FirstYes p K (nx :: rest') j a next l o t P trees D)
    (Pl : SwitchPlan p (t1At p K j a l o t P D).st.codes j a next n)
    (In : SwitchIn p j a next n gp (t1At p K j a l o t P D) rows
      (noDigest ⟨[.answer (ofE (aAns p j a next o D (t1At p K j a l o t P D)
        (qAt K (nx :: rest') j a next o P D)))], D (o + 2 + ((sgOf a).h + (sgOf a).g))⟩))
    (hPlan : PlanAll p (nx :: rest') (j + 1) next (l.drop (a.k + 3))
      (t1At p K j a l o t P D).st.codes)
    (hF : FitFrom D (l.drop (a.k + 3)) (o + ((sgOf a).h + (sgOf a).g) + 3)) :
    ClaimTrue (sgOf next) (t3At p K (nx :: rest') j a next l o t P trees D)
        (qAt K (nx :: rest') j a next o P D) →
      BodyInv p K (PlanAll p) D (nx :: rest') (j + 1) next (l.drop (a.k + 3))
        (o + ((sgOf a).h + (sgOf a).g) + 3) (t3At p K (nx :: rest') j a next l o t P trees D)
        (qAt K (nx :: rest') j a next o P D)
        (aCol (nx :: rest').isEmpty next (qAt K (nx :: rest') j a next o P D)) := by
  intro hcl
  obtain ⟨t₂, hs2⟩ := Y.switch
  obtain ⟨t₃, hs3⟩ := Y.behind
  have e2 : aRec2 p K (nx :: rest') j a next l o t P trees D = t₂ := getD_of_ok hs2
  have e3 : t3At p K (nx :: rest') j a next l o t P trees D = t₃ := getD_of_ok hs3
  rw [e2] at hs3
  have h2 := (ranged_ok _ _ _ _ _ _ hs2).1
  have h3 : (behindJ p (j + 1) next (((l.drop (1 + a.k)).take 2).map (·.1))).decide t₂ [] [] =
      .ok t₃ := hs3
  obtain ⟨⟨c, n', dS', dC', Pl'⟩, hD, hst, hown, -⟩ := hPlan.1
  obtain rfl : c = n := Option.some.inj (Pl'.stage.symm.trans Pl.stageN)
  -- the codes stay
  have hcodes : t₃.st.codes = (t1At p K j a l o t P D).st.codes := by
    obtain ⟨_, _, _, _, _, -, -, hd, -, -⟩ := switchUnfolds p j a next false _ _ t₂ t₃ _ _ _ rows _
      c Pl.early Pl.one In.pass Pl.stageN h2 h3
    exact hd.codes
  obtain ⟨row', lay, tr', hp3, I, hL, hQ⟩ := formInv_any Pl In h2 h3 Pl' rest' hD hst hown
    (qAt K (nx :: rest') j a next o P D).tabM (qAt K (nx :: rest') j a next o P D).tabZ
    (qAt K (nx :: rest') j a next o P D).tM (qAt K (nx :: rest') j a next o P D).tZ
    (qAt K (nx :: rest') j a next o P D).fM (qAt K (nx :: rest') j a next o P D).fT
  rw [e3] at hcl ⊢
  refine ⟨?_, hF, row', lay, c, _, _, _, tr', I, hcl row' lay hp3, rfl, ?_⟩
  · rw [hcodes]
    exact hPlan
  · exact ColIs.later rfl _ _ hL hQ

/-- **The stages accept.** -/
theorem stages_accept_body (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (j : ℕ)
    (a next : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS)
    (trees : List ProofFile.Honest.K12.Tree) (D : ℕ → Fmt.Drawn)
    (Y : FirstYes p K rest j a next l o t P trees D) (hfit : FitAll next rest)
    (hI : BodyInv p K (PlanAll p) D rest (j + 1) next (l.drop (a.k + 3))
      (o + ((sgOf a).h + (sgOf a).g) + 3) (t3At p K rest j a next l o t P trees D)
      (qAt K rest j a next o P D) (aCol rest.isEmpty next (qAt K rest j a next o P D))) :
    ∃ t', (stagesFrom guardedProximityTestParts p j a (next :: rest) l : Block T12 Unit).decide t
      ((stagesAll p K (next :: rest) j a l o t P trees D).rs.map noDigest)
      (stagesAll p K (next :: rest) j a l o t P trees D).gs = .ok t' := by
  obtain ⟨t', ih⟩ := body_yes p K D rest (j + 1) next _ _ _ _ _ hI
  exact ⟨t', stages_yes_first p K rest j a next l o t P trees D Y hfit t' ih⟩

/-- **The stages accept, and nothing is left untested, where nothing is behind the first switch.**
-/
theorem stages_left_body (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (j : ℕ)
    (a next : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS)
    (trees : List ProofFile.Honest.K12.Tree) (D : ℕ → Fmt.Drawn)
    (Y : FirstYes p K rest j a next l o t P trees D) (hfit : FitAll next rest)
    (hI : BodyInv p K (PlanAll p) D rest (j + 1) next (l.drop (a.k + 3))
      (o + ((sgOf a).h + (sgOf a).g) + 3) (t3At p K rest j a next l o t P trees D)
      (qAt K rest j a next o P D) (aCol rest.isEmpty next (qAt K rest j a next o P D)))
    (hl : ChainEnd.NothingLeft (t3At p K rest j a next l o t P trees D).st) :
    ∃ t', (stagesFrom guardedProximityTestParts p j a (next :: rest) l : Block T12 Unit).decide t
        ((stagesAll p K (next :: rest) j a l o t P trees D).rs.map noDigest)
        (stagesAll p K (next :: rest) j a l o t P trees D).gs = .ok t' ∧
      ChainEnd.NothingLeft t'.st := by
  obtain ⟨t', ih, hN⟩ := body_left p K D rest (j + 1) next _ _ _ _ _ hI hl
  exact ⟨t', stages_yes_first p K rest j a next l o t P trees D Y hfit t' ih, hN⟩

end Johnson.Prover.Link
