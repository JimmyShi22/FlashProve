-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/LiveClaims.lean: CONDITIONAL: an attention segment's own rounds: the
statements on the forms that the runs "first" and "second" gather
(Johnson/Desc/K5/Honest/Law/LiveFirst.lean, LiveSecond.lean), said of the same forms AS CLAIMS, in
the tests with code on a list of claims of Johnson/Desc/K9/Honest/SlotsLive.lean (liveAt, plainAt).
Statements with their proofs ON THE VERIFIER'S OWN DATA: no prover is in this file.

How a form becomes a claim. A run of forms, taken as a run of claims, lays each form f as the claim
with the form f, no run of entries, and its own number (runOfForms_hands,
Johnson/Desc/First/Att/Claims/RunsHand.lean: the list of claims is the list of forms under
fun f => { form := f }).

Main names:
  slotCoef_is, nzE_is   the coefficient and the test on an element of
                  Johnson/Desc/K5/Honest/Law/Live.lean are those of the files on claims, by their
                  texts
  liveAt_forms    a slot that some form of a list names with a coefficient that does not read 0 is
                  live in the list of claims
  plainAt_forms   every slot is plain in such a list: each claim takes its own number
  k5_first_liveAt, k5_second_liveAt   **the two statements, as liveAt**

The last two are CONDITIONAL as k5_live_first and k5_live_second are: their heads list the premises
and who is meant to show each.
Limits. A list of claims made of a run's forms: that a state's run returns just that list, at a
structure made of what the state holds of the hearing, is not shown here; nor that the structure's
premises hold at a reached state. Nothing on the lookup's runs, which name some of these slots too:
plainAt_forms speaks of these forms alone, and whoever appends other claims owes it of those.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.LiveFirst
import Johnson.Desc.K9.Honest.SlotsLive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E)
open OnBytes.Model (Reading Aff Fork)
open VerifiableInference.Desc (Claim)
open VerifiableInference.Desc.K9H (slotCoef notZero liveAt plainAt liveAt_iff)
open VerifiableInference.Desc.First.Att.P (geoOf Heard Left hear pointsOf LeftIs kB kV)
open VerifiableInference.Desc.First.Att.P.Runs (In JoinsP firstRun secondRun)

/-- The coefficient with which a claim names a slot is its form's. -/
theorem slotCoef_is {K : Type} [CommRing K] (ρ : Reading K) (cl : Claim) (j : ℕ) :
    slotCoef ρ cl j = slotCo ρ cl.form j := rfl

/-- The two tests on an element are one text. -/
theorem nzE_is (w : E) : nzE w = notZero w := rfl

/-- **A slot that some form names with a coefficient that does not read 0 is live in the list of
claims.** -/
theorem liveAt_forms {l : List Aff} {j : ℕ} (h : ∃ f ∈ l, slotCo Reading.gl f j ≠ 0) :
    liveAt (l.map fun f => ({ form := f } : Claim)) j = true := by
  obtain ⟨f, hf, hl⟩ := h
  exact (liveAt_iff _ j).2 ⟨{ form := f }, List.mem_map.2 ⟨f, hf, rfl⟩, rfl, hl⟩

/-- Each claim of such a list takes its own number. -/
theorem plainAt_forms (l : List Aff) (j : ℕ) :
    plainAt (l.map fun f => ({ form := f } : Claim)) j = true := by
  unfold plainAt
  rw [List.all_eq_true]
  intro cl hcl
  obtain ⟨f, _, rfl⟩ := List.mem_map.1 hcl
  rfl

section Main
variable {x : OnBytes.Params.AttentionRounds} {F G F' : Fork} {rs rest : List Fmt.RoundView} {lead : ℕ}
  {h : Heard} {i : In} {zk : Array (Array E)} {l : Left} {K : ℕ} {l₁ l₂ : List Aff} {jn : JoinsP}

/-- **The run "first"**: CONDITIONAL as k5_live_first. -/
theorem k5_first_liveAt (A : OnBytes.Attention.Plan) (S : OnBytes.Attention.Shape)
    (gL : OnBytes.Model.Forest.Heard)
    (hh : hear x (F, rs, 0) = some (h, G, rest, lead)) (hz : OnBytes.Model.Road.Sized F)
    (li : LeftIs i.g zk h F' l) (hp : pointsOf i.g zk h l = some i.p) (gf : LiveFits i.g x)
    (hg : i.g = geoOf S) (hzk : i.zk = gL.zk) (hN : A.NC = S.calls.size)
    (h1 : firstRun i K = some (l₁, jn)) (hL : heardLive h = true) :
    ∀ j, F.next ≤ j → j < kV x F.next → j ≠ kB x F.next →
      liveAt (l₁.map fun f => ({ form := f } : Claim)) j = true := fun j a b c =>
  liveAt_forms (k5_live_first A S gL hh hz li hp gf hg hzk hN h1 hL j a b c)

/-- **The run "second"**: CONDITIONAL as k5_live_second. -/
theorem k5_second_liveAt (S : OnBytes.Attention.Shape) (gL : OnBytes.Model.Forest.Heard)
    (hh : hear x (F, rs, 0) = some (h, G, rest, lead)) (hz : OnBytes.Model.Road.Sized F)
    (li : LeftIs i.g zk h F' l) (hp : pointsOf i.g zk h l = some i.p) (gf : LiveFits i.g x)
    (hg : i.g = geoOf S) (hzk : i.zk = gL.zk) (h2 : secondRun i K = some l₂)
    (hL : heardLive h = true) :
    ∀ j, j = kB x F.next ∨ (kV x F.next ≤ j ∧ j < k5End x F.next) →
      liveAt (l₂.map fun f => ({ form := f } : Claim)) j = true := fun j hj =>
  liveAt_forms (k5_live_second S gL hh hz li hp gf hg hzk h2 hL j hj)

end Main

end H2K5.Honest

#print axioms H2K5.Honest.slotCoef_is
#print axioms H2K5.Honest.nzE_is
#print axioms H2K5.Honest.liveAt_forms
#print axioms H2K5.Honest.plainAt_forms
#print axioms H2K5.Honest.k5_first_liveAt
#print axioms H2K5.Honest.k5_second_liveAt
