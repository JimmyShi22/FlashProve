-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Across/FormsFwd.lean: the proofs of `FormsQFwd`, `FormsQAFwd` and `FormsFwdMgAll`
(Johnson/Desc/K11/Across/FormsFwdStatement.lean), to the letter. Lemmas; none of the library's
goals.

How: the sentence has two halves. THE TESTS BEHIND THE STEP: the sentence in front holds the public
test in front (`formsQ_in`, `formsQA_in`); the library carries that test forward over the merge's
yes (`formsIn_merge`, Johnson/Top/H0/MergeLaw/FormsAcross.lean; `formsInA_merge`,
FormsAheadAcross.lean); unfolded at the part behind and at the reader's answer behind (`Fwd`), it is
the sentence's tests. THE VALUES: a form that passes the test in front has one value at both parts
(`value_rides`, `value_ridesW`, Johnson/Desc/Sound/FormsQ.lean), since the part behind rides on the
part in front (`more_at_merge`) and the data with what is ahead do not read the ledger
(`dataQA_same` at `seg_at_merge`'s equations). The third: the two, run by run, as the library's
`forms_back_mgAll` goes the other way.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Across.FormsFwdStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Desc.First.ForkMerge.Across
open VerifiableInference.Desc.K9 (formsIn formsInA affInA mergeOf)
open VerifiableInference.Desc.Sound (formsQ_in formsQA_in value_rides value_ridesW dataQA
  mgAll_forms)
open VerifiableInference.Desc.First.MergeLaw (formsIn_merge formsInA_merge more_at_merge
  seg_at_merge dataQA_same)

/-- **The plain sentence goes forward over the merge's accepting step.** -/
theorem formsQFwd : FormsQFwd := by
  intro Rd own piece run P s s' rs h pa hpa hS hfree hf hlate rd hq
  have hin' := formsIn_merge Rd own piece run P h pa hpa hS hfree hf hlate
    (formsQ_in Rd own piece run s rd hq)
  obtain ⟨a, R, ha, hR, hlo, hfm⟩ := hq
  obtain rfl : pa = a := Option.some.inj (hpa.symm.trans ha)
  obtain ⟨pb, hpb, _, hr, _⟩ := more_at_merge own P h pa hpa hS hfree R.late hlo (hlate R hR)
  have hR' := hf R hR
  unfold formsIn at hin'
  rw [hpb, hR'] at hin'
  obtain ⟨hlo', hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin'
  refine ⟨pb, R, hpb, hR', hlo', fun f hm => ⟨List.all_eq_true.1 hall f hm, ?_⟩⟩
  rw [value_rides own (mergeOf s) R.late pa pb rd hr f (hfm f hm).1]
  exact (hfm f hm).2

/-- **The sentence with what is ahead goes forward over the merge's accepting step.** -/
theorem formsQAFwd : FormsQAFwd := by
  intro Rd sent own piece run P s s' rs h pa hpa hS hfree hf hlate rd hq
  have hin' := formsInA_merge Rd sent own piece run P h pa hpa hS hfree hf hlate
    (formsQA_in sent own Rd piece run s rd hq)
  obtain ⟨a, R, ha, hR, hlo, hfm⟩ := hq
  obtain rfl : pa = a := Option.some.inj (hpa.symm.trans ha)
  obtain ⟨pb, hpb, _, hr, _⟩ := more_at_merge own P h pa hpa hS hfree R.late hlo (hlate R hR)
  obtain ⟨_, _, pb', _, _, hpb', _, _, eL, est, ebk⟩ := seg_at_merge P h pa hpa
  obtain rfl : pb' = pb := Option.some.inj (hpb'.symm.trans hpb)
  have eD := dataQA_same sent own pa pb' rd eL est ebk
  have hR' := hf R hR
  unfold formsInA at hin'
  rw [hpb, hR'] at hin'
  obtain ⟨hlo', hall⟩ := Eq.mp (Bool.and_eq_true _ _) hin'
  refine ⟨pb', R, hpb, hR', hlo', fun f hm => ⟨List.all_eq_true.1 hall f hm, ?_⟩⟩
  have h2 := (hfm f hm).1
  unfold affInA at h2
  obtain ⟨_, h3⟩ := Eq.mp (Bool.and_eq_true _ _) h2
  rw [value_ridesW own (mergeOf s) R.late pa pb' (dataQA sent own pa rd) (dataQA sent own pb' rd)
    hr.arrays hr.filled f (List.all_eq_true.1 h3) (fun _ _ _ _ => by rw [eD])
    (fun _ _ => by rw [eD])]
  exact (hfm f hm).2

/-- **The field forms of the composed meaning goes forward over the merge's accepting step**, at
every name but "weights". -/
theorem formsFwdMgAll : FormsFwdMgAll := by
  intro Xi Pp Tok rows cols nR X 𝔇 Mg m k r hr P z s s' hy pa hpa hS hfree hruns y y' w h
  obtain ⟨rs, hy⟩ := hy
  rw [mgAll_forms] at h ⊢
  refine ⟨fun p hp => ?_, fun e => absurd e hr⟩
  have h1 := h.1 p hp
  by_cases e : 𝔇.ah p.1 p.2 = true
  · rw [if_pos e] at h1 ⊢
    exact formsQAFwd _ _ _ _ _ P s s' rs hy pa hpa hS hfree (hruns p hp).1 (hruns p hp).2 _ h1
  · rw [if_neg e] at h1 ⊢
    exact formsQFwd _ _ _ _ P s s' rs hy pa hpa hS hfree (hruns p hp).1 (hruns p hp).2 _ h1

end Johnson.Desc.First.ForkMerge.Across

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Across.formsQFwd
#print axioms Johnson.Desc.First.ForkMerge.Across.formsQAFwd
#print axioms Johnson.Desc.First.ForkMerge.Across.formsFwdMgAll
