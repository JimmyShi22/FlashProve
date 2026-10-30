-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyOwnEntry.lean: the marks at the last chain's first state, from the two earlier chains' ends; and the two clauses
`claims`, `dense` of `OwnAsks` at a stand at border 2, with the own group read off the written shape.

  `start_mark`: `OwnMark` at what the start returns.
  `open_A2`: at the written shape the own group is there and has not begun: a closed line.
  `entry_marks`: the two clauses, at a stand.

What stays open. `hstart` of `mark_at_two`. SamplesDense at the two earlier chains' ends.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyOwnMarks
import E2E.KeyLastThread
import Johnson.Desc.ProofFile.Honest.K14.SecondDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyLastChain
open OnBytes OnBytes.Params
open OnBytes.Slice.ProxRun (DenseRow)
open ProofFile.Honest
open ProofFile.Honest.Sh (claimsB)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃ SharedOut)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource thirdPar)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyLastThread (start_key handOf endKey)
open AtPublicFiles.AtFiles (sh₃ SF)

/-- **The marks at the chain's first state.** -/
theorem start_mark {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces} {x : Xi} {e₁ : FirstState} {e₂ : St} {s₀ : S₃}
    {l : OnBytes.LinFirst} (hst : (descriptionFromSource Xs Nr Pl).start₃ x e₁ e₂ = .ok s₀) (hl : e₁.lin = some l)
    (hc : claimsAtB e₁.d.st l.own = true) (hsamp : SamplesDense e₁.d.st)
    (hsh : ∀ o, endKey e₂ = some o → SamplesDense o.st) : OwnMark s₀ := by
  obtain ⟨h, o, hh, ho, hs⟩ := (start_key Xs Nr Pl x e₁ e₂ s₀).1 hst
  have hh' : e₁.lin.map (handOf e₁) = some h := hh
  rw [hl] at hh'
  obtain rfl := Option.some.inj hh'
  obtain ⟨⟨g, hb⟩, -, -, -, est, -, -, eown, -⟩ := K14.start_gives (thirdPar Xs.chains) _ o s₀ hs
  refine ⟨?_, ?_, fun b hb' => ?_⟩
  · rw [est, eown]
    exact hc
  · rw [est]
    exact hsamp
  · rw [hb] at hb'
    obtain rfl := Option.some.inj hb'
    exact hsh o ho

/-- **At the written shape the own group is there and has not begun.** -/
theorem open_A2 : ((A2.1.st.groups[A2.2.own]?).any fun G => !G.inRun) = true := by decide +kernel

/-- **The two clauses at a state of the written shape with the marks.** -/
theorem entry_marks {st : S₃} {t : T12} (he : enterOwn st = .ok t) (hsh : sh₃ SF st = A2) (hm : OwnMark st) :
    claimsB t = true ∧ ∀ G, t.st.groups[t.g]? = some G →
      ∀ r ∈ (OnBytes.Slice.runRows t.st G).toList, DenseRow r := by
  have h := open_A2
  rw [← hsh] at h
  have h' : (((stSh st.st).groups[st.loc.own]?).any fun G => !G.inRun) = true := h
  rw [grp_get] at h'
  cases hG : st.st.groups[st.loc.own]? with
  | none =>
    rw [hG] at h'
    cases h'
  | some G =>
    rw [hG] at h'
    have hr : (!(grpSh G).inRun) = true := h'
    have hr' : G.inRun = false := by
      have : (!G.inRun) = true := hr
      simpa using this
    refine asks_of_mark he hm (fun G' hG' => ?_) ⟨G, hG⟩
    obtain rfl := Option.some.inj (hG.symm.trans hG')
    exact hr'

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.start_mark
#print axioms AtPublicFiles.KeyLastChain.open_A2
#print axioms AtPublicFiles.KeyLastChain.entry_marks
