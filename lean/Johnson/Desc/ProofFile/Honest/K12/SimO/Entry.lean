-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at a proximity test whose first fold sends its own fresh table: a state that stands in.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/Entry.lean: `exact_free_own` (SimO/Free.lean) at a job whose state on entry may be wiped: as Sim2/Entry.lean at the other arm. The second part reads no target (`testHalf_one`, Blind/All.lean), and the sentence fixes the
stand outside its law: so at each stand a state function that agrees with the job's but for targets may stand in, and that one alone need meet `OnFreeOwn`.

  `restMember_agree_own`   the second member is one at two such jobs
  `OnEntryOwn`             the condition
  `exact_entry_own`        **`ExactMember` at `restMember J Js`, at `OnEntryOwn`**

Limits. CONDITIONAL on `OnEntryOwn`. That a run meets it is no statement here. The condition reads the input, the rows and carried values: no later law may take it as a hypothesis on a run and then speak of the random values as sampled anew. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.SimO.Free
import Johnson.Desc.ProofFile.Honest.K12.Blind.All

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open VerifiableInference.Desc.K12 (T12)
open ProofFile.Honest ProofFile.Honest.K12.Blind
open ProofFile.Honest.Small (ExactMember)

variable {S Cl V W X Pb : Type}

theorem restMember_agree_own (J : TestJob W X) (Js : SimJob Pb) (r' : W → Front X → T12)
    (h : ∀ w fr, Blind.Agree (J.rec₀ w fr) (r' w fr)) :
    (restMember { J with rec₀ := r' } Js : Member V W X Pb) = restMember J Js := by
  have e := testHalf_one (V := V) J r' h
  unfold proverSideOfProximityTest at e
  have e2 := (Placed.mk.inj e).2
  have e3 := (List.cons.inj (List.cons.inj e2).2).1
  unfold restMember
  rw [e3]
  rfl

/-- **The condition at the second part's entry.** -/
def OnEntryOwn (φ : Face V W Pb) (J : TestJob W X) (Js : SimJob Pb) (K : OnBytes.Codes) (chain : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (u : Member V W X Pb) (ca : CsAll u.part.carries)
    (m : Mid W X) (front : Before) : Prop :=
  u.number = 1 → ∃ r' : W → Front X → T12, (∀ w fr, Blind.Agree (J.rec₀ w fr) (r' w fr)) ∧
    OnFreeOwn { J with rec₀ := r' } Js K chain os (φ.pub m.st.input) (stretches _ ca) m front

/-- **The sentence at the second member.** -/
theorem exact_entry_own (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X) (Js : SimJob Pb)
    (K : OnBytes.Codes) (chain firstTree : ℕ) (os : List (Fmt.Shape × Fmt.TreeSource))
    (T : PublicTiesOwn J Js K os.length) (To : OpenTies J Js chain os) :
    ExactMember φ σ chain firstTree (OnEntryOwn φ J Js K chain os) (budOpened J.p.nums.stages)
      (restMember J Js) := by
  intro ca m front ds asks hOn hs hf hb hh hst
  obtain ⟨r', hA, hO⟩ := hOn rfl
  have hE : ExactMember φ σ chain firstTree (onFreeOwn φ { J with rec₀ := r' } Js K chain os)
      (budOpened J.p.nums.stages) (restMember { J with rec₀ := r' } Js) :=
    exact_free_own φ σ { J with rec₀ := r' } Js K chain firstTree os
      ⟨T.place, T.own, T.flag, T.reach, T.plan, T.declared, T.form, T.count, T.rounds, T.tables⟩
      ⟨To.decl, To.opens⟩
  rw [restMember_agree_own J Js r' hA] at hE
  exact hE ca m front ds asks (fun _ => hO) hs hf hb hh hst

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.restMember_agree_own
#print axioms ProofFile.Honest.K12.OnEntryOwn
#print axioms ProofFile.Honest.K12.exact_entry_own
