-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the frame's sentence at both members, at a condition a run can meet.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/Entry.lean: the frame's sentence exact at both members of a
proximity test where the first fold's fresh table came earlier, at the condition OnEntry: at a job
whose state on entry may be wiped. The second part does not read targets (testHalf_one,
Blind/All.lean), and the sentence fixes the stand outside its law. So at each stand a state function
that agrees but for targets may stand in, and it alone need meet OnFreeTD.

r' stands only in the condition, on the real side, at one
stand, and may hang on the input. The simulators' job Js is no function of r': it is a parameter,
and what it must be at every Before is said by OnFreeTD.door. At the first chain's last test
Js.rec₀ is stateFromView (DoorTrue.lean).

  restPart_agree, restMember_agree   the second part and member are one at two such jobs
  OnEntry, onEntry_of_free, agree_of_onEntry   the condition; no narrower than OnFreeTD; what it forces
  exact_rest_entry, exact_both_entry   the sentence, at the second member; at both
  onFree_of_parts   OnFreeTD at the job that stands in, from its named parts

Limits. Conditional on OnEntry. That a run meets it is no statement here. The condition reads the
input, the rows and carried values: no later law may take it as a hypothesis on a run and then speak
of the random values as sampled anew. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudBothDense
import Johnson.Desc.ProofFile.Honest.K12.Blind.All
import Johnson.Desc.ProofFile.Honest.K12.Sim2.Clauses

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc.K12 (T12)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Blind ProofFile.Honest.K12.Light
open ProofFile.Honest.Small (ExactMember)

variable {S Cl V W X Pb : Type}

/-- The second part is one at two jobs whose states on entry agree but for targets. -/
theorem restPart_agree (J : TestJob W X) (r' : W → Front X → T12)
    (h : ∀ w fr, Blind.Agree (J.rec₀ w fr) (r' w fr)) :
    (restPart { J with rec₀ := r' } : ProofFile.Honest.Part V W X) = restPart J := by
  have e := testHalf_one (V := V) J r' h
  unfold proverSideOfProximityTest at e
  have e2 := (Placed.mk.inj e).2
  exact (List.cons.inj (List.cons.inj e2).2).1

/-- So is the second member. -/
theorem restMember_agree (J : TestJob W X) (Js : SimJob Pb) (r' : W → Front X → T12)
    (h : ∀ w fr, Blind.Agree (J.rec₀ w fr) (r' w fr)) :
    (restMember { J with rec₀ := r' } Js : Member V W X Pb) = restMember J Js := by
  unfold restMember
  rw [restPart_agree J r' h]
  rfl

/-- **The condition at the second part's entry.** At each stand there is a state function that
agrees with the job's but for targets, at which OnFreeTD holds there. -/
def OnEntry (φ : Face V W Pb) (J : TestJob W X) (Js : SimJob Pb) (K : OnBytes.Codes) (chain : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (u : Member V W X Pb) (ca : CsAll u.part.carries)
    (m : Mid W X) (front : Before) : Prop :=
  u.number = 1 → ∃ r' : W → Front X → T12, (∀ w fr, Blind.Agree (J.rec₀ w fr) (r' w fr)) ∧
    OnFreeTD { J with rec₀ := r' } Js K chain os (φ.pub m.st.input) (stretches _ ca) m front

/-- OnEntry is no narrower than OnFreeTD: the job's own state stands in. onFreeTD_of takes OnFreeT to
OnFreeTD. -/
theorem onEntry_of_free (φ : Face V W Pb) (J : TestJob W X) (Js : SimJob Pb) (K : OnBytes.Codes)
    (chain : ℕ) (os : List (Fmt.Shape × Fmt.TreeSource)) (u : Member V W X Pb)
    (ca : CsAll u.part.carries) (m : Mid W X) (front : Before)
    (h : OnFreeTD J Js K chain os (φ.pub m.st.input) (stretches _ ca) m front) :
    OnEntry φ J Js K chain os u ca m front := fun _ => ⟨J.rec₀, fun _ _ => rfl, h⟩

/-- What the condition forces: at its stand the job's state and the simulators' agree but for
targets. This says that the clause door bites; it shows no pair of states that fails. -/
theorem agree_of_onEntry (φ : Face V W Pb) (J : TestJob W X) (Js : SimJob Pb) (K : OnBytes.Codes)
    (chain : ℕ) (os : List (Fmt.Shape × Fmt.TreeSource))
    (ca : CsAll (restMember J Js : Member V W X Pb).part.carries) (m : Mid W X) (front : Before)
    (h : OnEntry φ J Js K chain os (restMember J Js) ca m front) :
    Blind.Agree (J.rec₀ m.st.input (restFront J m))
      (Js.rec₀ (φ.pub m.st.input) (front.cut (firstLen J.p.nums.stages))) := by
  obtain ⟨r', hA, O⟩ := h rfl
  have hd := O.door
  have ha := hA m.st.input (restFront J m)
  exact hd ▸ ha

/-- **The sentence at the second member.** -/
theorem exact_rest_entry (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X)
    (Js : SimJob Pb) (K : OnBytes.Codes) (chain firstTree : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (T : PubTiesT J Js K os.length)
    (To : OpenTies J Js chain os) :
    ExactMember φ σ chain firstTree (OnEntry φ J Js K chain os) (budBoth Js)
      (restMember J Js) := by
  intro ca m front ds asks hOn hs hf hb hh hst
  obtain ⟨r', hA, hO⟩ := hOn rfl
  have hE : ExactMember φ σ chain firstTree
      (onFreeTD φ { J with rec₀ := r' } Js K chain os) (budBoth Js)
      (restMember { J with rec₀ := r' } Js) :=
    exact_rest_both_dense φ σ { J with rec₀ := r' } Js K chain firstTree os
      ⟨T.place, T.own, T.reach, T.plan, T.form, T.count, T.rounds, T.tables⟩
      ⟨To.decl, To.opens⟩
  rw [restMember_agree J Js r' hA] at hE
  exact hE ca m front ds asks (fun _ => hO) hs hf hb hh hst

/-- **The sentence at both members**, where the fresh table came earlier. -/
theorem exact_both_entry (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : TestJob W X)
    (Js : SimJob Pb) (K : OnBytes.Codes) (chain firstTree : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (hfr : J.fresh.isNone = false) (T₀ : FirstPub J Js)
    (T : PubTiesT J Js K os.length) (To : OpenTies J Js chain os) :
    ∀ u ∈ [firstMember J Js, restMember J Js],
      ExactMember φ σ chain firstTree (OnEntry φ J Js K chain os) (budBoth Js) u := by
  intro u hu
  rcases List.mem_cons.1 hu with rfl | hu'
  · exact exact_first φ σ J Js chain firstTree _ _ hfr T₀
  · rcases List.mem_cons.1 hu' with rfl | hu''
    · exact exact_rest_entry φ σ J Js K chain firstTree os T To
    · cases hu''

/-- **OnFreeTD at the job that stands in, from its named parts.** hag, hdoor: r' at the stand agrees
with the job's state and is the simulators'. h5, htr: of the job itself: neither reads the targets.
hasks: of the job that stands in. -/
theorem onFree_of_parts (J : TestJob W X) (Js : SimJob Pb) (K : OnBytes.Codes) (chain : ℕ)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (pb : Pb) (mem : ℕ → Stretch) (m : Mid W X)
    (front : Before) (r' : W → Front X → T12) (h5 : FiveAt J mem m front)
    (hag : Blind.Agree (J.rec₀ m.st.input (restFront J m)) (r' m.st.input (restFront J m)))
    (hdoor : r' m.st.input (restFront J m) = Js.rec₀ pb (front.cut (firstLen J.p.nums.stages)))
    (hasks : ∃ Dp cc R, Dp.ts.length = os.length ∧
      ShapeAsksD { J with rec₀ := r' } m.st.input (restFront J m)
        (carriedCoins J mem) (heardIn J m) K Dp ∧
      DataAsks { J with rec₀ := r' } m.st.input (restFront J m)
        (carriedCoins J mem) (heardIn J m) Dp cc R)
    (htr : TreesAt J chain os mem m front) :
    OnFreeTD { J with rec₀ := r' } Js K chain os pb mem m front :=
  { le := h5.le, leS := h5.leS, heardFit := h5.heardFit, heard := h5.heard
    door := hdoor
    fold := h5.fold.trans (aFold_agree _ _ _ _ _ (recB_agree theSteps J r' _ _ hag _) _)
    asks := hasks
    trees := htr }

/-- **The condition at a stand of the second member, from its named parts.** r' is whatever state
function agrees with the job's at every input and front and is the simulators' at the stand. -/
theorem onEntry_of_parts (φ : Face V W Pb) (J : TestJob W X) (Js : SimJob Pb) (K : OnBytes.Codes)
    (chain : ℕ) (os : List (Fmt.Shape × Fmt.TreeSource))
    (ca : CsAll (restMember J Js : Member V W X Pb).part.carries) (m : Mid W X) (front : Before)
    (r' : W → Front X → T12) (hA : ∀ w fr, Blind.Agree (J.rec₀ w fr) (r' w fr))
    (h5 : FiveAt J (stretches _ ca) m front)
    (hdoor : r' m.st.input (restFront J m) =
      Js.rec₀ (φ.pub m.st.input) (front.cut (firstLen J.p.nums.stages)))
    (hasks : ∃ Dp cc R, Dp.ts.length = os.length ∧
      ShapeAsksD { J with rec₀ := r' } m.st.input (restFront J m)
        (carriedCoins J (stretches _ ca)) (heardIn J m) K Dp ∧
      DataAsks { J with rec₀ := r' } m.st.input (restFront J m)
        (carriedCoins J (stretches _ ca)) (heardIn J m) Dp cc R)
    (htr : TreesAt J chain os (stretches _ ca) m front) :
    OnEntry φ J Js K chain os (restMember J Js) ca m front := fun _ =>
  ⟨r', hA, onFree_of_parts J Js K chain os _ _ m front r' h5 (hA _ _) hdoor hasks htr⟩

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.restMember_agree
#print axioms ProofFile.Honest.K12.Sim2.OnEntry
#print axioms ProofFile.Honest.K12.Sim2.onEntry_of_free
#print axioms ProofFile.Honest.K12.Sim2.agree_of_onEntry
#print axioms ProofFile.Honest.K12.Sim2.exact_rest_entry
#print axioms ProofFile.Honest.K12.Sim2.exact_both_entry
#print axioms ProofFile.Honest.K12.Sim2.onFree_of_parts
#print axioms ProofFile.Honest.K12.Sim2.onEntry_of_parts
