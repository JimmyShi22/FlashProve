-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/TreesLaw.lean: over a proximity test's random values from the
first switch on, sampled uniformly: what is shown of the text at given rows, and what is shown of
the text at rows 0 with one item laid anew, have one law. As Sim/CoreLaw.lean, Sim/CoreOwn.lean and
Sim/ClaimBody.lean, but at any lists of trees in front, each tree of its own depth, that give the
first opening the same groups of columns. An equation of two texts' laws. No property is claimed,
and it is no sentence on a simulator: the state tB, the first fold's coefficients and the trees in
front are variables: nothing here says that they are made of public things.

On the right side the rows P₀ and the first fold's coefficients still stand, through `entryOf` alone
(Sim/CoreLaw.lean): the verifier's state behind the first fold, a function of tB and of the first
fold's rounds as they are shown.

  `realViewT`, `zeroViewT`, `core_upTo_trees`, `core_body_trees`   over the library's finite type
                 `BodyK`: the two views are one up to a change that can be undone; the law
  `realOwnT`, `zeroOwnT`, `endOwnT`, `EndOkT`, `core_own_trees`   over the second part's own
                 numbered random values
  `realOwn_trees`, `zeroOwn_trees`, `behindFirst_trees`   at one tree of the first stage's depth
                 these three definitions are other files': by unfolding; the other four have no
                 such equation
  `BehindFirstT`, `endOk_of_body_trees`, `core_inv_trees`   the law with the invariant of the later
                 stages behind the first switch in the place of the premise on the last claim

By what. `rest_view_trees` (Sim/TreesText.lean), `walkSame_trees` and `inBody_sh_trees`
(Sim/TreesWalk.lean), `t3_same_trees`; all else as in the three elder files, whose lemmas on the
finite type, on the two readers of the random values and on the last claim take the trees as a
variable and are called.

Limits. Three stages or more. The invariant is asked at every value of the part's random values.
`core_body_trees` and `core_own_trees` name neither arm of the first fold. `core_inv_trees` holds
emptily where the first fold sends its own fresh table: `BehindFirstT` is `BodyInv` at `PlanAll`
(Johnson/Prover/Link/BodyInv.lean, BodyCloseB.lean), whose `PlanFrom` (FormStepPlan.lean) asks
`ownMask = false` at every stage, so no state meets it at such a place; whether `EndOkT` can be met
there is not shown. And it can be met only where the claim's form has no written-out factor: in
front of a stage that is not the last `BodyInv` asks `FormInv`, whose field `plain`
(Johnson/Prover/Link/FormInv.lean) says so; by the library's own heads the key file's and the proof
file's tests take in rows with such factors (FormRow.lean, BodyInv.lean, Limits). Every law here
asks `FitsBody` (Johnson/LinkSim/AtText/SpecShift.lean: each stage fits the next; the sampled
positions, counted with repeats, are no more than a row's tail; the packing's room; h = g = 0 at the
last stage); `core_own_trees` and `core_inv_trees` also h ≤ k behind the first stage. The other
limits of `core_own` (Sim/CoreOwn.lean) stand but for "one tree"; among them: the state behind the
first fold is what the description's fold returns from a variable tB, or tB where it rejects; the
positions asked of a tree are among those that the next reading round samples; how many rounds are
shown is a variable. No theorem gives `core_own` or `core_inv` back from the laws here, and those
hold at two stages: as it stands this is no generalisation of them. "Uniformly" is said of the
finite type over which both sides are mapped, and of nothing that is shown. Nothing on completeness,
soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesText
import Johnson.Desc.ProofFile.Honest.K12.Sim.ClaimBody

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open OnBytes.LinkSim (UpToShift)
open OnBytes.LinkSim.AtText (zPS addPS addB FitsBody LamZero InBody LaidFrom addBody)
open OnBytes.LinkSim.Seam (inv_end claimTrue_of_inv)

attribute [local instance] bodyFintype bodyNonempty csNonempty

/-! ## 1 Over the library's finite type -/

section Core
variable (p : P12) (s next nx : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid) (tB : T12)
  (P₀ : PS) (W0 : ∀ σ : Sg, HIdx (sVars GE 2 (σ.h + σ.g)) → GE) (treesR treesF : List Tree)
  (D : ℕ → Fmt.Drawn) (dep : ℕ → Option ℕ) (n : ℕ) (asks : List (List (List ℕ)))

theorem t1T_lay (k : BodyK GE s (next :: nx :: rest)) :
    t1T p s l tB D (layBody s (next :: nx :: rest) W0 k) P₀ = entryOf p s l tB P₀ W0 D := rfl

/-- What is shown of the text at the rows P₀ and the trees treesR. -/
def realViewT (k : BodyK GE s (next :: nx :: rest)) : List Shown :=
  shownFrom (restText p (layBody s (next :: nx :: rest) W0 k) s next (nx :: rest) l 1
    (entryOf p s l tB P₀ W0 D) P₀ treesR D) dep n asks

/-- What is shown of the text at rows 0 and the trees treesF, with the one item laid anew. -/
def zeroViewT (k : BodyK GE s (next :: nx :: rest)) : List Shown :=
  shownFrom (zeroTextK p (layBody s (next :: nx :: rest) W0 k) s next (nx :: rest) l
    (entryOf p s l tB P₀ W0 D) treesF D) dep n asks

variable (hF : FitsBody D (next :: nx :: rest) s 1)
  (hG : aGroups s 1 treesR D = aGroups s 1 treesF D)
  (hcl : ∀ k : BodyK GE s (next :: nx :: rest),
    LamZero D (endT p s next nx rest l tB treesR D (layBody s (next :: nx :: rest) W0 k) P₀) ∨
      OnBytes.LinkSim.AtText.ClaimTrue p
        (endT p s next nx rest l tB treesR D (layBody s (next :: nx :: rest) W0 k) P₀))
  (hasks : ∀ i, ∀ q ∈ (((asks[i]?).getD [])[0]?).getD [],
    q ∈ openedTr D (next :: nx :: rest) s 1 (1 + ((sgOf s).h + (sgOf s).g) + i))

include hF hG hcl hasks in
/-- **The two are one up to a change of the random values that can be undone.** -/
theorem core_upTo_trees :
    UpToShift (addBody s (next :: nx :: rest))
      (realViewT p s next nx rest l tB P₀ W0 treesR D dep n asks)
      (zeroViewT p s next nx rest l tB P₀ W0 treesF D dep n asks) := by
  refine ⟨fun k => backOf s (next :: nx :: rest)
      (shiftT p s next nx rest l tB treesR D (layBody s (next :: nx :: rest) W0 k) P₀),
    fun k => backOf s (next :: nx :: rest)
      (shT p (virtK (layBody s (next :: nx :: rest) W0 k) (layBody s (next :: nx :: rest) W0 k) tB
          P₀ D) D nx rest 0 s next l 1 tB zPS
        (t3T p s next l tB treesR D
          (virtK (layBody s (next :: nx :: rest) W0 k) (layBody s (next :: nx :: rest) W0 k) tB P₀
            D) zPS) P₀), fun k => ?_⟩
  have hb : LaidFrom s (next :: nx :: rest) (backOf s (next :: nx :: rest)
      (shiftT p s next nx rest l tB treesR D (layBody s (next :: nx :: rest) W0 k) P₀)) 0
      (shiftT p s next nx rest l tB treesR D (layBody s (next :: nx :: rest) W0 k) P₀) :=
    backOf_spec (inBody_sh_trees p (layBody s (next :: nx :: rest) W0 k) D nx rest 0 s next
      l 1 tB P₀ (t3T p s next l tB treesR D (layBody s (next :: nx :: rest) W0 k) P₀) P₀ hF)
  have hA := atStage_first_trees p s next nx rest l tB D (layBody s (next :: nx :: rest) W0 k) P₀
    (t3T p s next l tB treesR D (layBody s (next :: nx :: rest) W0 k) P₀)
  refine ⟨?_, ?_⟩
  · have hv := rest_view_trees p s next nx rest l tB P₀ treesR treesF D
      (layBody s (next :: nx :: rest) W0 k) dep n asks hF hG (hcl k) hasks
    rw [t1T_lay] at hv
    unfold realViewT zeroViewT
    beta_reduce
    rw [zeroTextK_congr p (lay_add W0 k _ hb)]
    exact hv
  · beta_reduce
    rw [virt_add W0 k _ hb tB P₀ D]
    refine congrArg _ ?_
    have h3 := t3_same_trees treesR hF hA
    have hw := walkSame_trees hF hA
    unfold shiftT at h3 hw ⊢
    rw [← h3]
    exact hw

include hF hG hcl hasks in
/-- **The law, over the library's finite type.** -/
theorem core_body_trees :
    (Prob.unif (BodyK GE s (next :: nx :: rest))).map
        (realViewT p s next nx rest l tB P₀ W0 treesR D dep n asks) =
      (Prob.unif (BodyK GE s (next :: nx :: rest))).map
        (zeroViewT p s next nx rest l tB P₀ W0 treesF D dep n asks) :=
  UpToShift.law_eq body_cancel
    (core_upTo_trees p s next nx rest l tB P₀ W0 treesR treesF D dep n asks hF hG hcl hasks)

end Core

/-! ## 2 Over the second part's own numbered random values -/

section Own
variable (p : P12) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid) (tB : T12)
  (P₀ : PS) (hide : ℕ → GE) (treesR treesF : List Tree) (D : ℕ → Fmt.Drawn) (dep : ℕ → Option ℕ)
  (n : ℕ) (asks : List (List (List ℕ)))

/-- What is shown of the text at the rows P₀ and the trees treesR, at random values by number. -/
def realOwnT (c : ℕ → GE) : List Shown :=
  shownFrom (restText p (coinsOf (s :: next :: rest) hide c) s next rest l 1
    (entryOf p s l tB P₀ (hideW hide) D) P₀ treesR D) dep n asks

/-- What is shown of the text at rows 0 and the trees treesF with the one item laid anew. -/
def zeroOwnT (c : ℕ → GE) : List Shown :=
  shownFrom (zeroText p s next rest l (entryOf p s l tB P₀ (hideW hide) D) treesF c D) dep n asks

/-- The last stage's letters of the text at the rows P₀. -/
def endOwnT (c : ℕ → GE) : EndAt :=
  restEnd p (coinsOf (s :: next :: rest) hide c) s next rest l 1
    (entryOf p s l tB P₀ (hideW hide) D) P₀ treesR D

/-- The premise on the last claim: the last sampled element is 0, or the claim that is left at the
last stage is true on the last message. -/
def EndOkT (c : ℕ → GE) : Prop :=
  toE ((D (endOwnT p s next rest l tB P₀ hide treesR D c).o).elems.headD (0, 0, 0)) = 0 ∨
    EndTrue p (endOwnT p s next rest l tB P₀ hide treesR D c)

/-- At one tree of the first stage's depth they are Sim/CoreOwn.lean's. -/
theorem realOwn_trees (col : ℕ → List UInt64) (c : ℕ → GE) :
    realOwn p s next rest l tB P₀ hide col D dep n asks c =
      realOwnT p s next rest l tB P₀ hide [((sgOf s).C.a, col)] D dep n asks c := rfl

theorem zeroOwn_trees (col : ℕ → List UInt64) (c : ℕ → GE) :
    zeroOwn p s next rest l tB P₀ hide col D dep n asks c =
      zeroOwnT p s next rest l tB P₀ hide [((sgOf s).C.a, col)] D dep n asks c := rfl

end Own

section OwnLaw
variable (p : P12) (s next nx : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid) (tB : T12)
  (P₀ : PS) (hide : ℕ → GE) (treesR treesF : List Tree) (D : ℕ → Fmt.Drawn) (dep : ℕ → Option ℕ)
  (n : ℕ) (asks : List (List (List ℕ)))
  (hz : ∀ st, (s :: next :: nx :: rest).getLast? = some st → st.h = 0)

include hz in
theorem real_own_trees (c : ℕ → GE) :
    realOwnT p s next (nx :: rest) l tB P₀ hide treesR D dep n asks c =
      realViewT p s next nx rest l tB P₀ (hideW hide) treesR D dep n asks
        (toBody s (next :: nx :: rest) 0 c) := by
  unfold realOwnT realViewT
  rw [restText_same p s next (nx :: rest) l 1 (entryOf p s l tB P₀ (hideW hide) D) P₀ P₀ treesR D
    (own_same s next (nx :: rest) hide hide c hz) (PSame.refl _ _ _)]

include hz in
theorem zero_own_trees (c : ℕ → GE) :
    zeroOwnT p s next (nx :: rest) l tB P₀ hide treesF D dep n asks c =
      zeroViewT p s next nx rest l tB P₀ (hideW hide) treesF D dep n asks
        (toBody s (next :: nx :: rest) 0 c) := by
  unfold zeroOwnT zeroViewT zeroText
  rw [zeroTextK_same p s next (nx :: rest) l (entryOf p s l tB P₀ (hideW hide) D) treesF D
    (own_same s next (nx :: rest) hide (fun _ => 0) c hz)]

include hz in
/-- The premise on the last claim, carried over. -/
theorem claim_own_trees (hf : FitAll next (nx :: rest)) (c : ℕ → GE)
    (h : EndOkT p s next (nx :: rest) l tB P₀ hide treesR D c) :
    LamZero D (endT p s next nx rest l tB treesR D
        (layBody s (next :: nx :: rest) (hideW hide) (toBody s (next :: nx :: rest) 0 c)) P₀) ∨
      OnBytes.LinkSim.AtText.ClaimTrue p (endT p s next nx rest l tB treesR D
        (layBody s (next :: nx :: rest) (hideW hide) (toBody s (next :: nx :: rest) 0 c)) P₀) := by
  obtain ⟨Q, Q', hQ, e1, e2⟩ := restEnd_same p s next (nx :: rest) l 1
    (entryOf p s l tB P₀ (hideW hide) D) P₀ P₀ treesR D
    (own_same s next (nx :: rest) hide hide c hz) (PSame.refl _ _ _)
  have e3 := restEnd_at p s next nx rest l tB treesR D
    (layBody s (next :: nx :: rest) (hideW hide) (toBody s (next :: nx :: rest) 0 c)) P₀ hf
  rw [t1T_lay] at e3
  have e4 : toEnd (endT p s next nx rest l tB treesR D
      (layBody s (next :: nx :: rest) (hideW hide) (toBody s (next :: nx :: rest) 0 c)) P₀) =
      { endOwnT p s next (nx :: rest) l tB P₀ hide treesR D c with P := Q' } := e3.symm.trans e2
  rcases h with h | h
  · left
    have e5 := congrArg EndAt.o e4
    exact (congrArg (fun o => toE ((D o).elems.headD (0, 0, 0))) e5).trans h
  · right
    have h1 : EndTrue p { endOwnT p s next (nx :: rest) l tB P₀ hide treesR D c with P := Q } :=
      Eq.mp (congrArg (EndTrue p) e1) h
    have h2 := (endTrue_same p (endOwnT p s next (nx :: rest) l tB P₀ hide treesR D c) Q Q' hQ).1 h1
    exact (claim_iff p _).2 (Eq.mpr (congrArg (EndTrue p) e4) h2)

omit hz

variable (hF : FitsBody D (next :: nx :: rest) s 1) (hlow : ∀ st ∈ next :: nx :: rest, st.h ≤ st.k)
  (hG : aGroups s 1 treesR D = aGroups s 1 treesF D)
  (hcl : ∀ c : OwnCs s (next :: nx :: rest),
    EndOkT p s next (nx :: rest) l tB P₀ hide treesR D (stretchOf c).e)
  (hasks : ∀ i, ∀ q ∈ (((asks[i]?).getD [])[0]?).getD [],
    q ∈ openedTr D (next :: nx :: rest) s 1 (1 + ((sgOf s).h + (sgOf s).g) + i))

include hF hlow hcl in
theorem claim_all_trees (k : BodyK GE s (next :: nx :: rest)) :
    LamZero D (endT p s next nx rest l tB treesR D
        (layBody s (next :: nx :: rest) (hideW hide) k) P₀) ∨
      OnBytes.LinkSim.AtText.ClaimTrue p (endT p s next nx rest l tB treesR D
        (layBody s (next :: nx :: rest) (hideW hide) k) P₀) := by
  obtain ⟨c, rfl⟩ := (toBody_bij s (next :: nx :: rest) hlow).2 k
  exact claim_own_trees p s next nx rest l tB P₀ hide treesR D
    (lastZero (next :: nx :: rest) s 1 hF) (fitAll_of_fits _ _ _ hF).2 (stretchOf c).e (hcl c)

include hF hlow hG hcl hasks in
/-- **The law, at the second part's own random values.** -/
theorem core_own_trees :
    PMF.map (fun c : OwnCs s (next :: nx :: rest) =>
        realOwnT p s next (nx :: rest) l tB P₀ hide treesR D dep n asks (stretchOf c).e)
        (Prob.unif (OwnCs s (next :: nx :: rest))) =
      PMF.map (fun c : OwnCs s (next :: nx :: rest) =>
        zeroOwnT p s next (nx :: rest) l tB P₀ hide treesF D dep n asks (stretchOf c).e)
        (Prob.unif (OwnCs s (next :: nx :: rest))) := by
  have hz := lastZero (next :: nx :: rest) s 1 hF
  have hm := Prob.map_unif_of_bijective (toBody_bij s (next :: nx :: rest) hlow)
  have hc := core_body_trees p s next nx rest l tB P₀ (hideW hide) treesR treesF D dep n asks hF hG
    (claim_all_trees p s next nx rest l tB P₀ hide treesR D hF hlow hcl) hasks
  rw [← hm, PMF.map_comp, PMF.map_comp] at hc
  have e1 : (fun c : OwnCs s (next :: nx :: rest) =>
      realOwnT p s next (nx :: rest) l tB P₀ hide treesR D dep n asks (stretchOf c).e) =
      realViewT p s next nx rest l tB P₀ (hideW hide) treesR D dep n asks ∘
        fun c : OwnCs s (next :: nx :: rest) => toBody s (next :: nx :: rest) 0 (stretchOf c).e :=
    funext fun c => real_own_trees p s next nx rest l tB P₀ hide treesR D dep n asks hz
      (stretchOf c).e
  have e2 : (fun c : OwnCs s (next :: nx :: rest) =>
      zeroOwnT p s next (nx :: rest) l tB P₀ hide treesF D dep n asks (stretchOf c).e) =
      zeroViewT p s next nx rest l tB P₀ (hideW hide) treesF D dep n asks ∘
        fun c : OwnCs s (next :: nx :: rest) => toBody s (next :: nx :: rest) 0 (stretchOf c).e :=
    funext fun c => zero_own_trees p s next nx rest l tB P₀ hide treesF D dep n asks hz
      (stretchOf c).e
  rw [e1, e2]
  exact hc

end OwnLaw

/-! ## 3 From the invariant of the later stages behind the first switch -/

section Inv
variable (p : P12) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid) (tB : T12)
  (P₀ : PS) (hide : ℕ → GE) (trees : List Tree) (D : ℕ → Fmt.Drawn)

/-- The invariant of the later stages, behind the first switch, at random values by number and at
the trees that the first opening reads. -/
def BehindFirstT (c : ℕ → GE) : Prop :=
  BodyInv p (coinsOf (s :: next :: rest) hide c) (PlanAll p) D rest 1 next (l.drop (s.k + 3))
    (1 + ((sgOf s).h + (sgOf s).g) + 3)
    (t3At p (coinsOf (s :: next :: rest) hide c) rest 0 s next l 1 tB P₀ trees D)
    (qAt (coinsOf (s :: next :: rest) hide c) rest 0 s next 1 P₀ D)
    (aCol rest.isEmpty next (qAt (coinsOf (s :: next :: rest) hide c) rest 0 s next 1 P₀ D))

theorem behindFirst_trees (col : ℕ → List UInt64) (c : ℕ → GE) :
    BehindFirst p s next rest l tB P₀ hide col D c =
      BehindFirstT p s next rest l tB P₀ hide [((sgOf s).C.a, col)] D c := rfl

theorem endOk_of_body_trees (hf : FitAll next rest) (c : ℕ → GE)
    (h : BehindFirstT p s next rest l tB P₀ hide trees D c) :
    EndOkT p s next rest l tB P₀ hide trees D c := by
  have h1 := (claim_iff p _).1 (claimTrue_of_inv p _ D _ (inv_end p _ D _ _ _ _ _ _ _ _ h))
  rw [← stagesEnd_eq p _ rest 1 next _ _ _ _ _ D hf] at h1
  exact Or.inr h1

end Inv

/-- **The law, from the invariant behind the first switch**, at any lists of trees that give the
first opening the same groups. -/
theorem core_inv_trees (p : P12) (s next nx : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
    (tB : T12) (P₀ : PS) (hide : ℕ → GE) (treesR treesF : List Tree) (D : ℕ → Fmt.Drawn)
    (dep : ℕ → Option ℕ) (n : ℕ) (asks : List (List (List ℕ)))
    (hF : FitsBody D (next :: nx :: rest) s 1) (hlow : ∀ st ∈ next :: nx :: rest, st.h ≤ st.k)
    (hG : aGroups s 1 treesR D = aGroups s 1 treesF D)
    (hbody : ∀ c : OwnCs s (next :: nx :: rest),
      BehindFirstT p s next (nx :: rest) l tB P₀ hide treesR D (stretchOf c).e)
    (hasks : ∀ i, ∀ q ∈ (((asks[i]?).getD [])[0]?).getD [],
      q ∈ openedTr D (next :: nx :: rest) s 1 (1 + ((sgOf s).h + (sgOf s).g) + i)) :
    PMF.map (fun c : OwnCs s (next :: nx :: rest) =>
        realOwnT p s next (nx :: rest) l tB P₀ hide treesR D dep n asks (stretchOf c).e)
        (Prob.unif (OwnCs s (next :: nx :: rest))) =
      PMF.map (fun c : OwnCs s (next :: nx :: rest) =>
        zeroOwnT p s next (nx :: rest) l tB P₀ hide treesF D dep n asks (stretchOf c).e)
        (Prob.unif (OwnCs s (next :: nx :: rest))) :=
  core_own_trees p s next nx rest l tB P₀ hide treesR treesF D dep n asks hF hlow hG
    (fun c => endOk_of_body_trees p s next (nx :: rest) l tB P₀ hide treesR D
      (fitAll_of_fits _ _ _ hF).2 (stretchOf c).e (hbody c)) hasks

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.t1T_lay
#print axioms ProofFile.Honest.K12.realViewT
#print axioms ProofFile.Honest.K12.zeroViewT
#print axioms ProofFile.Honest.K12.core_upTo_trees
#print axioms ProofFile.Honest.K12.core_body_trees
#print axioms ProofFile.Honest.K12.realOwnT
#print axioms ProofFile.Honest.K12.zeroOwnT
#print axioms ProofFile.Honest.K12.endOwnT
#print axioms ProofFile.Honest.K12.EndOkT
#print axioms ProofFile.Honest.K12.realOwn_trees
#print axioms ProofFile.Honest.K12.zeroOwn_trees
#print axioms ProofFile.Honest.K12.real_own_trees
#print axioms ProofFile.Honest.K12.zero_own_trees
#print axioms ProofFile.Honest.K12.claim_own_trees
#print axioms ProofFile.Honest.K12.claim_all_trees
#print axioms ProofFile.Honest.K12.core_own_trees
#print axioms ProofFile.Honest.K12.BehindFirstT
#print axioms ProofFile.Honest.K12.behindFirst_trees
#print axioms ProofFile.Honest.K12.endOk_of_body_trees
#print axioms ProofFile.Honest.K12.core_inv_trees
