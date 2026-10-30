-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/FirstCutLaw.lean: cutOk = true gives what first_half_of_step asks of the first
switch's cut; with it the first half of GroupsAre holds at the first stage of the proximity test
(the kind K12).

Statements and proofs, over Johnson/Desc/K12/Law/FirstCut.lean, Johnson/Desc/K12/Law/StepGroups.lean
and Johnson/Desc/K12/Law/FirstOkLaw.lean.
Main names:
  `cutAt_eq`: the test's cut is the frame's (by rfl).
  `cut_of_ok`: cutOk's clauses as propositions; and what the cut opens is what its second round
    opens (opensOf, Johnson/Desc/K12/Law/FirstOk.lean).
  `opens_a_of_ok`: gpOk's clause opens.a as a proposition; here it is spent.
  `sg_k`: the stage's row variables in the library's form are the place's, under h ≤ k.
  `first_half_paid`: under planOk, the first two lines of Block.step, cutOk, gpOk, and every
    position that the switch's second round drew lying in the stage's range, the groups dealt to the
    first switch stand, tree by tree in the book's order, at the trees' own lists under these draws.
Limits: No soundness is claimed, and nothing is said on hiding. The law of the proximity test is not
proved here.
What a yes of labelsOk (Johnson/Desc/K12/Law/FirstCut.lean) gives is stated and proved in
Johnson/Desc/K12/Law/LabelsLaw.lean (the declared labels, uncut, are the book's numbers); no theorem
of the law spends it. The clause cs.draws of cutOk is spent by no theorem.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.StepGroups
import Johnson.Desc.K12.Law.FirstCut

set_option autoImplicit false
namespace H2K.First
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw

theorem cutAt_eq (p : P12) (k : ℕ) : H2K.First.cutAt p k = cutS (laidS p) k := rfl

/-- cutOk's clauses, as propositions, at the frame's own cut. -/
theorem cut_of_ok (p : P12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : p.nums.stages = a :: rest) (h : cutOk p = true) :
    ∃ dS dC, cutS (laidS p) a.k = [dS, dC] ∧ dS.stored = [] ∧ dS.opens = [] ∧ dC.stored = [] ∧
      dC.entry.logN = a.C.a ∧ dC.opens = opensOf p a.k := by
  unfold cutOk at h
  rw [hs] at h
  dsimp only at h
  unfold ok cutL at h
  split at h
  · rename_i dS dC hc
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq,
      List.isEmpty_iff, decide_eq_true_eq] at h
    obtain ⟨_, h1, h2, h3, h4, _⟩ := h
    refine ⟨dS, dC, hc, h1, h2, h3, h4, ?_⟩
    have e := opensOf_cut p a.k
    have hc' : cutS ((((H2U.roundsOfNums p.nums).getD []).zip p.oracles).drop 1) a.k = [dS, dC] :=
        hc
    rw [hc'] at e
    rw [← e]
    simp [h2]
  · simp at h

/-- gpOk's clause opens.a, as a proposition. -/
theorem opens_a_of_ok (p : P12) (a : Fmt.M1.Stage) (row : GroupRow) (D : Plain)
    (h : ok (gpL p a row D) = true) : D.opens.map (·.1.a) = D.ts.map (logAt D.book) := by
  unfold ok gpL at h
  dsimp only at h
  rw [List.all_append, Bool.and_eq_true] at h
  have ht := h.2
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at ht
  exact ht.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- The stage's row variables in the library's form are the place's (under pubOk's clause "h ≤ k").
-/
theorem sg_k (a : Fmt.M1.Stage) (h : a.h ≤ a.k) : (sg a).h + (sg a).g = a.k := by
  show a.h + (a.k - a.h) = a.k
  omega

/-- GroupsAre's first half, paid: by the block's test on the plan, Block.step's first two lines,
cutOk (a test on the plan) and gpOk (its clause opens.a), where every position that the first
switch's second round drew lies in the stage's range. rS, rC: the switch's two rounds as shown. D:
the plain data that gpOf makes. -/
theorem first_half_paid {T Cl : Type} (X : Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) (F : ℕ) (rs : List Fmt.RoundView)
    (cols : List VerifiableInference.Desc.OpenedColumn)
    (hfit : roundsFit (proximityTestKind X p : Block T Cl).rounds rs = true)
    (hcols : ((cols.take ((groupsOf F (proximityTestKind X p : Block T Cl).rounds
        (rs.map (·.drawn))).flatMap id).length).map (fun c => (c.1, c.2.1, c.2.2.length)) ==
      (groupsOf F (proximityTestKind X p : Block T Cl).rounds (rs.map (·.drawn))).flatMap id) = true)
    (t : T12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (row : GroupRow) (L : GroupLayout)
    (D : Plain) (hs : p.nums.stages = a :: rest) (hD : gpOf p t a L = some D)
    (hok : ok (gpL p a row D) = true) (hcut : cutOk p = true) (rS rC : Fmt.RoundView)
    (hrs : (rs.drop (1 + (1 + a.k))).take 2 = [rS, rC])
    (hr : ∀ x ∈ rC.drawn.poss, x < 2 ^ a.C.a) :
    List.Forall₂ (fun z grp => grp.map (·.1) =
        (ownAt (logAt D.book z) (Positions.ofDraws a.C.a rC.drawn.poss)).toList) D.ts
      (grpS (laidS p) a.k (grpsS p (regroup ((groupsOf F (proximityTestKind X p : Block T Cl).rounds
          (rs.map (·.drawn))).map (·.length))
        (cols.take ((groupsOf F (proximityTestKind X p : Block T Cl).rounds
          (rs.map (·.drawn))).flatMap id).length)))) := by
  obtain ⟨dS, dC, c1, c2, c3, c4, _, c6⟩ := cut_of_ok p a rest hs hcut
  exact first_half_of_step X p hp F rs cols hfit hcols a.k dS dC c1 c2 c3 c4 rS rC hrs
    (logAt D.book) D.ts a.C.a
    (by rw [c6, ← (made_of p t a L D hD).opens]; exact opens_a_of_ok p a row D hok) hr

end H2K.First
