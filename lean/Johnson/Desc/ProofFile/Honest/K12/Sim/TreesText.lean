-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/TreesText.lean: the text of a proximity test from the first
switch on, at given rows, and the same text at rows 0 with one item laid anew: under a written
change of the random values the two show the same rounds, and the same columns at the positions that
the next reading round samples. As Sim/CoreText.lean, but at any list of trees in front, each of its
own depth. Equations between texts, at variables: no finite type of random values, no law. No
property is claimed: the state tB and the trees in front are variables: no sentence on a simulator.

By what. Sim/CoreText.lean ties the text to the library's `bodyAll` at the FIRST stage, which deals
one group from one tree. Here the tie is made at the SECOND stage (`restText_body`, over
`stages_eq`); the first switch's step is TreesStep.lean's; from the second stage on the library's
induction is called (`bodyShiftOr`), and Sim/CoreText.lean's `body_trees`, `shownFrom_congr`,
`virtK`.

  `restText_body`, `restEnd_body`   the text from the first switch on, and its letters at the last
                 stage, over `bodyAll` and `bodyEnd` from the second stage on
  `zeroTextK_trees`   the text at rows 0 reads the trees through the first opening's groups alone
  `t1T`, `rsT`, `t3T`, `bodyT`, `endT`, `shiftT`   the run's letters from the state tB on; `t3T_eq`,
                 `restText_at`, `restEnd_at`, `atStage_first_trees`: what ties them
  `t1_same_trees`, `rs_same_trees`, `t3_same_trees`   both runs reach one state behind the first
                 switch
  `body_rounds_trees`, `rounds_aux_trees`, `body_trees_trees`, `trees_aux_trees`,
  `rest_view_trees`   the rounds; the trees; what is shown
  `shiftT_one`   at one tree of the first stage's depth the shift is the library's `shB`

Limits. Three stages or more. The two lists of trees are asked to give the first opening the same
groups (`aGroups`): that is the premise of `Spec.core` (Sim/Spec.lean); nothing here says when it
holds. The first opening's groups are not among what is compared. The state behind the first fold is
what the description's fold returns from a variable tB over the text's own first fold's rounds;
where the description's fold, switch or batching rejects, `t1T` and `t3T` keep the state in hand
(`aRec1`, `aRec3`, Johnson/Desc/K12/Honest/Stages.lean: a fall-back), without a warning: nothing
here says that they accept. Columns: at the positions that the part's own next reading round
samples; at no other. The claim that is left at the first text's last stage is asked true, or the
last sampled element 0: a premise on the prover's data and random values; where the state holds no
claim it is the empty claim with target 0 that is asked true. `FitsBody` is asked whole; its first
three clauses are not used: the first two hold the first reading round's count against the first
stage's tails, the third is the packing's room. Nothing on completeness, soundness, hiding, or on
any law.

Sources. Five statements are Sim/CoreText.lean's with the trees turned, and the file carries out the
plan of Johnson/LinkSim/AtText/ (a shift of the random values): the note on sources in the head of
ShiftDefs.lean there holds here too.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreesWalk
import Johnson.Desc.ProofFile.Honest.K12.Sim.CoreText
import Johnson.Desc.K12.Honest.FirstYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)
open Johnson.Prover.Link
open OnBytes.LinkSim.AtText

/-! ## 1 The text from the first switch on, over `bodyAll` from the second stage on -/

section Body
variable (p : P12) (K : BCoins) (s next nx : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
  (o : ℕ) (t₁ : T12) (P : PS) (trees : List Tree) (D : ℕ → Fmt.Drawn) (row : GroupRow)

/-- **The text from the first switch on is the switch's own pieces, at any trees, and then
`bodyAll` from the second stage on.** -/
theorem restText_body (hf : FitAll next (nx :: rest)) :
    restText p K s next (nx :: rest) l o t₁ P trees D =
      ⟨aSwitch s o D (aAns p 0 s next o D t₁ (aNext K false 0 s next o P D)) ++
          (bodyAll p K (nx :: rest) 1 next (l.drop (s.k + 3)) (oNext s o)
            (aRec3 p false 0 s next l o trees D t₁
              (aSwitch s o D (aAns p 0 s next o D t₁ (aNext K false 0 s next o P D))))
            (sNext K false 0 s next o P row D) (sCol K false 0 s next o P row D) D).rs,
        [sCol K false 0 s next o P row D, fun _ => []] ++
          (bodyAll p K (nx :: rest) 1 next (l.drop (s.k + 3)) (oNext s o)
            (aRec3 p false 0 s next l o trees D t₁
              (aSwitch s o D (aAns p 0 s next o D t₁ (aNext K false 0 s next o P D))))
            (sNext K false 0 s next o P row D) (sCol K false 0 s next o P row D) D).tr,
        aGroups s o trees D ++
          (bodyAll p K (nx :: rest) 1 next (l.drop (s.k + 3)) (oNext s o)
            (aRec3 p false 0 s next l o trees D t₁
              (aSwitch s o D (aAns p 0 s next o D t₁ (aNext K false 0 s next o P D))))
            (sNext K false 0 s next o P row D) (sCol K false 0 s next o P row D) D).gs⟩ := by
  rw [col_eq, next_eq]
  unfold restText
  simp only
  rw [stages_eq p K (nx :: rest) 1 next _ _ _ _ _ D hf]
  rfl

/-- The same of the letters at the last stage. -/
theorem restEnd_body (hf : FitAll next (nx :: rest)) :
    restEnd p K s next (nx :: rest) l o t₁ P trees D =
      toEnd (bodyEnd p K D (nx :: rest) 1 next (l.drop (s.k + 3)) (oNext s o)
        (aRec3 p false 0 s next l o trees D t₁
          (aSwitch s o D (aAns p 0 s next o D t₁ (aNext K false 0 s next o P D))))
        (sNext K false 0 s next o P row D) (sCol K false 0 s next o P row D)) := by
  rw [col_eq, next_eq]
  unfold restEnd
  simp only
  rw [stagesEnd_eq p K (nx :: rest) 1 next _ _ _ _ _ D hf]
  rfl

end Body

/-- The text at rows 0 reads the trees in front through the first opening's groups alone. -/
theorem zeroTextK_trees (p : P12) (K : BCoins) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (l : Laid) (t₁ : T12) (trees trees' : List Tree) (D : ℕ → Fmt.Drawn)
    (h : aGroups s 1 trees D = aGroups s 1 trees' D) :
    zeroTextK p K s next rest l t₁ trees D = zeroTextK p K s next rest l t₁ trees' D := by
  unfold zeroTextK
  rw [(restText_trees p K s next rest l 1 t₁ zeroPS trees trees' D h).1,
    (restText_trees p K s next rest l 1 t₁ zeroPS trees trees' D h).2]

theorem set_behind {α : Type} (X B B' : List α) (i : ℕ) (v : α) (hB : B = B'.set i v)
    (hi : (X ++ B').length - 2 = X.length + i) :
    X ++ B = (X ++ B').set ((X ++ B').length - 2) v := by
  rw [hi, List.set_append_right _ _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left, hB]

/-! ## 2 The letters for the call -/

section Core
variable (p : P12) (s next nx : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid) (tB : T12)
  (trees : List Tree) (D : ℕ → Fmt.Drawn) (K : BCoins) (P : PS)

/-- The verifier's state behind the first fold, from the state tB in front of it; tB itself where
the description's fold rejects. -/
def t1T : T12 := aRec1 p 0 s l tB (aFold K 0 s 1 P (rowOf tB) D)

/-- The first switch's two rounds. -/
def rsT : List Fmt.RoundView :=
  aSwitch s 1 D (aAns p 0 s next 1 D (t1T p s l tB D K P) (aNext K false 0 s next 1 P D))

/-- The verifier's state behind the first switch, at the trees that the first opening reads; the
state in hand where the description's switch or batching rejects. It is `t3At`
(Johnson/Desc/K12/Honest/FirstYes.lean) where a stage or more follows `next`: `t3T_eq`. -/
def t3T : T12 := aRec3 p false 0 s next l 1 trees D (t1T p s l tB D K P) (rsT p s next l tB D K P)

theorem t3T_eq : t3T p s next l tB trees D K P =
    t3At p K (nx :: rest) 0 s next l 1 tB P trees D := rfl

/-- `bodyAll` from the second stage on, along the run from tB. -/
def bodyT : BOut :=
  bodyAll p K (nx :: rest) 1 next (l.drop (s.k + 3)) (oNext s 1) (t3T p s next l tB trees D K P)
    (sNext K false 0 s next 1 P (rowOf tB) D) (sCol K false 0 s next 1 P (rowOf tB) D) D

/-- The letters at the last stage, along that run. -/
def endT : BEnd :=
  bodyEnd p K D (nx :: rest) 1 next (l.drop (s.k + 3)) (oNext s 1) (t3T p s next l tB trees D K P)
    (sNext K false 0 s next 1 P (rowOf tB) D) (sCol K false 0 s next 1 P (rowOf tB) D)

theorem restText_at (hf : FitAll next (nx :: rest)) :
    restText p K s next (nx :: rest) l 1 (t1T p s l tB D K P) P trees D =
      ⟨rsT p s next l tB D K P ++ (bodyT p s next nx rest l tB trees D K P).rs,
        [sCol K false 0 s next 1 P (rowOf tB) D, fun _ => []] ++
          (bodyT p s next nx rest l tB trees D K P).tr,
        aGroups s 1 trees D ++ (bodyT p s next nx rest l tB trees D K P).gs⟩ := by
  unfold bodyT t3T rsT
  exact restText_body p K s next nx rest l 1 _ P trees D (rowOf tB) hf

theorem restEnd_at (hf : FitAll next (nx :: rest)) :
    restEnd p K s next (nx :: rest) l 1 (t1T p s l tB D K P) P trees D =
      toEnd (endT p s next nx rest l tB trees D K P) := by
  unfold endT t3T rsT
  exact restEnd_body p K s next nx rest l 1 _ P trees D (rowOf tB) hf

/-- The shift, along the run at the rows P, at the text's own state behind the first switch. -/
def shiftT : BCoins :=
  shT p K D nx rest 0 s next l 1 tB P (t3T p s next l tB trees D K P) P

/-- **What holds in front of the first stage**, at any letter t₃, between the run at the rows P and
the run at rows 0 whose letters are more by the shift, the first coefficients as `virtK` lays them.
-/
theorem atStage_first_trees (t₃ : T12) :
    AtStageT p D nx rest 0 s next l 1 tB t₃ K
      (virtK (addB K (shT p K D nx rest 0 s next l 1 tB P t₃ P)) K tB P D) P zPS P where
  st := add_zPS P
  foldW := rfl
  fr := fun _ _ => rfl
  new := fun _ _ => rfl
  W := fun _ i hi => by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hi
    rw [show 0 + n + 1 = n + 1 by omega]
    rfl

end Core

/-! ## 3 Both runs reach one state behind the first switch -/

section Runs
variable {p : P12} {s next nx : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {l : Laid} {tB : T12}
  {P₀ : PS} {D : ℕ → Fmt.Drawn} {t₃ : T12} {Kr Ks : BCoins}

theorem t1_same_trees (hF : FitsBody D (next :: nx :: rest) s 1)
    (hA : AtStageT p D nx rest 0 s next l 1 tB t₃ Kr Ks P₀ zPS P₀) :
    t1T p s l tB D Kr P₀ = t1T p s l tB D Ks zPS :=
  congrArg (aRec1 p 0 s l tB) ((fold_eq Kr 0 s 1 P₀ (rowOf tB) D).symm.trans
    ((sRF_same_trees (atSwitch_of_trees hF hA)).trans (fold_eq Ks 0 s 1 zPS (rowOf tB) D)))

theorem rs_same_trees (hF : FitsBody D (next :: nx :: rest) s 1)
    (hA : AtStageT p D nx rest 0 s next l 1 tB t₃ Kr Ks P₀ zPS P₀) :
    rsT p s next l tB D Kr P₀ = rsT p s next l tB D Ks zPS :=
  (switch_eq p Kr false 0 s next l 1 tB P₀ (rowOf tB) D hF.2.2.2.1).symm.trans
    ((sRS_same_trees (atSwitch_of_trees hF hA)).trans
      (switch_eq p Ks false 0 s next l 1 tB zPS (rowOf tB) D hF.2.2.2.1))

/-- **The verifier's state behind the first switch is one in both runs**, at any trees. -/
theorem t3_same_trees (trees : List Tree) (hF : FitsBody D (next :: nx :: rest) s 1)
    (hA : AtStageT p D nx rest 0 s next l 1 tB t₃ Kr Ks P₀ zPS P₀) :
    t3T p s next l tB trees D Kr P₀ = t3T p s next l tB trees D Ks zPS := by
  unfold t3T
  rw [t1_same_trees hF hA, rs_same_trees hF hA]

end Runs

/-! ## 4 The rounds -/

section Texts
variable {p : P12} {s next nx : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {l : Laid} {tB : T12}
  {P₀ : PS} {trees : List Tree} {D : ℕ → Fmt.Drawn} {Kr Ks : BCoins}

theorem body_rounds_trees (hF : FitsBody D (next :: nx :: rest) s 1)
    (hA : AtStageT p D nx rest 0 s next l 1 tB (t3T p s next l tB trees D Kr P₀) Kr Ks P₀ zPS P₀)
    (hcl : LamZero D (endT p s next nx rest l tB trees D Kr P₀) ∨
      OnBytes.LinkSim.AtText.ClaimTrue p (endT p s next nx rest l tB trees D Kr P₀)) :
    (bodyT p s next nx rest l tB trees D Kr P₀).rs =
      (bodyT p s next nx rest l tB trees D Ks zPS).rs.set
        ((endT p s next nx rest l tB trees D Ks zPS).o - oNext s 1)
        ⟨[.e (tauStar p (endT p s next nx rest l tB trees D Ks zPS) D)],
          D (endT p s next nx rest l tB trees D Ks zPS).o⟩ := by
  have h := (bodyShiftOr p D (nx :: rest) 1 next (l.drop (s.k + 3)) (oNext s 1) _ Kr Ks _ _ _ _ _
    hF.2.2.2.2 (atStage_second hF hA) hcl).2
  unfold bodyT endT
  rw [← t3_same_trees trees hF hA]
  exact h

theorem rounds_aux_trees (hF : FitsBody D (next :: nx :: rest) s 1)
    (hA : AtStageT p D nx rest 0 s next l 1 tB (t3T p s next l tB trees D Kr P₀) Kr Ks P₀ zPS P₀)
    (hcl : LamZero D (endT p s next nx rest l tB trees D Kr P₀) ∨
      OnBytes.LinkSim.AtText.ClaimTrue p (endT p s next nx rest l tB trees D Kr P₀)) :
    (restText p Kr s next (nx :: rest) l 1 (t1T p s l tB D Kr P₀) P₀ trees D).rs =
      (zeroTextK p Ks s next (nx :: rest) l (t1T p s l tB D Ks zPS) trees D).rs := by
  have hf := (fitAll_of_fits _ _ _ hF).2
  have hlen : (bodyT p s next nx rest l tB trees D Ks zPS).rs.length =
      (endT p s next nx rest l tB trees D Ks zPS).o - oNext s 1 + 2 :=
    length_body p Ks D (nx :: rest) 1 next (l.drop (s.k + 3)) (oNext s 1) _ _ _
  unfold zeroTextK
  rw [show (zeroPS : PS) = zPS from rfl, restText_at p s next nx rest l tB trees D Kr P₀ hf,
    restText_at p s next nx rest l tB trees D Ks zPS hf,
    restEnd_at p s next nx rest l tB trees D Ks zPS hf]
  dsimp only
  rw [tauSim_eq, rs_same_trees hF hA]
  refine set_behind _ _ _ _ _ (body_rounds_trees hF hA hcl) ?_
  rw [List.length_append, hlen]
  have h2 : (rsT p s next l tB D Ks zPS).length = 2 := rfl
  rw [h2]
  omega

/-! ## 5 The trees -/

theorem body_trees_trees (hF : FitsBody D (next :: nx :: rest) s 1)
    (hA : AtStageT p D nx rest 0 s next l 1 tB (t3T p s next l tB trees D Kr P₀) Kr Ks P₀ zPS P₀)
    (i : ℕ) :
    ((((bodyT p s next nx rest l tB trees D Kr P₀).tr.getD i fun _ => []) 0).length =
        (((bodyT p s next nx rest l tB trees D Ks zPS).tr.getD i fun _ => []) 0).length) ∧
      ∀ q ∈ openedTr D (nx :: rest) next (oNext s 1) i,
        ((bodyT p s next nx rest l tB trees D Kr P₀).tr.getD i fun _ => []) q =
          ((bodyT p s next nx rest l tB trees D Ks zPS).tr.getD i fun _ => []) q := by
  have h := body_trees p D (nx :: rest) 1 next (l.drop (s.k + 3)) (oNext s 1) _ Kr Ks _ _ _ _ _
    hF.2.2.2.2 (atStage_second hF hA) i
  unfold bodyT
  rw [← t3_same_trees trees hF hA]
  exact h

theorem getD_two {α : Type} (a b : α) (L : List α) (i : ℕ) (d : α) :
    ([a, b] ++ L).getD (i + 2) d = L.getD i d := rfl

theorem getD_two_zero {α : Type} (a b : α) (L : List α) (d : α) : ([a, b] ++ L).getD 0 d = a := rfl

theorem getD_two_one {α : Type} (a b : α) (L : List α) (d : α) : ([a, b] ++ L).getD 1 d = b := rfl

theorem trees_aux_trees (hF : FitsBody D (next :: nx :: rest) s 1)
    (hA : AtStageT p D nx rest 0 s next l 1 tB (t3T p s next l tB trees D Kr P₀) Kr Ks P₀ zPS P₀)
    (i : ℕ) :
    (((restText p Kr s next (nx :: rest) l 1 (t1T p s l tB D Kr P₀) P₀ trees D).tr.getD i
        fun _ => []) 0).length =
      (((restText p Ks s next (nx :: rest) l 1 (t1T p s l tB D Ks zPS) zPS trees D).tr.getD i
        fun _ => []) 0).length ∧
    ∀ q ∈ openedTr D (next :: nx :: rest) s 1 (1 + ((sgOf s).h + (sgOf s).g) + i),
      ((restText p Kr s next (nx :: rest) l 1 (t1T p s l tB D Kr P₀) P₀ trees D).tr.getD i
        fun _ => []) q =
      ((restText p Ks s next (nx :: rest) l 1 (t1T p s l tB D Ks zPS) zPS trees D).tr.getD i
        fun _ => []) q := by
  have hf := (fitAll_of_fits _ _ _ hF).2
  have hS := atSwitch_of_trees hF hA
  rw [restText_at p s next nx rest l tB trees D Kr P₀ hf,
    restText_at p s next nx rest l tB trees D Ks zPS hf]
  dsimp only
  rcases i with _ | _ | i
  · rw [getD_two_zero, getD_two_zero]
    refine ⟨by rw [length_sCol, length_sCol], fun q hq => ?_⟩
    unfold openedTr at hq
    rw [if_neg (by omega), if_pos (by omega)] at hq
    exact sCol_same_trees hS hq
  · rw [getD_two_one, getD_two_one]
    exact ⟨rfl, fun _ _ => rfl⟩
  · have e : openedTr D (next :: nx :: rest) s 1 (1 + ((sgOf s).h + (sgOf s).g) + (i + 1 + 1)) =
        openedTr D (nx :: rest) next (oNext s 1) i := by
      conv_lhs => unfold openedTr
      rw [if_neg (by omega), if_neg (by omega),
        show 1 + ((sgOf s).h + (sgOf s).g) + (i + 1 + 1) - ((sgOf s).h + (sgOf s).g + 3) = i by
          omega]
    rw [e, getD_two, getD_two]
    exact body_trees_trees hF hA i

end Texts

/-! ## 6 What is shown -/

/-- **What is shown from the first switch on, at the rows P₀ and the trees treesR, is what is shown
of the text at rows 0 with the one item laid anew, at the trees treesF and at the letters more by
the shift**: under four premises: `FitsBody` (public); the two lists of trees give the first opening
the same groups; the claim left at the first run's last stage is true, or the last sampled element
is 0 (on the prover's data and random values); the positions asked of a later tree are among those
at which it is opened. -/
theorem rest_view_trees (p : P12) (s next nx : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
    (tB : T12) (P₀ : PS) (treesR treesF : List Tree) (D : ℕ → Fmt.Drawn) (Kr : BCoins)
    (dep : ℕ → Option ℕ) (n : ℕ) (asks : List (List (List ℕ)))
    (hF : FitsBody D (next :: nx :: rest) s 1)
    (hG : aGroups s 1 treesR D = aGroups s 1 treesF D)
    (hcl : LamZero D (endT p s next nx rest l tB treesR D Kr P₀) ∨
      OnBytes.LinkSim.AtText.ClaimTrue p (endT p s next nx rest l tB treesR D Kr P₀))
    (hasks : ∀ i, ∀ q ∈ (((asks[i]?).getD [])[0]?).getD [],
      q ∈ openedTr D (next :: nx :: rest) s 1 (1 + ((sgOf s).h + (sgOf s).g) + i)) :
    shownFrom (restText p Kr s next (nx :: rest) l 1 (t1T p s l tB D Kr P₀) P₀ treesR D) dep n
        asks =
      shownFrom (zeroTextK p (addB Kr (shiftT p s next nx rest l tB treesR D Kr P₀)) s next
        (nx :: rest) l (t1T p s l tB D Kr P₀) treesF D) dep n asks := by
  have hA := atStage_first_trees p s next nx rest l tB D Kr P₀ (t3T p s next l tB treesR D Kr P₀)
  have h1 := t1_same_trees hF hA
  rw [← zeroTextK_trees p _ s next (nx :: rest) l _ treesR treesF D hG,
    ← zeroTextK_congr p (virtK_same _ Kr tB P₀ D)]
  refine shownFrom_congr _ _ dep n asks ?_ (fun i => ?_) fun i q hq => ?_
  · have h := rounds_aux_trees hF hA hcl
    rw [← h1] at h
    exact h
  · have h := (trees_aux_trees hF hA i).1
    rw [← h1] at h
    exact h
  · have h := (trees_aux_trees hF hA i).2 q (hasks i q hq)
    rw [← h1] at h
    exact h

/-! ## 7 At one tree of the first stage's depth the shift is the library's -/

theorem shiftT_one (p : P12) (s next nx : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
    (tB : T12) (P₀ : PS) (D : ℕ → Fmt.Drawn) (col : ℕ → List UInt64) (K : BCoins)
    (hf : CsFit (sgOf s) (sgOf next)) :
    shiftT p s next nx rest l tB [((sgOf s).C.a, col)] D K P₀ =
      shB p K D (next :: nx :: rest) 0 s l 1 tB P₀ col P₀ := by
  rw [shB_trees]
  unfold shiftT t3T rsT t1T tNext
  rw [rec3_eq p K false 0 s next l 1 tB P₀ col (rowOf tB) D hf]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.restText_body
#print axioms ProofFile.Honest.K12.restEnd_body
#print axioms ProofFile.Honest.K12.zeroTextK_trees
#print axioms ProofFile.Honest.K12.set_behind
#print axioms ProofFile.Honest.K12.t1T
#print axioms ProofFile.Honest.K12.rsT
#print axioms ProofFile.Honest.K12.t3T
#print axioms ProofFile.Honest.K12.t3T_eq
#print axioms ProofFile.Honest.K12.bodyT
#print axioms ProofFile.Honest.K12.endT
#print axioms ProofFile.Honest.K12.restText_at
#print axioms ProofFile.Honest.K12.restEnd_at
#print axioms ProofFile.Honest.K12.shiftT
#print axioms ProofFile.Honest.K12.atStage_first_trees
#print axioms ProofFile.Honest.K12.t1_same_trees
#print axioms ProofFile.Honest.K12.rs_same_trees
#print axioms ProofFile.Honest.K12.t3_same_trees
#print axioms ProofFile.Honest.K12.body_rounds_trees
#print axioms ProofFile.Honest.K12.rounds_aux_trees
#print axioms ProofFile.Honest.K12.body_trees_trees
#print axioms ProofFile.Honest.K12.getD_two
#print axioms ProofFile.Honest.K12.getD_two_zero
#print axioms ProofFile.Honest.K12.getD_two_one
#print axioms ProofFile.Honest.K12.trees_aux_trees
#print axioms ProofFile.Honest.K12.rest_view_trees
#print axioms ProofFile.Honest.K12.shiftT_one
