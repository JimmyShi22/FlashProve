-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestReturns.lean: the stages of a proximity test accept, at any rounds
and columns of the declared form, under the four hypotheses of `stages_returns`, of which one,
`ValsFrom`, is on values; and under the other three they accept if and only if `ValsFrom` holds.
"The stages accept" means: the decision of their block (`stagesFrom`, Johnson/Desc/K12/Frame.lean,
at the parts `guardedProximityTestParts`, Johnson/Desc/K12/JoinGuarded.lean) returns `.ok`. The proof is an induction over
the stages on the form's half of the invariant only (`FormInv`, Johnson/Prover/Link/FormInv.lean).
General in the place's parameters, the list of stages, the structure before the stages, the rounds
and the columns. The verifier's structure alone: no prover, no coin, no frame for an honest side.
(That frame is Johnson/Desc/ProofFile/Honest/Frame.lean.)

Why. The lemmas on the test's single parts (Johnson/Prover/Link/: `form_step`, `hread_of`,
`formInv_next`, `lastForm_behind`, `baseJ5_yes`) hold at whatever rounds and columns have the
declared form. The induction over the stages in that folder (`body_yes_of`, BodyYes.lean) is used
with the invariant `BodyInv` (BodyInv.lean), which also speaks of a prover's values. Here the
induction is made on the form's half only, and what is asked of values is one named hypothesis.

In the list: p (`P12`, Johnson/Desc/K12/Frame.lean) holds the parameters of the place of a test. A
stage is a `Fmt.M1.Stage`; cur is the present stage, number j. A part (`Part`, same file) is a piece
of the test with a decision of its own: at a stage that is not the last the fold, the switch and the
batching after the switch, at the last stage the base case. t (`T12`, Johnson/Desc/K12/Join.lean) is
the verifier's structure inside a test. l (`Laid`, Frame.lean) lists the declared rounds from this
stage on, each with its oracle messages. A column is a position with a list of words. `noDigest`
(Johnson/Desc/Block.lean) sets the field `drawn.digest` of a round to `none`.

  `stages_returns`: from a stage that is not the last, under the plan from this stage on
    (`PlanFrom`, Johnson/Prover/Link/FormStepPlan.lean), `FormInv` before the fold, `ViewFrom` and
    `ValsFrom`: the stages' block accepts
  `vals_of_accept`, `vals_of_last`: the converse, with no other hypothesis, from any stage on and at
    the last stage: an accept of the stages gives `ValsFrom`. The parts are functions, so what they
    return is fixed, and the base case's decision returns the claim that it was handed, or refuses
    (`baseDecide_same`)
  `stages_accept_iff`: so, under the plan, the form's half and the view's form, the stages accept
    just where `ValsFrom` holds: beside what the view's form holds of drawn values, nothing else of
    the stages' own rounds and columns is tested on values
  `ViewFrom` (definition): the view's form from a stage on: at a stage that is not the last the
    fold's rounds and the switch's two are of the declared form, the round of the positions shows
    one answer, and one group is dealt, at the list of the drawn positions, each column of the
    declared width; at the last stage two rounds of the declared form and one group at the list of
    the drawn positions. Of what is shown it reads sorts and counts; of what is drawn: counts, the
    drawn positions themselves, that a drawn matrix entry is -1, 0 or 1, and what `drawsMarkedNonzeroHaveNonzeroWords` asks of
    elements drawn as non-zero; of a column its position and its length. For rounds, "of the
    declared form" is `roundsFit`; it and `drawsMarkedNonzeroHaveNonzeroWords` are in Johnson/Desc/Block.lean
  `ValsFrom` (definition): the one hypothesis on the values of the stages' own rounds and columns:
    at whatever structure the earlier parts return, the base case's own decision (`baseDecide`,
    Johnson/Desc/Prox/BaseCase.lean) accepts the claim written out. It is defined by recursion
    through the parts' own returns and is no closed formula on values: the claim is what the
    verifier's own parts make
  `stage_returns`: one stage that is not the last: the fold, the switch and the batching after it
    accept one after the other, at the cuts of rounds and groups of `stagesFrom_ok`
    (Johnson/Desc/K12/FrameLaws.lean); with `StepDone` (Johnson/Prover/Link/FormStep.lean),
    `FormInv` at the column function of the group that is dealt, and what the cuts leave of the
    rounds and the groups
  `last_returns`: the last stage accepts, under `BaseFront` (Johnson/Prover/Link/BasePart.lean), two
    declared rounds, `ViewFrom` and `ValsFrom`
  `formInv_recol`: the column function is read by one field of `FormInv`, `width`: `FormInv` holds
    as well at any other column function of that width
  `baseDecide_same`: where `baseDecide` returns a claim, it is the claim that it was handed

By what. In this paragraph a file without a folder is in Johnson/Prover/Link/. `stages_returns` goes
by recursion on the list of stages. At a stage, `stage_returns` gives the three decisions;
`ValsFrom` at these three gives `ValsFrom` from the next stage on; `formInv_next` (FormClose.lean)
gives `FormInv` at the next stage, or, before the last stage, `lastForm_behind` (FormLast.lean)
gives `LastForm`, whose field `front` is `BaseFront`; `stagesFrom_ok` joins the three decisions,
`StepDone.came` and the accept of the later stages. `formInv_next` is called at six zero functions:
they fill only the column function of the next `FormInv`, which `formInv_recol` replaces, and its
two other conclusions are not used. `stage_returns` calls `form_step` (FormStep.lean) and `hread_of`
(FormAt.lean), with `formInv_recol`, `switchCut_says`, `fit_says` (FormSwitchLaws.lean), `oF_of`,
`nS_of`, `oS_of` (BodyCuts.lean) and `roundsFit_len` (Johnson/Desc/Sound/Gather.lean).
`last_returns` calls `stagesFrom_last` (Johnson/Desc/K12/FrameLaws.lean), `ranged_yes`, `baseJ5_yes`
(BasePart.lean) and `inRange_fold` (FormFoldLaws.lean). Both call `roundsFit_noDigest`
(Johnson/Desc/K12/Law/TrOnto.lean). `vals_of_accept` reads `stagesFrom_ok` the other way.
`vals_of_last` calls `stagesFrom_last`, `ranged_ok` (Johnson/Desc/K12/Law/BaseGives.lean), `bind_ok`
(Johnson/Desc/K12/Law/FoldLaw.lean) and `baseDecide_same`, and unfolds `baseJ5`
(Johnson/Desc/K12/JoinGuarded.lean). `baseDecide_same` unfolds `baseDecide`.

Hypotheses of `stages_returns`. `PlanFrom`, at the codes of t: facts on the plan at every stage from
this one on (`StepPlan`, at the last stage `LastPlan`; `Dealt`; the plan's stages from number j on;
`p.nums.ownMask = false`). `FormInv`: clauses on t (its statement, its book, its count of roots and
the claim that it passes on) and on the tree that the plan declares, before the fold. `ViewFrom` at
R and gs. `ValsFrom` at `R.map noDigest` and gs.

Limits.
- No value that meets the hypotheses is given here: nothing in this file shows that the four
  hypotheses of `stages_returns` hold together anywhere. The proof of `k12_returns_one`
  (TestReturnsOne.lean, same folder) derives the four from its own hypotheses. That the four hold
  together anywhere is not stated as a theorem here.
- `stages_accept_iff` does not show it either: it says when the stages accept, not that they accept
  somewhere.
- "The declared form" is this file's own `ViewFrom`, not the library's test on a block's view
  (`Block.Fits`, Johnson/Top/H0/StepLaws/StepLaws.lean): no theorem here leads from the one to the
  other. `view_of_fits` (TestFits.lean in this folder) leads, under tests on the plan, from
  `Block.Fits` at the whole test's block to the test `viewFromB`, and `viewFrom_of_B`
  (TestView.lean, same folder) from that test to `ViewFrom`.
- `FormInv` and `PlanFrom` are premises, and they shut places out: `FormInv` holds that the count of
  roots is the plan's and one a switch; `PlanFrom` holds, at every stage, the place's flag that the
  first fold's mask came earlier: a place whose first fold sends its own mask is shut out from every
  stage on; `FormInv` holds that the claim's form has no written-out factor. In Lean: the fields
  `FormInv.roots` and `FormInv.plain`, and `p.nums.ownMask = false` in both arms of `PlanFrom`.
- `ValsFrom` asserts no accept of an earlier part. It holds vacuously where an earlier part refuses,
  where the structure before the base case passes no claim on, where the plan names no such stage,
  and where the claim cannot be written out.
- `ValsFrom` carries some form too: the base case's decision also refuses on the two last rounds'
  sorts, on the sizes of the claim's two vectors against the codes, and on a column that has not
  twelve words; `ViewFrom` asks no width at the last stage.
- The recursion of `ValsFrom` follows the three decisions of `stagesFrom_ok` and leaves out that
  theorem's clause `!p.early || X.maskCame t₃`: as a hypothesis it asks the more for that.
- At the last stage `ViewFrom` does not read its argument cur, and `ValsFrom` does not read l: a
  caller can pass anything there.
- The theorems begin before a fold: the test's front, its batching and a first stage whose group's
  members are in several trees are not here.
- What structure the stages return is not said: `stages_returns`, `last_returns` and
  `stages_accept_iff` state only that there is one.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Prover.Link.FormAt
import Johnson.Prover.Link.FormLast
import Johnson.Prover.Link.BodyCuts
import Johnson.Prover.Link.BasePart
import Johnson.Desc.K12.FrameLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Prox VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

/-! ## 1 The view's form, and the base case's test on values, from a stage on -/

/-- The view's form from a stage on. l: the declared rounds still to be dealt. R: the rounds, as the
view has them. gs: the groups of columns. At a stage that is not the last: the fold's rounds are of
the declared form; so are the switch's two; the round of the positions shows one answer; one group
is dealt: at the list of the drawn positions, each column of the declared width (col: the columns,
as a function of the position). At the last stage: two rounds of the declared form; one group, at
the list of the drawn positions. The first argument lists the stages after the present one, the
second is the present stage; at the last stage the second is not read. -/
def ViewFrom : List Fmt.M1.Stage → Fmt.M1.Stage → Laid → List Fmt.RoundView →
    List (List (ℕ × List UInt64)) → Prop
  | [], _, l, R, gs => ∃ rL rB g, R = [rL, rB] ∧ gs = [g] ∧ roundsFit (l.map (·.1)) R = true ∧
      g.map (·.1) = Fmt.listOf rB.drawn.poss
  | next :: rest, cur, l, R, gs =>
    ∃ (RF : List Fmt.RoundView) (rS rC : Fmt.RoundView) (R' : List Fmt.RoundView)
      (gs' : List (List (ℕ × List UInt64))) (a : Fmt.Ext) (col : ℕ → List UInt64),
      R = RF ++ rS :: rC :: R' ∧
      gs = ((Fmt.listOf (rC.drawn.poss.map (· % 2 ^ (sgOf cur).C.a))).map fun x => (x, col x)) ::
        gs' ∧
      roundsFit ((l.take (1 + cur.k)).map (·.1)) RF = true ∧
      roundsFit (((l.drop (1 + cur.k)).take 2).map (·.1)) [rS, rC] = true ∧
      rC.vals = [.answer a] ∧
      (∀ d ∈ ((l.drop (1 + cur.k)).take 2).map (·.1), ∀ o ∈ d.opens, ∀ x,
        (col x).length = o.1.W) ∧
      ViewFrom rest next (l.drop (cur.k + 3)) R' gs'

/-- The base case's test on values, from a stage on: at whatever structure the earlier parts return,
the base case's own decision accepts the claim written out. It asserts no accept of an earlier part.
rs: the rounds as a block's decision is shown them. It holds vacuously where an earlier part
refuses, where no claim is passed on, where the plan names no such stage, and where the claim cannot
be written out. At the last stage l is not read. -/
def ValsFrom (p : P12) : List Fmt.M1.Stage → ℕ → Fmt.M1.Stage → Laid → T12 → List Fmt.RoundView →
    List (List (ℕ × List UInt64)) → Prop
  | [], j, cur, _, t, rs, gs => ∀ row L c cl, t.pass = .claim row L → stageAt p j cur = some c →
      claimAt t.st.codes c row = some cl → baseDecide (basePar p cur) cl rs gs = .ok cl
  | next :: rest, j, cur, l, t, rs, gs => ∀ t₁ t₂ t₃,
      (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).decide t
        (rs.take (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).rounds.length)
        (gs.take (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).openings) = .ok t₁ →
      (switchAt guardedProximityTestParts p j cur next rest.isEmpty l : Block T12 Unit).decide t₁
        ((rs.drop (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).rounds.length).take
          (switchAt guardedProximityTestParts p j cur next rest.isEmpty l : Block T12 Unit).rounds.length)
        ((gs.drop (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).openings).take
          (switchAt guardedProximityTestParts p j cur next rest.isEmpty l : Block T12 Unit).openings) = .ok t₂ →
      (guardedProximityTestParts.batBehind p (j + 1) next (((l.drop (1 + cur.k)).take 2).map (·.1))).decide t₂ [] []
        = .ok t₃ →
      ValsFrom p rest (j + 1) next (l.drop (cur.k + 3)) t₃
        (rs.drop ((foldAt guardedProximityTestParts p j cur l : Block T12 Unit).rounds.length +
          (switchAt guardedProximityTestParts p j cur next rest.isEmpty l : Block T12 Unit).rounds.length))
        (gs.drop ((foldAt guardedProximityTestParts p j cur l : Block T12 Unit).openings +
          (switchAt guardedProximityTestParts p j cur next rest.isEmpty l : Block T12 Unit).openings))

/-! ## 2 The last stage -/

/-- The last stage accepts: its decision returns some structure. -/
theorem last_returns {p : P12} {j : ℕ} {cur : Fmt.M1.Stage} {l : Laid} {t : T12} {row : GroupRow}
    {L : GroupLayout} {c : IoppStage} {cl : BaseClaim} {m star a : ℕ} {d₁ d₂ : Fmt.DeclaredRound}
    (F : BaseFront p j cur t row L c cl m star a) (hcut : l.map (·.1) = [d₁, d₂])
    {R : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} (hV : ViewFrom [] cur l R gs)
    (hv : ValsFrom p [] j cur l t (R.map noDigest) gs) :
    ∃ tE, (stagesFrom guardedProximityTestParts p j cur [] l : Block T12 Unit).decide t (R.map noDigest) gs =
      .ok tE := by
  obtain ⟨rL, rB, g, rfl, rfl, hfit, hg⟩ := hV
  rw [stagesFrom_last, hcut]
  rw [hcut] at hfit
  have hfit' : roundsFit [d₁, d₂] ([rL, rB].map noDigest) = true :=
    (H2K.Onto.roundsFit_noDigest _ _).trans hfit
  show ∃ tE, (ranged [d₁, d₂] (baseJ5 p j cur [d₁, d₂])).decide t _ _ = .ok tE
  rw [ranged_yes _ _ _ _ _ (inRange_fold hfit')]
  exact ⟨_, baseJ5_yes p j cur d₁ d₂ t row L c cl m star a (noDigest rL) (noDigest rB) g F
    (hv row L c cl F.pass F.stage F.claim) hg⟩

/-! ## 3 One stage that is not the last -/

/-- `FormInv` holds as well at any other column function of the same width. -/
theorem formInv_recol {p : P12} {j : ℕ} {cur : Fmt.M1.Stage} {l : Laid} {t : T12}
    {col : ℕ → List UInt64} {row : GroupRow} {L : GroupLayout} {c : IoppStage} {n : ℕ × ℕ}
    {id tN : ℕ} {tr : Tree} (I : FormInv p j cur l t col row L c n id tN tr)
    (col' : ℕ → List UInt64)
    (h : ∀ x, (col' x).length = tr.shape.mainWidth + tr.shape.maskWidth) :
    FormInv p j cur l t col' row L c n id tN tr :=
  { I with width := h }

/-- What one stage that is not the last delivers, at any rounds and columns of the declared form:
the fold, the switch and the batching behind it accept in a row and leave the structure that
`stepT3` writes out (Johnson/Prover/Link/FormStep.lean), with `StepDone`, which holds that the next
mask has come. -/
theorem stage_returns {p : P12} {j : ℕ} {cur next : Fmt.M1.Stage} {last : Bool} {l : Laid}
    {c n : IoppStage} {dS dC : Fmt.DeclaredRound} {t : T12} {col : ℕ → List UInt64} {row : GroupRow}
    {L : GroupLayout} {id tN : ℕ} {tr : Tree}
    (Pl : StepPlan p t.st.codes j cur next last l c n dS dC)
    (I : FormInv p j cur l t col row L c (n.code, n.maskCode) id tN tr)
    (RF : List Fmt.RoundView) (rS rC : Fmt.RoundView) (R' : List Fmt.RoundView)
    (gs' : List (List (ℕ × List UInt64))) (a : Fmt.Ext) (col' : ℕ → List UInt64)
    (fitF : roundsFit ((l.take (1 + cur.k)).map (·.1)) RF = true)
    (fitS : roundsFit (((l.drop (1 + cur.k)).take 2).map (·.1)) [rS, rC] = true)
    (hans : rC.vals = [.answer a])
    (hw : ∀ d ∈ ((l.drop (1 + cur.k)).take 2).map (·.1), ∀ o ∈ d.opens, ∀ x,
      (col' x).length = o.1.W) :
    ∃ D x row' t₂,
      StepDone (sgOf cur) (sgOf next) p n last dS dC
        (foldT t row L c (n.code, n.maskCode) id (RF.map noDigest)) (noDigest rS) (noDigest rC)
        [(Fmt.listOf (rC.drawn.poss.map (· % 2 ^ (sgOf cur).C.a))).map fun x => (x, col' x)]
        (foldOut t row L c id (RF.map noDigest)) t.st.groups.size j cur next tN a D x row' ∧
      FormInv p j cur l t col' row L c (n.code, n.maskCode) id tN tr ∧
      (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).decide t
        (((RF ++ rS :: rC :: R').map noDigest).take
          (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).rounds.length)
        ((((Fmt.listOf (rC.drawn.poss.map (· % 2 ^ (sgOf cur).C.a))).map
          fun x => (x, col' x)) :: gs').take
            (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).openings) =
        .ok (foldT t row L c (n.code, n.maskCode) id (RF.map noDigest)) ∧
      (switchAt guardedProximityTestParts p j cur next last l : Block T12 Unit).decide
        (foldT t row L c (n.code, n.maskCode) id (RF.map noDigest))
        ((((RF ++ rS :: rC :: R').map noDigest).drop
          (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).rounds.length).take
            (switchAt guardedProximityTestParts p j cur next last l : Block T12 Unit).rounds.length)
        (((((Fmt.listOf (rC.drawn.poss.map (· % 2 ^ (sgOf cur).C.a))).map
          fun x => (x, col' x)) :: gs').drop
            (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).openings).take
              (switchAt guardedProximityTestParts p j cur next last l : Block T12 Unit).openings) = .ok t₂ ∧
      (guardedProximityTestParts.batBehind p (j + 1) next (((l.drop (1 + cur.k)).take 2).map (·.1))).decide t₂ [] []
        = .ok (stepT3 p n last dS dC (foldT t row L c (n.code, n.maskCode) id (RF.map noDigest))
          (noDigest rC)
          [(Fmt.listOf (rC.drawn.poss.map (· % 2 ^ (sgOf cur).C.a))).map fun x => (x, col' x)]
          (foldOut t row L c id (RF.map noDigest)) t.st.groups.size D tN row') ∧
      ((RF ++ rS :: rC :: R').map noDigest).drop
        ((foldAt guardedProximityTestParts p j cur l : Block T12 Unit).rounds.length +
          (switchAt guardedProximityTestParts p j cur next last l : Block T12 Unit).rounds.length) =
            R'.map noDigest ∧
      (((Fmt.listOf (rC.drawn.poss.map (· % 2 ^ (sgOf cur).C.a))).map
          fun x => (x, col' x)) :: gs').drop
        ((foldAt guardedProximityTestParts p j cur l : Block T12 Unit).openings +
          (switchAt guardedProximityTestParts p j cur next last l : Block T12 Unit).openings) = gs' := by
  obtain ⟨o, ho, -, -, oW⟩ := I.decl dS dC Pl.cutS
  have I' := formInv_recol I col' fun x => by
    rw [← oW]
    exact hw dC (by rw [Pl.cutS]; simp) o (by rw [ho]; simp) x
  rw [Pl.cutS] at fitS
  have fitS' : roundsFit [dS, dC] [noDigest rS, noDigest rC] = true :=
    (H2K.Onto.roundsFit_noDigest [dS, dC] [rS, rC]).trans fitS
  obtain ⟨-, -, -, -, -, -, -, -, -, c10, -, -, -, s1, s2⟩ := switchCut_says Pl.cutSw
  obtain ⟨-, ⟨-, -, -, g5⟩, -⟩ := fit_says fitS'
  have hx : ∀ x ∈ (noDigest rC).drawn.poss, x < 2 ^ (sgOf cur).C.a := by
    intro z hz
    have := List.all_eq_true.1 g5 z hz
    rw [c10] at this
    exact of_decide_eq_true this
  obtain ⟨hfold, D, x, row', Dn⟩ := form_step Pl I' RF fitF (noDigest rS) (noDigest rC) fitS' a
    hans _ (fun D => hread_of Pl I' RF fitF (noDigest rC) hx D)
  have nF : (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).rounds.length = RF.length := by
    show ((l.take (1 + cur.k)).map (·.1)).length = _
    exact (Sound.roundsFit_len _ _ fitF).symm
  have ck : c.k = cur.k := by
    rw [Pl.codes.k]
    exact Nat.add_sub_cancel' Pl.hk
  have oF := oF_of p j cur l (ck ▸ Pl.cutF)
  have nS := nS_of p j cur next last l dS dC Pl.cutS
  have oS := oS_of p j cur next last l dS dC Pl.cutS (by simpa using s1) (by simpa using s2)
    Pl.opensS Pl.opensC
  refine ⟨D, x, row', switchT p n last (foldT t row L c (n.code, n.maskCode) id (RF.map noDigest))
    (noDigest rC) t.st.groups.size D
    (stepB p n last dS dC (foldT t row L c (n.code, n.maskCode) id (RF.map noDigest)) (noDigest rC)
      [(Fmt.listOf (rC.drawn.poss.map (· % 2 ^ (sgOf cur).C.a))).map fun x => (x, col' x)]
      (foldOut t row L c id (RF.map noDigest)) t.st.groups.size D tN) (E.ofTriple x),
    Dn, I', ?_, ?_, ?_, ?_, ?_⟩
  · rw [nF, oF, List.map_append, ← List.length_map (f := noDigest) (as := RF),
      List.take_left]
    exact hfold
  · rw [nF, nS, oF, oS, List.map_append, ← List.length_map (f := noDigest) (as := RF),
      List.drop_left]
    show (guardedProximityTestParts.switch p j cur next last (((l.drop (1 + cur.k)).take 2).map (·.1))).decide
      _ [noDigest rS, noDigest rC] [_] = _
    rw [Pl.cutS]
    exact Dn.switch
  · rw [Pl.cutS]
    exact Dn.behind
  · rw [nF, nS, List.map_append, ← List.length_map (f := noDigest) (as := RF),
      ← List.drop_drop, List.drop_left]
    rfl
  · rw [oF, oS]
    rfl

/-! ## 4 The stages -/

/-- **The stages accept, at any rounds and columns of the declared form.** From a stage that is not
the last. Hypotheses: the plan from this stage on; the form's half of the invariant before the fold;
the view's form; the base case's test on values at whatever structure the earlier parts return. -/
theorem stages_returns (p : P12) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur next : Fmt.M1.Stage)
    (l : Laid) (t : T12) (col : ℕ → List UInt64) (row : GroupRow) (L : GroupLayout)
    (c : IoppStage) (nn : ℕ × ℕ) (id tN : ℕ) (tr : Tree) (R : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))),
    PlanFrom p (next :: rest) j cur l t.st.codes → FormInv p j cur l t col row L c nn id tN tr →
    ViewFrom (next :: rest) cur l R gs → ValsFrom p (next :: rest) j cur l t (R.map noDigest) gs →
    ∃ tE, (stagesFrom guardedProximityTestParts p j cur (next :: rest) l : Block T12 Unit).decide t
      (R.map noDigest) gs = .ok tE
  | [], j, cur, next, l, t, col, row, L, c, nn, id, tN, tr, R, gs, hP, I, hV, hv => by
    obtain ⟨⟨c0, n, dS, dC, Pl⟩, -, -, -, hPt⟩ := hP
    obtain rfl : c0 = c := Option.some.inj (Pl.stage.symm.trans I.front.stage)
    obtain rfl : nn = (n.code, n.maskCode) := Option.some.inj (I.front.next.symm.trans Pl.idx)
    obtain ⟨RF, rS, rC, R', gs', a, col', rfl, rfl, fitF, fitS, hans, hw, hV'⟩ := hV
    obtain ⟨D, x, row', t₂, Dn, I', k1, hsw, hbe, k4, k5⟩ :=
      stage_returns Pl I RF rS rC R' gs' a col' fitF fitS hans hw
    have hv' := hv _ _ _ k1 hsw hbe
    rw [k4, k5] at hv'
    obtain ⟨⟨c1, d₁, d₂, Lp⟩, -⟩ := hPt
    obtain rfl : c1 = n := Option.some.inj (Lp.stage.symm.trans Pl.stageN)
    have LF := lastForm_behind Pl I' Dn Lp
    obtain ⟨tE, hE⟩ := last_returns LF.front Lp.cut hV' hv'
    refine ⟨tE, (stagesFrom_ok guardedProximityTestParts p j cur next [] l t tE _ _).2
      ⟨_, _, _, k1, hsw, hbe, Dn.came, ?_⟩⟩
    rw [k4, k5]
    exact hE
  | nx :: rest', j, cur, next, l, t, col, row, L, c, nn, id, tN, tr, R, gs, hP, I, hV, hv => by
    obtain ⟨⟨c0, n, dS, dC, Pl⟩, -, -, hown, hPt⟩ := hP
    obtain rfl : c0 = c := Option.some.inj (Pl.stage.symm.trans I.front.stage)
    obtain rfl : nn = (n.code, n.maskCode) := Option.some.inj (I.front.next.symm.trans Pl.idx)
    obtain ⟨RF, rS, rC, R', gs', a, col', rfl, rfl, fitF, fitS, hans, hw, hV'⟩ := hV
    obtain ⟨D, x, row', t₂, Dn, I', k1, hsw, hbe, k4, k5⟩ :=
      stage_returns Pl I RF rS rC R' gs' a col' fitF fitS hans hw
    have hv' := hv _ _ _ k1 hsw hbe
    rw [k4, k5] at hv'
    have hPt' := hPt
    obtain ⟨⟨c1, n', dS', dC', Pl'⟩, hDl', hst', -, -⟩ := hPt'
    obtain rfl : c1 = n := Option.some.inj (Pl'.stage.symm.trans Pl.stageN)
    obtain ⟨tr', I2, -, -⟩ := formInv_next Pl I' Dn Pl' rest' hDl' hst' hown (fun _ => 0)
      (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
    have ecodes : _ = t.st.codes := Dn.did.codes
    rw [← ecodes] at hPt
    obtain ⟨tE, hE⟩ := stages_returns p rest' (j + 1) next nx (l.drop (cur.k + 3)) _ _ _ _ _ _ _ _
      _ R' gs' hPt I2 hV' hv'
    refine ⟨tE, (stagesFrom_ok guardedProximityTestParts p j cur next (nx :: rest') l t tE _ _).2
      ⟨_, _, _, k1, hsw, hbe, Dn.came, ?_⟩⟩
    rw [k4, k5]
    exact hE

/-! ## 5 The converse: an accept gives the hypothesis on values -/

/-- The base case's decision returns the claim that it was handed, or refuses. -/
theorem baseDecide_same (P : BasePar) (s x : BaseClaim) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (h : baseDecide P s rs gs = .ok x) : x = s := by
  unfold baseDecide at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; rfl)

/-- An accept of the last stage gives `ValsFrom` there. -/
theorem vals_of_last (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (t tE : T12)
    (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64)))
    (h : (stagesFrom guardedProximityTestParts p j cur [] l : Block T12 Unit).decide t rs gs = .ok tE) :
    ValsFrom p [] j cur l t rs gs := by
  rw [stagesFrom_last] at h
  have h' := (H2K.JointK.ranged_ok _ _ _ _ _ _ h).1
  intro row L c cl hp hs hc
  unfold baseJ5 at h'
  dsimp only at h'
  rw [hp, hs] at h'
  split at h'
  · rename_i row0 L0 c0 _ _ e1 e2 _
    obtain ⟨rfl, rfl⟩ := Passing.claim.inj e1
    obtain rfl := Option.some.inj e2
    obtain ⟨cl', hcl, h'⟩ := H2K.FoldLaw.bind_ok h'
    obtain ⟨_, _, h'⟩ := H2K.FoldLaw.bind_ok h'
    obtain ⟨x, hD, _⟩ := H2K.FoldLaw.bind_ok h'
    rw [hc] at hcl
    obtain rfl : cl = cl' := by
      simpa [named] using hcl
    rw [hD, baseDecide_same _ _ _ _ _ hD]
  · cases h'

/-- **An accept of the stages gives the hypothesis on values.** No other hypothesis. -/
theorem vals_of_accept (p : P12) : ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage)
    (l : Laid) (t tE : T12) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
    (stagesFrom guardedProximityTestParts p j cur rest l : Block T12 Unit).decide t rs gs = .ok tE →
    ValsFrom p rest j cur l t rs gs
  | [], j, cur, l, t, tE, rs, gs, h => vals_of_last p j cur l t tE rs gs h
  | next :: rest, j, cur, l, t, tE, rs, gs, h => by
    obtain ⟨s₁, s₂, s₃, a1, a2, a3, _, a5⟩ :=
      (stagesFrom_ok guardedProximityTestParts p j cur next rest l t tE rs gs).1 h
    intro t₁ t₂ t₃ b1 b2 b3
    obtain rfl : s₁ = t₁ := Except.ok.inj (a1.symm.trans b1)
    obtain rfl : s₂ = t₂ := Except.ok.inj (a2.symm.trans b2)
    obtain rfl : s₃ = t₃ := Except.ok.inj (a3.symm.trans b3)
    exact vals_of_accept p rest (j + 1) next _ _ tE _ _ a5

/-- **Under the plan, the form's half and the view's form, the stages accept if and only if the
hypothesis on values holds.** -/
theorem stages_accept_iff (p : P12) (rest : List Fmt.M1.Stage) (j : ℕ) (cur next : Fmt.M1.Stage)
    (l : Laid) (t : T12) (col : ℕ → List UInt64) (row : GroupRow) (L : GroupLayout)
    (c : IoppStage) (nn : ℕ × ℕ) (id tN : ℕ) (tr : Tree) (R : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (hP : PlanFrom p (next :: rest) j cur l t.st.codes)
    (I : FormInv p j cur l t col row L c nn id tN tr) (hV : ViewFrom (next :: rest) cur l R gs) :
    (∃ tE, (stagesFrom guardedProximityTestParts p j cur (next :: rest) l : Block T12 Unit).decide t
      (R.map noDigest) gs = .ok tE) ↔ ValsFrom p (next :: rest) j cur l t (R.map noDigest) gs :=
  ⟨fun ⟨tE, h⟩ => vals_of_accept p _ j cur l t tE _ _ h,
    stages_returns p rest j cur next l t col row L c nn id tN tr R gs hP I hV⟩

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.last_returns
#print axioms ProofFile.Honest.Sh.formInv_recol
#print axioms ProofFile.Honest.Sh.stage_returns
#print axioms ProofFile.Honest.Sh.stages_returns
#print axioms ProofFile.Honest.Sh.baseDecide_same
#print axioms ProofFile.Honest.Sh.vals_of_last
#print axioms ProofFile.Honest.Sh.vals_of_accept
#print axioms ProofFile.Honest.Sh.stages_accept_iff
#print axioms ProofFile.Honest.Sh.ViewFrom
#print axioms ProofFile.Honest.Sh.ValsFrom
