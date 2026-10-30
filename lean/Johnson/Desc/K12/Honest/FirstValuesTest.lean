-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/FirstValuesTest.lean: one test, `valuesB`, whose "true" gives all the
hypotheses of `first_V` (Johnson/Desc/K12/Honest/FirstValues.lean) but one, so that they can be
checked together at a value by an evaluation. The one: that the state's fresh table is the packing
of the hiding polynomial, an equation of two functions. "The hiding polynomial" is only a name, for
`K.W (sgOf a) 0`: nothing here says that it hides anything. In Lean that one is hpk:
`P.fM = packedN (sgOf a) (K.W (sgOf a) 0)`. `first_V` is on the first stage of a proximity test: if
the claim before the first fold is true at the prover's state then, under further hypotheses, the
claim after the first switch is true at the prover's state after that switch. A test is here a
definition with values in `Bool` that has code. `first_V_test` holds at every value of its
parameters. Definitions with code, theorems and proofs. It depends on no frame for an honest side:
the frame (Johnson/Desc/ProofFile/Honest/Frame.lean) is not among the imports, direct or indirect.

In the list: s and s' are stages in the library's form (`Sg`, OnBytes/Slice/Stage.lean). a and next
are the proximity test's first and second stage in the format's form (`Fmt.M1.Stage`), rest the
stages after them; `sgOf` (Johnson/Desc/K12/Law/ChainOf.lean) turns the format's form into the
library's, with `g := k - h`. p holds the numbers of the place of the proximity test (`P12`,
Johnson/Desc/K12/Frame.lean; `Place`, Johnson/Desc/Block.lean: where a sub-protocol is in the
description). t is the verifier's state before the first fold (`T12`, Johnson/Desc/K12/Join.lean),
and `t.pass` (`Passing`) is what one part of the proximity test hands on to the next. P is the
prover's state at the first stage (`PS`, Johnson/Prover/Link/BodyState.lean), and `μOf s P` is its
message. K is a `BCoins` (Johnson/Prover/Link/BodyAll.lean). D gives the sampled challenges by a
round's number; the first stage's rounds begin at the number o. c gives a tree's written column at a
position, R the prover's rows as functions of numbers (`PlainRows`,
Johnson/Desc/K12/Honest/FirstRows.lean). `t1At` is the verifier's state after the first fold, `t3At`
its state after the first switch and the batching after it, `qAt` the prover's state after the
switch (all three: Johnson/Desc/K12/Honest/FirstYes.lean). A claim is a target with a vector of
coefficients. It is true at a message if the products of the coefficients and the message's entries
add up to the target (`Slf.Holds` at `Slf.idf`, Cb/Ld/LdRel.lean). `stmGk s k h row`
(OnBytes/Slice/BlkRead.lean) is the claim of a row on a group (`GroupRow`), read with the numbers k
and h of a layout (`GroupLayout`; both: OnBytes/Iop/Ground.lean).

  `first_V_test`: `valuesB ... = true` · the fresh table is the packing ⟹ the end of `first_V`, at
    the claim that the state passes and at the plain data that `gpOf` makes of it. In Lean: under hB
    and hpk there are row, L, Dp, row' and lay' such that `t.pass` is the claim row with the layout
    L; `gpOf p t a L` (Johnson/Desc/K12/Law/FirstOk.lean) returns Dp; `t3At`, at the trees
    `groupTrees Dp.ts (logAt Dp.book) c`, passes the claim row' with the layout lay'; and
    `stmGk (sgOf next) lay'.k lay'.h row'` is true at the message of `qAt`
  `valuesB`: a definition: the test. It is `firstB` (Johnson/Desc/K12/Honest/FirstTest.lean) and the
    clauses that follow. It is false unless `t.pass` is a claim row with a layout L, `stageAt`
    (Join.lean) returns the two stages in the program's form, cu and nx, and `t1At` passes single
    rows. The clauses: `gpOf p t a L` returns some Dp, and `stateB a Dp P R`
    (Johnson/Desc/K12/Honest/FirstStateTest.lean) is true; h ≤ k at next; `csFitB` at the two
    stages; `L.k` is h + g and `L.h` is h of the first stage; `holdsB`: the claim
    `stmGk (sgOf a) L.k L.h row` is true at `μOf (sgOf a) P`; h + 2 g + 1 ≤ `Z.l` at the first
    stage; in the codes of `t1At`, the code number `cu.maskCode` of the list `mask` has `ell` =
    `a.Z.l`; `oldOkB` at the single rows and the two code numbers of nx; the seed's factor passes
    `okE` (OnBytes/Field/Ext.lean: its three words are below the prime). The seed's factor is
    element number `bitsAt` (FirstValues.lean) of those that D has at round o + 1 + h + g
  `endB`: a definition: the conclusion of `first_V` as a test, at a list of trees that is a
    parameter: `t3At` passes a claim, and by `holdsB` that claim, read with its own layout's
    numbers, is true at the message of `qAt`
  `holdsB`, `holds_of`: the test for "a claim is true at a message": the sum of the products and the
    target are written alike (`sameE`, FirstTest.lean); its "true" gives `Slf.Holds`
  `csFitB`, `csFit_of`: `CsFit` (OnBytes/Slice/CsData.lean: what a switch asks of the sizes of the
    stage before it and the stage after it) as a test; its "true" gives `CsFit`
  `oldOkB`, `oldOk_of`: `OldOk` (FirstValues.lean: `CsProg`, OnBytes/Slice/BlkCsJoint.lean, and four
    clauses on the single rows) as a test; its "true" gives `OldOk`

By what. `first_V_test` unfolds `valuesB` and `firstB`, splits on the values that they match on, and
calls `first_V` at l := `laidS p` (Johnson/Desc/K12/Law/ReadsK.lean). The tests' clauses become its
hypotheses by `sized_of`, `colsAt_of` and `firstYes_of` (FirstTest.lean), `stateAt_of`
(FirstStateTest.lean), and `csFit_of`, `holds_of` and `oldOk_of`. `holds_of` is `same_of`
(FirstTest.lean); the two others unfold their tests.

Hypotheses of `first_V_test`. hB: `valuesB` is true at the parameters. hpk: the equation above;
`packedN` is in Johnson/Prover/Link/BodyPack.lean.

Limits.
- A "true" at a value is an evaluation by Lean's evaluator, outside the kernel: it gives no theorem.
  Nothing is evaluated in this file. Johnson/Desc/ProofFile/Honest/K12/ToyGroup.lean evaluates
  `valuesB` and `endB` by `#guard`, at two small made-up places.
- For small sizes: `firstB` runs over every position of every tree of the group, `stateB` over every
  row of the state's tables.
- hpk is not tested: it is a hypothesis of `first_V_test`.
- Only the direction from the tests to the hypotheses is proved. `valuesB` asks more than `first_V`:
  `firstB` has a clause on the first stage's main code, which `first_V` does not ask.
- No theorem is on `endB`: that its "true" gives the conclusion of `first_V` is not stated.
- What `first_V` takes as hypotheses is here a clause of the test or hpk; none of it is shown. The
  limits in the head of FirstValues.lean hold here as well.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.FirstValues
import Johnson.Desc.K12.Honest.FirstStateTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw H2K.JointK H2K.First
open Johnson.Prover.Link
open H2K.Pub (sgOf)

/-- The test for "the claim q is true at the message μ": the sum of the products `q.2 j * μ j` and
the target `q.1` are written alike (`sameE`, Johnson/Desc/K12/Honest/FirstTest.lean). -/
def holdsB (s : Sg) (q : GE × (s.cIn.J → GE)) (μ : s.cIn.J → GE) : Bool :=
  sameE (∑ j, q.2 j * μ j) q.1

theorem holds_of {s : Sg} {q : GE × (s.cIn.J → GE)} {μ : s.cIn.J → GE}
    (h : holdsB s q μ = true) : (Slf.idf (E := GE) (J := s.cIn.J)).Holds q μ := same_of h

/-- `CsFit` (OnBytes/Slice/CsData.lean) as a test: its five clauses on the sizes of a stage s and
the next stage s', in its order. -/
def csFitB (s s' : Sg) : Bool :=
  decide (2 ^ (s'.h + s'.g) * s'.C.l = s.C.l) &&
  decide (2 * s.Z.l + s.C.r + 2 * s.Z.r + 1 ≤ 2 ^ s'.h * s'.Z.l) &&
  decide (s'.C.l = 2 ^ Fmt.M1.lg s'.C.l) && decide (s'.Z.l = 2 ^ Fmt.M1.lg s'.Z.l) &&
  decide (s.Z.a ≤ s.C.a)

theorem csFit_of {s s' : Sg} (h : csFitB s s' = true) : CsFit s s' := by
  simp only [csFitB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- `OldOk` (Johnson/Desc/K12/Honest/FirstValues.lean) as a test: the eight clauses of `CsProg`
(OnBytes/Slice/BlkCsJoint.lean), then the four further clauses of `OldOk` on the single rows `old`,
in their order. -/
def oldOkB (s s' : Sg) (codes : Codes) (old : SingleRows) (nc nz : ℕ) : Bool :=
  decide ((codes.base[old.code]?).map codeOf = some s.C) &&
  decide ((codes.mask[old.maskCode]?).map codeOf = some s.Z) &&
  decide ((codes.base[nc]?).map codeOf = some s'.C) &&
  decide ((codes.mask[nz]?).map codeOf = some s'.Z) &&
  decide (switchKept old = #[]) && decide (old.masks = 2) && decide (old.keptRows = 0) &&
  decide (s.C.a ≤ 32) && old.kept.isEmpty && decide ((old.d.getD 0 #[]).size = s.Z.l) &&
  decide ((old.d.getD 1 #[]).size = s.Z.l) &&
  old.c.tensors.all fun v => decide (v.vars = ceilLog2 s.C.l)

theorem oldOk_of {s s' : Sg} {codes : Codes} {old : SingleRows} {nc nz : ℕ}
    (h : oldOkB s s' codes old nc nz = true) : OldOk s s' codes old nc nz := by
  simp only [oldOkB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩ := h
  refine ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, Array.isEmpty_iff.1 a9, a10, a11, fun v hv => ?_⟩
  exact of_decide_eq_true (List.all_eq_true.1 a12 v hv)

/-- The test: `firstB`, and what `first_V` asks besides, all but its hypothesis hpk. It is false
where `t.pass` is no claim, where `stageAt` returns no first or no second stage, or where the
verifier's state after the fold passes no single rows. -/
def valuesB (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (a next : Fmt.M1.Stage) (o : ℕ)
    (t : T12) (P : PS) (D : ℕ → Fmt.Drawn) (c : ℕ → ℕ → List UInt64) (R : PlainRows) : Bool :=
  firstB p K rest a next o t P D c R &&
  match t.pass, stageAt p 0 a, stageAt p 1 next, (t1At p K 0 a (laidS p) o t P D).pass with
  | .claim row L, some cu, some nx, .single rows _ =>
    (match gpOf p t a L with
      | some Dp => stateB a Dp P R
      | none => false) &&
    decide (next.h ≤ next.k) && csFitB (sgOf a) (sgOf next) &&
    decide (L.k = (sgOf a).h + (sgOf a).g) && decide (L.h = (sgOf a).h) &&
    holdsB (sgOf a) (stmGk (sgOf a) L.k L.h row) (μOf (sgOf a) P) &&
    decide ((sgOf a).h + 2 * (sgOf a).g + 1 ≤ (sgOf a).Z.l) &&
    decide (((t1At p K 0 a (laidS p) o t P D).st.codes.mask.getD cu.maskCode default).ell =
      a.Z.l) &&
    oldOkB (sgOf a) (sgOf next) (t1At p K 0 a (laidS p) o t P D).st.codes rows nx.code
      nx.maskCode &&
    okE (((D (o + 1 + ((sgOf a).h + (sgOf a).g))).elems.map E.ofTriple).getD
      (bitsAt p 0 next (t1At p K 0 a (laidS p) o t P D)) zeroE)
  | _, _, _, _ => false

/-- The conclusion of `first_V` as a test. trees: a free parameter; `first_V` has the group's trees
`groupTrees Dp.ts (logAt Dp.book) c` there. It is false where `t3At` passes no claim. No theorem is
on this test. -/
def endB (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (a next : Fmt.M1.Stage) (o : ℕ)
    (t : T12) (P : PS) (D : ℕ → Fmt.Drawn) (trees : List Tree) : Bool :=
  match (t3At p K rest 0 a next (laidS p) o t P trees D).pass with
  | .claim row' lay' =>
    holdsB (sgOf next) (stmGk (sgOf next) lay'.k lay'.h row')
      (μOf (sgOf next) (qAt K rest 0 a next o P D))
  | _ => false

/-- **Where `valuesB` is true and hpk holds, the conclusion of `first_V` holds.** hpk is the one
hypothesis of `first_V` that the test does not give. -/
theorem first_V_test (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (a next : Fmt.M1.Stage)
    (o : ℕ) (t : T12) (P : PS) (D : ℕ → Fmt.Drawn) (c : ℕ → ℕ → List UInt64) (R : PlainRows)
    (hB : valuesB p K rest a next o t P D c R = true)
    (hpk : P.fM = packedN (sgOf a) (K.W (sgOf a) 0)) :
    ∃ (row : GroupRow) (L : GroupLayout) (Dp : Plain) (row' : GroupRow) (lay' : GroupLayout),
      t.pass = .claim row L ∧ gpOf p t a L = some Dp ∧
      (t3At p K rest 0 a next (laidS p) o t P (groupTrees Dp.ts (logAt Dp.book) c) D).pass =
        .claim row' lay' ∧
      (Slf.idf (E := GE) (J := (sgOf next).cIn.J)).Holds (stmGk (sgOf next) lay'.k lay'.h row')
        (μOf (sgOf next) (qAt K rest 0 a next o P D)) := by
  unfold valuesB at hB
  rw [Bool.and_eq_true] at hB
  obtain ⟨hF, hB⟩ := hB
  unfold firstB at hF
  cases hp : t.pass with
  | claim row L =>
    cases hD : gpOf p t a L with
    | none => simp [hp, hD] at hF
    | some Dp =>
      cases hcu : stageAt p 0 a with
      | none => simp [hp, hcu] at hB
      | some cu =>
        cases hnx : stageAt p 1 next with
        | none => simp [hp, hcu, hnx] at hB
        | some nx =>
          cases h1p : (t1At p K 0 a (laidS p) o t P D).pass with
          | single rows gp =>
            simp only [hp, hD, hcu, hnx, Bool.and_eq_true, decide_eq_true_eq,
              List.all_eq_true] at hF
            simp only [hp, hD, hcu, hnx, h1p, Bool.and_eq_true, decide_eq_true_eq] at hB
            obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨he, h1⟩, hok⟩, hhk⟩, hs⟩, -⟩, -⟩, hC⟩, hY⟩, hr⟩, ht⟩ := hF
            obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hS, hhk'⟩, hf⟩, hLk⟩, hLh⟩, hin⟩, hroom⟩, hZl⟩, hO⟩, hnz⟩ := hB
            obtain ⟨row', lay', e⟩ := first_V p K rest a next (laidS p) o t P D he h1 rfl row L hp
              Dp hD hok hhk hhk' (sized_of hs) cu nx hcu hnx c R (colsAt_of hC) (stateAt_of hS)
              (firstYes_of _ _ _ _ _ _ _ _ _ _ _ _ hY) hr ht (csFit_of hf) hLk hLh (holds_of hin)
              hroom hpk hZl
              (fun rows' gp' h' => by
                rw [h1p] at h'
                injection h' with e1 _
                rw [← e1]
                exact oldOk_of hO) hnz
            exact ⟨row, L, Dp, row', lay', rfl, hD, e⟩
          | _ => simp [hp, hcu, hnx, h1p] at hB
  | _ => simp [hp] at hF

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.first_V_test
#print axioms ProofFile.Honest.K12.holds_of
#print axioms ProofFile.Honest.K12.csFit_of
#print axioms ProofFile.Honest.K12.oldOk_of
#print axioms ProofFile.Honest.K12.holdsB
#print axioms ProofFile.Honest.K12.csFitB
#print axioms ProofFile.Honest.K12.oldOkB
#print axioms ProofFile.Honest.K12.valuesB
#print axioms ProofFile.Honest.K12.endB
