-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyInv.lean: THE ONE INVARIANT OF THE INDUCTION OVER THE STAGES OF THE
PROXIMITY TEST (body_yes_of, Johnson/Prover/Link/BodyYes.lean). Definitions alone: records of
premises; no theorem is stated. It stands IN FRONT OF A STAGE's FOLD, where the verifier's record
passes a claim on (pass = .claim row L), and, at the last stage, in front of the base case.

  (FormInv, LastForm   the form's half: Johnson/Prover/Link/FormInv.lean)
  ValInv      the values' half: the claim is true at the prover's state · the further table is the
              packing of the stage's W · the tree's written column is the state's
  ColIs       which writer wrote the tree that holds the state's rows: the link's first tree
              (firstColW) or a switch's (stageColW), with that tree's seat and the layout's form
  LastInv     at the last stage: LastForm, the claim, the column
  BodyInv     the invariant in body_yes_of's eight letters, over a letter Plan for the public facts
              on the rounds still to be dealt

Limits. BodyInv CAN BE MET ONLY WHERE THE TEST's FIRST FOLD SENDS NO FIRST MASK OF ITS OWN: at Plan
:= PlanAll (Johnson/Prover/Link/BodyCloseB.lean), whose PlanFrom
(Johnson/Prover/Link/FormStepPlan.lean) asks p.nums.ownMask = false at every stage; and FormInv
counts the roots as p.nums.free + j. AND, IN FRONT OF A STAGE THAT IS NOT THE LAST, ONLY WHERE THE
CLAIM's FORM IS DENSE (FormInv's field dense: DenseForm, OnBytes/Slice/BlkProxDense.lean): a form
without a written-out factor is dense; the key file's and the proof file's tests have rows with such
factors: these are served where they are dense (Johnson/Prover/Link/FormRow.lean, Limits).
What is not here. No statement; nothing here says that a record meets any of these (BodyInv in front
of the first stage, at the full size, under its premises: bodyInv0_full, BodyInv0Full.lean; again
behind a stage: hstep_at, BodyCloseS.lean). Nothing on soundness; nothing on what any entry
discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BodyYes
import Johnson.Prover.Link.BodyBase
import Johnson.Prover.Link.FormInv
import Johnson.Prover.Link.BodyFit
import Johnson.Prover.Link.BodyStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.Prox VerifiableInference.Desc.K12
open H2K.Pub (sgOf)
open OnBytes.Slice.ProxRun H2K.Sw H2K.JointK

/-- Which writer wrote the tree that holds the state's rows, and how that tree's parts sit in the
statement, the book and the layout: what the laws that read the tree's words back ask
(hy_first, FrontHy.lean; hy_stage, HyStage.lean). -/
inductive ColIs (cur : Fmt.M1.Stage) (t : T12) (L : GroupLayout) (c : IoppStage) (id : ℕ) (P : PS)
    (col : ℕ → List UInt64) : Prop
  /-- the link's first tree: two members' rows and the row beside them -/
  | first (S : Sz) (t₀ : ℕ) (m : Bool → S.MJ → GE) (tN : Bool → ℕ → ℕ → GE) (φN ψN : ℕ → GE)
      (hs : sgOf cur = S.sg t₀) (hP : P = firstPS S m tN φN ψN)
      (hc : col = firstColW S (membN S m) tN φN ψN)
      (o0 o1 k : ℕ) (sh frS : OracleShape)
      (hst : (Fmt.M2.starts [S.P.mem, S.P.mem]).1 = [some 0, some (2 ^ S.P.aR)])
      (hk1 : 2 ^ S.P.aR + S.P.R ≤ 2 ^ Fmt.M2.kOf [S.P.mem, S.P.mem])
      (hRw : sh.mainRows = S.P.R) (h3 : sh.mainDeg = 3) (hz : sh.maskRows = 0)
      (hfm : frS.mainRows = 0) (hfz : 0 < frS.maskRows)
      (hwid : 3 * (S.P.R + S.P.R) + frS.maskRows * 3 = Fmt.M2.widthOf S.P.mems 1)
      (hL : LayAt [o0, o1] #[some 0, some (2 ^ S.P.aR)] #[none, none] L)
      (seat : SeatP t.st t.book [o0, o1, id] k (S.sg t₀).C.a [sh, sh, frS]) :
      ColIs cur t L c id P col
  /-- a tree that a switch sent: one member and the message that rode with it -/
  | later (hc : col = stageColW (sgOf cur) P.tabM P.tabZ P.tM P.tZ P.fM P.fT) (o k : ℕ)
      (hL : LayAt [o] #[some 0] #[some 0] L)
      (seat : SeatP t.st t.book [o, id] k (sgOf cur).C.a (stageShapes (sgOf cur) c)) :
      ColIs cur t L c id P col

/-- **The values' half, in front of a fold.** packs: the further table is packedN of the stage's W,
which is 0 wherever h + 2 g + 1 ≤ Z.l fails, and at every j from Z.l on (BodyPack.lean); where there
is room, every place but the packing's is 0 (packed, FoldHolds.lean). That there is room is no
clause here: it is StepPlan.room (FormStepPlan.lean), inside PlanAll. That ValInv holds again behind
a stage: next_at, next_packs, col_later (BodyStepAt.lean). -/
structure ValInv (K : BCoins) (j : ℕ) (cur : Fmt.M1.Stage) (t : T12) (P : PS)
    (col : ℕ → List UInt64) (row : GroupRow) (L : GroupLayout) (c : IoppStage) (id : ℕ) :
    Prop where
  holds : (Slf.idf (E := GE) (J := (sgOf cur).cIn.J)).Holds (stmGk (sgOf cur) L.k L.h row)
    (μOf (sgOf cur) P)
  packs : P.fM = packedN (sgOf cur) (K.W (sgOf cur) j)
  colIs : ColIs cur t L c id P col

/-- **At the last stage**: the form's half (LastForm, FormInv.lean), the claim, the column. -/
structure LastInv (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (t : T12) (P : PS)
    (col : ℕ → List UInt64) (row : GroupRow) (L : GroupLayout) (c : IoppStage) (cl : BaseClaim)
    (m star a : ℕ) : Prop where
  form : LastForm p j cur t row L c cl m star a
  holds : (Slf.idf (E := GE) (J := (sgOf cur).cIn.J)).Holds (stmGk (sgOf cur) 1 0 row)
    (μOf (sgOf cur) P)
  colIs : col = lastCol (sgOf cur) P

/-- **The invariant, in body_yes_of's letters.** Plan: A LETTER (a predicate of rest, j, cur, l and
the statement's codes): nothing here says what it holds; BodyCloseB.lean, BodyCloseS.lean,
BodyInv0Full.lean, BodyInv0Meant.lean and LinkJoinE.lean use it at PlanAll (BodyCloseB.lean): facts
on the plan at the rounds still to be dealt. FitFrom D l o (BodyFit.lean): at which round the stage
stands: the draws from o on fit these rounds. -/
def BodyInv (p : P12) (K : BCoins)
    (Plan : List Fmt.M1.Stage → ℕ → Fmt.M1.Stage → Laid → Codes → Prop) (D : ℕ → Fmt.Drawn) :
    List Fmt.M1.Stage → ℕ → Fmt.M1.Stage → Laid → ℕ → T12 → PS → (ℕ → List UInt64) → Prop
  | [], j, cur, l, o, t, P, col =>
    Plan [] j cur l t.st.codes ∧ FitFrom D l o ∧
      ∃ row L c cl m star a, LastInv p j cur t P col row L c cl m star a
  | next :: rest, j, cur, l, o, t, P, col =>
    Plan (next :: rest) j cur l t.st.codes ∧ FitFrom D l o ∧ ∃ row L c n id tN tr,
      FormInv p j cur l t col row L c n id tN tr ∧ ValInv K j cur t P col row L c id

end Johnson.Prover.Link
