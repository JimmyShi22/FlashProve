-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyAll.lean: ALL THAT A PROVER SHOWS IN THE STAGES OF A PROXIMITY TEST, AT A
WHOLE FAMILY OF DRAWS: the rounds of the view and the groups of columns, by recursion after the
frame's own recursion on the list of stages (stagesFrom, Johnson/Desc/K12/Frame.lean). Definitions
alone; no theorem is stated.

It carries the prover's state by index (PS, BodyState.lean), the written column of the tree that
holds that state's rows, AND THE VERIFIER's RECORD: the fold's rounds read the coefficients of the
verifier's row, and the base case's first round those of its claim. The record is made by running
the description's own parts (guardedProximityTestParts) on the rounds and groups made so far; where a part refuses,
the record in hand is kept, IN SILENCE (sT1, sT3; so too lT, LinkAll.lean): a law that speaks of the
honest run needs "no part refused", as a premise or as a lemma.

  BCoins        the letters that this folder's laws leave free, stage by stage
  groupAt       one group as Block.step deals it: a tree's columns at the list of the drawn
                positions
  ansAt         the answer to the new message's sample: gAns where the two stages fit (decided by
                the library's decCsFit, Johnson/Top/H/StageJ.lean); else 0
  lastCol       the written column of the last stage's tree
  sRF ... sT3   one stage that is not the last, piece by piece: the fold's rounds · the drawn
                point · the state behind · the new tree's column · the record behind the fold · the
                answer · the switch's rounds and group · the record behind the batching
  lastOut       the last stage
  BOut, bodyAll the rounds · each round's tree, written · the groups

D: the draws as a function of the round's number; o: the number of the stage's first round. The
round at place i of the list drew D (o + i): the draws are counted by the library's s.h + s.g, which
is the stage's k where h ≤ k.
What is not here. No statement. No distribution on the free parameters. Nothing on how a value of
BCoins is chosen. Nothing on what any value that is sent discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BodyPack
import Johnson.Prover.Link.FoldSay
import Johnson.Prover.Link.BaseWhole
import Johnson.Desc.K12.Law.ChainOf
import Johnson.Top.H.StageJ

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)

/-- The letters that the laws leave free. The number: the stage's. W s j: the coefficients off which
the fold of stage j sends its rounds; the further table that goes out ahead of that fold is their
packing (packedN). new j: behind the switch out of stage j: the new rows' tails, the next further
table's tails and, at the last switch, the second message's rows and tails; its tables and, where a
fold follows, its further table are not read. fr j: the free room of that switch. -/
structure BCoins where
  W : ∀ s : Sg, ℕ → HIdx (sVars GE 2 (s.h + s.g)) → GE
  new : ℕ → PS
  fr : ℕ → ℕ → GE

/-- One group: a tree's columns at the list of the drawn positions, in the tree's own range. -/
def groupAt (a : ℕ) (poss : List ℕ) (col : ℕ → List UInt64) : List (ℕ × List UInt64) :=
  (Fmt.listOf (poss.map (· % 2 ^ a))).map fun x => (x, col x)

/-- The answer to the new message's sample. els: the elements that "SEND seed" drew; bits: the
coordinates of the seed's point. -/
def ansAt (s s' : Sg) (μ' : s.cMid.J → GE) (tl : s.cMid.Q → GE) (fr : ℕ → GE) (els : List E)
    (bits : ℕ) : GE :=
  if hf : CsFit s s' then
    gAns hf μ' tl fr (readP _ (els.take bits), unitOf (readE (els.getD bits zeroE)))
  else 0

/-- The written column of the last stage's tree. -/
def lastCol (s : Sg) (P : PS) (x : ℕ) : List UInt64 :=
  words12 (baseColW s.C s.Z (mainOf s (μOf s P)) (P.tM 0) (maskOf s (μOf s P)) (P.tZ 0) P.sM P.sT
    (P.fM 0) (P.fT 0) x)

/-! ## One stage that is not the last -/

section Stage
variable (p : P12) (K : BCoins) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ)
  (t : T12) (P : PS) (col : ℕ → List UInt64) (row : GroupRow) (D : ℕ → Fmt.Drawn)

/-- The fold's rounds. -/
def sRF : List Fmt.RoundView :=
  foldRV (sgOf cur) (vecG (sgOf cur) row) (μOf (sgOf cur) P) (K.W (sgOf cur) j) fun n => D (o + n)

/-- The drawn point. -/
def sGam : Fin ((sgOf cur).h + (sgOf cur).g) → GE :=
  readP ((sgOf cur).h + (sgOf cur).g) ((sRF K j cur o P row D).tail.map drawnOf)

/-- The prover's state behind the switch. -/
def sNext : PS :=
  nextPS (sgOf cur) (sGam K j cur o P row D) (K.fr j)
    (if last then K.new j else { K.new j with fM := packedN (sgOf next) (K.W (sgOf next) (j + 1)) })
    P

/-- The written column of the tree that the switch sends. -/
def sCol : ℕ → List UInt64 :=
  if last then lastCol (sgOf next) (sNext K last j cur next o P row D)
  else stageColW (sgOf next) (sNext K last j cur next o P row D).tabM
    (sNext K last j cur next o P row D).tabZ (sNext K last j cur next o P row D).tM
    (sNext K last j cur next o P row D).tZ (sNext K last j cur next o P row D).fM
    (sNext K last j cur next o P row D).fT

/-- The verifier's record behind the fold. -/
def sT1 : T12 :=
  ((guardedProximityTestParts.fold p j cur ((l.take (1 + cur.k)).map (·.1))).decide t
    ((sRF K j cur o P row D).map noDigest) []).toOption.getD t

/-- The answer that "CS" shows. -/
def sAns : GE :=
  ansAt (sgOf cur) (sgOf next)
    (foldMsg (sgOf cur) (μOf (sgOf cur) P) (φOf (sgOf cur) P) (sGam K j cur o P row D))
    (foldTl (sgOf cur) (ρOf (sgOf cur) P) (ψOf (sgOf cur) P) (sGam K j cur o P row D)) (K.fr j)
    ((D (o + 1 + ((sgOf cur).h + (sgOf cur).g))).elems.map E.ofTriple)
    (Send.cube (sT1 p K j cur l o t P row D).st.codes
      (switchTargetStage ((stageAt p (j + 1) next).getD default).code
        ((stageAt p (j + 1) next).getD default).maskCode ((sgOf next).h + (sgOf next).g)
        (sgOf next).h 1).shape).bits

/-- The switch's two rounds. -/
def sRS : List Fmt.RoundView :=
  [⟨[], D (o + 1 + ((sgOf cur).h + (sgOf cur).g))⟩,
    ⟨[.answer (ofE (sAns p K j cur next l o t P row D))],
      D (o + 2 + ((sgOf cur).h + (sgOf cur).g))⟩]

/-- The group that the switch's opening is dealt. -/
def sGS : List (List (ℕ × List UInt64)) :=
  [groupAt (sgOf cur).C.a (D (o + 2 + ((sgOf cur).h + (sgOf cur).g))).poss col]

/-- The verifier's record behind the switch and the batching behind it. -/
def sT3 : T12 :=
  let cutS := ((l.drop (1 + cur.k)).take 2).map (·.1)
  let t1 := sT1 p K j cur l o t P row D
  let t2 := ((guardedProximityTestParts.switch p j cur next last cutS).decide t1
    ((sRS p K j cur next l o t P row D).map noDigest) (sGS cur o col D)).toOption.getD t1
  ((guardedProximityTestParts.batBehind p (j + 1) next cutS).decide t2 [] []).toOption.getD t2

end Stage

/-- What is shown: the rounds · for each round the written column of the tree that it sends (no
word where it sends none) · the groups of columns that the rounds' openings are dealt. -/
structure BOut where
  rs : List Fmt.RoundView
  tr : List (ℕ → List UInt64)
  gs : List (List (ℕ × List UInt64))

/-- The last stage. The first round's challenge is read as (D o).elems.headD (0, 0, 0): AT AN EMPTY
LIST (0, 0, 0). shownAll (Johnson/Prover/Link/Base.lean) lays h + lam * m at each entry: lam
multiplies the row m, not the mask h. Where the stage or its claim is not found: the claim
⟨#[], #[], (0, 0, 0)⟩. Nothing here tests for either. -/
def lastOut (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (o : ℕ) (t : T12) (P : PS)
    (col : ℕ → List UInt64) (row : GroupRow) (D : ℕ → Fmt.Drawn) : BOut :=
  let s := sgOf cur
  let cl := ((stageAt p j cur).bind fun c => claimAt t.st.codes c row).getD ⟨#[], #[], (0, 0, 0)⟩
  ⟨[⟨[.e (tauSW s.C s.Z cl.c cl.d P.sM (P.fM 0))], D o⟩,
    ⟨(shownAll s.C s.Z ((D o).elems.headD (0, 0, 0)) (mainOf s (μOf s P)) (P.tM 0)
      (maskOf s (μOf s P)) (P.tZ 0) P.sM P.sT (P.fM 0) (P.fT 0)).map .e, D (o + 1)⟩],
    [fun _ => [], fun _ => []], [groupAt s.C.a (D (o + 1)).poss col]⟩

/-- The row of the claim that a record passes on; an empty one where it passes none. -/
def rowOf (t : T12) : GroupRow :=
  match t.pass with
  | .claim row _ => row
  | _ => {}

/-- **The rounds, the trees and the groups of the stages from a stage on.** col: the written column
of the tree that holds P's rows. -/
def bodyAll (p : P12) (K : BCoins) : List Fmt.M1.Stage → ℕ → Fmt.M1.Stage → Laid → ℕ → T12 → PS →
    (ℕ → List UInt64) → (ℕ → Fmt.Drawn) → BOut
  | [], j, cur, _, o, t, P, col, D => lastOut p j cur o t P col (rowOf t) D
  | next :: rest, j, cur, l, o, t, P, col, D =>
    let R := bodyAll p K rest (j + 1) next (l.drop (cur.k + 3))
      (o + ((sgOf cur).h + (sgOf cur).g) + 3)
      (sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D)
      (sNext K rest.isEmpty j cur next o P (rowOf t) D)
      (sCol K rest.isEmpty j cur next o P (rowOf t) D) D
    ⟨sRF K j cur o P (rowOf t) D ++ sRS p K j cur next l o t P (rowOf t) D ++ R.rs,
      (sRF K j cur o P (rowOf t) D).map (fun _ _ => []) ++
        [sCol K rest.isEmpty j cur next o P (rowOf t) D, fun _ => []] ++ R.tr,
      sGS cur o col D ++ R.gs⟩

end Johnson.Prover.Link
