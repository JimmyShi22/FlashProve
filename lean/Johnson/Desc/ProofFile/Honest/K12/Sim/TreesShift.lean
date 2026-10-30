-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/TreesShift.lean: a second text of four definitions of
Johnson/LinkSim/AtText/ShiftDefs.lean, and of the first step of a fifth, with the equations that tie
them to the firsts. Definitions and five equations.

Why a second text. The library's shift of a proximity test's random values (`shB`) is computed along
a run in which each round of positions opens one tree. Of the tree's written column `col` it reads
one term: the verifier's state behind the switch, `tNext ... col ...`. The four definitions at the
switch read that state's row of the claim alone (`rowOf (tNext ...)`, in `shWAt`; `dFresh`, `shNew`
and `dNext` hang on `shWAt`); `shB` also hands the state whole on, as the next stage's state. Where
the first round of positions opens several trees, that state is made of several groups of columns,
and no column gives it. Here the row is a variable ρ, and in the step along the stages the state is
a variable t₃. Nothing else turns. From the next stage on the library's `shB` is called as it
stands. Against the firsts the four are more general in ρ and narrower in the switch: they are the
case "not the last switch" alone, so `shNew` and `dNext` at the last switch are no instance of them.

  `shWT`, `dFreshT`, `shNewT`, `dNextT`   `shWAt`, `dFresh`, `shNew`, `dNext` at a switch that is
                 not the last, with ρ in the place of `rowOf (tNext ...)`
  `shT`          `shB`'s first step at t₃, then `shB`
  `shWAt_trees`, `dFresh_trees`, `shNew_trees`, `dNext_trees`, `shB_trees`   at the library's own
                 state behind the switch each is the first: by unfolding, no hypothesis

Limits. A switch that is not the last alone: the stage in hand is followed by two stages or more.
Definitions on variables: no finite type of random values, no law. Nothing on completeness,
soundness or hiding.

Sources. The four definitions and the proofs of the step follow, line by line,
Johnson/LinkSim/AtText/ShiftDefs.lean, Step.lean, Walk.lean, Induct.lean and PlacesProof.lean; the
note on sources in the head of ShiftDefs.lean holds here too.

Terms: RunBySpec.lean.
-/
import Johnson.LinkSim.AtText.Induct

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)
open Johnson.Prover.Link
open OnBytes.LinkSim.AtText

/-! ## 1 One switch that is not the last, at a letter for the row behind it -/

section Stage
variable (p : P12) (K : BCoins) (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12)
  (P : PS) (ρ : GroupRow) (D : ℕ → Fmt.Drawn) (d : PS)

open Classical in
/-- The shift of the next fold's coefficients: at the next stage's sizes; 0 at all other sizes. ρ:
the row of the claim in the verifier's state in front of the next stage. -/
def shWT (σ : Sg) : HIdx (sVars GE 2 (σ.h + σ.g)) → GE :=
  if σ = sgOf next then
    foldShift σ (vecG σ ρ) (μOf σ (dTab p K j cur next l o t P D d)) fun n => D (oNext cur o + n)
  else 0

/-- The next difference's further table: the negative of the packing of that shift. -/
def dFreshT (b i : ℕ) : GE :=
  -packedN (sgOf next) (shWT p K j cur next l o t P ρ D d (sgOf next)) b i

/-- The shift of the new random values that the switch is given: the tails of the new main rows, of
the carried mask rows and of the fresh mask rows. -/
def shNewT : PS :=
  { zPS with
    tM := fun b => if b < 2 ^ ((sgOf next).h + (sgOf next).g) then
        tailAt (sgOf next).C id (qNext false cur next o D) fun i =>
          (dTab p K j cur next l o t P D d).tabM (b + 2 ^ ((sgOf next).h + (sgOf next).g) * i)
      else 0
    tZ := fun b => if b < 2 ^ (sgOf next).h then
        tailAt (sgOf next).Z (· % 2 ^ (sgOf next).Z.a) (qNext false cur next o D) fun i =>
          (dTab p K j cur next l o t P D d).tabZ (b + 2 ^ (sgOf next).h * i)
      else 0
    fT := fun b => if b < 2 ^ (sgOf next).h then
        tailAt (sgOf next).Z (· % 2 ^ (sgOf next).Z.a) (qNext false cur next o D)
          (dFreshT p K j cur next l o t P ρ D d b)
      else 0 }

/-- The next difference: the two tables; minus the shift of the switch's new random values; the
further table as `dFreshT` gives it. -/
def dNextT : PS :=
  { negPS (shNewT p K j cur next l o t P ρ D d) with
    tabM := (dTab p K j cur next l o t P D d).tabM
    tabZ := (dTab p K j cur next l o t P D d).tabZ
    fM := dFreshT p K j cur next l o t P ρ D d }

end Stage

/-! ## 2 Along the stages: this step, then the library's own shift -/

/-- The shift of the stages' random values from a stage on that is followed by two stages or more.
t₃: the verifier's state in front of the next stage, a letter. From the next stage on: `shB`. -/
def shT (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) (nx : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (t₃ : T12) (d : PS) :
    BCoins :=
  let R := shB p K D (nx :: rest) (j + 1) next (l.drop (cur.k + 3)) (oNext cur o) t₃
    (sNext K false j cur next o P (rowOf t) D) (sCol K false j cur next o P (rowOf t) D)
    (dNextT p K j cur next l o t P (rowOf t₃) D d)
  { W := fun σ i => if i = j + 1 then shWT p K j cur next l o t P (rowOf t₃) D d σ else R.W σ i
    new := fun i => if i = j then shNewT p K j cur next l o t P (rowOf t₃) D d else R.new i
    fr := fun i => if i = j then shFr p K j cur next l o t P D d else R.fr i }

/-! ## 3 At the library's own state behind the switch they are the library's -/

section Same
variable (p : P12) (K : BCoins) (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12)
  (P : PS) (col : ℕ → List UInt64) (D : ℕ → Fmt.Drawn) (d : PS)

theorem shWAt_trees (σ : Sg) : shWAt p K false j cur next l o t P col D d σ =
    shWT p K j cur next l o t P (rowOf (tNext p K false j cur next l o t P col D)) D d σ := rfl

theorem dFresh_trees : dFresh p K false j cur next l o t P col D d =
    dFreshT p K j cur next l o t P (rowOf (tNext p K false j cur next l o t P col D)) D d := rfl

theorem shNew_trees : shNew p K false j cur next l o t P col D d =
    shNewT p K j cur next l o t P (rowOf (tNext p K false j cur next l o t P col D)) D d := rfl

theorem dNext_trees : dNext p K false j cur next l o t P col D d =
    dNextT p K j cur next l o t P (rowOf (tNext p K false j cur next l o t P col D)) D d := rfl

/-- **At the state that the library's text leaves behind the switch, the shift is `shB`.** -/
theorem shB_trees (nx : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) :
    shB p K D (next :: nx :: rest) j cur l o t P col d =
      shT p K D nx rest j cur next l o t P (tNext p K false j cur next l o t P col D) d := rfl

end Same

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.shWT
#print axioms ProofFile.Honest.K12.dFreshT
#print axioms ProofFile.Honest.K12.shNewT
#print axioms ProofFile.Honest.K12.dNextT
#print axioms ProofFile.Honest.K12.shT
#print axioms ProofFile.Honest.K12.shWAt_trees
#print axioms ProofFile.Honest.K12.dFresh_trees
#print axioms ProofFile.Honest.K12.shNew_trees
#print axioms ProofFile.Honest.K12.dNext_trees
#print axioms ProofFile.Honest.K12.shB_trees
