-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/ShiftDefs.lean: the shift of the coins under which the link prover's
algorithm and the simulator's algorithm are meant to disclose the same.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file defines. Two runs of the prover's algorithm stand side by side at the same verifier
challenges D. The honest run has the data X and the coins C. The other run has the data 0 and the
coins C plus the shift. The shift is what is added to the honest run's coins. At each stage, d
(a prover state, PS) is the difference "honest run's state minus the other run's state".
  shC            the shift of all the coins. It takes two data arguments: Xd, the data of which
                 the difference is made, and Xr with C, the data and coins of the run along which
                 it is computed.
  shB            the shift of the stages' coins, from a stage on. It is computed from the
                 difference d and along a run's coins, verifier state, prover state and columns
                 (K, t, P, col), of which it reads the verifier's state, the fold's point and sBits.

The order in which the shift is built. In front: the two pads; then the tails of the R rows in
which each of the two folded rows is laid out; beside them the first fold's coefficients, then the
tail of the row that holds their packing. At each switch: the pad among the free entries of the new
mask table; then the tails of the new main rows and of the carried mask rows; where a fold follows,
its coefficients and then the tails of the rows that hold their packing; at the last switch, the
masking word. Each piece is computed from the data, the challenges, the verifier's state and the
pieces built before it.
A piece may read challenges of rounds later than the round in which its coin is first used: all of
D is an argument.

How it fits. The statements about these definitions are in SpecStage.lean, SpecShiftIn.lean and
Places.lean, among others. LinkShift.lean proves that the shift does what it is meant to, under the
premises of Spec.linkShiftIn.

The other names.
  zPS, negPS, zB     a prover state of zeros; a state's negative; the stages' coins, all 0.
  tailAt C red Q dm  the compensating tail for the change dm of a row's message, at the points of
                     the positions red x for x in Q (tailShift, Johnson/LinkSim/Tail.lean; see
                     Defs.lean's terms).
  openAt a poss      the sampled positions taken into a tree's range (modulo 2^a), with repeats.
  sEls, sBits        the elements and the number that the prover's answer at a switch reads (sAns,
                     Johnson/Prover/Link/BodyAll.lean).
  dMu, dTl           the folded messages and tails of d.
  shFr               the shift of the free entries of the switch's new mask table: 0 except at
                     the pad's index.
  dTab               the two tables of the next difference; zeros elsewhere.
  shWAt              the shift of the next fold's coefficients, at the next stage's sizes; 0 at
                     all other sizes.
  shNew, dNext       the shift of the new coins that the switch is given; the next difference.
  oNext, tNext, qNext, lamNext   the next stage's first round number; the verifier's state in
                     front of it; the positions at which the switch's tree is opened; the element
                     that the base case's first round samples.
  fData, shPad, dMem, q0, shTN, dTab0, shW0, dPhi, shPsi, d0   the pieces of the front.

Limits.
  - Definitions alone: this file states no theorem.
  - Outside the sizes every piece of the shift is 0 by its definition, except what tailAt sets:
    that is 0 from the number of points on (tailFor_high, Johnson/LinkSim/Tail.lean).
Sources. It follows the recursion of bodyAll (Johnson/Prover/Link/BodyAll.lean) argument by
argument, as bodyEnd (Johnson/Prover/Link/BodyEnd.lean) does. The plan of the proof (a triangular
change of the prover's coins, in the order of sending) follows a write-up of ours that is not in
this repository, so it cannot be checked against that text from here (lean/CREDITS.md, "This
protocol's technical report", says what such a name means). SpecStage.lean, Step.lean and the files
on the shifts carry that plan out. That write-up is said to rest on files of this
repository that follow the paper that this protocol builds on (lean/CREDITS.md, under that heading).
That plan appears in small form in the head of Cb/Ld/LdSumZk.lean: a proof by a shift of the uniform
coefficients. The write-up does not count as made independently of the further work that this
protocol builds on (lean/CREDITS.md, under that heading).
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.Pad
import Johnson.LinkSim.AtText.Fold
import Johnson.LinkSim.AtText.Cols
import Johnson.LinkSim.AtText.PadPlace

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15 p12Of)
open H2K.Pub (sgOf)
open H2K.JointK (laidOf)
open Johnson.Prover.Link

/-! ## Zeros and negatives -/

/-- A state of zeros. -/
def zPS : PS :=
  ⟨fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => 0,
    fun _ => 0⟩

/-- A state's negative. -/
def negPS (P : PS) : PS :=
  ⟨fun i => -P.tabM i, fun i => -P.tabZ i, fun b q => -P.tM b q, fun b q => -P.tZ b q,
    fun b j => -P.fM b j, fun b q => -P.fT b q, fun j => -P.sM j, fun q => -P.sT q⟩

/-- The stages' coins, all 0. -/
def zB : BCoins := ⟨fun _ _ _ => 0, fun _ => zPS, fun _ _ => 0⟩

open Classical in
/-- The compensating tail for adding dm to a row's message, at the points of the positions red x
for x in Q. -/
def tailAt (C : Fmt.M1.Code) (red : ℕ → ℕ) (Q : List ℕ) (dm : ℕ → GE) : ℕ → GE :=
  tailShift C.r C.l (Q.map fun y => ptG C.a (red y)).toFinset dm

/-- The sampled positions taken into a tree's range, with repeats. -/
def openAt (a : ℕ) (poss : List ℕ) : List ℕ := poss.map (· % 2 ^ a)

/-! ## One switch -/

section Stage
variable (p : P12) (K : BCoins) (last : Bool) (j : ℕ) (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ)
  (t : T12) (P : PS) (col : ℕ → List UInt64) (D : ℕ → Fmt.Drawn) (d : PS)

/-- The elements sampled in the round in which the verifier sends the seed. -/
def sEls : List E := (D (o + 1 + ((sgOf cur).h + (sgOf cur).g))).elems.map E.ofTriple

/-- The number of coordinates of the seed's point, as the prover's answer reads it. -/
def sBits : ℕ :=
  (Send.cube (sT1 p K j cur l o t P (rowOf t) D).st.codes
    (switchTargetStage ((stageAt p (j + 1) next).getD default).code
      ((stageAt p (j + 1) next).getD default).maskCode ((sgOf next).h + (sgOf next).g)
      (sgOf next).h 1).shape).bits

/-- The difference's folded messages. -/
def dMu : (sgOf cur).cMid.J → GE :=
  foldMsg (sgOf cur) (μOf (sgOf cur) d) (φOf (sgOf cur) d) (sGam K j cur o P (rowOf t) D)

/-- The difference's folded tails. -/
def dTl : (sgOf cur).cMid.Q → GE :=
  foldTl (sgOf cur) (ρOf (sgOf cur) d) (ψOf (sgOf cur) d) (sGam K j cur o P (rowOf t) D)

/-- The shift of the free entries of the switch's new mask table: 0 except at the pad's index. -/
def shFr : ℕ → GE :=
  Pi.single (padIx (sgOf next))
    (ansShift (sgOf cur) (sgOf next) (dMu K j cur o t P D d) (dTl K j cur o t P D d)
      (sEls cur o D) (sBits p K j cur next l o t P D))

/-- The next difference's two tables; zeros elsewhere. -/
def dTab : PS :=
  nextPS (sgOf cur) (sGam K j cur o P (rowOf t) D) (-shFr p K j cur next l o t P D d) zPS d

/-- The number of the next stage's first round. -/
def oNext : ℕ := o + ((sgOf cur).h + (sgOf cur).g) + 3

/-- The verifier's state in front of the next stage. -/
def tNext : T12 := sT3 p K last j cur next l o t P col (rowOf t) D

open Classical in
/-- The shift of the next fold's coefficients: at the next stage's sizes; 0 at all other sizes. -/
def shWAt (σ : Sg) : HIdx (sVars GE 2 (σ.h + σ.g)) → GE :=
  if σ = sgOf next then
    foldShift σ (vecG σ (rowOf (tNext p K last j cur next l o t P col D)))
      (μOf σ (dTab p K j cur next l o t P D d)) fun n => D (oNext cur o + n)
  else 0

/-- The positions at which the tree that the switch sends is opened, with repeats. -/
def qNext : List ℕ :=
  openAt (sgOf next).C.a
    (if last then (D (oNext cur o + 1)).poss
      else (D (oNext cur o + 2 + ((sgOf next).h + (sgOf next).g))).poss)

/-- The element that the base case's first round samples. -/
def lamNext : GE := toE ((D (oNext cur o)).elems.headD (0, 0, 0))

/-- Where a fold follows: the next difference's further table, the negative of the packing of the
shift of the coefficients. -/
def dFresh (b i : ℕ) : GE :=
  -packedN (sgOf next) (shWAt p K last j cur next l o t P col D d (sgOf next)) b i

/-- The shift of the new coins that the switch is given: the tails of the new main rows and of
the carried mask rows; where a fold follows, the fresh mask rows' tails; at the last switch, the
masking word. -/
def shNew : PS :=
  if last then
    { zPS with
      tM := fun b => if b = 0 then
          tailAt (sgOf next).C id (qNext last cur next o D)
            (mainOf (sgOf next) (μOf (sgOf next) (dTab p K j cur next l o t P D d)))
        else 0
      tZ := fun b => if b = 0 then
          tailAt (sgOf next).Z (· % 2 ^ (sgOf next).Z.a) (qNext last cur next o D)
            (maskOf (sgOf next) (μOf (sgOf next) (dTab p K j cur next l o t P D d)))
        else 0
      sM := fun i => lamNext cur o D *
        mainOf (sgOf next) (μOf (sgOf next) (dTab p K j cur next l o t P D d)) i
      sT := fun q => lamNext cur o D *
        -tailAt (sgOf next).C id (qNext last cur next o D)
          (mainOf (sgOf next) (μOf (sgOf next) (dTab p K j cur next l o t P D d))) q
      fM := fun b i => if b = 0 then lamNext cur o D *
          maskOf (sgOf next) (μOf (sgOf next) (dTab p K j cur next l o t P D d)) i
        else 0
      fT := fun b q => if b = 0 then lamNext cur o D *
          -tailAt (sgOf next).Z (· % 2 ^ (sgOf next).Z.a) (qNext last cur next o D)
            (maskOf (sgOf next) (μOf (sgOf next) (dTab p K j cur next l o t P D d))) q
        else 0 }
  else
    { zPS with
      tM := fun b => if b < 2 ^ ((sgOf next).h + (sgOf next).g) then
          tailAt (sgOf next).C id (qNext last cur next o D) fun i =>
            (dTab p K j cur next l o t P D d).tabM (b + 2 ^ ((sgOf next).h + (sgOf next).g) * i)
        else 0
      tZ := fun b => if b < 2 ^ (sgOf next).h then
          tailAt (sgOf next).Z (· % 2 ^ (sgOf next).Z.a) (qNext last cur next o D) fun i =>
            (dTab p K j cur next l o t P D d).tabZ (b + 2 ^ (sgOf next).h * i)
        else 0
      fT := fun b => if b < 2 ^ (sgOf next).h then
          tailAt (sgOf next).Z (· % 2 ^ (sgOf next).Z.a) (qNext last cur next o D)
            (dFresh p K last j cur next l o t P col D d b)
        else 0 }

/-- The next difference: the two tables; minus the shift of the switch's new coins; where a fold
follows, the further table as dFresh gives it. -/
def dNext : PS :=
  { negPS (shNew p K last j cur next l o t P col D d) with
    tabM := (dTab p K j cur next l o t P D d).tabM
    tabZ := (dTab p K j cur next l o t P D d).tabZ
    fM := if last then (negPS (shNew p K last j cur next l o t P col D d)).fM
      else dFresh p K last j cur next l o t P col D d }

end Stage

/-! ## Along the stages -/

/-- The shift of the stages' coins, from a stage on. -/
def shB (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) : List Fmt.M1.Stage → ℕ → Fmt.M1.Stage → Laid →
    ℕ → T12 → PS → (ℕ → List UInt64) → PS → BCoins
  | [], _, _, _, _, _, _, _, _ => zB
  | next :: rest, j, cur, l, o, t, P, col, d =>
    let R := shB p K D rest (j + 1) next (l.drop (cur.k + 3)) (oNext cur o)
      (tNext p K rest.isEmpty j cur next l o t P col D)
      (sNext K rest.isEmpty j cur next o P (rowOf t) D)
      (sCol K rest.isEmpty j cur next o P (rowOf t) D)
      (dNext p K rest.isEmpty j cur next l o t P col D d)
    { W := fun σ i =>
        if i = j + 1 then
          (if rest.isEmpty then 0 else shWAt p K rest.isEmpty j cur next l o t P col D d σ)
        else R.W σ i
      new := fun i => if i = j then shNew p K rest.isEmpty j cur next l o t P col D d else R.new i
      fr := fun i => if i = j then shFr p K j cur next l o t P D d else R.fr i }

/-! ## The front -/

section Front
variable (P : P15) (S : Sz) (t : ℕ) (Xd Xr : LIn S) (C : LCoins) (D : ℕ → Fmt.Drawn)

/-- The messages of the front's two folded rows, made from the data, with 0 at the pads' entries. -/
def fData : Bool → S.MJ → GE := frontMem S (lGam S D) Xd.M₀ Xd.M₁ 0

/-- The shift of the two pads. -/
def shPad (a : Bool) : GE := padShift S t (lSeed S D) (fData S Xd D) a

/-- The difference of the two folded rows' messages. -/
def dMem : Bool → S.MJ → GE := fData S Xd D - fun a => Pi.single S.padJ (shPad S t Xd D a)

/-- The positions at which the first tree is opened, with repeats. -/
def q0 : List ℕ := openAt (sg0 P).C.a (D (6 + 2 + ((sg0 P).h + (sg0 P).g))).poss

/-- The shift of the tails of the R rows in which each of the two folded rows is laid out. -/
def shTN (a : Bool) (i : ℕ) : ℕ → GE :=
  if i < S.P.R then tailAt S.P.C id (q0 P D) (membN S (dMem S t Xd D) a i) else 0

/-- The first difference's tables; zeros elsewhere. -/
def dTab0 : PS := firstPS S (dMem S t Xd D) 0 0 0

open Classical in
/-- The shift of the first fold's coefficients: at the first stage's sizes; 0 at all others. -/
def shW0 (σ : Sg) : HIdx (sVars GE 2 (σ.h + σ.g)) → GE :=
  if σ = sg0 P then
    foldShift σ (vecG σ (rowOf (lT P S t Xr C D))) (μOf σ (dTab0 S t Xd D)) fun n => D (6 + n)
  else 0

/-- The difference of the row sent beside the two folded rows: the negative of the packing of the
first fold's shift. -/
def dPhi (i : ℕ) : GE := -packedN (sg0 P) (shW0 P S t Xd Xr C D (sg0 P)) 0 i

/-- The shift of that row's tail. -/
def shPsi : ℕ → GE := tailAt S.P.Z (· % 2 ^ S.P.Z.a) (q0 P D) (dPhi P S t Xd Xr C D)

/-- The first difference. -/
def d0 : PS :=
  firstPS S (dMem S t Xd D) (-shTN P S t Xd D) (dPhi P S t Xd Xr C D) (-shPsi P S t Xd Xr C D)

/-- The shift of all the coins. Xd: the data of which the difference is made. Xr and C: the data
and coins of the run along which it is computed. -/
def shC : LCoins :=
  match (p12Of P).nums.stages with
  | first :: rest =>
    let R := shB (p12Of P) C.body D rest 0 first ((laidOf (p12Of P)).drop 1) 6 (lT P S t Xr C D)
      (lPS P S Xr C D) (lCol P S Xr C D) (d0 P S t Xd Xr C D)
    { pad := shPad S t Xd D
      tN := shTN P S t Xd D
      ψN := shPsi P S t Xd Xr C D
      body :=
        { W := fun σ i => if i = 0 then shW0 P S t Xd Xr C D σ else R.W σ i
          new := R.new
          fr := R.fr } }
  | [] => ⟨fun _ => 0, fun _ _ _ => 0, fun _ => 0, zB⟩

end Front

end OnBytes.LinkSim.AtText
