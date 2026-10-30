-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/Part.lean: the honest side of the kind "the members' batching"
(K13), at its place behind the segments of a proof file's first chain, in the form of
Honest/Frame.lean and Honest/Side.lean. The kind's own text does not hold what the prover sends
(Johnson/Desc/K13/Kind.lean): this file holds it, up to one parameter (the pile's filler).
DEFINITIONS ALONE, with code: this file defines part of the honest prover. No theorem.

The rounds (`K13.battRounds`): "BAT-sigma", in which nothing is sent and x is sampled; "PSC
epsilon"; kCol times "PSC round". The row has two parts, as the book cuts it: the first round by
itself, then one masked sumcheck (`sumPart`, Honest/Sum.lean) of kCol variables, each summed
plainly, with round polynomials of three coefficients, without a lead and without end values.

The summand. For each row j of the pile: x^j, times the equality vector of the row's column point,
times the row's weights applied to the committed matrix. Its round polynomial is computed over the
library's field by `quadAll` (Johnson/Desc/K13/Honest/Moves.lean) and `foldsAll` (Code.lean there)
on the tables of Johnson/Desc/K13/Honest/MovesAtM3.lean (`tabsOf`) and laid into the program's type.

What the parts read. Of the index: the committed matrix's entries, through the reader
`Weights.entry` (Honest/ForKinds.lean) alone. Of the witness: nothing. Of the challenges in front:
x, the last of them; and those of which the pile's rows are made. THE PILE stands in the verifier's
state; a part is handed no state: so the small input has a field that makes the pile's rows of the
challenges in front. Of a row the parts read the weights and the column point alone: not its mask
entries, not its target, which in the verifier's state is a value that the prover has sent: no
function of the instance and the challenges gives it, and none is asked to. NO FILLER FOR THAT FIELD
IS WRITTEN HERE: the half takes it as a parameter.

The coins. None of its own. The sumcheck's part spends one stretch of 1 + 2 kCol entries of the
index-mask message. Nothing is carried. No stop.
Main names:
  `K13Ask`: the small input. `k13Ask`: it, of the prover's input: the matrix by the index's reader.
  `k13Wit`: the matrix in the form of the kind's laws.
  `k13E`: an element of the library's field as the program's. `PileOf`: the type of the pile's
    filler.
  `k13Shape`, `k13Job`: the call's shape; the job.
  `k13Sum`: the sumcheck's part; the part of "BAT-sigma" is `quietPart` (Honest/ForKinds.lean).
  `k13Place`, `k13Row`, `proverSideOfClaimCombination`: the row at its place.
  `k13Lot`: the half under the name of the lot that lays the kind's sub-protocol at its place.
  `k13Sims`, `k13Pairs`, `k13Side`: a simulator beside each part (`quietSim`, `sumSim`); the side.

Limits. Who fills the small input's field for the pile is not said here (`openHonest`,
Honest/OpenHonest.lean, lays `K13.pileAnyK3`). `k13Job`'s `round` makes the
tables and sets the earlier variables anew in every round. The number of the matrix's rows is the
shape's `matrixRows`. The two simulators are data: nothing is said here of what they are good for.
Nothing is said of `Good` at this side. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Sum
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.Desc.ProofFile.Lot.K13
import Johnson.Desc.K13.Honest.Code
import Johnson.Desc.K13.Honest.MovesAtM3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes (E TensorRow zeroE)
open OnBytes.Slice (GE toE ofE)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Part.MaskedSum (Var Call)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (Wit)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.K13.Honest (tabsOf quadAll foldsAll)

/-- **The small input**: what the kind's parts need of the prover's input. -/
structure K13Ask where
  /-- the committed matrix's entry, by row and by the column's number -/
  mat : Nat → Nat → GE
  /-- the rows on the pile, of the challenges in front of the sumcheck's part. OF A ROW THE WEIGHTS
  AND THE COLUMN POINT ALONE ARE READ; its mask form and its target are placeholders here: they
  need not be those of the verifier's state. There a row's target is a value that the prover has
  sent: no function of the instance and the challenges gives it -/
  pile : List Fmt.Drawn → List TensorRow

/-- The matrix in the form of the kind's laws: bit t of a column's number is coordinate t. THE MASK
ENTRIES OF THIS VALUE ARE A PLACEHOLDER, 0: the tables that are made of it read the matrix alone
(`tabsOf_mat`, Tie.lean of this folder); it is no witness of which a row with mask entries is true.
-/
def k13Wit (nR k : Nat) (w : K13Ask) : Wit GE nR k :=
  ⟨fun i c => w.mat i.val (Nat.ofBits c), fun _ => 0⟩

/-- An element of the library's field as the program's. -/
def k13E (a : GE) : E := E.ofTriple (ofE a)

/-- The call's shape: no lead; kCol variables, summed plainly, three coefficients each; no ends. -/
def k13Shape (k : Nat) : Call := ⟨0, List.replicate k (.plain 3), none⟩

/-- **The job.** x is the last challenge in front of the part. -/
def k13Job (nR k : Nat) : SumJob K13Ask Unit :=
  { shape := k13Shape k
    points := fun _ _ => []
    lead := fun _ _ => []
    round := fun w fr rs =>
      let x := (drawnE (fr.heard.drop (fr.heard.length - 1))).headD zeroE
      let c := quadAll (foldsAll (rs.map Reading.gl.val)
        (tabsOf Reading.gl (k13Wit nR k w) (w.pile fr.heard) (Reading.gl.val x)))
      [k13E c.1, k13E c.2.1, k13E c.2.2]
    inY := fun _ _ _ _ => []
    ends := fun _ _ _ => [] }

/-- The place: behind the segments of the first chain. -/
def k13Place (p : Where) : Place := ⟨p.chain, none, p.piece, .K13⟩

/-- The sumcheck's part: number 1 of the row. It spends a stretch of the mask entries of the oracle
message that the book calls `indexMaskRun` (Honest/ForKinds.lean). -/
def k13Sum (p : Where) : Part Unit K13Ask Unit :=
  sumPart (runName indexMaskRun ⟨k13Place p, 1⟩ "sum") "no ends"
    (k13Job p.lin.matrixRows p.lin.kCol)

variable {W₀ Rc Xi Tr X : Type}

/-- How the pile's rows are made: of the public instance and the challenges in front, and of nothing
else: a parameter of the half. What a filler has to yield: as many rows as the verifier's pile has,
each with that row's weights and column point. The rows' mask entries and targets are idle. -/
abbrev PileOf (Xi : Type) : Type := Xi → List Fmt.Drawn → List TensorRow

/-- **The small input, of the prover's input.** weights: the index's reader; of the index
`Weights.entry` alone is read; of the rest of the input the public instance alone, by the pile's
filler. -/
def k13Ask (weights : W₀ → Weights) (pile : PileOf Xi) (t : Local W₀ Rc Xi Tr) : K13Ask :=
  ⟨fun i c => Reading.gl.val (eOfF ((weights t.w₀).entry i c)), pile t.x⟩

/-- **The row**, at the first chain's input. -/
def k13Row (weights : W₀ → Weights) (pile : PileOf Xi) (p : Where) :
    List (Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X) :=
  [quietPart,
   (k13Sum p).lift (fun _ => ()) (k13Ask weights pile) (fun _ => ()) fun x _ => x]

/-- **The kind's half.** -/
def proverSideOfClaimCombination (weights : W₀ → Weights) (pile : PileOf Xi) :
    KindHalf Where (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  fun p => ⟨k13Place p, k13Row weights pile p⟩

/-- **The lot's honest side**, under the lot's own name, at a proof file: the pile's filler is
handed the public part and the segments' public data too. -/
def k13Lot (weights : W₀ → Weights) (pile : Pub → Ground → PileOf Xi) :
    HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  { name := "K13: the members' batching"
    halves := fun Z G =>
      [proverSideOfClaimCombination weights (pile Z G) (VerifiableInference.Desc.K13.whereOf Z)] }

/-- The two simulators. -/
def k13Sims {Pb : Type} : KindSim Where Pb :=
  fun p => [quietSim ⟨k13Place p, 0⟩, sumSim ⟨k13Place p, 1⟩ (k13Shape p.lin.kCol)]

/-- The row, each part with its simulator. -/
def k13Pairs {Pb : Type} (weights : W₀ → Weights) (pile : PileOf Xi)
    (p : Where) : List (Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X × Sim Pb) :=
  (k13Row weights pile p).zip (k13Sims p)

/-- **The side**: the row beside the member of the first chain of an IOP as written in Lean that
stands at the place; `none` if none does. -/
def k13Side {S Cl Pb : Type} (bs : List (VerifiableInference.Desc.Block S Cl))
    (weights : W₀ → Weights) (pile : PileOf Xi) (p : Where) :
    Option (Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) :=
  Side.seated bs (k13Place p) (k13Pairs weights pile p)

end ProofFile.Honest.K13
