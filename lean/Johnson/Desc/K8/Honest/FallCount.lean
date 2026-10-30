-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/FallCount.lean: THE SMALLNESS TEST: AT HOW MANY VALUES OF THE BATCHING ELEMENT
CAN AN ENTRY OF THE VECTOR OF READS HAVE THE WEIGHT 0. THE STATEMENT, as a closed proposition, with
the definitions that it needs. DEFINITIONS, some with code. NO THEOREM. No prover stands in it.
NOTHING IS CLAIMED ON COMPLETENESS, SOUNDNESS OR HIDING.

The setting. A segment's batching block draws one element chi, calls the segment's runs of claims,
and adds each claim to one equation: a plain claim under chi^(its number), a tie or a read of the
smallness test under chi^(n + first), n the plan's number of claims
(Johnson/Desc/First/Batch/Kind.lean: K9.batch; Add.lean: addOne). Behind the adding the verifier
asks, among other things, that every entry of the vector of reads has a weight other than 0
(`selfUnits`, Johnson/Desc/First/TailClaims/SelfTests.lean). The statement is on that one test's
"no" (`zeroUnitAt`, Johnson/Desc/K8/Honest/Fall.lean), asked behind the block's own decision
(`askBehind`, Johnson/Desc/K8/Honest/Behind.lean), and on no other test.

Why the weight is seldom 0. The weight of an entry is a sum over the claims that name it. Just one
read names it, with the coefficient -(sum over u of chi^u C[u]), C a column of the matrix that the
smallness test has drawn, its entries -1, 0, 1; that read stands under a power of chi from n on.
Every other claim that names the entry is plain: it stands under a power below n. So, IF NO PLAIN
CLAIM's COEFFICIENT HANGS ON chi, the weight is a polynomial in chi whose coefficients from n on are
the column's entries: not the zero polynomial unless the column is all 0, whatever the plain claims
lay, scalars that the prover has sent among it. And where a column that a read uses is all 0 the
read's own text refuses at every chi, so the block says yes at none: nothing is counted there.

Main names:
  `oneAt t r i`, `allZero`   two worlds: one entry is 1 and all else 0; all is 0
  `coefOn cl t r i`   the coefficient of a claim on an entry, read in the field
  `unitsLaid nU tl tU`   WITH CODE: the public conditions on the smallness test's data in front of
      the block
  `columnLive tl mu c`   WITH CODE: a column of the drawn matrix has an entry other than 0 (it
      stands in no premise of `FallFew`: a yes of the block gives it of every column that a read uses)
  `drawnAt p s d`   the state behind the draw, at which the block calls the runs
  `Gathers p g s tl funs nf nb a`   WHAT IS ASKED OF THE RUNS: see there
  `chiAt x`   a field element as the round's challenge
  **`FallFew`**   the statement: at most nU[2] * d values of chi. Its proof:
      Johnson/Desc/K8/Honest/FallFew.lean (`fall_few`)

THE CLAIMS ARE MADE BEHIND THE DRAW: the block calls the runs at a state that already holds chi. So
"no plain claim's coefficient hangs on chi" is no property of the state in front of the block: it
is a law on the runs' texts, and stands here as a premise (`Gathers`: the letter a is fixed outside
chi). This file shows it of no run.

Limits. (1) An implication: `Gathers` is shown of no function of claims here. (2) From a yes of the
block alone: a chi at which the block itself refuses is not counted: among these are the values at
which a read's column's sum is 0, and, where a column is all 0, every value: such challenges are
another count's matter. (3) The count is of field elements, each as the reduced words `chiAt` gives;
nothing on how chi is drawn. (4) U1 and U2 are asked to be absent. (5) The verifier's other tests
behind the adding are not counted here.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.Fall
import Johnson.Desc.K8.Honest.Behind
import Johnson.Desc.First.Batch.AtS
import Johnson.Desc.First.Batch.Law.Count
import Johnson.Desc.First.Batch.Law.Stages
import Johnson.Desc.First.TailClaims.EquationsForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open OnBytes.Tie.Pv.Tail.Port (topOf)

/-! ## A claim's coefficient on an entry -/

/-- The world in which entry i of virtual row r of array t is 1 and every other unknown is 0. -/
def oneAt (t r i : Nat) : World Cb.Gl.E :=
  ⟨fun _ => 0, fun t' r' i' => if t' = t ∧ r' = r ∧ i' = i then 1 else 0⟩

/-- The world in which every unknown is 0. -/
def allZero : World Cb.Gl.E := ⟨fun _ => 0, fun _ _ _ => 0⟩

/-- The coefficient of a claim on entry i of virtual row r of array t, read in the field: the
claim's value where that entry is 1 and all else 0, less its value where all is 0. -/
def coefOn (cl : Claim) (t r i : Nat) : Cb.Gl.E :=
  K9L.claimValue Reading.gl (oneAt t r i) cl - K9L.claimValue Reading.gl allZero cl

/-! ## The public conditions, with code -/

/-- On the smallness test's data tl in front of the batching block. nU: the plan's lengths of the
vectors of reads. tU: the number of U3's array. There is no U1 and no U2; U3 is array tU; all of U3
holds tables, from its first entry on, and has the plan's length; tU is neither the digits' array
nor a matrix's array of symbols. -/
def unitsLaid (nU : Array Nat) (tl : HTailF2) (tU : Nat) : Bool :=
  (tl.ix.U.getD 0 none).isNone && (tl.ix.U.getD 1 none).isNone &&
  tl.ix.U.getD 2 none == some tU &&
  tl.tabFirst.getD 1 0 == 0 && tl.tabLen.getD 1 0 == nU.getD 2 0 &&
  tl.nUF.getD 2 0 == nU.getD 2 0 &&
  tl.ix.ZZ != tU && ((List.range tl.NM).all fun mu => tl.gtTree.getD mu 0 != tU)

/-- Column c of matrix mu's part of the drawn matrix has an entry other than 0. -/
def columnLive (tl : HTailF2) (mu c : Nat) : Bool :=
  (List.range tl.tau).any fun u => tl.cfF.getD ((tl.cfFirst.getD mu 0 + c) * tl.tau + u) 0 != 0

/-! ## What is asked of the runs -/

/-- The state behind the draw of the batching element, at the challenge d: the draw's own decision.
The batching block calls the segment's runs at this state. -/
def drawnAt (p : K9.Where) (s : S) (d : Fmt.Drawn) : Except String S :=
  (K9.drawAlone (Cl := Claim) K9.atS p).decide s [⟨[], d⟩] []

/-- **What a count of this sort asks of a segment's function of claims g**, at the state s in front
of the batching block. tl, funs: the smallness test's data and the list of tables in s. nf, nb: how
many claims stand in front of the smallness test's list and behind it. a c t r i: the coefficient
of plain claim number c on entry i of virtual row r of array t. nf, nb AND a STAND OUTSIDE THE
CHALLENGE. At every challenge d at which the draw says yes and g returns:
  the runs have left the ledger's sums, the batching element, the count of claims, the plan's number
  and the arrays' frame;
  the list is nf claims, the list "K8.equations" made at tl and funs and at a ledger with the drawn
  element, the plan's number and the arrays' frame, and nb claims; the smallness test's data behind
  the runs are those that "K8.equations" has returned;
  each claim in front, each of the first four of "K8.equations" and each claim behind is plain and
  has on every entry of every array the coefficient that a gives at its number. -/
structure Gathers (p : K9.Where) (g : S → Except String (List Claim × S)) (s : S) (tl : HTailF2)
    (funs : Array HFun) (nf nb : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E) : Prop where
  each : ∀ (d : Fmt.Drawn) (t e : S) (cls : List Claim),
    drawnAt p s d = .ok t → g t = .ok (cls, e) →
    ∃ (x y : K9.Part) (tl' : HTailF2) (fr k8 bk : List Claim) (n₀ : Nat) (F₁ F₂ : Fork),
      K9.atS.get? t = some x ∧ K9.atS.get? e = some y ∧
      K9L.core y.F = K9L.core x.F ∧ treesFrame y.F.trees = treesFrame x.F.trees ∧
      e.tl? = some tl' ∧
      cls = fr ++ k8 ++ bk ∧ fr.length = nf ∧ bk.length = nb ∧
      equations n₀ tl funs F₁ = .ok (tl', F₂, k8) ∧
      F₁.theta = x.F.theta ∧ F₁.planClaimsF = x.F.planClaimsF ∧
      treesFrame F₁.trees = treesFrame x.F.trees ∧
      (∀ c cl, (fr ++ k8.take 4)[c]? = some cl →
        cl.eqFirst = none ∧ ∀ t r i, coefOn cl t r i = a c t r i) ∧
      (∀ c cl, bk[c]? = some cl →
        cl.eqFirst = none ∧ ∀ t r i, coefOn cl t r i = a (nf + k8.length + c) t r i)

/-! ## The statement -/

/-- A field element as the challenge of the batching's round: one element, in reduced words. -/
def chiAt (x : Cb.Gl.E) : Fmt.Drawn := ⟨[Slice.ofE x], [], [], none⟩

/-- **The count.** IF batch is a decision each of whose yeses at s is a yes of the batching block
K9.batch K9.atS p g with the same return (the block itself; the block under a seat's guards); s
holds the smallness test's data tl and the ledger F; tl passes the public test `unitsLaid`; g
meets `Gathers` at s; and d bounds the exponents (the plan's number of claims and the indices that
the smallness test's equations take, less 1): THEN at most nU[2] * d field elements are challenges
at which batch says yes and, behind it, `selfUnits` says no. -/
def FallFew : Prop :=
  ∀ (p : K9.Where) (g : S → Except String (List Claim × S))
    (batch : S → List Fmt.RoundView → Except String S) (nU : Array Nat) (s : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun) (tU nf nb d : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E),
    (∀ rs t, batch s rs = .ok t → (K9.batch K9.atS p g).decide s rs [] = .ok t) →
    tlForkP.get? s = some (tl, F) →
    unitsLaid nU tl tU = true →
    Gathers p g s tl funs nf nb a →
    F.planClaimsF + topOf tl funs ≤ d + 1 →
    Prob.cnt (fun x : Cb.Gl.E => askBehind batch (zeroUnitAt nU) s [chiAt x] = true) ≤
      nU.getD 2 0 * d

end VerifiableInference.Desc.First.K8.Honest
