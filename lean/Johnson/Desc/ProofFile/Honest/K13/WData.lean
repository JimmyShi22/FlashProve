-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/WData.lean: THE DATA OF W's MESSAGE, AS A FILLING OF `RowData`
(Johnson/Desc/ProofFile/Honest/RowData.lean): which elements the main rows of the oracle message W
hold, as a function of the index's weights, the public instance and the challenges heard.
Definitions with code, and statements with their proofs. The layout's laws: WDataLaid.lean of this
folder; tests at a toy: WDataToy.lean.

What W is. Behind the members' batching (kind K13) the prover commits to the vector W = g^T M: M is
the committed matrix; g are the row weights of the one claim that the batching leaves. The batching
samples x, then eps, then one element for each of the kCol column variables: the point pt. Row j of
the pile has the weights g_j and the column point psi_j. The claim's weights are the pile's, row j's
scaled by a_j := eps * x^j * eq(psi_j, pt) (`Batt.rowOf`, OnBytes/Iop/Batt.lean; the library's
`run_fields`, Johnson/Desc/K13/Law/FitC.lean). So W[c] = sum over the matrix's rows i of (sum over j
of a_j * g_j[i]) * M[i][c], for c below 2^kCol.
It reads: the index's `Weights.entry` · the last 2 + kCol challenges heard · of the pile's rows the
weights and the column points, through the filler `pile`, WHICH IS A PARAMETER HERE: the same filler
that the kind's half is handed (`proverSideOfClaimCombination`, Part.lean of this folder): it is handed the public
instance and the challenges through the batching's first.
Where it stands. At the address `wAddr`: the sending at the place "M:4", part 0, message 0. At main
row r and place j stands entry number `wNo` r j of W, just where that number is below 2^kCol.
Nothing is laid at any other place of that message, and nothing at the messages that are sent with
W.
How it is to be called. `heardAt` and `ready` do not look at the address: the filling is to be
joined with others BY THE ADDRESS (`RowData.join`). Where `lays` accepts and `ready` rejects,
`RowData.at_` still yields a value, which means nothing: read through `RowData.ask`, or name
`RowData.readyAt` at the list heard.
Main names:
  `k13Maps`, `claimG`: the batching's coefficients a_j; the claim's row weights. `claimG_eq`:
    **where the rows fit and the sumcheck's run returns, the row that the batching hands on has
    these weights, and the point as its column point.** `weights_claimG`: entry by entry they are
    the sum of a_j times row j's.
  `wVec`: W's entry, with code. `wVec_eq`: **it is `wEntry`**
    (Johnson/Desc/K13/Honest/MovesAtM4.lean) at the matrix of the kind's own job (`k13Wit`).
  `wAddr`, `wNo`, `wPublic`: the address; the entry's number at a row and place; the public tests:
    the shape is lawful at the codes (`Desc.Own.linFits`); the message length of W's code is a power
    of two; 2 + kCol challenges at least have been heard; the plan counts two rows at least on the
    pile.
  `wData codes Sh n u pile`: **the filling.** n: how many challenges have been heard when the
    sending begins. u: the plan's count of rows on the pile. `ready` REJECTS: where a public test
    fails; where not just n challenges are handed; where one of the last 2 + kCol has not just one
    element; WHERE THE FILLER YIELDS ANOTHER NUMBER OF ROWS THAN u, ROWS THAT THE BATCHING WOULD
    REJECT (`Batt.fits`), OR A WEIGHT THAT HAS NOT THE SHAPE's NUMBER OF ROW VARIABLES.
  `wDataAt pile Z G`: the filling at a proof file's public data: n := `wHeard Z`: the number of the
    batching's first round + 2 + kCol (`wDataAt_some`). WHERE THE PUBLIC DATA HAVE NO SUCH ROUND, n
    := 0: the public tests fail, nothing is laid and `ready` rejects (`wDataAt_none`).
  `wData_at`: what `RowData.at_` yields where data is laid. `wData_other`: nothing is laid at
    another address.

What is not claimed. That any part sends these values. That `pile` yields the verifier's pile's
weights and points: `pile` is a parameter here. WHAT HAS A TEXT ELSEWHERE (the list is not whole):
the library's `pileBySites` (Johnson/Desc/K13/Honest/PileDefs.lean) is a filler over a list of sites
and their claims. In two files of this folder that come into the library later than this one:
`fillerAt` (FillFitsAtHead.lean) is it at the thirteen sites of the first chain at the full size,
its claims still a parameter; `claimsText` (ClaimsText.lean) is a text for these claims up to lookOf
and headArm (and Q₀, which that file says no line reads); no definition joins the two. `ready` sees
a filler that fails, not one that yields fitting rows with other weights. That n is the number of
rounds in front of the place. That no data is laid at a pad's place (`RowData.clear`): it is
evaluated at the toy alone. WHERE THE PILE HAS ONE ROW there is no batching, W's place is another
and no such challenges are sampled: the public tests fail there. `entry` makes the pile and the
weights anew at every call. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.RowData
import Johnson.Desc.ProofFile.Honest.K13.Part
import Johnson.Desc.K13.Honest.MovesAtM4
import Johnson.Desc.K13.Law.FitC
import Johnson.Desc.K13.Law.StepBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Params
open OnBytes.Slice (GE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.K13.Law (weights weights_flatMap weights_scale run_fields ρg lowBits
  ofBits_low)
open VerifiableInference.Desc.K13.Honest (wEntry)
open VerifiableInference.Desc.K13 (fromOf? fromOf)

variable {Xi : Type}

/-! ## The claim's row weights -/

/-- The batching's coefficients: row j's is eps * x^j * eq(psi_j, pt). -/
def k13Maps (pile : List TensorRow) (x eps : E) (pt : List E) : List E :=
  ((Psc.powers oneE x pile.length).zip pile).map fun p => mulE eps (mulE p.1 (eqEval p.2.psi pt))

/-- The row weights of the one claim that the batching leaves. -/
def claimG (pile : List TensorRow) (x eps : E) (pt : List E) : List Tensor :=
  (zipT pile (k13Maps pile x eps pt)).flatMap fun p => p.1.g.map fun t => t.scale p.2

/-- **Where the rows fit and the sumcheck's run returns, the row that the batching hands on has
these weights, and the challenges of the run's rounds as its column point.** -/
theorem claimG_eq {k : ℕ} {pile : List TensorRow} {x : E} {fresh : List Slot} {h : Psc.Heard}
    {o : Psc.Out} (hf : Batt.fits k pile = true)
    (hr : Psc.run (Batt.claimOf pile x) (Batt.summandOf pile x) fresh h = some o) :
    (Batt.rowOf pile o).g = claimG pile x h.eps (h.rounds.map (·.2)) ∧
      (Batt.rowOf pile o).psi = h.rounds.map (·.2) := by
  obtain ⟨-, -, -, hpt, -, hmp, -⟩ := run_fields hf hr
  refine ⟨?_, hpt⟩
  show ((zipT pile o.rowMaps).flatMap fun p => p.1.g.map fun t => t.scale p.2) = _
  rw [hmp]
  rfl

/-- Entry by entry the claim's weights are the sum of a_j times row j's. -/
theorem weights_claimG (nR : ℕ) (pile : List TensorRow) (x eps : E) (pt : List E) (i : Fin nR) :
    weights ρg nR (claimG pile x eps pt) i =
      ((zipT pile (k13Maps pile x eps pt)).map fun p =>
        ρg.val p.2 * weights ρg nR p.1.g i).sum := by
  unfold claimG
  rw [weights_flatMap]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  exact weights_scale ρg nR p.1.g p.2 i

/-! ## The vector -/

/-- **W's entry number c**, with code: 0 from 2^kCol on. -/
def wVec (Sh : LinShape) (W : Weights) (g : List Tensor) (c : Nat) : GE :=
  if c < 2 ^ Sh.kCol then
    (List.ofFn fun i : Fin Sh.matrixRows =>
      weights ρg Sh.matrixRows g i * Reading.gl.val (eOfF (W.entry i.val c))).sum
  else 0

/-- **It is `wEntry` at the matrix of the kind's own job.** pl: the job's other field, which the
matrix does not read. -/
theorem wVec_eq (Sh : LinShape) (W : Weights) (pl : List Fmt.Drawn → List TensorRow)
    (g : List Tensor) (c : Nat) :
    wVec Sh W g c = wEntry (k13Wit Sh.matrixRows Sh.kCol
      ⟨fun i c => Reading.gl.val (eOfF (W.entry i c)), pl⟩).mat g c := by
  unfold wVec wEntry
  by_cases hc : c < 2 ^ Sh.kCol
  · rw [if_pos hc, if_pos hc, List.sum_ofFn]
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ = weights ρg Sh.matrixRows g i *
      Reading.gl.val (eOfF (W.entry i.val (Nat.ofBits (lowBits Sh.kCol c))))
    rw [ofBits_low hc]
  · rw [if_neg hc, if_neg hc]

/-! ## The address and the layout -/

/-- **W's address**: the sending at the place "M:4", part 0, message 0. -/
def wAddr : MsgAddr := ⟨⟨⟨1, none, 4, .K1⟩, 0⟩, 0⟩

/-- The number of the vector's entry at a main row and place. -/
def wNo (codes : Codes) (Sh : LinShape) (r j : Nat) : Nat :=
  (linLayW codes Sh).entryAt (r + j * 2 ^ (linLayW codes Sh).rowBits)

/-- The message length of W's code. -/
def wEll (codes : Codes) (Sh : LinShape) : Nat := (codes.base.getD Sh.w.code default).ell

/-- **The public tests.** -/
def wPublic (codes : Codes) (Sh : LinShape) (n u : Nat) : Bool :=
  VerifiableInference.Desc.Own.linFits codes Sh && powerOfTwo (wEll codes Sh) &&
    decide (2 + Sh.kCol ≤ n) && decide (2 ≤ u)

/-! ## The filling -/

/-- Of the n challenges heard: those that the pile's filler is handed: all through the batching's
first. -/
def wFront (Sh : LinShape) (n : Nat) (hd : List Fmt.Drawn) : List Fmt.Drawn :=
  hd.take (n - (1 + Sh.kCol))

/-- Of the n challenges heard: the batching's own: x, eps, then the point. -/
def wOwn (Sh : LinShape) (n : Nat) (hd : List Fmt.Drawn) : List E :=
  drawnE (hd.drop (n - (2 + Sh.kCol)))

/-- The claim's row weights, of the instance and the n challenges heard. -/
def wG (Sh : LinShape) (n : Nat) (pile : PileOf Xi) (x : Xi) (hd : List Fmt.Drawn) : List Tensor :=
  claimG (pile x (wFront Sh n hd)) ((wOwn Sh n hd).getD 0 zeroE) ((wOwn Sh n hd).getD 1 zeroE)
    ((wOwn Sh n hd).drop 2)

/-- **W's DATA.** codes, Sh: the sending's codes and the shape. n: how many challenges have been
heard when the sending begins. u: the plan's count of rows on the pile. pile: the filler that the
kind's half is handed. -/
def wData (codes : Codes) (Sh : LinShape) (n u : Nat) (pile : PileOf Xi) : RowDataOf Xi := fun x =>
  { heardAt := fun _ => n
    lays := fun a r j => a == wAddr && wPublic codes Sh n u && decide (r < Sh.w.mainRows) &&
      decide (j < wEll codes Sh) && decide (wNo codes Sh r j < 2 ^ Sh.kCol)
    entry := fun R hd _ r j => .inr (wVec Sh R.weights (wG Sh n pile x hd) (wNo codes Sh r j))
    ready := fun hd _ => wPublic codes Sh n u && hd.length == n &&
      ((hd.drop (n - (2 + Sh.kCol))).all fun d => d.elems.length == 1) &&
      (pile x (wFront Sh n hd)).length == u && Batt.fits Sh.kCol (pile x (wFront Sh n hd)) &&
      (pile x (wFront Sh n hd)).all fun r => r.g.all fun t => t.vars == Sh.kRow }

/-- How many challenges have been heard when W's sending begins, off the public data: the number of
the batching's first round + 2 + kCol; 0 WHERE THE PUBLIC DATA HAVE NO SUCH ROUND: the public tests
fail at 0. -/
def wHeard (Z : Pub) : Nat :=
  match fromOf? Z with
  | some f => f + 2 + Z.first.lin.kCol
  | none => 0

/-- **At a proof file's public data.** G: the segments' public data, for the filler alone. -/
def wDataAt (pile : Pub → Ground → PileOf Xi) (Z : Pub) (G : Ground) : RowDataOf Xi :=
  wData Z.first.codes Z.first.lin (wHeard Z) Z.first.pendingRows (pile Z G)

/-- Where the public data have the batching's first round: its number + 2 + kCol. -/
theorem wDataAt_some (pile : Pub → Ground → PileOf Xi) (Z : Pub) (G : Ground)
    (h : (fromOf? Z).isSome = true) :
    wDataAt pile Z G = wData Z.first.codes Z.first.lin (fromOf Z + 2 + Z.first.lin.kCol)
      Z.first.pendingRows (pile Z G) := by
  obtain ⟨f, hf⟩ := Option.isSome_iff_exists.1 h
  unfold wDataAt wHeard fromOf
  rw [hf]
  rfl

/-- Where they have none: nothing is laid, and `ready` rejects. -/
theorem wDataAt_none (pile : Pub → Ground → PileOf Xi) (Z : Pub) (G : Ground)
    (h : fromOf? Z = none) (x : Xi) (a : MsgAddr) :
    (∀ r j, (wDataAt pile Z G x).lays a r j = false) ∧
      ∀ hd, (wDataAt pile Z G x).ready hd a = false := by
  have e : wPublic Z.first.codes Z.first.lin (wHeard Z) Z.first.pendingRows = false := by
    unfold wPublic wHeard
    rw [h]
    have : decide (2 + Z.first.lin.kCol ≤ 0) = false := decide_eq_false (by omega)
    rw [this]
    simp
  constructor
  · intro r j
    show (a == wAddr && wPublic _ _ _ _ && _ && _ && _) = false
    rw [e]
    simp
  · intro hd
    show (wPublic _ _ _ _ && _ && _ && _ && _ && _) = false
    rw [e]
    simp

/-- What the one call yields where data is laid. -/
theorem wData_at (codes : Codes) (Sh : LinShape) (n u : Nat) (pile : PileOf Xi) (x : Xi)
    (R : Readers) (hd : List Fmt.Drawn) (a : MsgAddr) (r j : Nat)
    (h : (wData codes Sh n u pile x).lays a r j = true) :
    (wData codes Sh n u pile x).at_ R hd a r j =
      some (.inr (wVec Sh R.weights (wG Sh n pile x (hd.take n)) (wNo codes Sh r j))) := by
  unfold RowData.at_
  rw [if_pos h]
  rfl

/-- Nothing is laid at another address. -/
theorem wData_other (codes : Codes) (Sh : LinShape) (n u : Nat) (pile : PileOf Xi) (x : Xi)
    (a : MsgAddr) (r j : Nat) (h : a ≠ wAddr) : (wData codes Sh n u pile x).lays a r j = false := by
  have e : (a == wAddr) = false := beq_eq_false_iff_ne.2 h
  show (a == wAddr && _ && _ && _ && _) = false
  rw [e]
  rfl

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.claimG_eq
#print axioms ProofFile.Honest.K13.weights_claimG
#print axioms ProofFile.Honest.K13.wVec_eq
#print axioms ProofFile.Honest.K13.wDataAt_some
#print axioms ProofFile.Honest.K13.wDataAt_none
#print axioms ProofFile.Honest.K13.wData_at
#print axioms ProofFile.Honest.K13.wData_other
