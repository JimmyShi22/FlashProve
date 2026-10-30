-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/EqReturns.lean: THE SMALLNESS TEST: FIVE ROUTINES OF THE VERIFIER THAT HAVE
NO LOOP THAT LAYS CLAIMS AND READ NO OTHER KIND's DATA RETURN, UNDER PREMISES ON NUMBERS, FLAGS,
MARKS AND LENGTHS; one of them under one test on values beside. STATEMENTS, each as a definition of
a proposition, with a few definitions; no proof stands here. Lemmas; none of the library's goals.

The routines: `eqWeights`, `eqTie`, `eqRead` (Johnson/Desc/First/TailClaims/Equations.lean) and
`close`, `front` (Johnson/Desc/First/K8/Order.lean). The library's laws on them speak from a yes;
these go the other way. Each says: under the premises the routine returns; the ledger and the claims
in front stay; and what of the data's numbers and lengths, and of the claim that is laid, stands
behind.
  `oneRow tl`        the test of `powersF` on the shapes (OnBytes/Model/Tail.lean), by name
  `firstsOf tl`      the first exponents that `powersF` lays
  `takenOf tl`       the marks "this matrix's sums are laid", as `foldSums` reads them
  `Laid tl tl'`      behind `eqWeights`: the lengths of the weights and of the sums; the first
                      exponents; where there is a matrix, the library's test "every matrix has had
                      its sums" says yes; every other number, flag and mark is as it was
  `TieReady tl mu`   in front of a tie: three lengths against the matrix's shape; the matrix is in
                      the list and has a row of cells
  `TieClaim tl mu c` the tie's claim by its numbers: the exponent; a form without entry or slot;
                      three runs
  `ReadReady tl F Fn sg tU`   in front of a read: the vector's array; its columns; the table's
                      matrix is in the list; the segment is one of the table's
  `ReadClaim tl F Fn sg laid tU c`   the read's claim by its numbers
  `Spec.eqWeights_returns`, `Spec.eqTie_returns`, `Spec.eqRead_returns`, `Spec.close_returns`,
  `Spec.front_returns`
THE ONE TEST ON VALUES: `LiveAt tl (Fn, sg)` (Johnson/Desc/K8/Honest/FallLive.lean): no sum of a
column of the read's matrix is the element 0, as the verifier asks it: all three words 0. It does
not read sg. This file imports that one for this definition alone.
BESIDE THIS FILE: Johnson/Desc/K8/Honest/EqSim.lean and EqOwn.lean say of three of these routines
that they return wherever they return at data of the same shape: a tool for loops. The laws here
are the ones to call.
Limits. Nothing says that the premises hold at any state of a run. The weights, the sums and the
claims' coefficients are not said: the library's laws from a yes say them. `orderOk` stays a premise
as it stands: a test with code on the link's book and the statement's marks.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.FallLive
import Johnson.Desc.First.K8.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First.TailClaims

/-- The test of `powersF` on the shapes: each matrix's symbols lie in one row each. -/
def oneRow (tl : HTailF2) : Bool :=
  (List.range tl.NM).all fun mu =>
    let s := tl.shp.getD mu {}
    s.J == 1 && s.Rd == 0 && s.R == s.mS && s.Rr == s.mS &&
      s.mS == ((tl.mats.getD mu {}).m + 2) / 3

/-- The first exponents that `powersF` lays. -/
def firstsOf (tl : HTailF2) : Array Nat :=
  tl.shp.foldl (fun a s => a.push (a.getD (a.size - 1) 0 + tl.stepF * 2 ^ clog2 s.mS)) #[0]

/-- The marks "this matrix's sums are laid", as `foldSums` reads them. -/
def takenOf (tl : HTailF2) : Array Bool :=
  if tl.foldTakenF.size != tl.NM then Array.replicate tl.NM false else tl.foldTakenF

/-- The data without what `eqWeights` lays. -/
def unlaid (tl : HTailF2) : HTailF2 :=
  { tl with
    vt := #[], vp := #[], rowX := #[], loX := #[], gamX := #[], gamV := #[], eqFirst := #[]
    foldTakenF := #[] }

/-- Behind `eqWeights`. -/
structure Laid (tl tl' : HTailF2) : Prop where
  rest : unlaid tl' = unlaid tl
  vt : tl'.vt.size = tl.tau
  vp : tl'.vp.size = tl.tau
  rowX : ∀ mu, mu < tl.shp.size → (tl'.rowX.getD mu #[]).size = (tl.shp.getD mu {}).mS
  loX : ∀ mu, mu < tl.shp.size → (tl'.loX.getD mu #[]).size = 1
  gamX : ∀ mu, mu < tl.NM → (tl'.gamX.getD mu #[]).size = (tl.mats.getD mu {}).k
  gamV : ∀ mu, mu < tl.NM → (tl'.gamV.getD mu #[]).size = (tl.mats.getD mu {}).k
  eqFirst : tl'.eqFirst = firstsOf tl
  taken : 0 < tl.NM → tl'.foldAllTakenF = true

/-- In front of a tie. -/
structure TieReady (tl : HTailF2) (mu : Nat) : Prop where
  rows : (tl.rowX.getD mu #[]).size = (tl.shp.getD mu {}).Rr
  lo : (tl.loX.getD mu #[]).size = (tl.shp.getD mu {}).J
  gam : (tl.gamX.getD mu #[]).size = (tl.shp.getD mu {}).k
  mat : mu < tl.NM
  cells : 0 < (tl.mats.getD mu {}).m

/-- A run by its numbers: array, row, first column, first weight, length, number of weights. -/
def runNums (r : Run2) : Nat × Nat × Nat × Nat × Nat × Nat :=
  (r.tree, r.row, r.first, r.w0, r.n, r.w.size)

/-- The tie's claim by its numbers. -/
structure TieClaim (tl : HTailF2) (mu : Nat) (c : Claim) : Prop where
  eqFirst : c.eqFirst = some (tl.eqFirst.getD mu 0)
  ents : c.form.ents = #[]
  slots : c.form.slots = #[]
  runs : c.runs.toList.map runNums =
    [(tl.ix.ZZ, tl.zzRowTies, tl.off.getD mu 0, 0, (tl.shp.getD mu {}).m, (tl.shp.getD mu {}).m),
      (tl.ix.ZZ, tl.zzRowTies, tl.mz + tl.off.getD mu 0, 0, (tl.shp.getD mu {}).m,
        (tl.shp.getD mu {}).m),
      (tl.gtTree.getD mu 0, 0, 0, 0, (tl.shp.getD mu {}).J * (tl.shp.getD mu {}).k,
        (tl.shp.getD mu {}).J * (tl.shp.getD mu {}).k)]

/-- The columns of the array number tU, 0 if there is none. -/
def colsOf (F : Fork) (tU : Nat) : Nat := ((F.trees[tU]?).map fun X => X.K).getD 0

/-- How many segments a table has. -/
def segs (tl : HTailF2) (Fn : HFun) : Nat := (tl.mats.getD Fn.mat {}).m / Fn.len

/-- In front of a read. -/
structure ReadReady (tl : HTailF2) (F : Fork) (Fn : HFun) (sg tU : Nat) : Prop where
  unit : tl.ix.U.getD Fn.tree none = some tU
  cols : colsOf F tU ≠ 0
  mat : Fn.mat < tl.NM
  len : Fn.len ≠ 0
  seg : sg < segs tl Fn
  row : 0 < (tl.mats.getD Fn.mat {}).k →
    (Fn.start + ((tl.mats.getD Fn.mat {}).k - 1) * segs tl Fn + sg) / colsOf F tU < 2 ^ 32

/-- The read's claim by its numbers. -/
structure ReadClaim (tl : HTailF2) (F : Fork) (Fn : HFun) (sg laid tU : Nat) (c : Claim) :
    Prop where
  eqFirst : c.eqFirst = some (tl.eqFirst.getD tl.NM 0 + laid * tl.stepF)
  ents : c.form.ents.toList.map (fun x => (x.tree, x.row, x.idx)) =
    (List.range (tl.mats.getD Fn.mat {}).k).map fun col =>
      (tU, (Fn.start + col * segs tl Fn + sg) / colsOf F tU,
        (Fn.start + col * segs tl Fn + sg) % colsOf F tU)
  slots : c.form.slots = #[]
  runs : c.runs.toList.map runNums =
    [(tl.ix.ZZ, tl.zzRowReads, tl.off.getD Fn.mat 0 + sg * Fn.len, 0, Fn.len, Fn.phi.size),
      (tl.ix.ZZ, tl.zzRowReads, tl.mz + tl.off.getD Fn.mat 0 + sg * Fn.len, 0, Fn.len,
        Fn.phi.size)]

namespace Spec

/-- States: where the batching element is drawn, the plan has a claim, each matrix's symbols lie in
one row each and no matrix's sums are laid yet, the weights and the sums are laid; ledger and claims
stay. -/
def eqWeights_returns : Prop :=
  ∀ (tl : HTailF2) (front : Nat) (F : Fork) (cs : Array Claim),
    F.thetaDrawnF = true → F.planClaimsF ≠ 0 → oneRow tl = true →
    (∀ mu, mu < tl.NM → (takenOf tl).getD mu true = false) →
    ∃ tl', eqWeights tl front (F, cs) = .ok (tl', (F, cs)) ∧ Laid tl tl'

/-- States: a tie is laid; the ledger stays; one claim more. -/
def eqTie_returns : Prop :=
  ∀ (tl : HTailF2) (mu front : Nat) (F : Fork) (cs : Array Claim), TieReady tl mu →
    ∃ c, eqTie tl mu front (F, cs) = .ok ((), (F, cs.push c)) ∧ TieClaim tl mu c

/-- States: a read is laid, if also no sum of its matrix's columns is the element 0; the ledger
stays; one claim more. -/
def eqRead_returns : Prop :=
  ∀ (tl : HTailF2) (Fn : HFun) (sg laid tU : Nat) (sums : E) (front : Nat) (F : Fork)
    (cs : Array Claim), ReadReady tl F Fn sg tU → LiveAt tl (Fn, sg) →
    ∃ c, eqRead tl Fn sg laid sums front (F, cs) = .ok ((), (F, cs.push c)) ∧
      ReadClaim tl F Fn sg laid tU c

/-- States: an open list of tables is closed. -/
def close_returns : Prop :=
  ∀ (tl : HTailF2) (funs : Array HFun), tl.funClosed = false →
    Order.close tl funs = .ok { tl with funClosed := true, funs := funs }

/-- States: in front of the draw: the list is closed, one shape a matrix, and the guard of order
says yes. -/
def front_returns : Prop :=
  ∀ (tl : HTailF2) (L : LinkCtx) (S : Statement), tl.funClosed = true → tl.shp.size = tl.NM →
    Order.orderOk tl L S = true → Order.front tl L S = .ok ()

end Spec

end VerifiableInference.Desc.First.K8.Honest
