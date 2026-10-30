-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Walk/FrameZero.lean: the link's frame at link 0, at the one carried record:
"opened" there (LinkZero.lean's whole step at S) and its tests on the plan alone. lay and clear at
link 0 are Frame.lean's own layFront 0 and clearWith: nothing of them hangs on the link's number.
A refusal goes on under LinkZero.lean's own words (I1 ... I4, W1, W2, G1, G2); A and B as in
Frame.lean. The room that is asked of the ledger is roomOf fvs kCol (LinkZero.lean). The entering
goes by State.lean's form that refuses at once (enterLay?).
Limits: Frame.lean's.
No soundness: definitions with code.

-/
import Johnson.Desc.First.Walk.Frame
import Johnson.Desc.First.Walk.LinkZero

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk
open OnBytes OnBytes.Model
open VerifiableInference.Desc (need)
open VerifiableInference.Desc.First (S)

/-- Behind link 0's first call. P.l is 0. fvs: for each link of the chain: does its record leave a
  row. kCol: the shape of the test on the weight table. -/
def openLayZero (P : LayPar) (fvs : List Bool) (kCol : Nat) (s : S) : Except String S := do
  need "B: a link is open in the record" s.atBetween
  need "A: the link's first call has not run" (firstRun s.check)
  let a ← layFirstQuietZero P.X P.p4 P.g P.Tp P.Fp P.ns (roomOf fvs kCol) s.check s.out s.st.oracles
  S.enterLay? { s with out := a.out } a.L a.F P.tl₀

/-- The tests on the plan alone at link 0. -/
def planLayZero (shape : Params.ReqShape) (P : LayPar) : Bool :=
  P.l == 0 && planPlain shape P.X 0 && 0 == (if P.p4 then 2 * P.g else P.g) &&
    P.X.Tp.nt == P.Tp.nt && sizes P.X.Fp == sizes P.Fp && planFlag P.X 0

end Johnson.Desc.First.Walk
