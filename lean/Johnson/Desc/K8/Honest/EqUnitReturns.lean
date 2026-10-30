-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/EqUnitReturns.lean: THE SMALLNESS TEST: THE LAWS OF
Johnson/Desc/K8/Honest/EqTailReturns.lean, EqAllReturns.lean AND EqRunReturns.lean ONCE MORE, WITH
ONE CLAUSE MORE BEHIND: WHICH ARRAY A READ's ENTRIES LIE ON. Two definitions and three statements,
each a definition of a proposition; no proof stands here. Lemmas; none of the library's goals.

WHY. These three laws say of each read's claim "there is a number tU with `ReadClaim … tU c`", and
`ReadClaim` ties tU to nothing: so the array's number in the claim's entries, and with it each
entry's row and place (they are a quotient and a remainder by that array's columns), were not
determined by the laws. Here tU is the number that the plan's state holds for the table's vector.
  `ReadLaid tl tl' F q x c`   the claim c is read number q's, of the read x: there is tU with
                     `tl.ix.U.getD x.1.tree none = some tU` and `ReadClaim tl' F x.1 x.2 q tU c`
  `BehindAllU …`     `BehindAll` (EqRunReturns.lean) with that clause
  `Spec.eqTail_returns_unit`, `Spec.eqAll_returns_unit`, `Spec.run_returns_unit`   the same
                     premises as the three laws; the same ends, but for that clause
The end with the clause gives the end without it (`behindAll_of_unit`,
Johnson/Desc/K8/Honest/EqUnitProofs.lean). The limits are those of the three files.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.EqRunReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (St Ret OnlySide keysClaim countsClaims partOf
  eqTail)
open VerifiableInference.Desc.First.Shape
open OnBytes.Tie.Pv.Tail.Port (readsList)

/-- The claim c is read number q's, of the read x, on the array that the plan's state holds for the
table's vector. tl: the data in front; tl': behind the weights' step. -/
def ReadLaid (tl tl' : HTailF2) (F : Fork) (q : Nat) (x : HFun × Nat) (c : Claim) : Prop :=
  ∃ tU, tl.ix.U.getD x.1.tree none = some tU ∧ ReadClaim tl' F x.1 x.2 q tU c

/-- What stands behind the list, at no claim in front. -/
def BehindAllU (front : Nat) (tl : HTailF2) (funs : Array HFun) (F : Fork) (g : Forest.Heard)
    (out : HTailF2) (F' : Fork) (cls : List Claim) : Prop :=
  ∃ (bf : E) (tl' : HTailF2) (four ties reads : List Claim),
    Laid { tl with joinObj9 := some front, bitFactor9 := bf } tl' ∧
    out = { tl' with
      tieObj := numbersFrom (front + 4) tl.NM
      tiesOn := tiesOnOf tl F.trees.size
      nX4Laid := (readsList tl funs).length } ∧
    OnlySide F F' ∧
    ledSh F' = ((ledSh (F.paid g.owedJoin)).setGot
      (fillB (ledSh (F.paid g.owedJoin)).got g.leaves.first (D6.Ret.taken g.leaves))).setOwed
        (paidB (ledSh (F.paid g.owedJoin)).owed g.owedPlanes) ∧
    cls = four ++ (ties ++ reads) ∧
    four.map claimSh = keysClaim tl g :: countsClaims tl g ∧
    LaidBy (fun _ mu c => TieClaim tl' mu c) 0 (List.range tl.NM) ties ∧
    LaidBy (ReadLaid tl tl' F') 0 (readsList tl funs) reads

namespace Spec

/-- `eqTail_returns`, with the array of each read's entries said. -/
def eqTail_returns_unit : Prop :=
  ∀ (before front : Nat) (tl : HTailF2) (funs : Array HFun) (F : Fork) (cs : Array Claim)
    (rd : Array (Array Bool)) (s1 s3 : Nat), TailReady before front tl funs F cs rd s1 s3 →
    (∀ tl', eqWeights tl front (F, cs) = .ok (tl', (F, cs)) →
      ∀ x ∈ readsList tl funs, LiveAt tl' x) →
    Ret (eqTail before tl funs) front (F, cs) fun out s' =>
      ∃ (tl' : HTailF2) (ties reads : List Claim), Laid tl tl' ∧
        out = { tl' with
          tieObj := numbersFrom (front + cs.size) tl.NM
          tiesOn := tiesOnOf tl F.trees.size
          nX4Laid := (readsList tl funs).length } ∧
        s' = (F, cs ++ (ties ++ reads).toArray) ∧
        LaidBy (fun _ mu c => TieClaim tl' mu c) 0 (List.range tl.NM) ties ∧
        LaidBy (ReadLaid tl tl' F) 0 (readsList tl funs) reads

/-- `eqAll_returns`, with the array of each read's entries said. -/
def eqAll_returns_unit : Prop :=
  ∀ (front : Nat) (tl : HTailF2) (funs : Array HFun) (F : Fork) (cs : Array Claim)
    (g : Forest.Heard) (rd : Array (Array Bool)) (s1 s3 : Nat),
    AllReady front tl funs F cs g rd s1 s3 → tl.funsHeld funs = true →
    (F.LS.extract tl.slotA tl.slotB).all isZeroE = true → LiveCols tl funs F.theta →
    Ret (eqAll tl funs) front (F, cs) fun out s' =>
      ∃ (bf : E) (tl' : HTailF2) (four ties reads : List Claim),
        Laid { tl with joinObj9 := some (front + cs.size), bitFactor9 := bf } tl' ∧
        out = { tl' with
          tieObj := numbersFrom (front + (cs.size + 4)) tl.NM
          tiesOn := tiesOnOf tl F.trees.size
          nX4Laid := (readsList tl funs).length } ∧
        OnlySide F s'.1 ∧
        ledSh s'.1 = ((ledSh (F.paid g.owedJoin)).setGot
          (fillB (ledSh (F.paid g.owedJoin)).got g.leaves.first (D6.Ret.taken g.leaves))).setOwed
            (paidB (ledSh (F.paid g.owedJoin)).owed g.owedPlanes) ∧
        s'.2 = cs ++ (four ++ (ties ++ reads)).toArray ∧
        four.map claimSh = keysClaim tl g :: countsClaims tl g ∧
        LaidBy (fun _ mu c => TieClaim tl' mu c) 0 (List.range tl.NM) ties ∧
        LaidBy (ReadLaid tl tl' s'.1) 0 (readsList tl funs) reads

/-- `run_returns`, with the array of each read's entries said. -/
def run_returns_unit : Prop :=
  ∀ (p : K8.ParW) (run : Nat → S → Except String (List Claim × S)),
    ("K8.equations", run) ∈ (K8.whole p).claims →
    ∀ (front : Nat) (s : S) (q : K8Part) (g : Forest.Heard) (rd : Array (Array Bool))
      (s1 s3 : Nat), partOf s = some q →
    AllReady (q.F.nClaim + front) q.tl q.funs q.F #[] g rd s1 s3 →
    q.tl.funsHeld q.funs = true → (q.F.LS.extract q.tl.slotA q.tl.slotB).all isZeroE = true →
    LiveCols q.tl q.funs q.F.theta →
    ∃ (cls : List Claim) (out : HTailF2) (F' : Fork),
      run front s = .ok (cls, k8PartP.set s { q with tl := out, F := F' }) ∧
      BehindAllU (q.F.nClaim + front) q.tl q.funs q.F g out F' cls

end Spec

end VerifiableInference.Desc.First.K8.Honest
