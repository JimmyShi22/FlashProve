-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/EqRunReturns.lean: THE SMALLNESS TEST: THE RUN THAT THE KIND's BLOCK STATES
UNDER THE NAME "K8.equations" RETURNS AT A STATE OF THE DESCRIPTION, under the premises of
Johnson/Desc/K8/Honest/EqAllReturns.lean at the state's own parts. One definition, one statement as
a definition of a proposition, and its proof. A lemma; none of the library's goals.

  `BehindAll front tl funs F g out F' cls`   what stands behind the list: the end of `eqAll_returns`
                     at no claim in front: the data out, the ledger F', the claims cls
  `Spec.run_returns`, `run_returns`
By `eqAll_returns` (Johnson/Desc/K8/Honest/EqAllProofs.lean) and the library's `sits_equations`
(Johnson/Desc/First/TailClaims/K8Sits.lean), which says what that run is at a state. The number in
front is the ledger's count of claims plus the number that the run is handed, as there.
Limits. Those of Johnson/Desc/K8/Honest/EqAllReturns.lean: nothing says that the premises hold at
any state of a run of the verifier.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.EqAllProofs
import Johnson.Desc.First.TailClaims.K8Sits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (St Ret OnlySide keysClaim countsClaims partOf
  sits_equations)
open VerifiableInference.Desc.First.Shape
open OnBytes.Tie.Pv.Tail.Port (readsList)

/-- What stands behind the list, at no claim in front. -/
def BehindAll (front : Nat) (tl : HTailF2) (funs : Array HFun) (F : Fork) (g : Forest.Heard)
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
    LaidBy (fun q x c => ∃ tU, ReadClaim tl' F' x.1 x.2 q tU c) 0 (readsList tl funs) reads

namespace Spec

/-- States: the run under the name "K8.equations" returns at a state whose parts meet the premises;
behind it the state has the returned data and ledger laid, and nothing else turned. -/
def run_returns : Prop :=
  ∀ (p : K8.ParW) (run : Nat → S → Except String (List Claim × S)),
    ("K8.equations", run) ∈ (K8.whole p).claims →
    ∀ (front : Nat) (s : S) (q : K8Part) (g : Forest.Heard) (rd : Array (Array Bool))
      (s1 s3 : Nat), partOf s = some q →
    AllReady (q.F.nClaim + front) q.tl q.funs q.F #[] g rd s1 s3 →
    q.tl.funsHeld q.funs = true → (q.F.LS.extract q.tl.slotA q.tl.slotB).all isZeroE = true →
    LiveCols q.tl q.funs q.F.theta →
    ∃ (cls : List Claim) (out : HTailF2) (F' : Fork),
      run front s = .ok (cls, k8PartP.set s { q with tl := out, F := F' }) ∧
      BehindAll (q.F.nClaim + front) q.tl q.funs q.F g out F' cls

end Spec

theorem run_returns : Spec.run_returns := by
  intro p run hrun front s q g rd s1 s3 hq hA h1 h2 h3
  obtain ⟨out, ⟨F', c⟩, e, bf, tl', four, ties, reads, a1, a2, a3, a4, a5, a6, a7, a8⟩ :=
    eqAll_returns (q.F.nClaim + front) q.tl q.funs q.F #[] g rd s1 s3 hA h1 h2 h3
  dsimp only at a3 a4 a5 a8
  refine ⟨c.toList, out, F', (sits_equations p run hrun front s _ _).2 ⟨q, out, F', hq, ?_, rfl⟩,
    bf, tl', four, ties, reads, a1, a2, a3, a4, ?_, a6, a7, a8⟩
  · unfold equations
    rw [e]
    rfl
  · rw [a5]
    simp

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.run_returns
