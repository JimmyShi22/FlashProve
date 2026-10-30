-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyDotMeets.lean: (Dot)'s equation between the shared chain's honest Omega and the first chain's
honest W, with no thread and no last chain: the place where the two chains are asked to hold one
matrix.

This file is a composition of four library lemmas, and it answers no question of its own: what could
part the two chains stands here as premises, under «What stays open».

Why. The item (Dot) is read at the last chain's start, where the row is not yet laid, so its library
form is an equation on two vectors. The library has it at the shared chain's words, under the premise
`VIs` on the other vector (`dot_at`, Johnson/Desc/K14/Honest/ItemsHold.lean). The half on W is said of
the words that W's sending lays (`wIs_held`, E2E/KeyWIs.lean). Here the one meets the other.

Main names.
  `vis_of_wIs`: `WIs` at a matrix that spells the reader of the rows gives `VIs`.
  `dot_meets`: the equation, at any words that hold W.
  `dot_meets_job`: at the words that W's sending has laid, at the job's own weights.

What stays open. `hRw` ties the rows to the reader of the index; that W's job reads the same index as
the rows is the premise `hRw` at the job's `entry`, and `K.w` is a letter of `KeyParts`: that it is
`wJob` at `K.weights` is said nowhere. That the job's weights are the row weights handed to the last
chain is `handed_is` (E2E/KeyEvalSays.lean), under ties that are not paid here. That the point is the
shared end's is one equation, not here. No run is shown, and no item is joined to a thread. In
`dot_meets_job` the shape of the first chain and the shared chain's are one by the premise `hS`.

NOT IN FRONT OF A LAW OVER COINS: `dot_meets` and `dot_meets_job` bear this label; the rule is at its
home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: of the first kind `hRw`, which
ties the letter `H` to the committer's pads and tails; of the second kind `hW` and `hmat`, which read the
hidden matrix. None: the bar is flat: no lemma here lays in the made term `holds2`. `vis_of_wIs` keeps
`Tab` a letter under `hTab`, of the second kind, and bears the label too.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyDotSays
import Johnson.Desc.K14.Honest.ItemsHold
import Johnson.Desc.K14.Law.PointGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyDotMeets
open OnBytes OnBytes.Params
open OnBytes.Means (Words)
open OnBytes.Slice (rdE GE GF)
open _root_.Desc.K14.Law (DotEq VIs matOf)
open _root_.Desc.K14.Honest (PlanFacts Inputs omegaAt words2 dot_at)
open VerifiableInference.Desc.K13.Law (WIs ρg lowBits)

/-- **The half on W in the form that `dot_at` asks**, at a table of rows whose matrix is spelled by
the one in `WIs`.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem vis_of_wIs (S : LinShape) (Tab : Nat → Nat → GE)
    (mat : Fin S.matrixRows → (Fin S.kCol → Bool) → GE) (m : Words GE) (ws : List Tensor) (w : Nat)
    (wLay : VectorLay) (hW : WIs mat m ws w wLay)
    (hTab : ∀ (i : Fin S.matrixRows) (e : Nat), e < 2 ^ S.kCol →
      mat i (lowBits S.kCol e) = matOf S.kLo Tab i.val e) :
    VIs S (fun y => (ws.map fun g => ρg.val (g.entry y)).sum) Tab
      (fun c => m w .main (wLay.index c)) :=
  fun c hc => AtPublicFiles.Key.wHalf_of_wIs mat m ws w wLay hW (matOf S.kLo Tab) hTab c hc

/-- **(Dot)'s equation at the shared chain's Omega and at any words that hold W.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem dot_meets {P : _root_.Desc.K14.P14} {sentU : Array OracleNotice} {layO : TreeLay}
    (hP : PlanFacts P.par P.codes sentU layO) (d0 : _root_.Desc.K14.St) (r1 : Fmt.RoundView) (H : Inputs)
    (hpt : (_root_.Desc.K14.drawn r1).length = P.par.S.kCol) (entry pad tail : Nat → Nat → GF)
    (hRw : ∀ r j, H.Rw r j = rdE.val (ProofFile.Honest.K14.rowsOf P.par.S ⟨entry⟩ ⟨pad, tail⟩ r j))
    (mat : Fin P.par.S.matrixRows → (Fin P.par.S.kCol → Bool) → GE)
    (hmat : ∀ (i : Fin P.par.S.matrixRows) (e : Nat), e < 2 ^ P.par.S.kCol →
      mat i (lowBits P.par.S.kCol e) = algebraMap GF GE (entry i.val e))
    (m : Words GE) (ws : List Tensor) (w : Nat) (wLay : VectorLay)
    (hW : WIs mat m ws w wLay) :
    DotEq P.par.S.matrixRows P.par.S.kCol (fun y => (ws.map fun g => ρg.val (g.entry y)).sum)
      (omegaAt P d0 (words2 P sentU d0 r1 H)) ((_root_.Desc.K14.drawn r1).map rdE.val)
      (fun c => m w .main (wLay.index c)) := by
  have eR : H.Rw = fun r k =>
      ρg.val (ProofFile.Honest.K14.rowsOf P.par.S ⟨entry⟩ ⟨pad, tail⟩ r k) :=
    funext fun r => funext fun k => hRw r k
  refine dot_at hP d0 r1 H hpt _ _ (vis_of_wIs P.par.S H.Rw mat m ws w wLay hW fun i e he => ?_)
  rw [hmat i e he, eR, AtPublicFiles.Key.matOf_rowsOf P.par.S entry pad tail i.val e i.isLt]

section job
variable {W X : Type} (entry : W → Nat → Nat → GF) (one : OneTime) (N : VerifiableInference.Desc.Key.Pieces)
  (groups : List (List Nat)) (first : Nat) (ride : Nat → Option ProofFile.Honest.K1.Ride)
  (points : List Fmt.Drawn → Nat → Nat → List E) (a : AtPublicFiles.Key.BattAt)

/-- **(Dot)'s equation at the words that W's sending has laid**, at the weights of W's job. hS: the
first chain's shape is the shared chain's.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem dot_meets_job (J : ProofFile.Honest.K1.SendJob W X)
    (hJ : AtPublicFiles.Key.wJob entry one N groups first ride points a = some J)
    (hans : one.lin.w.answers ≠ 0) (hmask : one.lin.w.maskRows ≠ 0) (hdeg : one.lin.w.mainDeg = 3)
    (c : ProofFile.Honest.Cs (ProofFile.Honest.K1.dueR J.P J.ride)) (s : ProofFile.Honest.Seen)
    (t : ProofFile.Honest.State W X) (n : Nat) (w₀ : Words GE)
    (mat : Fin one.lin.matrixRows → (Fin one.lin.kCol → Bool) → GE)
    (hmat : ∀ i e, e < 2 ^ one.lin.kCol →
      mat i (lowBits one.lin.kCol e) = algebraMap GF GE (entry t.input i.val e))
    (hbits : one.lin.kCol ≤ (linLayW one.codes one.lin).bits)
    (hfit : ∀ e < 2 ^ one.lin.kCol,
      (linLayW one.codes one.lin).index e % 2 ^ ceilLog2 one.lin.w.mainRows <
          one.lin.w.mainRows ∧
        (linLayW one.codes one.lin).index e / 2 ^ ceilLog2 one.lin.w.mainRows <
          (one.codes.base.getD one.lin.w.code default).ell)
    {P : _root_.Desc.K14.P14} {sentU : Array OracleNotice} {layO : TreeLay}
    (hS : P.S = one.lin) (hP : PlanFacts P.par P.codes sentU layO) (d0 : _root_.Desc.K14.St)
    (r1 : Fmt.RoundView) (H : Inputs) (hpt : (_root_.Desc.K14.drawn r1).length = P.par.S.kCol)
    (pad tail : Nat → Nat → GF)
    (hRw : ∀ r j, H.Rw r j =
      rdE.val (ProofFile.Honest.K14.rowsOf P.par.S ⟨entry t.input⟩ ⟨pad, tail⟩ r j)) :
    DotEq P.par.S.matrixRows P.par.S.kCol
      (fun y => ((AtPublicFiles.Key.wWeights one points a (t.heard.take (t.heard.length - n))).map
        fun g => ρg.val (g.entry y)).sum)
      (omegaAt P d0 (words2 P sentU d0 r1 H)) ((_root_.Desc.K14.drawn r1).map rdE.val)
      (fun e => Johnson.Prover.Send.held w₀ first J.P (J.rows c s t n) first .main
        ((linLayW one.codes one.lin).index e)) := by
  obtain ⟨set, scope, codes, S, item, bp⟩ := P
  obtain rfl : S = one.lin := hS
  exact dot_meets hP d0 r1 H hpt (entry t.input) pad tail hRw mat hmat
    (Johnson.Prover.Send.held w₀ first J.P (J.rows c s t n))
    (AtPublicFiles.Key.wWeights one points a (t.heard.take (t.heard.length - n))) first
    (linLayW one.codes one.lin)
    (AtPublicFiles.Key.wIs_held entry one N groups first ride points a J hJ hans hmask hdeg c s t n w₀ mat hmat
      hbits hfit)

end job

end AtPublicFiles.KeyDotMeets

#print axioms AtPublicFiles.KeyDotMeets.vis_of_wIs
#print axioms AtPublicFiles.KeyDotMeets.dot_meets
#print axioms AtPublicFiles.KeyDotMeets.dot_meets_job
