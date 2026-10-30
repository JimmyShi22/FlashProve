-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/K5PlanCut.lean: code switching (K2): THE NAMED TEST k5PlanB
(Johnson/P1K2R/PlanBools.lean) CUT IN TWO: its first two conjuncts («link l is an attention
segment» · «the first message with a mask row stands among those of moment 0») are closed facts by
Lean's kernel at the written list of links and the written shape: so, where the layer's data have
these two, the test's value at a written attention link is the value of THE REST. NO BLOCK IMPORTS
THIS FILE.
  k5RestB Z W sh lay₀ l   k5PlanB without the two: the attention's plan at l / 2 and the built
                          link at l are there · r2B (the request's array of the reads) · the
                          starting ledger's array iU3 has one row and nW columns
  k5PlanB_split           k5PlanB Z d lay₀ l = (d.isAtt l && maskFirstB d.shape l && k5RestB Z d.W
                          d.shape lay₀ l): by the text
  isAtt_written           BY THE KERNEL: at the written list of links every l of attW is an
                          attention segment · isAtt_layers: A NEGATIVE FACT, BY THE KERNEL: none
                          of the other links 0 … 24 is
  k5PlanB_written         d.links = linksW · d.shape = proofSizedFull.request · l ∈ attW ⟹ k5PlanB
                          Z d lay₀ l = k5RestB Z d.W d.shape lay₀ l
  k5PlanB_head            at the composed meaning's own data (h.𝔇 𝔇₀).pubD.d5, under AtWritten Zp
                          cF: the same, with W := At.X Zp and the shape Zp.first.shape
AtWritten Zp cF holds from the head (with the fourteen entry tests): at_written
(Johnson/Top/H0/K2Ties/WrittenAt.lean) with pins_of_laid: NOT CALLED HERE: a premise.
LIMITS. k5RestB is evaluated nowhere by itself (k5PlanB accepted at the twelve at the stored
full-size public part). verify() asks neither. The full size alone. No soundness is claimed.

-/
import Johnson.P1K2R.PlanBools
import Johnson.Top.H0.K2Ties.HandsAtConst
import Johnson.Top.H0.K2Ties.WrittenAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Sound (MgData)
open VerifiableInference.Desc.First.K2Ties (AtWritten)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.Desc.First.Walk (startFork)
open Johnson.Desc.First.Walk.Seat (pubOf)
open H2K5.Door (K5Data)
open IM (linksW)

/-- k5PlanB without its first two conjuncts. -/
def k5RestB (Z : ProofFile.Pub) (W : Verify.Public) (sh : Params.ReqShape) (lay₀ : Params.ReqLayout)
    (l : Nat) : Bool :=
  match W.A[l / 2]?, Z.p.built.links[l]? with
  | some q, some X =>
    r2B lay₀ sh l (pubOf X).arrayOf q.iU3 q.nW &&
      match Z.p.X.A[X.g]? with
      | some p =>
        ((startFork (pubOf X) p.ns).trees[q.iU3]?).any fun T => T.R == 1 && T.K == q.nW
      | none => false
  | _, _ => false

theorem k5PlanB_split (Z : ProofFile.Pub) (d : K5Data) (lay₀ : Params.ReqLayout) (l : Nat) :
    k5PlanB Z d lay₀ l =
      (d.isAtt l && maskFirstB d.shape l && k5RestB Z d.W d.shape lay₀ l) := rfl

theorem k5PlanB_cut {Z : ProofFile.Pub} {d : K5Data} {lay₀ : Params.ReqLayout} {l : Nat}
    (ha : d.isAtt l = true) (hm : maskFirstB d.shape l = true) :
    k5PlanB Z d lay₀ l = k5RestB Z d.W d.shape lay₀ l := by
  rw [k5PlanB_split, ha, hm]
  rfl

theorem isAtt_written : attW.all (fun l => linksW[l]? == some .attention) = true := by
  decide +kernel

theorem isAtt_layers :
    ((List.range 25).filter fun l => !attW.contains l).any
      (fun l => linksW[l]? == some .attention) = false := by
  decide +kernel

theorem k5PlanB_written {Z : ProofFile.Pub} {d : K5Data} (hl : d.links = linksW)
    (hs : d.shape = proofSizedFull.request) (lay₀ : Params.ReqLayout) {l : Nat}
    (h : l ∈ attW) : k5PlanB Z d lay₀ l = k5RestB Z d.W d.shape lay₀ l := by
  refine k5PlanB_cut ?_ ?_
  · unfold K5Data.isAtt
    rw [hl]
    exact List.all_eq_true.1 isAtt_written l h
  · rw [hs]
    exact List.all_eq_true.1 mask_first_written l h

theorem k5PlanB_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {nR : Nat}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub P5J.At.Tok OnBytes.Flat.numsFull.rows
      (P5J.colsAt OnBytes.Flat.numsFull) nR (P5J.At.X Zp)) (A : AtWritten Zp cF)
    (lay₀ : Params.ReqLayout) {l : Nat} (hl : l ∈ attW) :
    k5PlanB Zp (h.𝔇 𝔇₀).pubD.d5 lay₀ l = k5RestB Zp (P5J.At.X Zp) Zp.first.shape lay₀ l :=
  k5PlanB_written (d := (h.𝔇 𝔇₀).pubD.d5) (Meaning.K2.const_lines (h := h) (𝔇₀ := 𝔇₀)).2.1
    A.shape lay₀ hl

end P1K2

#print axioms P1K2.k5PlanB_split
#print axioms P1K2.k5PlanB_cut
#print axioms P1K2.isAtt_written
#print axioms P1K2.isAtt_layers
#print axioms P1K2.k5PlanB_written
#print axioms P1K2.k5PlanB_head
