-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/ZzAheadAtReach.lean: the smallness test (K8), the verifier's state and public
data alone: behind a draw's yes, at each of the 25 segments, the array of digits is AHEAD: the state
has an open segment's part; the part's list of arrays is the built segment's; at the digits' index
that list names an array of the ground's layout; the plan's look ahead (`aheadIn`,
Johnson/Desc/First/Batch/Ahead.lean) returns that array, the seat that the plan gives its message
and the message's shape; and the programs' own test `laidMatrixOk` passes there. One theorem; no
definition.

  **`zzAhead_at_reach`**   the library's head, the blank ground, l at most 24, the built segment,
                  "reached" at the draw's border, no mark, the draw's yes from s to t
The lines are the first two thirds of `digAhead_at_reach`
(Johnson/Desc/K8/Honest/DigAheadAtReach.lean), written a further time: that law ends in the lookups'
`DigAheadOk`, which leaves open whether the look ahead returns; here what it returns is the end.
Two options are raised (maxHeartbeats, for the file; maxRecDepth, at the theorem) and one instance
is taken away, as in that file. No tactic that searches.
Limits. That any state is reached is not said. The full size alone. No prover, no Script, no input,
no coin, no witness.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.DigAheadAtReach

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Honest

open Iop
open OnBytes OnBytes.Model OnBytes.Params OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Claim Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Numbers FoldFacts flatPlacesOf)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.K9 (Ahead aheadIn rowBitsOf placeBitsOf aheadPlanSizeB)
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)
open Q38

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option maxRecDepth 40000 in
/-- **Behind a draw's yes the array of digits is ahead, and the look ahead returns it with the
plan's seat and the message's shape.** -/
theorem zzAhead_at_reach (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {l : ℕ} (hl : l ≤ 24)
    {Xl : LinkH} (e3 : G.built[l]? = some Xl) (z : ProofFile.InstPub) (s t : S)
    (hr : RchAt (P1K8T.FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) (drawAt l) ((z, s), ()))
    (hu : s.failed = none)
    (hd : ∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS (ProofFile.k8ParW Zp G Xl l).toPar).decide s rs gs = .ok t) :
    ∃ (p : VerifiableInference.Desc.K9.Part) (bn : ℕ × String) (A : ReqArray) (sh : ReqLink)
      (M : ReqMessage),
      VerifiableInference.Desc.K9.segAt? t = some p ∧ p.L.arrayOf = Xl.arrayOf ∧
      p.d.st.codes = P5J.At.cs Zp ∧ Xl.arrayOf[Xl.tl.ix.ZZ]? = some bn ∧ bn.1 = l ∧
      reqArray G.first.layout l bn.2 = some A ∧ Zp.first.shape.link[l]? = some sh ∧
      sh.messages[A.message]? = some M ∧
      aheadIn ((P5J.At.N Zp cF).sent l) ((P5J.At.N Zp cF).group l) p bn =
        some ⟨A, P5J.At.seat3At Zp l true A.message, M.shape⟩ ∧
      laidMatrixOk A (rowBitsOf M.shape .main) (placeBitsOf (P5J.At.cs Zp) M.shape .main) =
        true := by
  obtain ⟨L₀, A₀⟩ := P5J.atMgR_of_head h (Str := Unit)
    (fun k a => RchAt (P1K8T.FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) k a) (fun _ _ u => u)
  have FF := A₀.fold
  have hnear := IM.k08_near_at h hG hl e3
  obtain ⟨rs, gs, hd⟩ := hd
  obtain ⟨L, Gr, pre, hL, -, -, -, e1, e2, e5, e6, e4⟩ :=
    P1K8T.k08_fold_at h hG hl e3 ((z, s), ()) hr
  have hL' : s.link? = some L := hL
  obtain ⟨p, hp, pL, pst⟩ := segAt_behind_draw (drawn_of_yes _ _ _ rs gs hd) hL'
  obtain ⟨bn, A, sh, M, f1, f2, f3, f4, f5, f6⟩ :=
    ahead_of_seats (P1K8T.n0At Zp l) ((P5J.At.N Zp cF).sent l) ((P5J.At.N Zp cF).group l) p
      Xl.arrayOf G.first.layout Zp.first.shape (P5J.At.seat3At Zp l true) l Xl.tl.ix.ZZ
      (by rw [pL]; exact e1) (by rw [pL]; exact e2) (by rw [pL]; exact e6) (by rw [pL]; exact e4)
      (by rw [pL]; exact e5) hnear (aheadSeats_at_head h.toAtMg hl)
  have f3' : reqArray (P5J.At.layout Zp) l bn.2 = some A := by
    rw [← P1K8T.layout_at hG]
    exact f3
  have hmat : laidMatrixOk A (rowBitsOf M.shape .main) (placeBitsOf (P5J.At.cs Zp) M.shape .main) =
      true := matrixOk_ahead (lawful_at_head h) f3' f4 f5
  refine ⟨p, bn, A, sh, M, hp, ?_, ?_, f1, f2, f3, f4, f5, f6, hmat⟩
  · rw [pL]
    exact e1
  · rw [pst]
    exact codes_at_draw FF (a := ((z, s), ())) hr hu

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.zzAhead_at_reach
