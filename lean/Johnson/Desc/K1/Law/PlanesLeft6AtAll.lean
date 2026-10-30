-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/PlanesLeft6AtAll.lean: `PlanesLeft6` (Johnson/Desc/K1/Law/ArmPlanesHostAt.lean:
what stays of the clause hHostC: three clauses on the verifier's state in front of the output
head's reads' place) INSIDE THE FENCE, AT A CLOSED CONSTANT (`hA.𝔇`,
Johnson/P5J/MgAtAll.lean), where the fence's letter J is "reached in front of some segment's reads,
inside the promise, without a mark" (`JReach`, Johnson/Desc/K1/Law/JReach.lean). Statements with
their proofs; one small closed fact by Lean's kernel, with its negative test.

  `sentOpen342`, `sentOpen342_fails`   BY LEAN's KERNEL: the public item "frame.sentIs" of segment
      24 stands open in front of the head's reads' place; segment 23's does not
  `linkNo_in_fence`   so inside the fence the state's own number of the open segment is 24
  `at342_of_fence`   JReach says "in front of SOME segment's reads": by
      the two promises that segment is 24 (`linkNo_at_reads`,
      Johnson/Desc/AtSeats/FirstSeatedAtLinkNo.lean): so the fence's state in front is a reached
      state at number 342
  `planesLeft6_atAll`   **PlanesLeft6 inside the fence**: hlk by `look_at_342`
      (Johnson/Desc/AtSeats/LookAt342.lean) · hlay by `partLive_at_rch`
      (Johnson/Desc/AtSeats/LiveAtRch.lean) · hMatsP BY THE PREMISE hMP

THE PREMISE THAT STAYS: hMP: at each reached state at number 342, inside the promise, without a
mark: `MatsSeated` at the planes' matrix (number NHf + 2) at the open part: in the text of
`matsP_342` (Johnson/P4R/Head342Cols.lean), whose file is not imported here: not
called here.

What is not claimed. hMP. No member of the head hA. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.ArmPlanesHostAt
import Johnson.Desc.AtSeats.LookAt342
import Johnson.Desc.AtSeats.LiveAtRch
import Johnson.Desc.AtSeats.FirstSeatedAtLinkNo

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Maker (WholeD)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Block Chain Strs)
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.FillSent (sentIsB link_of_sentIs)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13 mgBase linkNo onQ)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Kinds.Head.Law (MatsSeated)
open Johnson.Desc.First.Walk.Tied (RchAt RchPub)
open OnBytes.Params (Rounds)
open ProofFile (Cl)
open IM (k1Ix)

set_option maxRecDepth 1000000 in
theorem sentOpen342 : openB mwMore linksFull (flatPlacesOf linksFull true) (noL 24 false)
    (.more (some 24) "frame.sentIs") = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: another segment's item is not open there. -/
theorem sentOpen342_fails : openB mwMore linksFull (flatPlacesOf linksFull true) (noL 24 false)
    (.more (some 23) "frame.sentIs") = false := by
  decide +kernel

/-- Inside the fence the state's own number of the open segment is 24. -/
theorem linkNo_in_fence {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
    (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data) {x : ProofFile.InstPub × S}
    {y : Strs}
    (hIn : InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm mgBase)) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) : linkNo x.2 = 24 := by
  have h0 := pub_at342 Dm dk (.more (some 24) "frame.sentIs") sentOpen342 hIn
  rw [First.pubAll_more_sentIs] at h0
  cases hL : x.2.link? with
  | none =>
    unfold sentIsB at h0
    rw [hL] at h0
    cases h0
  | some L =>
    unfold linkNo
    rw [hL]
    exact link_of_sentIs hL h0

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
include hA

/-- **The fence's state in front is a reached state at number 342.** -/
theorem at342_of_fence (dk : K12Data) (Pp : ProofFile.InstPub → Prop) {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt hA.𝔇.N (mw1 hA.𝔇.N (d13 hA.𝔇) dk (mgAll hA.𝔇 mgBase)) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y)
    (hJ : JReach (RchPub (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
      (D.at frS.P.T.a).key₁ 0).E.Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Pp) hA.𝔇.N
      (mgAll hA.𝔇 mgBase) x.2) :
    ∃ a, RchPub (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
        (D.at frS.P.T.a).key₁ 0).E.Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Pp 342 a ∧
      onQ hA.𝔇.N (mgAll hA.𝔇 mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) 342 a ∧
      a.1.2.failed = none ∧ a.1.2 = x.2 := by
  obtain ⟨l, hl, a, hr, hon, hm, e⟩ := hJ
  have h1 : linkNo a.1.2 = l := linkNo_at_reads hA l hl a hon hm
  have h2 : linkNo x.2 = 24 := linkNo_in_fence hA.𝔇 dk hIn
  obtain rfl : l = 24 := by rw [← h1, e, h2]
  exact ⟨a, hr, hon, hm, e⟩

/-- **PlanesLeft6 inside the fence.** -/
theorem planesLeft6_atAll (dk : K12Data) (Pp : ProofFile.InstPub → Prop) (num6 : ℕ → ℕ → ℕ)
    (hMP : ∀ a, RchPub (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
        (D.at frS.P.T.a).key₁ 0).E.Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Pp 342 a →
      onQ hA.𝔇.N (mgAll hA.𝔇 mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) 342 a →
      a.1.2.failed = none → ∀ aK, K9.segAt? a.1.2 = some aK →
      MatsSeated (fun μ _ => μ = (P5J.At.X Zp).hS.NHf + 2) hA.𝔇.arr hA.𝔇.N (P5J.At.X Zp)
        (hA.𝔇.N.sent 24 0) aK num6 (P5J.At.layout Zp))
    (aN : ℕ) (R₁ R₂ R₃ : Rounds) {X : Stages.LinkH} {arrs : Option (List ℕ)}
    {x x' : ProofFile.InstPub × S} {y y' : Strs}
    {w : Wit (CellsQ OnBytes.Flat.numsFull.rows (P5J.colsAt OnBytes.Flat.numsFull)) P5J.At.Tok
      MsgT}
    {p : ℕ × String} {A B : K9.Part}
    (Fc : ReadsFence hA.𝔇 dk mgBase
      (JReach (RchPub (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
        (D.at frS.P.T.a).key₁ 0).E.Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Pp) hA.𝔇.N
        (mgAll hA.𝔇 mgBase)) Zp Bs aN R₁ R₂ R₃ cF 24 X arrs x x' y y' w p A B) :
    PlanesLeft6 (P5J.At.X Zp) (hA.𝔇.N.sent 24 0) x.2 A hA.𝔇.arr hA.𝔇.N num6
      (P5J.At.layout Zp) := by
  obtain ⟨a, hr, hon, hm, e⟩ := at342_of_fence hA dk Pp Fc.inAt Fc.inv
  have hseg : K9.segAt? a.1.2 = some A := by rw [e]; exact Fc.front
  refine ⟨?_, (partLive_at_rch hA 342 a hr.1 hm A hseg).2, hMP a hr hon hm A hseg⟩
  rw [← e]
  exact look_at_342 hA a hr.1

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.sentOpen342
#print axioms VerifiableInference.Desc.K1.sentOpen342_fails
#print axioms VerifiableInference.Desc.K1.linkNo_in_fence
#print axioms VerifiableInference.Desc.K1.at342_of_fence
#print axioms VerifiableInference.Desc.K1.planesLeft6_atAll
