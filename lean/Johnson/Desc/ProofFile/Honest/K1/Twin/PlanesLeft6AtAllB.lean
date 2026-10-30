-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/PlanesLeft6AtAllB.lean: MADE BY PROGRAM OFF
Johnson/Desc/K1/Law/PlanesLeft6AtAll.lean UNDER A MAP OF NAMES AND ONE TURN OF THE MEANING:
3 OF ITS DECLARATIONS: linkNo_in_fence_b · at342_of_fence_b · planesLeft6_atAll_b. THE PROOFS ARE
COPIES.

This letter is for the honest run's own forms alone: no statement on any other party may take it.
NEVER ON SOUNDNESS's ROAD: at the meaning "honest" the
clauses noColl, shown and decodes are True by definition: a law at that meaning may stand beneath
statements on completeness or zero knowledge only, never beneath a statement on soundness.

The map of names. ReadsFence to ReadsFenceB; each twinned theorem n to n_b; the library's closed
facts at its wider table of names (mwMore) to their likes at mgMore, and its laws on the wider
meaning to their likes on "honest" over mgAll (both in Twin/HonestAt.lean, typed by hand).
The turn of the meaning. Where the elder has the wider meaning (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀),
or plus13 (d13 Dm) dk (mgAll Dm Mg₀)), the twin has honest (mgAll Dm Mg₀) ans test
(Johnson/Desc/ProofFile/Honest/Thread/First.lean): the meaning at which the honest thread's own
promise stands; at the item "tie": mgAll Dm Mg₀. The step down from mw1 to plus13 (inAt_down) falls.
The promise itself is the library's InAt: no new text of a promise.
Laid in, on no line of a statement: the letters ans and test, behind each block of letters: implicit
in the theorems, explicit in the structure ReadsFenceB; "include dk" where the source's block
binds dk (no twin's statement names it; it is kept so that a copied call has the source's number
of arguments). Kept as they stand in the source: its namespace, open, variable, section, set_option
and attribute lines, but for one prefix that makes dk implicit (in ArmAtReadsB.lean): there "omit dk
in" stands.
The namespace is the library's, so that a copied proof finds its callees without a sign turned; the
names with the suffix _b are not the library's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.PlanesLeft6AtAll
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAtReadsB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmHeadPromiseB
import Johnson.Desc.ProofFile.Honest.K1.Twin.FirstSeatedAtLinkNoB
import Johnson.Desc.ProofFile.Honest.K1.Twin.HonestAt
import Johnson.Desc.ProofFile.Honest.K1.Twin.OpenAt342

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open ProofFile.Honest.FirstThread (honest)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (CellsQ MsgT mgMore)
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

/-- Inside the fence the state's own number of the open segment is 24. -/
theorem linkNo_in_fence_b {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
    (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
    {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {test : ℕ → S → Option String} {x : ProofFile.InstPub × S}
    {y : Strs}
    (hIn : InAt Dm.N (honest (mgAll Dm mgBase) ans test) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y) : linkNo x.2 = 24 := by
  have h0 := pub_at342_b Dm dk (.more (some 24) "frame.sentIs") sentOpen342_mg hIn
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
variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT → Prop}
  {test : ℕ → S → Option String}
include hA

/-- **The fence's state in front is a reached state at number 342.** -/
theorem at342_of_fence_b (dk : K12Data) (Pp : ProofFile.InstPub → Prop) {x : ProofFile.InstPub × S} {y : Strs}
    (hIn : InAt hA.𝔇.N (honest (mgAll hA.𝔇 mgBase) ans test) linksFull
      (flatPlacesOf linksFull true) (noL 24 false) x y)
    (hJ : JReach (RchPub (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
      (D.at frS.P.T.a).key₁ 0).E.Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Pp) hA.𝔇.N (honest (mgAll hA.𝔇 mgBase) ans test) x.2) :
    ∃ a, RchPub (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
        (D.at frS.P.T.a).key₁ 0).E.Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Pp 342 a ∧
      onQ hA.𝔇.N (honest (mgAll hA.𝔇 mgBase) ans test) linksFull (flatPlacesOf linksFull true) (fun a => a) 342 a ∧
      a.1.2.failed = none ∧ a.1.2 = x.2 := by
  obtain ⟨l, hl, a, hr, hon, hm, e⟩ := hJ
  have h1 : linkNo a.1.2 = l := linkNo_at_reads_b hA l hl a hon hm
  have h2 : linkNo x.2 = 24 := linkNo_in_fence_b hA.𝔇 dk hIn
  obtain rfl : l = 24 := by rw [← h1, e, h2]
  exact ⟨a, hr, hon, hm, e⟩

/-- **PlanesLeft6 inside the fence.** -/
theorem planesLeft6_atAll_b (dk : K12Data) (Pp : ProofFile.InstPub → Prop) (num6 : ℕ → ℕ → ℕ)
    (hMP : ∀ a, RchPub (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
        (D.at frS.P.T.a).key₁ 0).E.Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Pp 342 a →
      onQ hA.𝔇.N (honest (mgAll hA.𝔇 mgBase) ans test) linksFull (flatPlacesOf linksFull true) (fun a => a) 342 a →
      a.1.2.failed = none → ∀ aK, K9.segAt? a.1.2 = some aK →
      MatsSeated (fun μ _ => μ = (P5J.At.X Zp).hS.NHf + 2) hA.𝔇.arr hA.𝔇.N (P5J.At.X Zp)
        (hA.𝔇.N.sent 24 0) aK num6 (P5J.At.layout Zp))
    (aN : ℕ) (R₁ R₂ R₃ : Rounds) {X : Stages.LinkH} {arrs : Option (List ℕ)}
    {x x' : ProofFile.InstPub × S} {y y' : Strs}
    {w : Wit (CellsQ OnBytes.Flat.numsFull.rows (P5J.colsAt OnBytes.Flat.numsFull)) P5J.At.Tok
      MsgT}
    {p : ℕ × String} {A B : K9.Part}
    (Fc : ReadsFenceB hA.𝔇 mgBase ans test
      (JReach (RchPub (Str := (Sound.frameAt (D.at frS.P.T.a) (Sound.allOf (D.at frS.P.T.a))
        (D.at frS.P.T.a).key₁ 0).E.Str) (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Pp) hA.𝔇.N (honest (mgAll hA.𝔇 mgBase) ans test)) Zp Bs aN R₁ R₂ R₃ cF 24 X arrs x x' y y' w p A B) :
    PlanesLeft6 (P5J.At.X Zp) (hA.𝔇.N.sent 24 0) x.2 A hA.𝔇.arr hA.𝔇.N num6
      (P5J.At.layout Zp) := by
  obtain ⟨a, hr, hon, hm, e⟩ := at342_of_fence_b hA dk Pp Fc.inAt Fc.inv
  have hseg : K9.segAt? a.1.2 = some A := by rw [e]; exact Fc.front
  refine ⟨?_, (partLive_at_rch hA 342 a hr.1 hm A hseg).2, hMP a hr hon hm A hseg⟩
  rw [← e]
  exact look_at_342 hA a hr.1

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.linkNo_in_fence_b
#print axioms VerifiableInference.Desc.K1.at342_of_fence_b
#print axioms VerifiableInference.Desc.K1.planesLeft6_atAll_b
