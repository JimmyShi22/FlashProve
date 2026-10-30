-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/FiftyAtAll.lean: EIGHT MORE PREMISES OF THE LAW ON THE SUB-PROTOCOL K1 AT ITS
FIFTY LATER PLACES, AT THE CLOSED CONSTANT (`hA.𝔇`, Johnson/P5J/MgAtAll.lean), each in
the premise's own type: calls alone. Statements with their proofs; nothing is evaluated.

  `hreq_atAll` `hdig_atAll` `hhead_atAll`   three laws on a step of k01_kind_atThree
      (Johnson/Desc/AtSeats/K01KindAtThree.lean [not in this library]): the three letters through which
      the constraints'
      sentence reads the verifier's state go back over a yes of each of the fifty: calls of
      Johnson/Desc/AtSeats/ConstrLettersAtAll.lean (by the make of the constant's terms) and of
      `reply_later` (Johnson/Desc/AtSeats/ReplyLeft.lean). Under the head hA alone; at every ground,
      every data of the proximity test and every letter xb
  `hN_atAll` `hseats_atAll` `hCnt_atAll` `hLk_atAll` `hMk_atAll`   the five equations that
      k01_fifty_paid (Johnson/Desc/K1/Law/K01FiftyPaid.lean) asks in the place of the ten tests on
      the table's numbers and the list of seats: TestsAtAll.lean's (this folder), by name; the last
      two at the data that are meant (`dkOf Zp`)

What is not claimed. That hP1 or hP2 accept at any files. No member of the head hA. Nothing on
soundness.

-/
import Johnson.Desc.K1.Law.TestsAtAll
import Johnson.Desc.K1.Law.K01FiftyAtThree
import Johnson.Desc.AtSeats.ConstrLettersAtAll
import Johnson.Desc.AtSeats.ReplyLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params Johnson.G
open OnBytes.Maker (WholeD)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Sound (linksFull mgAll mgBase d13)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.Desc.First (S Item flatPlacesOf)
open VerifiableInference.Desc.K13.Law (openAt CountsAre seatsFull LFull MFull)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.PlanWritten (madePinnedAt cutIs)
open _root_.Desc.K14.Law (seatZ secondAt)
open P5T (N0Full)
open ProofFile (Cl)
open IM (Open)

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}

/-! ## Three laws on a step -/

theorem hreq_atAll (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀) (G₀ : ProofFile.Ground) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, G₀.built[l]? = some X → ∀ x x',
      YesOf (blkL Zp G₀ l d X arrs) x x' → hA.𝔇.H.req x' = hA.𝔇.H.req x :=
  fun _ _ _ _ _ _ x x' hy => HashBuild.req_atAll hA x x' hy.1

theorem hhead_atAll (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀) (G₀ : ProofFile.Ground)
    (dk : K12Data) (xb : S → Bool) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, G₀.built[l]? = some X → ∀ x x' y y' w p i,
      YesOf (blkL Zp G₀ l d X arrs) x x' →
      InAt hA.𝔇.N (mw1 hA.𝔇.N (d13 hA.𝔇) dk (mgAll hA.𝔇 mgBase) xb) linksFull
        (flatPlacesOf linksFull true) (noL l d) x y →
      KeptBelow (baseD (D.at frS.P.T.a) cF l d) y y' →
      Item.constr (headLink (P5J.At.X Zp)) p ∈
        openAt linksFull (flatPlacesOf linksFull true) (noL l d) →
      hA.𝔇.headPart p i x' y' w → hA.𝔇.headPart p i x y w :=
  fun l _ d X arrs _ x x' y y' w p i hy _ _ _ h0 =>
    HashBuild.head_atAll hA p i x x' y y' w hy.1 (reply_later Zp G₀ l d X arrs x x' hy) h0

theorem hdig_atAll (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀) (G₀ : ProofFile.Ground)
    (dk : K12Data) (xb : S → Bool) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, G₀.built[l]? = some X → ∀ x x' y y' w m,
      YesOf (blkL Zp G₀ l d X arrs) x x' →
      InAt hA.𝔇.N (mw1 hA.𝔇.N (d13 hA.𝔇) dk (mgAll hA.𝔇 mgBase) xb) linksFull
        (flatPlacesOf linksFull true) (noL l d) x y →
      KeptBelow (baseD (D.at frS.P.T.a) cF l d) y y' →
      Item.constr m .lookDigits ∈ openAt linksFull (flatPlacesOf linksFull true) (noL l d) →
      hA.𝔇.digitsPart m x' y' w → hA.𝔇.digitsPart m x y w :=
  fun _ _ _ _ _ _ x x' y y' w m _ _ _ _ h0 => HashBuild.dig_atAll hA m x x' y y' w h0

/-! ## The five equations -/

theorem hCnt_atAll (hP2 : cutIs (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true) :
    CountsAre (First.toldOf cF.blocksInOrder) := atAll_counts hP2

variable (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
  (O : Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
  (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
include hA O hP1

theorem hN_atAll : hA.𝔇.N = N0Full.atBlocks (P5J.At.shape Zp) P5J.At.links cF.blocksInOrder :=
  (atAll_letters hA O hP1).1

theorem hseats_atAll : P5J.At.seats Zp = seatsFull := (atAll_letters hA O hP1).2.1

theorem hLk_atAll {dk : K12Data} (h : dkOf Zp = some dk) : dk.L = LFull :=
  (dk_written (PlanWritten.Joined.sends_in_scope hA.scope hA.laid.pub hP1) h).1

theorem hMk_atAll {dk : K12Data} (h : dkOf Zp = some dk) : dk.M = MFull :=
  (dk_written (PlanWritten.Joined.sends_in_scope hA.scope hA.laid.pub hP1) h).2

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hreq_atAll
#print axioms VerifiableInference.Desc.K1.hhead_atAll
#print axioms VerifiableInference.Desc.K1.hdig_atAll
#print axioms VerifiableInference.Desc.K1.hCnt_atAll
#print axioms VerifiableInference.Desc.K1.hN_atAll
#print axioms VerifiableInference.Desc.K1.hseats_atAll
#print axioms VerifiableInference.Desc.K1.hLk_atAll
#print axioms VerifiableInference.Desc.K1.hMk_atAll
