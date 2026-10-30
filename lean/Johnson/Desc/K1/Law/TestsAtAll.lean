-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/TestsAtAll.lean: SIXTEEN PREMISES OF THE LAW ON THE SUB-PROTOCOL K1, AT THE
CLOSED CONSTANT (the composed meaning's letters `hA.𝔇`, Johnson/P5J/MgAtAll.lean), each in
the premise's own type at Dm := hA.𝔇 · Z := Zp · c := cF · seats := `P5J.At.seats Zp` · the data :=
`D.at frS.P.T.a`: calls of TestsAtCounts.lean, TestsAtScope.lean and TestsAtThree.lean (this
folder). Statements with their proofs; nothing is evaluated.

THE PREMISES:
  hA    the one head (`P5J.AtMgA` at the second hash function)
  O     the maker's opening at the letters Bs and base₀, which the premises' types read
  hP1   `madePinnedAt … = true` (Johnson/Desc/Ok/PlanWritten/MadeTest.lean): sizes, lists of rounds
        and sendings are the written ones
  hP2   `cutIs (F0T …) = true` (Johnson/Desc/Ok/PlanWritten/CutTest.lean): the cut of the three
        chains into sub-protocols is the written one
hP1 and hP2 are tests with code on public data. That "the value is laid" gives both accepts is
pins_of_laid (Johnson/Goal/Skeleton/PinsOfLaid.lean) with cutIs_of_laid (CutIsOfLaid.lean beside
it): not called here.

  `laidP_atAll`      the value is laid, off the head
  `atAll_N`          the constant's numbers are the core off the public part's own list of rounds,
                     closed over the first chain's sub-protocols (`P5J.At.N_atBlocks`, in scope)
  `atAll_letters`    under hP1: that core is `N0Full`; the seats are `seatsFull`; hc; hs; hDsh
  `atAll_counts`     under hP2: `CountsAre (toldOf cF.blocksInOrder)`
  under hA alone: `hRows_atAll` · `hDlk_atAll` · `hsmp_atAll`
  under hA, O: `hOk_atAll` · `hBook_atAll`
  under hA, O, hP1: `hc_atAll` · `hs_atAll` · `hDsh_atAll` · `hNd_atAll`
  under all four: `hFence_atAll` · `hSent_atAll` · `hP1_atAll` · `hSeats_atAll` · `hidx_atAll` ·
    `hAtA_atAll` · `hPlan3_atAll` (at every dk with the written layout and shapes; `dk_atAll`: the
    data that are meant, `dkOf Zp`, are made and are such, with the first tree's number 0)

What is not claimed. That hP1 or hP2 accept at any files. No member of the head hA. hRows, hBook,
hDlk and hsmp are true by the make of the constant: proved (general), no example. Nothing on
soundness.

-/
import Johnson.Desc.K1.Law.TestsAtThree
import Johnson.P5J.MgAtAll
import Johnson.P5J.FourAtMg
import Johnson.Desc.Ok.PlanWritten.CutTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params Johnson.G
open OnBytes.Maker (WholeD)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.Sound (linksFull toldBy smpNamed)
open VerifiableInference.Desc.First (S ModelPart Numbers flatPlacesOf)
open VerifiableInference.Desc.K13.Law (openAt CountsAre seatsFull LFull MFull)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.PlanWritten (madePinnedAt cutIs cutIs_eq)
open _root_.Desc.K14.Law (seatZ secondAt)
open P5T (N0Full)
open ProofFile (Cl)
open IM (Open k1Ix)

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}

/-- The value is laid, off the head. -/
theorem laidP_atAll (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀) :
    LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL = .ok (D, r₀) :=
  hA.laid.run ▸ LPFD.Full.laidPOf_of hA.laid.value hA.laid.planOk hA.laid.data hA.laid.asks

/-- The constant's numbers, closed over the first chain's own sub-protocols. -/
theorem atAll_N (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (O : Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    hA.𝔇.N = (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).atBlocks (P5J.At.shape Zp) P5J.At.links
      cF.blocksInOrder :=
  P5J.At.N_atBlocks Zp cF (LPFK9.blockPlaces_full hA.scope hA.reads O)

/-- Under hP1: the five equations. -/
theorem atAll_letters (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (O : Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    hA.𝔇.N = N0Full.atBlocks (P5J.At.shape Zp) P5J.At.links cF.blocksInOrder ∧
      P5J.At.seats Zp = seatsFull ∧ Bs.G₀.first.codes = codesFull2 ∧
      Bs.G₀.first.shape = shapeFull ∧ hA.𝔇.shape = shapeFull := by
  obtain ⟨e1, e2, _, e4, e5⟩ := letters_in_scope hA.scope O hP1 (laidP_atAll hA)
  refine ⟨by rw [atAll_N hA O, e1], e2, e4, e5, ?_⟩
  show Zp.first.shape = shapeFull
  rw [← O.first]
  exact e5

/-- Under hP2: the written counts. -/
theorem atAll_counts (hP2 : cutIs (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true) :
    CountsAre (First.toldOf cF.blocksInOrder) :=
  countsAre_of_cut (bs := cF.blocksInOrder) (cutIs_eq hP2).1

/-! ## By the make of the constant -/

theorem hRows_atAll (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀) :
    First.eachOnce ((List.range 26).map fun m => (hA.𝔇.N.groupAt m, 0)) = true :=
  groupsOnce_id

theorem hDlk_atAll (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀) :
    hA.𝔇.links = linksFull := rfl

theorem hsmp_atAll (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀) :
    hA.𝔇.smp = smpNamed hA.𝔇.cs (P5J.At.seats Zp) := rfl

/-! ## Under the opening -/

variable (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
  (O : Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
include hA O

theorem hOk_atAll : ∀ b ∈ cF.blocksInOrder, b.planOk = true ∧ b.shaped = true :=
  hOk_of_planOk O hA.laid.planOk

theorem hBook_atAll :
    First.bookFit hA.𝔇.N (flatPlacesOf linksFull true) (toldBy cF.blocksInOrder) = true :=
  hBook_at hA.scope hA.reads O (atAll_N hA O)

/-! ## Under hP1 -/

variable (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
include hP1

theorem hc_atAll : Bs.G₀.first.codes = codesFull2 := (atAll_letters hA O hP1).2.2.1

theorem hs_atAll : Bs.G₀.first.shape = shapeFull := (atAll_letters hA O hP1).2.2.2.1

theorem hDsh_atAll : hA.𝔇.shape = shapeFull := (atAll_letters hA O hP1).2.2.2.2

theorem hNd_atAll : (P5J.At.seats Zp).Nodup := hNd_at (atAll_letters hA O hP1).2.1

/-- The data that are meant are made; their first tree is number 0. -/
theorem dk_atAll : dkOf Zp = some ⟨0, LFull, MFull⟩ := by
  have e : (gpOf Zp).firstTree = 0 :=
    congrArg (·.firstTree) (K13.Law.gpOf_in_scope hA.scope hA.laid.pub hP1)
  rw [dkOf_written (PlanWritten.Joined.sends_in_scope hA.scope hA.laid.pub hP1), e]

/-! ## Under hP1 and hP2 -/

variable (hP2 : cutIs (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true)
include hP2

theorem hFence_atAll : First.fenceFit hA.𝔇.N linksFull (flatPlacesOf linksFull true) = true :=
  hFence_at hA.scope hA.reads O (atAll_letters hA O hP1).1 (atAll_counts hP2)

theorem hSent_atAll : ∀ l, l < 25 → ∀ d : Bool,
    sentAtB hA.𝔇.N (toldBy cF.blocksInOrder) (noL l d) l (momL d) = true :=
  hSent_at hA.scope hA.reads O (fun b hb => (hOk_atAll hA O b hb).1) (hc_atAll hA O hP1)
    (hs_atAll hA O hP1) (atAll_letters hA O hP1).1 (atAll_counts hP2)

theorem hP1_atAll : ∀ l, l < 25 → laterSeatsB hA.𝔇.N (parL Zp Bs.G₀ l false) l 1
    (hA.𝔇.N.treesAt (flatPlacesOf linksFull true)[14 * l + k1Ix l false + 2]?) = true :=
  hP1_at hA.scope hA.reads O (hc_atAll hA O hP1) (hs_atAll hA O hP1) (atAll_letters hA O hP1).1
    (atAll_counts hP2)

theorem hSeats_atAll : ∀ l, l < 25 → ∀ d : Bool,
    ∀ j : Fin (shapesOf (parL Zp Bs.G₀ l d)).length,
      (P5J.At.seats Zp)[hA.𝔇.N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + j.val]? =
        some (seatOfMsg (parL Zp Bs.G₀ l d) (baseD (D.at frS.P.T.a) cF l d) j.val) := by
  have hD : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).data "proof file" = .ok (D.at frS.P.T.a) := by
    rw [P5J.LaidAt.atDepth hA.scope hA.laid]
    exact hA.laid.data
  obtain ⟨⟨b₁, l₁, q₁⟩, ⟨b₂, l₂, q₂⟩, ⟨b₃, l₃, q₃⟩⟩ := P5J.LaidAt.heads OnBytes.secondHashFunction Zp Np cF
  exact hSeats_atThree hA.scope hA.reads O hD hA.laid.planOk q₁ q₂ q₃ (hc_atAll hA O hP1)
    (hs_atAll hA O hP1) (hOk_atAll hA O) (atAll_letters hA O hP1).1 (atAll_counts hP2)
    (atAll_letters hA O hP1).2.1

theorem hidx_atAll : ∀ l, l < 25 → ∀ d : Bool,
    ∀ u ∈ First.sampledIn hA.𝔇.N (openAt linksFull (flatPlacesOf linksFull true) (noL l d)),
      (P5J.At.seats Zp).idxOf u < hA.𝔇.N.msgsAt (flatPlacesOf linksFull true)[noL l d]? :=
  hidx_at hA.scope hA.reads O (atAll_letters hA O hP1).1 (atAll_counts hP2)
    (atAll_letters hA O hP1).2.1

theorem hAtA_atAll : ∀ l, l < 25 → aheadAtB hA.𝔇.shape (hA.𝔇.N.sent l) (parL Zp Bs.G₀ l true) l
    (hA.𝔇.pubD.dS1.own l).size
    (hA.𝔇.N.treesAt (flatPlacesOf linksFull true)[noL l true]?) = true :=
  hAtA_at hA.𝔇 hA.scope hA.reads O (hc_atAll hA O hP1) (hs_atAll hA O hP1) (hDsh_atAll hA O hP1)
    (atAll_letters hA O hP1).1 (atAll_counts hP2)

theorem hPlan3_atAll {dk : K12Data} (hL : dk.L = LFull) (hM : dk.M = MFull) :
    planThreeB dk hA.𝔇.N Zp Bs.G₀ = true :=
  hPlan3_at hA.scope hA.reads O (hc_atAll hA O hP1) (hs_atAll hA O hP1)
    (atAll_letters hA O hP1).1 (atAll_counts hP2) hL hM

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.laidP_atAll
#print axioms VerifiableInference.Desc.K1.atAll_N
#print axioms VerifiableInference.Desc.K1.atAll_letters
#print axioms VerifiableInference.Desc.K1.atAll_counts
#print axioms VerifiableInference.Desc.K1.hRows_atAll
#print axioms VerifiableInference.Desc.K1.hDlk_atAll
#print axioms VerifiableInference.Desc.K1.hsmp_atAll
#print axioms VerifiableInference.Desc.K1.hOk_atAll
#print axioms VerifiableInference.Desc.K1.hBook_atAll
#print axioms VerifiableInference.Desc.K1.hc_atAll
#print axioms VerifiableInference.Desc.K1.hs_atAll
#print axioms VerifiableInference.Desc.K1.hDsh_atAll
#print axioms VerifiableInference.Desc.K1.hNd_atAll
#print axioms VerifiableInference.Desc.K1.dk_atAll
#print axioms VerifiableInference.Desc.K1.hFence_atAll
#print axioms VerifiableInference.Desc.K1.hSent_atAll
#print axioms VerifiableInference.Desc.K1.hP1_atAll
#print axioms VerifiableInference.Desc.K1.hSeats_atAll
#print axioms VerifiableInference.Desc.K1.hidx_atAll
#print axioms VerifiableInference.Desc.K1.hAtA_atAll
#print axioms VerifiableInference.Desc.K1.hPlan3_atAll
