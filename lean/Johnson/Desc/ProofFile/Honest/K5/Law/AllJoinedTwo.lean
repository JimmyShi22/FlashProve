-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AllJoinedTwo.lean: CONDITIONAL: ATTENTION's JOINED LAW WITHOUT
THE PREMISE "THE MAKER onlineProverFromPublicFiles RETURNS": in its stead the library's test on the head's public files
and the two binders of ReturnsLeftTwo.lean.

Why. `k5_owes_all_joined_nine` (RidesOnCs.lean) speaks at a letter A under hA: the maker returns A
at the head's three files and the filling widerFillAt. `atPure_returns_two` has that return from two
binders. Here the two theorems are joined, so that A stands in the end alone.

Main names:
  `ground_made_at_head`: under the head the ground is made: so hG is no debt: it names the ground,
    so that hLends and HQ can be typed in front of A.
  `k5_owes_all_joined_two`: there is an A that the maker returns, its ground is G, and at A's
    prover the joined law's end holds. In hA's stead: hl, book, range, and hG: G is the ground
    that is made of the head's public part. hLends and HQ are typed at G.

Which way it goes. hA is derived here from three binders under the head: the law is no worse than
RidesOnCs.lean's: whoever holds hA calls that one; this one asks less where the three are had.

Limits. IT MAY HOLD EMPTILY: each of the five parts of the end is an implication from the thread in
front, and that the thread holds at any run is proved nowhere; nothing proves that the premises can
be met together. An implication: none of its binders is proved here; those of RidesOnCs.lean stand
as they are, but for hA. THAT THE BOOK's MAKER RETURNS IS PROVED AT NO FILES. The head is a
hypothesis, and so is the library's test. The head and the library's test have a member together at
the library's written copy of the full-size public files (`AtFullSide.Top.headMember_zFull`,
AtFullSide/Top/HeadMemberAtFull.lean), which is tied to the package's files by no theorem. Else as
ReturnsLeftTwo.lean's and RidesOnCs.lean's. Through its imports the file stands above the files
under ThirdParty/ (lean/LIMITS.md, L15).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.RidesOnCs
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsLeftTwo
import Johnson.Desc.ProofFile.Honest.AtHeadGround

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block Place Strs Chain KindName)
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.Sound (MsgT)
open H2K5.Honest (K5KeepsM K5KeepsAt)
open ProofFile.Honest.FirstThread (Script WtF lettersHead b0Head k5_hsp_csHead)
open P5J (AtMgA TS CellsM)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {W₀ : Type} {I : WiderIn W₀} {o : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {Bk : ProverCoinCounts}
  (Q : Script Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ : Nat) (Vd : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) → Prop)
  (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (f : KindName → Place → TS → TS → Prop) (w : (Local W₀ IndexCommitterCoins ProofFile.Inst Cells))

include h in
/-- **Under the head the ground is made.** Conditional: h. -/
theorem ground_made_at_head : ∃ G, blankBy pureRoad.links Zp = some G := by
  obtain ⟨Bs, _, Op⟩ := h.laid.opened
  exact ⟨Bs.G₀, Op.blank⟩

/-- **ALL OF THE MEMBER's DEBTS AT THE PROVER THAT onlineProverFromPublicFiles RETURNS, WITHOUT THE PREMISE THAT IT
RETURNS.** Conditional: every premise stands, by name, in the file's head and in RidesOnCs.lean's.
-/
theorem k5_owes_all_joined_two {g : Nat} (hg : g < 12)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (book : ∀ k0 k1 k2 e p1 p2,
      Johnson.G.sendsOf Z.pol Z.lay Z.KL = .ok [k0, k1, k2, e, Zp.made.proof.1, p1, p2] →
        ∃ B, bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 p1 p2
          (mergesByName cF.blocksInOrder) = .ok B)
    (range : I.inRange I.dummy = true)
    {G : Ground} (hG : blankBy pureRoad.links Zp = some G)
    (hO : O.keyOf = keyOfK3)
    (hfix : ∀ b, b ≤ cF.blocksInOrder.length → ∀ j, j < treesTo cF.blocksInOrder b →
      Q.fixed (.own j) ≤ roundsTo cF.blocksInOrder b)
    (hf : f .K5 = K5KeepsAt (P5J.At.X Zp))
    (hLends : ∀ a, (P5J.At.X Zp).A[g]? = some a →
      lendsRow Bk 0 (seatOf keyOfK3 Zp G cF g a).place (k5Row (seatOf keyOfK3 Zp G cF g a)) =
        true)
    (HQ : ∀ a x₁, (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      K5ScriptQ h Q Vd (roundsTo cF.blocksInOrder (borderOf g)) x₁ a id (seatOf keyOfK3 Zp G cF g a)
        (OnBytes.Model.Forest.elems a.fs))
    (hH : Vd w → ∃ i, VerifiableInference.OnPublicFiles.Flat.Holds (Q.cells w) i) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (widerFillAt I o S O) = .ok A ∧ A.G = G ∧
      ((Plays (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd
            (ridersOf (csHead ν st R)) (kpBy f) w).thread
          (borderOf g) ∧
        Behind (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd
            (ridersOf (csHead ν st R)) (kpBy f) w).thread
          (borderOf g) ∧
        Exchange (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd
            (ridersOf (csHead ν st R)) (kpBy f) w).thread
          (borderOf g) ∧
        RidesPast (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd
            (ridersOf (csHead ν st R)) (kpBy f) w).thread
          (borderOf g)) ∧
        ∀ fall, Accepted (lettersHead h A.H Q test carryX item n₁ n₂ b0Head Vd
            (ridersOf (csHead ν st R)) (kpBy f) w).thread
          fall (borderOf g)) := by
  obtain ⟨A, hA, -, -⟩ := atPure_returns_two h hl I o S O book range
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid hG hA
  subst eG
  exact ⟨A, hA, rfl,
    k5_owes_all_joined_nine h Q test carryX item n₁ n₂ Vd ν st R f w hg hA hO hfix hf hLends HQ hH⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.ground_made_at_head
#print axioms ProofFile.Honest.K5.k5_owes_all_joined_two
