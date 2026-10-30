-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/OpensPaid.lean: NO SOUNDNESS IS CLAIMED.
THE SLOT's OWN CONDITION IS A LETTER Oc (a variable behind ps): these laws spend of the promise its book-keeping alone (shapeAt_of_onL). For the tables' count at ocR (ocEnd ∧ «reached»). opens_paid_is_field stands in a file of its own (not in this library).
THE FIELD «opens» OF THE LAST CHAIN's LEDGER (Johnson/LLT25R/LastLedger.lean: LastRest.opens), at every Oc, at num := numAt D.t₁ D.t₂ 2 and no := ToldDesc.noAt D.t₁ D.t₂ n₁ ft nΩ, FROM ToldDesc.opens_field_numbers (Johnson/ToldDescR/OpensAtW.lean).
  **opens_paid**   the field's own sentence (its premise Promised is not spent).
  **opens_closed**   the same from THE TWO RUNNING TESTS ON THE PLAN: the data's yes at the ledger's own D and planOk pay five of opens_paid's eight (bookOk_of_planOk · k12_planOk_of_planOk · counts_of_data): LEFT ON THE PLAN THERE: ownMask = false · two stages at least · placesOfMade's yes.
LEFT, BY NAME (of opens_paid): ON THE STATES: hH: inside the promise at border 2, what was handed meets ToldDesc.HandedRoots n₁ ft nΩ (the first chain has received n₁ roots; in its book the tree at place j has the number ft + j; Omega's tree in the shared chain's book has the number nΩ). ON THE PLAN: the description's data's yes and treeSharingOk · its two counts of trees are D's · the block's test on the plan · ownMask = false · two stages at least · placesOfMade's yes.
The header (options, opens, letters) is LastLedger.lean's own, copied by program.
-/
import Johnson.LLT25R.LastLedger
import Johnson.LLT25R.LastNum
import Johnson.LLT25R.LastStretch
import Johnson.Desc.Sound.TakenBelowOfData
import Johnson.ToldDescR.OpensAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace LLT25
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Fo.Peel Cb
    Johnson.Pack
open Iop Prob _root_.Run
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn)
open VerifiableInference.Desc.Third (SharedOut)
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers openSets sampledIn start)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0)
open H2K.First (batOneOk)

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (A : SharedSeat) (N : H2U.Places4)
  (c : Chain S Cl) {Cells Tok P₀ : Type} (D : WholeD)
  (cs : OnBytes.Codes) {Xi' : Type} (G : FileDescription Xi') (arr : ℕ → ℕ → ℕ)
  (smp : (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) × (FL o mk Z A N
      c).S₃) → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o
      mk Z A N c).S₂) × (FL o mk Z A N c).S₃) → Option Cells)
  (c₀' : Cells) (dB : RDT) (dt : List RDT) (mine : List Mem)
  (get : (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ → P₀ × First.S)
  (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (smp₂ : (FL o mk Z A N c).S₂ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om
      i).Smp)
  (ms₁ ms₂ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
  (decT₂ : (ℕ → Option (ℕ × List UInt64)) → (FL o mk Z A N c).S₂ → Option Cells)
  (M₁ : Meaning P₀ (Wit Cells Tok MsgT)) (MS : MeaningS (FL o mk Z A N c).S₂ ((FL o mk Z A N
      c).XiPub × (FL o mk Z A N c).S₁) (Wit Cells Tok MsgT))
  (ML : MeaningL (FL o mk Z A N c).S₃ (Wit Cells Tok MsgT)) (stOf : (FL o mk Z A N c).S₂ →
      OnBytes.Statement)
  (bookOf : (FL o mk Z A N c).S₂ → OnBytes.TreeBook) (Pm₀ : PromMeaning (FL o mk Z A N c).S₂) (N₁ :
      Numbers) (Ns : NumbersS)
  (links : List ModelPart) (ps : List VerifiableInference.Desc.Place)
  (Oc : (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ → Strs → Prop)
  (hand : (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ → Option Handed) (ended : (FL o mk Z A N
      c).S₂ → Option SharedOut)
  (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rd : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ)

/-- **The ledger's field «opens».** -/
theorem opens_paid {file : String} {D₀ : WholeD} (h : (FL o mk Z A N c).data file = .ok D₀)
    (hk : (FL o mk Z A N c).treeSharingOk = true)
    (hp : (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Unit).planOk = true)
    (e₁ : (FL o mk Z A N c).t₁ = D.t₁) (e₂ : (FL o mk Z A N c).t₂ = D.t₂)
    (ho : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.ownMask = false)
    (h2 : 2 ≤ (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.stages.length)
    (hNp : H2U.placesOfMade Z.made = .ok N) (n₁ ft nΩ : ℕ)
    (hH : ∀ a, (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber))
      (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G
      arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2
          N).rounds
      hand ended) Oc 2) a → ∀ f o',
      hand (a.1.1.1, a.1.1.2.1) = some f → ended a.1.1.2.2 = some o' →
      ToldDesc.HandedRoots n₁ ft nΩ f o') :
    ∀ a t, (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber))
      (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G
      arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2
          N).rounds
      hand ended) Oc 2) a → Promised cs
      G smp mine a.1 (strsOf (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) a.2) →
      enterOwn a.1.2 = .ok t → FirstOpens (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W)
      (VerifiableInference.Desc.numAt D.t₁ D.t₂ 2) (ToldDesc.noAt D.t₁ D.t₂ n₁ ft nΩ)
      (baseTwoAt (FL o mk Z A N c) D (c0 Z) (c1 N)) t :=
  fun a t ha _ he =>
    ToldDesc.opens_field_numbers _ _ _ _ (p14At Z) hand ended h hk _ hp
      (ToldDesc.seated_at o mk Z A N c) D.t₁ D.t₂ e₁ e₂ _ (by rw [baseTwo_pure]) ho h2
      (ToldDesc.first_at_W hNp) (c2 N).rounds rfl n₁ ft nΩ hH a t ha he

/-- The tests on the plan ask `treeSharingOk`. -/
theorem bookOk_of_planOk {Xi : Type} (F : FileDescription Xi) (h : F.planOk = true) : F.treeSharingOk = true := by
  unfold FileDescription.planOk FileDescription.planOkCore at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.2

/-- The tests on the plan ask the proximity test's own, at the place W. -/
theorem k12_planOk_of_planOk (hP : (FL o mk Z A N c).planOk = true) :
    (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Unit).planOk = true := by
  have hb := last_ok_of_planOk (FL o mk Z A N c) hP
  rw [last_flat_pure] at hb
  have hb' : ([c0 Z, c1 N, c2 N, c3 Z N].all fun b => b.planOk && b.shaped) = true := hb
  have h2 := List.all_eq_true.1 hb' (c2 N)
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have h3 : (c2 N).planOk = true := (Bool.and_eq_true_iff.1 h2).1
  have h4 : ((ToldDesc.ownAt N).planOk && (ToldDesc.ownAt N).claims.isEmpty) = true := h3
  have h5 : ((proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Unit).planOk &&
      (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Unit).claims.isEmpty &&
      (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Unit).after.isEmpty) = true :=
    (Bool.and_eq_true_iff.1 h4).1
  exact (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h5).1).1

/-- **The ledger's field «opens», from the two running tests on the plan**: the data's yes AT THE
LEDGER's OWN D and `planOk` pay five of the eight: the data's yes, `treeSharingOk`, the block's test, and
that the description's two counts of trees are D's (`counts_of_data`,
Johnson/Desc/Sound/TakenBelowOfData.lean). -/
theorem opens_closed {file : String} (hD : (FL o mk Z A N c).data file = .ok D)
    (hP : (FL o mk Z A N c).planOk = true)
    (ho : (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.ownMask = false)
    (h2 : 2 ≤ (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W).nums.stages.length)
    (hNp : H2U.placesOfMade Z.made = .ok N) (n₁ ft nΩ : ℕ)
    (hH : ∀ a, (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber))
      (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G
      arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2
          N).rounds
      hand ended) Oc 2) a → ∀ f o',
      hand (a.1.1.1, a.1.1.2.1) = some f → ended a.1.1.2.2 = some o' →
      ToldDesc.HandedRoots n₁ ft nΩ f o') :
    ∀ a t, (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber))
      (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G
      arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2
          N).rounds
      hand ended) Oc 2) a → Promised cs
      G smp mine a.1 (strsOf (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) a.2) →
      enterOwn a.1.2 = .ok t → FirstOpens (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W)
      (VerifiableInference.Desc.numAt D.t₁ D.t₂ 2) (ToldDesc.noAt D.t₁ D.t₂ n₁ ft nΩ)
      (baseTwoAt (FL o mk Z A N c) D (c0 Z) (c1 N)) t :=
  opens_paid o mk Z A N c D cs G arr smp mine get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂ M₁ MS
    stOf bookOf Pm₀ N₁ Ns Oc hand ended hD (bookOk_of_planOk _ hP)
    (k12_planOk_of_planOk o mk Z A N c hP) (counts_of_data hD).1.symm (counts_of_data hD).2.symm ho
    h2 hNp n₁ ft nΩ hH

end LLT25

#print axioms LLT25.bookOk_of_planOk
#print axioms LLT25.k12_planOk_of_planOk
#print axioms LLT25.opens_closed
#print axioms LLT25.opens_paid
