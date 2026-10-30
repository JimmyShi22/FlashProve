-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/TheLastLinePaid.lean: THE FOUR PREMISES THAT STAND BESIDE THE OBJECT IN `yes_at_any_sides` (AtFullSide/Honest/TheOneObjectLastLine.lean) ARE PAID: the field yes of the online debts, at the sides that
completeness is stated with, from the maker's return and a value of AtFullSide/Honest/TheOneObject.lean, with nothing else beside them but the policy's test on the public files.

`yes_at_any_sides` takes beside the object: h₀ (the description's first test accepts one written instance), Q (`PlainAt`: six clauses on the description and the rows' prover), hk (the committer's key is the prover's)
and hcols (the committer's columns are the prover's stored words at every tied request). Each is a theorem at these letters. Here they are handed in: so that Lean says that they are the called law's own premises.

  `closingPlain_at_any_sides`      Q at ANY sides whose prover is the online return's: of the sides `PlainAt` reads the running prover alone
  **`yes_of_theOneObject_paid`**     the statement, at the sides of TheOneObject.lean
  **`yes_at_any_sides_paid`**        the same at any sides that fit

By: `closingStart_of_theOneObject`, `closingPlain_of_theOneObject` (AtFullSide/Honest/ClosingPlainAndStart.lean); `crossing_columns_all` (AtFullSide/Honest/CrossingPremises.lean); `key_of_atPure`
(Johnson/Desc/ProofFile/Honest/ThruAtPure.lean); `running_prover_reads_no_sides`, `theSides_fit`, `yes_at_any_sides` (TheOneObjectLastLine.lean).

Limits. Implications: no value of the object is made here; each of its fields is a hypothesis. The table's randomness, the out-of-domain seed and the prover's coin at which `ready` is shown to return once are letters: one
value of each is asked. The head, the return of the maker and the policy's test are premises. No property is claimed.
-/
import AtFullSide.Honest.TheOneObjectLastLine
import AtFullSide.Honest.ClosingPlainAndStart

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput matrixFilling tableCoins)
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm AtPublicFiles.Committed
open VerifierAndGoals (PublicFiles readFiles InScope asDescriptionFiles)
open LPFD.Full (instanceAsPlainRecord)
open FlashProve (protocolDataWellFormed allZeroDigest committerCoinCountLessOne)

local instance (priority := high) nonemptyPadZ_theLastLinePaid : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

local instance (priority := high) nonemptyRunValue_theLastLinePaid : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_theLastLinePaid : Inhabited RunValue := ⟨fun _ => 0⟩

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {h : HeadAtReturn Z A} {pp : Inst.Model.ScalesAndPolicy}
  {hr : readFiles Z = .ok pp}

/-- **The six clauses at any sides whose prover is the online return's.** -/
theorem closingPlain_at_any_sides {G : OnlineSides (onlineReturn Z A) h.places h.firstChain}
    (hG : G.prover (onlineReturn Z A).H = (onlineReturn Z A).H)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) (O : TheOneObject h hr)
    (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (c : CoinG A.B RunValue RunValue) :
    PlainAt Z (onlineReturn Z A).Z h.places h.firstChain (onlineReturn Z A).B G
      (A.H.thru id (tableCoins Z) matrixInput.dummy) := by
  have Q := closingPlain_of_theOneObject made O r e c
  have eP : provG Z (onlineReturn Z A).Z h.places h.firstChain (onlineReturn Z A).B G
      (A.H.thru id (tableCoins Z) matrixInput.dummy) =
      provG Z (onlineReturn Z A).Z h.places h.firstChain (onlineReturn Z A).B (theSides h)
        (A.H.thru id (tableCoins Z) matrixInput.dummy) := running_prover_reads_no_sides hG
  exact ⟨Q.plainSeal, by rw [eP]; exact Q.halved, by rw [eP]; exact Q.rooted, Q.nonZero, Q.width, by
    rw [eP]
    exact Q.ready₁⟩

/-- **The field yes of the online debts, at any sides that fit, from the maker's return and a value of the object.** -/
theorem yes_at_any_sides_paid {G : OnlineSides (onlineReturn Z A) h.places h.firstChain} (F : SidesFit h G)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (O : TheOneObject h hr) (r : (protocolAtFiles Z).EncodingRandomness) (e : (protocolAtFiles Z).OutOfDomainSeed) (c : CoinG A.B RunValue RunValue) :
    YesZ allZeroDigest [] Z (onlineReturn Z A).Z h.places h.firstChain runValueBytes runValueBytes (onlineReturn Z A).B G
      (onlineReturn Z A).H (TiedRequestAt h hr G) :=
  yes_at_any_sides F h.head.scope live made O (closingStart_of_theOneObject made O r e c)
    (closingPlain_at_any_sides F.prover made O r e c) (key_of_atPure made).symm
    (fun _ w _ _ => crossing_columns_all h made w.1 w.2.1)

/-- **The same at the sides that completeness is stated with.** -/
theorem yes_of_theOneObject_paid (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) (O : TheOneObject h hr) (r : (protocolAtFiles Z).EncodingRandomness)
    (e : (protocolAtFiles Z).OutOfDomainSeed) (c : CoinG A.B RunValue RunValue) :
    YesZ allZeroDigest [] Z (onlineReturn Z A).Z h.places h.firstChain runValueBytes runValueBytes (onlineReturn Z A).B
      (theSides h) (onlineReturn Z A).H (TiedRequestAt h hr (theSides h)) :=
  yes_at_any_sides theSides_fit h.head.scope live made O (closingStart_of_theOneObject made O r e c)
    (closingPlain_of_theOneObject made O r e c) (key_of_atPure made).symm
    (fun _ w _ _ => crossing_columns_all h made w.1 w.2.1)

end AtFullSide.Honest

#print axioms AtFullSide.Honest.closingPlain_at_any_sides
#print axioms AtFullSide.Honest.yes_at_any_sides_paid
#print axioms AtFullSide.Honest.yes_of_theOneObject_paid
