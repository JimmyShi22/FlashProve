-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Top/ProofLaidOfLedgers.lean: THE MASTER LEDGER, THE PROOF FILE's SIDE: the ledgers of
    `pubPlain`, `onlineDescription`, the plan's words and the FOURTEEN entry tests LAID END TO END, OVER THE
    KEY FILE's SIDE's TWO RETURNS (hX · hm). IT PAYS NOTHING: it names what is owed, each premise
    under the name of the ledger that it comes from and under its own name there.
  `PubOwed` (6: PubPlainLedger.lean's u₂ … u₇) · `DescOwed` (7: Johnson/AtFull/Desc/Ledger.lean's
      `descPure_of_parts`: r₁ … r₇) · `PlanWordOwed` (9: Johnson/AtFull/ProofPlan/WrittenDesc.lean's
      `planWord_of_cut`, at the depth 32) · `RowsOwed` (9: Johnson/AtFull/ProofRows/Join14.lean's
      `Fourteen.laid_of_rows`, but its last binder).
    ASKED ONCE, WHERE TWO LEDGERS ASK ONE THING: the three cuts (`laid_of_rows`' c₁ c₂ c₃ are had
        from `planWord_of_cut`'s hC by `cutIs_eq`) · the depth (hd, at 32). PAID BY
        ANOTHER LEDGER's END: p₁ (`pubPlain_of_parts`) · hn (`planWord_of_cut`) · hW (the key file's
        side's hX) · hP (p₁: `pubPlain` IS `pureRoad.pub`).
  `ProofLetters`: every value that a step returns, as one structure of data (11 letters) ·
      `ProofLetters.Zq` (the public part) · `ProofLetters.F` (the description) · `ProofOwed`: the
      four ledgers at these letters: 31 premises.
  `ProofOwed.pub` · `ProofOwed.desc` · `ProofOwed.laid14` · **`proofLaid_of_ledgers14`**: hX · hm ·
      ProofOwed · row14 ⟹ `theProofLaid (asDescriptionFiles Z)` returns (the written data; the run of F).
  STATED OVER THE ENTRY TESTS' FOURTEEN ROWS (`LPFD.lawsAsk`, Johnson/Desc/Laid/ProofAsks.lean).
      The two theorems over `Fourteen.laid_of_rows` (`ProofOwed.laid14`, `proofLaid_of_ledgers14`)
      have, beside the ledgers, ONE PREMISE MORE: row14 : the
      fourteenth entry test `rowsMadeB` accepts at the public part.
A SEAM, CLOSED HERE: `theProofLaid (asDescriptionFiles Z)` unfolds to `LPFD.Full.proofDataAndDecisionOfPublicFiles secondHashFunction Z.pol Z.lay
    Z.KL`, a match on `onlineDescription`'s value with `proofDataAndDecisionOfDescription` behind it.
Not chained: `baseOf_of_parts` (its end is "there is Bs with these fields" , not a term): it is a
    payer of r₁, and r₂ … r₅ speak of the Bs that it gives.
Limits. No premise is shown to be met. No soundness follows.

-/
import Johnson.AtFull.Top.PubPlainLedger
import Johnson.AtFull.Desc.Ledger
import Johnson.AtFull.ProofPlan.WrittenDesc
import Johnson.AtFull.ProofRows.Join14

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Top
open ProofFile
open VerifiableInference VerifiableInference.PlanWritten
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Key (madeAt fixedDigest)
open Johnson.G Johnson.G.OfPlan VerifiableInference.Number
open VerifiableInference.Desc.First.Att.P (K5Asks.rowW)

/-- **What `pubPlain_of_parts` asks beyond hX and hm.** -/
structure PubOwed (m : Johnson.G.OfPlan.Made)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (told : List Root × List Root × List Root) (depth : Nat)
    (cuts : List VerifiableInference.Desc.First.Cut) (s₀ : S) : Prop where
  u₂ : m.p.chains.proof.first.codes.lengthsOk = true
  u₃ : Johnson.G.OfPlan.declPOf (ProofFile.Law.blankM m) = .ok D
  u₄ : toldOf (ProofFile.Law.blankM m) = .ok told
  u₅ : Johnson.G.OfPlan.depthOf (ProofFile.Law.blankM m) = .ok depth
  u₆ : VerifiableInference.Desc.First.cutOf m.p.chains.proof.first.given.rounds = some cuts
  u₇ : plainStarts.start (plainStarts.par m.p.chains.proof.first) m.p.chains.proof.first = some s₀

/-- **What `descPure_of_parts` asks beyond p₁.** -/
structure DescOwed (o : SecondHashFunctionArgument) (Z : Pub) (Bs : PureBase) (base : List (Block S Cl))
    (c : Chain S Cl) (A : SharedSeat) (B : SecondSeat) : Prop where
  r₁ : baseOf Z (pureSeat o Z) = .ok Bs
  r₂ : faultsAt (pureSeat o Z) Bs = []
  r₃ : lackingAt (pureSeat o Z) (partsAt (pureSeat o Z) Bs) = []
  r₄ : (partsAt (pureSeat o Z) Bs).base = .ok base
  r₅ : chainBy Z base (partsAt (pureSeat o Z) Bs).frames (partsAt (pureSeat o Z) Bs).road = .ok c
  r₆ : onlineSharedChain Z = some A
  r₇ : onlineLastChain Z = some B

/-- **What `planWord_of_cut` asks**, at the depth 32. -/
structure PlanWordOwed {Xi : Type} (F : FileDescription Xi)
    (R : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) : Prop where
  hW : (P2Law.ProofPlan.wOf cutFirstFull cutSharedFull cutSecondFull R 32).planOk = true
  hC : cutIs F = true
  hD : F.roundsDeclaredByBlocks = R
  hP : F.plans = R
  hd : F.tableDepth = 32
  b₁ : ∀ b ∈ F.first.blocksInOrder, b.planOk = true
  b₂ : ∀ b ∈ F.shared.blocksInOrder, b.planOk = true
  b₃ : ∀ b ∈ F.second.blocksInOrder, b.planOk = true
  hF : F.fileOk = true

/-- **What `laid_of_rows` asks beyond these.** -/
structure RowsOwed (W : OnBytes.Model.Verify.Public) (Zp : Pub) (F : FileDescription Inst) : Prop where
  hw : writtenOf "proof file" F.roundsDeclaredByBlocks = .ok dryProofFull
  att : ∀ k < 7, K5Asks.rowW k W = true
  m₁ : MadeWritten Zp.p.chains.made
  m₂ : FirstWritten Zp.first
  m₃ : Zp.made.proof = proofSendsFull
  m₄ : xShapeOf Zp.p.X = xShapeFull
  k₁ : Desc.K3Asks.digEntry Zp = true
  k₂ : Desc.K3Asks.readsEntry Zp = true
  k₃ : Desc.K3Asks.headEntry Zp = true

/-- **The proof file's side's letters.** Data: no condition. -/
structure ProofLetters where
  D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound
  told : List Root × List Root × List Root
  depth : Nat
  cuts : List VerifiableInference.Desc.First.Cut
  s₀ : S
  Bs : PureBase
  base : List (Block S Cl)
  c : Chain S Cl
  A : SharedSeat
  B : SecondSeat
  R : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound

namespace ProofLetters
variable (π : ProofLetters) (o : SecondHashFunctionArgument) (pol KL : ByteArray) (m : Johnson.G.OfPlan.Made)

/-- The public part. -/
def Zq : Pub := pubOfParts plainStarts pol KL (ProofFile.Law.blankM m) π.D π.told π.depth π.cuts π.s₀

/-- The proof file's description. -/
def F : FileDescription Inst :=
  fileDescBy o pureRoad.links (π.Zq pol KL m) π.A π.B (fun s => s) (startS (π.Zq pol KL m)) π.c

end ProofLetters

/-- **ALL THAT THE PROOF FILE's SIDE OWES beyond the key file's: four ledgers, 31 premises.** -/
structure ProofOwed (o : SecondHashFunctionArgument) (pol KL : ByteArray) (X₀ : OnBytes.Model.Verify.Public)
    (m : Johnson.G.OfPlan.Made) (π : ProofLetters) : Prop where
  pubSteps : PubOwed m π.D π.told π.depth π.cuts π.s₀
  descSteps : DescOwed o (π.Zq pol KL m) π.Bs π.base π.c π.A π.B
  planWord : PlanWordOwed (π.F o pol KL m) π.R
  rows : RowsOwed X₀ (π.Zq pol KL m) (π.F o pol KL m)

namespace ProofOwed
variable {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {X₀ : OnBytes.Model.Verify.Public}
  {m : Johnson.G.OfPlan.Made} {π : ProofLetters}

/-- p₁. -/
theorem pub (O : ProofOwed o pol KL X₀ m π) (hX : publicOfO o pol KL (some lay) = .ok X₀)
    (hm : madeAt X₀ lay fixedDigest = .ok m) : pubPlain o pol lay KL = .ok (π.Zq pol KL m) :=
  pubPlain_of_parts hX hm O.pubSteps.u₂ O.pubSteps.u₃ O.pubSteps.u₄ O.pubSteps.u₅ O.pubSteps.u₆
    O.pubSteps.u₇

/-- `onlineDescription` returns F. -/
theorem desc (O : ProofOwed o pol KL X₀ m π) (hX : publicOfO o pol KL (some lay) = .ok X₀)
    (hm : madeAt X₀ lay fixedDigest = .ok m) : onlineDescription o pol lay KL = .ok (π.F o pol KL m) :=
  Johnson.AtFull.Desc.descPure_of_parts (O.pub hX hm) O.descSteps.r₁ O.descSteps.r₂ O.descSteps.r₃
    O.descSteps.r₄ O.descSteps.r₅ O.descSteps.r₆ O.descSteps.r₇

end ProofOwed

/-- The seat's third step returns. -/
theorem ProofOwed.laid14 {o : SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public}
    {m : Johnson.G.OfPlan.Made} {π : ProofLetters} (O : ProofOwed o Z.pol Z.KL X₀ m π)
    (hZ : VerifierAndGoals.InScope Z = true) (hX : publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : madeAt X₀ Z.lay fixedDigest = .ok m)
    (row14 : VerifiableInference.Desc.LinkJoin.rowsMadeB (π.Zq Z.pol Z.KL m) = true) :
    LPFD.Full.proofDataAndDecisionOfDescription o Z.pol Z.lay Z.KL (π.F o Z.pol Z.KL m) =
      .ok (writtenPFull, LPFD.Full.proofDecisionOfDescription (π.F o Z.pol Z.KL m)) :=
  Johnson.AtFull.ProofRows.Fourteen.laid_of_rows hZ
    (P2Law.ProofPlan.planWord_of_cut O.planWord.hW O.planWord.hC O.planWord.hD O.planWord.hP
      O.planWord.hd O.planWord.b₁ O.planWord.b₂ O.planWord.b₃ O.planWord.hF)
    hX (O.pub hX hm) O.rows.hw O.planWord.hd O.rows.att O.rows.m₁ O.rows.m₂ O.rows.m₃ O.rows.m₄
    (cutIs_eq O.planWord.hC).1 (cutIs_eq O.planWord.hC).2.1 (cutIs_eq O.planWord.hC).2.2 O.rows.k₁
    O.rows.k₂ O.rows.k₃ row14

/-- **The proof file's maker returns, from the ledgers.** -/
theorem proofLaid_of_ledgers14 {Z : VerifierAndGoals.PublicFiles} {X₀ : OnBytes.Model.Verify.Public}
    {m : Johnson.G.OfPlan.Made} {π : ProofLetters} (hZ : VerifierAndGoals.InScope Z = true)
    (hX : publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : madeAt X₀ Z.lay fixedDigest = .ok m)
    (O : ProofOwed OnBytes.secondHashFunction Z.pol Z.KL X₀ m π)
    (row14 : VerifiableInference.Desc.LinkJoin.rowsMadeB (π.Zq Z.pol Z.KL m) = true) :
    FlashProve.theProofLaid (VerifierAndGoals.asDescriptionFiles Z) =
      .ok (writtenPFull, LPFD.Full.proofDecisionOfDescription (π.F OnBytes.secondHashFunction Z.pol Z.KL m)) := by
  show LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL = _
  unfold LPFD.Full.proofDataAndDecisionOfPublicFiles
  rw [O.desc hX hm]
  exact O.laid14 hZ hX hm row14

end AtFull.Top

#print axioms AtFull.Top.ProofOwed.pub
#print axioms AtFull.Top.ProofOwed.desc
#print axioms AtFull.Top.ProofOwed.laid14
#print axioms AtFull.Top.proofLaid_of_ledgers14
