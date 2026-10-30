-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/Lookup/LookupRowAtTheGOfReturn.lean: AT THE BASE PROVER, AND AT THE TERM. The kind "lookup"
(K3): AT G AT THE DESCRIPTION THAT THE RETURN HOLDS (`AtPublicFiles.TheG.theGOfReturn made h T K`,
E2E/TheG.lean, of other authors): what the rule that yields `Owed` from the kinds asks of one kind,
by other authors' names, at the kind K3:
  `VerifiableInference.Compilation.KindPays G .K3`   (Johnson/T3/OwedOfKinds.lean)
  `Johnson.M1.KindBud G .K3`                   (Johnson/M1/BudGather.lean)
  `ProofFile.Honest.KindOnAtEveryRun Rel threads .K3`   (Johnson/Desc/ProofFile/Honest/Law/UseByKind.lean)
with `ProofFile.Honest.ListsOfTheKindBear G .K3 rows` (the same file): G's lists of the kind are the
lookups' lot's rows, in the first chain alone; and the other way: the rows are fifty, each is one of
G's lists and has a side at G's own falls. Eleven theorems.

  `noLookupSideInTheLaterChainsAtAnyFilling`   at whatever the maker returns, under the head: no
                                   side of the returned prover's shared or last chain is at a place
                                   of the kind K3
  `lookupKindBudWhereTheListsBear`, `lookupOnAtEveryRunWhereTheListsBear`   the two conditions of
                                   use, at any G whose lists of the kind are the lot's rows: bud and
                                   On are "true" at a lookup's row
  `lookupListsBearAtTheGAtBase` | `…AtTerm`    at `theGAtBase` | `theGAtTerm`
  `lookupRowAtTheGOfReturnAtBase` | `…AtTerm`  THE FIVE AT `theGOfReturn`
  `lookupOnAtEveryRunAtTheGOfReturnAtBase` | `…AtTerm`
  `lookupRowAtTheGOfReturnAtBaseInScope` | `…AtTermInScope`   the five FROM scope AND `protocolDataWellFormed`
                                   ALONE: the maker returns; a head is there; at every head, T and K
                                   that lays the lookups' lot

The premises of the others. `made`: the return of `baseMaker files` | `onlineMaker files`. h: a head
at that return. T: what the threads take from outside: a letter; that its type has a value is shown
in no file of the lookups. K, with `laid`: the lookups' lot is one of the lots that K lays (such a K
exists: LookupLotIsAmongTheKindsRows.lean).

How it crosses from `theGAtBase` | `theGAtTerm`: by `castSides_of` (E2E/TheSides.lean) at the
equation
`returned.F = h.description` (`atPure_at_laid`).

READ THE HEAD OF Johnson/Desc/ProofFile/Honest/K3/Term/LookupSimulatorAtTheHead.lean: exact in
`Good` is THE SPENDER'S HALF ALONE; fresh is TRUE AND EMPTY; On and bud are "true"; `Good` is at A
and B "false". G IS ONE TERM AT A LETTER: a function of K. Nothing here ties G at the base to G at
the term.

THE PROOF FILE'S FIFTY PLACES ALONE: the key file's two lookups are not spoken of.

Limits. As there. Nothing on any property of the protocol.
-/
import Johnson.M1.BudGather
import Johnson.Desc.ProofFile.Honest.Law.UseByKind
import Johnson.Desc.ProofFile.Honest.K7.AtFill
import E2E.Lookup.LookupKindPaysAtTheGInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.Lookup
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Term ProofFile.Honest.Term AtPublicFiles.AtFiles AtPublicFiles.Cut
open AtFullSide.Honest.K3 AtPublicFiles.TheSides AtPublicFiles.TheG
open ProofFile.Honest.FirstThread (HeadAtReturn)
open VerifiableInference.Desc (Chain FileDescription KindName)

section
variable {files : VerifierAndGoals.PublicFiles} {description : OnBytes.Maker.WholeD} {proofRun : LPFD.Full.RunPF}
  {publicPart : ProofFile.Pub} {places : H2U.Places4} {firstChain : Chain P5J.TS ProofFile.Cl}
  {lookPlace : VerifiableInference.Desc.First.Look.Place} {W₀ Rc Ky Tr X₀ X : Type}

/-- **No side of the returned prover's shared or last chain is at a place of the kind K3.** The
maker
refuses a side that is at no sub-protocol's place, and these two chains have no sub-protocol of the
kind. -/
theorem noLookupSideInTheLaterChainsAtAnyFilling
    (head : P5J.AtMgA OnBytes.secondHashFunction files description proofRun publicPart places firstChain
      lookPlace)
    {makersFilling : ProofFile.Honest.OnlineProverParts W₀ Rc Tr X₀ X} {returned : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL makersFilling = .ok returned) :
    (∀ side ∈ returned.H.shared, side.place.kind ≠ KindName.K3) ∧
      ∀ side ∈ returned.H.second, side.place.kind ≠ KindName.K3 := by
  obtain ⟨-, noStrayShared, noStraySecond⟩ := atPure_strays made
  have planPasses : returned.F.planOk = true := by
    rw [(atPure_at_laid head.laid made).2]
    exact head.laid.planOk
  obtain ⟨noneShared, noneSecond⟩ :=
    noLookupPlaceInTheLaterChains (atPure_ok made).2.2.1 planPasses
  refine ⟨fun side inShared ofKind => ?_, fun side inSecond ofKind => ?_⟩
  · obtain ⟨b, inChain, samePlace⟩ := side_on_chain noStrayShared inShared
    exact noneShared b inChain (by rw [samePlace]; exact ofKind)
  · obtain ⟨b, inChain, samePlace⟩ := side_on_chain noStraySecond inSecond
    exact noneSecond b inChain (by rw [samePlace]; exact ofKind)

variable {Fd : FileDescription Inst} {Bk : ProverCoinCounts} {G : Sides Fd Bk W₀ Rc Ky Tr X₀ X} {ground : Ground}

/-- **The kind's share of the clause on bud**, at any G whose lists of the kind are the lot's rows.
In
the shared and the last chain it holds for want of a list of the kind. -/
theorem lookupKindBudWhereTheListsBear (F : Pub → K3.Fill (Local W₀ Rc Inst Tr))
    (bear : ListsOfTheKindBear G KindName.K3 ((lookupSimulatorLot F).rows publicPart ground)) :
    Johnson.M1.KindBud G KindName.K3 :=
  ⟨fun L inFirst ofKind => Johnson.M1.budOwed_true Fd L
      (lookupSimulatorBudHolds F publicPart ground L.bare (bear.first L inFirst ofKind)),
    fun L inShared ofKind => absurd ofKind (bear.noneShared L inShared),
    fun L inSecond ofKind => absurd ofKind (bear.noneSecond L inSecond)⟩

/-- **The kind's share of "On at every run"**, at any G whose lists of the kind are the lot's rows.
-/
theorem lookupOnAtEveryRunWhereTheListsBear (F : Pub → K3.Fill (Local W₀ Rc Inst Tr))
    (bear : ListsOfTheKindBear G KindName.K3 ((lookupSimulatorLot F).rows publicPart ground))
    {H : Prover W₀ Rc Inst Ky Tr X₀ X} (Rel : W₀ → Rc → Inst → Prop)
    (threads : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R, ready Fd Bk (G.prover H) w₀ rc x k = .ok R →
      ThreadsP Fd Bk (G.prover H) w₀ rc x k R) :
    KindOnAtEveryRun (G := G) (H := H) Rel threads KindName.K3 :=
  fun w₀ rc x holds k R isReady ρ r _ _ _ =>
    kindOnAtRun_of_rows bear
      (fun L inRows => lookupSimulatorOnHolds F publicPart ground L.bare inRows)
      (threads w₀ rc x holds k R isReady) ρ r

end

variable {files : VerifierAndGoals.PublicFiles} {Wt : Type}

/-! ## 1 At the base prover -/

/-- **AT THE BASE: G's lists of the kind K3 are the lot's rows, in the first chain alone.** -/
theorem lookupListsBearAtTheGAtBase {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (made : baseMaker
                                     files = .ok returned)
    (h : HeadAtReturn files returned) (T : ThreadParts returned Wt)
    (K : KindRows (baseFilling files) returned.Z returned.G) (laid :
        lookupSimulatorLotAtTheBaseProver ∈ K.lots) :
    ListsOfTheKindBear (theGAtBase h T K) KindName.K3
      ((lookupSimulatorLotAtTheBaseProver).rows returned.Z returned.G) := by
  obtain ⟨-, -, -, -, -, -, -, -, sameShared, sameSecond, -⟩ := atPure_ok made
  obtain ⟨noneShared, noneSecond⟩ := noLookupSideInTheLaterChainsAtAnyFilling h.head made
  refine ⟨lookupListsOfTheGAtBaseAreTheLotsRows h T K (lookupLotIsAmongTheSlotsAtTheBaseProver files
      K laid), ?_, ?_⟩
  · intro L inShared
    obtain ⟨row, inRows, rfl⟩ := List.mem_map.1 inShared
    refine noneShared row.half ?_
    rw [sameShared, ← K.slots.shared_fit]
    exact List.mem_map_of_mem inRows
  · intro L inSecond
    obtain ⟨row, inRows, rfl⟩ := List.mem_map.1 inSecond
    refine noneSecond row.half ?_
    rw [sameSecond, ← K.slots.second_fit]
    exact List.mem_map_of_mem inRows

/-- **AT THE BASE, AT THE DESCRIPTION THAT THE RETURN HOLDS (`theGOfReturn`): TWO OF THE THREE
THINGS that
the rule that yields `Owed` from the kinds asks of the kind K3 (`KindPays`, `KindBud`; the third, On
at every
run, is the next theorem), and that they are asked of something.** exact in `KindPays` IS THE
SPENDER'S HALF ALONE. -/
theorem lookupRowAtTheGOfReturnAtBase {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (made : baseMaker
                                     files = .ok returned)
    (h : HeadAtReturn files returned) (T : ThreadParts returned Wt)
    (K : KindRows (baseFilling files) returned.Z returned.G) (laid :
        lookupSimulatorLotAtTheBaseProver ∈ K.lots) :
    VerifiableInference.Compilation.KindPays (theGOfReturn made h T K) KindName.K3 ∧
      Johnson.M1.KindBud (theGOfReturn made h T K) KindName.K3 ∧
      ListsOfTheKindBear (theGOfReturn made h T K) KindName.K3
        ((lookupSimulatorLotAtTheBaseProver).rows returned.Z returned.G) ∧
      ((lookupSimulatorLotAtTheBaseProver).rows returned.Z returned.G).length = 50 ∧
      ∀ row ∈ (lookupSimulatorLotAtTheBaseProver).rows returned.Z returned.G,
        ∃ L ∈ (theGOfReturn made h T K).first, L.bare = row ∧
          ∃ σ, L.side returned.F.first.blocksInOrder (theGOfReturn made h T K).falls₁ = some σ := by
  have ours := lookupLotIsAmongTheSlotsAtTheBaseProver files K laid
  have sameDescription := (atPure_at_laid h.head.laid made).2
  have bear : ListsOfTheKindBear (theGOfReturn made h T K) KindName.K3
      ((lookupSimulatorLotAtTheBaseProver).rows returned.Z returned.G) :=
    castSides_of (Q := fun _ G => ListsOfTheKindBear G KindName.K3
      ((lookupSimulatorLotAtTheBaseProver).rows returned.Z returned.G)) sameDescription
      (lookupListsBearAtTheGAtBase made h T K laid)
  exact ⟨castSides_of (Q := fun _ G => VerifiableInference.Compilation.KindPays G KindName.K3)
      sameDescription (lookupKindPaysAtTheGAtBase made h T K ours),
    lookupKindBudWhereTheListsBear (lookupFillingAtTheBaseProver) bear, bear,
    lookupSimulatorRowsAreFifty h.head (lookupFillingAtTheBaseProver) returned.G,
    castSides_of (Q := fun F₀ G => ∀ row ∈ (lookupSimulatorLotAtTheBaseProver).rows returned.Z
        returned.G,
      ∃ L ∈ G.first, L.bare = row ∧ ∃ σ, L.side F₀.first.blocksInOrder G.falls₁ = some σ) sameDescription
      (everyLookupRowIsLaidAndSeatedInTheGAtBase h T K ours)⟩

/-- **AT THE BASE: the kind's share of "On at every run" at that G**: at every relation, every
prover
beside the lists and every family of invariants. On is "true" at a lookup's row. -/
theorem lookupOnAtEveryRunAtTheGOfReturnAtBase {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : baseMaker files = .ok returned) (h : HeadAtReturn files returned)
    (T : ThreadParts returned Wt) (K : KindRows (baseFilling files) returned.Z returned.G)
    (laid : lookupSimulatorLotAtTheBaseProver ∈ K.lots)
    {H : Prover FullSizeMatrix IndexCommitterCoins Inst OnBytes.TableKey Cells Unit Unit}
    (Rel : FullSizeMatrix → IndexCommitterCoins → Inst → Prop)
    (threads : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready returned.F returned.B ((theGOfReturn made h T K).prover H) w₀ rc x k = .ok R →
      ThreadsP returned.F returned.B ((theGOfReturn made h T K).prover H) w₀ rc x k R) :
    KindOnAtEveryRun (G := theGOfReturn made h T K) (H := H) Rel threads KindName.K3 :=
  lookupOnAtEveryRunWhereTheListsBear (lookupFillingAtTheBaseProver)
    (lookupRowAtTheGOfReturnAtBase made h T K laid).2.2.1 Rel threads

/-- **AT THE BASE, FROM scope AND `protocolDataWellFormed` ALONE, AT `theGOfReturn`**: the maker returns; there is
a head at
the return; and at EVERY head there, every T and every K that lays the lookups' lot: the five of
`lookupRowAtTheGOfReturnAtBase`. -/
theorem lookupRowAtTheGOfReturnAtBaseInScope (files : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) :
    ∃ (returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) (made : baseMaker files = .ok returned),
      Nonempty (HeadAtReturn files returned) ∧
      ∀ (h : HeadAtReturn files returned) (Wt : Type) (T : ThreadParts returned Wt)
        (K : KindRows (baseFilling files) returned.Z returned.G),
        lookupSimulatorLotAtTheBaseProver ∈ K.lots →
          VerifiableInference.Compilation.KindPays (theGOfReturn made h T K) KindName.K3 ∧
          Johnson.M1.KindBud (theGOfReturn made h T K) KindName.K3 ∧
          ListsOfTheKindBear (theGOfReturn made h T K) KindName.K3
            ((lookupSimulatorLotAtTheBaseProver).rows returned.Z returned.G) ∧
          ((lookupSimulatorLotAtTheBaseProver).rows returned.Z returned.G).length = 50 ∧
          ∀ row ∈ (lookupSimulatorLotAtTheBaseProver).rows returned.Z returned.G,
            ∃ L ∈ (theGOfReturn made h T K).first, L.bare = row ∧
              ∃ σ, L.side returned.F.first.blocksInOrder (theGOfReturn made h T K).falls₁ = some σ := by
  obtain ⟨returned, made⟩ := ProofFile.Honest.K1.baseMaker_returns files scope live
  obtain ⟨someHead, -⟩ := ProofFile.Honest.K1.headAtReturn_baseMaker files scope live made
  exact ⟨returned, made, ⟨someHead⟩, fun h _ T K laid =>
    lookupRowAtTheGOfReturnAtBase made h T K laid⟩

/-! ## 2 At the term -/

/-- **AT THE TERM: G's lists of the kind K3 are the lot's rows, in the first chain alone.** -/
theorem lookupListsBearAtTheGAtTerm {returned : OnlineReturn files} (made : onlineMaker files = .ok
    returned)
    (h : HeadAtReturn files returned) (T : ThreadParts returned Wt)
    (K : KindRows (onlineFilling files) returned.Z returned.G) (laid : lookupSimulatorLotAtTheTerm
        files ∈ K.lots) :
    ListsOfTheKindBear (theGAtTerm h T K) KindName.K3
      ((lookupSimulatorLotAtTheTerm files).rows returned.Z returned.G) := by
  obtain ⟨-, -, -, -, -, -, -, -, sameShared, sameSecond, -⟩ := atPure_ok made
  obtain ⟨noneShared, noneSecond⟩ := noLookupSideInTheLaterChainsAtAnyFilling h.head made
  refine ⟨lookupListsOfTheGAtTermAreTheLotsRows h T K (lookupLotIsAmongTheSlotsAtTheTerm files K
      laid), ?_, ?_⟩
  · intro L inShared
    obtain ⟨row, inRows, rfl⟩ := List.mem_map.1 inShared
    refine noneShared row.half ?_
    rw [sameShared, ← K.slots.shared_fit]
    exact List.mem_map_of_mem inRows
  · intro L inSecond
    obtain ⟨row, inRows, rfl⟩ := List.mem_map.1 inSecond
    refine noneSecond row.half ?_
    rw [sameSecond, ← K.slots.second_fit]
    exact List.mem_map_of_mem inRows

/-- **AT THE TERM, AT THE DESCRIPTION THAT THE RETURN HOLDS (`theGOfReturn`): TWO OF THE THREE
THINGS that
the rule that yields `Owed` from the kinds asks of the kind K3 (`KindPays`, `KindBud`; the third, On
at every
run, is the next theorem), and that they are asked of something.** exact in `KindPays` IS THE
SPENDER'S HALF ALONE. -/
theorem lookupRowAtTheGOfReturnAtTerm {returned : OnlineReturn files} (made : onlineMaker files =
    .ok returned)
    (h : HeadAtReturn files returned) (T : ThreadParts returned Wt)
    (K : KindRows (onlineFilling files) returned.Z returned.G) (laid : lookupSimulatorLotAtTheTerm
        files ∈ K.lots) :
    VerifiableInference.Compilation.KindPays (theGOfReturn made h T K) KindName.K3 ∧
      Johnson.M1.KindBud (theGOfReturn made h T K) KindName.K3 ∧
      ListsOfTheKindBear (theGOfReturn made h T K) KindName.K3
        ((lookupSimulatorLotAtTheTerm files).rows returned.Z returned.G) ∧
      ((lookupSimulatorLotAtTheTerm files).rows returned.Z returned.G).length = 50 ∧
      ∀ row ∈ (lookupSimulatorLotAtTheTerm files).rows returned.Z returned.G,
        ∃ L ∈ (theGOfReturn made h T K).first, L.bare = row ∧
          ∃ σ, L.side returned.F.first.blocksInOrder (theGOfReturn made h T K).falls₁ = some σ := by
  have ours := lookupLotIsAmongTheSlotsAtTheTerm files K laid
  have sameDescription := (atPure_at_laid h.head.laid made).2
  have bear : ListsOfTheKindBear (theGOfReturn made h T K) KindName.K3
      ((lookupSimulatorLotAtTheTerm files).rows returned.Z returned.G) :=
    castSides_of (Q := fun _ G => ListsOfTheKindBear G KindName.K3
      ((lookupSimulatorLotAtTheTerm files).rows returned.Z returned.G)) sameDescription
      (lookupListsBearAtTheGAtTerm made h T K laid)
  exact ⟨castSides_of (Q := fun _ G => VerifiableInference.Compilation.KindPays G KindName.K3)
      sameDescription (lookupKindPaysAtTheGAtTerm made h T K ours),
    lookupKindBudWhereTheListsBear (lookupFillingAtTheTerm files) bear, bear,
    lookupSimulatorRowsAreFifty h.head (lookupFillingAtTheTerm files) returned.G,
    castSides_of (Q := fun F₀ G => ∀ row ∈ (lookupSimulatorLotAtTheTerm files).rows returned.Z
        returned.G,
      ∃ L ∈ G.first, L.bare = row ∧ ∃ σ, L.side F₀.first.blocksInOrder G.falls₁ = some σ) sameDescription
      (everyLookupRowIsLaidAndSeatedInTheGAtTerm h T K ours)⟩

/-- **AT THE TERM: the kind's share of "On at every run" at that G**: at every relation, every
prover
beside the lists and every family of invariants. On is "true" at a lookup's row. -/
theorem lookupOnAtEveryRunAtTheGOfReturnAtTerm {returned : OnlineReturn files}
    (made : onlineMaker files = .ok returned) (h : HeadAtReturn files returned)
    (T : ThreadParts returned Wt) (K : KindRows (onlineFilling files) returned.Z returned.G)
    (laid : lookupSimulatorLotAtTheTerm files ∈ K.lots)
    {H : Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness Inst OnBytes.TableKey Cells Unit Unit}
    (Rel : FullSizeMatrix → (protocolAtFiles files).EncodingRandomness → Inst → Prop)
    (threads : ∀ w₀ rc x, Rel w₀ rc x → ∀ k R,
      ready returned.F returned.B ((theGOfReturn made h T K).prover H) w₀ rc x k = .ok R →
      ThreadsP returned.F returned.B ((theGOfReturn made h T K).prover H) w₀ rc x k R) :
    KindOnAtEveryRun (G := theGOfReturn made h T K) (H := H) Rel threads KindName.K3 :=
  lookupOnAtEveryRunWhereTheListsBear (lookupFillingAtTheTerm files)
    (lookupRowAtTheGOfReturnAtTerm made h T K laid).2.2.1 Rel threads

/-- **AT THE TERM, FROM scope AND `protocolDataWellFormed` ALONE, AT `theGOfReturn`**: the maker returns; there is
a head at
the return; and at EVERY head there, every T and every K that lays the lookups' lot: the five of
`lookupRowAtTheGOfReturnAtTerm`. -/
theorem lookupRowAtTheGOfReturnAtTermInScope (files : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) :
    ∃ (returned : OnlineReturn files) (made : onlineMaker files = .ok returned),
      Nonempty (HeadAtReturn files returned) ∧
      ∀ (h : HeadAtReturn files returned) (Wt : Type) (T : ThreadParts returned Wt)
        (K : KindRows (onlineFilling files) returned.Z returned.G),
        lookupSimulatorLotAtTheTerm files ∈ K.lots →
          VerifiableInference.Compilation.KindPays (theGOfReturn made h T K) KindName.K3 ∧
          Johnson.M1.KindBud (theGOfReturn made h T K) KindName.K3 ∧
          ListsOfTheKindBear (theGOfReturn made h T K) KindName.K3
            ((lookupSimulatorLotAtTheTerm files).rows returned.Z returned.G) ∧
          ((lookupSimulatorLotAtTheTerm files).rows returned.Z returned.G).length = 50 ∧
          ∀ row ∈ (lookupSimulatorLotAtTheTerm files).rows returned.Z returned.G,
            ∃ L ∈ (theGOfReturn made h T K).first, L.bare = row ∧
              ∃ σ, L.side returned.F.first.blocksInOrder (theGOfReturn made h T K).falls₁ = some σ := by
  obtain ⟨pp, read⟩ := LPFPol.read_of_scope scope
  obtain ⟨returned, made⟩ := lookupSimulatorHandInIsNotEmptyAtTheTerm files scope read live
  obtain ⟨someHead, -⟩ := AtPublicFiles.AtFiles.HonestTerm.headAtReturn_online files scope live made
  exact ⟨returned, made, ⟨someHead⟩, fun h _ T K laid =>
    lookupRowAtTheGOfReturnAtTerm made h T K laid⟩

end AtPublicFiles.Lookup

#print axioms AtPublicFiles.Lookup.noLookupSideInTheLaterChainsAtAnyFilling
#print axioms AtPublicFiles.Lookup.lookupKindBudWhereTheListsBear
#print axioms AtPublicFiles.Lookup.lookupOnAtEveryRunWhereTheListsBear
#print axioms AtPublicFiles.Lookup.lookupListsBearAtTheGAtBase
#print axioms AtPublicFiles.Lookup.lookupRowAtTheGOfReturnAtBase
#print axioms AtPublicFiles.Lookup.lookupOnAtEveryRunAtTheGOfReturnAtBase
#print axioms AtPublicFiles.Lookup.lookupRowAtTheGOfReturnAtBaseInScope
#print axioms AtPublicFiles.Lookup.lookupListsBearAtTheGAtTerm
#print axioms AtPublicFiles.Lookup.lookupRowAtTheGOfReturnAtTerm
#print axioms AtPublicFiles.Lookup.lookupOnAtEveryRunAtTheGOfReturnAtTerm
#print axioms AtPublicFiles.Lookup.lookupRowAtTheGOfReturnAtTermInScope
