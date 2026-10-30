-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/Lookup/LookupLotIsAmongTheKindsRows.lean: AT THE BASE PROVER, AND AT THE TERM. The kind "lookup"
(K3): THE PREMISE `ours` OF LookupKindPaysAtTheG.lean ("the lookups' lot is one of the lots of
`K.slots`") CAN BE MET, at both fillings: it follows where the lookups' lot is one of the lots that
the kinds lay (`K.lots`), and a K that lays it exists. `K : AtPublicFiles.TheSides.KindRows`
(E2E/TheSides.lean, of other authors). Eleven theorems.

  `aKindsLotOfAFillingsNameIsAmongTheSlots`   general, no kind named: a lot of `K.lots` that bears
                                   the name of a lot of the filling is one of the lots of `K.slots`
                                   (these are found by name; no two of `K.lots` bear one name)
  `onlyTheSixthLotBearsTheLookupsName`   of the thirteen lots of the wide filling the sixth alone
                                   bears the name of the lookups' lot: an evaluation of thirteen
                                   names; BENT beside it, an evaluation of its own: at that name
                                   with one sign more none of the thirteen says yes;
                                   the like at the online prover's filling (a lot read through
                                   keeps its name); a small lemma on lists
  `lookupLotIsAmongTheSlotsAtTheBaseProver` | `…AtTheTerm`   our lot ∈ K.lots ⊢ our lot ∈
      K.slots.lots
  `kindRowsWithTheLookupsLotExistAtTheBaseProver` | `…AtTheTerm`   A WITNESS, no premise: at every
                                   public part and ground there is a K THAT LAYS the lookups' lot
                                   (`∈ K.lots`), so that its slots hold it: it lays that lot alone,
                                   and no row on the two other chains
  `lookupLotFitsTheKindsRowsAtTheBaseProver` | `…AtTheTerm`   FOR WHOEVER FILLS K: the fields
      `named` and
                                   `lots_fit` of `KindRows` at the lookups' lot. No premise

So at every return there is a K at which `lookupKindPaysAtTheGAtBase` and
`lookupKindPaysAtTheGAtTerm` speak: neither is empty for want of one. The first theorem names no
kind: if the authors of E2E/TheSides.lean lay the like there, this one gives way to theirs.

WHAT THE WITNESS IS NOT. In it the other twelve lots of the filling stand beside simulators that
tell nothing (`bareSlot`): it shows that `ours` can be met, not that a K with thirteen simulators
that simulate anything exists.

THE PROOF FILE'S FIFTY PLACES ALONE: the key file's two lookups are not spoken of.

Limits. Sentences on lists of lots and on names. Nothing on any property of the protocol.
-/
import E2E.TheSides
import E2E.Lookup.LookupSimulatorAtTheBaseProver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.Lookup
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Term ProofFile.Honest.Term AtPublicFiles.AtFiles AtPublicFiles.Cut
open AtPublicFiles.TheSides

section
variable {W₀ Rc Tr X₀ X : Type} {P : ProofFile.Honest.OnlineProverParts W₀ Rc Tr X₀ X} {publicPart : Pub}
  {ground : Ground}

/-- **A lot of `K.lots` that bears the name of a lot of the filling is one of the lots of
`K.slots`.**
No kind is named. -/
theorem aKindsLotOfAFillingsNameIsAmongTheSlots (K : KindRows P publicPart ground)
    (kindsLot : SLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)
    (among : kindsLot ∈ K.lots)
    (fillingsLot : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X)
    (inFilling : fillingsLot ∈ P.lots) (sameName : kindsLot.name = fillingsLot.name) :
    kindsLot ∈ K.slots.lots := by
  have found : overlayLot K.lots fillingsLot = kindsLot := by
    unfold overlayLot
    cases search : K.lots.find? fun s => s.name == fillingsLot.name with
    | none =>
      have notThere := List.find?_eq_none.1 search kindsLot among
      simp [sameName] at notThere
    | some s =>
      have inLots : s ∈ K.lots := List.mem_of_find?_eq_some search
      have itsName : s.name = fillingsLot.name := by simpa using List.find?_some search
      exact List.inj_on_of_nodup_map K.apart inLots among (itsName.trans sameName.symm)
  show kindsLot ∈ P.lots.map (overlayLot K.lots)
  exact List.mem_map.2 ⟨fillingsLot, inFilling, found⟩

end

/-- **Of the thirteen lots of the wide filling the sixth alone bears the lookups' lot's name.** An
evaluation of thirteen names. -/
theorem onlyTheSixthLotBearsTheLookupsName {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ((onlineProverPartsInUse I o S O).lots.map fun L => L.name == lotName) =
      [false, false, false, false, false, true, false, false, false, false, false, false,
        false] :=
  rfl

/-- BENT: an evaluation of its own: at the lookups' lot's name with one sign more, none of the
thirteen
says yes. -/
theorem noLotBearsTheLookupsNameBent {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ((onlineProverPartsInUse I o S O).lots.map fun L => L.name == lotName ++ "!") =
      [false, false, false, false, false, false, false, false, false, false, false, false,
        false] :=
  rfl

/-- In a list whose test says yes at the sixth place alone, an entry that passes is the sixth. -/
theorem theEntryAtTheOnlyTrueIsTheSixth {α : Type} (list : List α) (test : α → Bool)
    (written : list.map test =
      [false, false, false, false, false, true, false, false, false, false, false, false, false])
    (entry : α) (inList : entry ∈ list) (passes : test entry = true) :
    list[5]? = some entry := by
  obtain ⟨number, atNumber⟩ := List.getElem?_of_mem inList
  have tested : (list.map test)[number]? = some true := by
    rw [List.getElem?_map, atNumber]
    exact congrArg some passes
  rw [written] at tested
  match number, tested, atNumber with
  | 5, _, atFive => exact atFive
  | later + 6, testedLater, _ =>
    exact absurd (List.mem_of_getElem?
      (l := [false, false, false, false, false, false, false]) (i := later) testedLater)
      (by decide)

/-- The like of `onlyTheSixthLotBearsTheLookupsName` at the online prover's filling: a lot read
through
keeps its name. -/
theorem onlyTheSixthLotBearsTheLookupsNameAtTheTerm (files : VerifierAndGoals.PublicFiles) :
    ((onlineFilling files).lots.map fun L => L.name == lotName) =
      [false, false, false, false, false, true, false, false, false, false, false, false,
        false] := by
  show (((onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
      openHonest).lots.map
    (HLot.thru (Local.thru id (tableCoins files)) (Local.thru id (tableCoins files)))).map
      fun L => L.name == lotName) = _
  rw [List.map_map]
  exact onlyTheSixthLotBearsTheLookupsName matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
    openHonest

/-- **AT THE BASE PROVER: the lookups' lot is one of the lots of `K.slots` where it is one of those
that the kinds
lay.** -/
theorem lookupLotIsAmongTheSlotsAtTheBaseProver (files : VerifierAndGoals.PublicFiles) {publicPart : Pub} {ground :
            Ground}
    (K : KindRows (baseFilling files) publicPart ground) (among : lookupSimulatorLotAtTheBaseProver
        ∈ K.lots) :
    lookupSimulatorLotAtTheBaseProver ∈ K.slots.lots :=
  aKindsLotOfAFillingsNameIsAmongTheSlots K _ among (lookupSimulatorLotAtTheBaseProver).toHLot
    (List.mem_of_getElem? (lookupSimulatorLotIsTheSixthLotAtTheBaseProver files)) rfl

/-- **AT THE BASE PROVER: A WITNESS**: at every public part and ground there is a K that lays the
lookups' lot; so its slots hold it. No premise. -/
theorem kindRowsWithTheLookupsLotExistAtTheBaseProver (files : VerifierAndGoals.PublicFiles) (publicPart : Pub)
    (ground : Ground) :
    ∃ K : KindRows (baseFilling files) publicPart ground,
      lookupSimulatorLotAtTheBaseProver ∈ K.lots ∧ lookupSimulatorLotAtTheBaseProver ∈ K.slots.lots
          := by
  have sixth := lookupSimulatorLotIsTheSixthLotAtTheBaseProver files
  refine ⟨{ lots := [lookupSimulatorLotAtTheBaseProver]
            named := ?_, apart := List.nodup_singleton _, lots_fit := ?_
            shared := [], shared_named := fun _ inNone => nomatch inNone
            shared_apart := List.nodup_nil, shared_fit := fun _ _ _ found => nomatch found
            second := [], second_named := fun _ inNone => nomatch inNone
            second_apart := List.nodup_nil, second_fit := fun _ _ _ found => nomatch found }, ?_⟩
  · intro s isOurs
    obtain rfl := List.mem_singleton.1 isOurs
    exact List.any_eq_true.2 ⟨_, List.mem_of_getElem? sixth, beq_self_eq_true _⟩
  · intro L inFilling s found
    have isOurs : s = lookupSimulatorLotAtTheBaseProver := List.mem_singleton.1
        (List.mem_of_find?_eq_some found)
    have itsName : s.name = L.name := by simpa using List.find?_some found
    subst isOurs
    have isSixth := theEntryAtTheOnlyTrueIsTheSixth _ (fun M => M.name == lotName)
      (onlyTheSixthLotBearsTheLookupsName matrixInput OnBytes.secondHashFunction
        OnBytes.HonestTrace.Sz.ref openHonest) L inFilling
      (by simpa using itsName.symm)
    obtain rfl := Option.some.inj (isSixth.symm.trans sixth)
    rfl
  · exact ⟨List.mem_cons_self, lookupLotIsAmongTheSlotsAtTheBaseProver files _ List.mem_cons_self⟩

/-- **AT THE TERM: the lookups' lot is one of the lots of `K.slots` where it is one of those that
the kinds
lay.** -/
theorem lookupLotIsAmongTheSlotsAtTheTerm (files : VerifierAndGoals.PublicFiles) {publicPart : Pub} {ground : Ground}
    (K : KindRows (onlineFilling files) publicPart ground) (among : lookupSimulatorLotAtTheTerm
        files ∈ K.lots) :
    lookupSimulatorLotAtTheTerm files ∈ K.slots.lots :=
  aKindsLotOfAFillingsNameIsAmongTheSlots K _ among (lookupSimulatorLotAtTheTerm files).toHLot
    (List.mem_of_getElem? (lookupSimulatorLotIsTheSixthLotAtTheTerm files)) rfl

/-- **AT THE TERM: A WITNESS**: at every public part and ground there is a K that lays the
lookups' lot; so its slots hold it. No premise. -/
theorem kindRowsWithTheLookupsLotExistAtTheTerm (files : VerifierAndGoals.PublicFiles) (publicPart : Pub)
    (ground : Ground) :
    ∃ K : KindRows (onlineFilling files) publicPart ground,
      lookupSimulatorLotAtTheTerm files ∈ K.lots ∧ lookupSimulatorLotAtTheTerm files ∈ K.slots.lots
          := by
  have sixth := lookupSimulatorLotIsTheSixthLotAtTheTerm files
  refine ⟨{ lots := [lookupSimulatorLotAtTheTerm files]
            named := ?_, apart := List.nodup_singleton _, lots_fit := ?_
            shared := [], shared_named := fun _ inNone => nomatch inNone
            shared_apart := List.nodup_nil, shared_fit := fun _ _ _ found => nomatch found
            second := [], second_named := fun _ inNone => nomatch inNone
            second_apart := List.nodup_nil, second_fit := fun _ _ _ found => nomatch found }, ?_⟩
  · intro s isOurs
    obtain rfl := List.mem_singleton.1 isOurs
    exact List.any_eq_true.2 ⟨_, List.mem_of_getElem? sixth, beq_self_eq_true _⟩
  · intro L inFilling s found
    have isOurs : s = lookupSimulatorLotAtTheTerm files := List.mem_singleton.1
        (List.mem_of_find?_eq_some found)
    have itsName : s.name = L.name := by simpa using List.find?_some found
    subst isOurs
    have isSixth := theEntryAtTheOnlyTrueIsTheSixth _ (fun M => M.name == lotName)
      (onlyTheSixthLotBearsTheLookupsNameAtTheTerm files) L inFilling
      (by simpa using itsName.symm)
    obtain rfl := Option.some.inj (isSixth.symm.trans sixth)
    rfl
  · exact ⟨List.mem_cons_self, lookupLotIsAmongTheSlotsAtTheTerm files _ List.mem_cons_self⟩

/-- **AT THE BASE PROVER: what whoever fills K needs of the lookups' lot**: a lot of the filling
bears its name; and
its rows' sides are the sides of EVERY lot of the filling that bears its name (there is one: the
sixth).
These are the fields `named` and `lots_fit` of `KindRows` at this lot. No premise. -/
theorem lookupLotFitsTheKindsRowsAtTheBaseProver (files : VerifierAndGoals.PublicFiles) (publicPart : Pub)
    (ground : Ground) :
    (baseFilling files).lots.any (fun L => L.name == (lookupSimulatorLotAtTheBaseProver).name) =
        true ∧
      ∀ L ∈ (baseFilling files).lots, (lookupSimulatorLotAtTheBaseProver).name = L.name →
        ((lookupSimulatorLotAtTheBaseProver).rows publicPart ground).map (·.half) = L.halves
            publicPart ground := by
  have sixth := lookupSimulatorLotIsTheSixthLotAtTheBaseProver files
  refine ⟨List.any_eq_true.2 ⟨_, List.mem_of_getElem? sixth, beq_self_eq_true _⟩,
    fun L inFilling sameName => ?_⟩
  have isSixth := theEntryAtTheOnlyTrueIsTheSixth _ (fun M => M.name == lotName)
    (onlyTheSixthLotBearsTheLookupsName matrixInput OnBytes.secondHashFunction
      OnBytes.HonestTrace.Sz.ref openHonest) L inFilling
    (by simpa using sameName.symm)
  obtain rfl := Option.some.inj (isSixth.symm.trans sixth)
  rfl

/-- **AT THE TERM: what whoever fills K needs of the lookups' lot**: a lot of the filling bears its
name; and
its rows' sides are the sides of EVERY lot of the filling that bears its name (there is one: the
sixth).
These are the fields `named` and `lots_fit` of `KindRows` at this lot. No premise. -/
theorem lookupLotFitsTheKindsRowsAtTheTerm (files : VerifierAndGoals.PublicFiles) (publicPart : Pub)
    (ground : Ground) :
    (onlineFilling files).lots.any (fun L => L.name == (lookupSimulatorLotAtTheTerm files).name) =
        true ∧
      ∀ L ∈ (onlineFilling files).lots, (lookupSimulatorLotAtTheTerm files).name = L.name →
        ((lookupSimulatorLotAtTheTerm files).rows publicPart ground).map (·.half) = L.halves
            publicPart ground := by
  have sixth := lookupSimulatorLotIsTheSixthLotAtTheTerm files
  refine ⟨List.any_eq_true.2 ⟨_, List.mem_of_getElem? sixth, beq_self_eq_true _⟩,
    fun L inFilling sameName => ?_⟩
  have isSixth := theEntryAtTheOnlyTrueIsTheSixth _ (fun M => M.name == lotName)
    (onlyTheSixthLotBearsTheLookupsNameAtTheTerm files) L inFilling
    (by simpa using sameName.symm)
  obtain rfl := Option.some.inj (isSixth.symm.trans sixth)
  rfl

end AtPublicFiles.Lookup

#print axioms AtPublicFiles.Lookup.aKindsLotOfAFillingsNameIsAmongTheSlots
#print axioms AtPublicFiles.Lookup.onlyTheSixthLotBearsTheLookupsName
#print axioms AtPublicFiles.Lookup.noLotBearsTheLookupsNameBent
#print axioms AtPublicFiles.Lookup.theEntryAtTheOnlyTrueIsTheSixth
#print axioms AtPublicFiles.Lookup.onlyTheSixthLotBearsTheLookupsNameAtTheTerm
#print axioms AtPublicFiles.Lookup.lookupLotIsAmongTheSlotsAtTheBaseProver
#print axioms AtPublicFiles.Lookup.kindRowsWithTheLookupsLotExistAtTheBaseProver
#print axioms AtPublicFiles.Lookup.lookupLotIsAmongTheSlotsAtTheTerm
#print axioms AtPublicFiles.Lookup.kindRowsWithTheLookupsLotExistAtTheTerm
#print axioms AtPublicFiles.Lookup.lookupLotFitsTheKindsRowsAtTheBaseProver
#print axioms AtPublicFiles.Lookup.lookupLotFitsTheKindsRowsAtTheTerm
