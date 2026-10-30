-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
WHAT IT IS FOR: (K-P2), TWO OF THE FIVE: `BehindS` AND `RidesPastS` (Honest/Thread/PaysS.lean) AT THE TWO BORDERS OF THE KEY
  FILE's FIRST THREAD AT WHICH A LOOKUP STANDS: NUMBERS 4 AND 10 OF THE NINETEEN. E2E/KeyPaidCells.lean pays both at the
  twelve sub-protocols of no kind and leaves these two out, because what a KIND's step keeps is a letter of the thread's
  filling (`KeyFill.kind₁`, E2E/KeyRest.lean). Here that letter gets its text at the lookups.

E2E/Lookup/Key/LookupBehindAndRidesPastAtTheKey.lean. Two definitions and five theorems with their proofs, with the lemmas
that these call. On the verifier's side alone: the thread's halves and tables are letters, no sender is read.

  `LookupKeeps s s'`                 WHAT THE LOOKUP's STEP KEEPS: s' is s with what was heard and the ledger behind the
                                     hearing laid (`lookupSeat.put`, Johnson/Desc/Key/Link.lean): every other field stays.
                                     The like of `LayerKeeps` (E2E/KeyKeepsEq.lean)
  `LookupsKeepByText filling`        THE PREMISE ON THE LETTER: at 4 and at 10 `kind₁` is `LookupKeeps`
  `lookupBordersAreFourAndTen`       in scope the thread's sub-protocols number 4 and 10 stand at `lookPlace 0` and
                                     `lookPlace 1`, and no other of the nineteen bears the kind K3
  `lookupStepKeepsAtTheKey`          behind a step of the thread at 4 or 10: `LookupKeeps`
  `lookupBehindAtTheKey`             **`BehindS` at 4 and 10**, at every letter "what is said"
  `lookupRidersReadNeitherHearingNorLedger`   an item that is open at 4 or 10 and neither shut nor owed there means the same at
                                     s and at s' wherever `LookupKeeps s s'`
  `lookupRidesPastAtTheKey`          **`RidesPastS` at 4 and 10**, at every letter "what is said"

By what. `lookupBordersAreFourAndTen`: `places_named` (E2E/KeyPlacesNamed.lean) says that the rows of the thread's list are
the literal list `fullFirst`, which is read at each number. `lookupStepKeepsAtTheKey`: the list's blocks 4 and 10 are the
lookups' by unfolding `firstChain`, under `hl_in_scope`; the text of `lookupKind`'s decision ends in the seat's `put`.
`lookupBehindAtTheKey`: `form_behind₁` (E2E/KeyBehind.lean) and that step. `lookupRidersReadNeitherHearingNorLedger`: what
is open at 4 or 10 and neither shut nor owed is of a plain sort, by evaluation of the table; `fwd_at` (E2E/KeyRides.lean)
carries such an item, because `put` turns nothing that the readers or, under `ReadsD`, the reading read.

NOT HERE. `PlaysS` and `AcceptedS` at 4 and 10 (the group that holds the key file's prover has them carried to the owned
row). `ExchangeS` at 4 and 10: the three items that the row owes (the forms "objects", the worths "planes" and "keys") with
the three pins: it reads the thread's script, which is a letter here; E2E/Lookup/Key/LookupExchangeOfTheNewItemsAtTheKey.lean
pays the three pins and leaves the three items.

CAN THE PREMISES HOLD TOGETHER AT THE STORED KEY FILE? `LookupsKeepByText`: a premise on a letter that whoever lays the
filling sets by writing `kind₁ := fun b => if b = 4 ∨ b = 10 then LookupKeeps else …`: it can be met at will, and it binds
nothing but these two borders' clause "keeps". A filling that exists lays `kind₁ := fun _ _ _ => True` (E2E/KeyStartsBare.lean):
there the premise fails, and `RidesPastS` at 4 and 10 cannot be had from this file. Whoever lays the offline prover's filling
must turn that letter at 4 and 10: the group that holds the key file's prover. `KeySourced` with `InScope`: `key_sourced`
(E2E/KeyPublic.lean) where the verifier's own test on the public files accepts; at the full files `key_sourced VerifierAndGoals.storedPublicFiles
theLive_zFull` with `VerifierAndGoals.inScope_full`, named here, not called by this file. `ReadsL`: `LettersOk.readsL` (E2E/KeyRest.lean)
under that file's premise, and without a premise at the library's `baseK` (`readsLK`, Johnson/RunOne/KeyFillSeed.lean). This
file shows no filling that carries `baseK` and that letter together. EACH STATEMENT HOLDS ALSO WHERE THE THREAD STANDS
AT NOTHING: that the thread stands at border 4 or 10 at any run is not shown here.

Limits. Nothing on a sender, on completeness as such, on soundness or on what a view shows.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import E2E.KeyPaidCells
import E2E.KeyPlacesNamed

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.Lookup.Key
open VerifiableInference.Desc (Block OpenedColumn KindName)
open VerifiableInference.Desc.Key (Xi FirstState Claim Source LaterPlaces lookupSeat)
open AtPublicFiles.KeyThread
open AtPublicFiles.KeyBook (lookPlace)
open ProofFile.Honest

/-! ## 1 What the lookup's step keeps -/

/-- **What the step of the key file's sub-protocol "lookup" keeps**: all of the state but what was heard and the ledger. -/
def LookupKeeps (s s' : FirstState) : Prop := ∃ heard ledger, s' = lookupSeat.put s heard ledger

/-- **The filling's letter for a kind's step is that text at the two lookups.** A premise on a letter. -/
def LookupsKeepByText {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec : Type} (filling : KeyFill Bk W₀ Rc Cells M Smp Rec) : Prop :=
  filling.kind₁ 4 = LookupKeeps ∧ filling.kind₁ 10 = LookupKeeps

/-- A value that `named` takes out of an `Option`, and what is behind it. -/
theorem namedReturnsItsValue {α β : Type} {name : String} {value : Option α}
    {rest : α → Except String β} {result : β}
    (returned : (VerifiableInference.Desc.named name value >>= rest) = .ok result) :
    ∃ a, value = some a ∧ rest a = .ok result := by
  cases value with
  | none =>
    have refused : (Except.error name : Except String β) = .ok result := returned
    cases refused
  | some a => exact ⟨a, rfl, returned⟩

/-- A test that `need` asks, and what is behind it. -/
theorem needPassesOn {β : Type} {name : String} {test : Bool} {rest : Unit → Except String β}
    {result : β} (returned : (VerifiableInference.Desc.need name test >>= rest) = .ok result) :
    rest () = .ok result := by
  cases test with
  | false =>
    have refused : (Except.error name : Except String β) = .ok result := returned
    cases refused
  | true => exact returned

/-- **Where the sub-protocol "lookup" accepts, it keeps all but the hearing and the ledger**: at
every list of tests and every place, off the text of its decision. -/
theorem lookupDecisionKeeps {before : List (Nat × Nat)} {bits : Nat}
    {guests : List (VerifiableInference.Desc.First.Look.Guest FirstState Claim)}
    {place : VerifiableInference.Desc.K3.PG} {s s' : FirstState} {rounds : List Fmt.RoundView}
    {columns : List (List (Nat × List UInt64))}
    (accepted : (VerifiableInference.Desc.K3.lookupKind lookupSeat before bits guests place).decide s
      rounds columns = .ok s') :
    LookupKeeps s s' := by
  obtain ⟨ledger, -, afterLedger⟩ := namedReturnsItsValue accepted
  have afterOwed := needPassesOn afterLedger
  have afterCount := needPassesOn afterOwed
  have afterRoom := needPassesOn afterCount
  obtain ⟨hearing, -, returned⟩ := namedReturnsItsValue afterRoom
  have same : (Except.ok (lookupSeat.put s hearing.1 hearing.2) : Except String FirstState) =
      .ok s' := returned
  cases same
  exact ⟨hearing.1, hearing.2, rfl⟩

variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} (source : Source) (numbers : H2U.PlaceNums)
  (later : LaterPlaces) (filling : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {halves : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tables : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {files : VerifierAndGoals.PublicFiles}

/-! ## 2 Where the lookups stand -/

/-- The place in a row of a list of sub-protocols is the place of the sub-protocol at that number. -/
theorem placeOfWrittenRow {S Cl : Type} {blocks : List (Block S Cl)} {b : Nat}
    {place : VerifiableInference.Desc.Place} {rounds : Nat}
    (written : (blocks[b]?).map (fun blk => (blk.place, blk.rounds.length)) = some (place, rounds)) :
    (blocks[b]?).map (·.place) = some place := by
  cases found : blocks[b]? with
  | none =>
    rw [found] at written
    cases written
  | some blk =>
    rw [found] at written
    exact congrArg some (congrArg Prod.fst (Option.some.inj written))

/-- Of the literal list of the first chain's rows only numbers 4 and 10 bear the kind K3. -/
theorem onlyTheLookupRowsBearTheKind (b : Nat) (row : VerifiableInference.Desc.Place × Nat)
    (written : AtPublicFiles.KeyBook.fullFirst[b]? = some row) (kind : row.1.kind = KindName.K3) :
    b = 4 ∨ b = 10 := by
  obtain ⟨inList, -⟩ := List.getElem?_eq_some_iff.1 written
  have below : b < 19 := inList
  interval_cases b
  all_goals
    first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | (exfalso
       obtain rfl := Option.some.inj written
       revert kind
       decide)

/-- At every number the thread's sub-protocol has the row that the literal list has there. -/
theorem rowAtNumberIsWritten (sourced : AtPublicFiles.AtFiles.KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) (b : Nat) :
    ((laid₁ source numbers later filling w₀ rc x halves tables).bs[b]?).map
        (fun blk => (blk.place, blk.rounds.length)) = AtPublicFiles.KeyBook.fullFirst[b]? := by
  have rows : Johnson.RunOne.Sound.rowsOf
      (laid₁ source numbers later filling w₀ rc x halves tables).bs = AtPublicFiles.KeyBook.fullFirst :=
    (AtPublicFiles.KeyBook.places_named scope sourced.named).1
  rw [← rows, Johnson.RunOne.Sound.rowsOf, List.getElem?_map]

/-- **The two lookups are numbers 4 and 10 of the thread's nineteen**, and no other bears the kind. -/
theorem lookupBordersAreFourAndTen (sourced : AtPublicFiles.AtFiles.KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) :
    ((laid₁ source numbers later filling w₀ rc x halves tables).bs[4]?).map (·.place) = some (lookPlace 0) ∧
      ((laid₁ source numbers later filling w₀ rc x halves tables).bs[10]?).map (·.place) = some (lookPlace 1) ∧
      ∀ b blk, (laid₁ source numbers later filling w₀ rc x halves tables).bs[b]? = some blk →
        blk.place.kind = KindName.K3 → b = 4 ∨ b = 10 := by
  have written := rowAtNumberIsWritten source numbers later filling w₀ rc x (halves := halves)
    (tables := tables) sourced scope
  have atFour : AtPublicFiles.KeyBook.fullFirst[4]? = some (lookPlace 0, 9581) := rfl
  have atTen : AtPublicFiles.KeyBook.fullFirst[10]? = some (lookPlace 1, 9220) := rfl
  refine ⟨placeOfWrittenRow ((written 4).trans atFour), placeOfWrittenRow ((written 10).trans atTen),
    ?_⟩
  intro b blk found kind
  have row := written b
  rw [found] at row
  exact onlyTheLookupRowsBearTheKind b (blk.place, blk.rounds.length) row.symm kind

/-! ## 3 Behind the step -/

section
variable (one : OnBytes.Params.OneTime) (declared : List Fmt.DeclaredRound) (told : List ProofFile.Root)
  (setting : OnBytes.Params.Setting) (places : H2U.PlaceNums)
  (first second : VerifiableInference.Desc.Key.Lookup)

/-- The sub-protocol number 4 of the library's first chain is the first lookup's. -/
theorem blockAtFourIsTheFirstLookup
    (two : VerifiableInference.Desc.Key.lookupsOf one = [first, second])
    (blk : Block FirstState Claim)
    (found : (VerifiableInference.Desc.Key.firstChain one declared told setting places).blocksInOrder[4]? =
      some blk) :
    blk = VerifiableInference.Desc.K3.lookupKind lookupSeat [(1, 0), (1, 1)] 0 []
      (VerifiableInference.Desc.Key.lookupPlace setting 0 first) := by
  simp only [VerifiableInference.Desc.Key.firstChain, two] at found
  have same : _ = blk := Option.some.inj found
  subst same
  rfl

/-- The sub-protocol number 10 of the library's first chain is the second lookup's. -/
theorem blockAtTenIsTheSecondLookup
    (two : VerifiableInference.Desc.Key.lookupsOf one = [first, second])
    (blk : Block FirstState Claim)
    (found : (VerifiableInference.Desc.Key.firstChain one declared told setting places).blocksInOrder[10]? =
      some blk) :
    blk = VerifiableInference.Desc.K3.lookupKind lookupSeat [(1, 0), (1, 1)] 0 []
      (VerifiableInference.Desc.Key.lookupPlace setting 1 second) := by
  simp only [VerifiableInference.Desc.Key.firstChain, two] at found
  have same : _ = blk := Option.some.inj found
  subst same
  rfl

end

/-- **Behind a step of the thread at a lookup, the state is the one in front with the hearing and the ledger laid.** -/
theorem lookupStepKeepsAtTheKey (sourced : AtPublicFiles.AtFiles.KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) :
    ∀ b ∈ [4, 10], ∀ blk, (laid₁ source numbers later filling w₀ rc x halves tables).bs[b]? = some blk →
      ∀ k s m E ds y cols s',
        (laid₁ source numbers later filling w₀ rc x halves tables).Stepped blk k s m E ds y cols s' →
        LookupKeeps s s' := by
  intro b atLookup blk found k s m E ds y cols s' stepped
  obtain ⟨public₀, made, fromFiles, maker, madeSource, -, -⟩ := sourced.source
  have reading := Johnson.RunOne.Law.ReadAtO.readOf_publicOfO fromFiles
  obtain ⟨first, second, two⟩ := LPFD.hl_in_scope scope reading maker madeSource sourced.named.plan
  obtain ⟨rounds, columns, accepted⟩ :=
    Johnson.Desc.First.Walk.Tied.stepYes_decide (stepYes_of_step stepped.2)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at atLookup
  rcases atLookup with rfl | rfl
  · rw [blockAtFourIsTheFirstLookup (one₀ source) source.Y.D.1 source.Y.told.1 source.set numbers
      first second two blk found] at accepted
    exact lookupDecisionKeeps accepted
  · rw [blockAtTenIsTheSecondLookup (one₀ source) source.Y.D.1 source.Y.told.1 source.set numbers
      first second two blk found] at accepted
    exact lookupDecisionKeeps accepted

/-- At the two lookups the thread's letter `keeps` is `LookupKeeps`, where the filling's letter has
that text. -/
theorem threadKeepsAtLookups (byText : LookupsKeepByText filling) :
    ∀ b ∈ [4, 10], ∀ s s',
      (laid₁ source numbers later filling w₀ rc x halves tables).keeps b s s' ↔
        LookupKeeps s s' := by
  intro b atLookup s s'
  simp only [List.mem_cons, List.not_mem_nil, or_false] at atLookup
  rcases atLookup with rfl | rfl
  · show filling.kind₁ 4 s s' ↔ _
    rw [byText.1]
  · show filling.kind₁ 10 s s' ↔ _
    rw [byText.2]

/-- **`BehindS` AT THE TWO LOOKUPS OF THE KEY FILE's FIRST THREAD.** -/
theorem lookupBehindAtTheKey (sourced : AtPublicFiles.AtFiles.KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) (byText : LookupsKeepByText filling)
    (said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X' → Prop) :
    ∀ b ∈ [4, 10], BehindS (laid₁ source numbers later filling w₀ rc x halves tables) said b := by
  intro b atLookup blk found k s m E ds y cols s' thread _ stepped
  have below : b < 19 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at atLookup
    omega
  exact ⟨form_behind₁ source numbers later filling w₀ rc x sourced scope below found thread.1 stepped,
    trivial,
    (threadKeepsAtLookups source numbers later filling w₀ rc x byText b atLookup s s').2
      (lookupStepKeepsAtTheKey source numbers later filling w₀ rc x sourced scope b atLookup blk
        found k s m E ds y cols s' stepped)⟩

/-! ## 4 What rides past -/

/-- What may ride past a lookup: every item that is open at 4 or 10 and neither shut nor owed there
is of a plain sort: by evaluation of the table. -/
theorem ridersAtLookupsArePlain : ∀ b ∈ [4, 10],
    ∀ i ∈ fwdOpen (VerifiableInference.Desc.Key.start₁ 2) rowsFirst b, i ∉ (rowsFirst b).shuts →
      i ∉ (rowsFirst b).owes → VerifiableInference.Desc.Key.plain i = true := by decide

/-- The library's facts on what rides, behind a lookup's step: its two fields are read by none of
the readers, and the reading sees the statement's part alone. -/
theorem ridesBehindTheLookupsStep {Cells M Smp Rec : Type}
    (reading : VerifiableInference.Desc.Reading (Xi × FirstState) Cells M Smp Rec)
    (one : OnBytes.Params.OneTime) (readsStatement : Johnson.RunOne.KeyRows1.ReadsD reading)
    (items : List VerifiableInference.Desc.Key.KItem) (p : Xi) (s : FirstState)
    (heard : VerifiableInference.Desc.K3.HeardG) (ledger : OnBytes.Model.Fork) :
    VerifiableInference.Desc.Key.Rides reading (Johnson.RunOne.KeyRows1.readers₁ one) items p
      (lookupSeat.put s heard ledger) s :=
  { marked := rfl, pins := readsStatement p (lookupSeat.put s heard ledger) s rfl
    stmt := fun _ => ⟨⟨rfl, fun _ _ => rfl⟩, fun _ x' h => ⟨x', h, rfl, rfl⟩⟩
    rows := fun _ _ => rfl, keys := fun _ _ => rfl, pile := fun _ => rfl
    grp := fun _ => ⟨rfl, fun _ G' h => ⟨G', h, rfl⟩⟩ }

/-- **An item that rides past a lookup reads neither the hearing nor the lookup's ledger.** -/
theorem lookupRidersReadNeitherHearingNorLedger (reads : Johnson.RunOne.KeyRows1.ReadsL filling.base.h₁) :
    ∀ b ∈ [4, 10], ∀ k s (m : Mid (Local W₀ Rc Xi Unit) X') E s' ps i v, LookupKeeps s s' →
      i ∈ (laid₁ source numbers later filling w₀ rc x halves tables).opened b →
      i ∉ ((laid₁ source numbers later filling w₀ rc x halves tables).row b).shuts →
      i ∉ ((laid₁ source numbers later filling w₀ rc x halves tables).row b).owes →
      (laid₁ source numbers later filling w₀ rc x halves tables).means m.st.input i
        ((laid₁ source numbers later filling w₀ rc x halves tables).seat k m s)
        ((laid₁ source numbers later filling w₀ rc x halves tables).strs E) v →
      (laid₁ source numbers later filling w₀ rc x halves tables).means m.st.input i
        ((laid₁ source numbers later filling w₀ rc x halves tables).seat k m s')
        ((laid₁ source numbers later filling w₀ rc x halves tables).strs (E.add ps)) v := by
  intro b atLookup k s m E s' ps i v keeps opened notShut notOwed holds
  obtain ⟨heard, ledger, rfl⟩ := keeps
  exact fwd_at (D source numbers later) filling.base.h₁ Johnson.RunOne.KeyRows23.atSix filling.meetsT
    (one₀ source) filling.R i (ridersAtLookupsArePlain b atLookup i opened notShut notOwed) _ s _ _ _
    v (ridesBehindTheLookupsStep _ _ (Johnson.RunOne.KeyRows1.ReadsL.readsD _ reads) [i] _ s heard
      ledger) holds

/-- **`RidesPastS` AT THE TWO LOOKUPS OF THE KEY FILE's FIRST THREAD.** -/
theorem lookupRidesPastAtTheKey (reads : Johnson.RunOne.KeyRows1.ReadsL filling.base.h₁)
    (byText : LookupsKeepByText filling) (said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X' → Prop) :
    ∀ b ∈ [4, 10], RidesPastS (laid₁ source numbers later filling w₀ rc x halves tables) said b := by
  intro b atLookup k s m E s' ps i v _ keeps opened notShut notOwed holds
  exact lookupRidersReadNeitherHearingNorLedger source numbers later filling w₀ rc x reads b atLookup
    k s m E s' ps i v
    ((threadKeepsAtLookups source numbers later filling w₀ rc x byText b atLookup s s').1 keeps)
    opened notShut notOwed holds

end AtPublicFiles.Lookup.Key

#print axioms AtPublicFiles.Lookup.Key.lookupBordersAreFourAndTen
#print axioms AtPublicFiles.Lookup.Key.lookupStepKeepsAtTheKey
#print axioms AtPublicFiles.Lookup.Key.lookupBehindAtTheKey
#print axioms AtPublicFiles.Lookup.Key.lookupRidersReadNeitherHearingNorLedger
#print axioms AtPublicFiles.Lookup.Key.lookupRidesPastAtTheKey
