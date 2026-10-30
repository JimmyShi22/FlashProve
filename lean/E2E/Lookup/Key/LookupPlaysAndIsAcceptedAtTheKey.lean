-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
(K-P2) `PlaysS` AND `AcceptedS` (Honest/Thread/PaysS.lean) AT NUMBERS 4 AND 10 OF THE KEY FILE's FIRST THREAD, AT EVERY `Said` AND
EVERY FALL: the honest lookup meets no stop of its own. Where the row at owners stands at the place and its part of the thread
has moved, the verifier's hearing returns on what was played (`ownedLookupBehindTheMove`), and that is all that the
sub-protocol's decision asks beside the ledger in front. So no fall is needed at a lookup. The cause: the hearing's one test
on a zero is on the draw of Y (the last challenge of a masked sumcheck with end values), whose round declares it never 0, and
`AcceptedS`'s own premise `drawsFit` bars a 0 there; the hearing has no inverse. The decision is book-keeping on hidden values:
it tests no sum, so unlawful data are accepted here too and fail later: `ExchangeS` carries the truth. Theorems with proofs.

  `roomOfTheBook`, `ledgerRoomAtTheKey`     the ledger in front of a lookup has just the lookup's slots as its room
  `lookupBlockAccepts`                     the sub-protocol's own step accepts where its tests fit, no column is read, no digest
                                           is borne, the ledger is fresh and `hearV` returns
  `lookupPlaysAtTheKey`                    **`PlaysS` at 4 and 10**
  `lookupAcceptedAtTheKey`                 **`AcceptedS` at 4 and 10, at every fall**
  `lookupFourStatementsAtTheKey`           `PlaysS`, `BehindS`, `RidesPastS`, `AcceptedS` together

What remains as a premise: `KeySourced`, `two` (which `theLookupsAreTwoAtTheKey` pays in scope), and that the half found at the
lookup's place is the row at owners, at the lookup's place, face and rounds in front; the last statement adds the three premises
of `lookupBehindAtTheKey` and `lookupRidesPastAtTheKey`.

Limits. Each statement holds also where the thread stands at nothing. `ExchangeS` is not here.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import E2E.Lookup.Key.LookupStepLaysTheHearingAtTheKey
import Johnson.Desc.ProofFile.Honest.K3.Key.OwnedLookupBehindTheMove
import Johnson.Desc.ProofFile.Honest.Thread.PaysS

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.Lookup.Key
open VerifiableInference.Desc (Block OpenedColumn noDigest)
open VerifiableInference.Desc.K3 (HeardV hearV hearG toHeardG faceOfLkp entriesFit lookupKind PG)
open VerifiableInference.Desc.Key (Xi FirstState Claim Source LaterPlaces Lookup lookupSeat lookupsOf
  lookupPlace core₁ shape₁ shape₁_iff)
open Johnson.RunOne.KeyRows1 (plan₁ readers₁ book₁ slots₁ slots₁_at)
open OnBytes.Model (Fork)
open AtPublicFiles.KeyThread
open ProofFile.Honest
open ProofFile.Honest.K3 (At LookJobs Owners proverSideOfLookupInChain ptsOf pointsAt)
open ProofFile.Honest.K3.Law.AtThr (K3PlaysAtO plays_k3O fitsAt_k3O)

/-! ## 1 The ledger's room -/

/-- What the book-keeping says of the room of a state's ledger. -/
theorem roomOfTheBook (one : OnBytes.Params.OneTime) (count : Nat) (s : FirstState)
    (ledger : ((book₁ one).ledger s).any
      (fun L => L.next == 0 && L.ns == count && L.sized && L.free) = true)
    {front : Fork} (opened : s.base.fork = some front) : front.ns = count := by
  have unfolded : (s.base.fork.map fun F =>
      ({ next := F.next, ns := F.ns, sized := F.vp.size == F.ns && F.mf.size == F.ns && F.gotF.size == F.ns
         free := (List.range (F.ns - F.next)).all fun j => !F.gotF.getD (F.next + j) true
         filled := (List.range F.next).all fun j => F.gotF.getD j false } :
        VerifiableInference.Desc.Key.LedgerView)).any
      (fun L => L.next == 0 && L.ns == count && L.sized && L.free) = true := ledger
  rw [opened] at unfolded
  simp only [Option.map, Option.any, Bool.and_eq_true, beq_iff_eq] at unfolded
  exact unfolded.1.1.2

variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} (source : Source) (numbers : H2U.PlaceNums)
  (later : LaterPlaces) (filling : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {halves : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tables : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {files : VerifierAndGoals.PublicFiles} {first second : Lookup}

/-- **The ledger in front of a lookup has room for just its slots.** -/
theorem ledgerRoomAtTheKey (two : lookupsOf (one₀ source) = [first, second]) :
    ∀ b ∈ [4, 10], ∀ k s (m : Mid (Local W₀ Rc Xi Unit) X') E,
      Thr (laid₁ source numbers later filling w₀ rc x halves tables) b k s m E →
      ∀ front, s.base.fork = some front →
        front.ns = (faceOfLkp (lookupAtBorder first second b)).slots := by
  intro b atLookup k s m E thread front opened
  have shape : shape₁ (plan₁ (one₀ source)) (readers₁ (one₀ source)) (book₁ (one₀ source)) 2
      (slots₁ (one₀ source)) b s = true := thread.2.2.1.1
  have core := ((shape₁_iff _ _ _ 2 _ b s).1 shape).2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at atLookup
  rcases atLookup with rfl | rfl
  · obtain ⟨rest, reduced⟩ : ∃ rest : Bool,
        core₁ (plan₁ (one₀ source)) (readers₁ (one₀ source)) (book₁ (one₀ source)) 2
          (slots₁ (one₀ source)) 4 s =
        (rest && (!(book₁ (one₀ source)).heard s &&
          (book₁ (one₀ source)).homes s == slots₁ (one₀ source) 0 &&
          ((book₁ (one₀ source)).ledger s).any fun L =>
            L.next == 0 && L.ns == slots₁ (one₀ source) 0 && L.sized && L.free)) := ⟨_, rfl⟩
    have reducedCore := reduced.symm.trans core
    simp only [Bool.and_eq_true] at reducedCore
    obtain ⟨-, -, ledger⟩ := reducedCore
    exact (roomOfTheBook _ _ s ledger opened).trans (slots₁_at (one₀ source) first second two).1
  · obtain ⟨rest, reduced⟩ : ∃ rest : Bool,
        core₁ (plan₁ (one₀ source)) (readers₁ (one₀ source)) (book₁ (one₀ source)) 2
          (slots₁ (one₀ source)) 10 s =
        (rest && (!(book₁ (one₀ source)).heard s &&
          (book₁ (one₀ source)).homes s == slots₁ (one₀ source) 1 &&
          ((book₁ (one₀ source)).ledger s).any fun L =>
            L.next == 0 && L.ns == slots₁ (one₀ source) 1 && L.sized && L.free)) := ⟨_, rfl⟩
    have reducedCore := reduced.symm.trans core
    simp only [Bool.and_eq_true] at reducedCore
    obtain ⟨-, -, ledger⟩ := reducedCore
    exact (roomOfTheBook _ _ s ledger opened).trans (slots₁_at (one₀ source) first second two).2

/-! ## 2 The sub-protocol's own step -/

/-- **The sub-protocol's own step accepts**, where its tests on rounds and columns pass, no column is read, no digest is borne,
the ledger in front is fresh and has the place's room, and `hearV` returns. -/
theorem lookupBlockAccepts {place : PG} {entries : List Fmt.Entry} (inPlace : place.entries = some entries)
    {before : List (Nat × Nat)} {bits : Nat}
    {guests : List (VerifiableInference.Desc.First.Look.Guest FirstState Claim)}
    {firstTree : Nat} {s : FirstState} {rounds : List Fmt.RoundView} {columns : List OpenedColumn}
    (fits : (lookupKind lookupSeat before bits guests place).Fits firstTree rounds columns)
    (noColumns : columns = []) (noneBorne : rounds.map noDigest = rounds)
    {front behind : Fork} {heard : HeardV} (opened : s.base.fork = some front)
    (next : front.next = place.first) (room : front.ns = place.ns)
    (hearing : hearV place.face front rounds = some (heard, behind)) :
    ∃ s', (lookupKind lookupSeat before bits guests place).step firstTree s rounds columns =
      .ok (s', columns.length) := by
  refine ⟨lookupSeat.put s (toHeardG heard) behind,
    (VerifiableInference.Desc.step_iff _ _ _ _ _ _ _).2 ⟨fits, ?_, ?_⟩⟩
  · rw [noneBorne]
    exact AtPublicFiles.KeyLookup.blockG_decide lookupSeat before bits guests _
      (Option.isSome_iff_exists.2 ⟨_, inPlace⟩) opened rfl next room hearing
  · subst noColumns
    have nothingWanted := eq_of_beq fits.2
    simp only [List.take_nil, List.map_nil] at nothingWanted
    rw [← nothingWanted]
    rfl

/-! ## 3 At the thread -/

section Statements
variable {Work : Type}

/-- **`PlaysS` AT THE TWO LOOKUPS OF THE KEY FILE's FIRST THREAD**, at every `Said`. -/
theorem lookupPlaysAtTheKey (sourced : AtPublicFiles.AtFiles.KeySourced files source numbers later)
    (two : lookupsOf (one₀ source) = [first, second]) (owners : Owners) (lookup : At)
    (jobs : LookJobs Work) (wit : Local W₀ Rc Xi Unit → Work)
    (said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X' → Prop) :
    ∀ b ∈ [4, 10],
      halves.find? (fun h => h.place == AtPublicFiles.KeyBook.lookPlace (lookupNumberAtBorder b)) =
        some (proverSideOfLookupInChain owners ⟨ptsOf, pointsAt⟩ jobs wit lookup) →
      lookup.place = AtPublicFiles.KeyBook.lookPlace (lookupNumberAtBorder b) →
      lookup.face = faceOfLkp (lookupAtBorder first second b) →
      lookup.base = roundsTo (laid₁ source numbers later filling w₀ rc x halves tables).bs b →
      PlaysS (laid₁ source numbers later filling w₀ rc x halves tables) said b := by
  intro b atLookup half place face base
  obtain ⟨entries, seven⟩ := lookupPlaysAtOwnersAtTheKey source numbers later filling w₀ rc x sourced two
    owners lookup jobs wit b atLookup half place face base
  exact playsS_of _ _ (plays_k3O seven)

/-- **`AcceptedS` AT THE TWO LOOKUPS OF THE KEY FILE's FIRST THREAD, AT EVERY `Said` AND EVERY FALL.** -/
theorem lookupAcceptedAtTheKey (sourced : AtPublicFiles.AtFiles.KeySourced files source numbers later)
    (two : lookupsOf (one₀ source) = [first, second]) (owners : Owners) (lookup : At)
    (jobs : LookJobs Work) (wit : Local W₀ Rc Xi Unit → Work)
    (said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    ∀ b ∈ [4, 10],
      halves.find? (fun h => h.place == AtPublicFiles.KeyBook.lookPlace (lookupNumberAtBorder b)) =
        some (proverSideOfLookupInChain owners ⟨ptsOf, pointsAt⟩ jobs wit lookup) →
      lookup.place = AtPublicFiles.KeyBook.lookPlace (lookupNumberAtBorder b) →
      lookup.face = faceOfLkp (lookupAtBorder first second b) →
      lookup.base = roundsTo (laid₁ source numbers later filling w₀ rc x halves tables).bs b →
      AcceptedS (laid₁ source numbers later filling w₀ rc x halves tables) said fall b := by
  intro b atLookup half place face base blk found k s m E ds y cols standing fits _ _ moved
  have thread := standing.1
  obtain ⟨entries, seven⟩ := lookupPlaysAtOwnersAtTheKey source numbers later filling w₀ rc x sourced two
    owners lookup jobs wit b atLookup half place face base
  obtain ⟨front, opened, ledger, -⟩ := ledgerInFrontOfTheLookupAtTheKey source numbers later filling w₀ rc x
    two b atLookup k s m E thread
  have room := ledgerRoomAtTheKey source numbers later filling w₀ rc x two b atLookup k s m E thread front opened
  have ledgerAtLookup : ProofFile.Honest.K3.Law.LedgerIn lookup.face 0 front := by
    rw [face]
    exact ledger
  obtain ⟨noColumns, -, -, heard, behind, hearing, -⟩ := ProofFile.Honest.K3.Key.ownedLookupBehindTheMove seven found
    thread fits moved 0 front ledgerAtLookup
  rw [face] at hearing
  have stepFits := fitsAt_k3O seven blk found k m E ds y cols fits moved
  have sameDrawn : (roundsOf y.1).map (·.drawn) = ds := by
    obtain ⟨⟨steps, -, played⟩, -⟩ := moved
    exact yields_drawn _ _ _ _ (play_yields _ _ _ _ _ played)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at atLookup
  rcases atLookup with rfl | rfl
  · obtain ⟨-, listed, inPlace, fit⟩ := AtPublicFiles.KeyFaces.fit_in_desc source numbers later
      sourced.named.plan (first, 0) (by rw [two]; exact List.mem_cons_self ..)
    have isBlock := blockAtFourIsTheFirstLookup (one₀ source) source.Y.D.1 source.Y.told.1 source.set
      numbers first second two blk found
    subst isBlock
    obtain ⟨s', step⟩ := lookupBlockAccepts inPlace stepFits noColumns
      (lookupRoundsBearNoDigest inPlace fit fits sameDrawn) opened ledger.next room hearing
    exact ⟨s', moved, step⟩
  · obtain ⟨-, listed, inPlace, fit⟩ := AtPublicFiles.KeyFaces.fit_in_desc source numbers later
      sourced.named.plan (second, 1)
      (by rw [two]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have isBlock := blockAtTenIsTheSecondLookup (one₀ source) source.Y.D.1 source.Y.told.1 source.set
      numbers first second two blk found
    subst isBlock
    obtain ⟨s', step⟩ := lookupBlockAccepts inPlace stepFits noColumns
      (lookupRoundsBearNoDigest inPlace fit fits sameDrawn) opened ledger.next room hearing
    exact ⟨s', moved, step⟩

/-- **FOUR OF THE FIVE STATEMENTS AT THE TWO LOOKUPS**, at every `Said` and every fall. `ExchangeS` is the fifth. -/
theorem lookupFourStatementsAtTheKey (sourced : AtPublicFiles.AtFiles.KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) (two : lookupsOf (one₀ source) = [first, second])
    (byText : LookupsKeepByText filling) (reads : Johnson.RunOne.KeyRows1.ReadsL filling.base.h₁)
    (owners : Owners) (lookup : At) (jobs : LookJobs Work) (wit : Local W₀ Rc Xi Unit → Work)
    (said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Unit) X' → Prop)
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    ∀ b ∈ [4, 10],
      halves.find? (fun h => h.place == AtPublicFiles.KeyBook.lookPlace (lookupNumberAtBorder b)) =
        some (proverSideOfLookupInChain owners ⟨ptsOf, pointsAt⟩ jobs wit lookup) →
      lookup.place = AtPublicFiles.KeyBook.lookPlace (lookupNumberAtBorder b) →
      lookup.face = faceOfLkp (lookupAtBorder first second b) →
      lookup.base = roundsTo (laid₁ source numbers later filling w₀ rc x halves tables).bs b →
      PlaysS (laid₁ source numbers later filling w₀ rc x halves tables) said b ∧
        BehindS (laid₁ source numbers later filling w₀ rc x halves tables) said b ∧
        RidesPastS (laid₁ source numbers later filling w₀ rc x halves tables) said b ∧
        AcceptedS (laid₁ source numbers later filling w₀ rc x halves tables) said fall b :=
  fun b atLookup half place face base =>
    ⟨lookupPlaysAtTheKey source numbers later filling w₀ rc x sourced two owners lookup jobs wit said b atLookup
        half place face base,
      lookupBehindAtTheKey source numbers later filling w₀ rc x sourced scope byText said b atLookup,
      lookupRidesPastAtTheKey source numbers later filling w₀ rc x reads byText said b atLookup,
      lookupAcceptedAtTheKey source numbers later filling w₀ rc x sourced two owners lookup jobs wit said fall b
        atLookup half place face base⟩

end Statements

end AtPublicFiles.Lookup.Key

#print axioms AtPublicFiles.Lookup.Key.roomOfTheBook
#print axioms AtPublicFiles.Lookup.Key.ledgerRoomAtTheKey
#print axioms AtPublicFiles.Lookup.Key.lookupBlockAccepts
#print axioms AtPublicFiles.Lookup.Key.lookupPlaysAtTheKey
#print axioms AtPublicFiles.Lookup.Key.lookupAcceptedAtTheKey
#print axioms AtPublicFiles.Lookup.Key.lookupFourStatementsAtTheKey
