-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
WHAT IT IS FOR: (K-P2): which state stands behind a lookup's step, and what ledger stands in front of it, at numbers 4 and 10
  of the key file's first thread. `lookupStepKeepsAtTheKey` (E2E/Lookup/Key/LookupBehindAndRidesPastAtTheKey.lean) says that
  some hearing and some ledger are laid; here it is said which.

E2E/Lookup/Key/LookupStepLaysTheHearingAtTheKey.lean. A definition and theorems with their proofs.

  `lookupAtBorder first second b`: the lookup that stands at a border: first at 4, else second
  `theLookupsAreTwoAtTheKey`: in scope the public values hold two lookups
  `lookupDecisionHears`: where the sub-protocol's decision accepts, a ledger is open, `hearG` returns, and its return is laid
  `lookupRoundsBearNoDigest`: rounds whose challenges the lookup's entries can draw bear no sealed digest: so `noDigest`, by
      which `Block.step` hands them to the decision, leaves them as they are
  **`lookupStepLaysTheHearingAtTheKey`**: behind a step at 4 or 10, from the ledger in front: the state is the one in front with
      what `hearV` heard on the played rounds, and the ledger behind it, laid
  **`ledgerInFrontOfTheLookupAtTheKey`**: the thread at 4 or 10 has a fresh ledger, `LedgerIn` at the lookup's face, and homes
      for all its hidden values
  **`lookupPlaysAtOwnersAtTheKey`**: the seven of `K3PlaysAtO` (E2E/KeyLookupOwned.lean) at the thread at 4 or 10, from a half at
      the lookup's place that is the row at owners, and from three premises on the row's public record

By what. The lookup's entries pass `staticT` (`static_of_fit`, E2E/KeyLookupHears.lean), so their names are of a kind that
`kindAsked` says, never the sealing kind; so `drawFit` (Honest/Frame.lean) leaves no digest. `hearG_of_hearV` carries `hearV`'s
return over. The ledger: the clause `Form` of the thread holds the library's `core₁` (Johnson/Desc/Key/KeyShape.lean).

Limits. The two lookups are a named premise `two`, which `theLookupsAreTwoAtTheKey` pays in scope. That the thread stands at
border 4 or 10 at any run is not shown here.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import E2E.Lookup.Key.LookupBehindAndRidesPastAtTheKey
import E2E.KeyFacesInDesc
import Johnson.Desc.ProofFile.Honest.K3.Law.Top
import OnBytes.Params.DeclaredOfLaws
import E2E.KeyLookupOwned
import E2E.Lookup.Key.LookupExchangeOfTheNewItemsAtTheKey

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

/-! ## 1 Which lookup -/

/-- The lookup that stands at a border of the two. -/
def lookupAtBorder (first second : Lookup) (b : Nat) : Lookup := if b = 4 then first else second

/-- **In scope the public values hold two lookups.** -/
theorem theLookupsAreTwoAtTheKey {source : Source} {numbers : H2U.PlaceNums} {later : LaterPlaces}
    {files : VerifierAndGoals.PublicFiles} (sourced : AtPublicFiles.AtFiles.KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) :
    ∃ first second, lookupsOf (one₀ source) = [first, second] := by
  obtain ⟨public₀, made, fromFiles, maker, madeSource, -, -⟩ := sourced.source
  have reading := Johnson.RunOne.Law.ReadAtO.readOf_publicOfO fromFiles
  exact LPFD.hl_in_scope scope reading maker madeSource sourced.named.plan

/-! ## 2 The decision -/

/-- **Where the sub-protocol "lookup" accepts, a ledger is open, the hearing returns, and what it
returns is laid.** -/
theorem lookupDecisionHears {before : List (Nat × Nat)} {bits : Nat}
    {guests : List (VerifiableInference.Desc.First.Look.Guest FirstState Claim)}
    {place : PG} {s s' : FirstState} {rounds : List Fmt.RoundView}
    {columns : List (List (Nat × List UInt64))}
    (accepted : (lookupKind lookupSeat before bits guests place).decide s rounds columns = .ok s') :
    ∃ ledger hearing, lookupSeat.fork s = some ledger ∧ hearG place ledger rounds = some hearing ∧
      s' = lookupSeat.put s hearing.1 hearing.2 := by
  obtain ⟨ledger, openLedger, afterLedger⟩ := namedReturnsItsValue accepted
  have afterOwed := needPassesOn afterLedger
  have afterCount := needPassesOn afterOwed
  have afterRoom := needPassesOn afterCount
  obtain ⟨hearing, heard, returned⟩ := namedReturnsItsValue afterRoom
  have same : (Except.ok (lookupSeat.put s hearing.1 hearing.2) : Except String FirstState) =
      .ok s' := returned
  cases same
  exact ⟨ledger, hearing, openLedger, heard, rfl⟩

/-! ## 3 No digest -/

/-- No entry of a lookup bears the name of a sealing round. -/
theorem lookupEntriesAreNotSealed {face : VerifiableInference.Desc.K3.Face} {entries : List Fmt.Entry}
    (fit : entriesFit face entries = true) :
    ∀ e ∈ entries, Fmt.kindOf e.name ≠ some .sealed := by
  intro e member sealed
  have static := List.all_eq_true.1 (AtPublicFiles.KeyLookup.static_of_fit fit) e member
  unfold VerifiableInference.Desc.K3.staticT at static
  simp only [Bool.and_eq_true] at static
  have kind : OnBytes.Params.kindOf e.name =
      some (VerifiableInference.Desc.First.Tape.kindAsked e.name) := eq_of_beq static.1.2
  have asked : VerifiableInference.Desc.First.Tape.kindAsked e.name = .sealed :=
    Option.some.inj (kind.symm.trans ((OnBytes.Params.kindOf_eq _).trans sealed))
  unfold VerifiableInference.Desc.First.Tape.kindAsked at asked
  split at asked
  · cases asked
  · split at asked <;> cases asked

/-- Challenges that rounds without a sealing round can draw bear no digest. -/
theorem drawsWithoutSealBearNoDigest : ∀ (declared : List Fmt.DeclaredRound) (drawn : List Fmt.Drawn),
    drawsFit declared drawn = true → (∀ d ∈ declared, Fmt.kindOf d.entry.name ≠ some .sealed) →
    ∀ r ∈ drawn, r.digest = none
  | [], [], _, _, r, member => by cases member
  | [], _ :: _, fits, _, _, _ => by cases fits
  | _ :: _, [], fits, _, _, _ => by cases fits
  | d :: declared, r :: drawn, fits, notSealed, x, member => by
    have parts : drawFit d r = true ∧ drawsFit declared drawn = true :=
      Bool.and_eq_true _ _ ▸ fits
    rcases List.mem_cons.1 member with rfl | later
    · have oneFits := parts.1
      unfold drawFit at oneFits
      simp only [Bool.and_eq_true] at oneFits
      rcases (Bool.or_eq_true _ _ ▸ oneFits.2 : _ ∨ _) with clear | sealed
      · exact Option.isNone_iff_eq_none.1 clear
      · exact absurd (eq_of_beq sealed) (notSealed d (List.mem_cons_self ..))
    · exact drawsWithoutSealBearNoDigest declared drawn parts.2
        (fun e member => notSealed e (List.mem_cons_of_mem _ member)) x later

/-- Rounds whose challenges bear no digest are as `noDigest` leaves them. -/
theorem roundsWithoutDigestStay : ∀ rounds : List Fmt.RoundView,
    (∀ r ∈ rounds.map (·.drawn), r.digest = none) → rounds.map noDigest = rounds
  | [], _ => rfl
  | r :: rounds, clear => by
    have first : noDigest r = r := by
      have this : r.drawn.digest = none := clear r.drawn (List.mem_cons_self ..)
      obtain ⟨values, ⟨elements, positions, trits, digest⟩⟩ := r
      have gone : digest = none := this
      subst gone
      rfl
    rw [List.map_cons, first, roundsWithoutDigestStay rounds
      (fun x member => clear x (List.mem_cons_of_mem _ member))]

/-- **Rounds whose challenges a lookup's rounds can draw bear no digest.** -/
theorem lookupRoundsBearNoDigest {place : PG} {entries : List Fmt.Entry}
    (found : place.entries = some entries) (fit : entriesFit place.face entries = true)
    {before : List (Nat × Nat)} {bits : Nat}
    {guests : List (VerifiableInference.Desc.First.Look.Guest FirstState Claim)}
    {rounds : List Fmt.RoundView} {drawn : List Fmt.Drawn}
    (fits : drawsFit (lookupKind lookupSeat before bits guests place).rounds drawn = true)
    (same : rounds.map (·.drawn) = drawn) : rounds.map noDigest = rounds := by
  refine roundsWithoutDigestStay rounds ?_
  rw [same]
  refine drawsWithoutSealBearNoDigest _ drawn fits ?_
  rw [(AtPublicFiles.KeyFaces.rounds_of_planOk lookupSeat found).1]
  intro d member
  obtain ⟨e, inEntries, rfl⟩ := List.mem_map.1 member
  exact lookupEntriesAreNotSealed fit e inEntries

/-! ## 4 Behind the step -/

/-- The step of a lookup's block, at a ledger and a hearing. -/
theorem lookupBlockStepLays {place : PG} {entries : List Fmt.Entry}
    (found : place.entries = some entries) {before : List (Nat × Nat)} {bits : Nat}
    {guests : List (VerifiableInference.Desc.First.Look.Guest FirstState Claim)}
    {firstTree : Nat} {s s' : FirstState} {rounds : List Fmt.RoundView} {columns : List OpenedColumn} {taken : Nat}
    (step : (lookupKind lookupSeat before bits guests place).step firstTree s rounds columns =
      .ok (s', taken))
    (noneBorne : rounds.map noDigest = rounds) {front behind : Fork} {heard : HeardV}
    (ledger : s.base.fork = some front)
    (hearing : hearV place.face front rounds = some (heard, behind)) :
    s' = lookupSeat.put s (toHeardG heard) behind := by
  have accepted := ((VerifiableInference.Desc.Sound.step_ok_iff _ _ s s' rounds columns taken).1
    step).2.2.2
  rw [noneBorne] at accepted
  obtain ⟨open₀, hearing₀, opened, heardHere, rfl⟩ := lookupDecisionHears accepted
  have sameLedger : open₀ = front := Option.some.inj (opened.symm.trans ledger)
  subst sameLedger
  have carried := AtPublicFiles.KeyLookup.hearG_of_hearV (Option.isSome_iff_exists.2 ⟨_, found⟩) hearing
  have sameHearing : hearing₀ = (toHeardG heard, behind) :=
    Option.some.inj (heardHere.symm.trans carried)
  rw [sameHearing]

variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} (source : Source) (numbers : H2U.PlaceNums)
  (later : LaterPlaces) (filling : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {halves : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tables : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {files : VerifierAndGoals.PublicFiles} {first second : Lookup}

/-- **Behind a step of the thread at a lookup: the state in front with what `hearV` heard on the
played rounds, and the ledger behind it, laid.** -/
theorem lookupStepLaysTheHearingAtTheKey
    (sourced : AtPublicFiles.AtFiles.KeySourced files source numbers later)
    (two : lookupsOf (one₀ source) = [first, second]) :
    ∀ b ∈ [4, 10], ∀ blk, (laid₁ source numbers later filling w₀ rc x halves tables).bs[b]? = some blk →
      ∀ k s m E ds y cols s', drawsFit blk.rounds ds = true →
        (laid₁ source numbers later filling w₀ rc x halves tables).Stepped blk k s m E ds y cols s' →
        ∀ front heard behind, s.base.fork = some front →
          hearV (faceOfLkp (lookupAtBorder first second b)) front (roundsOf y.1) =
            some (heard, behind) →
          s' = lookupSeat.put s (toHeardG heard) behind := by
  intro b atLookup blk found k s m E ds y cols s' fits stepped front heard behind ledger hearing
  have moved := stepped.1
  unfold Thread.Moved at moved
  obtain ⟨⟨steps, -, played⟩, -⟩ := moved
  have same := yields_drawn _ _ _ _ (play_yields _ _ _ _ _ played)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at atLookup
  rcases atLookup with rfl | rfl
  · obtain ⟨-, entries, inPlace, fit⟩ := AtPublicFiles.KeyFaces.fit_in_desc source numbers later
      sourced.named.plan (first, 0) (by rw [two]; exact List.mem_cons_self ..)
    have isBlock := blockAtFourIsTheFirstLookup (one₀ source) source.Y.D.1 source.Y.told.1 source.set
      numbers first second two blk found
    subst isBlock
    exact lookupBlockStepLays inPlace stepped.2 (lookupRoundsBearNoDigest inPlace fit fits same)
      ledger hearing
  · obtain ⟨-, entries, inPlace, fit⟩ := AtPublicFiles.KeyFaces.fit_in_desc source numbers later
      sourced.named.plan (second, 1)
      (by rw [two]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have isBlock := blockAtTenIsTheSecondLookup (one₀ source) source.Y.D.1 source.Y.told.1 source.set
      numbers first second two blk found
    subst isBlock
    exact lookupBlockStepLays inPlace stepped.2 (lookupRoundsBearNoDigest inPlace fit fits same)
      ledger hearing

/-! ## 5 In front of the step -/

/-- What the book-keeping says of a state's ledger, as the lookup's law asks it. -/
theorem ledgerOfTheBook (one : OnBytes.Params.OneTime) (count : Nat) (s : FirstState)
    (homes : ((book₁ one).homes s == count) = true)
    (ledger : ((book₁ one).ledger s).any
      (fun L => L.next == 0 && L.ns == count && L.sized && L.free) = true)
    (face : VerifiableInference.Desc.K3.Face) (slots : face.slots = count) :
    ∃ front, s.base.fork = some front ∧ ProofFile.Honest.K3.Law.LedgerIn face 0 front ∧
      s.base.home.size = face.slots := by
  have unfolded : (s.base.fork.map fun F =>
      ({ next := F.next, ns := F.ns, sized := F.vp.size == F.ns && F.mf.size == F.ns && F.gotF.size == F.ns
         free := (List.range (F.ns - F.next)).all fun j => !F.gotF.getD (F.next + j) true
         filled := (List.range F.next).all fun j => F.gotF.getD j false } :
        VerifiableInference.Desc.Key.LedgerView)).any
      (fun L => L.next == 0 && L.ns == count && L.sized && L.free) = true := ledger
  cases opened : s.base.fork with
  | none =>
    rw [opened] at unfolded
    cases unfolded
  | some F =>
    rw [opened] at unfolded
    simp only [Option.map, Option.any, Bool.and_eq_true, beq_iff_eq] at unfolded
    obtain ⟨⟨⟨nextZero, room⟩, ⟨sizeOne, sizeTwo⟩, sizeThree⟩, free⟩ := unfolded
    refine ⟨F, rfl, ⟨And.intro sizeOne (And.intro sizeTwo sizeThree), nextZero, by omega, ?_⟩,
      (eq_of_beq homes).trans slots.symm⟩
    intro j _ below filled
    have inRange : j ∈ List.range (F.ns - F.next) := List.mem_range.2 (by omega)
    have stillFree := List.all_eq_true.1 free j inRange
    have inArray : j < F.gotF.size := by omega
    have atJ : ∀ d, F.gotF.getD j d = F.gotF[j] := fun d => by simp [Array.getD, inArray]
    rw [nextZero, Nat.zero_add, atJ] at stillFree
    have isFilled : F.gotF.getD j false = true := filled
    rw [atJ] at isFilled
    rw [isFilled] at stillFree
    cases stillFree

/-- **The thread at a lookup has a fresh ledger for it, with homes for all its hidden values.** -/
theorem ledgerInFrontOfTheLookupAtTheKey (two : lookupsOf (one₀ source) = [first, second]) :
    ∀ b ∈ [4, 10], ∀ k s (m : Mid (Local W₀ Rc Xi Unit) X') E,
      Thr (laid₁ source numbers later filling w₀ rc x halves tables) b k s m E →
      ∃ front, s.base.fork = some front ∧
        ProofFile.Honest.K3.Law.LedgerIn (faceOfLkp (lookupAtBorder first second b)) 0 front ∧
        s.base.home.size = (faceOfLkp (lookupAtBorder first second b)).slots := by
  intro b atLookup k s m E thread
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
    obtain ⟨-, ⟨-, homes⟩, ledger⟩ := reducedCore
    exact ledgerOfTheBook _ _ s homes ledger _ (slots₁_at (one₀ source) first second two).1.symm
  · obtain ⟨rest, reduced⟩ : ∃ rest : Bool,
        core₁ (plan₁ (one₀ source)) (readers₁ (one₀ source)) (book₁ (one₀ source)) 2
          (slots₁ (one₀ source)) 10 s =
        (rest && (!(book₁ (one₀ source)).heard s &&
          (book₁ (one₀ source)).homes s == slots₁ (one₀ source) 1 &&
          ((book₁ (one₀ source)).ledger s).any fun L =>
            L.next == 0 && L.ns == slots₁ (one₀ source) 1 && L.sized && L.free)) := ⟨_, rfl⟩
    have reducedCore := reduced.symm.trans core
    simp only [Bool.and_eq_true] at reducedCore
    obtain ⟨-, ⟨-, homes⟩, ledger⟩ := reducedCore
    exact ledgerOfTheBook _ _ s homes ledger _ (slots₁_at (one₀ source) first second two).2.symm

/-! ## 6 The seven at a row at owners -/

section Seven
open ProofFile.Honest.K3 (At LookJobs Owners proverSideOfLookupInChain ptsOf pointsAt)
open ProofFile.Honest.K3.Law.AtThr (K3PlaysAtO)

variable {Work : Type}

/-- The seven at one number of the thread, at the block that stands there. -/
theorem lookupPlaysAtOwnersAtOneNumber (sourced : AtPublicFiles.AtFiles.KeySourced files source numbers later)
    {b number : Nat} {lookupAtNumber : Lookup}
    (listed : (lookupAtNumber, number) ∈ (lookupsOf (one₀ source)).zipIdx)
    (blockIs : ∀ blk, (laid₁ source numbers later filling w₀ rc x halves tables).bs[b]? = some blk →
      blk = lookupKind lookupSeat [(1, 0), (1, 1)] 0 []
        (lookupPlace source.set number lookupAtNumber))
    (owners : Owners) (lookup : At) (jobs : LookJobs Work) (wit : Local W₀ Rc Xi Unit → Work)
    (half : halves.find? (fun h => h.place == AtPublicFiles.KeyBook.lookPlace number) =
      some (proverSideOfLookupInChain owners ⟨ptsOf, pointsAt⟩ jobs wit lookup))
    (place : lookup.place = AtPublicFiles.KeyBook.lookPlace number)
    (face : lookup.face = faceOfLkp lookupAtNumber)
    (base : lookup.base = roundsTo (laid₁ source numbers later filling w₀ rc x halves tables).bs b) :
    ∃ entries, K3PlaysAtO (laid₁ source numbers later filling w₀ rc x halves tables) owners b lookup
      jobs wit entries := by
  obtain ⟨ok, entries, inPlace, fit⟩ := AtPublicFiles.KeyFaces.fit_in_desc source numbers later
    sourced.named.plan (lookupAtNumber, number) listed
  exact ⟨entries,
    { half := fun blk found => by
        rw [blockIs blk found]
        exact half
      place := fun blk found => by
        rw [blockIs blk found, place]
        rfl
      rounds := fun blk found => by
        rw [blockIs blk found]
        exact (AtPublicFiles.KeyFaces.rounds_of_planOk lookupSeat inPlace).1
      oracles := fun blk found => by
        rw [blockIs blk found]
        exact (AtPublicFiles.KeyFaces.rounds_of_planOk lookupSeat inPlace).2
      ok := by
        rw [face]
        exact ok
      entries := by
        rw [face]
        exact fit
      base := by
        rw [base]
        exact (Nat.zero_add _).symm }⟩

/-- **The seven of `K3PlaysAtO` at the two lookups of the key file's first thread.** -/
theorem lookupPlaysAtOwnersAtTheKey (sourced : AtPublicFiles.AtFiles.KeySourced files source numbers later)
    (two : lookupsOf (one₀ source) = [first, second]) (owners : Owners) (lookup : At)
    (jobs : LookJobs Work) (wit : Local W₀ Rc Xi Unit → Work) :
    ∀ b ∈ [4, 10],
      halves.find? (fun h => h.place == AtPublicFiles.KeyBook.lookPlace (lookupNumberAtBorder b)) =
        some (proverSideOfLookupInChain owners ⟨ptsOf, pointsAt⟩ jobs wit lookup) →
      lookup.place = AtPublicFiles.KeyBook.lookPlace (lookupNumberAtBorder b) →
      lookup.face = faceOfLkp (lookupAtBorder first second b) →
      lookup.base = roundsTo (laid₁ source numbers later filling w₀ rc x halves tables).bs b →
      ∃ entries, K3PlaysAtO (laid₁ source numbers later filling w₀ rc x halves tables) owners b
        lookup jobs wit entries := by
  intro b atLookup half place face base
  simp only [List.mem_cons, List.not_mem_nil, or_false] at atLookup
  rcases atLookup with rfl | rfl
  · exact lookupPlaysAtOwnersAtOneNumber source numbers later filling w₀ rc x sourced
      (by rw [two]; exact List.mem_cons_self ..)
      (fun blk found => blockAtFourIsTheFirstLookup (one₀ source) source.Y.D.1 source.Y.told.1
        source.set numbers first second two blk found)
      owners lookup jobs wit half place face base
  · exact lookupPlaysAtOwnersAtOneNumber source numbers later filling w₀ rc x sourced
      (by rw [two]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..))
      (fun blk found => blockAtTenIsTheSecondLookup (one₀ source) source.Y.D.1 source.Y.told.1
        source.set numbers first second two blk found)
      owners lookup jobs wit half place face base

end Seven

end AtPublicFiles.Lookup.Key

#print axioms AtPublicFiles.Lookup.Key.lookupPlaysAtOwnersAtTheKey
#print axioms AtPublicFiles.Lookup.Key.theLookupsAreTwoAtTheKey
#print axioms AtPublicFiles.Lookup.Key.lookupDecisionHears
#print axioms AtPublicFiles.Lookup.Key.lookupRoundsBearNoDigest
#print axioms AtPublicFiles.Lookup.Key.lookupStepLaysTheHearingAtTheKey
#print axioms AtPublicFiles.Lookup.Key.ledgerInFrontOfTheLookupAtTheKey
