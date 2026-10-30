-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRowsByPlace.lean: the three fields of OwedRest (E2E/OfflineClauses.lean), cut row by row:
what is owed at each of the offline file's sixteen rows, at its own place, in that structure's own
text; one value of the rows' letters, laid place by place; and what stays owed when six rows of the
first chain are paid.

STATEMENTS AND DEFINITIONS ONLY: nothing is proved here but that the laid letters meet what the six
rows ask of them.

  GoodFirstAt, GoodSharedAt, GoodLastAt   a conjunct of the field good, with one premise laid in:
                                          L.place = p.
  OwedFirstAt, OwedSharedAt, OwedLastAt   a conjunct of what the field owed concludes, under that
                                          field's own premises, with the same premise laid in.
  RunsAt                                  the field runs, its text to the letter.
  TheirConditions                         the letters of the ten rows that are not ours: LETTERS.
  laidConditions                          ONE value of c: the senders' letters at the three sendings,
                                          nothing at the two lookups and the batching, the ten
                                          letters at the ten other places.
  laidConditions_positions, _letters      SendingPositions and SixLetters hold at it, whatever the
                                          ten letters.
  TenRowsOwed                             twenty-one named premises: ten rows' good, ten rows' owed,
                                          and runs whole.

The relation on (index, committer's randomness, instance) under which owed and runs are asked is a
letter Rel here: OwedRest has KeyRel files in its place.

CONDITIONAL: TenRowsOwed is a premise of the join (E2E/OfflineRowsJoin.lean): tenRowsOwed_of_four (E2E/OfflineFourRowsLeft.lean) gives a member from FourRowsOwed.
It stands in for ten rows' proofs and for the run's; it proves nothing of them. Nothing on any
property.
-/
import E2E.OfflineFirstRowsAtFiles
import E2E.OfflineSixConditions

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.Term
open VerifiableInference.Desc (FileDescription Place)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open OnBytes (TableKey)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyBook (idxPlace msgPlace lookPlace rngPlace battPlace wPlace pointPlace foldedPlace
  locPlace omegaPlace zetaPlace splitPlace foldedTestPlace omegaTestPlace ownTestPlace)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open VerifierAndGoals (PublicFiles)

/-! ## 1 The letters, laid place by place -/

section Letters
variable {W₀ Rc X₀ X Wk : Type}

/-- **The letters of the ten rows beside the six**: the four proximity tests and the shared
chain's six rows. LETTERS. -/
structure TheirConditions (Fx : FileDescription AtPublicFiles.KeyFile.KeyInst) (Bk : ProverCoinCounts) (W₀ Rc X₀ X : Type) where
  rangesTest : RowConditions Bk Fx.S₁ (Local W₀ Rc AtPublicFiles.KeyFile.KeyInst Unit) (Local W₀ Rc AtPublicFiles.KeyFile.KeyInst Unit) X AtPublicFiles.KeyFile.KeyInst
  linPoint : RowConditions Bk Fx.S₂ Empty (Common W₀ Rc TableKey) X₀ TableKey
  foldedRowSending : RowConditions Bk Fx.S₂ Empty (Common W₀ Rc TableKey) X₀ TableKey
  locColumns : RowConditions Bk Fx.S₂ Empty (Common W₀ Rc TableKey) X₀ TableKey
  omegaSending : RowConditions Bk Fx.S₂ Empty (Common W₀ Rc TableKey) X₀ TableKey
  linZeta : RowConditions Bk Fx.S₂ Empty (Common W₀ Rc TableKey) X₀ TableKey
  split : RowConditions Bk Fx.S₂ Empty (Common W₀ Rc TableKey) X₀ TableKey
  testOnFoldedRow : RowConditions Bk Fx.S₂ Empty (Common W₀ Rc TableKey) X₀ TableKey
  testOnOmega : RowConditions Bk Fx.S₂ Empty (Common W₀ Rc TableKey) X₀ TableKey
  ownTest : RowConditions Bk Fx.S₃ (Local W₀ Rc AtPublicFiles.KeyFile.KeyInst Unit) (Local W₀ Rc AtPublicFiles.KeyFile.KeyInst Unit) X AtPublicFiles.KeyFile.KeyInst

/-- **The one value of the rows' letters**: at the three sendings' places the senders' letters; at the
ten other rows' places the ten letters; elsewhere, so at the two lookups and the batching, the letters
that say nothing. -/
def laidConditions (Fx : FileDescription AtPublicFiles.KeyFile.KeyInst) (Bk : ProverCoinCounts) (K : KeyParts W₀ Rc X₀ X Wk)
    (t : TheirConditions Fx Bk W₀ Rc X₀ X) : ConditionsByChain Fx Bk W₀ Rc TableKey Unit X₀ X :=
  ⟨fun p => (([(idxPlace, senderConditions K.idx.P), (msgPlace, senderConditions K.msg.P),
      (wPlace, senderConditions K.w.P), (rngPlace, t.rangesTest)] : List (Place × _)).lookup
        p).getD RowConditions.bare,
    fun p => (([(pointPlace, t.linPoint), (foldedPlace, t.foldedRowSending),
      (locPlace, t.locColumns), (omegaPlace, t.omegaSending), (zetaPlace, t.linZeta),
      (splitPlace, t.split), (foldedTestPlace, t.testOnFoldedRow),
      (omegaTestPlace, t.testOnOmega)] : List (Place × _)).lookup p).getD RowConditions.bare,
    fun p => (([(ownTestPlace, t.ownTest)] : List (Place × _)).lookup p).getD RowConditions.bare⟩

/-- **What the field owed asks of the letters at the six rows holds at it**, whatever the ten. -/
theorem laidConditions_letters (Fx : FileDescription AtPublicFiles.KeyFile.KeyInst) (Bk : ProverCoinCounts) (K : KeyParts W₀ Rc X₀ X Wk)
    (t : TheirConditions Fx Bk W₀ Rc X₀ X) : SixLetters K (laidConditions Fx Bk K t) where
  idx := ⟨fun _ _ _ _ => trivial, fun _ _ _ h => h⟩
  msg := ⟨fun _ _ _ _ => trivial, fun _ _ _ h => h⟩
  look0 := RowConditions.bare_asksNothing
  look1 := RowConditions.bare_asksNothing
  batt := RowConditions.bare_asksNothing
  w := ⟨fun _ _ _ _ => trivial, fun _ _ _ h => h⟩

/-- **What the field good asks of the letters at the three sendings holds at it**, whatever the ten.
-/
theorem laidConditions_positions {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} (Bk : ProverCoinCounts)
    (K : KeyParts W₀ Rc Unit Unit Wk) (t : TheirConditions (keyFileDescription Xs N Pl) Bk W₀ Rc Unit Unit) :
    SendingPositions K (laidConditions (keyFileDescription Xs N Pl) Bk K t) where
  indexMasks := fun _ _ _ h => h
  multiplicities := fun _ _ _ h => h
  messageW := fun _ _ _ h => h

/-- The ten letters stand at their places. -/
theorem laidConditions_theirs (Fx : FileDescription AtPublicFiles.KeyFile.KeyInst) (Bk : ProverCoinCounts) (K : KeyParts W₀ Rc X₀ X Wk)
    (t : TheirConditions Fx Bk W₀ Rc X₀ X) :
    (laidConditions Fx Bk K t).first rngPlace = t.rangesTest ∧
      (laidConditions Fx Bk K t).shared pointPlace = t.linPoint ∧
      (laidConditions Fx Bk K t).shared foldedPlace = t.foldedRowSending ∧
      (laidConditions Fx Bk K t).shared locPlace = t.locColumns ∧
      (laidConditions Fx Bk K t).shared omegaPlace = t.omegaSending ∧
      (laidConditions Fx Bk K t).shared zetaPlace = t.linZeta ∧
      (laidConditions Fx Bk K t).shared splitPlace = t.split ∧
      (laidConditions Fx Bk K t).shared foldedTestPlace = t.testOnFoldedRow ∧
      (laidConditions Fx Bk K t).shared omegaTestPlace = t.testOnOmega ∧
      (laidConditions Fx Bk K t).second ownTestPlace = t.ownTest :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Letters

/-! ## 2 The fields of OwedRest at one place -/

variable {files : PublicFiles}

section AtPlace
variable (d : OfflineDescription) (S : OfflineSimulators)
  (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) offlineProverCoinCounts FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey
    Unit Unit Unit)

/-- The first conjunct of OwedRest.good at the rows of one place. -/
def GoodFirstAt (p : Place) : Prop :=
  let F := keyFileDescription d.source d.numbers d.later
  let G := (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute
  ∀ L ∈ G.first, L.place = p → (L.withField 0 0 F.first.blocksInOrder [] 0).goodAt (earlierOf F 0) .own
      F.first.blocksInOrder (orderOf F) 0 0 G.falls₁

/-- The second conjunct at the rows of one place. -/
def GoodSharedAt (p : Place) : Prop :=
  let F := keyFileDescription d.source d.numbers d.later
  let G := (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute
  ∀ L ∈ G.shared, L.place = p → (L.withField 1 0 F.shared.blocksInOrder [] 0).goodAt (earlierOf F 1) .shared
      F.shared.blocksInOrder (orderOf F) 1 0 G.falls₂

/-- The third conjunct at the rows of one place. -/
def GoodLastAt (p : Place) : Prop :=
  let F := keyFileDescription d.source d.numbers d.later
  let G := (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute
  ∀ L ∈ G.second, L.place = p → ∀ base skip,
    (L.withField 2 F.lastChainFirstTreeNumber F.second.blocksInOrder base skip).goodAt (earlierOf F 2) .own
      F.second.blocksInOrder (orderOf F) 2 F.lastChainFirstTreeNumber G.falls₃

variable (Rel : FullSizeMatrix → (protocolAtFiles files).EncodingRandomness → AtPublicFiles.KeyFile.KeyInst → Prop)
  (H : Prover FullSizeMatrix (protocolAtFiles files).EncodingRandomness AtPublicFiles.KeyFile.KeyInst TableKey Unit Unit Unit)

/-- The field runs of OwedRest, at a relation. -/
def RunsAt : Prop :=
  let F := keyFileDescription d.source d.numbers d.later
  let G := (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute
  ∀ w₀ rc x, Rel w₀ rc x → ∀ (k : Coins offlineProverCoinCounts) ρ, ρ.due F = true →
    silentAt F (G.prover H) w₀ rc x ρ = none →
    ∃ r, runC F offlineProverCoinCounts (G.prover H) w₀ rc x k ρ = .ok r

/-- The first conjunct of what OwedRest.owed concludes, at the rows of one place. -/
def OwedFirstAt (p : Place) : Prop :=
  let F := keyFileDescription d.source d.numbers d.later
  let G := (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute
  ∀ w₀ rc x, Rel w₀ rc x → ∀ (k : Coins offlineProverCoinCounts) ρ r, ρ.due F = true →
    silentAt F (G.prover H) w₀ rc x ρ = none →
    runC F offlineProverCoinCounts (G.prover H) w₀ rc x k ρ = .ok r →
    ∀ L ∈ G.first, L.place = p → L.owedAt F.first.blocksInOrder k 0
      (fun a => orRefused (midAtW F offlineProverCoinCounts (G.prover H) w₀ rc x k ρ a)) r.run
      (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called

/-- The second conjunct, at the rows of one place. -/
def OwedSharedAt (p : Place) : Prop :=
  let F := keyFileDescription d.source d.numbers d.later
  let G := (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute
  ∀ w₀ rc x, Rel w₀ rc x → ∀ (k : Coins offlineProverCoinCounts) ρ r, ρ.due F = true →
    silentAt F (G.prover H) w₀ rc x ρ = none →
    runC F offlineProverCoinCounts (G.prover H) w₀ rc x k ρ = .ok r →
    ∀ L ∈ G.shared, L.place = p → L.owedAt F.shared.blocksInOrder k 1
      (fun a => orRefused (midSharedAtW F offlineProverCoinCounts (G.prover H) w₀ rc x k ρ a)) r.run
      (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called

/-- The third conjunct, at the rows of one place. -/
def OwedLastAt (p : Place) : Prop :=
  let F := keyFileDescription d.source d.numbers d.later
  let G := (offlineRowsAt (files := files) d offlineProverCoinCounts S c).mute
  ∀ w₀ rc x, Rel w₀ rc x → ∀ (k : Coins offlineProverCoinCounts) ρ r, ρ.due F = true →
    silentAt F (G.prover H) w₀ rc x ρ = none →
    runC F offlineProverCoinCounts (G.prover H) w₀ rc x k ρ = .ok r →
    ∀ L ∈ G.second, L.place = p → L.owedAt F.second.blocksInOrder k 2
      (fun a => orRefused (midAtW F offlineProverCoinCounts (G.prover H) w₀ rc x k ρ a)) r.run
      (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called

/-- **WHAT STAYS OWED WHEN THE SIX ROWS ARE PAID**: ten rows' good, ten rows' owed, each at the row's own
place, and the field runs whole. NAMED PREMISES. tenRowsOwed_of_four (E2E/OfflineFourRowsLeft.lean) gives a member from FourRowsOwed. -/
structure TenRowsOwed : Prop where
  rangesTestGood : GoodFirstAt (files := files) d S c rngPlace
  linPointGood : GoodSharedAt (files := files) d S c pointPlace
  foldedRowSendingGood : GoodSharedAt (files := files) d S c foldedPlace
  locColumnsGood : GoodSharedAt (files := files) d S c locPlace
  omegaSendingGood : GoodSharedAt (files := files) d S c omegaPlace
  linZetaGood : GoodSharedAt (files := files) d S c zetaPlace
  splitGood : GoodSharedAt (files := files) d S c splitPlace
  testOnFoldedRowGood : GoodSharedAt (files := files) d S c foldedTestPlace
  testOnOmegaGood : GoodSharedAt (files := files) d S c omegaTestPlace
  ownTestGood : GoodLastAt (files := files) d S c ownTestPlace
  runs : RunsAt (files := files) d S c Rel H
  rangesTestOwed : OwedFirstAt (files := files) d S c Rel H rngPlace
  linPointOwed : OwedSharedAt (files := files) d S c Rel H pointPlace
  foldedRowSendingOwed : OwedSharedAt (files := files) d S c Rel H foldedPlace
  locColumnsOwed : OwedSharedAt (files := files) d S c Rel H locPlace
  omegaSendingOwed : OwedSharedAt (files := files) d S c Rel H omegaPlace
  linZetaOwed : OwedSharedAt (files := files) d S c Rel H zetaPlace
  splitOwed : OwedSharedAt (files := files) d S c Rel H splitPlace
  testOnFoldedRowOwed : OwedSharedAt (files := files) d S c Rel H foldedTestPlace
  testOnOmegaOwed : OwedSharedAt (files := files) d S c Rel H omegaTestPlace
  ownTestOwed : OwedLastAt (files := files) d S c Rel H ownTestPlace

end AtPlace

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.laidConditions_letters
#print axioms AtPublicFiles.OfflineRows.laidConditions_positions
#print axioms AtPublicFiles.OfflineRows.laidConditions_theirs
