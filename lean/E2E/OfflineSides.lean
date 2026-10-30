-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/OfflineSides.lean: the offline file's rows. Sixteen named lists of simulators, one for each half
of `keyProver`, and the value of `Sides` that lays them beside the halves' own parts.

  `OfflineSimulators`          the sixteen lists, by name; `byChain`: each at its half's place
  `TheirSimulators`, `laidSimulators`   the ten lists that are not laid here stay letters; the six
                               of the kinds K1, K3, K13 are laid with the terms that exist
  `offlineRows`                the value of `Sides` at a key file's description and a book
  `offlineRows_prover`         its prover is `keyProver K`: no premise
  `first_counts`, `shared_counts`, `second_counts`   each half's place and number of parts
  `offlineRows_places`         the rows' places
  `offlineRows_seated`         every row is at a place of its chain, in scope
  `offlineRows_owns`           every owner of the book has a row, at the written sizes
  `laid_covered`               the laid lists are as long as their halves, given the letters' lengths

Limits. A SOCKET: IT PAYS NOTHING, AND NOBODY COUNTS IT. `offlineRows` is a function of the lists S
and the letters c: it holds at sixteen empty lists, and every theorem here but `laid_covered` does
too; `laid_covered` holds at ten lists of constant printers of the right lengths. `keyProver` is
E2E/KeyProver.lean's text, with the owned lookups. `RowsCovered` stands under every
sentence that names the simulators: where a list is short a simulator that tells nothing stands
there, the session then prints a constant, and only `Side.fits` refuses it.
No simulator here is shown to simulate anything, at any place: a term of type `Sim` asks
nothing. The four letters of a row are free. The halves at the two sealing places do not exist:
`keyProver` has sixteen halves; with those two places there would be eighteen. Where a
list of simulators is shorter than its half, `noSim` stands beside the rest. `offlineRows_owns` is at
the written sizes alone. Nothing on any property.
-/
import E2E.OfflineRows
import E2E.KeyBookLendsNamed
import Johnson.SendSim.At.Sim

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open OnBytes (TableKey)
open OnBytes.SendSim.At (sendSim)
open Johnson.RunOne.Sound (rowsOf)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver keyProver_first keyProver_second first_places sharedChainProverSidesInOrder)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull idxPlace msgPlace lookPlace rngPlace battPlace wPlace
  pointPlace foldedPlace locPlace omegaPlace zetaPlace splitPlace foldedTestPlace omegaTestPlace
  ownTestPlace fullFirst fullShared fullSecond of_atFull places_named)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription)
open VerifierAndGoals (PublicFiles InScope)

/-! ## 1 The lists of simulators -/

/-- **The simulators of the offline file, half by half, in the order of the chains.** -/
structure OfflineSimulators where
  /-- the sending of the index-mask message: one part -/
  indexMasks : List (Sim KeyInst)
  /-- the sending of the multiplicities: one part -/
  multiplicities : List (Sim KeyInst)
  /-- the two lookups: a part for each stage -/
  lookup0 : List (Sim KeyInst)
  lookup1 : List (Sim KeyInst)
  /-- the proximity test on the ranges' group: two parts -/
  rangesTest : List (Sim KeyInst)
  /-- the batching: two parts -/
  batching : List (Sim KeyInst)
  /-- the sending of W: one part -/
  messageW : List (Sim KeyInst)
  /-- the shared chain's rounds, each one part: "LIN point", the sending of the folded row, "LOC",
  the sending of Omega, "LIN zeta", "SPLIT" -/
  linPoint : List (Sim TableKey)
  foldedRowSending : List (Sim TableKey)
  locColumns : List (Sim TableKey)
  omegaSending : List (Sim TableKey)
  linZeta : List (Sim TableKey)
  split : List (Sim TableKey)
  /-- the proximity tests on the folded row's group and on Omega's: two parts each -/
  testOnFoldedRow : List (Sim TableKey)
  testOnOmega : List (Sim TableKey)
  /-- the proximity test of the last chain: two parts -/
  ownTest : List (Sim KeyInst)

/-- The first chain's lists by place. -/
def OfflineSimulators.firstTable (S : OfflineSimulators) : List (Place × List (Sim KeyInst)) :=
  [(idxPlace, S.indexMasks), (msgPlace, S.multiplicities), (lookPlace 0, S.lookup0),
    (lookPlace 1, S.lookup1), (rngPlace, S.rangesTest), (battPlace, S.batching),
    (wPlace, S.messageW)]

/-- The shared chain's lists by place. -/
def OfflineSimulators.sharedTable (S : OfflineSimulators) : List (Place × List (Sim TableKey)) :=
  [(pointPlace, S.linPoint), (foldedPlace, S.foldedRowSending), (locPlace, S.locColumns),
    (omegaPlace, S.omegaSending), (zetaPlace, S.linZeta), (splitPlace, S.split),
    (foldedTestPlace, S.testOnFoldedRow), (omegaTestPlace, S.testOnOmega)]

/-- **Each list at its half's place**; no simulator at any other place. -/
def OfflineSimulators.byChain (S : OfflineSimulators) : SimulatorsByChain KeyInst TableKey :=
  ⟨fun p => (S.firstTable.lookup p).getD [], fun p => (S.sharedTable.lookup p).getD [],
    fun p => ([(ownTestPlace, S.ownTest)].lookup p).getD []⟩

/-- **The lists that index privacy lays**, by its word (lane): the four proximity tests
and the shared chain's six rows. Letters. -/
structure TheirSimulators where
  rangesTest : List (Sim KeyInst)
  linPoint : List (Sim TableKey)
  foldedRowSending : List (Sim TableKey)
  locColumns : List (Sim TableKey)
  omegaSending : List (Sim TableKey)
  linZeta : List (Sim TableKey)
  split : List (Sim TableKey)
  testOnFoldedRow : List (Sim TableKey)
  testOnOmega : List (Sim TableKey)
  ownTest : List (Sim KeyInst)

/-- **These lists have the number of parts of the halves that they stand beside.** -/
structure TheirSimulators.Fit (T : TheirSimulators) : Prop where
  rangesTest : T.rangesTest.length = 2
  linPoint : T.linPoint.length = 1
  foldedRowSending : T.foldedRowSending.length = 1
  locColumns : T.locColumns.length = 1
  omegaSending : T.omegaSending.length = 1
  linZeta : T.linZeta.length = 1
  split : T.split.length = 1
  testOnFoldedRow : T.testOnFoldedRow.length = 2
  testOnOmega : T.testOnOmega.length = 2
  ownTest : T.ownTest.length = 2

variable {W₀ Rc X₀ X Wk : Type}

/-- The simulator that the kind K1 has beside a sending of the first chain: the sender's own two
rounds at a job without data, on coins of its own. -/
def sendingSimulator (J : K1.SendJob (AtPublicFiles.KeyFile.In1 W₀ Rc) X) : Sim KeyInst :=
  sendSim J.P J.first J.ride ⟨J.P.place, 0⟩

/-- **The sixteen lists**: the kinds K1, K3 and K13 at the terms that exist, the others the letters.
Nothing says that these terms simulate their parts. -/
def laidSimulators (K : KeyParts W₀ Rc X₀ X Wk) (T : TheirSimulators) : OfflineSimulators where
  indexMasks := [sendingSimulator K.idx]
  multiplicities := [sendingSimulator K.msg]
  lookup0 := K3.lookSims K.look0
  lookup1 := K3.lookSims K.look1
  rangesTest := T.rangesTest
  batching := K13.k13Sims K.batt
  messageW := [sendingSimulator K.w]
  linPoint := T.linPoint
  foldedRowSending := T.foldedRowSending
  locColumns := T.locColumns
  omegaSending := T.omegaSending
  linZeta := T.linZeta
  split := T.split
  testOnFoldedRow := T.testOnFoldedRow
  testOnOmega := T.testOnOmega
  ownTest := T.ownTest

/-! ## 2 The rows -/

/-- **The offline file's rows**: `keyProver K`'s own halves, each with its list of simulators, at a
description and a book. No falls. -/
def offlineRows (Fx : FileDescription KeyInst) (Bk : ProverCoinCounts) (K : KeyParts W₀ Rc X₀ X Wk)
    (S : OfflineSimulators) (c : ConditionsByChain Fx Bk W₀ Rc TableKey Unit X₀ X) :
    Sides Fx Bk W₀ Rc TableKey Unit X₀ X :=
  offlineSides Fx Bk (keyProver K) S.byChain c [] [] []

variable (Fx : FileDescription KeyInst) (Bk : ProverCoinCounts) (K : KeyParts W₀ Rc X₀ X Wk) (S : OfflineSimulators)
  (c : ConditionsByChain Fx Bk W₀ Rc TableKey Unit X₀ X)

/-- **Their prover is `keyProver K`.** -/
theorem offlineRows_prover : (offlineRows Fx Bk K S c).prover (keyProver K) = keyProver K :=
  offlineSides_prover Fx Bk (keyProver K) S.byChain c [] [] []

/-- The prover of these rows at any prover: its three lists are `keyProver K`'s, its other fields that
prover's own. -/
theorem offlineRows_prover_at (H : Prover W₀ Rc KeyInst TableKey Unit X₀ X) :
    (offlineRows Fx Bk K S c).prover H =
      { H with first := (keyProver K).first, shared := (keyProver K).shared,
               second := (keyProver K).second } := by
  unfold Sides.prover offlineRows offlineSides
  simp only [rowsAt_back]

/-! ## 3 The halves, each with its place and its number of parts -/

/-- The first chain's halves. -/
theorem first_counts :
    (keyProver K).first.map (fun g => (g.place, g.parts.length)) =
      [(K.idx.P.place, 1), (K.msg.P.place, 1), (K.look0.place, (K3.stages K.look0.face).length),
        (K.look1.place, (K3.stages K.look1.face).length), (K.rng.place, K.rng.parts.length),
        (K13.k13Place K.batt, 2), (K.w.P.place, 1)] := by
  simp [keyProver, K1.proverSideOfSending, K3.proverSideOfLookupInChain, K3.lookRowOwned, K13.proverSideOfClaimCombination, K13.k13Row]

/-- The shared chain's halves, where the shape splits. -/
theorem shared_counts (h : K.lin.S.sharedSplitNeeded = true) :
    (keyProver K).shared.map (fun g => (g.place, g.parts.length)) =
      [(K14.place 1, 1), (K14.sendPlace 2, 1), (K14.place 4, 1), (K14.sendPlace 5, 1),
        (K14.place 7, 1), (K14.place 8, 1), (K.onU.place, K.onU.parts.length),
        (K.onOmega.place, K.onOmega.parts.length)] := by
  simp [keyProver, sharedChainProverSidesInOrder, K14.proverSidesOfSharedRounds, K14.proverSidesOfSharedSendings, h]

/-- The second chain's one half. -/
theorem second_counts :
    (keyProver K).second.map (fun g => (g.place, g.parts.length)) =
      [(K.own.place, K.own.parts.length)] := rfl

/-! ## 4 The rows stand at their places -/

/-- **The rows' places**, chain by chain. -/
theorem offlineRows_places (hK : K.AtAll) :
    (offlineRows Fx Bk K S c).first.map (·.place) =
        [idxPlace, msgPlace, lookPlace 0, lookPlace 1, rngPlace, battPlace, wPlace] ∧
      (offlineRows Fx Bk K S c).shared.map (·.place) =
        [pointPlace, foldedPlace, locPlace, omegaPlace, zetaPlace, splitPlace, foldedTestPlace,
          omegaTestPlace] ∧
      (offlineRows Fx Bk K S c).second.map (·.place) = [ownTestPlace] := by
  refine ⟨?_, ?_, ?_⟩
  · show (rowsAt _ _ (keyProver K).first).map (·.place) = _
    rw [rowsAt_places, first_places K hK.first]
    rfl
  · show (rowsAt _ _ (keyProver K).shared).map (·.place) = _
    rw [rowsAt_places, AtPublicFiles.KeyFile.keyProver_shared K hK.splits, hK.onU, hK.onOmega]
    rfl
  · show (rowsAt _ _ (keyProver K).second).map (·.place) = _
    rw [rowsAt_places, keyProver_second, List.map_cons, List.map_nil, hK.own]

/-- The places of a list of sub-protocols, off its rows. -/
theorem places_of_rows {S' Cl : Type} {bs : List (Block S' Cl)} {rows : List (Place × Nat)}
    (hr : rowsOf bs = rows) : bs.map (·.place) = rows.map (·.1) := by
  rw [← hr]
  unfold rowsOf
  rw [List.map_map]
  rfl

/-- **In scope every row is at a place of its chain.** -/
theorem offlineRows_seated {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    (scope : InScope Z = true) (h : KeyNamed Z Xs N P) (hK : K.AtAll) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N P) Bk W₀ Rc TableKey Unit X₀ X) :
    (offlineRows (keyFileDescription Xs N P) Bk K S c).seated = true := by
  obtain ⟨r1, r2, r3⟩ := places_named scope h
  refine seated_of _ _ _ _ _ _ _ _ ?_ ?_ ?_
  · intro g hg
    have hm : g.place ∈ (keyProver K).first.map (·.place) := List.mem_map_of_mem hg
    rw [first_places K hK.first] at hm
    rw [places_of_rows r1]
    have incl : ∀ p ∈ ([⟨1, none, 1, .K1⟩, ⟨1, none, 2, .K1⟩, ⟨1, some 0, 2, .K3⟩,
        ⟨1, some 1, 2, .K3⟩, ⟨1, none, 5, .K12⟩, ⟨1, none, 13, .K13⟩, ⟨1, none, 14, .K1⟩] :
        List Place), p ∈ fullFirst.map (·.1) := by decide
    exact incl _ hm
  · intro g hg
    have hm : g.place ∈ (keyProver K).shared.map (·.place) := List.mem_map_of_mem hg
    rw [AtPublicFiles.KeyFile.keyProver_shared K hK.splits, hK.onU, hK.onOmega] at hm
    rw [places_of_rows r2]
    have incl : ∀ p ∈ ([K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7,
        K14.place 8, foldedTestPlace, omegaTestPlace] : List Place),
        p ∈ fullShared.map (·.1) := by decide
    exact incl _ hm
  · intro g hg
    have hm : g.place ∈ (keyProver K).second.map (·.place) := List.mem_map_of_mem hg
    rw [keyProver_second, List.map_cons, List.map_nil, hK.own] at hm
    rw [places_of_rows r3]
    have incl : ∀ p ∈ ([ownTestPlace] : List Place), p ∈ fullSecond.map (·.1) := by decide
    exact incl _ hm

/-! ## 5 Every owner has a row -/

/-- The six owners of the book's entries. -/
def bookOwners : List Addr :=
  [⟨idxPlace, 0⟩, ⟨msgPlace, 0⟩, ⟨wPlace, 0⟩, ⟨foldedPlace, 0⟩, ⟨omegaPlace, 0⟩,
    ⟨omegaTestPlace, 0⟩]

/-- **Every entry of the written book is owned by one of the six.** By evaluation. -/
theorem owners_full :
    atFull (fun B => (keyBook B).ahead.all fun e => bookOwners.contains e.owner) = true := by
  decide +kernel

/-- A half with a part gives its list of rows the address of its first part. -/
theorem address_of_count {Bk : ProverCoinCounts} {S' Cl V W Y Pb : Type} {sims : Place → List (Sim Pb)}
    {cs : Place → RowConditions Bk S' V W Y Pb} {hs : List (Placed V W Y)} {p : Place} {n : Nat}
    (hm : (p, n) ∈ hs.map (fun g => (g.place, g.parts.length))) (hn : 0 < n) :
    (⟨p, 0⟩ : Addr) ∈ addrsOf (rowsAt (Cl := Cl) sims cs hs) := by
  obtain ⟨g, hg, e⟩ := List.mem_map.1 hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  refine addr_mem (L := rowOf g (sims g.place) (cs g.place)) (List.mem_map.2 ⟨g, hg, rfl⟩) ?_
  show 0 < (partsBeside g.parts (sims g.place)).length
  rw [partsBeside_length]
  exact hn

/-- **At the written book every owner has a row.** hO: the test on Omega's group has a part. -/
theorem offlineRows_owns {B₀ : KeyPub} (hB : fullPub = some B₀) (hK : K.AtAll)
    (hO : 0 < K.onOmega.parts.length) (S : OfflineSimulators) (Fx : FileDescription KeyInst)
    (c : ConditionsByChain Fx (keyBook B₀) W₀ Rc TableKey Unit X₀ X) :
    (offlineRows Fx (keyBook B₀) K S c).owns = true := by
  refine owns_of _ bookOwners (of_atFull owners_full hB) ?_
  have c1 := first_counts K
  have c2 := shared_counts K hK.splits
  rw [hK.first.idx, hK.first.msg, hK.first.w] at c1
  rw [hK.onOmega] at c2
  have a1 : ∀ p n, (p, n) ∈ (keyProver K).first.map (fun g => (g.place, g.parts.length)) →
      0 < n → (⟨p, 0⟩ : Addr) ∈ addrsOf (offlineRows Fx (keyBook B₀) K S c).first :=
    fun _ _ hm hn => address_of_count hm hn
  have a2 : ∀ p n, (p, n) ∈ (keyProver K).shared.map (fun g => (g.place, g.parts.length)) →
      0 < n → (⟨p, 0⟩ : Addr) ∈ addrsOf (offlineRows Fx (keyBook B₀) K S c).shared :=
    fun _ _ hm hn => address_of_count hm hn
  intro a ha
  simp only [bookOwners, List.mem_cons, List.not_mem_nil, or_false] at ha
  simp only [List.mem_append]
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl (a1 _ 1 (by rw [c1]; simp [idxPlace]) Nat.one_pos))
  · exact Or.inl (Or.inl (a1 _ 1 (by rw [c1]; simp [msgPlace]) Nat.one_pos))
  · exact Or.inl (Or.inl (a1 _ 1 (by rw [c1]; simp [wPlace]) Nat.one_pos))
  · exact Or.inl (Or.inr (a2 _ 1 (by rw [c2]; simp [foldedPlace, K14.sendPlace]) Nat.one_pos))
  · exact Or.inl (Or.inr (a2 _ 1 (by rw [c2]; simp [omegaPlace, K14.sendPlace]) Nat.one_pos))
  · exact Or.inl (Or.inr (a2 _ _ (by rw [c2]; simp) hO))

/-! ## 6 The laid lists cover the halves -/

/-- **The laid lists are as long as their halves**, given the letters' lengths. -/
theorem laid_covered (hK : K.AtAll) (T : TheirSimulators) (hT : T.Fit)
    (hr : K.rng.parts.length = 2) (hu : K.onU.parts.length = 2)
    (ho : K.onOmega.parts.length = 2) (hw : K.own.parts.length = 2) :
    RowsCovered (laidSimulators K T).byChain.first (keyProver K).first ∧
      RowsCovered (laidSimulators K T).byChain.shared (keyProver K).shared ∧
      RowsCovered (laidSimulators K T).byChain.second (keyProver K).second := by
  have at_count {Pb V W Y : Type} (hs : List (Placed V W Y)) (sims : Place → List (Sim Pb))
      (l : List (Place × Nat)) (hl : hs.map (fun g => (g.place, g.parts.length)) = l)
      (ok : ∀ x ∈ l, (sims x.1).length = x.2) : RowsCovered sims hs := by
    intro g hg
    have hm : (g.place, g.parts.length) ∈ hs.map (fun g => (g.place, g.parts.length)) :=
      List.mem_map.2 ⟨g, hg, rfl⟩
    rw [hl] at hm
    exact ok _ hm
  refine ⟨at_count _ _ _ (first_counts K) ?_, at_count _ _ _ (shared_counts K hK.splits) ?_,
    at_count _ _ _ (second_counts K) ?_⟩
  · rw [hK.first.idx, hK.first.msg, hK.first.look0, hK.first.look1, hK.first.rng, hK.first.batt,
      hK.first.w, hr]
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · rfl
    · show (K3.lookSims K.look0).length = _
      simp [K3.lookSims]
    · show (K3.lookSims K.look1).length = _
      simp [K3.lookSims]
    · exact hT.rangesTest
    · rfl
    · rfl
  · rw [hK.onU, hK.onOmega, hu, ho]
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hT.linPoint
    · exact hT.foldedRowSending
    · exact hT.locColumns
    · exact hT.omegaSending
    · exact hT.linZeta
    · exact hT.split
    · exact hT.testOnFoldedRow
    · exact hT.testOnOmega
  · rw [hK.own, hw]
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    subst hx
    exact hT.ownTest

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.offlineRows_prover
#print axioms AtPublicFiles.OfflineRows.first_counts
#print axioms AtPublicFiles.OfflineRows.shared_counts
#print axioms AtPublicFiles.OfflineRows.offlineRows_places
#print axioms AtPublicFiles.OfflineRows.offlineRows_seated
#print axioms AtPublicFiles.OfflineRows.owners_full
#print axioms AtPublicFiles.OfflineRows.offlineRows_owns
#print axioms AtPublicFiles.OfflineRows.laid_covered
