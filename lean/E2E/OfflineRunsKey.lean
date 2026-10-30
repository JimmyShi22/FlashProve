-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRunsKey.lean: "every run returns" at the key file's description and `keyProver K`: one named premise for
each of the sixteen places that have a prover's side, three of them paid here.

  `PlaysAtFirst`, `PlaysAtShared`, `PlaysAtSecond`   THE NAMED PREMISE AT A PLACE: `BlockPlays`
                         (E2E/OfflineRunsForm.lean) at the sub-protocol at that place, from the form in front of it
  `halvesPlay_of_places`   `HalvesPlay` (E2E/OfflineRunsRows.lean) from the premise at every prover's side's place.
                         General in the description, the book and the prover
  `find_look0`, `find_look1`, `find_batt`   which prover's side stands at the two lookups' and the batching's place
  `lookups_play`, `batching_plays`   PAID: the premise at these three places, in scope
  `KeyOthersPlay`        the premise at the other thirteen places: LETTERS: no member is shown here
  `key_blocks_play`      `BlocksPlay` at the key file from these
  `key_runs`             every run returns, from these thirteen, `ready`, `sealPlain`, `rootedAll` and `PlanServes`

No acceptance is spent or shown. Nothing on any property.
-/
import E2E.OfflineRunsLaw
import E2E.OfflineRunsBatching
import E2E.KeyLaid
import E2E.KeyPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place)
open VerifiableInference.Desc.Key (Source LaterPlaces lookupsOf)
open OnBytes (TableKey)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver keyProver_first keyProver_second first_places
  keyProver_shared)
open AtPublicFiles.KeyBook (idxPlace msgPlace lookPlace rngPlace battPlace wPlace pointPlace foldedPlace locPlace
  omegaPlace zetaPlace splitPlace foldedTestPlace omegaTestPlace ownTestPlace)
open AtPublicFiles.KeyValues (faceAt keyBatt)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription five_sourced)
open VerifierAndGoals (PublicFiles InScope)

section General
variable {Xi W₀ Rc Ky Tr X₀ X : Type}

/-- **The named premise at a place of the first chain.** -/
def PlaysAtFirst (F : FileDescription Xi) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (own : Local W₀ Rc Xi Tr) (p : Place) : Prop :=
  ∀ j b, F.first.blocksInOrder[j]? = some b → b.place = p →
    BlockPlays .own Bk 0 H.first b (MidForm startNone (roundsIn F.first.blocksInOrder j) own)

/-- At a place of the shared chain. -/
def PlaysAtShared (F : FileDescription Xi) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (common : Common W₀ Rc Ky) (p : Place) : Prop :=
  ∀ j b, F.shared.blocksInOrder[j]? = some b → b.place = p →
    BlockPlays .shared Bk 1 H.shared b (MidForm startNone (roundsIn F.shared.blocksInOrder j) common)

/-- At a place of the second chain. -/
def PlaysAtSecond (F : FileDescription Xi) (Bk : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (own : Local W₀ Rc Xi Tr) (p : Place) : Prop :=
  ∀ j b, F.second.blocksInOrder[j]? = some b → b.place = p →
    BlockPlays .own Bk 2 H.second b (MidForm (startThird F) (roundsIn F.second.blocksInOrder j) own)

/-- What `find?` by a place returns is a member at that place. -/
theorem place_of_find {V W Y : Type} {hs : List (Placed V W Y)} {p : Place} {g : Placed V W Y}
    (h : (hs.find? fun g => g.place == p) = some g) : g ∈ hs ∧ p = g.place :=
  ⟨List.mem_of_find?_eq_some h,
    (beq_iff_eq.1 (List.find?_some (p := fun g : Placed V W Y => g.place == p) h)).symm⟩

/-- **`HalvesPlay` from the premise at every prover's side's place.** -/
theorem halvesPlay_of_places {F : FileDescription Xi} {Bk : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X}
    {own : Local W₀ Rc Xi Tr} {common : Common W₀ Rc Ky}
    (h₁ : ∀ p ∈ H.first.map (·.place), PlaysAtFirst F Bk H own p)
    (h₂ : ∀ p ∈ H.shared.map (·.place), PlaysAtShared F Bk H common p)
    (h₃ : ∀ p ∈ H.second.map (·.place), PlaysAtSecond F Bk H own p) :
    HalvesPlay F Bk H own common where
  first := fun j b g hb hf =>
    h₁ g.place (List.mem_map.2 ⟨g, (place_of_find hf).1, rfl⟩) j b hb
      (place_of_find hf).2
  shared := fun j b g hb hf =>
    h₂ g.place (List.mem_map.2 ⟨g, (place_of_find hf).1, rfl⟩) j b hb
      (place_of_find hf).2
  second := fun j b g hb hf =>
    h₃ g.place (List.mem_map.2 ⟨g, (place_of_find hf).1, rfl⟩) j b hb
      (place_of_find hf).2

end General

section Key
variable {W₀ Rc X₀ X Wk : Type} (K : KeyParts W₀ Rc X₀ X Wk)

/-- The prover's side at the first lookup's place. -/
theorem find_look0 (hA : K.AtPlaces) :
    ((keyProver K).first.find? fun g => g.place == lookPlace 0) =
      some (K3.proverSideOfLookupInChain (K3.keyOwners K.look0.face) K.reads K.jobs0 K.wit K.look0) := by
  rw [keyProver_first,
    List.find?_cons_of_neg (by show ¬ ((K.idx.P.place == lookPlace 0) = true); rw [hA.idx]; decide),
    List.find?_cons_of_neg (by show ¬ ((K.msg.P.place == lookPlace 0) = true); rw [hA.msg]; decide),
    List.find?_cons_of_pos (by show (K.look0.place == lookPlace 0) = true; rw [hA.look0]; rfl)]

/-- At the second lookup's place. -/
theorem find_look1 (hA : K.AtPlaces) :
    ((keyProver K).first.find? fun g => g.place == lookPlace 1) =
      some (K3.proverSideOfLookupInChain (K3.keyOwners K.look1.face) K.reads K.jobs1 K.wit K.look1) := by
  rw [keyProver_first,
    List.find?_cons_of_neg (by show ¬ ((K.idx.P.place == lookPlace 1) = true); rw [hA.idx]; decide),
    List.find?_cons_of_neg (by show ¬ ((K.msg.P.place == lookPlace 1) = true); rw [hA.msg]; decide),
    List.find?_cons_of_neg (by show ¬ ((K.look0.place == lookPlace 1) = true); rw [hA.look0]; decide),
    List.find?_cons_of_pos (by show (K.look1.place == lookPlace 1) = true; rw [hA.look1]; rfl)]

/-- At the batching's place. -/
theorem find_batt (hA : K.AtPlaces) :
    ((keyProver K).first.find? fun g => g.place == battPlace) =
      some (K13.proverSideOfClaimCombination K.weights K.pile K.batt) := by
  rw [keyProver_first,
    List.find?_cons_of_neg (by show ¬ ((K.idx.P.place == battPlace) = true); rw [hA.idx]; decide),
    List.find?_cons_of_neg (by show ¬ ((K.msg.P.place == battPlace) = true); rw [hA.msg]; decide),
    List.find?_cons_of_neg (by show ¬ ((K.look0.place == battPlace) = true); rw [hA.look0]; decide),
    List.find?_cons_of_neg (by show ¬ ((K.look1.place == battPlace) = true); rw [hA.look1]; decide),
    List.find?_cons_of_neg (by rw [hA.rng]; decide),
    List.find?_cons_of_pos (by show (K13.k13Place K.batt == battPlace) = true; rw [hA.batt]; rfl)]

variable {K} {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **PAID: the premise at the two lookups' places**, in scope. -/
theorem lookups_play (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (Bk : ProverCoinCounts)
    (hA : K.AtPlaces) (hf0 : K.look0.face = faceAt Xs 0) (hf1 : K.look1.face = faceAt Xs 1)
    (own : Local W₀ Rc KeyInst Unit) :
    PlaysAtFirst (keyFileDescription Xs N Pl) Bk (keyProver K) own (lookPlace 0) ∧
      PlaysAtFirst (keyFileDescription Xs N Pl) Bk (keyProver K) own (lookPlace 1) := by
  obtain ⟨-, er, el, -, -⟩ := five_sourced hs scope
  have hlen : (lookupsOf Xs.Y.k.oneTime).length = 2 := by
    unfold VerifiableInference.Desc.Key.lookupsOf
    rw [er, el]
    decide +kernel
  constructor
  · intro j b hb hp
    exact look_block_plays hs.named.plan (i := 0) (by omega) _ _ _ _ _ hf0 (List.mem_of_getElem? hb) hp
      (by rw [hp]; exact find_look0 K hA) _
  · intro j b hb hp
    exact look_block_plays hs.named.plan (i := 1) (by omega) _ _ _ _ _ hf1 (List.mem_of_getElem? hb) hp
      (by rw [hp]; exact find_look1 K hA) _

/-- **PAID: the premise at the batching's place**, in scope. -/
theorem batching_plays (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (Bk : ProverCoinCounts)
    (hA : K.AtPlaces) (hb : K.batt = keyBatt Xs) (own : Local W₀ Rc KeyInst Unit) :
    PlaysAtFirst (keyFileDescription Xs N Pl) Bk (keyProver K) own battPlace := by
  obtain ⟨-, -, el, -, -⟩ := five_sourced hs scope
  have hk : (keyBatt Xs).lin.kCol = 18 := by
    show Xs.Y.k.oneTime.lin.kCol = 18
    rw [el]
    decide +kernel
  intro j b hj hp
  exact batt_block_plays hk K.weights K.pile (List.mem_of_getElem? hj) hp
    (by rw [hp, find_batt K hA, hb]) _

/-- **The premise at the other thirteen places.** LETTERS. -/
structure KeyOthersPlay (F : FileDescription KeyInst) (Bk : ProverCoinCounts) (K : KeyParts W₀ Rc X₀ X Wk)
    (own : Local W₀ Rc KeyInst Unit) (common : Common W₀ Rc TableKey) : Prop where
  indexMasks : PlaysAtFirst F Bk (keyProver K) own idxPlace
  multiplicities : PlaysAtFirst F Bk (keyProver K) own msgPlace
  rangesTest : PlaysAtFirst F Bk (keyProver K) own rngPlace
  messageW : PlaysAtFirst F Bk (keyProver K) own wPlace
  linPoint : PlaysAtShared F Bk (keyProver K) common pointPlace
  foldedRowSending : PlaysAtShared F Bk (keyProver K) common foldedPlace
  locColumns : PlaysAtShared F Bk (keyProver K) common locPlace
  omegaSending : PlaysAtShared F Bk (keyProver K) common omegaPlace
  linZeta : PlaysAtShared F Bk (keyProver K) common zetaPlace
  split : PlaysAtShared F Bk (keyProver K) common splitPlace
  testOnFoldedRow : PlaysAtShared F Bk (keyProver K) common foldedTestPlace
  testOnOmega : PlaysAtShared F Bk (keyProver K) common omegaTestPlace
  ownTest : PlaysAtSecond F Bk (keyProver K) own ownTestPlace

/-- **`BlocksPlay` at the key file**, from the thirteen. -/
theorem key_blocks_play (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (Bk : ProverCoinCounts)
    (hA : K.AtAll) (hf0 : K.look0.face = faceAt Xs 0) (hf1 : K.look1.face = faceAt Xs 1)
    (hb : K.batt = keyBatt Xs) (own : Local W₀ Rc KeyInst Unit) (common : Common W₀ Rc TableKey)
    (hO : KeyOthersPlay (keyFileDescription Xs N Pl) Bk K own common) :
    BlocksPlay (keyFileDescription Xs N Pl) Bk (keyProver K) own common := by
  obtain ⟨l0, l1⟩ := lookups_play (N := N) (Pl := Pl) hs scope Bk hA.first hf0 hf1 own
  have bt := batching_plays (N := N) (Pl := Pl) hs scope Bk hA.first hb own
  refine blocksPlay_of_halves (halvesPlay_of_places ?_ ?_ ?_)
  · intro p hp
    rw [first_places K hA.first] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hO.indexMasks
    · exact hO.multiplicities
    · exact l0
    · exact l1
    · exact hO.rangesTest
    · exact bt
    · exact hO.messageW
  · intro p hp
    rw [keyProver_shared K hA.splits, hA.onU, hA.onOmega] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hO.linPoint
    · exact hO.foldedRowSending
    · exact hO.locColumns
    · exact hO.omegaSending
    · exact hO.linZeta
    · exact hO.split
    · exact hO.testOnFoldedRow
    · exact hO.testOnOmega
  · intro p hp
    rw [keyProver_second, List.map_cons, List.map_nil, hA.own] at hp
    obtain rfl := List.mem_singleton.1 hp
    exact hO.ownTest

/-- **Every run returns at the key file**, from the thirteen, `ready`, `sealPlain`, `rootedAll` and
`PlanServes`. -/
theorem key_runs (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (Bk : ProverCoinCounts) (hA : K.AtAll)
    (hf0 : K.look0.face = faceAt Xs 0) (hf1 : K.look1.face = faceAt Xs 1) (hb : K.batt = keyBatt Xs)
    (hq : sealPlain (keyFileDescription Xs N Pl) = true) (hroot : rootedAll (keyFileDescription Xs N Pl) (keyProver K) = true)
    {w₀ : W₀} {rc : Rc} {x : KeyInst} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc KeyInst TableKey Unit X₀ X}
    (hR : ready (keyFileDescription Xs N Pl) Bk (keyProver K) w₀ rc x k = .ok R)
    (hP : PlanServes (keyProver K) w₀ rc R)
    (hO : KeyOthersPlay (keyFileDescription Xs N Pl) Bk K R.own R.common)
    (hρ : ρ.due (keyFileDescription Xs N Pl) = true)
    (hsil : silentAt (keyFileDescription Xs N Pl) (keyProver K) w₀ rc x ρ = none) :
    ∃ r, runC (keyFileDescription Xs N Pl) Bk (keyProver K) w₀ rc x k ρ = .ok r :=
  runs_of_blocks _ _ _ w₀ rc x k ρ R hR hs.named.plan hq hroot hP
    (key_blocks_play hs scope Bk hA hf0 hf1 hb R.own R.common hO) hρ hsil

end Key

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.halvesPlay_of_places
#print axioms AtPublicFiles.OfflineRows.find_look0
#print axioms AtPublicFiles.OfflineRows.find_look1
#print axioms AtPublicFiles.OfflineRows.find_batt
#print axioms AtPublicFiles.OfflineRows.lookups_play
#print axioms AtPublicFiles.OfflineRows.batching_plays
#print axioms AtPublicFiles.OfflineRows.key_blocks_play
#print axioms AtPublicFiles.OfflineRows.key_runs
