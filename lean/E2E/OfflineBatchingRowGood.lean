-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineBatchingRowGood.lean: the field `good` of `OwedRest` (E2E/OfflineClauses.lean) at the row of
the key file's batching: `goodAt` at the muted row, at the key file's own description, at the written
book, in scope, at any letters K that bear the key file's places and the description's numbers of
the batching, and at any lists of simulators whose list for the batching is `K13.k13Sims`.

  `columns_full`, `batching_columns`   the written shape has 18 column variables (the kernel); in scope
                         so has the batching
  `batching_stretch_full`   whose coins the sumcheck's part spends, by the written book (the kernel)
  `batt_at_value`        `GoodAt` at the batching's row, `Side.fits` a premise
  `batching_good`        `GoodAt` at the batching's row with no premise on `Side.fits`
  `batching_row_goodAt`, `batching_row_good_mute`   the row; it in the form of the field's first clause
  `membersOf_length`     a list of parts is cut into as many members as it has parts
  `batching_row_there`   A TEST OF EMPTINESS: the first list has a row at the place, it has a side, and the
                         side has two members

What it leans on. `KeySourced`, scope, the written book's list of owners (`owners_full`, by the kernel).

Limits. `A` and `B` are false at a muted row, so `plays` and `acc` are vacuous. `exact` is one part at a
time and the spender's half alone: at the sumcheck's part it is over 37 coins drawn uniformly for the
one stretch that the part spends, which it states under the name of the index-mask message's run. THAT
THIS STRETCH IS UNIFORM AND INDEPENDENT OF WHAT ITS OWNER SHOWS IS NOT SHOWN AND NOT ASSUMED HERE: it is
the field `fresh` at the stretch's owner, at this part; by the written book that owner is the sending of
the index masks (`batching_stretch_full`). `fresh` at the batching's own parts holds because
no part spends their coins: they own none, and the field carries nothing there. The statements stand at
every reader of the index and every pile, right or wrong. Nothing on any property.
-/
import E2E.OfflineBatchingFields
import E2E.OfflineGoodAt
import E2E.KeyPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Source LaterPlaces descriptionFromSource)
open VerifiableInference.Desc.K13 (battRounds)
open OnBytes (TableKey)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver keyProver_first)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull idxPlace battPlace)
open AtPublicFiles.KeyValues (keyBatt oneOf)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription five_sourced)
open VerifierAndGoals (PublicFiles InScope)

/-- The written shape has 18 column variables. By evaluation. -/
theorem columns_full : Lk6.AtPlan.keyFull.once.shape.kCol = 18 := by decide +kernel

/-- **By the written book the batching's sumcheck spends one stretch: 37 coins of the extension field,
of the sending of the index masks, once; and the batching's quiet part is handed nothing.** By
evaluation. -/
theorem batching_stretch_full : atFull (fun K =>
    (((keyBook K).ahead.filter fun e => e.spender == ⟨battPlace, 1⟩).map
      fun e => (e.owner, e.once, e.count.f, e.count.e)) == [(⟨idxPlace, 0⟩, true, 0, 37)] &&
    ((keyBook K).ahead.filter fun e => e.spender == ⟨battPlace, 0⟩).isEmpty) = true := by
  decide +kernel

/-- In scope the batching has 18 column variables. -/
theorem batching_columns {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) : (keyBatt Xs).lin.kCol = 18 := by
  obtain ⟨-, -, el, -, -⟩ := five_sourced hs scope
  show (oneOf Xs).lin.kCol = 18
  rw [el]
  exact columns_full

section Value
variable {W₀ Rc Pb Wk : Type}

/-- **The batching's row.** -/
theorem batt_at_value (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces) (f : W₀ → Weights)
    {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) (pile : K13.PileOf KeyInst)
    (fs : List (Fall (keyFileDescription Xs N Pl).S₁))
    (σ : Side (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc KeyInst Unit)
      (Local W₀ Rc KeyInst Unit) Unit Pb)
    (hσ : Side.seated (keyFileDescription Xs N Pl).first.blocksInOrder battPlace
      (K13.k13Pairs f pile (AtPublicFiles.KeyValues.keyBatt Xs)) fs = some σ)
    (hf : σ.fits = true)
    (On : (u : Member (Local W₀ Rc KeyInst Unit) (Local W₀ Rc KeyInst Unit) Unit Pb) →
      CsAll u.part.carries → Mid (Local W₀ Rc KeyInst Unit) Unit → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    GoodAt Xs N Pl K₀ σ On bud := fun pre φ chain firstTree =>
  batt_row_good (batching_columns hs scope) f pile hK batching_owns_none fs σ hσ hf pre φ _ chain
    firstTree On bud

/-- **`GoodAt` at the batching's row**, `Side.fits` shown. -/
theorem batching_good {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub} (hK : fullPub = some K₀)
    (f : W₀ → Weights) (pile : K13.PileOf KeyInst) (fs : List (Fall (keyFileDescription Xs N Pl).S₁))
    (σ : Side (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl (Local W₀ Rc KeyInst Unit)
      (Local W₀ Rc KeyInst Unit) Unit Pb)
    (hσ : Side.seated (keyFileDescription Xs N Pl).first.blocksInOrder battPlace
      (K13.k13Pairs f pile (keyBatt Xs)) fs = some σ)
    (On : (u : Member (Local W₀ Rc KeyInst Unit) (Local W₀ Rc KeyInst Unit) Unit Pb) →
      CsAll u.part.carries → Mid (Local W₀ Rc KeyInst Unit) Unit → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    GoodAt Xs N Pl K₀ σ On bud :=
  batt_at_value Xs N Pl f hs scope hK pile fs σ hσ
    (batching_fits (batching_columns hs scope) f pile fs σ hσ) On bud

/-- **`goodAt` at the muted row of the batching**: the share of `OwedRest.good` at row 6 of the first
chain. The book is a letter that equals the written book, so that it serves at a constant. -/
theorem batching_row_goodAt {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub} (hK : fullPub = some K₀)
    {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces)
    (hb : K.batt = keyBatt Xs) (S : OfflineSimulators) (hS : S.batching = K13.k13Sims K.batt)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).first, L.place = battPlace →
      (L.mute.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription Xs N Pl) 0) .own (keyFileDescription Xs N Pl).first.blocksInOrder
        (orderOf (keyFileDescription Xs N Pl)) 0 0 [] := by
  subst hB
  intro L hL hp
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hL
  have hp' : h.place = battPlace := hp
  rw [keyProver_first] at hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (hA.idx.symm.trans hp') (by decide)
  · exact absurd (hA.msg.symm.trans hp') (by decide)
  · exact absurd (hA.look0.symm.trans hp') (by decide)
  · exact absurd (hA.look1.symm.trans hp') (by decide)
  · exact absurd (hA.rng.symm.trans hp') (by decide)
  · refine goodAt_mute fun σ hσ => ⟨fun _ _ _ _ => False, fun _ _ _ _ => False, ?_⟩
    have hσ' : Side.seated (keyFileDescription Xs N Pl).first.blocksInOrder (K13.k13Place K.batt)
        (partsBeside (K13.k13Row K.weights K.pile K.batt)
          (S.byChain.first (K13.k13Place K.batt))) [] = some σ := hσ
    have es : S.byChain.first (K13.k13Place K.batt) = K13.k13Sims K.batt := by
      rw [hA.batt]
      exact hS
    rw [es, hA.batt, hb] at hσ'
    exact batching_good hs scope hK K.weights K.pile [] σ hσ' _ _ _ _ _ _
  · exact absurd (hA.w.symm.trans hp') (by decide)

/-- **The row in the form of `OwedRest.good`'s first clause.** -/
theorem batching_row_good_mute {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub} (hK : fullPub = some K₀)
    {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces)
    (hb : K.batt = keyBatt Xs) (S : OfflineSimulators) (hS : S.batching = K13.k13Sims K.batt)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.first, L.place = battPlace →
      (L.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).goodAt
        (earlierOf (keyFileDescription Xs N Pl) 0) .own (keyFileDescription Xs N Pl).first.blocksInOrder
        (orderOf (keyFileDescription Xs N Pl)) 0 0 (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.falls₁ := by
  intro L hL hp
  obtain ⟨L', hL', rfl⟩ := List.mem_map.1 hL
  exact batching_row_goodAt hs scope hK hB K hA hb S hS c L' hL' hp

/-- A list of parts is cut into as many members as it has parts. -/
theorem membersOf_length {V W Y Pb' : Type} : ∀ (row : List (Part V W Y × Sim Pb')) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle)),
    (membersOf row j rs).length = row.length
  | [], _, _ => rfl
  | x :: l, j, rs => by
    show (membersOf l (j + 1) (rs.drop x.1.moves.length)).length + 1 = l.length + 1
    rw [membersOf_length l]

/-- **A TEST OF EMPTINESS.** In scope, at letters that bear the first chain's places, the muted rows'
first list has a row at the batching's place, that row has a side at the description's first chain, and
the side has two members: so the sentence above speaks of two parts. -/
theorem batching_row_there {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {Bk : ProverCoinCounts}
    (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit) :
    ∃ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.first, L.place = battPlace ∧
      ∃ σ, (L.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).side (keyFileDescription Xs N Pl).first.blocksInOrder
        [] = some σ ∧ σ.members.length = 2 := by
  obtain ⟨r1, -, -⟩ := AtPublicFiles.KeyBook.places_named scope hs.named
  have hin : battPlace ∈ AtPublicFiles.KeyBook.fullFirst.map (·.1) := by decide
  have hmem : ∀ h ∈ (keyProver K).first, h.place = battPlace → h.parts.length = 2 →
      ∃ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.first, L.place = battPlace ∧
        ∃ σ, (L.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).side (keyFileDescription Xs N Pl).first.blocksInOrder
          [] = some σ ∧ σ.members.length = 2 := by
    intro h hh hp hl
    refine ⟨(rowOf h (S.byChain.first h.place) (c.first h.place)).mute,
      List.mem_map.2 ⟨_, List.mem_map.2 ⟨h, hh, rfl⟩, rfl⟩, hp, ?_⟩
    have hsome := side_isSome (((rowOf (Cl := (keyFileDescription Xs N Pl).Cl) h (S.byChain.first h.place)
      (c.first h.place)).mute).withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0)
      (keyFileDescription Xs N Pl).first.blocksInOrder [] (by
                            show h.place ∈ _
                            rw [hp, places_of_rows r1]
                            exact hin)
    obtain ⟨σ, hσ⟩ := Option.isSome_iff_exists.1 hsome
    refine ⟨σ, hσ, ?_⟩
    have hrow : σ.row = partsBeside h.parts (S.byChain.first h.place) := by
      unfold Lettered.side Side.seated at hσ
      obtain ⟨m, _, rfl⟩ := Option.map_eq_some_iff.1 hσ
      rfl
    unfold Side.members
    rw [membersOf_length, hrow, partsBeside_length, hl]
  exact hmem (K13.proverSideOfClaimCombination K.weights K.pile K.batt) (by rw [keyProver_first]; simp) hA.batt rfl

end Value

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.columns_full
#print axioms AtPublicFiles.OfflineRows.batching_stretch_full
#print axioms AtPublicFiles.OfflineRows.batching_columns
#print axioms AtPublicFiles.OfflineRows.batt_at_value
#print axioms AtPublicFiles.OfflineRows.batching_good
#print axioms AtPublicFiles.OfflineRows.batching_row_goodAt
#print axioms AtPublicFiles.OfflineRows.batching_row_good_mute
#print axioms AtPublicFiles.OfflineRows.membersOf_length
#print axioms AtPublicFiles.OfflineRows.batching_row_there
