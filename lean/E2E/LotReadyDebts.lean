-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotReadyDebts.lean: at the key file's offline prover and the written
book, what is left to show so that the frame's ready returns (ReadyDebts,
Johnson/Desc/ProofFile/Honest/Law/ReadyOfSides.lean) is shown, field by field; and so ready returns.

  sidePays_of_laid     a half that is laid (RowLaid, E2E/OfflineLaying.lean) pays (SidePays)
  readyDebts_offline   ReadyDebts at the senders at letters (AtPublicFiles.OfflineRows.offlineValue)
  LotReadyDebts        THE STATEMENT: ReadyDebts at keyProver (AtPublicFiles.KeyStandWalked.offlineValue d),
                       the object that the stands and the accept law's clause AtRunS name
  LotReadyReturns      THE STATEMENT: there ready returns, at every index in range, every rc, every
                       instance and all coins of a run

What it stands on.
 1. The sixteen halves are laid: offline_first_laid, offline_shared_laid, offline_second_laid
    (E2E/OfflineRowsAtValue.lean). These rest on closed lines that Lean's kernel evaluates
    at the written book (within_full, cuts_full, tests_full, rounds_full, full_two, rides_full,
    shape_full and their like): while one of them is red, this file has no proof.
 2. The book's eleven tests: book_passes (E2E/KeyBookThirdNamed.lean).
 3. The join: ready_of_sides, IOP's TRIAL, over Honest/Law/ReadyOfParts.lean: both are on no row of
    the library yet and are laid beside this file in a ride.
Premises.
 1. LookupsStated (E2E/OfflineLaying.lean): THE TWO LOOKUPS' 935 + 920 PARTS STATE WHAT THE BOOK HAS
    FOR THEM. IT IS NOT PROVED IN THIS FILE: fourteen of the sixteen sides are paid here. The other two:
    lookupsStated_offline (E2E/LotLookupsStated.lean) proves it; E2E/LotReadyWhole.lean has both
    statements without it.
 2. The test on the public files says yes (protocolDataWellFormed). It is no more than the laws beneath ask:
    KeyNamed gives it back (live_of_named, E2E/LotReadyGuards.lean).
 3. The files are in scope; offlineDescription returns d; fullPub returns the book's data.
 4. In LotReadyReturns: the index is in range. That a tied input's index is in range is not shown.
That premises 2 to 4 have a member: premises_met (E2E/LotReadyGuards.lean), at the written copy of
the full-size files, where the test's yes is a theorem of the side library.
Beside offline_ready_at_files (E2E/OfflineRowsAtFiles.lean): the same content by another
road (that one unfolds ready by hand; this one goes by ReadyDebts). This one speaks of every d and
K₀ that are returned, and at the term that the stands name. The accept law's clause reads ready at
its own letter for the book: where that is offlineProverCoinCounts, offlineBook_eq turns it to keyBook K₀.
Limits. ready says that the rounds are prepared: no round has been played, and nothing says that a
move returns or that a verifier accepts. The written sizes alone. Nothing on soundness,
completeness, hiding or binding.
-/
import E2E.OfflineRowsAtFiles
import E2E.KeyStandWalked
import Johnson.Desc.ProofFile.Honest.Law.ReadyOfSides

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows.Lots
open ProofFile.Honest
open ProofFile.Honest.Term (matrixInput)
open VerifiableInference.Desc (Block FileDescription Place)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open OnBytes.Slice (GF)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver keyProver_second first_places)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub fullFirst fullShared fullSecond places_named book_passes
  foldedTestPlace omegaTestPlace ownTestPlace)
open AtPublicFiles.KeyValues (WitK)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

section General
variable {S Cl V W Y : Type} {K₀ : KeyPub}

/-- **A half that is laid pays**, at the written book. -/
theorem sidePays_of_laid (hK : fullPub = some K₀) {ch : Nat} (bs : List (Block S Cl))
    (g : Placed V W Y) (hl : RowLaid (keyBook K₀) ch g)
    (ho : ∀ b ∈ bs, b.oracles.length = b.rounds.length)
    (hrows : ∀ b ∈ bs, (b.place, b.rounds.length) ∈ fullFirst ++ fullShared ++ fullSecond) :
    SidePays (keyBook K₀) ch bs g := by
  refine sidePays_of_tests _ _ _ _ fun b hb hp => ?_
  have hr := hrows b hb
  rw [hp] at hr ⊢
  obtain ⟨c, hc⟩ := hl.lends default
  exact ⟨ho b hb, half_rounds hK hl hr, hl.cut, hl.noRow, hl.noEntry, default, c, hc⟩

end General

section Value
variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)

/-- **ReadyDebts at the offline prover's senders, at letters.** hL: the two lookups' parts state what
the book has for them. hd: the prover's named member is in range. hA: the sixteen places. -/
theorem readyDebts_offline {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀)
    (hL : LookupsStated K₀ (offlineValue K' Xs N Pl f g inR d ent groups first))
    (hd : inR d = true) (hA : (offlineValue K' Xs N Pl f g inR d ent groups first).AtAll) :
    ReadyDebts (keyFileDescription Xs N Pl) (keyBook K₀)
      (keyProver (offlineValue K' Xs N Pl f g inR d ent groups first)) := by
  obtain ⟨r1, r2, r3⟩ := places_named scope hs.named
  obtain ⟨p1, p2, p3⟩ := planOk_all hs.named.plan
  have mem₁ : ∀ b ∈ (keyFileDescription Xs N Pl).first.blocksInOrder,
      (b.place, b.rounds.length) ∈ fullFirst ++ fullShared ++ fullSecond := fun b hb =>
    List.mem_append_left _ (List.mem_append_left _ (r1 ▸ List.mem_map.2 ⟨b, hb, rfl⟩))
  have mem₂ : ∀ b ∈ (keyFileDescription Xs N Pl).shared.blocksInOrder,
      (b.place, b.rounds.length) ∈ fullFirst ++ fullShared ++ fullSecond := fun b hb =>
    List.mem_append_left _ (List.mem_append_right _ (r2 ▸ List.mem_map.2 ⟨b, hb, rfl⟩))
  have mem₃ : ∀ b ∈ (keyFileDescription Xs N Pl).second.blocksInOrder,
      (b.place, b.rounds.length) ∈ fullFirst ++ fullShared ++ fullSecond := fun b hb =>
    List.mem_append_right _ (r3 ▸ List.mem_map.2 ⟨b, hb, rfl⟩)
  refine ⟨hs.named.plan, AtPublicFiles.KeyThread.placesOk_of_plan hs.named.plan,
    book_passes scope hs.named K₀ hK, ?_, ?_, ?_, ?_, ?_, ?_, hd, ?_, ?_, ?_⟩
  · refine strays_nil fun q hq => ?_
    have hm : q.place ∈ (keyProver (offlineValue K' Xs N Pl f g inR d ent groups first)).first.map
        (·.place) := List.mem_map_of_mem hq
    rw [first_places _ hA.first] at hm
    rw [places_of_rows r1]
    have incl : ∀ p ∈ ([⟨1, none, 1, .K1⟩, ⟨1, none, 2, .K1⟩, ⟨1, some 0, 2, .K3⟩,
        ⟨1, some 1, 2, .K3⟩, ⟨1, none, 5, .K12⟩, ⟨1, none, 13, .K13⟩, ⟨1, none, 14, .K1⟩] :
        List Place), p ∈ fullFirst.map (·.1) := by decide
    exact incl _ hm
  · refine strays_nil fun q hq => ?_
    have hm : q.place ∈ (keyProver (offlineValue K' Xs N Pl f g inR d ent groups first)).shared.map
        (·.place) := List.mem_map_of_mem hq
    rw [AtPublicFiles.KeyFile.keyProver_shared _ hA.splits, hA.onU, hA.onOmega] at hm
    rw [places_of_rows r2]
    have incl : ∀ p ∈ ([K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7,
        K14.place 8, foldedTestPlace, omegaTestPlace] : List Place),
        p ∈ fullShared.map (·.1) := by decide
    exact incl _ hm
  · refine strays_nil fun q hq => ?_
    have hm : q.place ∈ (keyProver (offlineValue K' Xs N Pl f g inR d ent groups first)).second.map
        (·.place) := List.mem_map_of_mem hq
    rw [keyProver_second, List.map_cons, List.map_nil, hA.own] at hm
    rw [places_of_rows r3]
    have incl : ∀ p ∈ ([ownTestPlace] : List Place), p ∈ fullSecond.map (·.1) := by decide
    exact incl _ hm
  · rw [twice_eq, first_places _ hA.first]
    decide
  · rw [twice_eq, AtPublicFiles.KeyFile.keyProver_shared _ hA.splits, hA.onU, hA.onOmega]
    decide
  · rw [twice_eq, keyProver_second, List.map_cons, List.map_nil, hA.own]
    decide
  · exact fun _ h hh _ => sidePays_of_laid hK _ h
      (offline_first_laid K' Xs N Pl f g inR d ent groups first hs scope hK hL h hh)
      (fun b hb => (shaped_parts (p1 b hb).2).1) mem₁
  · exact fun _ h hh _ => sidePays_of_laid hK _ h
      (offline_shared_laid K' Xs N Pl f g inR d ent groups first hs scope hK h hh)
      (fun b hb => (shaped_parts (p2 b hb).2).1) mem₂
  · exact fun _ h hh _ => sidePays_of_laid hK _ h
      (offline_second_laid K' Xs N Pl f g inR d ent groups first hs scope hK h hh)
      (fun b hb => (shaped_parts (p3 b hb).2).1) mem₃

end Value

/-- **The debts.** -/
def LotReadyDebts : Prop :=
  ∀ {Z : PublicFiles} {description : OfflineDescription} {K₀ : KeyPub}, protocolDataWellFormed (asDescriptionFiles Z) = true →
    offlineDescription Z = .ok description → InScope Z = true → fullPub = some K₀ →
    LookupsStated K₀ (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) description) →
    ReadyDebts (keyFileDescription description.source description.numbers description.later) (keyBook K₀)
      (keyProver (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) description))

/-- **Ready returns.** -/
def LotReadyReturns : Prop :=
  ∀ {Z : PublicFiles} {description : OfflineDescription} {K₀ : KeyPub}, protocolDataWellFormed (asDescriptionFiles Z) = true →
    offlineDescription Z = .ok description → InScope Z = true → fullPub = some K₀ →
    LookupsStated K₀ (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) description) →
    ∀ (w₀ : FullSizeMatrix) (rc : (protocolAtFiles Z).EncodingRandomness) (x : KeyInst) (k : Coins (keyBook K₀)),
      matrixInput.inRange w₀ = true →
      ∃ R, ready (keyFileDescription description.source description.numbers description.later) (keyBook K₀)
        (keyProver (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) description)) w₀ rc x k = .ok R

theorem lotReadyDebts : LotReadyDebts := by
  intro Z description K₀ live hd scope hK hL
  have hs := AtPublicFiles.AtFiles.HonestTerm.sourced_of_ok live hd
  exact readyDebts_offline _ description.source description.numbers description.later _ _ _ _ _ _ _
    hs scope hK hL dummy_in_range (senderValue_atAll hs scope)

theorem lotReadyReturns : LotReadyReturns := by
  intro Z description K₀ live hd scope hK hL w₀ rc x k hin
  exact ready_of_sides (lotReadyDebts live hd scope hK hL) hin rfl rc k

end AtPublicFiles.OfflineRows.Lots

#print axioms AtPublicFiles.OfflineRows.Lots.sidePays_of_laid
#print axioms AtPublicFiles.OfflineRows.Lots.readyDebts_offline
#print axioms AtPublicFiles.OfflineRows.Lots.lotReadyDebts
#print axioms AtPublicFiles.OfflineRows.Lots.lotReadyReturns
