-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineLookupMembers.lean: A TEST OF EMPTINESS for E2E/OfflineLookupRowsAtValue.lean: the sides of which
its sentences speak have 935 and 920 members.

  `members_length`           a side has as many members as its row has parts (`membersOf_length`,
                             E2E/OfflineBatchingRowGood.lean)
  `lookup_members_counted`   in scope, at letters that bear the first chain's places and the
                             description's two faces: every side of the muted row at lookup 0's place
                             has 935 members, at lookup 1's place 920, whatever the simulators
  `lookup_members_at_value`  the same at the offline prover's own senders

Numbers of members alone. Nothing on any property.
-/
import E2E.OfflineLookupRowsAtValue
import E2E.OfflineLookupCounts
import E2E.OfflineBatchingRowGood

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (Place Oracle)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open OnBytes (TableKey)
open OnBytes.Slice (GF)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeyBook (lookPlace)
open AtPublicFiles.KeyValues (WitK faceAt)
open AtPublicFiles.KeyValueHolds (valueAt)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open VerifierAndGoals (PublicFiles InScope)

section General
variable {S Cl V W Y Pb : Type}

/-- A side has as many members as its row has parts. -/
theorem members_length (σ : Side S Cl V W Y Pb) : σ.members.length = σ.row.length :=
  membersOf_length _ _ _

end General

section Letters
variable {W₀ Rc Wk : Type}

/-- **The two sides have 935 and 920 members.** -/
theorem lookup_members_counted {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}
    (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {Bk : ProverCoinCounts}
    (K : KeyParts W₀ Rc Unit Unit Wk) (hA : K.AtPlaces) (hf0 : K.look0.face = faceAt Xs 0)
    (hf1 : K.look1.face = faceAt Xs 1) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.first, ∀ σ,
      (L.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).side (keyFileDescription Xs N Pl).first.blocksInOrder [] =
        some σ →
      (L.place = lookPlace 0 → σ.members.length = 935) ∧
        (L.place = lookPlace 1 → σ.members.length = 920) := by
  obtain ⟨n0, n1, -⟩ := lookup_parts_counted hs scope
  intro L hL σ hσ
  obtain ⟨L', hL', rfl⟩ := List.mem_map.1 hL
  obtain ⟨h, hh, rfl⟩ := List.mem_map.1 hL'
  have hσ' : Side.seated (keyFileDescription Xs N Pl).first.blocksInOrder h.place
      (partsBeside h.parts (S.byChain.first h.place)) [] = some σ := hσ
  have hrow : σ.row = partsBeside h.parts (S.byChain.first h.place) := by
    unfold Side.seated at hσ'
    obtain ⟨m, _, rfl⟩ := Option.map_eq_some_iff.1 hσ'
    rfl
  have hlen : σ.members.length = h.parts.length := by
    rw [members_length, hrow, partsBeside_length]
  have hm : (h.place, h.parts.length) ∈
      (keyProver K).first.map (fun g => (g.place, g.parts.length)) := List.mem_map.2 ⟨h, hh, rfl⟩
  rw [first_counts K, hA.idx, hA.msg, hA.look0, hA.look1, hA.rng, hA.batt, hA.w, hf0, hf1, n0, n1] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rw [hlen]
  constructor
  · intro hp
    have hp' : h.place = lookPlace 0 := hp
    rw [hp'] at hm
    rcases hm with ⟨e, l⟩ | ⟨e, l⟩ | ⟨e, l⟩ | ⟨e, l⟩ | ⟨e, l⟩ | ⟨e, l⟩ | ⟨e, l⟩
    · exact absurd e (by decide)
    · exact absurd e (by decide)
    · exact l
    · exact absurd e (by decide)
    · exact absurd e (by decide)
    · exact absurd e (by decide)
    · exact absurd e (by decide)
  · intro hp
    have hp' : h.place = lookPlace 1 := hp
    rw [hp'] at hm
    rcases hm with ⟨e, l⟩ | ⟨e, l⟩ | ⟨e, l⟩ | ⟨e, l⟩ | ⟨e, l⟩ | ⟨e, l⟩ | ⟨e, l⟩
    · exact absurd e (by decide)
    · exact absurd e (by decide)
    · exact absurd e (by decide)
    · exact l
    · exact absurd e (by decide)
    · exact absurd e (by decide)
    · exact absurd e (by decide)

end Letters

section Value
variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (pU pO : P12) (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat))
  (first : Nat)

/-- **The same at the offline prover's own senders.** -/
theorem lookup_members_at_value {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {Bk : ProverCoinCounts} (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk
        (valueAt K' Xs N Pl f g inR d pU pO ent groups first) S c).mute.first, ∀ σ,
      (L.withField 0 0 (keyFileDescription Xs N Pl).first.blocksInOrder [] 0).side (keyFileDescription Xs N Pl).first.blocksInOrder [] =
        some σ →
      (L.place = lookPlace 0 → σ.members.length = 935) ∧
        (L.place = lookPlace 1 → σ.members.length = 920) :=
  lookup_members_counted hs scope _
    (value_atPlaces K' Xs N Pl f g inR d pU pO ent groups first hs scope) rfl rfl S c

end Value

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.owners_full
#print axioms AtPublicFiles.OfflineRows.members_length
#print axioms AtPublicFiles.OfflineRows.lookup_members_counted
#print axioms AtPublicFiles.OfflineRows.lookup_members_at_value
