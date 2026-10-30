-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineBatchingFields.lean: the fields `fits`, `exact` and `fresh` of `Good` at the row of the key
file's batching, at the key file's own sub-protocol: one quiet part and one masked sumcheck of 18
variables.

  `batt_block`           the sub-protocol at the batching's place declares the batching's rounds
  `k13_exact`            `ExactMember` at the batching's two members
  `batching_owns_none`   no part of the batching is one of the six owners of the written book's entries
  `batching_fits`        `Side.fits` at the batching's row, off the sub-protocol's own rounds: it reads no
                         book
  `batt_row_good`        `Good` at the row, at letters that are false

Each sentence is one part at a time, the spender's half alone, at every reader of the index and every
pile, right or wrong. It says nothing on whether the job is the protocol's. `exact` at the sumcheck's
part is over 37 coins drawn uniformly for the one stretch that the part spends, which it states under
the name of the index-mask message's run. THAT THIS STRETCH IS UNIFORM AND INDEPENDENT OF WHAT ITS OWNER
SHOWS IS NOT SHOWN AND NOT ASSUMED HERE: it is the field `fresh` at the stretch's owner, at this part.
`fresh` at the batching's own parts holds because no part spends their coins: they own none, and the
field carries nothing there. This is not the sentence on the file. Nothing on any property.
-/
import E2E.OfflineMembers
import E2E.OfflineRowFields
import E2E.KeyFirstSends
import Johnson.SendSim.Seat.AtKeyStands

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Block Place Oracle)
open VerifiableInference.Desc.Key (Source LaterPlaces descriptionFromSource firstChain pieces batchTableRows FirstState
  Claim rootsBefore batchRound layRows rangesTest enterRanges leaveRanges sendW)
open VerifiableInference.Desc.K13 (battRounds)
open ProofFile.Honest.Small (ExactMember FreshMember quietPart_exact statedOf)
open ProofFile.Honest.SumLaw (StatedBy statedBy_nums exact_sumPart_field)
open OnBytes.SendSim.Seat (key_places_apart mem_flat_back)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub battPlace)
open AtPublicFiles.KeyValues (keyBatt)

section Blocks
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)

/-- **The sub-protocol at the batching's place** declares the batching's rounds. -/
theorem batt_block {b : Block _ _} (hb : b ∈ (descriptionFromSource X N P).first.blocksInOrder) (hpl : b.place = battPlace) :
    b.rounds = battRounds (keyBatt X) ∧
      b.oracles = List.replicate (2 + (keyBatt X).lin.kCol) [] := by
  have hmem : (batchTableRows (·.keys) X.Y.k.oneTime pieces
      (rootsBefore X.Y.D.1 (batchRound X.Y.D.1)) : Block FirstState Claim) ∈
      (firstChain X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N).back := by
    show _ ∈ [layRows X.Y.k.oneTime, rangesTest (enterRanges X.Y.k.oneTime) leaveRanges N,
      batchTableRows (·.keys) X.Y.k.oneTime pieces _] ++ (sendW X.Y.k.oneTime pieces _ _).toList
    exact List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)))
  have hm := mem_flat_back _ hmem
  have e := List.inj_on_of_nodup_map (key_places_apart X N P) hb hm hpl
  rw [e]
  constructor
  · show (([] ++ []) ++ battRounds (keyBatt X)) ++ [] = _
    rw [List.append_nil]
    rfl
  · show (([] ++ []) ++ List.replicate (2 + (keyBatt X).lin.kCol) []) ++ [] = _
    rw [List.append_nil]
    rfl

end Blocks

section Batching
variable {W₀ Rc Xi Tr Y S Cl Pb : Type}

/-- **`ExactMember` at the batching's two members**, at every On and bud, at 18 variables. -/
theorem k13_exact (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb)
    {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Pb} (weights : W₀ → Weights)
    (pile : K13.PileOf Xi) (p : VerifiableInference.Desc.K13.Where)
    (hrow : σ.row = K13.k13Pairs weights pile p) (hr : σ.block.rounds = battRounds p)
    (ho : σ.block.oracles = List.replicate (2 + p.lin.kCol) []) (hk : p.lin.kCol = 18)
    (chain firstTree : Nat)
    (On : (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y Pb) → CsAll u.part.carries →
      Mid (Local W₀ Rc Xi Tr) Y → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    ∀ u ∈ σ.members, ExactMember φ σ chain firstTree On bud u := by
  have hz : σ.block.rounds.zip σ.block.oracles =
      ({ entry := VerifiableInference.Desc.K13.sigmaEntry p }, []) ::
        ({ entry := VerifiableInference.Desc.K13.epsEntry p }, []) ::
          List.replicate 18 ({ entry := VerifiableInference.Desc.K13.roundEntry p }, []) := by
    rw [hr, ho, hk]
    unfold battRounds
    rw [hk]
    rfl
  have hm : (K13.k13Sum p).moves.length = 19 := by
    unfold K13.k13Sum
    rw [K3.sumPart_moves]
    show VerifiableInference.Desc.K3.roundsOf (K13.k13Shape p.lin.kCol) = 19
    rw [hk]
    rfl
  have hs : VerifiableInference.Desc.Part.MaskedSum.shapeOk (K13.k13Shape p.lin.kCol) = true := by
    rw [hk]
    rfl
  intro u hu
  unfold Side.members at hu
  rw [hrow, hz] at hu
  obtain ⟨i, x, hx, rfl⟩ := membersOf_spec _ 0 _ u hu
  match i, hx with
  | 0, hx =>
    obtain rfl := Option.some.inj hx
    refine quietPart_exact φ σ chain firstTree On bud _ 1 _ _ ?_
    show statedOf [(({ entry := VerifiableInference.Desc.K13.sigmaEntry p } : Fmt.DeclaredRound),
      ([] : List Oracle))] = [([], [])]
    obtain ⟨a1, -, -⟩ : StatedBy [0] [(({ entry := VerifiableInference.Desc.K13.sigmaEntry p } :
        Fmt.DeclaredRound), ([] : List Oracle))] :=
      statedBy_nums _ _ rfl fun r hr => by rw [List.mem_singleton.1 hr]
    show [(_, _)] = _
    rw [a1]
    rfl
  | 1, hx =>
    obtain rfl := Option.some.inj hx
    have hl : ((K13.k13Sum p).lift (V := Local W₀ Rc Xi Tr) (W := Local W₀ Rc Xi Tr) (X := Y)
        (fun _ => ()) (K13.k13Ask weights pile)
        (fun _ => ()) (fun x _ => x)).moves.length = 19 := (List.length_map _).trans hm
    refine exact_sumPart_field φ σ chain firstTree On bud (fun _ => ()) (K13.k13Ask weights pile)
      (fun _ => ()) (fun y _ => y) (fun _ _ => rfl) (fun _ => rfl) _ _ _ hs _ ?_ rfl _ _
    refine statedBy_nums _ _ ?_ ?_
    · show List.map _ (List.take _ (List.drop 1 _)) = _
      rw [hl]
      show _ = List.map _ (scalarsOf (K13.k13Shape p.lin.kCol))
      rw [hk]
      rfl
    · intro r hr'
      have hr'' := List.mem_of_mem_take hr'
      have hr''' := List.mem_of_mem_drop hr''
      simp only [List.mem_cons, List.mem_replicate] at hr'''
      rcases hr''' with rfl | rfl | h
      · rfl
      · rfl
      · rw [h.2]
  | i + 2, hx => cases hx

end Batching

/-- No part of the batching is an owner of an entry of the written book: none of the six owners stands
at a place of its kind. -/
theorem batching_owns_none (j : Nat) : (⟨battPlace, j⟩ : Addr) ∉ bookOwners := by
  intro h
  exact (by decide : ∀ a ∈ bookOwners, a.place ≠ battPlace) _ h rfl


section Fits
variable {W₀ Rc Xi Tr Y' Pb : Type}

/-- **The batching's row passes the frame's test on a side**, at the key file's sub-protocol. It reads
no book. -/
theorem batching_fits {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    (hk : (keyBatt X).lin.kCol = 18) (weights : W₀ → Weights) (pile : K13.PileOf Xi)
    (fs : List (Fall (descriptionFromSource X N P).S₁))
    (σ : Side (descriptionFromSource X N P).S₁ (descriptionFromSource X N P).Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y' Pb)
    (hσ : Side.seated (descriptionFromSource X N P).first.blocksInOrder battPlace (K13.k13Pairs weights pile (keyBatt X)) fs =
      some σ) : σ.fits = true := by
  have hrow : σ.row = K13.k13Pairs weights pile (keyBatt X) := by
    unfold Side.seated at hσ
    obtain ⟨m, _, rfl⟩ := Option.map_eq_some_iff.1 hσ
    rfl
  have hbp : σ.block.place = battPlace := OnBytes.SendSim.At.place_of_seated hσ
  have hbm : σ.block ∈ (descriptionFromSource X N P).first.blocksInOrder := OnBytes.SendSim.Seat.block_of_seated hσ
  obtain ⟨e1, e2⟩ := batt_block X N P hbm hbp
  have hm : (K13.k13Sum (keyBatt X)).moves.length = 19 := by
    unfold K13.k13Sum
    rw [K3.sumPart_moves]
    show VerifiableInference.Desc.K3.roundsOf (K13.k13Shape (keyBatt X).lin.kCol) = 19
    rw [hk]
    rfl
  have hl : ((K13.k13Sum (keyBatt X)).lift (V := Local W₀ Rc Xi Tr) (W := Local W₀ Rc Xi Tr)
      (X := Y') (fun _ => ())
      (K13.k13Ask weights pile) (fun _ => ()) (fun x _ => x)).moves.length = 19 :=
    (List.length_map _).trans hm
  have hr : σ.block.rounds.length = 20 := by
    rw [e1]
    unfold battRounds
    rw [hk]
    rfl
  unfold Side.fits
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hrow, hbp]
    rfl
  · rw [hr]
    unfold Side.half
    rw [hrow]
    show 0 + 1 + ((K13.k13Sum (keyBatt X)).lift (V := Local W₀ Rc Xi Tr)
      (W := Local W₀ Rc Xi Tr) (X := Y') (fun _ => ())
      (K13.k13Ask weights pile) (fun _ => ()) (fun x _ => x)).moves.length = 20
    rw [hl]
  · rw [hr, e2, hk]
    rfl

end Fits

section Rows
variable {W₀ Rc Xi Tr Y S' Cl' V' W' Y' Pb Wk : Type}

/-- **`Good` at the batching's row**, at the key file's sub-protocol at the written book. -/
theorem batt_row_good {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}
    (hk : (keyBatt X).lin.kCol = 18) (weights : W₀ → Weights) (pile : K13.PileOf Xi)
    {K₀ : KeyPub} (hK : fullPub = some K₀)
    (hown : ∀ j, (⟨battPlace, j⟩ : Addr) ∉ bookOwners) (fs : List (Fall (descriptionFromSource X N P).S₁))
    (σ : Side (descriptionFromSource X N P).S₁ (descriptionFromSource X N P).Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y' Pb)
    (hσ : Side.seated (descriptionFromSource X N P).first.blocksInOrder battPlace (K13.k13Pairs weights pile (keyBatt X)) fs =
      some σ)
    (hf : σ.fits = true) (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Pb) (ord : List Place)
    (chain firstTree : Nat)
    (On : (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Y' Pb) → CsAll u.part.carries →
      Mid (Local W₀ Rc Xi Tr) Y' → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    Good pre φ σ (keyBook K₀) ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      On bud := by
  have hrow : σ.row = K13.k13Pairs weights pile (keyBatt X) := by
    unfold Side.seated at hσ
    obtain ⟨m, _, rfl⟩ := Option.map_eq_some_iff.1 hσ
    rfl
  have hbp : σ.block.place = battPlace := OnBytes.SendSim.At.place_of_seated hσ
  have hbm : σ.block ∈ (descriptionFromSource X N P).first.blocksInOrder := OnBytes.SendSim.Seat.block_of_seated hσ
  obtain ⟨e1, e2⟩ := batt_block X N P hbm hbp
  refine good_of_row hf (k13_exact φ weights pile _ hrow e1 e2 hk chain firstTree On bud)
    (fresh_of_owns_none φ σ (keyBook K₀) ord bud fun u _ q => ?_)
  rw [hbp]
  exact spent_none hK (hown _) q

end Rows

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.batt_block
#print axioms AtPublicFiles.OfflineRows.k13_exact
#print axioms AtPublicFiles.OfflineRows.batching_owns_none
#print axioms AtPublicFiles.OfflineRows.batching_fits
#print axioms AtPublicFiles.OfflineRows.batt_row_good
