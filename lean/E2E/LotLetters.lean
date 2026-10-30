-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotLetters.lean: DEFINITIONS OF THE KEY FILE's LETTERS, IN ONE FILE BENEATH ALL ITS PROOFS. Definitions and abbreviations alone: no theorem. Each stands under the full name and with the
text, the binders and the settings that it had in the file where it lay beside proofs; that file now imports this one. So the file of the key file's letters (AtFullSide/Honest/TheKeyLetters.lean) can stand
on this file alone of ours, and every payer of ours can import that file.

  AtPublicFiles.FirstH.Lots:            `kindFirst` (from E2E/LotKindFirst.lean) · `noTable`, `laterValue` (E2E/LotLaterValue.lean) · `inFirst`, `startFirst`, `walkedFirst` (E2E/LotBegunFirst.lean) ·
                              `joinThread`, `joinSaid` (E2E/LotJoinFirst.lean) · `laidFirst`, `laidSaid` (E2E/LotJoinLaid.lean)
  AtPublicFiles.KeyStandWalked.Lots:    `ttShared` (E2E/LotOpensShared.lean) · `sendersAt`, `ttValue` (E2E/LotSharedAtValue.lean)

THREE NAMED HOLES: this file must import three files that hold proofs beside the definition that is wanted:
  `LookupKeeps`: E2E/Lookup/Key/LookupBehindAndRidesPastAtTheKey.lean.
  `RngYes`: Johnson/Desc/ProofFile/Honest/K12/AtKey/RangesRides.lean.
  `ttPlaced`, `AQ`, `t7K`: E2E/KeyDepthsAt.lean, E2E/KeyDepthsClosed.lean, whose heads call them trials.
Until these three are cut likewise, whoever imports this file has these proofs beneath it.

What each value is: the heads of the files named above. Nothing on soundness, completeness, hiding or binding: names.
-/
import E2E.FirstHSeat
import E2E.WalkedFrom
import E2E.KeyStandWalked
import E2E.KeyTied
import E2E.KeyDepthsClosed
import E2E.Lookup.Key.LookupBehindAndRidesPastAtTheKey
import Johnson.Desc.ProofFile.Honest.K12.AtKey.RangesRides

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

/-! ## 1 From E2E/LotKindFirst.lean -/

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc.Key (FirstState Source)
open AtPublicFiles.Lookup.Key (LookupKeeps)
open ProofFile.Honest.K12.AtKey (RngYes)

/-- **THE TERM.** -/
def kindFirst (Xs : Source) (N : H2U.PlaceNums) : Nat → FirstState → FirstState → Prop
  | 4 | 10 => LookupKeeps
  | 15 => RngYes Xs N
  | _ => fun _ _ => True

end AtPublicFiles.FirstH.Lots

/-! ## 2 From E2E/LotLaterValue.lean -/

section
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc (Place)
open AtPublicFiles.AtFiles (keyFileDescription FullSizeMatrix protocolAtFiles relKeyZ)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription)
open AtPublicFiles.KeyBook (KeyPub keyBook)
open VerifierAndGoals (PublicFiles)
open ProofFile.Honest

/- As in E2E/KeyTied.lean: the search for this instance runs out of time. -/
local instance (priority := high) lotLettersPad : Nonempty AtPublicFiles.Committed.PadZ :=
  AtPublicFiles.Committed.pads_nonempty OnBytes.Slice.frS 402653181

/-- A table that shows nothing, at no place of the file. -/
def noTable : Place × Table := (⟨0, none, 0, .frame⟩, ⟨0, 0, fun _ i => i.elim0⟩)

/-- **THE VALUE.** -/
def laterValue (Z : PublicFiles) (d : OfflineDescription) (K₀ : KeyPub) :
    LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness where
  msg := fun _ _ _ _ _ _ _ => 0
  fixedMsg := fun _ => 0
  ends := fun _ _ _ x _ =>
    ((keyFileDescription d.source d.numbers d.later).start₁ ((keyFileDescription d.source d.numbers d.later).pub x),
      (keyFileDescription d.source d.numbers d.later).start₂ ((keyFileDescription d.source d.numbers d.later).pub x))
  kind₁ := kindFirst d.source d.numbers
  kind₂ := fun _ _ _ => True
  kind₃ := fun _ _ _ => True
  Rel := relKeyZ Z AtPublicFiles.AtFiles.inRange
  enc := fun v => v
  rad := 0
  table₁ := fun _ _ _ _ => noTable
  table₂ := fun _ _ _ _ => noTable
  table₃ := fun _ _ _ _ => noTable

end AtPublicFiles.FirstH.Lots

end

end

/-! ## 3 From E2E/LotBegunFirst.lean and E2E/LotJoinFirst.lean -/

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc (OpenedColumn)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces)
open AtPublicFiles.KeyFile (KeyParts In1 keyProver)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription matrixReader)
open AtPublicFiles.KeyStandWalked (offlineValue)
open AtPublicFiles.KeyBook (KeyPub keyBook)
open VerifierAndGoals (PublicFiles)
open ProofFile.Honest

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (K : KeyParts W₀ Rc X₀ X' Wk) (f : W₀ → Weights) (Q : LaterFill Bk W₀ Rc) (w₀ : W₀) (rc : Rc)
  (x : Xi)

/-- The first chain's input at this instance. -/
abbrev inFirst : In1 W₀ Rc := ⟨w₀, rc, x, ()⟩

/-- **The state in which the first chain's run begins, with the field opened at the start**: none at the
frame's play, some [] at the walk. -/
abbrev startFirst (o : Option (List OpenedColumn)) (v : In1 W₀ Rc) : Mid (In1 W₀ Rc) X' :=
  ⟨⟨v, [], (keyProver K).own₀⟩, [], [], o⟩

/-- **The letter**: what the thread's steps reach from the walk's start. -/
abbrev walkedFirst : Nat → Coins Bk → Mid (In1 W₀ Rc) X' → Prop :=
  WalkedFrom (Th Xs N Pl K f Q w₀ rc x) (fun _ m => m = startFirst K (some []) (inFirst w₀ rc x))

end

section
variable {Z : PublicFiles} {K₀ : KeyPub} (d : OfflineDescription)
  (Q : LaterFill (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness)

/-- **U₁: the first chain's thread at an input.** -/
noncomputable abbrev joinThread (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi) :=
  Th d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w.1 w.2.1 x

/-- **S₁: its letter.** -/
noncomputable abbrev joinSaid (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi) :=
  walkedFirst d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader Q w.1 w.2.1 x

end

end AtPublicFiles.FirstH.Lots

/-! ## 4 From E2E/LotJoinLaid.lean -/

section
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc.Key (Xi)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription)
open AtPublicFiles.KeyBook (KeyPub)
open VerifierAndGoals (PublicFiles)

variable (Z : PublicFiles) (d : OfflineDescription) (K₀ : KeyPub)

/-- **U₁, laid**: the first chain's thread with no letter left. -/
abbrev laidFirst (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi) :=
  joinThread d (laterValue Z d K₀) w x

/-- **S₁, laid.** -/
abbrev laidSaid (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi) :=
  joinSaid d (laterValue Z d K₀) w x

end AtPublicFiles.FirstH.Lots

end

end

/-! ## 5 From E2E/LotOpensShared.lean -/

section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace AtPublicFiles.KeyStandWalked.Lots
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyBook (KeyPub keyBook)
open AtPublicFiles.KeyDepthsAt (ttPlaced)
open AtPublicFiles.KeyDepthsClosed (AQ t7K)
open AtPublicFiles.KeyLay (JKU JKO)

variable {W₀ Rc X₀ : Type} (K₀ : KeyPub)
  (bs : List (Block St Unit)) (st : W₀ → Rc → ℕ → ℕ → Option (List UInt64))
  (wts : Common W₀ Rc TableKey → Weights) (rnd : Common W₀ Rc TableKey → TableRand) (own₀ : X₀)

/-- **The value of the letter tt**: IOP's. -/
abbrev ttShared : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table :=
  ttPlaced K₀ (JKU (X := X₀) AQ bs st wts rnd) (JKO (X := X₀) AQ bs wts rnd) own₀
    (t7K K₀ bs wts rnd own₀)

end AtPublicFiles.KeyStandWalked.Lots

end

end

/-! ## 6 From E2E/LotSharedAtValue.lean -/

section
set_option synthInstance.maxHeartbeats 400000
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.KeyStandWalked.Lots
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineSenders)
open AtPublicFiles.KeyBook (KeyPub keyBook)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyValues (WitK)
open AtPublicFiles.KeyLay (bsOf stOf wtOf rdOf)

variable (Z : VerifierAndGoals.PublicFiles) (d : OfflineDescription) (K₀ : KeyPub)

/-- The offline prover's senders, of which the two halves are made. -/
abbrev sendersAt : KeyParts FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Unit Unit WitK := offlineSenders (files := Z) d

/-- **The letter tt at the real value.** -/
abbrev ttValue : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table :=
  ttShared K₀ (bsOf (sendersAt Z d)) (stOf (sendersAt Z d)) (wtOf (sendersAt Z d))
    (rdOf (sendersAt Z d)) ()

end AtPublicFiles.KeyStandWalked.Lots

end

end
