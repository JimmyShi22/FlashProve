-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotLaterValue.lean: A PROPOSAL: ONE CLOSED VALUE of `AtPublicFiles.FirstH.LaterFill` (E2E/FirstHFill.lean), the letters Q of the key
file's first thread `Th`, at three public files Z, a description d of them and the written book's data K₀; and its tests.

  `noTable`: a table that shows nothing, at no place of the file.
  `laterValue Z d K₀`: THE VALUE.
      kind₁ := kindFirst d.source d.numbers (E2E/LotKindFirst.lean) · Rel := relKeyZ Z inRange (E2E/KeyTied.lean): the relation of the
      frame's `Tied` at the offline prover, at "the matrix is in range" · table₁ := noTable · msg, fixedMsg := 0 ·
      ends := the description's two starts · kind₂, kind₃ := True · enc := the identity · rad := 0 · table₂, table₃ := noTable.
  `rel_inRange`, `rel_passes`: WHAT Rel GIVES OF THE INDEX: the matrix is in range (`Flat.InRange`), and so it passes the prover's own
      test (`matrixInput.inRange`): what the lookups' values and `ready` ask of a valid input.
  `th_reads_five`: WHICH FIELDS `Th` READS AT ALL: two values of Q that agree in msg, fixedMsg, kind₁, Rel and table₁ give ONE thread:
      ends, kind₂, kind₃, enc, rad, table₂, table₃ are read by no clause of `Th`.
  `LotLaterValue`: THE TESTS, as one statement: the three arms of kind₁ · Rel is the relation of `Tied` · and AT THIS Q: what
      the first chain opens; `Enters₁`, from that relation and a return of `ready`; the five at 14; `FitsAt`; and
      BehindS, RidesPastS at 4, 10.

WHO READS WHAT, by reading (KeyRest.lean's rest₁, rest₂, rest₃; FirstHFill.lean's fillH, tbH):
- kind₁: `keeps` at 4, 10, 15. Rel: `valid`. These two bear content.
- table₁: `tbH` at a source that is none of own 0 to 5. The first chain sends six trees and takes none over: no such source is in
  `hand` at any border. That no round opens one goes through at this Q (as at every Q).
- msg n, fixedMsg n at n ≥ 3: they stand in the witness's term, and there at THE EMPTY LIST: `Th`'s witness is `L.wit k w₀ rc h []`, and
  so is the first half of the last thread's (`wit₃`, E2E/KeyDoorItems.lean): the shared chain's challenges are not handed to it. So
  whatever is laid there is not the run's message. By the table's own list (`msgsOf₁`, Johnson/Desc/Key/KeyBorders.lean) no item of the first chain
  reads a message from 3 on: READ OFF THAT LIST, NOT PROVED HERE.
- The other seven: the threads `laid₂`, `laid₃` alone (E2E/KeyRest.lean). The offline socket's shared and last threads are `threadAt` and a thread
  over `lettersLastKey`, which read no `KeyFill` but for `wit₃`'s first half and `firstSays`.

Limits.
- A PROPOSAL FOR ANOTHER HOUSE's LETTER. AT `laid₂` | `laid₃` THIS VALUE IS NOT FIT: kind₂, kind₃ := True would make RidesPast there false, and
  ends is no end of a run. Whoever spends these two threads must lay the seven anew.
- The tests are calls of other files' statements, each general in Q but for Rel and kind₁: that they go through says that the value has the
  right TYPE and meets these two premises, no more.
- `Enters₁` is under "ready returns". No stand of `Th` beyond border 0 is shown.
- The written sizes alone: in scope, at a sourced description.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.LotLetters
import E2E.LotKindFirst
import E2E.LotsAtValue
import E2E.LotEntersFirstAtTerm
import E2E.KeyTied
import E2E.KeyRangeOne

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces)
open AtPublicFiles.KeyFile (KeyParts In1 keyProver)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription FullSizeMatrix protocolAtFiles relKeyZ)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription matrixReader)
open AtPublicFiles.KeyStandWalked (offlineValue)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.Lookup.Key (LookupKeeps)
open ProofFile.Honest.K12.AtKey (RngYes)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest

/- As in E2E/KeyTied.lean: the search for this instance runs out of time. -/
local instance (priority := high) laterValuePad : Nonempty AtPublicFiles.Committed.PadZ :=
  AtPublicFiles.Committed.pads_nonempty OnBytes.Slice.frS 402653181

/-- **Where Rel holds the matrix is in range.** -/
theorem rel_inRange {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub} {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness}
    {x : Xi} (h : (laterValue Z d K₀).Rel w₀ rc x) : VerifiableInference.OnPublicFiles.Flat.InRange w₀ := by
  obtain ⟨_, _, hok⟩ := (AtPublicFiles.AtFiles.relKey_iff (AtPublicFiles.Committed.AZ Z) AtPublicFiles.Committed.PadZ
    (AtPublicFiles.Committed.holdZ Z) AtPublicFiles.AtFiles.inRange w₀ rc x).1 h
  exact hok

/-- **Where Rel holds the matrix passes the prover's own test.** -/
theorem rel_passes {Z : PublicFiles} {d : OfflineDescription} {K₀ : KeyPub} {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness}
    {x : Xi} (h : (laterValue Z d K₀).Rel w₀ rc x) :
    ProofFile.Honest.Term.matrixInput.inRange w₀ = true :=
  (AtPublicFiles.AtFiles.HonestTerm.inRange_iff w₀).2 (rel_inRange h)

/-- **`Th` reads five of the twelve fields.** -/
theorem th_reads_five {Bk : ProverCoinCounts} {W₀ Rc X₀ X' Wk : Type} (Xs : Source) (N : H2U.PlaceNums)
    (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X' Wk) (f : W₀ → Weights) (Q Q' : LaterFill Bk W₀ Rc)
    (w₀ : W₀) (rc : Rc) (x : Xi) (h1 : Q.msg = Q'.msg) (h2 : Q.fixedMsg = Q'.fixedMsg)
    (h3 : Q.kind₁ = Q'.kind₁) (h4 : Q.Rel = Q'.Rel) (h5 : Q.table₁ = Q'.table₁) :
    Th Xs N Pl K f Q w₀ rc x = Th Xs N Pl K f Q' w₀ rc x := by
  cases Q
  cases Q'
  cases h1
  cases h2
  cases h3
  cases h4
  cases h5
  rfl

/-- **The tests of the value.** -/
def LotLaterValue : Prop :=
  ∀ (Z : PublicFiles) (d : OfflineDescription) (K₀ : KeyPub),
    ((laterValue Z d K₀).kind₁ 4 = LookupKeeps ∧ (laterValue Z d K₀).kind₁ 10 = LookupKeeps ∧
      (laterValue Z d K₀).kind₁ 15 = RngYes d.source d.numbers) ∧
    (laterValue Z d K₀).Rel = relKeyZ Z AtPublicFiles.AtFiles.inRange ∧
    (KeySourced Z d.source d.numbers d.later → InScope Z = true → fullPub = some K₀ →
      ∀ (w₀ : FullSizeMatrix) (rc : (protocolAtFiles Z).EncodingRandomness) (x : Xi),
        -- what the first chain opens
        ((∀ n, n < 20 → (ThValue d (laterValue Z d K₀) w₀ rc x).opensAvailable n = true) ∧
          (∀ n, n ≤ 19 → ∀ k m, DepthsAt (ThValue d (laterValue Z d K₀) w₀ rc x) n k m) ∧
          ∀ j, Fmt.TreeSource.own j ∉ (ThValue d (laterValue Z d K₀) w₀ rc x).taken) ∧
        -- `Enters₁`, from that relation and a return of `ready`
        (relKeyZ Z AtPublicFiles.AtFiles.inRange w₀ rc x → ∀ k R,
          ready (keyFileDescription d.source d.numbers d.later) (keyBook K₀)
            (keyProver (offlineValue (files := Z) d)) w₀ rc x k = .ok R →
          Enters₁ (keyFileDescription d.source d.numbers d.later) (keyProver (offlineValue (files := Z) d))
            (ThValue d (laterValue Z d K₀) w₀ rc x) w₀ rc x k R) ∧
        -- the five at 14; `FitsAt`; BehindS, RidesPastS at 4, 10
        ∀ (Said : Nat → Coins (keyBook K₀) → Mid (In1 FullSizeMatrix (protocolAtFiles Z).EncodingRandomness) Unit → Prop)
          (fall : Nat → FirstState → List Fmt.Drawn → Option String),
          (PlaysS (ThValue d (laterValue Z d K₀) w₀ rc x) Said 14 ∧
            BehindS (ThValue d (laterValue Z d K₀) w₀ rc x) Said 14 ∧
            ExchangeS (ThValue d (laterValue Z d K₀) w₀ rc x) Said 14 ∧
            RidesPastS (ThValue d (laterValue Z d K₀) w₀ rc x) Said 14 ∧
            AcceptedS (ThValue d (laterValue Z d K₀) w₀ rc x) Said fall 14) ∧
          (∀ b ∈ [4, 10, 14, 18], FitsAt (ThValue d (laterValue Z d K₀) w₀ rc x) b) ∧
          ∀ b ∈ [4, 10], BehindS (ThValue d (laterValue Z d K₀) w₀ rc x) Said b ∧
            RidesPastS (ThValue d (laterValue Z d K₀) w₀ rc x) Said b)

theorem lotLaterValue : LotLaterValue := by
  intro Z d K₀
  refine ⟨⟨rfl, rfl, rfl⟩, rfl, fun hs scope hK w₀ rc x => ⟨?_, ?_, fun Said fall => ⟨?_, ?_, ?_⟩⟩⟩
  · exact opensFirst_atValue d (laterValue Z d K₀) w₀ rc x hs scope hK
  · exact fun rel k R hR => entersFirst_atTerm d hs scope (laterValue Z d K₀) w₀ rc x rel k R hR
  · exact memberFourteen_atValue d (laterValue Z d K₀) w₀ rc x hs scope hK Said fall
  · exact fitsAt_atValue d (laterValue Z d K₀) w₀ rc x hs scope hK
  · exact lotKindFirst d.source d.numbers d.later (offlineValue (files := Z) d) matrixReader
      (laterValue Z d K₀) w₀ rc x hs scope rfl rfl Said

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.rel_inRange
#print axioms AtPublicFiles.FirstH.Lots.rel_passes
#print axioms AtPublicFiles.FirstH.Lots.th_reads_five
#print axioms AtPublicFiles.FirstH.Lots.lotLaterValue
