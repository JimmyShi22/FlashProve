-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineThreadSeams.lean: THE SEAMS between the letters at which the offline prover's debts on acceptance
are stated (`TheLots`, E2E/OfflineJoin.lean: at a tied input with a seed, at a coin of the honest side, at
the prover of bare sides) and the letters at which the field `owed` of `OwedRest` (E2E/OfflineClauses.lean)
asks (at the relation of the key file, at every coin of the book, at the prover of the muted rows).

  `coinOf`, `coinOf_triple`   (a) every coin of a book is the triple that `AtRunS` reads of a coin of the honest side
  `tied_of_relation`         (b) the key file's relation gives a seed at which the input is tied
  `okStart_of_relation`      (b) and the description's test on the instance passes there
  `provers_are_one`          (c) the prover of the bare sides, the offline prover and the prover of the muted rows
                             are one term
  `lots_at_relation`         the three together: from `TheLots`, at every w₀ rc x in the relation: a seed, and at it
                             every premise of a member of `ThreadsP` with the threads' own invariants: `Sits` at the
                             muted rows' prover, `OwesS` and `SaidNext` at the three threads, and at EVERY coin k of
                             the book: `ready` returns, `Enters₁`, `Enters₂`, the letters at the two starts,
                             `DoorBehindS`

The relation shuts out no coin of the committer and no seed: (b) takes the seed that the relation names, and
`tied_offline` (E2E/OfflineAtParts.lean) holds at every index in range, every coin and every seed.

Limits. CONDITIONAL on `TheLots`: no thread is shown here to meet any of its fields. Of `TheLots` the fields that
say yes are spent on the shared chain's law alone (`shared_at_tied` takes them); no acceptance is concluded.
At the written book `keyBook K₀`; `offlineProverCoinCounts` is that book where `fullPub = some K₀` (`offlineBook_eq`).
Nothing on any property.
-/
import E2E.OfflineJoin
import E2E.KeyOkStart
import E2E.KeyStoredAtValue
import E2E.OfflineRowsAtFiles
import E2E.KeyExact

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open ProofFile.Honest.Term
open AtPublicFiles.Cut AtPublicFiles.KeyLink AtPublicFiles.KeyFile
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open _root_.Desc.K14 (St)
open ProofFile.Honest.K14 (WitLens)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyStoredTie (stored_at_description)
open AtPublicFiles.AtFiles.HonestTerm
open AtPublicFiles.Committed
open AtPublicFiles.AtFiles
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

local instance (priority := high) threadSeamsPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) threadSeamsValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) threadSeamsDefault : Inhabited RunValue := ⟨fun _ => 0⟩

/-! ## (a) The coins -/

/-- A coin of the honest side over a coin of the book; the two run values are letters. -/
def coinOf {B : ProverCoinCounts} {R₂ R₃ : Type} (r₂ : R₂) (r₃ : R₃) (k : Coins B) : CoinOne B R₂ R₃ :=
  ((k.shared, r₂), ((k.first, k.second), r₃))

/-- **Every coin of the book is the triple that `AtRunS` reads.** -/
theorem coinOf_triple {B : ProverCoinCounts} {R₂ R₃ : Type} (r₂ : R₂) (r₃ : R₃) (k : Coins B) :
    (⟨(coinOf r₂ r₃ k).2.1.1, (coinOf r₂ r₃ k).1.1, (coinOf r₂ r₃ k).2.1.2⟩ : Coins B) = k := rfl

/-! ## (b) The relation -/

variable {Z : PublicFiles} {d : OfflineDescription}

/-- **The key file's relation gives a seed at which the input is tied.** The relation is written out: it is
`KeyRel Z` (E2E/OfflineClauses.lean). -/
theorem tied_of_relation (hs : KeySourced Z d.source d.numbers d.later) (scope : InScope Z = true)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x : AtPublicFiles.AtFiles.KeyInst}
    (h : relAt (ansAt (AZ Z) PadZ (holdZ Z)) (fun i (_ : XF) => inRange i) wrK w₀ rc x) :
    ∃ e, TiedAt Z d (w₀, rc, e) x := by
  obtain ⟨s, x', e, hr⟩ := h
  have hT := tied_offline Z d.source d.numbers d.later runValueBytes runValueBytes
    (AtPublicFiles.KeyStandWalked.offlineValue (files := Z) d) inRange hs.named
    (fun w r it p => stored_at_description d (sized_sourced hs scope) w r it p) w₀ rc s hr
  have e1 : (protocolAtFiles Z).recOf w₀ rc s = (s, ansC (Cf (AZ Z) PadZ (holdZ Z)) w₀ rc s) :=
    validT_obj (Cf (AZ Z) PadZ (holdZ Z)) (filesAt Z) (FlashProve.dataAtFiles FlashProve.flashProveData Z).P
      (w₀, rc, s) _ (valid_has (protocolAtFiles Z) (w₀, rc, s))
  rw [e1, ← ansAt_eq] at hT
  rw [e]
  exact ⟨s, hT⟩

/-- **There the description's test on the instance passes.** -/
theorem okStart_of_relation (hs : KeySourced Z d.source d.numbers d.later)
    (scope : InScope Z = true) {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x : AtPublicFiles.AtFiles.KeyInst}
    (h : relAt (ansAt (AZ Z) PadZ (holdZ Z)) (fun i (_ : XF) => inRange i) wrK w₀ rc x) :
    (descOf d).okStart x = true := by
  obtain ⟨e, ht⟩ := tied_of_relation hs scope h
  exact okStart_of_tied hs.named scope ht

/-! ## (c) The provers -/

/-- **The prover of the bare sides, the offline prover and the prover of the muted rows are one.** -/
theorem provers_are_one (Bk : ProverCoinCounts) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) Bk FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Unit Unit
      Unit) :
    (bareSides (descOf d) Bk (proverOf Z d) [] [] []).prover (proverOf Z d) = proverOf Z d ∧
      (offlineRowsAt (files := Z) d Bk S c).mute.prover ((partsOfDescription d).prover d) =
        proverOf Z d := by
  refine ⟨bareSides_prover _ _ _ _ _ _, ?_⟩
  rw [prover_mute, offlineRowsAt_prover]
  rfl

/-! ## The three together -/

variable {P₁ Wt : Type} {K₀ : KeyPub} (ℓ : WitLens Wt) (Nm : NumbersS)
  (Mg₀ : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn →
    Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey → Prop) (Z₀ : ProofFile.Pub)

/-- **From the lots to every premise of a member of `ThreadsP` with the threads' own invariants, at the
quantifiers of `OwedRest.owed`**: at every input in the key file's relation there is a seed, and at it, at the
prover of the muted rows, the threads sit and owe; and at every coin of the book what a run owes but the
yes. -/
theorem lots_at_relation {U₁ : FirstFamily Z d (keyBook K₀)} {U₃ : LastFamily Z d (keyBook K₀)}
    {S₁ S₃ : OwnLetter Z (keyBook K₀)} (hd : offlineDescription Z = .ok d)
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) (hK₀ : fullPub = some K₀)
    (hs : KeySourced Z d.source d.numbers d.later) (hN : Function.Injective Nm.tenant)
    (hKp : ∀ b ∈ [0, 11], ∀ s, Kp b s s) (hE : ∀ s s', Kp 0 s s' → s' = s)
    (hEnd : ∀ s s', Kp 11 s s' → s' = s) (hC : ∀ v, AtPublicFiles.KeySharedQuiet.CellsAlone (Mg₀ v))
    (L : TheLots (Z := Z) ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d U₁ U₃ S₁ S₃) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription d.source d.numbers d.later) (keyBook K₀) FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey
      Unit Unit Unit) :
    ∀ w₀ rc x, relAt (ansAt (AZ Z) PadZ (holdZ Z)) (fun i (_ : XF) => inRange i) wrK w₀ rc x →
    ∃ e,
      Sits (descOf d) ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d))
        (U₁ (w₀, rc, e) x) (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d (w₀, rc, e) x) (U₃ (w₀, rc, e) x) ∧
      OwesS (U₁ (w₀, rc, e) x) (S₁ (w₀, rc, e) x) ∧
      OwesS (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d (w₀, rc, e) x) (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d (w₀, rc, e) x) ∧
      OwesS (U₃ (w₀, rc, e) x) (S₃ (w₀, rc, e) x) ∧
      (∀ b, SaidNext (U₁ (w₀, rc, e) x) (S₁ (w₀, rc, e) x) b) ∧
      (∀ b, SaidNext (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d (w₀, rc, e) x) (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d (w₀, rc, e) x) b) ∧
      (∀ b, SaidNext (U₃ (w₀, rc, e) x) (S₃ (w₀, rc, e) x) b) ∧
      ∀ k : Coins (keyBook K₀), ∃ R,
        ready (descOf d) (keyBook K₀) ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d)) w₀ rc x k = .ok R ∧
        Enters₁ (descOf d) ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d)) (U₁ (w₀, rc, e) x) w₀ rc x k R ∧
        Enters₂ (descOf d) ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d)) (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d (w₀, rc, e) x) w₀ rc x k R ∧
        S₁ (w₀, rc, e) x 0 k { R.start₁ ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d)) with opened := some [] } ∧
        sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d (w₀, rc, e) x 0 k { R.start₂ ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d)) with opened := some [] } ∧
        DoorBehindS (descOf d) ((offlineRowsAt (files := Z) d (keyBook K₀) S c).mute.prover ((partsOfDescription d).prover d)) (U₁ (w₀, rc, e) x) (sharedThread ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d (w₀, rc, e) x) (U₃ (w₀, rc, e) x)
          (S₁ (w₀, rc, e) x) (sharedSaid ℓ Nm Mg₀ tk tt rest Kp Vd Z₀ d (w₀, rc, e) x) (S₃ (w₀, rc, e) x) x k R := by
  intro w₀ rc x hrel
  obtain ⟨e, ht⟩ := tied_of_relation hs scope hrel
  have hok := okStart_of_tied hs.named scope ht
  obtain ⟨p1, p2⟩ := provers_are_one (Z := Z) (d := d) (keyBook K₀) S c
  obtain ⟨o₂, n₂, -⟩ := shared_at_tied hd scope live hK₀ inRange ℓ Nm Mg₀ tk tt rest Kp Vd Z₀
    (w₀, rc, e) x ht hN hKp hE hEnd hC (fallsBy [] (descOf d).shared.blocksInOrder) (L.testU _ x ht)
    (L.testOmega _ x ht) (L.testYesU _ x ht) (L.testYesOmega _ x ht)
  have hsit := L.sits _ x ht hok
  rw [p1] at hsit
  rw [p2]
  refine ⟨e, hsit, L.firstOwes _ x ht, o₂, L.lastOwes _ x ht, L.firstNext _ x ht, n₂,
    L.lastNext _ x ht, fun k => ?_⟩
  obtain ⟨-, R, hR, -, a₁, a₂, e₁, e₂, a₃, -, -⟩ :=
    L.run (w₀, rc, e) x (coinOf (fun _ => 0) (fun _ => 0) k) ht
  exact ⟨R, hR, a₁, a₂, e₁, e₂, a₃⟩

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.coinOf_triple
#print axioms AtPublicFiles.OfflineRows.tied_of_relation
#print axioms AtPublicFiles.OfflineRows.okStart_of_relation
#print axioms AtPublicFiles.OfflineRows.provers_are_one
#print axioms AtPublicFiles.OfflineRows.lots_at_relation
