-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/DrawsBlind.lean: what the honest side of a file's protocol reads of the verifier's messages for
its abort sets does not depend on the proof-of-work test bits. The honest side is `honestB`
(Honest/Record.lean) or `honestBatchProverOfFile` (Honest/StratC.lean, both under Johnson/Desc/ProofFile/): a
structure `BatchHonestProver` (Iop/Batch.lean), written over a description F of the file. Its three tests for
a stop (`badB`, `hidB`, `stop0B`, Honest/Record.lean) read the verifier's messages through two
functions: `drawsLo`, the challenges of the description's first and second chain, from the local
messages, and `drawsSh`, the shared chain's, from the shared messages. In the library's count
(`Chains`, Compile/Joined/Types.lean) the first two are chains 1 and 3, and the shared chain is
chain 2. `RoundsQueryLayout.zero s A W ρ` (OnBytes/TypedOracleCompiler/Iop/BatchWire.lean) is the verifier randomness ρ with
all test bits set to 0. E2E/KeyHonestBlind.lean, E2E/BridgeAlong.lean, E2E/BridgeAtFiles.lean and
E2E/BridgeFalls.lean call `hid_zero`, and the first and the last of them `bad_zero`. General in the
three chains' data D (`WholeD`), the description F, the book of coins B (`ProverCoinCounts`), the prover
structure H (`ProofFile.Honest.Prover`), every other parameter of `honestBatchProverOfFile`, and the parameters K and
chal of `wiresOf`. Statements and proofs; no definition.

  `hid_zero`: for one request's prover of `honestBatchProverOfFile` (`BatchHonestProver.one`, Iop/Batch.lean), under the
    wiring data `wiresOf`: ρ with the test bits set to 0 lies in the part of the abort set that may
    depend on the private input (`Hid`) just when ρ does
  `bad_zero`: the same for the public part (`Bad`)
  `draws_zero`: under the wiring data that the library writes out for a file's parts (`wiresOf`,
    OnBytes/Maker/Wire.lean), `drawsLo` at the local part of ρ (`Rho.lo`) and `drawsSh` at the
    shared part (`Rho.sh`) are the same at ρ and at ρ with all test bits set to 0
  `drawsLo_eq`: `drawsLo` at the local part of ρ is a pair: the library's `drawnT`
    (OnBytes/Maker/Trees.lean) of chain 1's part of ρ (`rho₁`), followed by the one empty challenge
    that `drawsLo` appends for the sealing round; and `drawnT` of chain 3's part (`rho₃`)
  `drawsSh_eq`: `drawsSh` at the shared part of ρ is `drawnT` of chain 2's part (`rho₂`)
  `loTake_lo`, `shTake_sh`: the steps of the two functions, at a chain's rounds followed by any
    shape `rest`. `loTake`, at the local part of ρ and a local chain, returns `drawnT` of the
    chain's part of ρ and the local part of the rest; `shTake` the same, at the shared part and a
    shared chain
  `loSkip_lo`, `shSkip_sh`: `loSkip`, at the local part of ρ and a shared chain, returns the local
    part of the rest; `shSkip`, at the shared part and a local chain, the shared part of the rest
  `loEnd_lo`: `loEnd`, at the local part of ρ and a local chain with no round after it, is `drawnT`
    of ρ

By what. The five lemmas on the steps go by recursion on the list of rounds: a round's entry is
`drOf` (Honest/Strat.lean), which unfolds to the entry of `drawnT`. `drawsLo_eq` and `drawsSh_eq`
join them along the shape of `chainsOf` (OnBytes/Maker/Whole.lean). `draws_zero` rewrites by these
two; then by `rho₁_zero`, `rho₂_zero` and `rho₃_zero` (to take a chain's part of ρ and to set the
test bits to 0 can be done in either order) and by `drawn_zeroLo` and `drawn_zeroSh` (`drawnT` is
the same with the test bits set to 0; all five in E2E/ReadsBlind.lean). By unfolding `BatchHonestProver.one`
and the fields of `honestBatchProverOfFile`, ρ lies in `Hid` just when `hidB` is true at `drawsLo` of the local
part of ρ, and in `Bad` just when `badB` is true there or `stop0B` is true at `drawsSh` of the
shared part; `draws_zero` rewrites both.

Limits. The statements are on the abort sets only: nothing on what is sent, nothing on acceptance (a
verifier that tests proof of work does read the test bits), no probability. The independence is of
the test bits only, not of the index: the part of the abort set that may depend on the private input
reads it. `hid_zero` and `bad_zero` are stated in Lean for `honestBatchProverOfFile`; for `honestB`, whose tests
for a stop are the same terms, only `draws_zero` is stated. The wiring data are the ones that the
library writes out, `wiresOf`. At data without proof of work, setting the test bits to 0 changes
nothing, and the statements hold trivially. No property of a protocol is stated: nothing on
completeness, soundness or hiding.
-/
import E2E.ReadsBlind
import Johnson.Desc.ProofFile.Honest.StratC

set_option autoImplicit false

noncomputable section

namespace AtPublicFiles.Reads
open TypedOracleCompiler.Iop TypedOracleCompiler.Joined OnBytes.Maker
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open Compile.Joined (Chains)
open ProofFile.Honest (loTake loSkip loEnd shTake shSkip drawsLo drawsSh drOf)

section
variable (C : CK) {rest : Shape} {A : RoundSplits rest}

theorem loTake_lo : ∀ (ds : List RDT) (ρ : Rho (uLT C ds ++ rest)),
    loTake C ds (Rho.lo (RoundSplits.app (RoundSplits.allLocal (uLT C ds)) A) ρ) =
      (drawnT C ds (Rho.fst ρ), Rho.lo A (Rho.snd (s := uLT C ds) ρ))
  | [], _ => rfl
  | d :: ds, (c, ρ) => by
      show ((drOf C d c :: (loTake C ds (Rho.lo _ ρ)).1), (loTake C ds (Rho.lo _ ρ)).2) = _
      rw [loTake_lo ds ρ]
      rfl

theorem loSkip_lo : ∀ (ds : List RDT) (ρ : Rho (uLT C ds ++ rest)),
    loSkip C ds (Rho.lo (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) A) ρ) =
      Rho.lo A (Rho.snd (s := uLT C ds) ρ)
  | [], _ => rfl
  | _ :: ds, (_, ρ) => loSkip_lo ds ρ

theorem shTake_sh : ∀ (ds : List RDT) (ρ : Rho (uLT C ds ++ rest)),
    shTake C ds (Rho.sh (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) (uLT C ds)) A) ρ) =
      (drawnT C ds (Rho.fst ρ), Rho.sh A (Rho.snd (s := uLT C ds) ρ))
  | [], _ => rfl
  | d :: ds, (c, ρ) => by
      show ((drOf C d c :: (shTake C ds (Rho.sh _ ρ)).1), (shTake C ds (Rho.sh _ ρ)).2) = _
      rw [shTake_sh ds ρ]
      rfl

theorem shSkip_sh : ∀ (ds : List RDT) (ρ : Rho (uLT C ds ++ rest)),
    shSkip C ds (Rho.sh (RoundSplits.app (RoundSplits.allLocal (uLT C ds)) A) ρ) =
      Rho.sh A (Rho.snd (s := uLT C ds) ρ)
  | [], _ => rfl
  | _ :: ds, (_, ρ) => shSkip_sh ds ρ

end

theorem loEnd_lo (C : CK) : ∀ (ds : List RDT) (ρ : Rho (uLT C ds)),
    loEnd C ds (Rho.lo (RoundSplits.allLocal (uLT C ds)) ρ) = drawnT C ds ρ
  | [], _ => rfl
  | d :: ds, (c, ρ) => by
      show drOf C d c :: loEnd C ds (Rho.lo _ ρ) = _
      rw [loEnd_lo C ds ρ]
      rfl

section
variable (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- **`drawsLo` at the local part of ρ is the library's `drawnT` of the parts of chains 1 and 3**
(the description's first and second chain), with the sealing round's empty challenge after chain
1's. -/
theorem drawsLo_eq (ρ : Rho (chainsOf C D tF tJ t3).sh) :
    drawsLo C D tF tJ t3 (Rho.lo (chainsOf C D tF tJ t3).ann ρ) =
      (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ) ++ [⟨[], [], [], none⟩],
        drawnT C D.ds₃ ((chainsOf C D tF tJ t3).rho₃ ρ)) := by
  have h₁ := loTake_lo C (rest := (chainsOf C D tF tJ t3).shJ)
    (A := (chainsOf C D tF tJ t3).annJ) D.ds₁ ρ.2
  have h₂ := loSkip_lo C (rest := (chainsOf C D tF tJ t3).sh₃)
    (A := (chainsOf C D tF tJ t3).ann₃) D.ds₂ (Rho.snd (s := uLT C D.ds₁) ρ.2).2
  have h₃ := loEnd_lo C D.ds₃
    (Rho.snd (s := uLT C D.ds₂) (Rho.snd (s := uLT C D.ds₁) ρ.2).2).2
  show ((loTake C (rest := (chainsOf C D tF tJ t3).shJ) (A := (chainsOf C D tF tJ t3).annJ) D.ds₁
        (Rho.lo (RoundSplits.app (RoundSplits.allLocal (uLT C D.ds₁)) (chainsOf C D tF tJ t3).annJ) ρ.2)).1 ++
      [⟨[], [], [], none⟩],
    loEnd C D.ds₃ (loSkip C (rest := (chainsOf C D tF tJ t3).sh₃)
      (A := (chainsOf C D tF tJ t3).ann₃) D.ds₂
      (loTake C (rest := (chainsOf C D tF tJ t3).shJ) (A := (chainsOf C D tF tJ t3).annJ) D.ds₁
        (Rho.lo (RoundSplits.app (RoundSplits.allLocal (uLT C D.ds₁)) (chainsOf C D tF tJ t3).annJ)
          ρ.2)).2.2).2) = _
  rw [h₁]
  show (_, loEnd C D.ds₃ (loSkip C (rest := (chainsOf C D tF tJ t3).sh₃)
      (A := (chainsOf C D tF tJ t3).ann₃) D.ds₂
      (Rho.lo (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) (uLT C D.ds₂))
        (chainsOf C D tF tJ t3).ann₃) (Rho.snd (s := uLT C D.ds₁) ρ.2).2)).2) = _
  rw [h₂]
  exact congrArg (Prod.mk _) h₃

/-- **`drawsSh` at the shared part of ρ is the library's `drawnT` of chain 2's part of ρ** (the
description's shared chain). -/
theorem drawsSh_eq (ρ : Rho (chainsOf C D tF tJ t3).sh) :
    drawsSh C D tF tJ t3 (Rho.sh (chainsOf C D tF tJ t3).ann ρ) =
      drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ) := by
  have h₁ := shSkip_sh C (rest := (chainsOf C D tF tJ t3).shJ)
    (A := (chainsOf C D tF tJ t3).annJ) D.ds₁ ρ.2
  have h₂ := shTake_sh C (rest := (chainsOf C D tF tJ t3).sh₃)
    (A := (chainsOf C D tF tJ t3).ann₃) D.ds₂ (Rho.snd (s := uLT C D.ds₁) ρ.2).2
  show (shTake C (rest := (chainsOf C D tF tJ t3).sh₃) (A := (chainsOf C D tF tJ t3).ann₃) D.ds₂
      (shSkip C (rest := (chainsOf C D tF tJ t3).shJ) (A := (chainsOf C D tF tJ t3).annJ) D.ds₁
        (Rho.sh (RoundSplits.app (RoundSplits.allLocal (uLT C D.ds₁)) (chainsOf C D tF tJ t3).annJ)
          ρ.2)).2).1 = _
  rw [h₁]
  show (shTake C (rest := (chainsOf C D tF tJ t3).sh₃) (A := (chainsOf C D tF tJ t3).ann₃) D.ds₂
      (Rho.sh (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) (uLT C D.ds₂))
        (chainsOf C D tF tJ t3).ann₃) (Rho.snd (s := uLT C D.ds₁) ρ.2).2)).1 = _
  rw [h₂]
  rfl

variable (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

/-- **`drawsLo` and `drawsSh` are the same with all test bits set to 0**, under the wiring data
`wiresOf`. -/
theorem draws_zero (ρ : Rho (chainsOf C D tF tJ t3).sh) :
    drawsLo C D tF tJ t3 (Rho.lo (chainsOf C D tF tJ t3).ann
        (RoundsQueryLayout.zero _ _ (wiresOf C K chal D tF tJ t3).sh ρ)) =
      drawsLo C D tF tJ t3 (Rho.lo (chainsOf C D tF tJ t3).ann ρ) ∧
    drawsSh C D tF tJ t3 (Rho.sh (chainsOf C D tF tJ t3).ann
        (RoundsQueryLayout.zero _ _ (wiresOf C K chal D tF tJ t3).sh ρ)) =
      drawsSh C D tF tJ t3 (Rho.sh (chainsOf C D tF tJ t3).ann ρ) := by
  refine ⟨?_, ?_⟩
  · rw [drawsLo_eq, drawsLo_eq, rho₁_zero (wiresOf C K chal D tF tJ t3) ρ,
      rho₃_zero (wiresOf C K chal D tF tJ t3) ρ]
    exact congrArg₂ (fun a b => (a ++ [(⟨[], [], [], none⟩ : Fmt.Drawn)], b))
      (drawn_zeroLo C K chal D.ds₁ _) (drawn_zeroLo C K chal D.ds₃ _)
  · rw [drawsSh_eq, drawsSh_eq, rho₂_zero (wiresOf C K chal D tF tJ t3) ρ]
    exact drawn_zeroSh C K chal D.ds₂ _

variable {Xi W₀ Rc Ky Tr X₀ X Sd R₂ R₃ : Type} (F : VerifiableInference.Desc.FileDescription Xi)
  (silent : Xi → TF → TJ → T3 → Bool) (B : ProofFile.Honest.ProverCoinCounts)
  (H : ProofFile.Honest.Prover W₀ Rc Xi Ky Tr X₀ X) [Fintype R₂] [Nonempty R₂] [Fintype R₃]
  [Inhabited R₃] (J : R₂ → R₃ → ProofFile.Honest.KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3) (sh : Ky → F.S₂)
  (ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str)

/-- **The part of the abort set that may depend on the private input does not depend on the test
bits**: for one request's prover of `honestBatchProverOfFile`, under the wiring data `wiresOf`. -/
theorem hid_zero (w : W₀ × Rc × Sd) (x : Xi) (ρ : Rho (chainsOf C D tF tJ t3).sh) :
    RoundsQueryLayout.zero _ _ (wiresOf C K chal D tF tJ t3).sh ρ ∈
        (ProofFile.Honest.honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).one.Hid w x ↔
      ρ ∈ (ProofFile.Honest.honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).one.Hid w x := by
  show ProofFile.Honest.hidB F H w.1 w.2.1 x (drawsLo C D tF tJ t3 (Rho.lo (chainsOf C D tF tJ t3).ann
            (RoundsQueryLayout.zero _ _ (wiresOf C K chal D tF tJ t3).sh ρ))) = true ↔
    ProofFile.Honest.hidB F H w.1 w.2.1 x
      (drawsLo C D tF tJ t3 (Rho.lo (chainsOf C D tF tJ t3).ann ρ)) = true
  rw [(draws_zero C D tF tJ t3 K chal ρ).1]

/-- The same for the public part. -/
theorem bad_zero (ρ : Rho (chainsOf C D tF tJ t3).sh) :
    RoundsQueryLayout.zero _ _ (wiresOf C K chal D tF tJ t3).sh ρ ∈
        (ProofFile.Honest.honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).one.Bad ↔
      ρ ∈ (ProofFile.Honest.honestBatchProverOfFile C D tF tJ t3 F silent B H J sh ext).one.Bad := by
  show (ProofFile.Honest.badB F H (drawsLo C D tF tJ t3 (Rho.lo (chainsOf C D tF tJ t3).ann
              (RoundsQueryLayout.zero _ _ (wiresOf C K chal D tF tJ t3).sh ρ))) = true ∨
      ProofFile.Honest.stop0B F H (drawsSh C D tF tJ t3 (Rho.sh (chainsOf C D tF tJ t3).ann
              (RoundsQueryLayout.zero _ _ (wiresOf C K chal D tF tJ t3).sh ρ))) = true) ↔
    (ProofFile.Honest.badB F H (drawsLo C D tF tJ t3 (Rho.lo (chainsOf C D tF tJ t3).ann ρ)) = true ∨
      ProofFile.Honest.stop0B F H
        (drawsSh C D tF tJ t3 (Rho.sh (chainsOf C D tF tJ t3).ann ρ)) = true)
  rw [(draws_zero C D tF tJ t3 K chal ρ).1, (draws_zero C D tF tJ t3 K chal ρ).2]

end

end AtPublicFiles.Reads

#print axioms AtPublicFiles.Reads.hid_zero
#print axioms AtPublicFiles.Reads.bad_zero
#print axioms AtPublicFiles.Reads.drawsLo_eq
#print axioms AtPublicFiles.Reads.drawsSh_eq
#print axioms AtPublicFiles.Reads.draws_zero
#print axioms AtPublicFiles.Reads.loTake_lo
#print axioms AtPublicFiles.Reads.loSkip_lo
#print axioms AtPublicFiles.Reads.shTake_sh
#print axioms AtPublicFiles.Reads.shSkip_sh
#print axioms AtPublicFiles.Reads.loEnd_lo
