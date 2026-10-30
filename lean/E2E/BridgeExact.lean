-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeExact.lean: `ExactAt` (E2E/BridgeAlong.lean), a hypothesis of the privacy side (`PremW`)
of E2E/BridgeJoinAtFiles.lean (of `good_join` and `both_atFiles`), is proved at three public files
Z, at a named simulator `simZ`, from a hypothesis on the rows G (`Sides`: for each sub-protocol the
prover's part and its simulator). `ExactAt` says: at tied inputs, at every verifier randomness
outside the abort set `Hid`, the honest output is the named simulator's. Here it is stated of the
family `honestProversByCopyNumber` of one request's honest provers at the description's own instances, one prover for
each number n of a stored copy (below: the number), at the inputs of `TiedIn`. The proof is one
call, at each number, of a conditional lemma on one slot of the honest side `ProofFile.Honest.honestBatchProverOfFile`.
The three theorems are stated for Z in scope, where the IOP's own test on the public files accepts,
at a description `descZ Zp Np cF` that `LaidAt` ties to Z. The book of coins B (`ProverCoinCounts`), the rows G,
the prover structure H (`ProofFile.Honest.Prover`), the finite types R₂ and R₃ with their codes run₂ and
run₃, and Yes, ok and Gs are free parameters. The theorems of E2E/BridgeJoinAtFiles.lean do not call
this file: they keep `ExactAt` as a hypothesis. E2E/BridgeOwedLink.lean puts `exactAt_of_owed` into
`premW_link` (E2E/BridgePremWLink.lean).

  `exactAt_of_owed`: the form to use: `ExactAt` of that family at `simZ` and `TiedIn … Yes ok Gs`,
    from `Owed` at the whole relation `RyesZ Z` of the library's object. One simulator is then exact
    at every Yes that implies `RyesZ Z`, every ok and every Gs at once. So the gap that the Limits
    of E2E/BridgeJoinAtFiles.lean name (a simulator that leans on the one index of a Yes or ok that
    holds at one index only) is closed where `ExactAt` is had from this theorem, for the session's
    simulator `simZ` only, and as far as `RyesZ Z` is wide: that it holds at more than one index is
    not shown here, and if it held at one index only, this form and the narrow form would be the
    same. Nothing is said of the key file's simulator: in `premW_of_owed` (E2E/BridgeOwedLink.lean),
    which calls this theorem, it remains a free parameter next to the free range ok
  `exactAt_of_owedAt`: the same conclusion, from `Owed` at any relation Rq that holds of the
    requests of Yes at the indices of ok. The other two forms are calls of this one
  `exactAt_of_owedNarrow`: the same conclusion, from `Owed` at "ok and Yes" only. Less has to be
    shown, and that gap is open again: the rows may be chosen with ok and Yes in hand
  `simZ … n`: an abbreviation: the simulator of that lemma (`simOne`,
    Johnson/Desc/ProofFile/Honest/Law/Rule/OneSim.lean) at the parameters at Z and at the number n.
    By its type it is given the written instance, the verifier randomness and the external answers.
    It is built from the description, the book of coins, the rounds' data, the rows' simulators
    (`G.sims`), the committer's map from an instance to its key, the public form `pubAt` of what the
    three rounds without a challenge send, and the honest side's public abort set `Bad`
    (`….one.Bad`, a set of verifier randomness: the stops of the first sort of the rows' parts,
    which read challenges only: `badB`, `stop0B`, Honest/Record.lean). It reads none of Yes, ok and
    Gs
  `simZ_any`: `simZ` reads nothing of the prover structure H: at two such structures it is the same
    term, by definition

By what. `ProofFile.Honest.one_exact_atItem_mute`
(Johnson/Desc/ProofFile/Honest/Law/Rule/TiedAtItem.lean): the conclusion of `one_exact_at`
(Honest/Law/Rule/OneAt.lean), from `Owed` at the muted rows as in `one_exact_at_mute`
(Honest/Law/Rule/Mute.lean), at a prover structure whose stored table is the committer's at one item
only (`Committer.proverAt`, Honest/CommitterAt.lean; here the item 0, as in `provG`). Of its
hypotheses, hO and hE are those of the theorems here; the others are proved. The six equations
`TiedAt` (Honest/Law/Rule/Tied.lean): `tiedAt_along` (E2E/TiedAtFiles.lean). Every stored table that
a round of the description declares is under the item 0 (`ItemsZero`): `itemsZero_of_data`
(E2E/ItemsZero.lean), from the field `data` of `LaidAt`. `DataFits`, and "due" at every verifier
randomness (`Draws.due`: the challenges are such as the description's rounds can draw):
`dataFits_atFiles` and `due_atFiles` (E2E/BridgePaidAtFiles.lean). The two clauses of a valid pair:
`valid_obj` and `ansAt_eq` (E2E/TiedAtFiles.lean), from the clauses of `TiedIn` on ok and Yes, with
hq. `simZ_any`: `Committer.proverAt` sets the key, and `Sides.prover` (Honest/Rule.lean) sets the
three lists of parts that `Bad` reads. Definitions: `honestBatchProverOfFile` (Honest/StratC.lean); `honestProversByCopyNumber`
(E2E/BridgeAlong.lean); `TiedIn`, `provG`, `descZ`, `dataZ` (E2E/BridgeJoinAtFiles.lean); `seamZ`,
`extZ` (E2E/BridgeLinkAtFiles.lean); `RyesZ`, `pubAt`, `cmAlong`, `ansAt`, `shAt`, `silInst`
(E2E/TiedAtFiles.lean).

Hypotheses. scope: `InScope Z = true`. live: the IOP's own test on the public files accepts
(`protocolDataWellFormed (asDescriptionFiles Z) = true`). L: `LaidAt` (Johnson/P5J/LaidOpens.lean) holds of Z's files and (Zp,
Np, cF). hY, in `exactAt_of_owed`: Yes implies `RyesZ Z`. hq, in `exactAt_of_owedAt`: see the list.
hO: `Owed` (Honest/Owed.lean) at `G.mute`: what has to be shown of the rows for the privacy side, at
the rows with their two fields A and B set to "never". There two fields of `Good`
(Honest/Side.lean), `plays` and `acc`, are vacuous, on purpose; all else is asked as at G. `Owed` at
G implies it (`ProofFile.Honest.Owed.mute`), so each theorem here also holds with G in that place. The
conclusions name G, not `G.mute`. The prover structure in hO is H with the committer's key and, at
the item 0 only, the committer's columns. In all three forms hO is asked at all OOD seeds: the
lemma's relation `relAt` (Honest/Law/Rule/Tied.lean) has no parameter for Gs, so a smaller Gs makes
hO no weaker. The field `input` of `Owed` asks the same two tests as `ServesAt`
(E2E/BridgeJoinAtFiles.lean), at another range. hE: `G.owns = true` (Honest/Law/Rule/Session.lean):
a Bool-valued test on the rows. hnz: no declared round asks for more non-zero elements than elements
(in scope, under `LaidAt`, a theorem: `nonZero_atFiles`, E2E/BridgeNonZero.lean, which this file
does not import).

Limits.
- All limits of the head of Honest/Law/Rule/OneAt.lean (`one_exact_at`) hold here, and those of the
  heads of Honest/Law/Rule/Mute.lean and Honest/Law/Rule/TiedAtItem.lean. The next four items
  restate some of them as they apply here.
- The hypotheses of `one_exact_at` are met together by small made-up rows only (its head names
  them), at no description of the protocol; by that head, `Owed` is shown of such rows only. They
  are at `Committer.prover`. For `Committer.proverAt`, which is what hO has,
  Honest/Law/Rule/TiedAtItem.lean names no rows, and no rows G are shown here to meet hO.
- By value the written instance holds the OOD answers, and the external answers hold the encoded
  index at the positions read. Both are made of the index and the committer's randomness, which are
  fixed: no statement here is over a distribution of these two.
- The measure of the abort set `Hid`, which may depend on the private input, has no bound here
  (`HidSmall` asks one, as a hypothesis of E2E/BridgeOwedLink.lean), and inside that set the
  verifier sees whether the prover answers.
- The lemma is on one slot of `honestBatchProverOfFile` only (`BatchHonestProver.one`, Iop/Batch.lean).
- The limits of E2E/BridgeJoinAtFiles.lean hold here too.
- Nothing on completeness, soundness or hiding follows from this file alone.
-/
import E2E.BridgeJoinAtFiles
import Johnson.Desc.ProofFile.Honest.Law.Rule.Mute

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (front₀ join₀)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open _root_.Run (ckP)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest (Prover ProverCoinCounts Sides Owed relAt honestBatchProverOfFile simOne)
open LPFD.Full (XF instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed)
open P5J

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

/- The same for this one. -/
local instance (priority := high) {α : Type} [Inhabited α] : Nonempty α := ⟨default⟩

variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
  {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃] (run₂ : R₂ → ByteArray)
  (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
  (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)

/-- The simulator `simOne` of `one_exact_atItem_mute`, at the parameters at Z and the number n. -/
abbrev simZ (n : ℕ) :=
  simOne (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2) (join₀ (dataAtFiles flashProveData Z).G.z₀.2)
    ByteArray.empty (descZ Zp Np cF) silInst B G.sims
      ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H).key
    (pubAt run₂ run₃ ansInst n)
    (honestBatchProverOfFile (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
      (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B
      (provG Z Zp Np cF B G H) (seamZ Z run₂ run₃ n) (shAt Zp Np cF) (extZ Z)).one.Bad

/-- **The simulator reads nothing of the prover structure H.** -/
theorem simZ_any (H' : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh) (n : ℕ) :
    simZ Z Zp Np cF run₂ run₃ B G H n = simZ Z Zp Np cF run₂ run₃ B G H' n := rfl

/-- **`ExactAt` at Z, from the hypothesis `Owed` on the rows for the privacy side**, with `Owed` at
any relation Rq that holds of the requests of Yes at the indices of ok. The simulator reads none of
Rq, Yes, ok and Gs. -/
theorem exactAt_of_owedAt (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {Yes : FullSizeMatrix → XF → Prop} (ok : FullSizeMatrix → Prop) (Gs) (Rq : FullSizeMatrix → XF → Prop)
    (hq : ∀ i x, ok i → Yes i x → Rq i x)
    (hO : Owed (descZ Zp Np cF) B ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) G.mute
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) Rq instanceAsPlainRecord))
    (hE : G.owns = true)
    (hnz : ∀ d ∈ (descZ Zp Np cF).roundsDeclaredByBlocks.1 ++ (descZ Zp Np cF).roundsDeclaredByBlocks.2.1 ++
      (descZ Zp Np cF).roundsDeclaredByBlocks.2.2, d.entry.drawNZ ≤ d.entry.drawE) :
    ExactAt (honestProversByCopyNumber (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
        (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B
        (provG Z Zp Np cF B G H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z))
      (simZ Z Zp Np cF run₂ run₃ B G H) (TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs) := by
  intro n w x hx ρ hρ
  obtain ⟨x', hx', rfl⟩ := hx.2.2.1
  exact ProofFile.Honest.one_exact_atItem_mute
    (tiedAt_along (AZ Z) PadZ (holdZ Z) Zp Np cF run₂ run₃ n (dataAtFiles flashProveData Z).DP)
    (AtPublicFiles.AtZero.itemsZero_of_data L.data) hO hE
    (dataFits_atFiles Z Zp Np cF scope live L) w (x', (protocolAtFiles Z).recOf w.1 w.2.1 w.2.2)
    (by
      rw [ansAt_eq]
      exact valid_obj (Cf (AZ Z) PadZ (holdZ Z)) (filesAt Z) (dataAtFiles flashProveData Z).P Rq w
        (x', (protocolAtFiles Z).recOf w.1 w.2.1 w.2.2) ⟨rfl, hq _ _ hx.1 hx'⟩)
    ρ (due_atFiles Z Zp Np cF scope live L hnz ρ) hρ

/-- **The form to use: `Owed` at the whole relation of the library's object.** One simulator, which
reads none of Yes, ok and Gs, is then exact at every Yes that implies that relation, every ok and
every Gs at once: so a Yes or ok that holds at one index only gains it nothing (as far as the whole
relation is wide). -/
theorem exactAt_of_owed (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {Yes : FullSizeMatrix → XF → Prop} (hY : ∀ i x, Yes i x → RyesZ Z i x) (ok : FullSizeMatrix → Prop) (Gs)
    (hO : Owed (descZ Zp Np cF) B ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) G.mute
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (RyesZ Z) instanceAsPlainRecord))
    (hE : G.owns = true)
    (hnz : ∀ d ∈ (descZ Zp Np cF).roundsDeclaredByBlocks.1 ++ (descZ Zp Np cF).roundsDeclaredByBlocks.2.1 ++
      (descZ Zp Np cF).roundsDeclaredByBlocks.2.2, d.entry.drawNZ ≤ d.entry.drawE) :
    ExactAt (honestProversByCopyNumber (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
        (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B
        (provG Z Zp Np cF B G H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z))
      (simZ Z Zp Np cF run₂ run₃ B G H) (TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs) :=
  exactAt_of_owedAt Z Zp Np cF run₂ run₃ B G H scope live L ok Gs (RyesZ Z) (fun i x _ h => hY i x
    h) hO hE hnz

/-- **The narrow form, and its price**: `Owed` at "ok and Yes" only: less has to be shown. But the
rows G, from which the simulator is built, may then be chosen with ok and Yes in hand: at an ok or
Yes that holds at one index only the rows' simulators may lean on that index, and the equation says
nothing on hiding. -/
theorem exactAt_of_owedNarrow (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {D : WholeD} {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {Yes : FullSizeMatrix → XF → Prop} (ok : FullSizeMatrix → Prop) (Gs)
    (hO : Owed (descZ Zp Np cF) B ((cmAlong (AZ Z) PadZ (holdZ Z)).proverAt 0 H) G.mute
      (relAt (ansAt (AZ Z) PadZ (holdZ Z)) (fun i x => ok i ∧ Yes i x) instanceAsPlainRecord))
    (hE : G.owns = true)
    (hnz : ∀ d ∈ (descZ Zp Np cF).roundsDeclaredByBlocks.1 ++ (descZ Zp Np cF).roundsDeclaredByBlocks.2.1 ++
      (descZ Zp Np cF).roundsDeclaredByBlocks.2.2, d.entry.drawNZ ≤ d.entry.drawE) :
    ExactAt (honestProversByCopyNumber (ckP .two) (dataZ Z) (front₀ (dataAtFiles flashProveData Z).G.z₀.2)
        (join₀ (dataAtFiles flashProveData Z).G.z₀.2) ByteArray.empty (descZ Zp Np cF) silInst B
        (provG Z Zp Np cF B G H) (seamZ Z run₂ run₃) (shAt Zp Np cF) (extZ Z))
      (simZ Z Zp Np cF run₂ run₃ B G H) (TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs) :=
  exactAt_of_owedAt Z Zp Np cF run₂ run₃ B G H scope live L ok Gs _ (fun _ _ h h' => ⟨h, h'⟩) hO hE
    hnz

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.simZ_any
#print axioms AtPublicFiles.AtFiles.exactAt_of_owedAt
#print axioms AtPublicFiles.AtFiles.exactAt_of_owed
#print axioms AtPublicFiles.AtFiles.exactAt_of_owedNarrow
#print axioms AtPublicFiles.AtFiles.simZ
