-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyAcceptAtFiles.lean: THE ACCEPT LAW OF THE KEY FILE's HONEST PROVER AT THREE PUBLIC FILES Z:
E2E/KeyAccept.lean's `accLaw_key_of_threads` at the letters from which the verifier is compiled, at
the key file's own IOP as written in Lean at Z (below: the description), at the letters of
E2E/KeyTied.lean. In scope, where the IOP's own test on the public files accepts. NOTHING IS CLAIMED
OF ANY PROVER.

Of the nine premises of `accLaw_key_of_threads` that are not on threads EIGHT ARE PAID HERE, one of
them from a test with code that is left as a premise, for X, N, P with `KeyNamed Z X N P`
(E2E/KeyProtocolOverDescription.lean):
  `full_key`: at every typed verifier randomness every stored table's part of a round's sampled
    positions has as many positions as it says (`FullAt`; `LPFFrame.fullAt_liveK`).
  `carries_key`: the committed table carries its positions (`tableOf_eq_cm`, E2E/KeyTied.lean).
  `dataFits_key`: `DataFits` at the key file's data at Z (`ProofFile.Honest.dataFits_of_data`;
    `KeyNamed.data_at`, `KeyNamed.plan`).
  The description's tests on the plan: a field of `KeyNamed`.
  `seal_last`, **`sealPlain_key`**: the first chain's last declared round is the library's sealing
    round, so that round is plain (`sealPlain` reads no other round): at every X, N, P, by
    unfolding.
  `due_key`: "due" at every typed verifier randomness (`ProofFile.Honest.due_at_two`), from one premise on
    the declared rounds: no round asks for more non-zero elements than elements.
  `nzWritten`, **`nz_key`**: that premise, in scope: all declared rounds but the sealing round bear
    the entries of the library's written data (`ProofFile.Honest.kinds_of_data`; `key_data`,
    E2E/ReadsAtFiles.lean), and the sealing round asks for none. LEFT OF IT: `nzWritten = true`: a
    test with code on the written data, WITHOUT A LETTER.
  `run_key`: where the description's decision accepts at the written key, the object's decision on
    the key file accepts (`KeyNamed.run`).
  `sil_key`: the verifier's test on the three rounds without a challenge accepts the seam's three
    values at tied inputs (`Tied.key`; the laid prover's key of an instance is the instance's field;
    `keySeam_silentK_of_key`, E2E/KeySilent.lean).
  `TiedK …`: "tied" at the prover of parts with the rows G, its key, trace and stored table laid.
  `tiedK_valid`: every pair that is valid for the object's key file's protocol is tied so.
  **`accLaw_key_atFiles`**: the accept law at Z. LEFT AS PREMISES: every place with a round has a
    half (`halvedAll`); `nzWritten = true`; and ALL THAT IS OWED ON THREADS: three threads sit;
    `Owes` and `Yes` at every member of the three chains; `AtRun` at every tied input and coin.
  `accLaw_key_valid`: the same at every valid pair of the object at Z THAT IS NOT CUT: see the
    Limits.
  `tiedK_cut`, **`accLaw_key_cut`**: THE END THAT AN HONEST PROVER IS MEANT TO MEET: at every valid
    pair of the object whose index type is cut to the matrices in range (`objAt`,
    E2E/ObjectAtFiles.lean; `tied_key_cut`, E2E/KeyTied.lean): what is owed at a run is asked at
    indices in range alone.

Limits.
- CONDITIONAL: all limits of E2E/KeyAccept.lean stand but the last. No premise on threads is shown
  of the description or of any prover of parts.
- THE LISTS OF FALLS ARE FREE LETTERS (fields of the rows G): the law says something at a member
  only beside each fall's text and its measured share, at each fixed coin.
- That the IOP's own test accepts any Z is evaluated, not proved.
- `nzWritten = true` STAYS A PREMISE HERE. An evaluation in Lean's kernel ends in a stack overflow, of
  the whole test and of its first thousand rounds alike; at the two short lists it goes through. The
  same content stands as a theorem beside this file: `nz_writtenK` (E2E/WrittenNonZero.lean).
- AT THE OBJECT THAT IS NOT CUT the index is every matrix; `ok` is a letter. SO `accLaw_key_valid`
  ASKS `AtRun` AT MATRICES OUT OF RANGE TOO, and says that the verifier accepts there outside the
  abort set and the falls: by the lookups' purpose that can be met only with falls that speak at
  nearly all verifier randomness [argued, no theorem]. It is kept as a corollary; the end that is
  meant is `accLaw_key_cut`.
- Pointwise in the verifier randomness: no measure. No OOD seed is set aside.
- Nothing on hiding follows from this file.


-/
import E2E.KeyAccept
import E2E.KeyTied
import E2E.KeySilent
import Johnson.Desc.ProofFile.Honest.Law.Data
import Johnson.Desc.ProofFile.Honest.Law.DueData
import Johnson.Desc.ProofFile.Honest.Law.DataKinds
import E2E.ReadsAtFiles

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Cut AtPublicFiles.KeyLink
open OnBytes.Flat (relationsAndEncodingOfClaims RecFull silK front₀ join₀)
open OnBytes.Slice (frS)
open _root_.Run (ckP)
open VerifiableInference.Desc.Key (keyInstanceOfOutOfDomainSample)
open ProofFile.Honest (Prover ProverCoinCounts Sides Thread Local Common Sits Owes Yes fallsBy Tied DataFits
  halvedAll sealPlain drawsAt)
open OnBytes.Prover (AccLaw)
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open VerifiableInference.OnPublicFiles (innerCompilerInputAtFullSize)
open AtPublicFiles.Committed (pubAt AZ PadZ holdZ)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (dataAtFiles)
open FlashProve (protocolDataWellFormed flashProveData)

/- As in E2E/KeyTied.lean: the search for this instance runs out of time. -/
local instance (priority := high) keyAccept_pads : Nonempty PadZ := AtPublicFiles.Committed.pads_nonempty frS 402653181

variable (Z : PublicFiles) {X : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {P : VerifiableInference.Desc.Key.LaterPlaces}

/-! ## 1. The premises on the data, the table and the description -/

theorem full_key (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    LPFFrame.FullAt (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) :=
  (FlashProve.dk_built_live Z live).symm ▸ LPFFrame.fullAt_liveK Z scope live

theorem carries_key (w) : LPFFrame.Carries
    (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK w) := by
  rw [show tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK =
    (cmKeyZ Z).ext ((dataAtFiles flashProveData Z).DK.at frS.P.T.a).a from
      tableOf_eq_cm (AZ Z) PadZ (holdZ Z) (dataAtFiles flashProveData Z).DK]
  exact fun _ => rfl

variable {Z}

theorem dataFits_key (hn : KeyNamed Z X N P) :
    DataFits (keyFileDescription X N P) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) :=
  ProofFile.Honest.dataFits_of_data hn.data_at hn.plan

theorem due_key (hn : KeyNamed Z X N P)
    (hz : ∀ d ∈ (keyFileDescription X N P).roundsDeclaredByBlocks.1 ++ (keyFileDescription X N P).roundsDeclaredByBlocks.2.1 ++ (keyFileDescription X N P).roundsDeclaredByBlocks.2.2,
      d.entry.drawNZ ≤ d.entry.drawE) :
    ∀ ρ, (drawsAt (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.rec₀)
      (join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty ρ).due (keyFileDescription X N P) = true :=
  fun ρ => ProofFile.Honest.due_at_two _ _ _ hn.data_at hz ρ

theorem run_key (hn : KeyNamed Z X N P) (a : RecFull) (v₁ v₂ v₃)
    (h : (keyFileDescription X N P).run (keyInstanceOfOutOfDomainSample a) v₁ v₂ v₃ = true) :
    (dataAtFiles flashProveData Z).runK a v₁ v₂ v₃ = true := by
  rw [← hn.run]
  exact (VerifiableInference.Desc.FileDescription.pull_run _ _ _ _ _ _).trans h

/-! ## 1b. The sealing round, and "no round asks for more non-zero elements than elements" -/

/-- A chain's declared rounds end with its last block's. -/
theorem flat_rounds {S Cl : Type} (c : VerifiableInference.Desc.Chain S Cl) :
    ∃ l, c.blocksInOrder.flatMap (·.rounds) = l ++ c.last.rounds := by
  unfold VerifiableInference.Desc.Chain.blocksInOrder
  exact ⟨_, by rw [List.flatMap_append, List.flatMap_singleton]⟩

/-- **The first chain's last declared round is the library's sealing round**, at every X, N, P. -/
theorem seal_last (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
    (P : VerifiableInference.Desc.Key.LaterPlaces) :
    ∃ l, (keyFileDescription X N P).roundsDeclaredByBlocks.1 = l ++ [VerifiableInference.Desc.ChainEnd.sealRound] :=
  flat_rounds (keyFileDescription X N P).first

/-- **The sealing round is plain**, at every X, N, P. -/
theorem sealPlain_key (X : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
    (P : VerifiableInference.Desc.Key.LaterPlaces) : sealPlain (keyFileDescription X N P) = true := by
  obtain ⟨l, e⟩ := seal_last X N P
  unfold sealPlain
  rw [e, List.getLast?_append_of_ne_nil _ (by simp)]
  rfl

/-- A TEST WITH CODE AND WITHOUT A LETTER: no round of the library's written data of the key file
asks for more non-zero elements than elements. That it accepts is shown by no theorem here. -/
def nzWritten : Bool :=
  (Johnson.G.writtenKFull.ds₁ ++ Johnson.G.writtenKFull.ds₂ ++ Johnson.G.writtenKFull.ds₃).all
    fun d => decide (d.entry.drawNZ ≤ d.entry.drawE)

/-- A member of the right list of two lists that are related member by member has a partner. -/
theorem partner {α β : Type} {R : α → β → Prop} : ∀ {l₁ : List α} {l₂ : List β},
    List.Forall₂ R l₁ l₂ → ∀ z ∈ l₂, ∃ d ∈ l₁, R d z
  | _, _, .nil, _, h => absurd h (by simp)
  | _, _, .cons h t, z, hz => by
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨d, hd, hr⟩ := partner t z hz
      exact ⟨d, List.mem_cons_of_mem _ hd, hr⟩

/-- **No declared round of the key file's description at Z asks for more non-zero elements than
elements**: in scope, where the IOP's own test on the public files accepts, and where `nzWritten`
accepts. All rounds but the sealing round bear the entries of the written data; the sealing round
asks for none. -/
theorem nz_key (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hn : KeyNamed Z X N P) (hnz : nzWritten = true) :
    ∀ d ∈ (keyFileDescription X N P).roundsDeclaredByBlocks.1 ++ (keyFileDescription X N P).roundsDeclaredByBlocks.2.1 ++ (keyFileDescription X N P).roundsDeclaredByBlocks.2.2,
      d.entry.drawNZ ≤ d.entry.drawE := by
  have hd := hn.data_at
  rw [AtPublicFiles.Reads.key_data Z scope live] at hd
  obtain ⟨k1, k2, k3, -⟩ := ProofFile.Honest.kinds_of_data hd
  have hw : ∀ d ∈ Johnson.G.writtenKFull.ds₁ ++ Johnson.G.writtenKFull.ds₂ ++
      Johnson.G.writtenKFull.ds₃, d.entry.drawNZ ≤ d.entry.drawE := fun d h =>
    of_decide_eq_true (List.all_eq_true.1 hnz d h)
  obtain ⟨l, e⟩ := seal_last X N P
  rw [e, List.dropLast_concat] at k1
  intro z hz
  rw [e] at hz
  simp only [List.mem_append, List.mem_singleton] at hz
  rcases hz with ((hz | rfl) | hz) | hz
  · obtain ⟨d, hd', hr⟩ := partner k1 z hz
    rw [← hr.1]
    exact hw d (by simp [hd'])
  · exact Nat.le_refl 0
  · obtain ⟨d, hd', hr⟩ := partner k2 z hz
    rw [← hr.1]
    exact hw d (by simp [hd'])
  · obtain ⟨d, hd', hr⟩ := partner k3 z hz
    rw [← hr.1]
    exact hw d (by simp [hd'])

/-! ## 2. Tied, and the test on the three rounds without a challenge -/

variable (Z) (X N P)
variable {R₂ R₃ : Type} [Inhabited R₃] (val₂ : R₂ → ByteArray) (val₃ : R₃ → ByteArray)
  {X₀ Xh : Type} (B : ProverCoinCounts)
  (G : Sides (keyFileDescription X N P) B FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) OnBytes.TableKey Unit X₀ Xh)
  (H : Prover FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst OnBytes.TableKey Unit X₀ Xh)

/-- The prover of parts at Z: H with the committer's stored table, the instance's field as its key,
and the one trace. -/
abbrev proverK : Prover FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst OnBytes.TableKey Unit X₀ Xh :=
  keyLetters ((cmKeyZ Z).prover H)

/-- "Tied" at that prover with the rows G. -/
def TiedK (ok : FullSizeMatrix → Prop) (w : FullSizeMatrix × ((Cz Z).Pad × (Cz Z).Rnd) × (Cz Z).Seed) (x : KeyInst) :
    Prop :=
  Tied ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (keyFileDescription X N P) (G.prover (proverK Z H))
    (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃)
    (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK)
    (pubAt val₂ val₃ keyAnswersTied 0) (keyFirst X N P) (relKeyZ Z ok) w x

/-- **Every pair that is valid for the object's key file's protocol at Z is tied so.** -/
theorem tiedK_valid (Q : (filesAt Z).Provers)
    (w : FullSizeMatrix × ((filesAt Z).withProvers Q).EncodingRandomness × ((filesAt Z).withProvers Q).OutOfDomainSeed) (a : RecFull)
    (h : ((filesAt Z).withProvers Q).validT w a) :
    TiedK Z X N P val₂ val₃ B G H (fun _ => True) w (keyInstanceOfOutOfDomainSample a) :=
  tied_key_atFiles Z X N P Q val₂ val₃ (G.prover H) w a h

/-- **The test on the three rounds without a challenge accepts, at tied inputs.** -/
theorem sil_key (ok : FullSizeMatrix → Prop) (r2 : R₂) (r3 : R₃) (w) (a : RecFull)
    (ht : TiedK Z X N P val₂ val₃ B G H ok w (keyInstanceOfOutOfDomainSample a)) :
    silK a
      ((keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃ r2 r3).front w.1 w.2.1
        w.2.2 (keyInstanceOfOutOfDomainSample a))
      ((keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃ r2 default).join w.1
        w.2.1 w.2.2)
      ((keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃ r2 r3).seam w.1 w.2.1
        w.2.2 (keyInstanceOfOutOfDomainSample a)) = true :=
  keySeam_silentK_of_key (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃ r2 r3 default
    w.1 w.2.1 w.2.2 a (ht.key r2 r3).symm

/-! ## 3. The accept law at Z -/

variable [Fintype R₂] [Nonempty R₂] [Fintype R₃]

/-- The key file's honest prover at Z: the fields of `keyHonestAny` (E2E/KeyHonest.lean) at the
letters from which the verifier is compiled and at the letters of this file. -/
abbrev keyHonestZ :=
  keyHonestAny (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK
    (dataAtFiles flashProveData Z).DP (keyFileDescription X N P) (dataAtFiles flashProveData Z).runP PV.EntryFive.dsF PV.EntryFive.xsF
    (dataAtFiles flashProveData Z).dec (dataAtFiles flashProveData Z).G.rec₀ (dataAtFiles flashProveData Z).G.z₀.2
    (LPFD.Full.sBG (dataAtFiles flashProveData Z).G).logLeaves (dataAtFiles flashProveData Z).G.early
    (LPFD.Full.saltG (dataAtFiles flashProveData Z).G) B (G.prover (proverK Z H))
    (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃) (keyFirst X N P)
    (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK)
    (dataAtFiles flashProveData Z).runK (dataAtFiles flashProveData Z).P

variable {X N P}
  {U₁ : Thread B (keyFileDescription X N P).S₁ (keyFileDescription X N P).Cl
    (Local FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst Unit)
    (Local FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst Unit) Xh KeyInst}
  {U₂ : Thread B (keyFileDescription X N P).S₂ (keyFileDescription X N P).Cl Empty
    (Common FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) OnBytes.TableKey) X₀ OnBytes.TableKey}
  {U₃ : Thread B (keyFileDescription X N P).S₃ (keyFileDescription X N P).Cl
    (Local FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst Unit)
    (Local FullSizeMatrix ((Cz Z).Pad × (Cz Z).Rnd) KeyInst Unit) Xh KeyInst}

/-- **THE ACCEPT LAW OF THE KEY FILE's PROVER AT Z**, from what is owed on threads and two tests
with code: one on the prover of parts, one on the written data. -/
theorem accLaw_key_atFiles (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hn : KeyNamed Z X N P) (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256))
    (ok : FullSizeMatrix → Prop) (hnz : nzWritten = true)
    (h4 : halvedAll (keyFileDescription X N P) (G.prover (proverK Z H)) = true)
    (hS : Sits (keyFileDescription X N P) (G.prover (proverK Z H)) U₁ U₂ U₃) (o₁ : Owes U₁) (o₂ : Owes U₂)
    (o₃ : Owes U₃) (y₁ : Yes U₁ (fallsBy G.falls₁ (keyFileDescription X N P).first.blocksInOrder))
    (y₂ : Yes U₂ (fallsBy G.falls₂ (keyFileDescription X N P).shared.blocksInOrder))
    (y₃ : Yes U₃ (fallsBy G.falls₃ (keyFileDescription X N P).second.blocksInOrder))
    (hat : ∀ w x (c : CoinOne B R₂ R₃), TiedK Z X N P val₂ val₃ B G H ok w x →
      AtRun (keyFileDescription X N P) (G.prover (proverK Z H)) U₁ U₂ U₃ w x c) :
    ∀ w (a : RecFull) (c : CoinOne B R₂ R₃), TiedK Z X N P val₂ val₃ B G H ok w (keyInstanceOfOutOfDomainSample a) →
      AccLaw (batTC (innerCompilerInputAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)).protocol
          (innerCompilerInputAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)).offlineRoundSplits)
        (wTC (innerCompilerInputAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)).queryLayout) a
        ((keyHonestZ Z X N P val₂ val₃ B G H).ext w)
        ((keyHonestZ Z X N P val₂ val₃ B G H).strat w a c)
        ((keyHonestZ Z X N P val₂ val₃ B G H).withheld w a ∪
          fallOne (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.rec₀)
            (join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty (keyFileDescription X N P) B G (proverK Z H) w
            (keyInstanceOfOutOfDomainSample a) c) :=
  accLaw_key_of_threads ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀) (keyFileDescription X N P) B G (proverK Z H)
    (keySeam (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) val₂ val₃) (keyFirst X N P)
    (tableOf (dataAtFiles flashProveData Z).A (relationsAndEncodingOfClaims _ (dataAtFiles flashProveData Z).E) (dataAtFiles flashProveData Z).DK)
    (pubJ := pubAt val₂ val₃ keyAnswersTied 0) (Rel := relKeyZ Z ok) (full_key Z scope live)
    (carries_key Z) (dataFits_key hn) hn.plan (sealPlain_key X N P)
    (due_key hn (nz_key scope live hn hnz)) (run_key hn)
    (fun r2 r3 w a ht => sil_key Z X N P val₂ val₃ B G H ok r2 r3 w a ht) h4 hS o₁ o₂ o₃ y₁ y₂ y₃
    hat

/-- **The same at every pair that is valid for the object's key file's protocol at Z.** -/
theorem accLaw_key_valid (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hn : KeyNamed Z X N P) (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256))
    (hnz : nzWritten = true)
    (h4 : halvedAll (keyFileDescription X N P) (G.prover (proverK Z H)) = true)
    (hS : Sits (keyFileDescription X N P) (G.prover (proverK Z H)) U₁ U₂ U₃) (o₁ : Owes U₁) (o₂ : Owes U₂)
    (o₃ : Owes U₃) (y₁ : Yes U₁ (fallsBy G.falls₁ (keyFileDescription X N P).first.blocksInOrder))
    (y₂ : Yes U₂ (fallsBy G.falls₂ (keyFileDescription X N P).shared.blocksInOrder))
    (y₃ : Yes U₃ (fallsBy G.falls₃ (keyFileDescription X N P).second.blocksInOrder))
    (hat : ∀ w x (c : CoinOne B R₂ R₃), TiedK Z X N P val₂ val₃ B G H (fun _ => True) w x →
      AtRun (keyFileDescription X N P) (G.prover (proverK Z H)) U₁ U₂ U₃ w x c)
    (Q : (filesAt Z).Provers) (w : FullSizeMatrix × ((filesAt Z).withProvers Q).EncodingRandomness × ((filesAt Z).withProvers Q).OutOfDomainSeed)
    (a : RecFull) (c : CoinOne B R₂ R₃) (hv : ((filesAt Z).withProvers Q).validT w a) :
    AccLaw (batTC (innerCompilerInputAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)).protocol
        (innerCompilerInputAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)).offlineRoundSplits)
      (wTC (innerCompilerInputAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)).queryLayout) a
      ((keyHonestZ Z X N P val₂ val₃ B G H).ext w)
      ((keyHonestZ Z X N P val₂ val₃ B G H).strat w a c)
      ((keyHonestZ Z X N P val₂ val₃ B G H).withheld w a ∪
        fallOne (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.rec₀)
          (join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty (keyFileDescription X N P) B G (proverK Z H) w
          (keyInstanceOfOutOfDomainSample a) c) :=
  accLaw_key_atFiles Z val₂ val₃ B G H scope live hn c₀ m₀ (fun _ => True) hnz h4 hS o₁ o₂ o₃ y₁ y₂
    y₃ hat w a c (tiedK_valid Z X N P val₂ val₃ B G H Q w a hv)

omit [Fintype R₂] [Nonempty R₂] [Fintype R₃] in
/-- Every pair that is valid for the key file's protocol of THE OBJECT WHOSE INDEX TYPE IS CUT TO
THE MATRICES IN RANGE is tied, at ok := "in range"; the index is read through the inclusion. -/
theorem tiedK_cut (Q : (filesAt Z).Provers) (w : Ix × (objAt Z Q).EncodingRandomness × (objAt Z Q).OutOfDomainSeed)
    (a : RecFull) (h : (objAt Z Q).validT w a) :
    TiedK Z X N P val₂ val₃ B G H inRange (onFst Subtype.val w) (keyInstanceOfOutOfDomainSample a) :=
  tied_key_cut Z X N P Q val₂ val₃ (G.prover H) w a h

/-- **THE END THAT AN HONEST PROVER IS MEANT TO MEET: at the object that is cut to the matrices in
range.** What is owed at a run (`AtRun`) is asked at tied inputs whose index is in range, and at no
other. -/
theorem accLaw_key_cut (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hn : KeyNamed Z X N P) (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256))
    (hnz : nzWritten = true)
    (h4 : halvedAll (keyFileDescription X N P) (G.prover (proverK Z H)) = true)
    (hS : Sits (keyFileDescription X N P) (G.prover (proverK Z H)) U₁ U₂ U₃) (o₁ : Owes U₁) (o₂ : Owes U₂)
    (o₃ : Owes U₃) (y₁ : Yes U₁ (fallsBy G.falls₁ (keyFileDescription X N P).first.blocksInOrder))
    (y₂ : Yes U₂ (fallsBy G.falls₂ (keyFileDescription X N P).shared.blocksInOrder))
    (y₃ : Yes U₃ (fallsBy G.falls₃ (keyFileDescription X N P).second.blocksInOrder))
    (hat : ∀ w x (c : CoinOne B R₂ R₃), TiedK Z X N P val₂ val₃ B G H inRange w x →
      AtRun (keyFileDescription X N P) (G.prover (proverK Z H)) U₁ U₂ U₃ w x c)
    (Q : (filesAt Z).Provers) (w : Ix × (objAt Z Q).EncodingRandomness × (objAt Z Q).OutOfDomainSeed) (a : RecFull)
    (c : CoinOne B R₂ R₃) (hv : (objAt Z Q).validT w a) :
    AccLaw (batTC (innerCompilerInputAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)).protocol
        (innerCompilerInputAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)).offlineRoundSplits)
      (wTC (innerCompilerInputAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)).queryLayout) a
      ((keyHonestZ Z X N P val₂ val₃ B G H).ext (onFst Subtype.val w))
      ((keyHonestZ Z X N P val₂ val₃ B G H).strat (onFst Subtype.val w) a c)
      ((keyHonestZ Z X N P val₂ val₃ B G H).withheld (onFst Subtype.val w) a ∪
        fallOne (ckP .two) ((dataAtFiles flashProveData Z).DK.at frS.P.T.a) (front₀ (dataAtFiles flashProveData Z).G.rec₀)
          (join₀ (dataAtFiles flashProveData Z).G.rec₀) ByteArray.empty (keyFileDescription X N P) B G (proverK Z H)
          (onFst Subtype.val w) (keyInstanceOfOutOfDomainSample a) c) :=
  accLaw_key_atFiles Z val₂ val₃ B G H scope live hn c₀ m₀ inRange hnz h4 hS o₁ o₂ o₃ y₁ y₂ y₃ hat
    (onFst Subtype.val w) a c (tiedK_cut Z val₂ val₃ B G H Q w a hv)

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.full_key
#print axioms AtPublicFiles.AtFiles.carries_key
#print axioms AtPublicFiles.AtFiles.dataFits_key
#print axioms AtPublicFiles.AtFiles.due_key
#print axioms AtPublicFiles.AtFiles.run_key
#print axioms AtPublicFiles.AtFiles.flat_rounds
#print axioms AtPublicFiles.AtFiles.seal_last
#print axioms AtPublicFiles.AtFiles.sealPlain_key
#print axioms AtPublicFiles.AtFiles.partner
#print axioms AtPublicFiles.AtFiles.nz_key
#print axioms AtPublicFiles.AtFiles.tiedK_valid
#print axioms AtPublicFiles.AtFiles.sil_key
#print axioms AtPublicFiles.AtFiles.accLaw_key_atFiles
#print axioms AtPublicFiles.AtFiles.accLaw_key_valid
#print axioms AtPublicFiles.AtFiles.tiedK_cut
#print axioms AtPublicFiles.AtFiles.accLaw_key_cut
