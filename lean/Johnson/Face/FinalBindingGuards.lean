-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/FinalBindingGuards.lean: TESTS FOR EMPTINESS of the
lines on binding and extraction at compile's own committer (FinalBindingStatement.lean): what they
quantify over has members.

 1. `filesTaken_zFull`: FilesTaken has a member: the library's written copy of the full-size public
    files, storedPublicFiles, at what the reader returns there.
 2. `silentPart files settings length`: at EVERY public files, settings and length there is an honest
    part whose tables' salts have that length (`silentPart_salts`): so FinalBindingGoal's domain is
    not empty at any files, and HonestProversAndSettings has a member (`allHonestParts_nonempty`).
 3. `twoWeightsWhereRead`: at all public files that are read there are two different weights: so "binds
    to the weights" tells something apart.

Limits. MEMBERS, NOT THE MEMBER THAT IS MEANT. The provers of silentPart send fixed messages; its search
limits are 0, it makes one copy, its coins are one number out of one. No verifier accepts its proofs,
and nothing here says so or needs it: the lines on binding read no prover. It is a control of the
statements' domain and no honest part of flashProveAtFiles. NOT TESTED HERE: that CommitterWithin, the premise
of the line on extraction, is met by some number at some part; that the verifier accepts anything under
a commitment of this committer's make. storedPublicFiles is a value written in Lean; no theorem ties it to a file on
a disk.
-/
import Johnson.Face.FinalBindingStatement
import Johnson.Goal.Files.FilesReadProof
import Johnson.FrontRoad.LaidBeside
import Johnson.Bind.Cpp.Controls

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve
open IntegerTransformer (Settings)

/-! ## 1. The public files -/

/-- **FilesTaken has a member.** -/
theorem filesTaken_zFull : ∃ parameters, FilesTaken storedPublicFiles parameters :=
  let ⟨scope, parameters, read, exact⟩ := VerifierAndGoals.filesRead.full
  ⟨parameters, ⟨scope, read, exact⟩⟩

/-! ## 2. The honest parts -/

/-- A prover of any interactive oracle proof that sends the fixed messages of the rounds' formats. -/
def silentProver {Y : Type} {E : Iop.ExtSpec} (Q : Iop.InteractiveOracleProof Y E) {Input : Type}
    (tables : Input → E.Str) : Iop.Honest Q Input where
  Coin := Unit
  neCoin := ⟨()⟩
  ext := tables
  strat := fun _ _ _ => Iop.Strat.dflt Q.shape ()
  Bad := ∅
  Hid := fun _ _ => ∅

/-- Three such provers, at any protocol; the tables of which they speak are the encodings of their
index. -/
def silentProvers {Index Instance : Type} (protocol : Iop.HolographicProtocol Index Instance) :
    HonestProvers protocol where
  offlineProver := silentProver protocol.offline fun w => protocol.encodeIndex w.1 w.2.1
  linkProver := silentProver protocol.link fun w =>
    (protocol.encodeIndex w.1 w.2.1.1, protocol.encodeIndex w.1 w.2.2.1)
  onlineProver := silentProver protocol.onlineBatch.loc fun w => protocol.encodeIndex w.1 w.2.1

/-- Settings with constants: no search, one copy, plain starts; a table's salt has no public start and
so many free bits. -/
def silentSettings {Index Instance : Type} {protocol : Iop.HolographicProtocol Index Instance}
    {offlineRoundMarks : Iop.RoundSplits protocol.offline.shape} {linkRoundMarks : Iop.RoundSplits protocol.link.shape}
    (layout : HashLayout protocol offlineRoundMarks linkRoundMarks) (provers : HonestProvers protocol)
    (filler : layout.LeafBody) (length : ℕ) : CompiledSettings layout provers where
  leafFiller := filler
  searchLimitOffline := fun _ => 0
  searchLimitLink := fun _ => 0
  searchLimitOnline := fun _ => 0
  furtherCopies := 0
  copyNumber := id
  RunValues := Unit
  wellFormed := fun _ => True
  runValuesOffline := fun _ => ()
  runValuesLink := fun _ => ()
  runValuesOnline := fun _ => ()
  readOffline := fun _ => ()
  readLink := fun _ => ()
  readOnline := fun _ => ()
  saltStartOffline := fun _ _ _ bits => bits
  saltStartLink := fun _ _ _ bits => bits
  saltStartOnline := fun _ _ _ bits => bits
  slotTail := fun _ => []
  windowFiller := []
  coinNumbers := ⟨[], length, 0, filler, filler, filler, 0, 0, 0⟩

/-- **An honest part at every public files and settings**, whose tables' salts have a given length. A
control of the statements' domain: see the head's limits. -/
def silentPart (files : PublicFiles) (settings : Settings) (length : ℕ) :
    HonestProversAndSettingsAtFiles files settings where
  fallbackInstance := (FlashProve.dataAtFiles flashProveData files).G.z₀.1
  provers := silentProvers _
  compiledSettings := fun _ => silentSettings _ _ ([] : List Bool) length
  coinBound := 0
  onlineRunsPerCopy := 1

theorem silentPart_salts (files : PublicFiles) (settings : Settings) (length : ℕ) :
    TableSaltsHaveLength (silentPart files settings length) length :=
  fun _ => Nat.zero_add length

/-- **FinalBindingGoal's domain has a member at every public files, settings and length.** -/
theorem part_with_salts (files : PublicFiles) (settings : Settings) (length : ℕ) :
    ∃ part : HonestProversAndSettingsAtFiles files settings, TableSaltsHaveLength part length :=
  ⟨silentPart files settings length, silentPart_salts files settings length⟩

/-- HonestProversAndSettings has a member. -/
theorem allHonestParts_nonempty : Nonempty HonestProversAndSettings :=
  ⟨fun files settings => silentPart files settings 0⟩

/-! ## 3. The weights -/

/-- **At public files that are read there are two different weights**: those of the all-zero index, and
those of an index with one entry that is not zero (Bind.Control.two_weights). -/
theorem twoWeightsWhereRead (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (read : readFiles files = .ok parameters) :
    ∃ weights weights' : ModelWeights (settingsOfRead parameters), weights ≠ weights' :=
  Bind.Control.two_weights (valid_of_read read)

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.filesTaken_zFull
#print axioms VerifiableInference.Compilation.silentPart
#print axioms VerifiableInference.Compilation.silentPart_salts
#print axioms VerifiableInference.Compilation.part_with_salts
#print axioms VerifiableInference.Compilation.allHonestParts_nonempty
#print axioms VerifiableInference.Compilation.twoWeightsWhereRead
