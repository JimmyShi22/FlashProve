--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyLookupSeat.lean: THE SEAT OF A LOOKUP'S ROW OF HONEST PARTS AT THE KEY FILE: at which place,
face and number of rounds in front the row of Johnson/Desc/ProofFile/Honest/K3/Row.lean is laid, and
WHICH RECORD OF KEYS AND BITS all its parts read of the prover's input. Definitions with code, five
small facts by unfolding, and tests.

Why. The row of a lookup's honest parts is general in the lookup's numbers (`Face`) and typed at a
small record: `Hidden`: the keys, part by part, and the bits of the table's rows' counts; each part
is handed a function `Ask` from the challenges heard in front of it to that record. Whoever seats
the row says what the record is. At the key file keys and bits hang on no challenge: the function is
constant, so ALL PARTS OF THE ROW READ ONE RECORD.

What is defined.
  **`hiddenKey ranges codes l m L mat valB`**: the keys are the library's `keyVec m L mat` (padding
    counted; the shift is not read); the bit of row u and plane j is what the library's `bitVec`
    READS off the multiplicities' message valB at j + 2 ^ mu · u (Johnson/Desc/Key/KeyK3W.lean).
    THESE ARE THE LETTERS OF `TruthAt` (E2E/KeyLookupTruth.lean).
  `askKey`: the constant function.   `atKey i x base`: chain 1, link i, piece 2, the kind "lookup";
    the face of the lookup's public record.   `readsKey`: the run's points, by the row's own
    readers.
  **`seatKey J rd …`**: the row, seated: rd reads the matrix and the multiplicities' message off
    what the chain's parts are handed.   `seatKeyFast`: at the summands that fold tables.
What is shown, each by unfolding.
  `askKey_const`: one record at all lists of challenges.   `seat_record`: the seated row's input is
    that record.   `atKey_place`: the place is that of the key file's own sub-protocol.  
    `hidden_key`, `hidden_bit`: the record's two fields.
Tests, by Lean's evaluator: at the key file's two lookups of the full size the row has 935 and 920
parts, and its stages take 9,581 and 9,220 rounds.

Limits.
- DEFINITIONS. Nothing is played, and nothing is shown of what the row sends.
- Every stretch of mask entries that the row spends is written there as one message's; at the key
  file the entries come of two messages (E2E/KeyLookupAround.lean: `fromKeys_true`). That is the
  row's file's to turn.
- base is a variable: that it is the number of the chain's rounds in front of the place is the
  caller's.
- That valB is the message which the sending in front sends, and that its bits are the counts' bits,
  is other files'.
- Nothing on any property.


-/
import Johnson.Desc.ProofFile.Honest.K3.Row
import Johnson.Desc.ProofFile.Honest.K3.Heard
import Johnson.Desc.ProofFile.Honest.K3.JobsFast
import Johnson.Top.H.KeyRangesFull
import E2E.KeyLookupTruth

set_option autoImplicit false

namespace AtPublicFiles.KeyLookup
open OnBytes
open VerifiableInference.Desc.K3 (faceOfLkp lookupKind)
open VerifiableInference.Desc.Key
open ProofFile.Honest (Placed)
open ProofFile.Honest.K3 (Hidden Ask At Reads LookJobs proverSideOfLookupInChainAtOneOwner ptsOf pointsAt fastJobs stages Stage)

section
variable (ranges : Params.WfPublic) (codes : Codes) (l : ℕ) (m : Wf.Matrix) (L : Params.WfLookup)

/-- **What a lookup's stages read of the key file's prover's input.** -/
def hiddenKey (mat : ℕ → ℕ → F) (valB : ℕ → E) : Hidden where
  key := fun _ i k => keyVec m L mat i k
  bit := fun u j => bitVec ranges codes l valB (j + 2 ^ L.mu * u)

/-- The same at every list of challenges. -/
def askKey (mat : ℕ → ℕ → F) (valB : ℕ → E) : Ask := fun _ => hiddenKey ranges codes l m L mat valB

/-- **One record at all lists of challenges.** -/
theorem askKey_const (mat : ℕ → ℕ → F) (valB : ℕ → E) (h h' : List Fmt.Drawn) :
    askKey ranges codes l m L mat valB h = askKey ranges codes l m L mat valB h' := rfl

theorem hidden_key (mat : ℕ → ℕ → F) (valB : ℕ → E) (θ : E) :
    (hiddenKey ranges codes l m L mat valB).key θ = keyVec m L mat := rfl

theorem hidden_bit (mat : ℕ → ℕ → F) (valB : ℕ → E) (u j : ℕ) :
    (hiddenKey ranges codes l m L mat valB).bit u j =
      bitVec ranges codes l valB (j + 2 ^ L.mu * u) := rfl

end

/-- A lookup's public data at its place in the key file's first chain. -/
def atKey (i : ℕ) (x : Lookup) (base : ℕ) : At := ⟨⟨1, some i, 2, .K3⟩, faceOfLkp x, base⟩

/-- The place is that of the key file's own sub-protocol. -/
theorem atKey_place (set : Params.Setting) (i : ℕ) (x : Lookup) (base : ℕ) :
    (atKey i x base).place =
      (lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set i x)).place := rfl

/-- The run's points, by the row's own readers. -/
def readsKey : Reads := ⟨ptsOf, pointsAt⟩

section
variable {V₁ W₁ X₁ : Type} (ranges : Params.WfPublic) (codes : Codes) (l : ℕ) (m : Wf.Matrix)
  (L : Params.WfLookup) (rd : W₁ → (ℕ → ℕ → F) × (ℕ → E))

/-- What the seated row's parts are handed, of what the chain's parts are handed. -/
def witKey (w : W₁) : Ask := askKey ranges codes l m L (rd w).1 (rd w).2

/-- **The row, seated at the key file.** -/
def seatKey (J : LookJobs Ask) (i : ℕ) (x : Lookup) (base : ℕ) : Placed V₁ W₁ X₁ :=
  proverSideOfLookupInChainAtOneOwner readsKey J (witKey ranges codes l m L rd) (atKey i x base)

/-- **All parts of the row read one record**, at every list of challenges. -/
theorem seat_record (w : W₁) (h : List Fmt.Drawn) :
    witKey ranges codes l m L rd w h = hiddenKey ranges codes l m L (rd w).1 (rd w).2 := rfl

/-- At the summands that fold tables; the table's row is the lookup's public record's. -/
def seatKeyFast (i : ℕ) (x : Lookup) (base : ℕ) : Placed V₁ W₁ X₁ :=
  seatKey ranges codes l m L rd (fastJobs (faceOfLkp x) fun θ u => Lkp.rowAt x θ u).asked i x base

end

/-! ## Tests -/

def full0 : Lkp.Public := Wf.lookupOf 1 ⟨18, 0⟩ Johnson.Pack.lk0Full
def full1 : Lkp.Public := Wf.lookupOf 1 ⟨18, 0⟩ Johnson.Pack.lk1Full

#guard (stages (faceOfLkp full0)).length == 935 && (stages (faceOfLkp full1)).length == 920
#guard ((stages (faceOfLkp full0)).map (Stage.rounds (faceOfLkp full0))).sum == 9581
#guard ((stages (faceOfLkp full1)).map (Stage.rounds (faceOfLkp full1))).sum == 9220

end AtPublicFiles.KeyLookup

#print axioms AtPublicFiles.KeyLookup.askKey_const
#print axioms AtPublicFiles.KeyLookup.hidden_key
#print axioms AtPublicFiles.KeyLookup.hidden_bit
#print axioms AtPublicFiles.KeyLookup.atKey_place
#print axioms AtPublicFiles.KeyLookup.seat_record
