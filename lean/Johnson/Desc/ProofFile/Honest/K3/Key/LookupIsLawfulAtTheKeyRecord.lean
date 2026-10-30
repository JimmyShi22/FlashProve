-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
Johnson/Desc/ProofFile/Honest/K3/Key/LookupIsLawfulAtTheKeyRecord.lean: THE SUMMANDS THAT FOLD TABLES ARE `Lawful` AT EVERY COURSE
THAT A PLAY OF THE SEATED ROW IS, at a key file's lookup, where the row's reader hands, of the run's input, ONE RECORD of keys
and bits at all lists of challenges and that record meets the three sentences `KeyMidHyp` at every shift and alpha. It is
`lawful_key_fast` (Honest/K3/FastLaw/PartsKey.lean) and `mid_key` (Honest/K3/Parts/KeyMid.lean) called at `courseAt`
(Honest/K3/Law/Top.lean): the premise "lawful" of Honest/K3/Key/LookupTruthBehindTheHearing.lean. One theorem, with proof.

Hypotheses that remain. face: the lookup's face is the key file's lookup's. constant: AT THE RUN's OWN INPUT the reader
hands one record at all lists of challenges (the record may turn with the input). stands: the
run stands in front of the lookup (`Stands`). accepted: the two conditions on the public structure (`okK`). relation:
`KeyMidHyp` at every shift and alpha (at the written key: E2E/Lookup/Key/LookupDataMeetTheRelationAtTheWrittenKey.lean).

Limits. An implication. No thread, no book, no mask.
Not claimed: anything on soundness, completeness, hiding or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.PartsKey
import Johnson.Desc.ProofFile.Honest.K3.Parts.KeyMid
import Johnson.Desc.ProofFile.Honest.K3.Law.Top

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Key
open OnBytes (E)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.Spec (planesOf)
open ProofFile.Honest.K3.Parts (specJobsPAt dataP keysOfP)
open ProofFile.Honest.K3.Parts.Key (faceK rowK padsK numsK okK hidK KeyMidHyp mid_key)
open ProofFile.Honest.K3.FastLaw (lawful_key_fast)

/-- **AT A KEY FILE's LOOKUP THE SUMMANDS THAT FOLD TABLES ARE LAWFUL AT EVERY COURSE OF THE SEATED ROW's PLAY.** -/
theorem lookupIsLawfulAtTheKeyRecord {W₁ X₁ : Type} (id : Nat) (matrix : OnBytes.Wf.Matrix)
    (structure_ : OnBytes.Params.WfLookup) (keyReader : Nat → Nat → E) (bitReader : Nat → E) (lookup : At)
    (face : lookup.face = faceK id matrix structure_) (wit : W₁ → Ask)
    (entries : List Fmt.Entry) (mid : Mid W₁ X₁) (draws : List Fmt.Drawn)
    (constant : ∀ heard, wit mid.st.input heard = hidK structure_ keyReader bitReader)
    (stands : Stands lookup entries mid draws) (accepted : okK id matrix structure_ = true)
    (relation : ∀ theta alpha, KeyMidHyp id matrix structure_ keyReader bitReader theta alpha)
    (stageCoins : (s : Stage) → StageCoins lookup s) :
    Lawful (courseAt lookup (fastJobs (faceK id matrix structure_) (rowK id matrix structure_)).asked 0 wit mid draws
        stageCoins)
      (planesOf (dataAt (numsK id matrix structure_) (hidK structure_ keyReader bitReader)
        (ptsOf lookup.face lookup.base (mid.st.heard ++ draws))))
      (keysOfP (dataP (numsK id matrix structure_) lookup.face.parts lookup.face.orders
        (hidK structure_ keyReader bitReader) (ptsOf lookup.face lookup.base (mid.st.heard ++ draws)))) := by
  have fit := fit_of_stands stands
    (specJobsPAt (faceK id matrix structure_) (rowK id matrix structure_) (padsK id matrix structure_)).asked 0 wit
    stageCoins
  exact lawful_key_fast
    (courseAt lookup
      (specJobsPAt (faceK id matrix structure_) (rowK id matrix structure_) (padsK id matrix structure_)).asked 0 wit
      mid draws stageCoins)
    id matrix structure_ (hidK structure_ keyReader bitReader) face rfl fit accepted
    (fun _ _ => constant _)
    (by
      show (dataP (numsK id matrix structure_) lookup.face.parts lookup.face.orders
        (hidK structure_ keyReader bitReader) (ptsOf lookup.face lookup.base (mid.st.heard ++ draws))).Mid
      rw [face]
      exact mid_key id matrix structure_ keyReader bitReader _ (relation _ _) (by rw [← face]; exact stands.ok)
        accepted)

end ProofFile.Honest.K3.Key

#print axioms ProofFile.Honest.K3.Key.lookupIsLawfulAtTheKeyRecord
