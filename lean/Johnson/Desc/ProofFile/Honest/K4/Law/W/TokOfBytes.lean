-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/TokOfBytes.lean: CONDITIONAL.

What is here. `TokensArePrompt` (Law/W/TokPublic.lean: the public sentence to which the hypothesis
hTok of Law/W/EmbHead.lean and of the tops comes down) HOLDS OF THE READER THAT THE LOT ITSELF LAYS,
`k4Tokens` (Honest/K4/Part.lean: all words of the instance's request file but the last two), AT
EVERY INSTANCE WHOSE REQUEST BYTES THE LIBRARY DECODES (`Meaning.backReq`,
Johnson/Meaning/ReqBytes.lean, returns a request). Both sides read word number q of the request
file: the library's decoder lays it as the prompt's token at position q (`unlayB`,
Johnson/Flat/LayBytes.lean), and its test on the words has the file at two words more than there are
positions. With `tok_head` (Law/W/TokPublic.lean): at tokens := `k4Tokens` the hypothesis hTok
follows from hr alone. Each proof unfolds the two readers.

  `getD_words`   a word below the cut, read behind the cut and the map to numbers, is the word.
  `tokens_k4`   **`TokensArePrompt k4Tokens xi`**, from hr.

Not shown here. hr: THE INSTANCE's REQUEST BYTES ARE A WELL-FORMED REQUEST's: the library's decoder
returns: a hypothesis on public bytes; that it holds at a run's instance is not shown here. WHERE IT
FAILS NOTHING IS SAID: the library's reader of the request then answers a default without a word
(Law/W/TokPublic.lean's head), and `TokensArePrompt k4Tokens` may be false. That a prover's list of
halves holds the half with `k4Tokens` is the hypothesis half of the tops: they take the reader
`tokens` as a parameter. Of hr no example is written here. THE FULL SIZE ALONE: the library's
decoder stands at its reference parameters. Nothing on soundness, on completeness or on any other
property. No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 70 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 78 is not counted: all the numbers are floors. They
come with Law/W/TokPublic.lean, for the definition `TokensArePrompt` alone: neither proof calls a
statement of a file under Johnson/Goal/. A LAW, NOT A PART: no file that defines a part of the proof
file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.TokPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open Inst.Model (ppref)
open Inst.Model.All (DF)
open VerifiableInference.OnPublicFiles.Flat (Req)

/-- CONDITIONAL: on hq and hn. **A word below the cut.** -/
theorem getD_words (w : Array UInt32) (n q : Nat) (hq : q < n) (hn : n ≤ w.size) :
    ((w.extract 0 n).map (·.toNat)).getD q 0 = (w.getD q 0).toNat := by
  have h1 : q < w.size := Nat.lt_of_lt_of_le hq hn
  have h2 : q < (w.extract 0 n).size := by
    rw [Array.size_extract]
    omega
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map,
    Array.getElem?_eq_getElem h2, Array.getElem?_eq_getElem h1, Array.getElem_extract]
  simp

/-- CONDITIONAL: on hr. **THE LOT's OWN READER OF THE TOKENS READS THE PROMPT THAT THE LIBRARY
DECODES.** xi: an instance. rq: what the library's decoder returns at its request bytes. -/
theorem tokens_k4 (xi : ProofFile.Inst) {rq : Req} (hr : Meaning.backReq xi.pub.request = some rq) :
    TokensArePrompt k4Tokens xi := by
  intro q hq
  have eT : 2 ^ DF.lT = ppref.T := rfl
  rw [eT] at hq
  rw [hr, Option.getD_some]
  unfold Meaning.backReq at hr
  obtain ⟨i, hi, h2⟩ := Option.bind_eq_some_iff.1 hr
  split at h2
  · rename_i hw
    obtain rfl : (⟨i, hw⟩ : Req) = rq := Option.some.inj h2
    unfold OnBytes.Flat.unlayB at hi
    split at hi
    · rename_i hfit
      obtain rfl := Option.some.inj hi
      have hsz : (Verify.words32 xi.pub.request).size = ppref.T + 2 := hfit.2.1
      show (k4Tokens xi).getD q 0 = Inst.Model.All.tokOf _ q
      unfold Inst.Model.All.tokOf
      rw [dif_pos hq]
      exact getD_words (Verify.words32 xi.pub.request) ((Verify.words32 xi.pub.request).size - 2) q
        (by omega) (by omega)
    · cases hi
  · cases h2

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.getD_words
#print axioms ProofFile.Honest.K4.W.tokens_k4
