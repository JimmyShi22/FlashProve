-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingThinKeep.lean: `famC` (Run/CodingThin.lean) at the format's oracle, with the hash's state
kept after the whole blocks of what all blocks of one chain answer share. `famC` is the typed oracle
functions that the encoding of the queries reads out of the single oracle on bit strings. A theorem
of this file says that, under the hypotheses below, its typed oracle functions are `famC`. (The
hash: `Fmt.formatHash`, Fmt/Rules23.lean: BLAKE2b, no key, the start in its parameter block, of 16-byte label
and bytes.)

Definitions that compute; theorems with proofs.

Why: `famC` writes, for each of the K + 1 blocks of a chain answer, the encoding's string as bits,
turns it into bytes and hashes it whole. With a prover's message of 77,280 bytes and some eighty
blocks that is eighty times 618,000 bits and eighty times 604 compressions. But, under
`PageFit C D`, at a query that fits the format the encoding's string is the string of the format's
call (Run/CodingPut.lean; `PageFit`, Run/CodingAgree.lean), so the answer is the one that
Run/CodingFnKeep.lean computes from the call's data, the state kept: no string of bits is written at
all.

Main names:
  fits is a parameter: a test on a chain query that can be run without writing the string. Its law
    is a hypothesis of the tie (`famCKB_eq`, `famCK_eq`): where it says yes, the round is not 0 and
    the code of a round's query writes at every block.
  `famCKB Lf C D fits o q`: at a chain query under the tag of the data (a parameter tg) with fits q:
    Run/CodingFnKeep.lean's `blocksK` at D; else `famC`'s own bytes.
  `famCKB_eq`, `famCK_eq`: under PageFit C D and the law of fits, famCK (fun _ => L) C D fits = famC
    (fun _ => L) C oBy.

Limits: this file does not say that `PageFit` and the law of fits hold at a given description: other
files. Leaves, nodes, round 0 (under the law of fits) and all that does not fit: as in `famC`. This
file says nothing on time (measured outside this file) and nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingThin
import Run.CodingAgree
import Run.CodingFnKeep

set_option autoImplicit false

namespace Run
open Rom Compile Compile.Batch Iop

variable {I X : Type} {K : ℕ} (Lf : Unit → BatchProtocol I X) {tg : Tag}

/-- The answer as bytes. -/
def famCKB (C : PageC (Lf ()) K tg) (D : PageD (Lf ()) tg) (fits : FbIn 256 (Lf ()) tg → Bool) :
    (o : Batch.OracleName) → Batch.domOf 256 (Lf ()) o → Array ByteArray
  | .fb t', q =>
      match castTag (F := fun t => FbIn 256 (Lf ()) t) tg t' q with
      | some q' => if fits q' then blocksK Lf D K q' else famCB Lf C oBy (.fb t') q
      | none => famCB Lf C oBy (.fb t') q
  | o, q => famCB Lf C oBy o q

/-- The typed oracle functions read out of the single oracle, the state kept. -/
def famCK (C : PageC (Lf ()) K tg) (D : PageD (Lf ()) tg) (fits : FbIn 256 (Lf ()) tg → Bool) :
    Fam (spec 256 K (Lf ())) :=
  fun o q => famCD K o (famCKB Lf C D fits o q)

variable {L : BatchProtocol I X}

/-- The single oracle at the bits of a call's string whose first byte is not 4 (`h4`) is the
format's oracle at that string. -/
theorem oBy_call (c : _root_.Fmt.OQ) (h4 : ¬ bitsOfByte 4 <+: bytesToBits (strOf c)) :
    oBy (bytesToBits (strOf c)) = _root_.Fmt.oracle (strOf c) := by
  have hp : plainB (bytesToBits (strOf c)) = true := by
    unfold plainB
    rw [whole_bytesToBits, Bool.true_and, Bool.not_eq_true', beq_eq_false_iff_ne]
    intro h8
    exact h4 (h8 ▸ List.take_prefix 8 _)
  unfold oBy
  rw [toBytes_plain _ hp, bitsToBytes_bytesToBits]

/-- One block, under `PageFit C D` (`F`), at a round other than 0 (`h0`) and a block at which the
code of a round's query writes (`hj`). -/
theorem block_tie (C : PageC L K tg) (D : PageD L tg) (F : PageFit C D) (q : FbIn 256 L tg)
    (h0 : q.round ≠ 0) (j : Fin (K + 1)) (hj : ((p162 C.chain K).put (q, j)).isSome = true) :
    oBy (codeP (fun _ => L) C (.fb tg) q j) =
      bytesP _root_.Fmt.oracle (fbCallP (fun _ => L) D K q j) := by
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hj
  have hp : (pFb C).put (q, j) = some s := by rw [pFb_succ C q j h0]; exact hs
  have h4 : ¬ bitsOfByte 4 <+: s := (pFb_facts C (q, j) s hp).2 4 (by decide) (by decide)
  obtain ⟨c, hc, rfl⟩ := F.round (q, j) s hs
  rw [codeP_eq, theImpl_fb C q j _ hp, oBy_call c h4, fbCallP_eq]
  have hc' : fbCall D K q j = some c := hc
  rw [hc']
  rfl

/-- The bytes: under `PageFit C D` (`F`) and the law of fits (`hf`), `famCKB` is `famCB` at `oBy`.
-/
theorem famCKB_eq (C : PageC L K tg) (D : PageD L tg)
    (fits : FbIn 256 L tg → Bool) (F : PageFit C D)
    (hf : ∀ q,
      fits q = true → q.round ≠ 0 ∧ ∀ j : Fin (K + 1), ((p162 C.chain K).put (q, j)).isSome = true)
    (o : Batch.OracleName) (q : Batch.domOf 256 L o) :
    famCKB (fun _ => L) C D fits o q = famCB (fun _ => L) C oBy o q := by
  cases o with
  | fb t =>
      by_cases ht : t = tg
      · subst ht
        simp only [famCKB, castTag_self]
        split
        · rename_i h
          obtain ⟨h0, hj⟩ := hf q h
          rw [blocksK_eq]
          show (Array.ofFn (n := K + 1) fun j =>
              bytesP _root_.Fmt.oracle (fbCallP (fun _ => L) D K q j)) =
            Array.ofFn (n := K + 1) fun j => oBy (codeP (fun _ => L) C (.fb t) q j)
          congr 1
          funext j
          exact (block_tie C D F q h0 j (hj j)).symm
        · rfl
      · simp only [famCKB, castTag_ne ht]
  | leaf => rfl
  | node => rfl
  | fbw _ _ => rfl
  | rleaf => rfl
  | rnode => rfl
  | g _ => rfl
  | ann => rfl
  | other => rfl

/-- Under `PageFit C D` (`F`) and the law of fits (`hf`), `famCK` is `famC` at `oBy`. -/
theorem famCK_eq (C : PageC L K tg) (D : PageD L tg) (fits : FbIn 256 L tg → Bool) (F : PageFit C D)
    (hf : ∀ q, fits q = true →
      q.round ≠ 0 ∧ ∀ j : Fin (K + 1), ((p162 C.chain K).put (q, j)).isSome = true) :
    famCK (fun _ => L) C D fits = famC (fun _ => L) C oBy := by
  funext o q
  show famCD K o (famCKB (fun _ => L) C D fits o q) = famCD K o (famCB (fun _ => L) C oBy o q)
  rw [famCKB_eq C D fits F hf]

end Run
