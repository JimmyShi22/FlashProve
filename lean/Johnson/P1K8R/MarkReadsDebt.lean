-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/MarkReadsDebt.lean: THE MARK AT THE OWN ROUNDS OF AN ATTENTION SEGMENT FOR THE WEIGHTS
OF TWO OF ITS TABLES (`mkReads`, Johnson/Desc/ProofFile/Honest/K5/Law/MarkReads.lean): ITS SENTENCE
`MarkDebt` (Johnson/Desc/ProofFile/Honest/Law/CoverJoin.lean) AT STRINGS OF HASH BLOCKS, AT ITS OWN
STATED SHARE's VALUE. Lemmas; NONE OF THE LIBRARY's GOALS. Nothing on completeness, soundness or
hiding.

  `anyBad_eq`   the walk over a member's challenges as that file writes it is the walk of
      Johnson/P1K8R/MarkRounds.lean
  `PscData w ds L`   the one premise on the data, by name: at each listed number the round's data
      bear the entry of a masked sumcheck's round (one element, which may be 0), and a kind that is
      neither that of seeds nor the sealed one
  **`reads_markDebt_blocks`**   under `PscData w ds (readRounds x g)`: `MarkDebt` of `mkReads l x g`
      at Run.ckP .two, the data ds, whatever sentence on the challenges in front, and the mark's
      stated share's value
By: `markDebt_of_list_blocks` (Johnson/P1K8R/MarkRounds.lean) · mkReads_walk (MarkReads.lean) ·
bad01_elem (Johnson/Desc/K5/Honest/Law/MarkTest.lean) · read_draws, read_logN (MarkForm.lean).
Limits. `PscData` is a premise: that the chain's own stretch of data at the member meets it is not
shown here. No number is evaluated. The mark covers two of the segment's matrices.

-/
import Johnson.P1K8R.MarkRounds
import Johnson.Desc.ProofFile.Honest.K5.Law.MarkReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open OnBytes.Maker (RDT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att.P (Geo)
open VerifiableInference.Desc.First.K8.Honest (OneElem)
open ProofFile.Honest (Mark MarkDebt)
open ProofFile.Honest.K5 (mkReads mkReads_walk)
open H2K5.Honest (readRounds bad01 bad01_elem read_draws read_logN)

/-- The two walks are one. -/
theorem anyBad_eq (bad : Fmt.Drawn → Bool) (mk : ℕ → Bool) : ∀ (own : List Fmt.Drawn) (j : ℕ),
    H2K5.Honest.anyBad bad mk j own = anyBad bad mk j own
  | [], _ => rfl
  | x :: l, j => by
    show ((mk j && bad x) || H2K5.Honest.anyBad bad mk (j + 1) l) =
      ((mk j && bad x) || anyBad bad mk (j + 1) l)
    rw [anyBad_eq bad mk l (j + 1)]

/-- The one premise on the data. -/
def PscData (w : ℕ) (ds : List RDT) (L : List ℕ) : Prop :=
  ∀ i d, ds[i]? = some d → i ∈ L →
    d.entry = { Part.MaskedSum.entry "PSC round" 3 1 0 with work := w } ∧ d.kind ≠ .seeds ∧
      d.kind ≠ .sealed

/-- **The mark's sentence at strings of hash blocks.** -/
theorem reads_markDebt_blocks (l : ℕ) (x : OnBytes.Params.AttentionRounds) (g : Geo) (w : ℕ)
    (ds : List RDT) (hd : PscData w ds (readRounds x g)) (Q : List Fmt.Drawn → Prop) :
    MarkDebt (_root_.Run.ckP .two) (mkReads l x g) ds Q (mkReads l x g).share.val := by
  refine markDebt_of_list_blocks (mkReads l x g) bad01 (readRounds x g) ds ?_
    (fun dr y hb he => bad01_elem hb he) ?_ rfl Q
  · intro fr own h
    rw [← anyBad_eq]
    exact mkReads_walk l x g fr own h
  · intro i d hi hL
    obtain ⟨e1, e2, e3⟩ := hd i d hi hL
    rw [e1]
    exact ⟨read_draws w e2 e3, by rw [read_logN]; exact Nat.zero_le _⟩

end P1K8

#print axioms P1K8.anyBad_eq
#print axioms P1K8.reads_markDebt_blocks
