-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/ReaderPays.lean: two ways to prove parts of the hypothesis
`ReaderAt` (Law/Rule/ReaderAt.lean). It holds three lemmas and no definition.

Three of the six facts of `ReaderAt` are the library's own definition `MaskAt own xM R s`
(Johnson/Top/H0/MergeLaw/MaskRow.lean) at R = 0: the frame names the message that holds the mask
row, the book of trees gives it the member's seat, and its mask table has one row. Whoever has
`MaskAt` at a state has these three by one call.

The sixth fact, that no entry below `free` is a place of the sample's pad, depends only on the
member's shape. The library's `padB` (Johnson/Desc/SeatAt.lean) accepts, in the mask table, only the
last place of the last mask row. So with one mask row every entry but the last is outside the pad,
and the library's count of free mask entries at one row and one answer
(`Send.freeMaskEntries`, OnBytes/Iop/Send.lean) is the message length less one.

  1  `noPad_one`, `noPad_free`   the sixth fact, from a bound on `free`; the same at the library's
     count of free entries at one row and one answer
  2  `readerAt_of_maskAt`   `ReaderAt` from the library's `MaskAt`, the member found at its seat,
     its number, and the sixth fact

Limits.
  * The first two lemmas speak of row 0 of the mask table only; that row 0 is the only row is fact
    (v) of `ReaderAt`, not theirs. `noPad_free` is at one row and one answer. `padB` itself is
    written for one answer.
  * Nothing here shows `MaskAt`, the member, or its number at a state of the protocol.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.ReaderAt
import Johnson.Top.H0.MergeLaw.MaskRow
import OnBytes.Iop.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (padB)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (Mem seatOf numOf)
open VerifiableInference.Desc.First.MergeLaw (MaskAt)

/-! ## 1 The sixth fact -/

/-- In row 0 of the mask table, a place below `free` is outside the pad if `free` is below the
message length. -/
theorem noPad_one {cs : OnBytes.Codes} {sh : OnBytes.OracleShape} {free : ℕ}
    (hf : free + 1 ≤ (cs.mask.getD sh.maskCode default).ell) :
    ∀ ν, ν < free → padB cs sh true 0 ν = false := by
  intro ν hν
  show ((0 + 1 == sh.maskRows) && (ν + 1 == (cs.mask.getD sh.maskCode default).ell)) = false
  rw [Bool.and_eq_false_iff]
  right
  exact beq_false_of_ne (by omega)

/-- The same below the library's count of free mask entries at one row and one answer. -/
theorem noPad_free {cs : OnBytes.Codes} {sh : OnBytes.OracleShape}
    (h1 : 1 ≤ (cs.mask.getD sh.maskCode default).ell) :
    ∀ ν, ν < OnBytes.Send.freeMaskEntries 1 (cs.mask.getD sh.maskCode default).ell 1 →
      padB cs sh true 0 ν = false := by
  refine noPad_one ?_
  unfold OnBytes.Send.freeMaskEntries
  have hc : ((1 : ℕ) == 0 || decide ((cs.mask.getD sh.maskCode default).ell < 1)) = false := by
    rw [Bool.or_eq_false_iff]
    exact ⟨rfl, decide_eq_false (by omega)⟩
  rw [if_neg (by rw [hc]; exact Bool.false_ne_true)]
  omega

/-! ## 2 From the library's `MaskAt` -/

/-- Three of the six facts of `ReaderAt` are the library's `MaskAt` at R = 0. `hx`: the member is
the first of `ms` at its own seat. `hn`: its number in the witness. `hp`: the sixth fact. -/
theorem readerAt_of_maskAt {cs : OnBytes.Codes} {arr : ℕ → ℕ → ℕ} {ms : List Mem}
    {own : List (ℕ × ℕ)} {xM : Mem} {s : VerifiableInference.Desc.First.S}
    {a : VerifiableInference.Desc.K9.Part} {n free : ℕ} (hM : MaskAt own xM 0 s)
    (ha : segAt? s = some a)
    (hx : ms.find? (fun z => decide (seatOf z = seatOf xM)) = some xM) (hn : numOf arr xM = n)
    (hp : ∀ ν, ν < free → padB cs (xM.1.l.get xM.2).1 true 0 ν = false) :
    ReaderAt cs arr ms own a n free := by
  obtain ⟨a9, o, e9, ho, hs, hR⟩ := hM
  obtain rfl : a9 = a := Option.some.inj (e9.symm.trans ha)
  exact ⟨o, seatOf xM, xM, ho, hs, hx, hn, hR, hp⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.noPad_one
#print axioms ProofFile.Honest.noPad_free
#print axioms ProofFile.Honest.readerAt_of_maskAt
