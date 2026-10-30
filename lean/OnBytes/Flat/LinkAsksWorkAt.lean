-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinkAsksWorkAt.lean: OnBytes/Flat/LinkAsksWork.lean at the written links of both sizes,
with what shows that it is not idle there.

`link_asks_work` says: where the written link accepts, every written round's test of work has
passed. If no round had a bit of work, or the link accepted nothing, that would hold for free.
`linkSibFull` and `linkSibSmall` (OnBytes/Flat/LinkSibAt.lean) are the written link at the written
rounds' data `dsFull`, `dsSmall`, with the program's own decision; they are the entry file's
protocol in OnBytes/Flat/FilesAt.lean. Statements and proofs; two evaluations in Lean's kernel.

Main names (namespace `OnBytes.Flat.Work`):
  `linkSibFull_asks_work`, `linkSibSmall_asks_work`: the law at these two protocols.
  `works_full`, `works_small`: the rounds' bits of work, in order, written out: 32 at 6 of 41 rounds
    and at 4 of 24, 0 at the others.
  `link_no_of_bit`: the law's other face, at all letters: where some entry of `workTestsL` says no,
    the link rejects, whatever its decision.
Near kin in the library, on other lists: `fr_work`, `sr_work` (OnBytes/Slice/FullRecRounds.lean,
SmallRecRounds.lean): the same numbers of `frD.ds`, `srD.ds`, the data in the first compiler's form,
which `PQ.ofLib` carries over to `dsFull`, `dsSmall`; `record_workRounds`,
`small_record_workRounds`, `work_bits` (OnBytes/K/Oracle/WorkRounds.lean): place, name and bits of
the rounds with work among the rounds that the dry run of the link's block states. `letters_full`,
`letters_small` (OnBytes/Flat/LinkSibAt.lean): `dsFull`, `dsSmall` are the rounds' data of the
entry's description at the two settings with a record.
That the small link accepts something: OnBytes/Flat/LinkSibAccepts.lean, its first test: yes at one
written transcript, by Lean's evaluator, not by the kernel. At the full size no file runs the link.
Limits: those of OnBytes/Flat/LinkAsksWork.lean. That a verifier in use has one of these two as its
entry file's protocol is not said here. That a bound counts these bits, and how, is not said here.
Nothing on soundness.

-/
import OnBytes.Flat.LinkAsksWork
import OnBytes.Flat.LinkSibAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Flat.Work
open Iop TypedOracleCompiler.Run.PQ OnBytes.Slice
open _root_.Run (ckP)
open _root_.Run.PQ (View SgX CK XO)

/-- The law at the written link of the full size. -/
theorem linkSibFull_asks_work (rr) (y) (τ : Tr linkSibFull.shape)
    (h : linkSibFull.accept rr y τ = true) :
    ∀ r ∈ workTestsL (ckP .two) dsFull τ.2.2, r.2 = true :=
  link_asks_work _ _ _ _ _ rr y τ h

/-- The law at the written link of the small example. -/
theorem linkSibSmall_asks_work (rr) (y) (τ : Tr linkSibSmall.shape)
    (h : linkSibSmall.accept rr y τ = true) :
    ∀ r ∈ workTestsL (ckP .two) dsSmall τ.2.2, r.2 = true :=
  link_asks_work _ _ _ _ _ rr y τ h

set_option maxRecDepth 1000000 in
/-- The written rounds' bits of work, full size. -/
theorem works_full : dsFull.map (·.entry.work) =
    [0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0,
    32, 0, 0, 0, 0, 0, 0, 32, 0, 32] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The written rounds' bits of work, small example. -/
theorem works_small : dsSmall.map (·.entry.work) =
    [0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32, 0, 0, 0, 0, 0, 0, 32, 0, 32] := by
  decide +kernel

/-- Where a round's test of work fails, the link rejects, whatever its decision. -/
theorem link_no_of_bit {Y : Type} (C : CK) (ds : List RD) (a : ℕ) (xs : List XO)
    (dec : Y → View → Bool) (x : Y) (y : (twoExternalStrings (2 ^ a) SgX).Str)
    (τ : Tr (linkProtocolOfRoundData C ds a xs dec).shape) (r : RD × Bool) (hr : r ∈ workTestsL C ds τ.2.2)
    (hb : r.2 = false) : (linkProtocolOfRoundData C ds a xs dec).accept x y τ = false := by
  cases h : (linkProtocolOfRoundData C ds a xs dec).accept x y τ with
  | false => rfl
  | true => exact absurd (link_asks_work C ds a xs dec x y τ h r hr) (by rw [hb]; decide)

end OnBytes.Flat.Work

#print axioms OnBytes.Flat.Work.linkSibFull_asks_work
#print axioms OnBytes.Flat.Work.linkSibSmall_asks_work
#print axioms OnBytes.Flat.Work.works_full
#print axioms OnBytes.Flat.Work.works_small
#print axioms OnBytes.Flat.Work.link_no_of_bit
