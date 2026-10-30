-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Total/HandsCalls.lean: the kind "lookup" (K3). Conditional,
under the library's hypothesis `P5J.AtMgA`: at the lookup on the calls of every one of the 25 links
the first chain's member hands the table's Boolean tests on: the library's `IM.HandsR`
(Johnson/IMR/HandsFence.lean: "what one sub-protocol owes, at the fenced states"), all six fields,
at the library's narrow fence `IM.RB` ("reached by the wrapped sub-protocols' steps"); and the same
as one sentence on two states. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: a state s bears no mark if `s.failed = none`. The
lookups' 50 members stand at the numbers `k3K l d` of the flat list
(Johnson/Desc/First/Look/K3Base.lean): l < 25 is the link; d is false for the lookup on the calls
and true for the lookup on the digits. The step's acceptance alone from s to s' is `IM.Yes 0 b s s'`
(Johnson/IMR/HandsDef.lean). The table is the table of borders (Johnson/Desc/First/Borders.lean). A
state is fenced if `IM.RB` (Johnson/IMR/GrownRch.lean) holds of it. The five tests are `IM.XK`
(HandsDef.lean) at the public items' test: where the verifier stands; the open rows' lists; the
groups' members; the book; the public items' test. "In order", the sixth test of the table's
promise, is not among them. In the statements EP is a local notation: EP z k s is the public items'
test at border k (`ePubAt`). Two more local notations: 𝔐 is `AtMg.𝔇` at the head h (the composed
meaning's data there); baseP is the field pub of `mgBase`.

What is shown.
  `ep_is_ew`: the public items' test at the composed meaning's own letters is the library's constant
    test `LPFK9.HandsAt.EW` (Johnson/LPFK9R/SharesAtE.lean).
  `handsR_calls`: `IM.HandsR` at the calls of all 25 links, at the fence `IM.RB`, at the test
    `LPFK9.HandsAt.EW`, at the written lists `IM.linksW` and `IM.placesW`
    (Johnson/IMR/WrittenList.lean), at the first tree 0.
  `xk_next_calls`: from a fenced state without a mark at which the five tests hold, over the
    acceptance alone of the member's step to a state without a mark: the five tests hold behind. It
    is stated at `P5J.At.N Zp cF`, `P5J.At.links`, `P5J.At.ps` and the public items' test of
    `P5J.mgAtAll h`.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean).
  `hl`, `hb`: the link is below 25; b is the member at the number `k3K l false`.
  `hf`, `hy`, `h0`, `h1`, `hx`: (in `xk_next_calls`) s is fenced; the step's acceptance alone from s
    to s'; s bears no mark; s' bears no mark; the five tests hold at s. No other hypothesis is made
    on a state.

Imported. Honest/K3/Law/Total/MadeOwedCallsHead.lean and files of the library. No module under
Johnson/Goal/ is imported directly.
Follows. The way from `IM.MadeOwed` to `IM.HandsR` by the library's `IM.rows_at_rch`
(Johnson/IMR/RowsAtRch.lean) and `IM.rows_at_plan` (Johnson/IMR/RowsAtPaid.lean) was pointed out in
the work on K11's files.

How the proof goes. `handsR_calls` is one call of `IM.rows_at_rch` on `madeOwed_calls`
(MadeOwedCallsHead.lean). `xk_next_calls` follows by the library's `IM.HandsR.step`
(HandsFence.lean). The equations between letters that the proofs use are of two sorts. By the
library's lemmas (Johnson/P5J/FoldJ3.lean): the written list of links is that of `P5J.AtMgA`
(`linksW_at`); the written list of places likewise (`placesW_at`); the numbers `P5J.At.N Zp cF` are
some numbers closed over what the chain's members tell, at the written places, which is the form
that `IM.rows_at_rch` asks (`N₀_told`); the composed meaning's list of extra public tests is the
closed one (`mgAll_more_closed`, Johnson/Desc/Sound/MgAllAt.lean). By the texts alone (`rfl`, as
Lean checks): `P5J.mgAtAll h` is the composed meaning over the closed meaning beneath; its public
items' test is `pubAll` (Johnson/Desc/First/PubAll.lean) at its data; the two closed lists of extra
tests are one; the data's numbers are `P5J.At.N Zp cF`.

Users. `step_calls_whole` (Honest/K3/Law/Total/StepWhole.lean) calls `xk_next_calls`, which is
stated so as to meet a lemma of the files under Honest/Thread/ that takes "the
five Boolean tests at a test that gives the public items' test" behind a step. The terms
`P5J.At.N Zp cF`, `P5J.At.links`, `P5J.At.ps` and `P5J.mgAtAll h` are those in which it
was asked for.

Options. `maxRecDepth` is raised to 100000 for the file; `quotPrecheck` is off at two local
notations. These raise limits on Lean's own work or switch off a check on a notation's names: none
loosens a check on a proof.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
`P5J.AtMgA` is a hypothesis; no state is shown to be reached. The Boolean tests alone: nothing on
what a public item says beside its test, on the samples, on "in order" or on the witness. The calls
alone: nothing at the lookups on the digits. At the full size alone.
`handsR_calls` stands at the test `LPFK9.HandsAt.EW`, which is the public items' test alone, not at
`P1K2.EQ` (Johnson/P1K2R/TieTwo.lean), which has "in order" besides.
That lemma's file is not imported here;
see the head of Honest/K3/Law/Total/NoMarkBehind.lean.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Total.MadeOwedCallsHead
import Johnson.IMR.RowsAtRch
import Johnson.P5J.MgAtAll
import Johnson.P5J.FoldJ3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Total
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ePubAt)
open P5J

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)

set_option quotPrecheck false in
local notation "𝔐" => AtMg.𝔇 (AtMgA.toAtMg h) (AtMgA.𝔇 h)
local notation "baseP" => Desc.First.Meaning.pub (mgBase : Desc.First.Meaning ProofFile.InstPub
  (Desc.Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT))
set_option quotPrecheck false in
local notation "EP" => fun (z : ProofFile.InstPub) (k : ℕ) (s : TS) =>
  ePubAt (mgAtAll h).pub (mgAtAll h).more At.links At.ps k (z, s)

/-- **The public items' test at the composed meaning's own letters is the library's constant test.**
Conditional on `P5J.AtMgA`. No instance of these hypotheses is exhibited in this file. -/
theorem ep_is_ew (z : ProofFile.InstPub) : EP z = LPFK9.HandsAt.EW (𝔐).pubD baseP z := by
  funext k s
  unfold LPFK9.HandsAt.EW
  rw [linksW_at, placesW_at]
  show ePubAt (mgAll (𝔐) mgBase).pub (mgAll (𝔐) mgBase).more _ _ k (z, s) = _
  rw [mgAll_more_closed (𝔐) mgBase rfl]
  rfl

/-- **`IM.HandsR` at the calls of every link, at the narrow fence.** Conditional on `P5J.AtMgA`; a
link below 25; b being the member at the number. No instance of these hypotheses is exhibited in
this file. -/
theorem handsR_calls {l : ℕ} (hl : l < 25) {b : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l false]? = some b) (z : ProofFile.InstPub) :
    IM.HandsR (IM.RB cF Zp z) (At.N Zp cF) IM.linksW IM.placesW
      (LPFK9.HandsAt.EW (𝔐).pubD baseP z) 0 (k3K l false) b := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hpl : b.place = IM.k3Place l false := by
    have e1 := IM.place_at h.scope h.reads O hb
    rw [IM.placesW_full, K3Lot.k03_at_full l hl false] at e1
    exact (Option.some.inj e1).symm
  have M := madeOwed_calls h hl hb z (IM.RB cF Zp z) (fun _ hs => hs)
  have M' : IM.MadeOwed (IM.RB cF Zp z) (At.N Zp cF) IM.linksW IM.placesW (𝔐).pubD baseP z 0
      (k3K l false) b b.place := M
  rw [← N₀_told Zp cF] at M' ⊢
  exact IM.rows_at_rch h.scope h.reads O h.laid.planOk _ (fun _ _ _ => rfl) hb
    (by rw [hpl]; rfl) M'

/-- **The five Boolean tests pass over the step's acceptance alone**, in the terms of the files
under Honest/Thread/. Conditional on `P5J.AtMgA`; a link below 25; b being the member at the
number; s being fenced; the step's acceptance alone from s to s'; no mark at either; the five tests
at s. No instance of these hypotheses is exhibited in this file. -/
theorem xk_next_calls {l : ℕ} (hl : l < 25) {b : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[k3K l false]? = some b) (z : ProofFile.InstPub) {s s' : TS}
    (hf : IM.RB cF Zp z (k3K l false) s) (hy : IM.Yes 0 b s s') (h0 : s.failed = none)
    (h1 : s'.failed = none)
    (hx : IM.XK (At.N Zp cF) At.links At.ps (EP z) (k3K l false) s = true) :
    IM.XK (At.N Zp cF) At.links At.ps (EP z) (k3K l false + 1) s' = true := by
  rw [ep_is_ew h z, ← linksW_at, ← placesW_at] at hx ⊢
  exact (handsR_calls h hl hb z).step hf hy h0 h1 hx

end ProofFile.Honest.K3.Law.Total

#print axioms ProofFile.Honest.K3.Law.Total.ep_is_ew
#print axioms ProofFile.Honest.K3.Law.Total.handsR_calls
#print axioms ProofFile.Honest.K3.Law.Total.xk_next_calls
