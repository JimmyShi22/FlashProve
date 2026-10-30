-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/Q38E/DigAtHead.lean: at every one of the 25 segments of the first chain, the
reader `First.Look.digAt` (Johnson/Desc/First/Look/K3CallerTests.lean) answers at the closed
letters' public data: the place of the lookup on the segment's digits, and the structure of its
approximate range proof. In scope, wherever the value is laid. No test on written values is called
and nothing is evaluated.

Row or tool. Laws in scope, each a call of the library's laws. For the law on the digits of the
sub-protocol K8: the condition `DigAheadOk` at the state behind the draw of the approximate range
proof.

A twin, said plainly. Johnson/P1K8R/DigThereAll.lean has "the reader answers at every segment" as a
statement of its own (`digThere_at_head`), by another road.

What it spends. Rows are those of the proof file's entry tests, `LPFD.lawsAsk`
(Johnson/Desc/Laid/ProofAsks.lean), counted from 1: row 1 holds the
declared rounds to the written ones, row 9 the made plan (`madeRow`), row 11 is the lookups' digits'
row (`digEntry`). `links_25`: no row: the scope and the field `publicO` of `LaidAt`.
`digOK_at_name`, `digAt_at_name`, `digAt_at_head`: row 11, through the fields `asks` and `pub` of
`LaidAt`, and `links_25`.

Why it holds. Where the value is laid every entry test has accepted (`LaidAt.asks`).
`LPFD.asks_rest` (Johnson/Desc/Laid/ProofAsksLaw2.lean) gives row 11's accept at the public part,
and `K3Asks.digEntry_gives` (Johnson/Desc/First/Look/K3AsksDoorLaw.lean) unfolds it: at every
segment below `K3Asks.linksOf` the reader answers, and the lookups' condition on public data `DigOK`
holds at every radius. `linksOf` is 25 by `publicO_at_scope`
(Johnson/Desc/K12/Law/Sizes/PublicOAtScope.lean).

What is here (namespace Q38). General in the letter o (the second hash function), but for the last.
  `links_25`: in scope, where the value is laid: `K3Asks.linksOf Zp.p.X = 25`.
  `digOK_at_name`: for l up to 24 and every radius: there are x and tl with `digAt (At.X Zp) l =
    some (x, tl)` and `DigOK` at them.
  `digAt_at_name`: its first half alone.
  `digAt_at_head`: the same at the one head.

Limits. Which x and tl is not said. Over entry tests without row 11 the last three
cannot be had. Nothing on soundness.


-/
import Johnson.P5J.MgAtAll
import Johnson.Desc.Laid.ProofAsksLaw2
import Johnson.Desc.First.Look.K3AsksDoorLaw
import Johnson.Desc.K12.Law.Sizes.PublicOAtScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Q38
open OnBytes
open P5J (LaidAt AtMgA TS)
open VerifiableInference.Desc (Chain K3Asks.linksOf K3Asks.digEntry_gives K3Asks.sentOf)
open VerifiableInference.Desc.First.Look (digAt DigOK Place)

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The first chain has 25 segments. -/
theorem links_25 (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) : K3Asks.linksOf Zp.p.X = 25 := by
  have hF := H2K.Sizes.publicO_at_scope hZ L.publicO
  unfold K3Asks.linksOf
  rw [hF.p4, hF.groups]
  rfl

/-- **At every segment the reader answers, and the lookups' condition holds at every radius.** -/
theorem digOK_at_name (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {l : ℕ} (hl : l ≤ 24)
    (rad : OracleShape → ℕ) :
    ∃ x tl, digAt (P5J.At.X Zp) l = some (x, tl) ∧
      DigOK (Params.settingOf (P5J.At.X Zp).P.frame) x tl (K3Asks.sentOf Zp).up rad Cb.Gl.p :=
  K3Asks.digEntry_gives (LPFD.asks_rest L.asks L.pub).1 rad l (by rw [links_25 hZ L]; omega)

/-- **At every segment the reader answers.** -/
theorem digAt_at_name (hZ : VerifierAndGoals.InScope Z = true)
    (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {l : ℕ} (hl : l ≤ 24) :
    ∃ x tl, digAt (P5J.At.X Zp) l = some (x, tl) :=
  let ⟨x, tl, e, _⟩ := digOK_at_name hZ L hl fun _ => 0
  ⟨x, tl, e⟩

end

/-- **At the one head.** -/
theorem digAt_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x₀ : Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {l : ℕ} (hl : l ≤ 24) :
    ∃ x tl, digAt (P5J.At.X Zp) l = some (x, tl) :=
  digAt_at_name h.scope h.laid hl

end Q38


#print axioms Q38.links_25
#print axioms Q38.digOK_at_name
#print axioms Q38.digAt_at_name
#print axioms Q38.digAt_at_head
