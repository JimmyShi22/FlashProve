-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/QuietPays.lean: the condition on a file's own chain queries that
OnBytes/Maker/Page/RowsAt.lean asks (`QuietAt`) is met: under the key file's tag at "the seeds' code
writes nothing at this query" (`Quiet`, OnBytes/Maker/Page/SeedsAt.lean), and under any tag at the
condition that is always true.

Why. Under the key file's tag two spellings meet: the seeds' two chain queries, which go first, and
the key file's three chains. The laws on the typed oracle functions hold at the queries at which the
first is silent. The seeds' code writes at a query of the first format at round 1 and at a query of
the second format at round 2 with one fixed plain part p1. The key file's own queries are none of
these: by the form of the head and the round's number, but at round 2; there by the plain part: p1
is read as the front round's, and a written round's plain part as embedded is not.

  `ne_p1_one`, `ne_p1_three`: a plain part of the first or the third stretch as embedded is not p1.
  `quietAt_test`: `QuietAt` at `Quiet`.
  `quietAt_true`: `QuietAt` at the condition that is always true.

Two hypotheses: the read-back `rd` undoes the embedding `embP`; `rd` reads p1 as the front round's
message.


-/
import OnBytes.Maker.Page.RowsAt
import OnBytes.Maker.Page.SeedsAt

set_option autoImplicit false

namespace OnBytes.Maker.Page

open Rom TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Joined.K TypedOracleCompiler.Compile.Batch
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ _root_.Compile.Joined
open _root_.Run.Twin (allLo)

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} (C : CK) (Dw : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ)
  (t3 : T3)

section Test
variable (rd : PBt L .test → Option (PlainPart (chainsOf C Dw tF tJ t3).sh (chainsOf C Dw tF tJ t3).ann))
  (Sl : SilentJ X TF TJ T3)
  (embP : PlainPart (chainsOf C Dw tF tJ t3).sh (chainsOf C Dw tF tJ t3).ann → PBt L .test)
  (hrd : ∀ w, rd (embP w) = some w) (p1 : PBt L .test) (p : TF)
  (h1 : partAt C Dw tF tJ t3 rd p1 = .front p)
include hrd h1

theorem ne_p1_one (z : PlainPart (TypedOracleCompiler.Run.PQ.uL C (toRDs Dw.ds₁)) (allLo (SLT C Dw.ds₁))) :
    e₁ C Dw tF tJ t3 embP (Sum.inr z) ≠ p1 := fun e =>
  ofSaid_ne_front _ _ p ((partAt_one C Dw tF tJ t3 rd embP hrd z).symm.trans
    ((congrArg (partAt C Dw tF tJ t3 rd) e).trans h1))

theorem ne_p1_three (z : PlainPart (TypedOracleCompiler.Run.PQ.uL C (toRDs Dw.ds₃)) (allLo (SLT C Dw.ds₃))) :
    e₃ C Dw tF tJ t3 embP (Sum.inr z) ≠ p1 := fun e =>
  ofSaid_ne_front _ _ p ((partAt_three C Dw tF tJ t3 rd embP hrd z).symm.trans
    ((congrArg (partAt C Dw tF tJ t3 rd) e).trans h1))

/-- **At the key file's own chain queries the seeds' code writes nothing.** -/
theorem quietAt_test (p0 : PBt L .test) (isP0 isP1 : PBt L .test → Bool) (cfgL : List (Dig 256))
    (sh : Bits) (hp0 : ∀ q, isP0 q = true ↔ q = p0) (hp1 : ∀ q, isP1 q = true ↔ q = p1)
    (rest : ByteArray) (K : ℕ) (cms : List (Dig 256)) (x : Option X) (salt rtreq ρ0 c : Bits)
    (pF : TF) (pJ : TJ) (p3 : T3) :
    QuietAt C Dw tF tJ t3 rd Sl (Quiet L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K) embP cms x salt
      rtreq ρ0 c pF pJ p3 where
  one := fun i ρ rt z => quiet_f2 L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K i none ρ rt _ fun _ =>
    ne_p1_one C Dw tF tJ t3 rd embP hrd p1 p h1 z
  two := fun i ρ rt _ => quiet_f5 L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K i ρ rt _
  three := fun i ρ rt z => quiet_f2 L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K i none ρ rt _ fun _ =>
    ne_p1_three C Dw tF tJ t3 rd embP hrd p1 p h1 z
  first₁ := quiet_f1 L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K 0 (by decide) cms x salt [] _
  first₂ := quiet_f4 L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K _ cms rtreq [] _
  first₃ := quiet_f3 L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K _ ρ0 c [] _

end Test

/-- At the condition that is always true. -/
theorem quietAt_true {t : Tag}
    (rd : PBt L t → Option (PlainPart (chainsOf C Dw tF tJ t3).sh (chainsOf C Dw tF tJ t3).ann))
    (Sl : SilentJ X TF TJ T3)
    (embP : PlainPart (chainsOf C Dw tF tJ t3).sh (chainsOf C Dw tF tJ t3).ann → PBt L t)
    (cms : List (Dig 256)) (x : Option X) (salt rtreq ρ0 c : Bits) (pF : TF) (pJ : TJ) (p3 : T3) :
    QuietAt C Dw tF tJ t3 rd Sl (fun _ => True) embP cms x salt rtreq ρ0 c pF pJ p3 :=
  ⟨fun _ _ _ _ => trivial, fun _ _ _ _ => trivial, fun _ _ _ _ => trivial, trivial, trivial,
    trivial⟩

end

end OnBytes.Maker.Page
