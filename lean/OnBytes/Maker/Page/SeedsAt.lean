-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/SeedsAt.lean: at which chain queries under the tag of Test the code of the seeds'
two queries writes nothing: by the query's head and round, and at round 2 by its plain part; and
what the plain part `SeedVals.plainFirst` is at the rounds of a whole file.

The seeds' code writes at `⟨1, .f1 (cm :: cfgL) none sh, [], p0⟩` and at `⟨2, .f2 none v, [], p1⟩`
alone (`seeds_writes`, OnBytes/Maker/Page/Holes.lean). A key file's own queries stand under the same
tag.

Main names.
  `Quiet ... q`: at the query q the seeds' code writes nothing, at any block.
  `quiet_f1`: a query in the first format at a round other than 1. `quiet_f3`, `quiet_f4`,
    `quiet_f5`: every query in these formats. `quiet_f2`: a query in the second format, unless its
    round is 2 and its plain part is p1.
  `ne_of_parts`: two plain parts that `partAt` (OnBytes/Maker/Page/Fill.lean) reads as a written
    round's and as the front round's are different.
  `partOf_plainFirst`: at the rounds of a whole file `SeedVals.plainFirst` is the front round's
    part, with the front's fixed message.
  `quiet_row`: so a query in the second format whose plain part is read as a written round's is
    quiet, where p1 is read as the front round's.

Limits: that a verifier's query of a written round bears a plain part that `partAt` reads as a
written round's is not shown here. OnBytes/Maker/Page/FillLine.lean has, under a law on the
read-back, that it is read as `PartJ.ofSaid …`: a written round's or nothing;
OnBytes/Maker/Page/QuietPays.lean goes by that and `quiet_f2`, not by `quiet_row`. Nobody calls
`quiet_row`, and `ne_of_parts` is called by it alone. `gJ P O` is a function of the typed query, no
one-to-one coding. Nothing on soundness.


-/
import OnBytes.Maker.Page.Holes
import OnBytes.Maker.Page.FillLaws
import OnBytes.TypedOracleCompiler.Run.SeedVals

set_option autoImplicit false

namespace OnBytes.Maker.Page
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Run.SeedPoints
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ _root_.Compile.Joined

variable {I X : Type} (L : BatchProtocolWithLeafBody I X) (p0 p1 : PBt L .test) (isP0 isP1 : PBt L .test → Bool)
  (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (K : ℕ)

/-- At the query q the seeds' code writes nothing, at any block. -/
def Quiet (q : FbIn 256 L .test) : Prop :=
  ∀ j, (fbSeeds L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K).put (q, j) = none

/-- A query in the first format at a round other than 1. -/
theorem quiet_f1 (i : ℕ) (hi : i ≠ 1) (cms : List (Dig 256)) (x : Option X) (salt : Bits)
    (rt : List (Dig 256)) (pl : PBt L .test) :
    Quiet L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K ⟨i, .f1 cms x salt, rt, pl⟩ := fun j =>
  seeds_none L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K _ j
    (fun _ e => hi (congrArg FbIn.round e)) (fun _ e => by
      have h := congrArg FbIn.head e
      cases h)

/-- A query in the second format, unless its round is 2 and its plain part is p1. -/
theorem quiet_f2 (i : ℕ) (xl : Option X) (ρ : Bits) (rt : List (Dig 256)) (pl : PBt L .test)
    (h : i = 2 → pl ≠ p1) :
    Quiet L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K ⟨i, .f2 xl ρ, rt, pl⟩ := fun j =>
  seeds_none L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K _ j
    (fun _ e => by
      have h := congrArg FbIn.head e
      cases h)
    (fun _ e => h (congrArg FbIn.round e) (congrArg FbIn.plain e))

theorem quiet_f3 (i : ℕ) (ρ0 c : Bits) (rt : List (Dig 256)) (pl : PBt L .test) :
    Quiet L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K ⟨i, .f3 ρ0 c, rt, pl⟩ := fun j =>
  seeds_none L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K _ j
    (fun _ e => by
      have h := congrArg FbIn.head e
      cases h)
    (fun _ e => by
      have h := congrArg FbIn.head e
      cases h)

theorem quiet_f4 (i : ℕ) (cms : List (Dig 256)) (rtreq : Bits) (rt : List (Dig 256))
    (pl : PBt L .test) :
    Quiet L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K ⟨i, .f4 cms rtreq, rt, pl⟩ := fun j =>
  seeds_none L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K _ j
    (fun _ e => by
      have h := congrArg FbIn.head e
      cases h)
    (fun _ e => by
      have h := congrArg FbIn.head e
      cases h)

theorem quiet_f5 (i : ℕ) (ρ : Bits) (rt : List (Dig 256)) (pl : PBt L .test) :
    Quiet L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K ⟨i, .f5 ρ, rt, pl⟩ := fun j =>
  seeds_none L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K _ j
    (fun _ e => by
      have h := congrArg FbIn.head e
      cases h)
    (fun _ e => by
      have h := congrArg FbIn.head e
      cases h)

/-! ## The plain part at round 2 -/

section
variable (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) {t : Tag}
  (rd : PBt L t → Option (PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann))

/-- Two plain parts that are read as a written round's and as the front round's are different. -/
theorem ne_of_parts (x y : PBt L t) (i : ℕ) (m : List ByteArray → ByteArray) (n : ℕ) (p : TF)
    (hx : partAt C D tF tJ t3 rd x = .row i m n) (hy : partAt C D tF tJ t3 rd y = .front p) :
    x ≠ y := fun e => by
  rw [e, hy] at hx
  cases hx

/-- At the rounds of a whole file `SeedVals.plainFirst` is the front round's part. -/
theorem partOf_plainFirst :
    partOf C D tF tJ t3 (SeedVals.plainFirst _ _ (chainsOf C D tF tJ t3).ann.1
      (chainsOf C D tF tJ t3).ann.2) = .front tF :=
  partOf_front C D tF tJ t3 tF

end

/-- A query in the second format whose plain part is read as a written round's is quiet, where p1
is read as the front round's. -/
theorem quiet_row (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
    (rd : PBt L .test → Option (PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann))
    (p : TF) (h1 : partAt C D tF tJ t3 rd p1 = .front p) (i : ℕ) (xl : Option X) (ρ : Bits)
    (rt : List (Dig 256)) (pl : PBt L .test) (i' : ℕ) (m : List ByteArray → ByteArray) (n : ℕ)
    (hpl : partAt C D tF tJ t3 rd pl = .row i' m n) :
    Quiet L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K ⟨i, .f2 xl ρ, rt, pl⟩ :=
  quiet_f2 L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K i xl ρ rt pl fun _ =>
    ne_of_parts L C D tF tJ t3 rd pl p1 i' m n p hpl h1

end OnBytes.Maker.Page
