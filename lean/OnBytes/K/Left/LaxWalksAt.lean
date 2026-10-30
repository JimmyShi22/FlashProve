-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxWalksAt.lean: what is owed for the walks (`WalkParts`,
OnBytes/K/Left/LaxWalks.lean), at the family that runs and the hash made of the realised oracle: the
four fields on hash and family are filled from the laws at the page (OnBytes/K/Left/LaxPages.lean,
LaxPagesOwnAt.lean); the ten on what was read, on the description and on the roots stay premises.

Main names:
  `ShapeFacts`: what the laws at the leaves ask of the shapes that are opened, of the run value and
    of the salt's length: named premises.
  `walkParts_at`: `WalkParts` at `EntryRunTop.famOf` and `hOfG oBits`; with `walks_of_parts` it
    gives the field "walks" of `LaxDebts` there.

Limits: `ShapeFacts` and the ten premises are shown of no file and no ground here. Fm and Rt are
letters. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.LaxWalks
import OnBytes.K.Left.LaxPagesOwnAt

set_option autoImplicit false

namespace OnBytes.K.Left
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Slice.EntryFill TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.Apart
open TypedOracleCompiler.Run.RowsG (hOfG)
open TypedOracleCompiler.Run.PQ (XD bodyS)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-- What the laws at the leaves ask: an own opening's shape is a tree of a round of the
description; a stored opening's shape has the tree's number 0, a width below 2^24 and a depth of at
most 63; the run value has 32 bytes; a salt has fewer than 2^11 bytes. -/
structure ShapeFacts (D : XD) (o : _root_.Fmt.ChainOut) : Prop where
  /-- an own opening's shape is a tree of a round of the description -/
  ownTree : ∀ op ∈ ownOps o, ∃ d ∈ D.ds, op.sh ∈ d.trees
  /-- a stored opening's shape has the tree's number 0 -/
  stoTree : ∀ op ∈ stoOps o, op.sh.tree = 0
  /-- and a width below 2^24 -/
  stoWidth : ∀ op ∈ stoOps o, op.sh.W < 2 ^ 24
  /-- and a depth of at most 63 -/
  stoDeep : ∀ op ∈ stoOps o, 2 ^ op.sh.a + 2 ^ op.sh.a ≤ 2 ^ 64
  /-- the run value has 32 bytes -/
  run32 : ∀ run, o.run = some run → run.size = 32
  /-- a salt has fewer than 2^11 bytes -/
  salt8 : D.base.plan.salt / 8 < 2 ^ 8

variable {lg s : ℕ} [DecidableEq (Sd1 lg s)] (D : XD) (d₁ : Sd1 lg s)
  (hD : D.base.cfg.size = 32) (sh : OnBytes.Params.IndexShape)

/-- What is owed for the walks, at the family that runs. -/
theorem walkParts_at (hok : TypedOracleCompiler.Run.PQ.ok D.base = true) {c₀ c₁ : Dig 256}
    {o : _root_.Fmt.ChainOut}
    {Fm : ℕ → _root_.Fmt.Shape → Prop} {Rt : ℕ → Dig 256 → Prop} (A : ShapeFacts D o)
    (readOwn : ∀ run, o.run = some run → ∀ op ∈ ownOps o,
      ReadAs (hOfG oBits) D.base.cfg run op)
    (readSto : ∀ op ∈ stoOps o, ReadAs (hOfG oBits) D.base.cfg D.base.cfg op)
    (salts : ∀ op ∈ opsOf 1 o, ∀ sl ∈ op.out.salts, sl.size = D.base.plan.salt)
    (colSto : ∀ op ∈ stoOps o, ∀ c ∈ op.out.cols, c.length = op.sh.W)
    (forms : FormsOn Fm 0 D.ds) (roots : RtsL Rt D.C 0 D.ds (PQ.rtSL D.C D.ds o.rounds.toList))
    (formOf : ∀ op ∈ ownOps o, ∀ n f, Fm n f → f.tree = op.sh.tree → f = op.sh)
    (rootOf : ∀ op ∈ ownOps o, ∀ n f c, Fm n f → f.tree = op.sh.tree → Rt n c →
      c = bytesToDig op.out.root)
    (depthSto : ∀ op ∈ stoOps o, op.sh.a = D.a)
    (rootSto : ∀ op ∈ stoOps o, [c₀, c₁].getD (whichOf D op) default = bytesToDig op.out.root) :
    WalkParts D d₁ (EntryRunTop.famOf D hD d₁ sh) c₀ c₁ o (hOfG oBits) Fm Rt where
  size := size_hOfG oBits
  node := famOf_nodeLaw D d₁ hD sh
  leafOwn := fun run hrun op hop x sym salt hs => by
    obtain ⟨d, hd, ht⟩ := A.ownTree op hop
    have h1 : op.sh.stored = false := by
      have h := (List.mem_filter.mp hop).2
      simpa using h
    exact famOf_own D d₁ hD sh op.sh h1 (own_bounds D hok d hd op.sh ht).1
      (own_bounds D hok d hd op.sh ht).2 run (A.run32 run hrun) x sym salt hs
  leafSto := fun op hop x col salt hx hc hs =>
    famOf_stored D d₁ hD sh op.sh (List.mem_filter.mp hop).2 (A.stoTree op hop) (depthSto op hop)
      (A.stoWidth op hop) (A.stoDeep op hop) A.salt8 x col salt hx hc hs
  readOwn := readOwn
  readSto := readSto
  salts := salts
  colSto := colSto
  forms := forms
  roots := roots
  formOf := formOf
  rootOf := rootOf
  depthSto := depthSto
  rootSto := rootSto

end OnBytes.K.Left
