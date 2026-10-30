-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/AskedPd.lean: the parameter digest in what the reading of an entry file returns is
the answer, at the same function, to the string of the call that hashes the parameter bytes.

`Tie.askedAt O q first ent` (OnBytes/Tie/EntryAsked.lean) is the value of the reading that asks, at
a function O in the place of the hash. What it returns of the chain has a first field `pd`, the
digest of the parameter bytes as the reader computed it.

Main names:
  `read_pd`: of one yes of the library's strict reader at the hash that O induces.
  `asked_pd`: of `askedAt`: `a.out.pd = O (Tie.digestStr q.given.bytes)`.
  `own₁_pin`: the oracle's own second table, at the string of the call that hashes the parameter
    bytes at the digest that its own first table holds, has the oracle's own value.
  `asked_pin`: at every family g with one oracle, at a ground G and the digest c that g's own first
    table holds: the digest in what the reading returns at g, as a typed digest, is the value that
    `HomeData.atR` (OnBytes/TypedOracleCompiler/Slice/EntryHome.lean) hands to the page as the parameter bytes'
    digest: the reader's parameter digest is the page's, under every oracle.

What is not claimed. Values alone. Nothing on what O is; nothing on soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.EntryAsked
import OnBytes.Tie.EntryCheckRec
import OnBytes.Tie.EntryPlaceRec
import OnBytes.Tie.TraceStrict
import OnBytes.TypedOracleCompiler.Slice.EntryRunPlay
import OnBytes.TypedOracleCompiler.Slice.ShapesOne
import OnBytes.TypedOracleCompiler.Slice.ShapesPub

set_option autoImplicit false

namespace OnBytes.K.Oracle
open OnBytes.Tie
open Rom
open TypedOracleCompiler.Slice (homeOf entryXD)
open OnBytes.Slice (s0Of)
open OnBytes.Slice.Shapes (Cfg dgOf pubS₀ pubS₁)
open OnBytes.Slice.Shapes.FileSpec (own₀ own₁)

/-- The digest that the strict reader hands out is O's answer at the string of its first call. -/
theorem read_pd (O : ByteArray → ByteArray) (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray)
    (i : ℕ) (o : Fmt.ChainOut) (j : ℕ)
    (e : Fmt.readChainX (m := Id) (Fmt.HO O) S seen b i = some (o, j)) :
    o.pd = O (digestStr S.base.params) := by
  obtain ⟨-, x, i0, hd, s, -, -, -, rfl, -⟩ := readX_stages (Fmt.HO O) S seen b i o j e
  rfl

/-- The digest in what the reading returns is O's answer at the string of the call that hashes the
parameter bytes. -/
theorem asked_pd (O : ByteArray → ByteArray) (q : Params.Link) (first : Params.TableName)
    (ent : ByteArray) (a : AskedE) (h : askedAt O q first ent = some a) :
    a.out.pd = O (digestStr q.given.bytes) := by
  unfold askedAt at h
  obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨l0, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨l1, -, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨P, hP, hrun, -, -, -⟩ := (readWithR_iff _ _ q first ent r).1 hr
  obtain ⟨y, hy, e1⟩ := Option.map_eq_some_iff.1 hrun
  obtain ⟨-, ⟨r0, -, eP⟩, -⟩ := entryPlaceR_spec_any hP
  have e2 := (readInAt_read O P.spec ent P.byte Session.start y.2 y.1 hy).1
  have e3 := read_pd O P.spec _ ent P.byte _ _ e2
  rw [e1, eP] at e3
  exact e3

/-- The oracle's own second table has the oracle's own value at the string of the call that hashes
the parameter bytes. prm: the parameter bytes as a function of the configuration's digest. -/
theorem own₁_pin (prm : ByteArray → ByteArray) (cfg : Cfg) (g : Fam (rom 256)) :
    own₁ (pubS₀ cfg) (pubS₁ [prm] cfg) g (s0Of (prm (dgOf cfg (own₀ (pubS₀ cfg) g)))) =
      g () (s0Of (prm (dgOf cfg (own₀ (pubS₀ cfg) g)))) := by
  have hm : s0Of (prm (dgOf cfg (own₀ (pubS₀ cfg) g))) ∈
      pubS₁ [prm] cfg (own₀ (pubS₀ cfg) g) := by
    unfold pubS₁
    simp
  unfold own₁ OnBytes.Slice.Shapes.cutT
  rw [if_pos hm]
  rfl

/-- **The reader's parameter digest is the page's, under every oracle.** -/
theorem asked_pin (G : EntryGround)
    (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)
    (eM : ℕ) (cfg : Cfg) (g : Fam (rom 256)) (first : Params.TableName) (ent : ByteArray)
    (a : AskedE)
    (h : askedAt (Run.oB (g ())) (linkAtCfg G.q (dgOf cfg (own₀ (pubS₀ cfg) g))) first ent =
      some a) :
    Run.bytesToDig a.out.pd =
      own₁ (pubS₀ cfg) (pubS₁ [(homeOf G hok eM).prm] cfg) g
        (s0Of ((homeOf G hok eM).prm (dgOf cfg (own₀ (pubS₀ cfg) g)))) := by
  rw [own₁_pin, asked_pd _ _ _ _ _ h]
  exact Run.TieTree.bytes_dig _

end OnBytes.K.Oracle
