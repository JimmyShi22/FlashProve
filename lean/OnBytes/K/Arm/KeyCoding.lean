-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/KeyCoding.lean: what the key file's encoding `mKey` (OnBytes/K/Arm/KeyInj.lean) reads
out of a hash function at the key file's typed queries. `mKey` is an encoding of the typed oracles
into one hash function, in the sense of the soundness theorem (`Rom.OracleCoding`, Rom/Family.lean). It is
the key file's encoding alone: the entry file's and the proof file's chain queries go to `back`; no
one encoding of all three files' queries is given.

The `codeJ` of the page of OnBytes/Maker/Page/Frame.lean is a function of the typed query and no
encoding: it is not one to one. `cutKey` (OnBytes/K/Arm/KeyCut.lean) is made after it, for the key
file, cut down to the queries that fit. Under `KeyLaws` it is one to one, and `mKey` is the encoding
that `implOf` (OnBytes/TypedOracleCompiler/Run/PageOf.lean) makes of it. `mKey` writes leaves by the page's spelling
`leafX`, vertices by the library's code, the request tree's points and the key file's chain and slot
queries that fit, where the page has a call that passes `inDom` and the field `seeds` is silent, by
the format's calls, what the page's field `seeds` writes under the key file's tag, and every other
typed point behind an escape by a total code `back`. For proofs only; the program does not import
this file.

Main names.
 `pageKey C H back`   the page of `mKey`; `mKey_page`: `mKey` is its encoding, by rfl.
 `QKey C`, `QgKey C` the chain queries, and the queries for the slot value, at which the encoding
                writes the key file's own rows: wherever the page has a call, the query (with that
                block) fits, the call passes `inDom` (OnBytes/K/Arm/KeyCut.lean: its half is 0 or 1
                and it lies in the domain of the format's hash), and, for a chain query, the seeds'
                spelling is silent at that block.
 `speaks_key` what is read out of g through `mKey` speaks by the key file's data at these queries
                (`SpeaksQ`, OnBytes/Maker/Page/ChainsQ.lean), for every g.
 `key_rowEnd₁`, `key_rowShE₂`, `key_rowEnd₃`, `key_gAt`, `key_s0`, `key_s4`, `key_s3` so seven of
                the fields that the tie of a file's three chains asks, its laws on g (`ReadL`,
                OnBytes/TypedOracleCompiler/Joined/K/RunsLineRead.lean), hold of what is read out of g through
                `mKey`, at the oracle on byte strings made of g, under the premises of
                OnBytes/Maker/Page/ChainsQ.lean at Q := `QKey C`, Qg := `QgKey C`.
 `key_leaf`, `key_node`, `key_rleaf`, `key_rnode`   what is read at a leaf, a vertex, and a leaf and
                a vertex of the request tree.
 `takesIn_key`  the page of `mKey` takes the seeds' code in (`TakesIn`,
                OnBytes/TypedOracleCompiler/Run/SeedPoints.lean), if the page's field `seeds` is that code.
 `takenCalls_of` `TakenCalls C` (OnBytes/K/Arm/KeyInj.lean), if the page's field `leafX` is a code
                of leaves (`Leaves`, OnBytes/TypedOracleCompiler/Run/PageG.lean) and its field `seeds` the seeds'
                code.

Not claimed. `KeyLaws` at any cut. That a total code `back` exists at any interface. That the
strings are those that the programs hash at a file. That data fit any stretch (`FitsEndQ`,
`FitsShEQ`) or that any query for which the page has a call meets `QKey` or `QgKey`. No property of
a hash function is used or claimed; nothing on soundness.

The page's data hold three digests of parameter bytes. The laws on the three first queries ask that
each is the hash of its parameter bytes under the hash that the very g that is read gives. So "for
every g" is said of each law at a fixed cut; it is not said that one cut meets that premise at every
g. A cut laid so is chosen after the function: its encoding serves a tie at one fixed function, and
it is not fixed before a function is drawn, as a bound over a drawn function asks. Of the
configuration's digest the laws here ask the length alone.

`QKey C q` holds of every q for which the page has no call at any block: a query of the format f2
whose head holds an instance, a round outside the three chains, a first head at another round. So "q
meets `QKey`" does not say that `mKey` writes q as the format's string; it says so only together
with a call.

At a cut whose two tests say no, `QKey` and `QgKey` fail at every query for which the page has a
call: then `speaks_key` and the seven laws say nothing, whether or not `KeyLaws` holds there. So the
laws are worth what the tests let through.

The premises `FitsEndQ` and `FitsShEQ` at `QKey C` ask that every list of as many roots as a round
has trees gives a query that fits, and that the round's message is `bytesL` of the roots and the
plain part (`RoundFitsQ.ours`, `RoundFitsQ.msg`, OnBytes/Maker/Page/ChainsQ.lean); `KeyLaws.fb` asks
that fitting queries with one call are one query. `bytesL` (OnBytes/TypedOracleCompiler/Run/PlanQSpell.lean) writes
a root only at an item for a root and drops the roots beyond the items. So where a round that has a
plain part has more trees than its message has such items, two lists that differ in a dropped root
have one call, and the premises cannot hold together: an argument from these texts, no theorem of
this library. That they can hold together elsewhere is not shown here.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.K.Arm.KeyInj
import OnBytes.TypedOracleCompiler.Run.SeedPoints
import OnBytes.Maker.Page.ChainsQ

set_option autoImplicit false

namespace OnBytes.K.Arm
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run Rom
open OnBytes.Maker.Page TypedOracleCompiler.Run.PageOf TypedOracleCompiler.Run.PageG
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (CK)
open TypedOracleCompiler.Run.PQ TypedOracleCompiler.Run.Twin TypedOracleCompiler.Run.Thin
open _root_.Run.Twin (allLo)

variable {I X : Type} {L : BatchProtocolWithLeafBody I X}

/-! ## The encoding -/

section
variable {K : ℕ}

variable (C : KeyCut L K) (H : KeyLaws C) (back : StrCode (AllPts 256 K L))

/-- The page of `mKey`. -/
noncomputable abbrev pageKey : Page L K :=
  pageOf (cutKey C) (cutKey_one C H.taken H.cfg H.lab1 H.lab2 H.lab3 H.fb H.g H.fbg)
    (cutKey_hd C H.taken) back

/-- `mKey` is the encoding of that page. -/
theorem mKey_page : mKey C H back = implG (pageKey C H back) := rfl

variable (g : Fam (rom 256))

/-- A leaf query at which the page's spelling of leaves writes. -/
theorem key_leaf (q : LeafIn L) (s : List Bool) (h : C.P.leafX q = some s) :
    (readBlocks (mKey C H back) g .leaf q : Dig 256) = g () s :=
  implOf_leaf (cutKey C) _ _ back g q s ((cutKey_leaf C q).trans h)

/-- A vertex query at which the library's code of vertices writes. -/
theorem key_node (q : Bits × Bits) (s : List Bool) (h : (pNode C.P.cfg).put q = some s) :
    (readBlocks (mKey C H back) g .node q : Dig 256) = g () s :=
  implOf_node (cutKey C) _ _ back g q s ((cutKey_node C q).trans h)

/-- A leaf of the request tree. -/
theorem key_rleaf (q : Bits) (c : Fmt.OQ) (hc : rleafCall C.P.cfg C.P.sR q = some c)
    (hd : inDom c = true) :
    (readBlocks (mKey C H back) g .rleaf q : Dig 256) = bytesToDig (oB (g ()) (strOf c)) :=
  (implOf_rleaf (cutKey C) _ _ back g q _ (cutKey_rleaf C q c hc hd)).trans
    (TieTree.bytes_dig _).symm

/-- A vertex of the request tree. -/
theorem key_rnode (q : Bits × Bits) (c : Fmt.OQ) (hf : fitTree q = true)
    (hc : rnodeCall C.P.cfg q = some c) (hd : inDom c = true) :
    (readBlocks (mKey C H back) g .rnode q : Dig 256) = bytesToDig (oB (g ()) (strOf c)) :=
  (implOf_rnode (cutKey C) _ _ back g q _ (cutKey_rnode C q c hf hc hd)).trans
    (TieTree.bytes_dig _).symm

/-- **The page of the encoding takes the seeds' code in**, if the page's field `seeds` is that
code. -/
theorem takesIn_key (p0 p1 : PBt L .test) (isP0 isP1 : PBt L .test → Bool) (cfgL : List (Dig 256))
    (sh : Bits) (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1)
    (rest : ByteArray)
    (hS : C.P.seeds = (SeedPoints.fbSeeds L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K).put) :
    SeedPoints.TakesIn L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K
      (pageKey C H back) :=
  fun x s h => cutKey_seeds C x s (by rw [hS]; exact h)

/-- **What is asked of the page's two spellings** (`TakenCalls`, OnBytes/K/Arm/KeyInj.lean) holds if
they are a code of leaves and the seeds' code. -/
theorem takenCalls_of (V : Leaves L) (hX : C.P.leafX = V.lf.put) (p0 p1 : PBt L .test)
    (isP0 isP1 : PBt L .test → Bool) (cfgL : List (Dig 256)) (sh : Bits)
    (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
    (hS : C.P.seeds = (SeedPoints.fbSeeds L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K).put) :
    TakenCalls C where
  leafInj q q' s h h' := by
    rw [hX] at h h'
    exact V.lf.inj h h'
  leafTag q s h := by
    rw [hX] at h
    exact V.hlf q s h
  seedInj x x' s h h' := by
    rw [hS] at h h'
    exact PCode.inj _ h h'
  seedIs x s h := by
    rw [hS] at h
    exact SeedPoints.fbSeeds_is L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K x s h

end

/-! ## What the encoding reads speaks by the key file's data -/

variable {K : ℕ}

/-- **The chain queries at which the encoding writes the key file's own rows**: at every block for
which the page has a call, the seeds' spelling is silent, the query with that block fits, and the
call lies in the domain of the format's hash. Nothing is asked at a block without a call: a chain's
first query has a call at its last block alone. -/
def QKey {K : ℕ} (C : KeyCut L K) (q : FbIn 256 L .test) : Prop :=
  ∀ j c, fbCallJ C.P.key K q j = some c →
    C.P.seeds (q, j) = none ∧ C.fitFb (q, j) = true ∧ inDom c = true

/-- The queries for the slot value at which it does: if the page has a call, the query fits and the
call lies in the domain. -/
def QgKey {K : ℕ} (C : KeyCut L K) (q : JoiningRoundQuery 256 L .test) : Prop :=
  ∀ c, gCallJ C.P.key q = some c → C.fitG q = true ∧ inDom c = true

/-- **What is read out of g through the encoding speaks by the key file's data.** -/
theorem speaks_key (C : KeyCut L (K + 1)) (H : KeyLaws C) (back : StrCode (AllPts 256 (K + 1) L))
    (g : Fam (rom 256)) :
    SpeaksQ (readBlocks (mKey C H back) g) .test C.P.key (oB (g ())) (QKey C) (QgKey C) where
  blk q k c hQ hc := by
    obtain ⟨hs, hf, hd⟩ := hQ k.castSucc c hc
    exact (implOf_fb (cutKey C) _ _ back g .test q k _
      (cutKey_fb C (q, k.castSucc) c hs hf hc hd)).trans (TieTree.bytes_dig _).symm
  tail q c hQ hc := by
    obtain ⟨hs, hf, hd⟩ := hQ (Fin.last (K + 1)) c hc
    exact (implOf_fb_last (cutKey C) _ _ back g .test q _
      (cutKey_fb C (q, Fin.last (K + 1)) c hs hf hc hd)).trans (TieTree.bytes_dig _).symm
  slot q c hQ hc :=
    (implOf_g (cutKey C) _ _ back g .test q _ (cutKey_g C q c (hQ c hc).1 hc (hQ c hc).2)).trans
      (TieTree.bytes_dig _).symm

/-! ## The seven laws of a file's three chains, at what the encoding reads -/

section Seven
variable (C : KeyCut L (K + 1)) (H : KeyLaws C) (back : StrCode (AllPts 256 (K + 1) L))
  (g : Fam (rom 256))

/-- The answers of the oracle on byte strings have 32 bytes. -/
theorem size_oBg (s : ByteArray) : (oB (g ()) s).size = 32 := size_digToBytes _

/-- **The first chain's rounds**, from the typed round i on. -/
theorem key_rowEnd₁ (Ck : CK) (ds : List RD)
    (embP : PlainPart (uL Ck ds) (allLo (SL Ck ds)) → PBt L .test) (i : ℕ)
    (hf : FitsEndQ C.P.key (QKey C) Ck ds embP i) (h1 : 1 ≤ i)
    (h2 : i + ds.length ≤ C.P.key.n₁ + 1) :
    RowEnd (fun _ => L) Ck K (readBlocks (mKey C H back) g) .test (oB (g ())) C.P.key.lab₁ ds embP
      i i :=
  rowEndQ₁ (size_oBg g) (speaks_key C H back g) Ck ds embP i hf h1 h2

/-- **The third chain's rounds**, from the typed round J3 + n on. -/
theorem key_rowEnd₃ (Ck : CK) (ds : List RD)
    (embP : PlainPart (uL Ck ds) (allLo (SL Ck ds)) → PBt L .test) (n : ℕ)
    (hf : FitsEndQ C.P.key (QKey C) Ck ds embP (C.P.key.J3 + n)) (h1 : 1 ≤ n)
    (h2 : n + ds.length ≤ C.P.key.n₃ + 1) :
    RowEnd (fun _ => L) Ck K (readBlocks (mKey C H back) g) .test (oB (g ())) C.P.key.lab₃ ds embP
      (C.P.key.J3 + n) n :=
  rowEndQ₃ (size_oBg g) (speaks_key C H back g) Ck ds embP n hf h1 h2

/-- **The shared chain's rounds**, from the typed round J + n on, to its last. -/
theorem key_rowShE₂ (Ck : CK) (ds : List RD)
    (embP : PlainPart (uL Ck ds) (annShE Ck ds) → PBt L .test) (n : ℕ)
    (hf : FitsShEQ C.P.key (QKey C) Ck ds embP (C.P.key.J + n)) (h1 : 1 ≤ n)
    (h2 : n + ds.length = C.P.key.n₂ + 1) :
    RowShE (fun _ => L) Ck K (readBlocks (mKey C H back) g) .test (oB (g ())) C.P.key.lab₂ ds embP
      (C.P.key.J + n) n :=
  rowShEQ₂ (size_oBg g) (speaks_key C H back g) Ck ds embP n hf h1 h2

/-- **The call in which the first chain is sealed.** -/
theorem key_gAt (e : PBt L .test)
    (hQ : ∀ ρ : Bits, ρ.length = 256 → QgKey C ⟨C.P.key.J, ρ, [], e⟩) :
    GAt (fun _ => L) K (readBlocks (mKey C H back) g) .test (oB (g ())) C.P.key.lab₁ e C.P.key.J
      C.P.key.J :=
  (speaks_key C H back g).gAt (size_oBg g) e hQ

variable {Sp : Fmt.SpecX} {o : Fmt.ChainOut} {st rnd run : ByteArray}

/-- **The first chain's first query.** -/
theorem key_s0 (Hd : HeadIs (Fmt.HO (oB (g ()))) Sp o C.P.key.lab₁ st rnd) (hr : o.run = some run)
    (hp : C.P.key.pd₁ = pdOf (Fmt.HO (oB (g ()))) Sp) (cms : List (Dig 256)) (x : Option X)
    (rt : List (Dig 256)) (pl : PBt L .test)
    (hq : QKey C ⟨0, .f1 cms x (bytesToBits run), rt, pl⟩) (hst : C.P.key.stm₁ cms x pl = st) :
    (readBlocks (mKey C H back) g (OracleName.fb .test)
      (⟨0, .f1 cms x (bytesToBits run), rt, pl⟩ : FbIn 256 L .test) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o.rho0 :=
  s0Q_of (size_oBg g) (speaks_key C H back g) Hd hr hp cms x rt pl hq hst

/-- **The shared chain's first query.** -/
theorem key_s4 (Hd : HeadIs (Fmt.HO (oB (g ()))) Sp o C.P.key.lab₂ st rnd) (hr : o.run = some run)
    (hp : C.P.key.pd₂ = pdOf (Fmt.HO (oB (g ()))) Sp) (cms : List (Dig 256)) (rtreq : Bits)
    (rt : List (Dig 256)) (pl : PBt L .test)
    (hq : QKey C ⟨C.P.key.J, .f4 cms rtreq, rt, pl⟩) (hst : C.P.key.stm₂ cms rtreq pl = st)
    (hrun : C.P.key.run₂ pl = bytesToBits run) :
    (readBlocks (mKey C H back) g (OracleName.fb .test)
      (⟨C.P.key.J, .f4 cms rtreq, rt, pl⟩ : FbIn 256 L .test) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o.rho0 :=
  s4Q_of (size_oBg g) (speaks_key C H back g) Hd hr hp cms rtreq rt pl hq hst hrun

/-- **The third chain's first query.** ρ0: the shared chain's seal; c: the first chain's. -/
theorem key_s3 (Hd : HeadIs (Fmt.HO (oB (g ()))) Sp o C.P.key.lab₃ st rnd) (hr : o.run = some run)
    (hp : C.P.key.pd₃ = pdOf (Fmt.HO (oB (g ()))) Sp) (ρ0 c : Bits) (rt : List (Dig 256))
    (pl : PBt L .test) (hq : QKey C ⟨C.P.key.J3, .f3 ρ0 c, rt, pl⟩)
    (hst : C.P.key.stm₃ ρ0 c pl = st) (hrun : C.P.key.run₃ pl = bytesToBits run) :
    (readBlocks (mKey C H back) g (OracleName.fb .test)
      (⟨C.P.key.J3, .f3 ρ0 c, rt, pl⟩ : FbIn 256 L .test) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o.rho0 :=
  s3Q_of (size_oBg g) (speaks_key C H back g) Hd hr hp ρ0 c rt pl hq hst hrun

end Seven

end OnBytes.K.Arm
