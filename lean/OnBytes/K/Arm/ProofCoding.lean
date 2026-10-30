-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/ProofCoding.lean: what the proof file's encoding `mProof`
(OnBytes/K/Arm/ProofInj.lean) reads out of a hash function at the proof file's typed queries.
`mProof` is an encoding of the typed oracles into one hash function, in the sense of the soundness
theorem (`Rom.OracleCoding`, Rom/Family.lean). It is the proof file's encoding alone: the entry file's and
the key file's chain queries go to `back`, but where the page's field `seeds` writes; no one
encoding of all three files' queries is given.

`mProof` writes leaves by the page's spelling `leafX`, vertices by the library's code, the request
tree's points and the proof file's chain and slot queries that fit, where the page has a call that
passes `inDom`, by the format's calls, what the page's field `seeds` writes under the key file's
tag, and every other typed point behind an escape by a total code `back`. The field `seeds` speaks
of queries under the key file's tag alone, so `QProof` has no clause on the seeds. For proofs only;
the program does not import this file.

Main names.
 `pageProof C H back` the page of `mProof`; `mProof_page`: `mProof` is its encoding, by rfl.
 `QProof C`, `QgProof C` the chain queries, and the queries for the slot value, at which the
                encoding writes the proof file's own rows: wherever the page has a call, the query
                (with that block) fits and the call passes `inDom` (OnBytes/K/Arm/KeyCut.lean: its
                half is 0 or 1 and it lies in the domain of the format's hash).
 `speaks_proof` what is read out of g through `mProof` speaks by the proof file's data at these
                queries (`SpeaksQ`, OnBytes/Maker/Page/ChainsQ.lean), for every g.
 `proof_rowEnd₁`, `proof_rowShE₂`, `proof_rowEnd₃`, `proof_gAt`, `proof_s0`, `proof_s4`, `proof_s3`
                so seven of the fields that the tie of a file's three chains asks, its laws on g
                (`ReadL`, OnBytes/TypedOracleCompiler/Joined/K/RunsLineRead.lean), hold of what is read out of g
                through `mProof`, under the premises of OnBytes/Maker/Page/ChainsQ.lean at Q :=
                `QProof C`, Qg := `QgProof C`.
 `proof_leaf`, `proof_node`, `proof_rleaf`, `proof_rnode` what is read at a leaf, a vertex, and a
                leaf and a vertex of the request tree.
 `takesIn_proof` the page of `mProof` takes the seeds' code in, under the key file's tag (`TakesIn`,
                OnBytes/TypedOracleCompiler/Run/SeedPoints.lean), if the page's field `seeds` is that code.
 `takenCallsP_of` `TakenCallsP C` (OnBytes/K/Arm/ProofInj.lean), if the page's field `leafX` is a
                code of leaves (`Leaves`, OnBytes/TypedOracleCompiler/Run/PageG.lean) and its field `seeds` the
                seeds' code.

Not claimed. `ProofLaws` at any cut. That a total code `back` exists at any interface. That the
strings are those that the programs hash at a file. That data fit any stretch (`FitsEndQ`,
`FitsShEQ`) or that any query for which the page has a call meets `QProof` or `QgProof`. No property
of a hash function is used or claimed; nothing on soundness.

Where the page's first statement holds a request through the format's item, which is made of digests
of the request, `ProofLaws` cannot hold at a test of fitness that lets the first query of every
request through: there are more requests than items, so two such queries would have one call.
Nothing here shows that it holds at any test; what this cause leaves open is a test that lets
through a set of instances on which the item is one to one. That it is so on a given set is a
hypothesis on the hash that makes the digests. The set stands in the encoding. Whoever lays it has
to name it without knowledge of the hash function and before any run; nothing here enforces that.
For a request outside the set nothing is tied here.

The page's data hold three digests of parameter bytes. The laws on the three first queries ask that
each is the hash of its parameter bytes under the hash that the very g that is read gives. So "for
every g" is said of each law at a fixed cut; it is not said that one cut meets that premise at every
g. A cut laid so is chosen after the function: its encoding serves a tie at one fixed function, and
it is not fixed before a function is drawn, as a bound over a drawn function asks. Of the
configuration's digest the laws here ask the length alone.

`QProof C q` holds of every q for which the page has no call at any block: a query of the format f2
whose head holds an instance, a round outside the three chains, a first head at another round. So "q
meets `QProof`" does not say that `mProof` writes q as the format's string; it says so only together
with a call.

At a cut whose two tests say no, `QProof` and `QgProof` fail at every query for which the page has a
call: then `speaks_proof` and the seven laws say nothing, whether or not `ProofLaws` holds there. So
the laws are worth what the tests let through.

At a chain query of the format f2 whose head holds an instance the page has no call, so no law here
speaks of it. Where the compiled verifier is handed an instance, its query of the round that the
interface's field `late` names holds it (the head of OnBytes/TypedOracleCompiler/Compile/Batch/LateX.lean); the
shared chain's queries hold none. So the row laws reach a proof file's run only where that round is
none of the written rounds of the first and the third chain. That is asked nowhere here; the tie
asks it itself (`ReadL.late₁`, `ReadL.late₃`).

The premises `FitsEndQ` and `FitsShEQ` at `QProof C` ask that every list of as many roots as a round
has trees gives a query that fits, and that the round's message is `bytesL` of the roots and the
plain part (`RoundFitsQ.ours`, `RoundFitsQ.msg`, OnBytes/Maker/Page/ChainsQ.lean); `ProofLaws.fb`
asks that fitting queries with one call are one query. `bytesL` (OnBytes/TypedOracleCompiler/Run/PlanQSpell.lean)
writes a root only at an item for a root and drops the roots beyond the items. So where a round that
has a plain part has more trees than its message has such items, two lists that differ in a dropped
root have one call, and the premises cannot hold together: an argument from these texts, no theorem
of this library. That they can hold together elsewhere is not shown here.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.K.Arm.ProofInj
import OnBytes.K.Arm.KeyCoding
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

variable (C : ProofCut L K) (H : ProofLaws C) (back : StrCode (AllPts 256 K L))

/-- The page of `mProof`. -/
noncomputable abbrev pageProof : Page L K :=
  pageOf (cutProof C) (cutProof_one C H.taken H.cfg H.lab1 H.lab2 H.lab3 H.fb H.g H.fbg)
    (cutProof_hd C H.taken) back

/-- `mProof` is the encoding of that page. -/
theorem mProof_page : mProof C H back = implG (pageProof C H back) := rfl

variable (g : Fam (rom 256))

/-- A leaf query at which the page's spelling of leaves writes. -/
theorem proof_leaf (q : LeafIn L) (s : List Bool) (h : C.P.leafX q = some s) :
    (readBlocks (mProof C H back) g .leaf q : Dig 256) = g () s :=
  implOf_leaf (cutProof C) _ _ back g q s ((cutProof_leaf C q).trans h)

/-- A vertex query at which the library's code of vertices writes. -/
theorem proof_node (q : Bits × Bits) (s : List Bool) (h : (pNode C.P.cfg).put q = some s) :
    (readBlocks (mProof C H back) g .node q : Dig 256) = g () s :=
  implOf_node (cutProof C) _ _ back g q s ((cutProof_node C q).trans h)

/-- A leaf of the request tree. -/
theorem proof_rleaf (q : Bits) (c : Fmt.OQ) (hc : rleafCall C.P.cfg C.P.sR q = some c)
    (hd : inDom c = true) :
    (readBlocks (mProof C H back) g .rleaf q : Dig 256) = bytesToDig (oB (g ()) (strOf c)) :=
  (implOf_rleaf (cutProof C) _ _ back g q _ (cutProof_rleaf C q c hc hd)).trans
    (TieTree.bytes_dig _).symm

/-- A vertex of the request tree. -/
theorem proof_rnode (q : Bits × Bits) (c : Fmt.OQ) (hf : fitTree q = true)
    (hc : rnodeCall C.P.cfg q = some c) (hd : inDom c = true) :
    (readBlocks (mProof C H back) g .rnode q : Dig 256) = bytesToDig (oB (g ()) (strOf c)) :=
  (implOf_rnode (cutProof C) _ _ back g q _ (cutProof_rnode C q c hf hc hd)).trans
    (TieTree.bytes_dig _).symm

/-- **The page of the encoding takes the seeds' code in**, if the page's field `seeds` is that code.
-/
theorem takesIn_proof (p0 p1 : PBt L .test) (isP0 isP1 : PBt L .test → Bool) (cfgL : List (Dig 256))
    (sh : Bits) (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1)
    (rest : ByteArray)
    (hS : C.P.seeds = (SeedPoints.fbSeeds L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K).put) :
    SeedPoints.TakesIn L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K
      (pageProof C H back) :=
  fun x s h => cutProof_seeds C x s (by rw [hS]; exact h)

/-- **What is asked of the page's two spellings** (`TakenCallsP`, OnBytes/K/Arm/ProofInj.lean) holds
if they are a code of leaves and the seeds' code. -/
theorem takenCallsP_of (V : Leaves L) (hX : C.P.leafX = V.lf.put) (p0 p1 : PBt L .test)
    (isP0 isP1 : PBt L .test → Bool) (cfgL : List (Dig 256)) (sh : Bits)
    (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
    (hS : C.P.seeds = (SeedPoints.fbSeeds L .test p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K).put) :
    TakenCallsP C where
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

/-! ## What the encoding reads speaks by the proof file's data -/

variable {K : ℕ}

/-- **The chain queries at which the encoding writes the proof file's own rows**: at every block for
which the page has a call, the query with that block fits, and the call lies in the domain of the
format's hash. Nothing is asked at a block without a call: a chain's first query has a call at its
last block alone. -/
def QProof {K : ℕ} (C : ProofCut L K) (q : FbIn 256 L .onl) : Prop :=
  ∀ j c, fbCallJ C.P.proof K q j = some c → C.fitFb (q, j) = true ∧ inDom c = true

/-- The queries for the slot value at which it does: if the page has a call, the query fits and the
call lies in the domain. -/
def QgProof {K : ℕ} (C : ProofCut L K) (q : JoiningRoundQuery 256 L .onl) : Prop :=
  ∀ c, gCallJ C.P.proof q = some c → C.fitG q = true ∧ inDom c = true

/-- **What is read out of g through the encoding speaks by the proof file's data.** -/
theorem speaks_proof (C : ProofCut L (K + 1)) (H : ProofLaws C)
    (back : StrCode (AllPts 256 (K + 1) L)) (g : Fam (rom 256)) :
    SpeaksQ (readBlocks (mProof C H back) g) .onl C.P.proof (oB (g ())) (QProof C) (QgProof C) where
  blk q k c hQ hc := by
    obtain ⟨hf, hd⟩ := hQ k.castSucc c hc
    exact (implOf_fb (cutProof C) _ _ back g .onl q k _
      (cutProof_fb C (q, k.castSucc) c hf hc hd)).trans (TieTree.bytes_dig _).symm
  tail q c hQ hc := by
    obtain ⟨hf, hd⟩ := hQ (Fin.last (K + 1)) c hc
    exact (implOf_fb_last (cutProof C) _ _ back g .onl q _
      (cutProof_fb C (q, Fin.last (K + 1)) c hf hc hd)).trans (TieTree.bytes_dig _).symm
  slot q c hQ hc :=
    (implOf_g (cutProof C) _ _ back g .onl q _ (cutProof_g C q c (hQ c hc).1 hc (hQ c hc).2)).trans
      (TieTree.bytes_dig _).symm

/-! ## The seven laws of a file's three chains, at what the encoding reads -/

section Seven
variable (C : ProofCut L (K + 1)) (H : ProofLaws C) (back : StrCode (AllPts 256 (K + 1) L))
  (g : Fam (rom 256))

/-- **The first chain's rounds**, from the typed round i on. -/
theorem proof_rowEnd₁ (Ck : CK) (ds : List RD)
    (embP : PlainPart (uL Ck ds) (allLo (SL Ck ds)) → PBt L .onl) (i : ℕ)
    (hf : FitsEndQ C.P.proof (QProof C) Ck ds embP i) (h1 : 1 ≤ i)
    (h2 : i + ds.length ≤ C.P.proof.n₁ + 1) :
    RowEnd (fun _ => L) Ck K (readBlocks (mProof C H back) g) .onl (oB (g ())) C.P.proof.lab₁ ds
      embP i i :=
  rowEndQ₁ (size_oBg g) (speaks_proof C H back g) Ck ds embP i hf h1 h2

/-- **The third chain's rounds**, from the typed round J3 + n on. -/
theorem proof_rowEnd₃ (Ck : CK) (ds : List RD)
    (embP : PlainPart (uL Ck ds) (allLo (SL Ck ds)) → PBt L .onl) (n : ℕ)
    (hf : FitsEndQ C.P.proof (QProof C) Ck ds embP (C.P.proof.J3 + n)) (h1 : 1 ≤ n)
    (h2 : n + ds.length ≤ C.P.proof.n₃ + 1) :
    RowEnd (fun _ => L) Ck K (readBlocks (mProof C H back) g) .onl (oB (g ())) C.P.proof.lab₃ ds
      embP (C.P.proof.J3 + n) n :=
  rowEndQ₃ (size_oBg g) (speaks_proof C H back g) Ck ds embP n hf h1 h2

/-- **The shared chain's rounds**, from the typed round J + n on, to its last. -/
theorem proof_rowShE₂ (Ck : CK) (ds : List RD)
    (embP : PlainPart (uL Ck ds) (annShE Ck ds) → PBt L .onl) (n : ℕ)
    (hf : FitsShEQ C.P.proof (QProof C) Ck ds embP (C.P.proof.J + n)) (h1 : 1 ≤ n)
    (h2 : n + ds.length = C.P.proof.n₂ + 1) :
    RowShE (fun _ => L) Ck K (readBlocks (mProof C H back) g) .onl (oB (g ())) C.P.proof.lab₂ ds
      embP (C.P.proof.J + n) n :=
  rowShEQ₂ (size_oBg g) (speaks_proof C H back g) Ck ds embP n hf h1 h2

/-- **The call in which the first chain is sealed.** -/
theorem proof_gAt (e : PBt L .onl)
    (hQ : ∀ ρ : Bits, ρ.length = 256 → QgProof C ⟨C.P.proof.J, ρ, [], e⟩) :
    GAt (fun _ => L) K (readBlocks (mProof C H back) g) .onl (oB (g ())) C.P.proof.lab₁ e
      C.P.proof.J C.P.proof.J :=
  (speaks_proof C H back g).gAt (size_oBg g) e hQ

variable {Sp : Fmt.SpecX} {o : Fmt.ChainOut} {st rnd run : ByteArray}

/-- **The first chain's first query.** -/
theorem proof_s0 (Hd : HeadIs (Fmt.HO (oB (g ()))) Sp o C.P.proof.lab₁ st rnd)
    (hr : o.run = some run)
    (hp : C.P.proof.pd₁ = pdOf (Fmt.HO (oB (g ()))) Sp) (cms : List (Dig 256)) (x : Option X)
    (rt : List (Dig 256)) (pl : PBt L .onl)
    (hq : QProof C ⟨0, .f1 cms x (bytesToBits run), rt, pl⟩) (hst : C.P.proof.stm₁ cms x pl = st) :
    (readBlocks (mProof C H back) g (OracleName.fb .onl)
      (⟨0, .f1 cms x (bytesToBits run), rt, pl⟩ : FbIn 256 L .onl) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o.rho0 :=
  s0Q_of (size_oBg g) (speaks_proof C H back g) Hd hr hp cms x rt pl hq hst

/-- **The shared chain's first query.** -/
theorem proof_s4 (Hd : HeadIs (Fmt.HO (oB (g ()))) Sp o C.P.proof.lab₂ st rnd)
    (hr : o.run = some run)
    (hp : C.P.proof.pd₂ = pdOf (Fmt.HO (oB (g ()))) Sp) (cms : List (Dig 256)) (rtreq : Bits)
    (rt : List (Dig 256)) (pl : PBt L .onl)
    (hq : QProof C ⟨C.P.proof.J, .f4 cms rtreq, rt, pl⟩) (hst : C.P.proof.stm₂ cms rtreq pl = st)
    (hrun : C.P.proof.run₂ pl = bytesToBits run) :
    (readBlocks (mProof C H back) g (OracleName.fb .onl)
      (⟨C.P.proof.J, .f4 cms rtreq, rt, pl⟩ : FbIn 256 L .onl) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o.rho0 :=
  s4Q_of (size_oBg g) (speaks_proof C H back g) Hd hr hp cms rtreq rt pl hq hst hrun

/-- **The third chain's first query.** ρ0: the shared chain's seal; c: the first chain's. -/
theorem proof_s3 (Hd : HeadIs (Fmt.HO (oB (g ()))) Sp o C.P.proof.lab₃ st rnd)
    (hr : o.run = some run)
    (hp : C.P.proof.pd₃ = pdOf (Fmt.HO (oB (g ()))) Sp) (ρ0 c : Bits) (rt : List (Dig 256))
    (pl : PBt L .onl) (hq : QProof C ⟨C.P.proof.J3, .f3 ρ0 c, rt, pl⟩)
    (hst : C.P.proof.stm₃ ρ0 c pl = st) (hrun : C.P.proof.run₃ pl = bytesToBits run) :
    (readBlocks (mProof C H back) g (OracleName.fb .onl)
      (⟨C.P.proof.J3, .f3 ρ0 c, rt, pl⟩ : FbIn 256 L .onl) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o.rho0 :=
  s3Q_of (size_oBg g) (speaks_proof C H back g) Hd hr hp ρ0 c rt pl hq hst hrun

end Seven

end OnBytes.K.Arm
