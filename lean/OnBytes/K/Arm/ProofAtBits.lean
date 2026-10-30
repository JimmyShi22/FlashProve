-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/ProofAtBits.lean: what the proof file's encoding `mProof` reads out of the oracle made
from Lean's BLAKE2b (`oBits`, Run/OracleBits.lean), said at the format's own oracle `Fmt.oracle`. It
is the proof file's encoding alone: the entry file's and the key file's chain queries go to `back`,
but where the page's field `seeds` writes; no one encoding of all three files' queries is given.

OnBytes/K/Arm/ProofCoding.lean has these laws for every g, at the oracle on byte strings made of g
(`oB (g ())`). At g := `oBits` that oracle is the format's own at the string of every call whose
half is 0 or 1 (`Run.ph_oStr`, Run/ParserHashProofs.lean). The conditions `QProof` and `QgProof` ask
that the calls pass `inDom` (OnBytes/K/Arm/KeyCut.lean), whose first clause is that. For proofs
only; the program does not import this file.

Main names.
 `speaks_proof_bits` `SpeaksQ (readBlocks (mProof C H back) oBits) .onl C.P.proof Fmt.oracle (QProof
                C) (QgProof C)`.
 `proof_bits_rowEnd₁`, `proof_bits_rowShE₂`, `proof_bits_rowEnd₃`, `proof_bits_gAt`,
                `proof_bits_s0`, `proof_bits_s4`, `proof_bits_s3` the seven laws of a file's three
                chains there, at O := `Fmt.oracle`.
 `proof_bits_rleaf`, `proof_bits_rnode` a leaf and a vertex of the request tree.

Not claimed. `ProofLaws` at any cut. That data fit any stretch or that any query for which the page
has a call meets `QProof` or `QgProof`. The leaves and vertices of the trees over oracles and over
stored tables are not spoken of here; those of the request tree are. One fixed function stands here,
Lean's BLAKE2b, in the place of a random function. Nothing on soundness.

Where the page's first statement holds a request through the format's item, which is made of digests
of the request, `ProofLaws` cannot hold at a test of fitness that lets the first query of every
request through: there are more requests than items, so two such queries would have one call.
Nothing here shows that it holds at any test; what this cause leaves open is a test that lets
through a set of instances on which the item is one to one. That it is so on a given set is a
hypothesis on the hash that makes the digests. The set stands in the encoding. Whoever lays it has
to name it without knowledge of the hash function and before any run; nothing here enforces that.
For a request outside the set nothing is tied here.

The page's data hold three digests of parameter bytes. The laws on the three first queries ask that
each is the hash of its parameter bytes under the hash that the function that is read gives. A cut
laid so is chosen after the function: its encoding serves a tie at one fixed function, and it is not
fixed before a function is drawn, as a bound over a drawn function asks. Of the configuration's
digest the laws here ask the length alone.

`QProof C q` holds of every q for which the page has no call at any block: a query of the format f2
whose head holds an instance, a round outside the three chains, a first head at another round. So "q
meets `QProof`" does not say that `mProof` writes q as the format's string; it says so only together
with a call.

At a cut whose two tests say no, `QProof` and `QgProof` fail at every query for which the page has a
call: then `speaks_proof_bits` and the seven laws say nothing, whether or not `ProofLaws` holds
there. So the laws are worth what the tests let through. Where the premises `FitsEndQ` and
`FitsShEQ` cannot hold together with `ProofLaws.fb`: the head of OnBytes/K/Arm/ProofCoding.lean.

At a chain query of the format f2 whose head holds an instance the page has no call, so no law here
speaks of it. Where the compiled verifier is handed an instance, its query of the round that the
interface's field `late` names holds it (the head of OnBytes/TypedOracleCompiler/Compile/Batch/LateX.lean); the
shared chain's queries hold none. So the row laws reach a proof file's run only where that round is
none of the written rounds of the first and the third chain. That is asked nowhere here; the tie
asks it itself (`ReadL.late₁`, `ReadL.late₃`).

Terms: lean/GLOSSARY.md.


-/
import OnBytes.K.Arm.ProofCoding
import OnBytes.K.Arm.KeyAtBits

set_option autoImplicit false

namespace OnBytes.K.Arm
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run Rom
open OnBytes.Maker.Page
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (CK)
open TypedOracleCompiler.Run.PQ TypedOracleCompiler.Run.Twin TypedOracleCompiler.Run.Thin
open _root_.Run.Twin (allLo)

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

section
variable (C : ProofCut L (K + 1)) (H : ProofLaws C) (back : StrCode (AllPts 256 (K + 1) L))

/-- **What is read out of `oBits` through the encoding speaks by the proof file's data, at the
format's own oracle.** -/
theorem speaks_proof_bits :
    SpeaksQ (readBlocks (mProof C H back) oBits) .onl C.P.proof Fmt.oracle (QProof C) (QgProof C)
      where
  blk q k c hQ hc := by
    rw [← oB_call c (hQ k.castSucc c hc).2]
    exact (speaks_proof C H back oBits).blk q k c hQ hc
  tail q c hQ hc := by
    rw [← oB_call c (hQ (Fin.last (K + 1)) c hc).2]
    exact (speaks_proof C H back oBits).tail q c hQ hc
  slot q c hQ hc := by
    rw [← oB_call c (hQ c hc).2]
    exact (speaks_proof C H back oBits).slot q c hQ hc

/-- **The first chain's rounds**, from the typed round i on. -/
theorem proof_bits_rowEnd₁ (Ck : CK) (ds : List RD)
    (embP : PlainPart (uL Ck ds) (allLo (SL Ck ds)) → PBt L .onl) (i : ℕ)
    (hf : FitsEndQ C.P.proof (QProof C) Ck ds embP i) (h1 : 1 ≤ i)
    (h2 : i + ds.length ≤ C.P.proof.n₁ + 1) :
    RowEnd (fun _ => L) Ck K (readBlocks (mProof C H back) oBits) .onl Fmt.oracle C.P.proof.lab₁ ds
      embP i i :=
  rowEndQ₁ Fmt.size_oracle (speaks_proof_bits C H back) Ck ds embP i hf h1 h2

/-- **The third chain's rounds**, from the typed round J3 + n on. -/
theorem proof_bits_rowEnd₃ (Ck : CK) (ds : List RD)
    (embP : PlainPart (uL Ck ds) (allLo (SL Ck ds)) → PBt L .onl) (n : ℕ)
    (hf : FitsEndQ C.P.proof (QProof C) Ck ds embP (C.P.proof.J3 + n)) (h1 : 1 ≤ n)
    (h2 : n + ds.length ≤ C.P.proof.n₃ + 1) :
    RowEnd (fun _ => L) Ck K (readBlocks (mProof C H back) oBits) .onl Fmt.oracle C.P.proof.lab₃ ds
      embP (C.P.proof.J3 + n) n :=
  rowEndQ₃ Fmt.size_oracle (speaks_proof_bits C H back) Ck ds embP n hf h1 h2

/-- **The shared chain's rounds**, from the typed round J + n on, to its last. -/
theorem proof_bits_rowShE₂ (Ck : CK) (ds : List RD)
    (embP : PlainPart (uL Ck ds) (annShE Ck ds) → PBt L .onl) (n : ℕ)
    (hf : FitsShEQ C.P.proof (QProof C) Ck ds embP (C.P.proof.J + n)) (h1 : 1 ≤ n)
    (h2 : n + ds.length = C.P.proof.n₂ + 1) :
    RowShE (fun _ => L) Ck K (readBlocks (mProof C H back) oBits) .onl Fmt.oracle C.P.proof.lab₂ ds
      embP (C.P.proof.J + n) n :=
  rowShEQ₂ Fmt.size_oracle (speaks_proof_bits C H back) Ck ds embP n hf h1 h2

/-- **The call in which the first chain is sealed.** -/
theorem proof_bits_gAt (e : PBt L .onl)
    (hQ : ∀ ρ : Bits, ρ.length = 256 → QgProof C ⟨C.P.proof.J, ρ, [], e⟩) :
    GAt (fun _ => L) K (readBlocks (mProof C H back) oBits) .onl Fmt.oracle C.P.proof.lab₁ e
      C.P.proof.J C.P.proof.J :=
  (speaks_proof_bits C H back).gAt Fmt.size_oracle e hQ

variable {Sp : Fmt.SpecX} {o : Fmt.ChainOut} {st rnd run : ByteArray}

/-- **The first chain's first query.** -/
theorem proof_bits_s0 (Hd : HeadIs (Fmt.HO Fmt.oracle) Sp o C.P.proof.lab₁ st rnd)
    (hr : o.run = some run) (hp : C.P.proof.pd₁ = pdOf (Fmt.HO Fmt.oracle) Sp)
    (cms : List (Dig 256)) (x : Option X) (rt : List (Dig 256)) (pl : PBt L .onl)
    (hq : QProof C ⟨0, .f1 cms x (bytesToBits run), rt, pl⟩) (hst : C.P.proof.stm₁ cms x pl = st) :
    (readBlocks (mProof C H back) oBits (OracleName.fb .onl)
      (⟨0, .f1 cms x (bytesToBits run), rt, pl⟩ : FbIn 256 L .onl) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o.rho0 :=
  s0Q_of Fmt.size_oracle (speaks_proof_bits C H back) Hd hr hp cms x rt pl hq hst

/-- **The shared chain's first query.** -/
theorem proof_bits_s4 (Hd : HeadIs (Fmt.HO Fmt.oracle) Sp o C.P.proof.lab₂ st rnd)
    (hr : o.run = some run) (hp : C.P.proof.pd₂ = pdOf (Fmt.HO Fmt.oracle) Sp)
    (cms : List (Dig 256)) (rtreq : Bits) (rt : List (Dig 256)) (pl : PBt L .onl)
    (hq : QProof C ⟨C.P.proof.J, .f4 cms rtreq, rt, pl⟩) (hst : C.P.proof.stm₂ cms rtreq pl = st)
    (hrun : C.P.proof.run₂ pl = bytesToBits run) :
    (readBlocks (mProof C H back) oBits (OracleName.fb .onl)
      (⟨C.P.proof.J, .f4 cms rtreq, rt, pl⟩ : FbIn 256 L .onl) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o.rho0 :=
  s4Q_of Fmt.size_oracle (speaks_proof_bits C H back) Hd hr hp cms rtreq rt pl hq hst hrun

/-- **The third chain's first query.** ρ0: the shared chain's seal; c: the first chain's. -/
theorem proof_bits_s3 (Hd : HeadIs (Fmt.HO Fmt.oracle) Sp o C.P.proof.lab₃ st rnd)
    (hr : o.run = some run) (hp : C.P.proof.pd₃ = pdOf (Fmt.HO Fmt.oracle) Sp) (ρ0 c : Bits)
    (rt : List (Dig 256)) (pl : PBt L .onl) (hq : QProof C ⟨C.P.proof.J3, .f3 ρ0 c, rt, pl⟩)
    (hst : C.P.proof.stm₃ ρ0 c pl = st) (hrun : C.P.proof.run₃ pl = bytesToBits run) :
    (readBlocks (mProof C H back) oBits (OracleName.fb .onl)
      (⟨C.P.proof.J3, .f3 ρ0 c, rt, pl⟩ : FbIn 256 L .onl) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o.rho0 :=
  s3Q_of Fmt.size_oracle (speaks_proof_bits C H back) Hd hr hp ρ0 c rt pl hq hst hrun

end

section
variable (C : ProofCut L K) (H : ProofLaws C) (back : StrCode (AllPts 256 K L))

/-- A leaf of the request tree. -/
theorem proof_bits_rleaf (q : Bits) (c : Fmt.OQ) (hc : rleafCall C.P.cfg C.P.sR q = some c)
    (hd : inDom c = true) :
    (readBlocks (mProof C H back) oBits .rleaf q : Dig 256) = bytesToDig (Fmt.oracle (strOf c)) :=
      by
  rw [← oB_call c hd]
  exact proof_rleaf C H back oBits q c hc hd

/-- A vertex of the request tree. -/
theorem proof_bits_rnode (q : Bits × Bits) (c : Fmt.OQ) (hf : fitTree q = true)
    (hc : rnodeCall C.P.cfg q = some c) (hd : inDom c = true) :
    (readBlocks (mProof C H back) oBits .rnode q : Dig 256) = bytesToDig (Fmt.oracle (strOf c)) :=
      by
  rw [← oB_call c hd]
  exact proof_rnode C H back oBits q c hf hc hd

end

end OnBytes.K.Arm
