-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/KeyAtBits.lean: what the key file's encoding `mKey` reads out of the oracle made from
Lean's BLAKE2b (`oBits`, Run/OracleBits.lean), said at the format's own oracle `Fmt.oracle`. It is
the key file's encoding alone: the entry file's and the proof file's chain queries go to `back`; no
one encoding of all three files' queries is given.

OnBytes/K/Arm/KeyCoding.lean has these laws for every g, at the oracle on byte strings made of g
(`oB (g ())`). At g := `oBits` that oracle is the format's own at the string of every call whose
half is 0 or 1 (`Run.ph_oStr`, Run/ParserHashProofs.lean). The conditions `QKey` and `QgKey` ask
that the calls pass `inDom` (OnBytes/K/Arm/KeyCut.lean), whose first clause is that. For proofs
only; the program does not import this file.

Main names.
 `inDom_half`, `oB_call` a call that passes `inDom` has the half 0 or 1; there the two oracles
                agree.
 `speaks_key_bits` `SpeaksQ (readBlocks (mKey C H back) oBits) .test C.P.key Fmt.oracle (QKey C)
                (QgKey C)`.
 `key_bits_rowEnd₁`, `key_bits_rowShE₂`, `key_bits_rowEnd₃`, `key_bits_gAt`, `key_bits_s0`,
                `key_bits_s4`, `key_bits_s3` the seven laws of a file's three chains there, at O :=
                `Fmt.oracle`.
 `key_bits_rleaf`, `key_bits_rnode` a leaf and a vertex of the request tree.

Not claimed. `KeyLaws` at any cut. That data fit any stretch or that any query for which the page
has a call meets `QKey` or `QgKey`. The leaves and vertices of the trees over oracles and over
stored tables are not spoken of here; those of the request tree are. One fixed function stands here,
Lean's BLAKE2b, in the place of a random function. Nothing on soundness.

The page's data hold three digests of parameter bytes. The laws on the three first queries ask that
each is the hash of its parameter bytes under the hash that the function that is read gives. A cut
laid so is chosen after the function: its encoding serves a tie at one fixed function, and it is not
fixed before a function is drawn, as a bound over a drawn function asks. Of the configuration's
digest the laws here ask the length alone.

`QKey C q` holds of every q for which the page has no call at any block: a query of the format f2
whose head holds an instance, a round outside the three chains, a first head at another round. So "q
meets `QKey`" does not say that `mKey` writes q as the format's string; it says so only together
with a call.

At a cut whose two tests say no, `QKey` and `QgKey` fail at every query for which the page has a
call: then `speaks_key_bits` and the seven laws say nothing, whether or not `KeyLaws` holds there.
So the laws are worth what the tests let through. Where the premises `FitsEndQ` and `FitsShEQ`
cannot hold together with `KeyLaws.fb`: the head of OnBytes/K/Arm/KeyCoding.lean.

Terms: lean/GLOSSARY.md.


-/
import OnBytes.K.Arm.KeyCoding
import Run.ParserHashProofs

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

/-- A call in the domain has the half 0 or 1. -/
theorem inDom_half (c : Fmt.OQ) (h : inDom c = true) : c.half = 0 ∨ c.half = 1 := by
  unfold inDom at h
  rw [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h
  exact h.1

/-- **At the string of a call in the domain the oracle on byte strings made of `oBits` is the
format's own.** -/
theorem oB_call (c : Fmt.OQ) (h : inDom c = true) :
    oB (oBits ()) (strOf c) = Fmt.oracle (strOf c) :=
  ph_oStr c.half c.number c.tree c.index c.start c.bytes (inDom_half c h)

section
variable (C : KeyCut L (K + 1)) (H : KeyLaws C) (back : StrCode (AllPts 256 (K + 1) L))

/-- **What is read out of `oBits` through the encoding speaks by the key file's data, at the
format's own oracle.** -/
theorem speaks_key_bits :
    SpeaksQ (readBlocks (mKey C H back) oBits) .test C.P.key Fmt.oracle (QKey C) (QgKey C) where
  blk q k c hQ hc := by
    rw [← oB_call c (hQ k.castSucc c hc).2.2]
    exact (speaks_key C H back oBits).blk q k c hQ hc
  tail q c hQ hc := by
    rw [← oB_call c (hQ (Fin.last (K + 1)) c hc).2.2]
    exact (speaks_key C H back oBits).tail q c hQ hc
  slot q c hQ hc := by
    rw [← oB_call c (hQ c hc).2]
    exact (speaks_key C H back oBits).slot q c hQ hc

/-- **The first chain's rounds**, from the typed round i on. -/
theorem key_bits_rowEnd₁ (Ck : CK) (ds : List RD)
    (embP : PlainPart (uL Ck ds) (allLo (SL Ck ds)) → PBt L .test) (i : ℕ)
    (hf : FitsEndQ C.P.key (QKey C) Ck ds embP i) (h1 : 1 ≤ i)
    (h2 : i + ds.length ≤ C.P.key.n₁ + 1) :
    RowEnd (fun _ => L) Ck K (readBlocks (mKey C H back) oBits) .test Fmt.oracle C.P.key.lab₁ ds
      embP i i :=
  rowEndQ₁ Fmt.size_oracle (speaks_key_bits C H back) Ck ds embP i hf h1 h2

/-- **The third chain's rounds**, from the typed round J3 + n on. -/
theorem key_bits_rowEnd₃ (Ck : CK) (ds : List RD)
    (embP : PlainPart (uL Ck ds) (allLo (SL Ck ds)) → PBt L .test) (n : ℕ)
    (hf : FitsEndQ C.P.key (QKey C) Ck ds embP (C.P.key.J3 + n)) (h1 : 1 ≤ n)
    (h2 : n + ds.length ≤ C.P.key.n₃ + 1) :
    RowEnd (fun _ => L) Ck K (readBlocks (mKey C H back) oBits) .test Fmt.oracle C.P.key.lab₃ ds
      embP (C.P.key.J3 + n) n :=
  rowEndQ₃ Fmt.size_oracle (speaks_key_bits C H back) Ck ds embP n hf h1 h2

/-- **The shared chain's rounds**, from the typed round J + n on, to its last. -/
theorem key_bits_rowShE₂ (Ck : CK) (ds : List RD)
    (embP : PlainPart (uL Ck ds) (annShE Ck ds) → PBt L .test) (n : ℕ)
    (hf : FitsShEQ C.P.key (QKey C) Ck ds embP (C.P.key.J + n)) (h1 : 1 ≤ n)
    (h2 : n + ds.length = C.P.key.n₂ + 1) :
    RowShE (fun _ => L) Ck K (readBlocks (mKey C H back) oBits) .test Fmt.oracle C.P.key.lab₂ ds
      embP (C.P.key.J + n) n :=
  rowShEQ₂ Fmt.size_oracle (speaks_key_bits C H back) Ck ds embP n hf h1 h2

/-- **The call in which the first chain is sealed.** -/
theorem key_bits_gAt (e : PBt L .test)
    (hQ : ∀ ρ : Bits, ρ.length = 256 → QgKey C ⟨C.P.key.J, ρ, [], e⟩) :
    GAt (fun _ => L) K (readBlocks (mKey C H back) oBits) .test Fmt.oracle C.P.key.lab₁ e
      C.P.key.J C.P.key.J :=
  (speaks_key_bits C H back).gAt Fmt.size_oracle e hQ

variable {Sp : Fmt.SpecX} {o : Fmt.ChainOut} {st rnd run : ByteArray}

/-- **The first chain's first query.** -/
theorem key_bits_s0 (Hd : HeadIs (Fmt.HO Fmt.oracle) Sp o C.P.key.lab₁ st rnd)
    (hr : o.run = some run) (hp : C.P.key.pd₁ = pdOf (Fmt.HO Fmt.oracle) Sp)
    (cms : List (Dig 256)) (x : Option X) (rt : List (Dig 256)) (pl : PBt L .test)
    (hq : QKey C ⟨0, .f1 cms x (bytesToBits run), rt, pl⟩) (hst : C.P.key.stm₁ cms x pl = st) :
    (readBlocks (mKey C H back) oBits (OracleName.fb .test)
      (⟨0, .f1 cms x (bytesToBits run), rt, pl⟩ : FbIn 256 L .test) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o.rho0 :=
  s0Q_of Fmt.size_oracle (speaks_key_bits C H back) Hd hr hp cms x rt pl hq hst

/-- **The shared chain's first query.** -/
theorem key_bits_s4 (Hd : HeadIs (Fmt.HO Fmt.oracle) Sp o C.P.key.lab₂ st rnd)
    (hr : o.run = some run) (hp : C.P.key.pd₂ = pdOf (Fmt.HO Fmt.oracle) Sp)
    (cms : List (Dig 256)) (rtreq : Bits) (rt : List (Dig 256)) (pl : PBt L .test)
    (hq : QKey C ⟨C.P.key.J, .f4 cms rtreq, rt, pl⟩) (hst : C.P.key.stm₂ cms rtreq pl = st)
    (hrun : C.P.key.run₂ pl = bytesToBits run) :
    (readBlocks (mKey C H back) oBits (OracleName.fb .test)
      (⟨C.P.key.J, .f4 cms rtreq, rt, pl⟩ : FbIn 256 L .test) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o.rho0 :=
  s4Q_of Fmt.size_oracle (speaks_key_bits C H back) Hd hr hp cms rtreq rt pl hq hst hrun

/-- **The third chain's first query.** ρ0: the shared chain's seal; c: the first chain's. -/
theorem key_bits_s3 (Hd : HeadIs (Fmt.HO Fmt.oracle) Sp o C.P.key.lab₃ st rnd)
    (hr : o.run = some run) (hp : C.P.key.pd₃ = pdOf (Fmt.HO Fmt.oracle) Sp) (ρ0 c : Bits)
    (rt : List (Dig 256)) (pl : PBt L .test) (hq : QKey C ⟨C.P.key.J3, .f3 ρ0 c, rt, pl⟩)
    (hst : C.P.key.stm₃ ρ0 c pl = st) (hrun : C.P.key.run₃ pl = bytesToBits run) :
    (readBlocks (mKey C H back) oBits (OracleName.fb .test)
      (⟨C.P.key.J3, .f3 ρ0 c, rt, pl⟩ : FbIn 256 L .test) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o.rho0 :=
  s3Q_of Fmt.size_oracle (speaks_key_bits C H back) Hd hr hp ρ0 c rt pl hq hst hrun

end

section
variable (C : KeyCut L K) (H : KeyLaws C) (back : StrCode (AllPts 256 K L))

/-- A leaf of the request tree. -/
theorem key_bits_rleaf (q : Bits) (c : Fmt.OQ) (hc : rleafCall C.P.cfg C.P.sR q = some c)
    (hd : inDom c = true) :
    (readBlocks (mKey C H back) oBits .rleaf q : Dig 256) = bytesToDig (Fmt.oracle (strOf c)) := by
  rw [← oB_call c hd]
  exact key_rleaf C H back oBits q c hc hd

/-- A vertex of the request tree. -/
theorem key_bits_rnode (q : Bits × Bits) (c : Fmt.OQ) (hf : fitTree q = true)
    (hc : rnodeCall C.P.cfg q = some c) (hd : inDom c = true) :
    (readBlocks (mKey C H back) oBits .rnode q : Dig 256) = bytesToDig (Fmt.oracle (strOf c)) := by
  rw [← oB_call c hd]
  exact key_rnode C H back oBits q c hf hc hd

end

end OnBytes.K.Arm
