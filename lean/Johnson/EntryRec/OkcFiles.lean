-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/EntryRec/OkcFiles.lean: the laws of the wires (`OKC`, Johnson/TypedOracleCompiler/RecCompile/Cms.lean) at an
object with records whose Test is a whole key file, whose session is a whole proof file and whose
Link is ANY protocol on two records over two stored tables, at verifier's messages as hash blocks:
from hypotheses on numbers, on the entry file's wire record, on how a symbol is written into a
leaf's body, and on the record's code.

The compiled verifier with a record over the compiler's verifier side under OnBytes/TypedOracleCompiler/
(`TypedOracleCompiler.Compile.Batch.Cms.VC`) takes an object with records, a type of bodies, annotations of
Test and Link, and a wiring of the carrier of the typed oracles. Here:
  Test and the session are OnBytes/Maker/WholeLaws.lean's `wholeDesc`: three joined chains each,
  with the annotation local, shared, local (`Chains.ann`); their wire records are
  OnBytes/Maker/Wire.lean's `wqWhole`; Link, its marks and its wire record are letters (`LinkProtocolWithLeafCoding`,
  `wL`): so the object and the wiring can be laid at any written entry file; the wiring is
  Johnson/EntryRec/WiringOfTypedOracleCarrier.lean's `wireOf2` of the three, with one number K + 1 of blocks and the
  depth a of the stored tables.

  `WholeD.at`: a file's data with the stored table's depth laid as a.
  `Letters`: what an object with records holds beside its word length, alphabet and three protocols.
  `LinkProtocolWithLeafCoding R a`: the entry file's part but for its wire record: its protocol, its marks, and the two
    maps by which a symbol of its oracles is written into a leaf's body as a string of bits and read
    back.
  `objF`: the object. `wireF`: the wiring.
  `LinkWireOK`: what the laws ask of the entry file's wire record: its own law; its stored tables'
    depth is a and is no more than its greatest depth; a position of the first stored table lies in
    tree 0, of the second in tree 1, each at its own number.
  `okc_files`: `OKC (wireF ..) S`. Its hypotheses, each named: in neither whole file a round has
    more than K blocks (`bK`, `bP`) or more than 64 bits of work (`wK`, `wP`); `LinkWireOK` (`hL`);
    the number of slots is 2 ^ depthReq (`slots`); what is written into a body is read back (`hb`);
    the record's code is one to one and of one length (`hS`).

Limits. The data of the two whole files, the decisions, the tests on what the silent rounds send,
the entry's part, the bodies, the wire of the record and the three depths of request trees are
letters. That `LinkWireOK` is met by any wire record is not shown here. Nothing is said on a
verifier's run, on soundness, or on whether the data are those of any file. `wireF` is a wiring of
our choice: that the programs are wired so is not a statement of Lean. `okc_files` has no caller.


-/
import Johnson.EntryRec.LinkWireWithListsOfTrees
import Johnson.EntryRec.WiringOfTypedOracleCarrier
import OnBytes.Maker.WireLaws

set_option autoImplicit false

namespace OnBytes.RunA

open _root_.Run _root_.Run.PQ Iop Compile OnBytes.Maker OnBytes.Slice
open TypedOracleCompiler.Compile.Batch.Cms (Bodies wireOf2 okc_wireOf2 typedOracleCarrier)

/-- A file's data with the stored table's depth laid as a. -/
@[reducible] def _root_.OnBytes.Maker.WholeD.at (D : WholeD) (a : ℕ) : WholeD := { D with a := a }

/-- **What an object with records holds beside its word length, its alphabet and its three
protocols.** -/
structure Letters (I X RI Seed Ans : Type) (a : ℕ) (QT : InteractiveOracleProof (Seed × Ans) (oneExternalString (2 ^ a) SgX))
    (QL : InteractiveOracleProof ((Seed × Ans) × (Seed × Ans)) (twoExternalStrings (2 ^ a) SgX))
    (QB : BatchInteractiveOracleProof (X × (Seed × Ans)) (oneExternalString (2 ^ a) SgX)) where
  enc : I → RI → Fin (2 ^ a) → SgX
  ans : I → RI → Seed → Ans
  coll : (Fin (2 ^ a) → SgX) → Seed → Prop
  dcd : (Fin (2 ^ a) → SgX) → Seed × Ans → Option I
  N : ℕ
  hT : Honest QT (I × RI × Seed)
  hL : Honest QL (I × (RI × Seed) × (RI × Seed))
  hB : BatchHonestProver QB (I × RI × Seed)
  early : X → X
  late : Option ℕ

@[reducible] def Letters.rest {I X RI Seed Ans : Type} {a : ℕ}
    {QT : InteractiveOracleProof (Seed × Ans) (oneExternalString (2 ^ a) SgX)}
    {QL : InteractiveOracleProof ((Seed × Ans) × (Seed × Ans)) (twoExternalStrings (2 ^ a) SgX)}
    {QB : BatchInteractiveOracleProof (X × (Seed × Ans)) (oneExternalString (2 ^ a) SgX)}
    (Z : Letters I X RI Seed Ans a QT QL QB) : RestR I X RI Seed Ans a QL :=
  ⟨Z.enc, Z.ans, Z.coll, Z.dcd, QT, Z.N, QB, Z.hT, Z.hL, Z.hB, Z.early, Z.late⟩

/-- **The entry file's part of three files**, but for its wire record: its protocol, on two records,
over two encoded indices; its marks; how a symbol of its oracles is written into a leaf's body as a
string of bits, and read back. -/
structure LinkProtocolWithLeafCoding (R : Type) (a : ℕ) where
  QL : InteractiveOracleProof (R × R) (twoExternalStrings (2 ^ a) SgX)
  aL : RoundSplits QL.shape
  embL : (p : OPos QL.shape) → OSym QL.shape p → List Bool
  prjL : (p : OPos QL.shape) → List Bool → Option (OSym QL.shape p)

section
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed]
  (f : _root_.Fmt.Fld) (K a : ℕ) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Seed × Ans → TFk → TJk → T3k → Bool)
  (runK : Seed × Ans → View → View → View → Bool)
  (silP : X × (Seed × Ans) → TFp → TJp → T3p → Bool)
  (runP : X × (Seed × Ans) → View → View → View → Bool)
  (eL : LinkProtocolWithLeafCoding (Seed × Ans) a)
  (Z : Letters I X RI Seed Ans a (wholeDesc (ckP f) (DK.at a) tFk tJk t3k silK runK).proto eL.QL
    (wholeDesc (ckP f) (DP.at a) tFp tJp t3p silP runP).batch)

/-- **The object with records of three files.** The entry file's protocol is a letter. -/
@[reducible] def objF : HolographicProtocol I X := LrG Z.rest

variable (wL : TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1)
    (⟨eL.QL, eL.aL⟩ : BatchInteractiveOracleProof ((Seed × Ans) × (Seed × Ans)) (twoExternalStrings (2 ^ a) SgX)))

/-- **Its wiring**, over wire records with lists of trees. Test's annotation is the key file's:
local, shared, local; Link's marks and its wire record are letters. -/
noncomputable def wireF (Bd : Type) (depthReq depthReqT depthReqL : ℕ)
    (b : Bodies (objF f a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z) Bd) :
    TypedOracleCompiler.Iop.QueryLayout 256
      (typedOracleCarrier (objF f a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z) Bd
        (chainsOf (ckP f) (DK.at a) tFk tJk t3k).ann eL.aL) :=
  wireOf2 (K + 1) (wqWhole (ckP f) K (chalP f K) (DK.at a) tFk tJk t3k silK runK) wL
    (wqWhole (ckP f) K (chalP f K) (DP.at a) tFp tJp t3p silP runP) a depthReq depthReqT depthReqL b

/-- **What the laws of the wires ask of the entry file's wire record.** -/
structure LinkWireOK : Prop where
  okg : wL.OKG
  depth : wL.ext.depth = a
  deep : a ≤ wL.maxDepth
  first : ∀ p, wL.ext.which (.inl p) = 0 ∧ wL.ext.leaf (.inl p) = p.val
  second : ∀ p, wL.ext.which (.inr p) = 1 ∧ wL.ext.leaf (.inr p) = p.val

/-- **The laws of the wires at the three files**, from numbers, the law of the entry file's wire
record, the bodies' law and the laws of the record's code. -/
theorem okc_files (Bd : Type) (depthReq depthReqT depthReqL : ℕ)
    (b : Bodies (objF f a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z) Bd)
    (S : TypedOracleCompiler.Compile.Batch.Cms.OutOfDomainSampleQueryLayout 256 (K + 1)
      (objF f a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z) Bd
      (chainsOf (ckP f) (DK.at a) tFk tJk t3k).ann eL.aL)
    (bK : ∀ d ∈ DK.ds₁ ++ (DK.ds₂ ++ DK.ds₃), (bsRound f d.entry d.kind).b ≤ K)
    (wK : ∀ d ∈ DK.ds₁ ++ (DK.ds₂ ++ DK.ds₃), d.entry.work ≤ 64)
    (hL : LinkWireOK K a eL wL)
    (bP : ∀ d ∈ DP.ds₁ ++ (DP.ds₂ ++ DP.ds₃), (bsRound f d.entry d.kind).b ≤ K)
    (wP : ∀ d ∈ DP.ds₁ ++ (DP.ds₂ ++ DP.ds₃), d.entry.work ≤ 64)
    (slots : Z.N = 2 ^ depthReq) (hb : b.OK) (hS : S.OK) :
    TypedOracleCompiler.Compile.Batch.Cms.OKC
      (wireF f K a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd depthReq
        depthReqT depthReqL b) S :=
  okc_wireOf2 S
    (wqWhole_okg_ckP f K (DK.at a) tFk tJk t3k silK runK bK wK) hL.okg
    (wqWhole_okg_ckP f K (DP.at a) tFp tJp t3p silP runP bP wP)
    (le_refl _) slots ⟨rfl, hL.depth, rfl⟩ (le_max_left _ _) hL.deep (le_max_left _ _)
    (fun _ => ⟨rfl, rfl⟩) (fun _ => ⟨rfl, rfl⟩) ⟨hL.first, hL.second⟩ hb hS

end

end OnBytes.RunA
