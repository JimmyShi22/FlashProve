-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/EntryRec/BodiesAt.lean: at the object of three files (`objF`,
Johnson/EntryRec/OkcFiles.lean), the eight maps by which a symbol is written into the body of a leaf
and read back, with a body the leaf's own string of bits.

  `bodiesF`: the eight maps (`Bodies`, Johnson/EntryRec/WiringOfTypedOracleCarrier.lean). For the prover's oracles of
    the two whole files they are OnBytes/Flat/LeafBodies.lean's `scWhole`: a symbol is written as
    what the library's code of one tree's leaves writes at its own tree. For the entry file's
    oracles they are the entry's part's own (`LinkProtocolWithLeafCoding.embL`, `prjL`). For a stored table's symbols
    the two maps are letters.
  `bodiesF_ok`: what is written is read back, if that holds of the two letters (`hE`) and of the
    entry's part's two maps (`hLb`), and no tree of the two whole files is deeper than 63 (`dK`,
    `dP`).

Limits: those of Johnson/EntryRec/OkcFiles.lean's head. That a body is the string that a program
hashes in a leaf is said for one tree of a run (not a stored table's) by
OnBytes/Flat/LeafBodies.lean's `emb1_fit` and not here. salt, the length of a file's salt in bytes,
is one letter for both whole files.


-/
import Johnson.EntryRec.OkcFiles
import OnBytes.Flat.LeafBodies
import OnBytes.Flat.WireBlocks

set_option autoImplicit false

namespace OnBytes.RunA

open _root_.Run _root_.Run.PQ Iop Compile OnBytes.Maker OnBytes.Flat
open TypedOracleCompiler.Compile.Batch.Cms (Bodies)

variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed]
  (f : _root_.Fmt.Fld) (a : ℕ) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Seed × Ans → TFk → TJk → T3k → Bool)
  (runK : Seed × Ans → View → View → View → Bool)
  (silP : X × (Seed × Ans) → TFp → TJp → T3p → Bool)
  (runP : X × (Seed × Ans) → View → View → View → Bool)
  (eL : LinkProtocolWithLeafCoding (Seed × Ans) a)
  (Z : Letters I X RI Seed Ans a (wholeDesc (ckP f) (DK.at a) tFk tJk t3k silK runK).proto eL.QL
    (wholeDesc (ckP f) (DP.at a) tFp tJp t3p silP runP).batch)
  (salt : ℕ) (embE : SgX → List Bool) (prjE : List Bool → Option SgX)

/-- **The eight maps**: a body is the leaf's own string of bits. The two of a stored table's symbol
are letters; the two of the entry file's oracles are the entry's part's own. -/
def bodiesF :
    Bodies (objF f a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z)
      (List Bool) where
  embE := embE
  prjE := prjE
  embT := SCode.emb _ (scWhole salt (ckP f) (DK.at a) tFk tJk t3k)
  prjT := SCode.prj _ (scWhole salt (ckP f) (DK.at a) tFk tJk t3k)
  embL := eL.embL
  prjL := eL.prjL
  embB := SCode.emb _ (scWhole salt (ckP f) (DP.at a) tFp tJp t3p)
  prjB := SCode.prj _ (scWhole salt (ckP f) (DP.at a) tFp tJp t3p)

/-- **What is written is read back.** -/
theorem bodiesF_ok (hE : ∀ s, prjE (embE s) = some s)
    (dK : ∀ d ∈ DK.ds₁ ++ (DK.ds₂ ++ DK.ds₃), ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (hLb : ∀ p s, eL.prjL p (eL.embL p s) = some s)
    (dP : ∀ d ∈ DP.ds₁ ++ (DP.ds₂ ++ DP.ds₃), ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64) :
    (bodiesF f a DK DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z salt embE prjE).OK where
  E := hE
  T := SCode.prj_emb _ _ (scWhole_ok salt (ckP f) (DK.at a) tFk tJk t3k dK)
  L := hLb
  B := SCode.prj_emb _ _ (scWhole_ok salt (ckP f) (DP.at a) tFp tJp t3p dP)

end OnBytes.RunA
