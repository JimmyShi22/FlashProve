-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/TypingAKey.lean: a typing of a key file at one public input (`TypingA`,
OnBytes/TypedOracleCompiler/Joined/K/LeftOfChains.lean): the written file `fileKey` (Johnson/Maker/Written.lean) and
the parts of `typeFile` (OnBytes/Maker/TypingParts.lean).

`TypingA` has the letters of a statement "where the program says yes to a key file, the compiled
verifier of a file with three joined chains has the value yes": an interface of typed oracles and
its wiring, the file's rounds, the file as it is written, and maps from one fixed reading of the
file's bytes to a proof string's parts. Here these letters get values.

  `typingKey`       the value. The interface is made of the file's own rounds, so it stands at one
                    set of plain data W, that is: at one public input.
  `typingKey_prf`   where `typeFile` returns a string at a reading, and the binding tree as read has
                    2 ^ depthReqT leaves, the typing's proof string is that string

What stays a letter. recOf: the record of a table (its seeds are a function of the table's name and
the public files, OnBytes/Entry/Table.lean). cA: how the record's answers are written into the list
that a chain is handed. pF, pJ, p3: what the three silent rounds send, from the reading's data. g,
the oracle functions. sb, the plan's number of bytes of a salt; cfg; sFS. And all of which the
interface and the wiring are made beside W: f, K, a; the six fixed messages; the two tests on the
silent rounds and the two runs; DP, the proof file's data; eL, the entry file's part (any protocol)
and wL, its wire record (no law is asked of it); Z, the object's letters; Bd and b, the bodies; the
three depths.

Not claimed. No field of `LeftHoles`. That W is the data of any file. Nothing on soundness.


-/
import Johnson.Maker.WrittenA
import OnBytes.Maker.TypingParts
import OnBytes.TypedOracleCompiler.Joined.K.LeftOfChains

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ Compile OnBytes.RunA TypedOracleCompiler.Joined TypedOracleCompiler.Joined.K Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Compile.Batch.Cms (Bodies typedOracleCarrier cmsTA)

section Key
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed]
  (f : _root_.Fmt.Fld) (K a : ℕ) (W : Three.Whole) (DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Seed × Ans → TFk → TJk → T3k → Bool)
  (runK : Seed × Ans → View → View → View → Bool)
  (silP : X × (Seed × Ans) → TFp → TJp → T3p → Bool)
  (runP : X × (Seed × Ans) → View → View → View → Bool)
  (eL : LinkProtocolWithLeafCoding (Seed × Ans) a)
  (Z : Letters I X RI Seed Ans a
    (wholeDesc (ckP f) ((WholeD.of a W).at a) tFk tJk t3k silK runK).proto eL.QL
    (wholeDesc (ckP f) (DP.at a) tFp tJp t3p silP runP).batch)
  (wL : TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1)
    (⟨eL.QL, eL.aL⟩ : BatchInteractiveOracleProof ((Seed × Ans) × (Seed × Ans)) (twoExternalStrings (2 ^ a) SgX)))
  (Bd : Type) (depthReq depthReqT depthReqL : ℕ)
  (b : Bodies (objF f a (WholeD.of a W) DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z)
    Bd)
  (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1)
    (typedOracleCarrier (objF f a (WholeD.of a W) DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z)
      Bd (chainsOf (ckP f) ((WholeD.of a W).at a) tFk tJk t3k).ann
      eL.aL)))
  (sb sFS : ℕ) (cfg : ByteArray) (recOf : Params.TableName → Seed × Ans)
  (cA : Ans → List (Dig 256)) (pF : Dat → TFk) (pJ : Dat → TJk) (p3 : Dat → T3k)

/-- **A typing of a key file.** -/
noncomputable def typingKey : TypingA where
  I := Empty
  X := (objF f a (WholeD.of a W) DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z).XC
  L := typedOracleCarrier
    (objF f a (WholeD.of a W) DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z) Bd
    (chainsOf (ckP f) ((WholeD.of a W).at a) tFk tJk t3k).ann
    eL.aL
  W := wireF f K a (WholeD.of a W) DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
    depthReq depthReqT depthReqL b
  Y := Seed × Ans
  E := oneExternalString (2 ^ a) SgX
  sMT := 256 + 8 * sb
  sFS := sFS
  g := g
  G := chainsOf (ckP f) ((WholeD.of a W).at a) tFk tJk t3k
  F := fileKey f K a (WholeD.of a W) DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL
    Bd depthReq depthReqT depthReqL b
  rsOf := fun place salt => rsOf (2 ^ depthReqT + place) salt
  cms := fun t _ =>
    cmsTA (L := objF f a (WholeD.of a W) DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z)
      cA (bytesToDig t.root) (recOf t).2
  x := fun t _ => recOf t
  salt := fun d => saltAt d.2.r
  k₁ := fun d => strAt₁ (ckP f) a W tFk tJk t3k sb (pF d) d.2.r
  k₂ := fun d => strAt₂ (ckP f) a W tFk tJk t3k sb (pJ d) d.2.r
  k₃ := fun d => strAt₃ (ckP f) a W tFk tJk t3k sb (p3 d) d.2.r
  ext := fun d => extAt a W cfg d.2.r

/-- **Where `typeFile` returns a string, the typing's proof string is that string.** -/
theorem typingKey_prf (d : Dat) (π)
    (h : typeFile (ckP f) a W tFk tJk t3k silK runK sb cfg (pF d) (pJ d) (p3 d) d.2.salt d.2.path
      d.2.r = some π)
    (hp : d.2.r.place.places = 2 ^ depthReqT) :
    (typingKey f K a W DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd depthReq
      depthReqT depthReqL b g sb sFS cfg recOf cA pF pJ p3).prf d = π := by
  rw [typeFile_parts (ckP f) a W tFk tJk t3k silK runK
    (Wb := wireF f K a (WholeD.of a W) DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
      depthReq depthReqT depthReqL b) .test
    (wqWhole (ckP f) K (chalP f K) ((WholeD.of a W).at a) tFk tJk t3k silK runK) b.embT
    (fun z => z) (fun _ => none) b.embE sb cfg (pF d) (pJ d) (p3 d) d.2.salt d.2.path d.2.r π h, hp]
  rfl

end Key

end OnBytes.Maker
