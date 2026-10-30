-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TypingParts.lean: the parts of the typing of a whole file (`typeFile`,
OnBytes/Maker/TypeFile.lean) as total functions of what was read.

`typeFile` returns a proof string or nothing. A statement over a proof string that is assembled from
three chains as read (`FileW.assemble`, OnBytes/TypedOracleCompiler/Joined/Assemble.lean) wants the parts as values:
the first chain's salt, the three chains' strings, the openings of the stored table. Here each part
is a function that has a fixed value where `typeFile`'s own step returns nothing.

  `plainsD`    the fixed plain parts of a shape: each round's own fixed message
  `saltAt`, `tabsAt`, `extAt`, `strAt₁`, `strAt₂`, `strAt₃`   the parts
  `typeFile_parts`   where `typeFile` returns a string, that string is the assembly of these parts,
      at every written file whose verifier is the description's

Not claimed. That `typeFile` returns a string at any file. Where it returns nothing, the parts are
still values, and nothing is said of their assembly. Nothing on soundness.


-/
import OnBytes.Maker.TypeFile

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ Compile.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile (Opening)
open TypedOracleCompiler.Compile.Batch (OneProtocolProof)
open TypedOracleCompiler.Joined (ChainStr FileW)

/-- The fixed plain parts of a shape: each round's own fixed message. -/
def plainsD : (s : Shape) → Plains s
  | [] => ()
  | r :: s => (r.dPlain, plainsD s)

section
variable {TF TJ T3 Xi : Type} (C : CK) (a : ℕ) (W : Three.Whole) (tF : TF) (tJ : TJ) (t3 : T3)

/-- The first chain's salt: the bits of its run's value. -/
def saltAt (r : Proof.TailRead) : List Bool := bytesToBits (r.first.out.run.getD ByteArray.empty)

/-- The tables of all openings of the file. -/
def tabsAt (saltBytes : ℕ) (r : Proof.TailRead) : List (ℕ × List (ℕ × Row3)) :=
  (tabsWFull W saltBytes r).getD []

/-- The openings of the stored table. -/
def extAt (cfg : ByteArray) (r : Proof.TailRead) :
    (oneExternalString (2 ^ a) SgX).Pos → Option (Opening 256 SgX) :=
  (extWFull a cfg W r).getD fun _ => none

/-- What is read for the first chain. -/
def strAt₁ (saltBytes : ℕ) (pF : TF) (r : Proof.TailRead) :
    ChainStr 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₁ :=
  str₁ C (WholeD.of a W) tF tJ t3 pF
    ((plainsT C (WholeD.of a W).ds₁ r.first.out.rounds.toList.dropLast).getD (plainsD _))
    (tabsAt W saltBytes r) r.first.out.rounds.toList

/-- For the second chain. -/
def strAt₂ (saltBytes : ℕ) (pJ : TJ) (r : Proof.TailRead) :
    ChainStr 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₂ :=
  str₂ C (WholeD.of a W) tF tJ t3 pJ
    ((plainsT C (WholeD.of a W).ds₂ r.shared.out.rounds.toList).getD (plainsD _))
    (tabsAt W saltBytes r) r.shared.out.rounds.toList

/-- For the third chain. -/
def strAt₃ (saltBytes : ℕ) (p3 : T3) (r : Proof.TailRead) :
    ChainStr 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₃ :=
  str₃ C (WholeD.of a W) tF tJ t3 p3
    ((plainsT C (WholeD.of a W).ds₃ r.second.out.rounds.toList).getD (plainsD _))
    (tabsAt W saltBytes r) r.second.out.rounds.toList

variable (silent : Xi → TF → TJ → T3 → Bool) (run : Xi → View → View → View → Bool)

/-- **Where the typing returns a string, it is the assembly of the parts.** -/
theorem typeFile_parts {I X : Type} {L : TypedOracleCompiler.Iop.BatchProtocolWithLeafBody I X}
    {Wb : TypedOracleCompiler.Iop.QueryLayout 256 L} (t) (wq) (embS) (embP) (xin) (embE) (saltBytes : ℕ)
    (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3) (salt : ByteArray) (path : List ByteArray)
    (r : Proof.TailRead) (π)
    (h : typeFile C a W tF tJ t3 silent run saltBytes cfg pF pJ p3 salt path r = some π) :
    π = FileW.assemble (W := Wb)
      ⟨wholeDesc C (WholeD.of a W) tF tJ t3 silent run, t, wq, embS, embP, xin, embE⟩ (saltAt r)
      (strAt₁ C a W tF tJ t3 saltBytes pF r) (strAt₂ C a W tF tJ t3 saltBytes pJ r)
      (strAt₃ C a W tF tJ t3 saltBytes p3 r) (extAt a W cfg r) (bytesToDig r.place.root)
      r.place.place (path.map bytesToDig) (rsOf (r.place.places + r.place.place) salt) := by
  obtain ⟨tabs, ext, ht, he, h1⟩ :=
    typeFile_some C a W tF tJ t3 silent run saltBytes cfg pF pJ p3 salt path r π h
  obtain ⟨run₁, pl₁, pl₂, pl₃, e0, e1, e2, e3, hπ⟩ :=
    toBPrfW_assemble C (WholeD.of a W) tF tJ t3 silent run (Wb := Wb) t wq embS embP xin embE pF pJ
      p3 tabs ext salt path r π h1
  unfold saltAt strAt₁ strAt₂ strAt₃ tabsAt extAt
  rw [e0, e1, e2, e3, ht, he]
  exact hπ

end

end OnBytes.Maker
