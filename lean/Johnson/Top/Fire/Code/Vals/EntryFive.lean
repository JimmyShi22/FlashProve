-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Vals/EntryFive.lean: the entry file's five letters of the written-out verifier
(lk, aL, wL, embL, prjL) as values with code, and the eight letters of which they are made (C, ds,
a, xs, dec, K, chal, salt), at both sizes. K and salt are arguments. No `noncomputable` stands in
this file: a definition for which Lean makes no code would be an error.
To evaluate the stored openings (`srD.xs`, `frD.xs`) makes the link's dry run once. `decS` and
`decF` are the decision of the program `verify-on-bytes` on the link.
No soundness is claimed.

-/
import Johnson.EntryRec.OklaSib
import OnBytes.Flat.EntryTerm
import OnBytes.Slice.EntryWireK

set_option autoImplicit false

namespace PV.EntryFive
open OnBytes.Flat OnBytes.Slice OnBytes.RunA
open _root_.Iop (InteractiveOracleProof twoExternalStrings RoundSplits BatchInteractiveOracleProof OPos OSym Dig)
open TypedOracleCompiler.Iop (ProtocolQueryLayout)
open _root_.Run (ckP chalP)
open _root_.Run.PQ (View SgX)
open TypedOracleCompiler.Run.PQ (SOf wqX)

/-! ## The small example -/

/-- the kit: verifier's messages as hash blocks, at the second field -/
abbrev CS : _root_.Run.PQ.CK := ckP .two
/-- the rounds' data -/
abbrev dsS : List TypedOracleCompiler.Run.PQ.RD := dsSmall
/-- the depth of the stored tables -/
abbrev aS : ℕ := srS.P.T.a
/-- the two openings of stored tables, as the library's term has them -/
abbrev xsS : List _root_.Run.PQ.XO := srD.xs
/-- the same, written: no name of the description srD in it -/
abbrev xsWS : List _root_.Run.PQ.XO := [⟨3, false, 0, 51⟩, ⟨3, true, 51, 51⟩]
theorem xsWS_eq : xsWS = srD.xs := sr_xs.symm
/-- the decision at a pair of records -/
abbrev decS : RecSmall × RecSmall → View → Bool := fun rr => decSmallX (recX rr)
/-- how a round's verifier message is read off K blocks -/
abbrev chalS (K : ℕ) : ∀ e k, (Fin K → Dig 256) → CS.Ch e k := chalP .two K
/-- the least K that the entry file's own rounds need -/
abbrev kEntryS : ℕ := 99
theorem kEntryS_eq : kEntryS = srD.K := sr_K.symm

/-- (1) lk -/
def lkS : InteractiveOracleProof (RecSmall × RecSmall) (twoExternalStrings (2 ^ srS.P.T.a) SgX) := linkSibSmall
theorem lkS_eq : lkS = linkProtocolOfRoundData CS dsS aS xsS decS := rfl
theorem lkS_is : lkS = linkSibSmall := rfl

/-- (2) aL -/
def aLS : RoundSplits linkSibSmall.shape := _root_.Run.Twin.allLo (SOf CS dsS)
theorem aLS_eq : aLS = _root_.Run.Twin.allLo (SOf CS dsS) := rfl

/-- (3) wL: the five fields of the written link's own wire record, as `wSib` lays them
(Johnson/EntryRec/OklaSib.lean). ITS FIELD ext IS weX a: THE LIST OF ALL 2 · 2^a POSITIONS: to
  read ANY
field builds it. -/
def wLS (K : ℕ) : ProtocolQueryLayout 256 (K + 1) (⟨linkSibSmall, aLS⟩ : BatchInteractiveOracleProof _ _) :=
  ⟨(wqX CS K (chalS K) dsS aS xsS fun _ => true).sh,
    (wqX CS K (chalS K) dsS aS xsS fun _ => true).ext,
    (wqX CS K (chalS K) dsS aS xsS fun _ => true).decO,
    (wqX CS K (chalS K) dsS aS xsS fun _ => true).nOpen,
    (wqX CS K (chalS K) dsS aS xsS fun _ => true).maxDepth⟩

/-- (4) embL -/
def embLS (salt : ℕ) : (p : OPos linkSibSmall.shape) → OSym linkSibSmall.shape p → List Bool :=
  TypedOracleCompiler.StringsList.embT salt CS dsS
theorem embLS_eq (salt : ℕ) : embLS salt = TypedOracleCompiler.StringsList.embT salt CS dsS := rfl

/-- (5) prjL -/
def prjLS (salt : ℕ) :
    (p : OPos linkSibSmall.shape) → List Bool → Option (OSym linkSibSmall.shape p) :=
  TypedOracleCompiler.StringsList.prjT salt CS dsS
theorem prjLS_eq (salt : ℕ) : prjLS salt = TypedOracleCompiler.StringsList.prjT salt CS dsS := rfl

/-- at every rest T over linkSibSmall: `wSib`'s fields are wL's -/
theorem wLS_wSib {I X RI : Type} [Fintype RI] [Nonempty RI]
    (T : RestR I X RI (Fin 1 → (Fin 19 → GE) × NZ) ((Fin srS.P.v → Bool) × Fin 1 → GE) srS.P.T.a
      linkSibSmall) (K : ℕ) :
    (wSib T K (chalP .two K)).nOpen = (wLS K).nOpen ∧
      (wSib T K (chalP .two K)).maxDepth = (wLS K).maxDepth := ⟨rfl, rfl⟩


/-! ## The full size -/

/-- the kit: verifier's messages as hash blocks, at the second field -/
abbrev CF : _root_.Run.PQ.CK := ckP .two
/-- the rounds' data -/
abbrev dsF : List TypedOracleCompiler.Run.PQ.RD := dsFull
/-- the depth of the stored tables -/
abbrev aF : ℕ := frS.P.T.a
/-- the two openings of stored tables, as the library's term has them -/
abbrev xsF : List _root_.Run.PQ.XO := frD.xs
/-- the same, written: no name of the description frD in it -/
abbrev xsWF : List _root_.Run.PQ.XO := [⟨3, false, 0, 62⟩, ⟨3, true, 62, 62⟩]
theorem xsWF_eq : xsWF = frD.xs := fr_xs.symm
/-- the decision at a pair of records -/
abbrev decF : RecFull × RecFull → View → Bool := fun rr => decFullX (recX rr)
/-- how a round's verifier message is read off K blocks -/
abbrev chalF (K : ℕ) : ∀ e k, (Fin K → Dig 256) → CF.Ch e k := chalP .two K
/-- the least K that the entry file's own rounds need -/
abbrev kEntryF : ℕ := 140
theorem kEntryF_eq : kEntryF = frD.K := fr_K.symm

/-- (1) lk -/
def lkF : InteractiveOracleProof (RecFull × RecFull) (twoExternalStrings (2 ^ frS.P.T.a) SgX) := linkSibFull
theorem lkF_eq : lkF = linkProtocolOfRoundData CF dsF aF xsF decF := rfl
theorem lkF_is : lkF = linkSibFull := rfl

/-- (2) aL -/
def aLF : RoundSplits linkSibFull.shape := _root_.Run.Twin.allLo (SOf CF dsF)
theorem aLF_eq : aLF = _root_.Run.Twin.allLo (SOf CF dsF) := rfl

/-- (3) wL: the five fields of the written link's own wire record, as `wSib` lays them
(Johnson/EntryRec/OklaSib.lean). ITS FIELD ext IS weX a: THE LIST OF ALL 2 · 2^a POSITIONS: to
  read ANY
field builds it. -/
def wLF (K : ℕ) : ProtocolQueryLayout 256 (K + 1) (⟨linkSibFull, aLF⟩ : BatchInteractiveOracleProof _ _) :=
  ⟨(wqX CF K (chalF K) dsF aF xsF fun _ => true).sh,
    (wqX CF K (chalF K) dsF aF xsF fun _ => true).ext,
    (wqX CF K (chalF K) dsF aF xsF fun _ => true).decO,
    (wqX CF K (chalF K) dsF aF xsF fun _ => true).nOpen,
    (wqX CF K (chalF K) dsF aF xsF fun _ => true).maxDepth⟩

/-- (4) embL -/
def embLF (salt : ℕ) : (p : OPos linkSibFull.shape) → OSym linkSibFull.shape p → List Bool :=
  TypedOracleCompiler.StringsList.embT salt CF dsF
theorem embLF_eq (salt : ℕ) : embLF salt = TypedOracleCompiler.StringsList.embT salt CF dsF := rfl

/-- (5) prjL -/
def prjLF (salt : ℕ) :
    (p : OPos linkSibFull.shape) → List Bool → Option (OSym linkSibFull.shape p) :=
  TypedOracleCompiler.StringsList.prjT salt CF dsF
theorem prjLF_eq (salt : ℕ) : prjLF salt = TypedOracleCompiler.StringsList.prjT salt CF dsF := rfl

/-- at every rest T over linkSibFull: `wSib`'s fields are wL's -/
theorem wLF_wSib {I X RI : Type} [Fintype RI] [Nonempty RI]
    (T : RestR I X RI (Fin 1 → (Fin 29 → GE) × NZ) ((Fin frS.P.v → Bool) × Fin 1 → GE) frS.P.T.a
      linkSibFull) (K : ℕ) :
    (wSib T K (chalP .two K)).nOpen = (wLF K).nOpen ∧
      (wSib T K (chalP .two K)).maxDepth = (wLF K).maxDepth := ⟨rfl, rfl⟩

end PV.EntryFive
