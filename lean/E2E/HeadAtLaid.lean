-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/HeadAtLaid.lean: in scope, where the test `protocolDataWellFormed` accepts, the structures of conditions
`P5J.AtMg` (Johnson/P5J/AtMg.lean) and `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean) hold at the very
letters of any `P5J.LaidAt` (Johnson/P5J/LaidOpens.lean) at the same public files.

Why. The statements of E2E/ at three public files Z bind the letters D, r, Zp, Np, cF under a
hypothesis L : `LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF`. Statements of other folders
stand under `AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x`. `P5J.head_of_live`
(Johnson/P5J/HeadOfLive.lean) gives such a structure at SOME letters. Here: these letters are L's.

What is shown.
  `read_of_inScope`: files in scope are read. (The text of `AtFullSide.Tie.read_of_inScope`,
    AtFullSide/Bind/TheTieAtNamed.lean, once more: that file lies in a side library, which no file
    of the main library imports.)
  `laidAt_unique`: two `LaidAt` at one letter for the earlier hash and the same three files have the
    same five other letters. (The proof of `P5J.AtMg.unique`, Johnson/HB/LLHARD/HeadFacts.lean,
    which reads of its two structures the field laid alone.)
  **`head_at_laid`**: scope, live and L give an x with `AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x`.
  `atMg_at_laid`: so `AtMg OnBytes.secondHashFunction Z D r Zp Np cF`.
  `data_run_at_laid`: D is `VerifierAndGoals.AtTheName.dpZ Z` and r is `theProofRun (asDescriptionFiles Z)`.

Limits. No property of the protocol is claimed. The three premises are premises: that files are in
scope, that `protocolDataWellFormed` accepts them and that a `LaidAt` holds at them is shown here of no files. x
stays under "there is"; it is the only one (`P5J.head_unique`, Johnson/HB/LLHARD/HeadFacts.lean,
which this file does not import). `data_run_at_laid` gives D = `dpZ Z`; `data_atFiles`
(E2E/BridgePaidAtFiles.lean, not imported here) gives `(dpZ Z).at frS.P.T.a = D` from the same
premises. The two agree: under `AtMg` the data are `Johnson.G.writtenPFull`
(`P5J.AtMg.data_written`), which `.at frS.P.T.a` leaves as they are (`writtenPFull_at`,
Johnson/Flat/Dec/DataAtWritten.lean). This file does not state that. At the format's second hash function
`OnBytes.secondHashFunction` alone; the full size alone. All limits of Johnson/P5J/HeadOfLive.lean stand.
-/
import Johnson.P5J.HeadOfLive
import Johnson.P5J.ChainFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.AtFiles
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open VerifierAndGoals (PublicFiles InScope readFiles asDescriptionFiles)
open FlashProve (protocolDataWellFormed theProofRun)
open VerifierAndGoals.AtTheName (dpZ)
open P5J

/-- Files in scope are read: by its text `InScope` is false where the reader rejects. -/
theorem read_of_inScope {Z : PublicFiles} (scope : InScope Z = true) : ∃ pp, readFiles Z = .ok pp := by
  unfold InScope at scope
  rw [Bool.and_eq_true] at scope
  obtain ⟨-, h⟩ := scope
  split at h
  · exact ⟨_, by assumption⟩
  · cases h

/-- Two `LaidAt` at one letter for the earlier hash and the same three files have the same five
other letters. -/
theorem laidAt_unique {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {D D' : WholeD}
    {r r' : LPFD.Full.RunPF} {Zp Zp' : ProofFile.Pub} {Np Np' : H2U.Places4} {cF cF' : Chain TS ProofFile.Cl}
    (L : LaidAt o pol lay KL D r Zp Np cF) (L' : LaidAt o pol lay KL D' r' Zp' Np' cF') :
    Zp = Zp' ∧ Np = Np' ∧ cF = cF' ∧ D = D' ∧ r = r' := by
  obtain rfl : Zp = Zp' := Except.ok.inj (L.pub.symm.trans L'.pub)
  obtain rfl : Np = Np' := Except.ok.inj (L.places.symm.trans L'.places)
  obtain rfl : cF = cF' := Except.ok.inj (L.chain.symm.trans L'.chain)
  exact ⟨rfl, rfl, rfl, Except.ok.inj (L.data.symm.trans L'.data), L.run.trans L'.run.symm⟩

/-- **The head at `LaidAt`'s letters.** In scope, where `protocolDataWellFormed` accepts: at the letters of any
`LaidAt` at Z's three files and the format's second hash function there is an x at which `AtMgA` holds. -/
theorem head_at_laid (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    ∃ x, AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x := by
  obtain ⟨pp, read⟩ := read_of_inScope scope
  obtain ⟨Zp', Np', cF', x, h⟩ := head_of_live Z scope read live
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := laidAt_unique L h.laid
  exact ⟨x, h⟩

/-- So `AtMg` holds at these letters. -/
theorem atMg_at_laid (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    AtMg OnBytes.secondHashFunction Z D r Zp Np cF :=
  let ⟨_, h⟩ := head_at_laid Z scope live L
  h.toAtMg

/-- The data and the decision of such a `LaidAt` are the description's own at Z. -/
theorem data_run_at_laid (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    D = dpZ Z ∧ r = theProofRun (asDescriptionFiles Z) := by
  obtain ⟨pp, read⟩ := read_of_inScope scope
  obtain ⟨Zp', Np', cF', x, h⟩ := head_of_live Z scope read live
  obtain ⟨-, -, -, hD, hr⟩ := laidAt_unique L h.laid
  exact ⟨hD, hr⟩

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.read_of_inScope
#print axioms AtPublicFiles.AtFiles.laidAt_unique
#print axioms AtPublicFiles.AtFiles.head_at_laid
#print axioms AtPublicFiles.AtFiles.atMg_at_laid
#print axioms AtPublicFiles.AtFiles.data_run_at_laid
