-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/ForProver/HomeIsOurs.lean: IT STATES NO GOAL. AT THE INPUT OF THE LIBRARY'S TYPED
COMPILER AT THE FULL SIZE (`FlashProve.homeR b Z`, Johnson/Goal/Conditions/HomeAtWider.lean) THE
ENCODING AND THE OOD SAMPLE OF AN INDEX ARE `strAt` AND `recAt`
(Johnson/Bind/ForProver/SevenAt.lean) AT THE PLAIN READERS OF THE INDEX AND THE COINS; and one law
of the library that stands at that encoding and that sample, written again at these terms. LAWS ON
THE MAPS OF THE TIE. Statements and proofs.

Why. The library's laws on an honest side over typed oracles stand at `(homeR b Z).protocol.encodeIndex i r` and
`(homeR b Z).protocol.recOf i r e`. `strAt` is made of the columns of the stand-in committer on byte
strings (`Bind.Twin.commitW`, Johnson/Bind/Twin.lean). With the two equations here such a law speaks
of that committer's columns and of the sample `recAt`. Two inputs are spoken of below: the goals' (a
matrix of cells, pads and tails on finite ranges: what the library's typed encoder takes) and the
frame's (functions of two plain numbers: what the frame for an honest prover hands out).

Main names (namespace `Bind.ForProver`).
   **`home_is_ours`**: at every b, all public files Z, every index i, all coins q and every seed e
      of the input `homeR b Z`: the encoding is `strAt`, and the sample is `recAt`, at the full
      size's sizes and shape, the packing of `cellsReader i` and the coins made of `padReader q.1`
      and `tailReader q.2`. It is `FlashProve.enc_home` (Johnson/Goal/Conditions/LinkMeant.lean)
      with `strAt_readers` and `recAt_readers` (Johnson/Bind/ForProver/SevenReaders.lean).
   **`accL_at_ours`**: WHAT IT BUYS, ONCE: the third clause of `FlashProve.linkFits_at`
      (Johnson/Goal/Conditions/LinkFitsAt.lean), under that theorem's own premises to the letter,
      with its first clause laid in: the accept law of that input's link, at the instance
      (`recAt`, `recAt`) and the stored strings (`strAt`, `strAt`) of one index under two coins and
      two seeds.
Limits. `accL_at_ours` SAYS NOTHING THAT `linkFits_at` DOES NOT SAY: it is that theorem's clause
with two terms written otherwise. ITS PREMISES ARE THAT THEOREM'S, AND NO TERM OF THIS FILE MEETS
THEM ALL: the files are in scope and the description is live; the link's structure of the honest
side is the written one at the library's messages; no fall at the link; the clause's own: Yes i x,
and the two seeds outside Zs, where Yes and Zs are letters; the three structures Hs and the falls F
are letters, for which no term is laid here; the coin's type and its map are letters. An accept law
is conditional on the tests of work. It is one of three protocols' honest sides: NOT verify(), NOT
COMPLETENESS. EVERY STATEMENT HERE IS ON MAPS BETWEEN THE TWO INPUTS (`cellsReader`, `padReader`,
`tailReader`); THAT THE HONEST PROVER'S PRIVATE INPUT AT THE PROTOCOL IS THE GOALS', WITH THE
FRAME'S READERS MADE OF IT BY THESE MAPS, IS SAID BY NO FILE BENEATH THIS ONE. The index i is any
member of the input's type: in range or not. (r, e) stand where the link reads the committed table
(its item 0), (r', e') where it reads a second table (its item 1). That r, e are the coins and the
seed of the run that makes the commitment ID (its salts, tree, root and name; e sampled at that
name), and that r', e' are a copy's own, sampled apart, with a copy's tree, name and root: NEITHER
is said here. Nothing here says that each table's randomness has one seed, that the two tables'
randomness is sampled apart, or that the second table's is the one at which a session runs. The full
size alone. No query, no coin's law. The format's second hash function (`OnBytes.secondHashFunction`,
OnBytes/Hash/SecondHashFunction.lean; the library's files call it the earlier hash) stands by name beneath terms
of these statements: the premise `protocolDataWellFormed` is the library's test on the public files at it
(Johnson/Goal/Description/Live.lean), and `flashProveData`, of which `homeR b Z` and `(dataAtFiles flashProveData Z).dec`
are made, is `flashProveDataAtSecondHash OnBytes.secondHashFunction` (`theLayAt_older`, Johnson/Goal/Description/Lay.lean); no
statement here says anything of that function. This file writes no honest prover. Nothing on index
privacy, on soundness or on any program.
Terms: lean/TERMS.md.
-/
import Johnson.Bind.ForProver.SevenReaders
import Johnson.Goal.Conditions.LinkFitsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.ForProver
open VerifierAndGoals FlashProve VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD Rom
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open _root_.Run (ckP)
open TypedOracleCompiler.Compile.Batch.Cms (batLC wLC)
open OnBytes.Prover (ThreeProvers Falls AccLaw)
open PV.EntryFive (dsF xsF)
open Johnson.Prover.Link (linkRec LCoins linkNext)
open _root_.Desc.K15 (frP)
open AtPublicFiles.Key (cellsReader padReader tailReader)
open ProofFile.Honest (TableRand)
open Bind.Column (shFull agree_full)

/- Lean compares these by their names. (Not the coding: its types are unfolded below.) -/
attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

/-- **At the input of the library's typed compiler at the full size the encoding and the OOD sample
of an index are `strAt` and `recAt` at the plain readers of the index and the coins.** A law on the
maps of the tie; that the honest prover's input at the protocol is so made is said by no file
beneath this one. -/
theorem home_is_ours :
  ∀ (b : PublicFiles → ℕ) (Z : PublicFiles) (i : (homeR b Z).Index) (q : (homeR b Z).protocol.EncodingRandomness) (e : (homeR b Z).protocol.OutOfDomainSeed),
    (homeR b Z).protocol.encodeIndex i q =
        strAt frS shFull
          (entryAtF numsRef.kLo numsRef.rows frS.P.v
            (cellsReader (i : Cells (frS.toDecR frZ 402653181) numsRef)))
          ⟨padReader (S := frS) (cut := 402653181) q.1, tailReader (S := frS) q.2⟩ ∧
      (homeR b Z).protocol.recOf i q e =
        recAt frS frZ shFull
          (entryAtF numsRef.kLo numsRef.rows frS.P.v
            (cellsReader (i : Cells (frS.toDecR frZ 402653181) numsRef)))
          ⟨padReader (S := frS) (cut := 402653181) q.1, tailReader (S := frS) q.2⟩ e :=
  fun b Z i q e =>
    ⟨(enc_home b Z i q e).1.trans (strAt_readers (Zs := frZ) agree_full full_fits.1 i q).symm,
      (enc_home b Z i q e).2.trans (recAt_readers (Zs := frZ) agree_full full_fits.1 i q e).symm⟩

/-- **What it buys, once**: the accept law of that input's link (the third clause of
`FlashProve.linkFits_at`, its first laid in), under that theorem's premises to the letter, the
instance and the two stored strings at this folder's terms; the prover's messages stay the
library's, made of the typed input: en is the packing of the index's plain reader, τ and τ' are the
coins made of the plain readers of r and r'. It says nothing that `linkFits_at` does not say.
Conditional on the tests of work; not verify(); not completeness. -/
theorem accL_at_ours :
  ∀ (b : PublicFiles → ℕ) (Z : PublicFiles), InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
    ∀ (Kc : Type) [Fintype Kc] [Nonempty Kc] (coinsOf : Kc → LCoins)
      (Hs : ThreeProvers (homeR b Z).protocol) (F : Falls Hs) (Yes : (homeR b Z).Index → (homeR b Z).Instance → Prop)
      (Zs : (homeR b Z).Index → (homeR b Z).protocol.EncodingRandomness → Set (homeR b Z).protocol.OutOfDomainSeed),
    Hs.Lk = linkRec (ckP .two) dsF frS.P.T.a xsF (dataAtFiles flashProveData Z).dec
      (fun w => ((homeR b Z).protocol.encodeIndex w.1 w.2.1.1, (homeR b Z).protocol.encodeIndex w.1 w.2.2.1))
      (fun w x c => linkNext frP frS 97
        (Johnson.Prover.Link.linOf x
          ((homeR b Z).protocol.encodeIndex w.1 w.2.1.1, (homeR b Z).protocol.encodeIndex w.1 w.2.2.1)
          (honestPolys frS
            (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef w.1 w.2.1.1.1)))
            (tailWords frS w.2.1.1.2))
          (honestPolys frS
            (rowWords frS (honestMsgs frS (cellWords frS frZ 402653181 numsRef w.1 w.2.2.1.1)))
            (tailWords frS w.2.2.1.2)))
        (coinsOf c)) →
    (∀ w x c, F.Lk w x c = ∅) →
    ∀ i x r e r' e' c, Yes i x → e ∉ Zs i r → e' ∉ Zs i r' →
    ∀ (en : ℕ → ℕ → UInt64) (τ τ' : TableRand),
      en = entryAtF numsRef.kLo numsRef.rows frS.P.v
        (cellsReader (i : Cells (frS.toDecR frZ 402653181) numsRef)) →
      τ = ⟨padReader (S := frS) (cut := 402653181) r.1, tailReader (S := frS) r.2⟩ →
      τ' = ⟨padReader (S := frS) (cut := 402653181) r'.1, tailReader (S := frS) r'.2⟩ →
      AccLaw (batLC (homeR b Z).protocol (homeR b Z).linkRoundSplits) (wLC (homeR b Z).queryLayout)
        (recAt frS frZ shFull en τ e, recAt frS frZ shFull en τ' e')
        (strAt frS shFull en τ, strAt frS shFull en τ')
        (Hs.Lk.strat (i, (r, e), (r', e'))
          (recAt frS frZ shFull en τ e, recAt frS frZ shFull en τ' e') c)
        (Hs.Lk.withheld (i, (r, e), (r', e'))
            (recAt frS frZ shFull en τ e, recAt frS frZ shFull en τ' e') ∪
          F.Lk (i, (r, e), (r', e'))
            (recAt frS frZ shFull en τ e, recAt frS frZ shFull en τ' e') c) := by
  intro b Z hZ hl Kc _ _ coinsOf Hs F Yes Zs hLk hF i x r e r' e' c hy he he' en τ τ' hen hτ hτ'
  subst hen hτ hτ'
  have k := linkFits_at b Z hZ hl Kc coinsOf Hs F Yes Zs hLk hF
  have a := k.2.2.1 i x r e r' e' c hy he he'
  rw [k.1 i r e r' e', (home_is_ours b Z i r e).1, (home_is_ours b Z i r' e').1,
    (home_is_ours b Z i r e).2, (home_is_ours b Z i r' e').2] at a
  exact a

end Bind.ForProver

end

#print axioms Bind.ForProver.home_is_ours
#print axioms Bind.ForProver.accL_at_ours
