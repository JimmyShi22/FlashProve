-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/KeyTypesRead.lean: where the verifier program has said yes, the key file's reading
THROUGH THE ORACLE (`preT`, OnBytes/Tie/Decl/KeyPre.lean), at the oracle made from Lean's BLAKE2b,
has the value of the tie's fixed reading and typing of the key file (`rdKey`, `tyKeyFull`,
Johnson/Top/KeyTypesAt.lean): one value, by a lemma.

The key file's tie at one fixed hash, which is not in this library, speaks of a reading
`fun x key => (rdKey x key).bind fun td => (tyKeyFull … x td).map fun π => (td.1, π)` (the field
`key` of `readKeyOf`, Johnson/Top/Fire/KeyArmPair.lean [not in this library]): a plain function in
which the format's hash is called. A bound over a drawn hash function speaks of a term that asks the
function. Here the two are joined at the one function at which the tie stands.

Main names (Small for Full):
  `tyReadAt`, `tyReadFull`: the typing (`typeFile`) from the four things that it takes of a reading:
    the table, the three chains as read, the salt and the siblings of the binding tree's leaf.
  `tyKeyAt_eq`, `tyKeyFull_eq`: `tyKeyAt` | `tyKeyFull` at a reading whose number of a copy is 0 is
    that. By unfolding.
  `preT_keyAt`: general in the typing. `preT_keyFull`: at the full size's own letters.

Premises of `preT_keyFull`: those of `preT_yes` (OnBytes/KeyLink/KeyPreOwn.lean): the program's yes;
the planner's answer p; two tests on public data at the dry runs' rounds R at a key key₀ with the
item 0 that fits the tail's shape (`okAt`, `shapesFit`); hc: the oracle's answer at the string sC is
the program's digest of the public files. G, sb, cfg are free: the equation holds at every typing's
letters.

Limits: one direction of nothing: an equation of two values, at one fixed function. That either side
returns a string is not said (`types_keyFull`). Nothing at a drawn function. Nothing on soundness.
All that the heads of KeyPreOwn.lean and KeyTypesAt.lean do not claim. No other file of this library
calls `preT_keyAt`, `preT_keyFull` or `preT_keySmall`; here the last two call the first.

Named in this file and not in this library: Johnson/Top/Fire/KeyArmPair.lean.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.KeyTypesAt
import OnBytes.KeyLink.KeyPreOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker OnBytes.Maker.Page OnBytes.Tie
open OnBytes.TieK (ChainsData)
open OnBytes.KeyLink (tabK ksPlanned asmSlot ownK PubK preT_yes)
open OnBytes.Params (Rounds)
open VerifiableInference.OnPublicFiles
open _root_.Compile.Joined (JoinMsg)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

/-- The typing of a key file, from the four things that it takes of a reading. -/
def tyReadAt {Xi : Type} (C : CK) (a : ℕ) (W : Three.Whole) (tF : FrontMsg (List E))
    (tJ : JoinMsg (List E) ByteArray) (t3 : ByteArray)
    (silent : Xi → FrontMsg (List E) → JoinMsg (List E) ByteArray → ByteArray → Bool)
    (run : Xi → View → View → View → Bool) (sb : ℕ) (cfg : ByteArray) (t : Params.TableName)
    (r : Proof.TailRead) (salt : ByteArray) (path : List ByteArray) :
    Option (OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch) :=
  typeFile C a W tF tJ t3 silent run sb cfg (frontOf t.answers 0) ((joinOf t.answers r).getD tJ)
    ((seamOf r).getD t3) salt path r

/-- `tyKeyAt` at a reading whose number of a copy is 0. -/
theorem tyKeyAt_eq {Xi : Type} (C : CK) (a : ℕ) (W : Three.Whole) (tF : FrontMsg (List E))
    (tJ : JoinMsg (List E) ByteArray) (t3 : ByteArray)
    (silent : Xi → FrontMsg (List E) → JoinMsg (List E) ByteArray → ByteArray → Bool)
    (run : Xi → View → View → View → Bool) (sb : ℕ) (cfg : ByteArray)
    (td : Params.TableName × ChainsData) (h : td.2.copy = 0) :
    tyKeyAt C a W tF tJ t3 silent run sb cfg td =
      tyReadAt C a W tF tJ t3 silent run sb cfg td.1 td.2.r td.2.salt td.2.path := by
  unfold tyKeyAt tyReadAt frontK joinK seamK
  rw [h]

/-- **General in the typing**: tyK, a typing of the fixed reading; tyR, from the four things; the
two agree at a reading whose number of a copy is 0. -/
theorem preT_keyAt {Out : Type} {tyK : UserStm → Params.TableName × ChainsData → Option Out}
    (tyR : Params.TableName → Proof.TailRead → ByteArray → List ByteArray → Option Out)
    (hty : ∀ x td, td.2.copy = 0 → tyK x td = tyR td.1 td.2.r td.2.salt td.2.path)
    (Pt : List Bool → Prop) [DecidablePred Pt] (sC : List Bool) (sP : ByteArray → List Bool)
    (F : Files) (o : Model.Verify.Options) (id : String) (table further : Params.TableName)
    (h : PortYesAt F id table further) (p : Model.Verify.Planned)
    (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p) (key₀ : TableKey)
    (h0 : key₀.item = 0)
    (hf : key₀.fits (Key.tailPublic p.chains.key noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds) (hR : dryKey p.chains.key key₀ = some R) (a : ℕ)
    (hok : okAt a (some R) = true) (hsh : shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hc : digToBytes (oBits () sC) = Model.Verify.configuration F.pol F.lay F.KL) :
    (preT Pt (tabK sC sP (oBits ())) PubK.cfg (ksPlanned F.pol F.KL F.lay)
      (asmSlot fun t r s q => (tyR t r s q).map fun π => (t, π))
      (ownK sC sP p.chains.key) F.key).det oBits =
      (rdKey (stmOf F o) F.key).bind fun td => (tyK (stmOf F o) td).map fun π => (td.1, π) := by
  obtain ⟨d, hd⟩ := reads_key F o id table further h
  obtain ⟨e, hcopy⟩ := preT_yes Pt sC sP (fun t r s q => (tyR t r s q).map fun π => (t, π)) F id
    table further h p hp d hd key₀ h0 hf R hR a hok hsh hc
  rw [e, hd]
  show _ = (tyK (stmOf F o) (table, d)).map fun π => (table, π)
  rw [hty _ (table, d) hcopy]

/-! ## The full size -/

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) (G : FilesParameters X RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) G).Provers)

/-- The typing at this size's own letters, from the four things that a typing takes of a reading. -/
def tyReadFull (sb : ℕ) (cfg : ByteArray) (t : Params.TableName) (r : Proof.TailRead)
    (salt : ByteArray) (path : List ByteArray) :
    Option (OneProtocolProof 256 (batTC (LrG (restFullAt A E G P)) (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) G).annT)) :=
  tyReadAt (ckP .two) frS.P.T.a
    (dataAt frS.P.T.a (dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀))) (front₀ G.rec₀)
    (join₀ G.rec₀) ByteArray.empty silK (runKFull G) sb cfg t r salt path

/-- `tyKeyFull` at a reading whose number of a copy is 0. -/
theorem tyKeyFull_eq (sb : ℕ) (cfg : ByteArray) (x : UserStm)
    (td : Params.TableName × ChainsData) (h : td.2.copy = 0) :
    tyKeyFull A E G P sb cfg x td = tyReadFull A E G P sb cfg td.1 td.2.r td.2.salt td.2.path :=
  tyKeyAt_eq _ _ _ _ _ _ _ _ _ _ td h

/-- **Where the program has said yes: the key file's reading through the oracle, at the oracle made
from Lean's BLAKE2b, makes what the tie's fixed reading and typing make of the key file.** -/
theorem preT_keyFull (sb : ℕ) (cfg : ByteArray) (Pt : List Bool → Prop) [DecidablePred Pt]
    (sC : List Bool) (sP : ByteArray → List Bool) (F : Files) (o : Model.Verify.Options)
    (id : String) (table further : Params.TableName) (h : PortYesAt F id table further)
    (p : Model.Verify.Planned) (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p)
    (key₀ : TableKey) (h0 : key₀.item = 0)
    (hf : key₀.fits (Key.tailPublic p.chains.key noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds) (hR : dryKey p.chains.key key₀ = some R) (a : ℕ)
    (hok : okAt a (some R) = true) (hsh : shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hc : digToBytes (oBits () sC) = Model.Verify.configuration F.pol F.lay F.KL) :
    (preT Pt (tabK sC sP (oBits ())) PubK.cfg (ksPlanned F.pol F.KL F.lay)
      (asmSlot fun t r s q => (tyReadFull A E G P sb cfg t r s q).map fun π => (t, π))
      (ownK sC sP p.chains.key) F.key).det oBits =
      (rdKey (stmOf F o) F.key).bind fun td =>
        (tyKeyFull A E G P sb cfg (stmOf F o) td).map fun π => (td.1, π) :=
  preT_keyAt _ (fun x td h => tyKeyFull_eq A E G P sb cfg x td h) Pt sC sP F o id table further h p
    hp key₀ h0 hf R hR a hok hsh hc

end

/-! ## The small example -/

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (E : Coding A) (G : FilesParameters X RecSmall)
  (P : (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).Provers)

/-- The typing at this size's own letters, from the four things that a typing takes of a reading. -/
def tyReadSmall (sb : ℕ) (cfg : ByteArray) (t : Params.TableName) (r : Proof.TailRead)
    (salt : ByteArray) (path : List ByteArray) :
    Option (OneProtocolProof 256 (batTC (LrG (restSmallAt A E G P)) (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).annT)) :=
  tyReadAt (ckP .two) srS.P.T.a
    (dataAt srS.P.T.a (dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀))) (front₀ G.rec₀)
    (join₀ G.rec₀) ByteArray.empty silK (runKSmall G) sb cfg t r salt path

/-- `tyKeySmall` at a reading whose number of a copy is 0. -/
theorem tyKeySmall_eq (sb : ℕ) (cfg : ByteArray) (x : UserStm)
    (td : Params.TableName × ChainsData) (h : td.2.copy = 0) :
    tyKeySmall A E G P sb cfg x td = tyReadSmall A E G P sb cfg td.1 td.2.r td.2.salt td.2.path :=
  tyKeyAt_eq _ _ _ _ _ _ _ _ _ _ td h

/-- **Where the program has said yes: the key file's reading through the oracle, at the oracle made
from Lean's BLAKE2b, makes what the tie's fixed reading and typing make of the key file.** -/
theorem preT_keySmall (sb : ℕ) (cfg : ByteArray) (Pt : List Bool → Prop) [DecidablePred Pt]
    (sC : List Bool) (sP : ByteArray → List Bool) (F : Files) (o : Model.Verify.Options)
    (id : String) (table further : Params.TableName) (h : PortYesAt F id table further)
    (p : Model.Verify.Planned) (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p)
    (key₀ : TableKey) (h0 : key₀.item = 0)
    (hf : key₀.fits (Key.tailPublic p.chains.key noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds) (hR : dryKey p.chains.key key₀ = some R) (a : ℕ)
    (hok : okAt a (some R) = true) (hsh : shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hc : digToBytes (oBits () sC) = Model.Verify.configuration F.pol F.lay F.KL) :
    (preT Pt (tabK sC sP (oBits ())) PubK.cfg (ksPlanned F.pol F.KL F.lay)
      (asmSlot fun t r s q => (tyReadSmall A E G P sb cfg t r s q).map fun π => (t, π))
      (ownK sC sP p.chains.key) F.key).det oBits =
      (rdKey (stmOf F o) F.key).bind fun td =>
        (tyKeySmall A E G P sb cfg (stmOf F o) td).map fun π => (td.1, π) :=
  preT_keyAt _ (fun x td h => tyKeySmall_eq A E G P sb cfg x td h) Pt sC sP F o id table further h p
    hp key₀ h0 hf R hR a hok hsh hc

end

end OnBytes.K.Arm
