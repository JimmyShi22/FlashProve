-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/KeyTypesAt.lean: a reader and a typing of a key file, written out, and two facts on them
where the Lean program `verify-on-bytes` (OnBytes/Main.lean; "the program") has said yes: the reader
returns the program's own table; and the typing of what was read returns a string, or the key file
shows a collision of the format's hash (`keyCollidesAt`, OnBytes/Maker/Page/CollidesAt.lean).

These are the hypotheses `reads` and `types` of `KeyFive` (Johnson/Top/Fire/KeyArmPair.lean
[not in this library]), in that record's form, at the three files' own object
(Johnson/Flat/WireAt.lean) at both sizes. No wire, no number of blocks, no coding of typed queries
as strings and no family of typed oracle functions occurs in them. THE READER HASHES: `rdKey` is
made of the program's own readers, and these hash at Fmt.formatHash (they draw the rounds' verifier's
messages and walk the opened trees); what they return, and so the typed string, holds answers of
that hash beside the file's bytes. So the reader and the typing are fixed before the key file, not
before the hash. No file of this library calls `reads_keyAt`, `types_keyFull` or `types_keySmall`,
and `types_key` is called in this file alone.

Main names (Small for Full at the small example):
  `rdKey x key`: the reader: `TieK.readKeyChains` (OnBytes/TieK/ReadThreeDefs.lean) at the
    statement's three public files: the planner, the program's reader of the table, the three chains
    as read.
  `tyKeyAt`: the typing: `typeFile` (OnBytes/Maker/TypeFile.lean) at what the silent rounds send
    by `frontK`, `joinK`, `seamK` (Johnson/Maker/Page/PortKey.lean) and at the salt, the siblings
    and the chains of what was read.
  `reads_key`: at the program's yes the reader returns the program's own table. No hypothesis.
  `types_key`: at the program's yes on a served statement, the typing returns at what the reader
    returned, or `keyCollidesAt`. General in the record's type and in the typing's letters.
  `tyKeyFull A E G P sb cfg`: the typing at the full size's own letters, typed as Test's string of
    the three files' object. sb: the number of bytes of a salt; cfg: the typing's digest.
  `reads_keyAt`, `types_keyFull`: the two facts in the form of the fields of `KeyFive`
    [not in this library]. At the sizes the key at which the dry runs are made is `keyOf` of
    `G.rec₀`, whose item is 0 by definition.

Hypotheses of `types_key`, none of which sees a key file: G is at the plan of Z (`AtPlan`,
OnBytes/Flat/BigAt.lean); the key at which the dry runs are made has item 0 and fits the index; the
dry runs return three lists R; three tests on R pass (`okAt`, `oneShapeB`, `saltsFit`); sb is the
one-time chain's own number of bytes of a salt.

Limits. The hypotheses are not shown here at any G. A, E and P, which enter the sized names through
the typing's type alone, carry laws or instances inside: that their types have members together is
not shown here. Nothing is said on how hard a key file is to make of which `keyCollidesAt` holds.
That the typing returns says nothing on what a verifier says of the string. cfg is a free letter:
the two facts hold at every cfg; which cfg is the right one is a matter of what a verifier says of
the string. What the reader and the typing cost, and how often they hash, is not looked into.
Nothing on soundness. All that the heads of OnBytes/Maker/Page/CollidesAt.lean and
Johnson/Flat/WireAt.lean do not claim. For proofs only; no program imports this file.

Named in this file and not in this library: Johnson/Top/Fire/KeyArmPair.lean.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.WireAt
import Johnson.Maker.Page.PortKey
import OnBytes.Flat.BigAt
import OnBytes.K.ExitServed
import OnBytes.Maker.Page.CollidesAt
import OnBytes.Maker.TypeTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker OnBytes.Maker.Page OnBytes.Tie
open OnBytes.TieK (ChainsData)
open TypedOracleCompiler.Joined.K (Dat)
open OnBytes.Params (Rounds)
open VerifiableInference.OnPublicFiles
open _root_.Compile.Joined (JoinMsg)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

/-- The reader of a key file, at the statement's three public files. -/
def rdKey (x : UserStm) (key : ByteArray) : Option (Params.TableName × ChainsData) :=
  TieK.readKeyChains x.pol x.lay x.KL key

/-- The typing of what was read of a key file. -/
def tyKeyAt {Xi : Type} (C : CK) (a : ℕ) (W : Three.Whole) (tF : FrontMsg (List E))
    (tJ : JoinMsg (List E) ByteArray) (t3 : ByteArray)
    (silent : Xi → FrontMsg (List E) → JoinMsg (List E) ByteArray → ByteArray → Bool)
    (run : Xi → View → View → View → Bool) (sb : ℕ) (cfg : ByteArray)
    (td : Params.TableName × ChainsData) :
    Option (OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch) :=
  typeFile C a W tF tJ t3 silent run sb cfg (frontK td) (joinK tJ td) (seamK t3 td) td.2.salt
    td.2.path td.2.r

/-- **At the program's yes the reader returns the program's own table.** -/
theorem reads_key (F : Files) (o : Model.Verify.Options) (id : String)
    (table further : Params.TableName) (h : PortYesAt F id table further) :
    ∃ d, rdKey (stmOf F o) F.key = some (table, d) := by
  obtain ⟨_, _, d, _, _, -, -, hd, -⟩ :=
    TieK.readKeyChains_of F table (TieK.port_key_chains F id table further h)
  exact ⟨d, hd⟩

/-- The field `reads` of `KeyFive` [not in this library], at `rdKey`. The size does not occur. -/
theorem reads_keyAt (Z : Pub) :
    ∀ F o id table further, o.id = some id → o.bits = 128 → PortYesAt F id table further →
      servedAt Z (stmOf F o) = true → ∃ d, rdKey (stmOf F o) F.key = some (table, d) :=
  fun F o id table further _ _ h _ => reads_key F o id table further h

/-- **At the program's yes on a served statement the typing returns, or the key file shows a
collision.** key₀: the key at which the dry runs are made; R: the three lists that they return. -/
theorem types_key {X Rc Xi : Type} {Z : Pub} {G : FilesParameters X Rc} (hG : AtPlan Z G) (key₀ : TableKey)
    (h0 : key₀.item = 0)
    (hf : key₀.fits (Key.tailPublic G.k noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds) (hR : dryKey G.k key₀ = some R) (C : CK) (a : ℕ)
    (hok : okAt a (some R) = true) (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (sb : ℕ) (hsb : sb = G.k.oneTime.given.plan.salt)
    (hsalts : saltsFit sb (Three.Whole.of R.1 R.2.1 R.2.2) = true) (cfg : ByteArray)
    (tF : FrontMsg (List E)) (tJ : JoinMsg (List E) ByteArray) (t3 : ByteArray)
    (silent : Xi → FrontMsg (List E) → JoinMsg (List E) ByteArray → ByteArray → Bool)
    (run : Xi → View → View → View → Bool) :
    ∀ F o id table further d, o.id = some id → o.bits = 128 → PortYesAt F id table further →
      servedAt Z (stmOf F o) = true → rdKey (stmOf F o) F.key = some (table, d) →
      (∃ π, tyKeyAt C a (dataAt a (dryKey G.k key₀)) tF tJ t3 silent run sb cfg (table, d) =
        some π) ∨ keyCollidesAt F o table further := by
  intro F o id table further d _ _ h hs hd
  obtain ⟨e1, e2, e3, -⟩ := (servedAt_pins Z (stmOf F o)).1 hs
  obtain ⟨pl, hpl, hk, -, -⟩ := hG
  have hpl : Model.Verify.planned F.pol F.KL (some F.lay) = .ok pl := by
    have e1 : F.pol = Z.pol := e1
    have e2 : F.lay = Z.lay := e2
    have e3 : F.KL = Z.KL := e3
    rw [e1, e2, e3]
    exact hpl
  have hW : dataAt a (dryKey G.k key₀) = Three.Whole.of R.1 R.2.1 R.2.2 := by
    rw [hR]
    exact if_pos hok
  rw [hk] at hf hR hsb
  subst hsb
  refine (port_key_or F o id table further h pl hpl d hd key₀ h0 hf R hR C a cfg hok hB hsalts).imp
    (fun hr => Option.isSome_iff_exists.1 ?_) fun c => c
  unfold tyKeyAt
  rw [typeFile_isSome, hW]
  exact hr

/-! ## The full size -/

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X) (E : Coding A) (G : FilesParameters X RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) G).Provers)

/-- The typing at the full size's own letters, typed as Test's string of the three files' object.
The statement is not read. -/
def tyKeyFull (sb : ℕ) (cfg : ByteArray) (_ : UserStm) (td : Params.TableName × ChainsData) :
    Option (OneProtocolProof 256 (batTC (LrG (restFullAt A E G P)) (threeProtocolsFromDryRunAtFullSize A (Flat.relationsAndEncodingOfClaims A E) G).annT)) :=
  tyKeyAt (ckP .two) frS.P.T.a
    (dataAt frS.P.T.a (dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀))) (front₀ G.rec₀)
    (join₀ G.rec₀) ByteArray.empty silK (runKFull G) sb cfg td

/-- The field `types` of `KeyFive` [not in this library], at `rdKey`, `tyKeyFull` and
`keyCollidesAt`. -/
theorem types_keyFull {Z : Pub} (hG : AtPlan Z G)
    (hf : (keyOf (fun β : NZ => β.val) G.rec₀).fits
      (Key.tailPublic G.k noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds) (hR : dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀) = some R)
    (hok : okAt frS.P.T.a (some R) = true)
    (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true) (sb : ℕ)
    (hsb : sb = G.k.oneTime.given.plan.salt)
    (hsalts : saltsFit sb (Three.Whole.of R.1 R.2.1 R.2.2) = true) (cfg : ByteArray) :
    ∀ F o id table further d, o.id = some id → o.bits = 128 → PortYesAt F id table further →
      servedAt Z (stmOf F o) = true → rdKey (stmOf F o) F.key = some (table, d) →
      (∃ π, tyKeyFull A E G P sb cfg (stmOf F o) (table, d) = some π) ∨
        keyCollidesAt F o table further :=
  types_key hG _ (keyOf_item _ _) hf R hR (ckP .two) frS.P.T.a hok hB sb hsb hsalts cfg
    (front₀ G.rec₀) (join₀ G.rec₀) ByteArray.empty silK (runKFull G)

end

/-! ## The small example -/

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X) (E : Coding A) (G : FilesParameters X RecSmall)
  (P : (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).Provers)

/-- The typing at the small example's own letters, typed as Test's string of the three files'
object. The statement is not read. -/
def tyKeySmall (sb : ℕ) (cfg : ByteArray) (_ : UserStm) (td : Params.TableName × ChainsData) :
    Option
      (OneProtocolProof 256 (batTC (LrG (restSmallAt A E G P)) (threeProtocolsFromDryRunAtSmallSize A (Flat.relationsAndEncodingOfClaims A E) G).annT)) :=
  tyKeyAt (ckP .two) srS.P.T.a
    (dataAt srS.P.T.a (dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀))) (front₀ G.rec₀)
    (join₀ G.rec₀) ByteArray.empty silK (runKSmall G) sb cfg td

/-- The field `types` of `KeyFive` [not in this library], at `rdKey`, `tyKeySmall` and
`keyCollidesAt`. -/
theorem types_keySmall {Z : Pub} (hG : AtPlan Z G)
    (hf : (keyOf (fun β : NZ => β.val) G.rec₀).fits
      (Key.tailPublic G.k noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds) (hR : dryKey G.k (keyOf (fun β : NZ => β.val) G.rec₀) = some R)
    (hok : okAt srS.P.T.a (some R) = true)
    (hB : oneShapeB (Three.Whole.of R.1 R.2.1 R.2.2) = true) (sb : ℕ)
    (hsb : sb = G.k.oneTime.given.plan.salt)
    (hsalts : saltsFit sb (Three.Whole.of R.1 R.2.1 R.2.2) = true) (cfg : ByteArray) :
    ∀ F o id table further d, o.id = some id → o.bits = 128 → PortYesAt F id table further →
      servedAt Z (stmOf F o) = true → rdKey (stmOf F o) F.key = some (table, d) →
      (∃ π, tyKeySmall A E G P sb cfg (stmOf F o) (table, d) = some π) ∨
        keyCollidesAt F o table further :=
  types_key hG _ (keyOf_item _ _) hf R hR (ckP .two) srS.P.T.a hok hB sb hsb hsalts cfg
    (front₀ G.rec₀) (join₀ G.rec₀) ByteArray.empty silK (runKSmall G)

end

end OnBytes.K.Arm
