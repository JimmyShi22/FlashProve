-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/KeyLink/KeyPrePort.lean: where the verifier program has said yes, the reading of the key
file through the oracle (`preT`, OnBytes/Tie/Decl/KeyPre.lean), at the oracle made from Lean's
BLAKE2b, makes the plain map's value at what the fixed reading of the key file has read.

OnBytes/Tie/KeyAsked.lean leaves one premise, `KeyTwinAtO`: that the twin of the program's reader,
at the hash over the format's oracle, returns what the program's reader returns.
OnBytes/Maker/Page/TwinKey.lean (`twinKey_returns_O`) has that from the record of a reading
(`ThreeRead`), the bounds `SmallThree` and 32 bytes of the table's root. Here the two are joined,
and the bounds are taken from the program's yes and two tests on public data (`small_port_key`,
OnBytes/Maker/Page/SmallOfP.lean).

Main names:
  `keyTwinAtO_of_read`: `KeyTwinAtO`, from one record of a reading with its bounds and the root's 32
    bytes. Every reading that the program's reader returns is that record's (`threeRead_same`).
  `preT_port`: at files to which the program has said yes; p: the planner's answer; d: the fixed
    reading (`readKeyChains`); `ksAt` returns p's key chains at the digest in dd; the table holds
    `oBits`' own values at the public strings; two tests at the rounds R of the dry runs at a key
    key₀, a letter whose item is 0 (h0) and which fits the index of p's key chains (hf): `okAt`,
    `shapesFit`. Then `(preT … dd F.key).det oBits = asm p.chains.key F.key table d.r`.
  `asmSlot ty`, `preT_port_slot`: at the plain map that cuts the binding tree's leaf's salt and
    siblings out of the file and then applies ty: the value is `ty table d.r d.salt d.path`: all
    that a typing of the fixed reading takes of it, but for its number of a copy, which is 0.

Limits: one direction, at one fixed function. The two tests are not shown here. That `ksAt` is the
planner's plain steps, and that the table's premise can be met, is not shown here. asm is a letter.
Nothing on a drawn function. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.Decl.KeyPre
import OnBytes.Maker.Page.TwinKey
import OnBytes.Maker.Page.SmallOfP

set_option autoImplicit false

namespace OnBytes.KeyLink

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker OnBytes.Maker.Page
open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds KeyChains TableName)
open _root_.Iop (Dig)

/-- **The named premise, from one record of a reading.** -/
theorem keyTwinAtO_of_read {k : KeyChains} {table : TableName} {file : ByteArray} {j : ℕ}
    {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
    {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃ : Rounds} {S₃ : Fmt.SpecX}
    (hS : k.oneTime.describe table R₁ = some S₁)
    (T : ThreeRead (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime) file j
      R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃ S₃)
    (hsm : SmallThree S₁ S₂ S₃ file) (hr : table.root.size = 32) :
    KeyTwinAtO k table file j := by
  intro r' h'
  obtain ⟨Q₁, d0, Z₁, z1, z2, Q₂, d2, Z₂, Q₃, Z₃, hZ, T'⟩ :=
    threeRead_of_readKey k table file j r' h'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (T.first_dry.symm.trans T'.first_dry))
  obtain rfl : S₁ = Z₁ := Option.some.inj (hS.symm.trans hZ)
  obtain ⟨-, -, rfl, -, -, -, -, -, -, -⟩ := threeRead_same T T'
  exact twinKey_returns_O k table file j hS T hsm hr

variable {D Out : Type} (Pt : List Bool → Prop) [DecidablePred Pt]
  (tab : D → KeyChains → List Bool → Dig 256) (cfgOf : D → Dig 256)
  (ksAt : ByteArray → Option KeyChains)
  (asm : KeyChains → ByteArray → TableName → TailRead → Option Out)

/-- **Where the program has said yes.** -/
theorem preT_port (F : K.Files) (id : String) (table further : TableName)
    (h : K.PortYesAt F id table further) (p : Model.Verify.Planned)
    (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p) (d : ChainsData)
    (hd : readKeyChains F.pol F.lay F.KL F.key = some (table, d)) (key₀ : TableKey)
    (h0 : key₀.item = 0)
    (hf : key₀.fits (Key.tailPublic p.chains.key noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds) (hR : dryKey p.chains.key key₀ = some R) (a : ℕ)
    (hok : okAt a (some R) = true) (hsh : shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (dd : D) (hk : ksAt (digToBytes (cfgOf dd)) = some p.chains.key)
    (hT : ∀ x, Pt x → tab dd p.chains.key x = oBits () x) :
    (preT Pt tab cfgOf ksAt asm dd F.key).det oBits = asm p.chains.key F.key table d.r := by
  have ho := port_key_chains F id table further h
  obtain ⟨p', j, d', real, real2, hp', ht, hd', hS, T, -, -⟩ := readKeyChains_of F table ho
  obtain rfl : p = p' := Except.ok.inj (hp.symm.trans hp')
  obtain rfl : d = d' := congrArg Prod.snd (Option.some.inj (hd.symm.trans hd'))
  have hsm := small_port_key F id table further h p hp d hd key₀ h0 hf R hR a hok hsh
  have hh : headAt ksAt (digToBytes (cfgOf dd)) F.key = some (p.chains.key, table, j) := by
    unfold headAt
    rw [hk]
    show (match Key.readTable p.chains.key.oneTime.lin.fold.index
      p.chains.key.oneTime.given.cfg F.key with
      | .error _ => none
      | .ok x => some (p.chains.key, x.1, x.2)) = _
    rw [ht]
  exact preT_twin Pt tab cfgOf ksAt asm dd F.key hh hT d.r
    (twinKey_returns_O p.chains.key table F.key j hS T.toRead hsm (Tie.keyTable_root ht))

/-- A plain map from what was read: the salt and the siblings of the binding tree's leaf, which the
reading hashes and does not keep, are cut out of the file (`slotBytes`,
OnBytes/TieK/ReadThree.lean); then ty. -/
def asmSlot (ty : TableName → TailRead → ByteArray → List ByteArray → Option Out) (k : KeyChains)
    (file : ByteArray) (t : TableName) (r : TailRead) : Option Out :=
  (slotBytes (Key.tailPublic k t).binding file r.first.next).bind fun sp => ty t r sp.1 sp.2

/-- **Where the program has said yes, at that plain map**: ty at the table, the three chains as
read, the salt and the siblings of the fixed reading; and the fixed reading's number of a copy is
0. -/
theorem preT_port_slot (ty : TableName → TailRead → ByteArray → List ByteArray → Option Out)
    (F : K.Files) (id : String) (table further : TableName)
    (h : K.PortYesAt F id table further) (p : Model.Verify.Planned)
    (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p) (d : ChainsData)
    (hd : readKeyChains F.pol F.lay F.KL F.key = some (table, d)) (key₀ : TableKey)
    (h0 : key₀.item = 0)
    (hf : key₀.fits (Key.tailPublic p.chains.key noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds) (hR : dryKey p.chains.key key₀ = some R) (a : ℕ)
    (hok : okAt a (some R) = true) (hsh : shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (dd : D) (hk : ksAt (digToBytes (cfgOf dd)) = some p.chains.key)
    (hT : ∀ x, Pt x → tab dd p.chains.key x = oBits () x) :
    (preT Pt tab cfgOf ksAt (asmSlot ty) dd F.key).det oBits = ty table d.r d.salt d.path ∧
      d.copy = 0 := by
  have e := preT_port Pt tab cfgOf ksAt (asmSlot ty) F id table further h p hp d hd key₀ h0 hf R hR
    a hok hsh dd hk hT
  have ho := port_key_chains F id table further h
  obtain ⟨p', j, d', real, real2, hp', -, hd', -, -, sl, hc⟩ := readKeyChains_of F table ho
  obtain rfl : p = p' := Except.ok.inj (hp.symm.trans hp')
  obtain rfl : d = d' := congrArg Prod.snd (Option.some.inj (hd.symm.trans hd'))
  refine ⟨?_, hc⟩
  rw [e]
  unfold asmSlot
  rw [sl.bytes]
  rfl

end OnBytes.KeyLink
