-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/KeyLink/KeyPreOwn.lean: the reading of the key file through the oracle (`preT`,
OnBytes/Tie/Decl/KeyPre.lean) with three of its letters written out: the parameters are the
planner's plain steps' at a given digest; the table holds four digests at the four public strings;
and, where the verifier program has said yes, at the oracle's own four digests, its value.

The key file's like of Johnson/Top/ProofPreOwn.lean [not in this library], whose names and proofs it
follows.

Main names:
  `PubK`: four public digests: the public files'; the key file's three chains' parameter bytes'.
  `tabK sC sP rest d k`: the table: d's four digests at the four strings; `rest` elsewhere. sC: the
    string of the call that hashes the three public files; sP: from parameter bytes to the string of
    the call that hashes them: two letters here.
  `ksPlanned pol KL lay c`: the key's chains' parameters of `plannedAt`
    (OnBytes/Tie/ChainsAtCfg.lean) at the digest c.
  `ownK`, `tabK_own`: the answers of the oracle made from Lean's BLAKE2b at the four strings; the
    table at these, with that oracle elsewhere, is that oracle: at every string.
  `preT_yes`: at files to which the program has said yes: at `ownK` and that table, at every Pt:
    `(preT …).det oBits = ty table d.r d.salt d.path`, and `d.copy = 0`; d the fixed reading.

Premises of `preT_yes` beside the yes, the planner's answer and the fixed reading: three on a key
key₀, which is a letter (h0: its item is 0; hf: it fits the index of the planner's chains; hR: the
key file's dry run at it returns the three lists R); two tests on public data (`okAt`, `shapesFit`);
hc: that oracle's answer at sC is the program's digest of the public files. hc is a premise: it is
not shown here at any sC. At the string `s0Of pol lay KL` (Johnson/Top/Pub/PubStrings.lean)
`oBits_cfg` (Johnson/Top/Pub/PubMany.lean) has that oracle's answer as `bytesToDig` of that digest,
under a bound on the length of what is hashed; that file is not imported here, and the bound is not
shown here of any files.

Which hash. The planner's plain steps are `plannedAt` (OnBytes/Tie/ChainsAtCfg.lean). The format's
second hash function, a fixed function, is called in them, at every c alike: the head of
OnBytes/Tie/PlanAtDigest.lean says where.

Limits: one direction, at one fixed function: there the public algorithm returns that function's
answers, so d is `ownK`; that it does is not shown here. `preT_yes` holds at EVERY sC with hc and at
EVERY sP: with that oracle as `rest` the table is the oracle at every string: so it is no witness
that the four strings are the right ones. Nothing at a drawn function. Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.KeyLink.KeyPrePort
import OnBytes.Tie.ChainsAtCfg

set_option autoImplicit false

noncomputable section

namespace OnBytes.KeyLink

open _root_.Run _root_.Run.PQ OnBytes.Tie OnBytes.Maker OnBytes.Maker.Page
open OnBytes.Proof OnBytes.TieK
open OnBytes.Model.Verify (planned configuration)
open OnBytes.Params (Rounds KeyChains TableName)
open _root_.Iop (Dig)

/-- The four public digests of a key file's reading. -/
structure PubK where
  cfg : Dig 256
  oneTime : Dig 256
  shared : Dig 256
  second : Dig 256

/-- The table: d's four digests at the four strings; `rest` elsewhere. Where two of the four strings
are one, the earlier in this order stands. -/
def tabK (sC : List Bool) (sP : ByteArray → List Bool) (rest : List Bool → Dig 256) (d : PubK)
    (k : KeyChains) : List Bool → Dig 256 := fun s =>
  if s = sC then d.cfg
  else if s = sP k.oneTime.given.bytes then d.oneTime
  else if s = sP k.shared.given.bytes then d.shared
  else if s = sP k.second.given.bytes then d.second
  else rest s

/-- The key's chains' parameters of the planner's plain steps at the digest c. -/
def ksPlanned (pol KL lay c : ByteArray) : Option KeyChains :=
  match plannedAt pol KL (some lay) c with
  | .error _ => none
  | .ok p => some p.chains.key

/-- The oracle's own answers at the four public strings. -/
def ownK (sC : List Bool) (sP : ByteArray → List Bool) (k : KeyChains) : PubK :=
  ⟨oBits () sC, oBits () (sP k.oneTime.given.bytes), oBits () (sP k.shared.given.bytes),
    oBits () (sP k.second.given.bytes)⟩

/-- The table at these digests, with that oracle elsewhere, is that oracle. -/
theorem tabK_own (sC : List Bool) (sP : ByteArray → List Bool) (k : KeyChains) (x : List Bool) :
    tabK sC sP (oBits ()) (ownK sC sP k) k x = oBits () x := by
  unfold tabK ownK
  split
  · rename_i e; rw [e]
  · split
    · rename_i e; rw [e]
    · split
      · rename_i e; rw [e]
      · split
        · rename_i e; rw [e]
        · rfl

/-- **From the program's yes, at the oracle's own digests.** -/
theorem preT_yes {Out : Type} (Pt : List Bool → Prop) [DecidablePred Pt] (sC : List Bool)
    (sP : ByteArray → List Bool)
    (ty : TableName → TailRead → ByteArray → List ByteArray → Option Out)
    (F : K.Files) (id : String) (table further : TableName)
    (h : K.PortYesAt F id table further) (p : Model.Verify.Planned)
    (hp : planned F.pol F.KL (some F.lay) = .ok p) (d : ChainsData)
    (hd : readKeyChains F.pol F.lay F.KL F.key = some (table, d)) (key₀ : TableKey)
    (h0 : key₀.item = 0)
    (hf : key₀.fits (Key.tailPublic p.chains.key noTable).lin.fold.index = true)
    (R : Rounds × Rounds × Rounds) (hR : dryKey p.chains.key key₀ = some R) (a : ℕ)
    (hok : okAt a (some R) = true) (hsh : shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true)
    (hc : digToBytes (oBits () sC) = configuration F.pol F.lay F.KL) :
    (preT Pt (tabK sC sP (oBits ())) PubK.cfg (ksPlanned F.pol F.KL F.lay) (asmSlot ty)
      (ownK sC sP p.chains.key) F.key).det oBits = ty table d.r d.salt d.path ∧ d.copy = 0 := by
  refine preT_port_slot Pt _ PubK.cfg _ ty F id table further h p hp d hd key₀ h0 hf R hR a hok hsh
    _ ?_ fun x _ => tabK_own _ _ _ x
  show ksPlanned F.pol F.KL F.lay (digToBytes (oBits () sC)) = _
  rw [hc]
  unfold ksPlanned
  have e : plannedAt F.pol F.KL (some F.lay) (configuration F.pol F.lay F.KL) = .ok p :=
    (planned_eq F.pol F.KL (some F.lay)).symm.trans hp
  rw [e]

end OnBytes.KeyLink
