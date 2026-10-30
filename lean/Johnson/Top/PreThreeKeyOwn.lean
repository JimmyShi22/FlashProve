-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/PreThreeKeyOwn.lean: behind the public algorithm, under EVERY family of oracle
functions, the pin in the term `preTQ` is not seen, if the parameters that it takes at a digest are
those of the planner's plan at that digest. `preTQ` is meant for the key file's part of a reading of
a call's files; no file here lays it in there.

Johnson/Top/KeyPin.lean has the key file's part pinned at three strings (`preTQ`), and
`preTQ_unseen`: where the three digests laid in are g's own answers, its value under g is that of
the unpinned reading. Here the three digests that `pub8` (Johnson/Top/PreThreePub.lean) returns
under g are shown to be g's own. Definitions, statements and proofs.

Main names:
  `key8_own`: where the planner's text returns a plan at g's first answer: `key8` of what `pub8`
    returns under g is g's three answers at the strings of the parameter bytes of that plan's key's
    chains.
  `tab3_key8_own`: so the table of these three holds g's own answers at the three strings.
  `partKU ksAt asm c keyFile`: the key file's part without a pin.
  `preTQ_unseen_pub`: the key file's part at `key8`, `cfg8` has its value, if ksAt gives at a digest
    the key's chains of the planner's plan at that digest.
Limits: ksAt and asm are letters; the premise on ksAt is not shown of any term here. Values under
one g at a time; no probability. Nothing on what the unpinned reading returns. Nothing on soundness.
A fixed hash, the format's earlier one, stands in these statements beside the drawn function: in
`pub8` and in the premises on the plan. The planner's text (`plannedAt`) hashes with it at seven
places, which read the three public files alone (the head of OnBytes/K/TopG.lean counts them):
constants where the three public files are fixed before g is drawn; here they are letters beside g
(a reader's count at `publicOf`'s text; no theorem).
So "every family" is every drawn function for the format's later mode, and "without a pin" means: it
asks the oracle for its hashes of that mode; the digest of the public files is an argument. No file
that the prover names is hashed with the fixed hash in a key file's reading.

-/
import Johnson.Top.PreThreePub
import Johnson.Top.KeyPin

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm.Pub
open Rom
open _root_.Run (digToBytes)
open _root_.Iop (Dig)
open OnBytes.Tie
open OnBytes.Params (TableName KeyChains)
open OnBytes.Proof (TailRead)
open OnBytes.KeyLink (headAt_ks)

variable (G : EntryGround) (pol KL lay : ByteArray) (g : Fam (rom 256))

/-- The key's three answers are g's own. -/
theorem key8_own {p : OnBytes.Model.Verify.Planned}
    (hp : plannedAt pol KL (some lay) (digToBytes (g () (s0Of pol lay KL))) = .ok p) :
    key8 ((pub8 G pol KL lay).det g) =
      (g () (strPar p.chains.key.oneTime.given.bytes), g () (strPar
          p.chains.key.shared.given.bytes),
        g () (strPar p.chains.key.second.given.bytes)) := by
  rw [pub8_det]
  unfold key8 ssOf par7
  rw [hp]
  rfl

/-- The table of these three holds g's own answers at the three strings. -/
theorem tab3_key8_own {p : OnBytes.Model.Verify.Planned}
    (hp : plannedAt pol KL (some lay) (digToBytes (g () (s0Of pol lay KL))) = .ok p) :
    ∀ s ∈ setK p.chains.key, tab3 (key8 ((pub8 G pol KL lay).det g)) p.chains.key s = g () s := by
  intro s hs
  rw [key8_own G pol KL lay g hp]
  unfold tab3
  dsimp only
  split
  · rename_i e
    rw [e]
  · rename_i n1
    split
    · rename_i e
      rw [e]
    · rename_i n2
      rcases mem_setK.1 hs with e | e | e
      · exact absurd e n1
      · exact absurd e n2
      · rw [e]

/-- The key file's part without a pin. -/
def partKU {Out : Type} (ksAt : ByteArray → Option KeyChains)
    (asm : KeyChains → ByteArray → TableName → TailRead → Option Out) (c keyFile : ByteArray) :
    OComp (rom 256) (Option Out) :=
  match headAt ksAt c keyFile with
  | none => .pure none
  | some a => typedKR (asm a.1 keyFile a.2.1) a.1 a.2.1 keyFile a.2.2

/-- **The key file's part: the pin is not seen.** -/
theorem preTQ_unseen_pub {Out : Type} (ksAt : ByteArray → Option KeyChains)
    (hks : ∀ c k, ksAt c = some k → ∃ p, plannedAt pol KL (some lay) c = .ok p ∧ k = p.chains.key)
    (asm : KeyChains → ByteArray → TableName → TailRead → Option Out) (keyFile : ByteArray) :
    (preTQ key8 cfg8 ksAt asm ((pub8 G pol KL lay).det g) keyFile).det g =
      (partKU ksAt asm (digToBytes (g () (s0Of pol lay KL))) keyFile).det g := by
  have hc : cfg8 ((pub8 G pol KL lay).det g) = g () (s0Of pol lay KL) := by
    rw [pub8_det]
    rfl
  cases h : headAt ksAt (digToBytes (g () (s0Of pol lay KL))) keyFile with
  | none =>
    unfold preTQ partKU
    rw [hc, h]
  | some a =>
    obtain ⟨k, t, j⟩ := a
    obtain ⟨p, hp, rfl⟩ := hks _ _ (headAt_ks ksAt h)
    have h' : headAt ksAt (digToBytes (cfg8 ((pub8 G pol KL lay).det g))) keyFile =
        some (p.chains.key, t, j) := by rw [hc]; exact h
    rw [preTQ_unseen key8 cfg8 ksAt asm g _ keyFile h' (tab3_key8_own G pol KL lay g hp)]
    unfold partKU
    rw [h]

end OnBytes.K.Arm.Pub

#print axioms OnBytes.K.Arm.Pub.key8_own
#print axioms OnBytes.K.Arm.Pub.preTQ_unseen_pub
