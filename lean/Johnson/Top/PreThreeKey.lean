-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/PreThreeKey.lean: the key file's part with its questions laid in: the key file's reader
at the planner's plain steps, with its hash asked, pinned at the strings of the calls on its three
chains' parameter bytes and nowhere else. The table that pins it holds three of the public digests
and nothing else. What the part makes of what it has read is a letter (ty).

`preTQ` (Johnson/Top/KeyPin.lean) is the key file's part with four letters: the pin's three digests,
the digest of the public files, the parameters and the plain map. Here the parameters are the
planner's plain steps' (`ksPlanned`, OnBytes/KeyLink/KeyPreOwn.lean) and the four digests are four
of the eight that `pub8` draws (`key8`: three; `cfg8`: one; Johnson/Top/PreThreePub.lean). The
definitions follow texts written for this file by the writers of
Johnson/Top/PreThreeAt.lean [not in this library].

NOT HERE, so that this file stands on few files: the key's reading `headAt8` with its number
`cHead`, the bound on the three arms `three_arms_keySees_all`, the three laws under the program's
yes (`pubK8_yes`, `keyAt8_yes`, `headAt8_yes`) and their tools `pubK8`, `preTQ_congr`: they stand
over this file, in Johnson/Top/PreThreeKeyAll.lean [not in this library]. No name of the oracle made
from the format's hash and no yes of a program stands in this file.

Main names:
  `asmSlotC ty`, `keyAt8 pol KL lay ty`: the key file's part. ty: the typing of a reading, a letter.
    It sees the digest of the public files that stands in the chains at which the file is read:
    behind `pub8` under a family g these are the plain steps' chains at g's own answer, so it moves
    with g. That it is that answer is a law on the plain steps; it is not shown here.
  `cKey p₀ t₀`: the number that is meant to bound the key file's part's queries, at a reference
    plan p₀. That it does is not shown here: `keyTree_asks` (Johnson/Top/KeyTree.lean) and
    `keyRun_asks` (Johnson/Top/KeyRun.lean) show it behind `pub8`, under three premises: the
    planner's text returns p₀ at a string of 32 bytes, and each of p₀'s seven strings of parameter
    bytes has fewer than 2 ^ 64 bytes. A yes of the test `shortB` gives that (`short_of_test`,
    OnBytes/Tie/PlanAtDigest.lean), a test that the verifier program does not run; each of three
    files' yeses gives it for one of the seven, two of them at the program's own plan alone, so not
    at a p₀ that the planner's text returns at another string (the head of
    OnBytes/Tie/ChainsAtCfg.lean). The number is not evaluated.
  `keyAt8_unseen`: under EVERY family g of oracle functions, behind `pub8`: the value of the key
    file's part is that of the reading without a pin (`partKU`, Johnson/Top/PreThreeKeyOwn.lean):
    the three digests laid in are g's own answers at the pinned strings.
What the definitions beneath hold (the planner's plain steps, the parse of a table, the asking
reader) is not gone through here.
Limits: A fixed hash, the format's earlier one, stands in these terms beside the drawn function: the
planner's text (plannedAt) hashes with it at places that read the three public files alone (the head
of OnBytes/K/TopG.lean counts seven): constants where the three public files are fixed before g is
drawn; here they are letters beside g (a reader's count at `publicOf`'s text; no theorem). The
typing ty stays a letter. Nothing on what the part returns. No bound stands here, and no yes of a
program. The limits of Johnson/Top/KeyPin.lean stand: two of the three strings may be one string.
Nothing on soundness.
`set_option maxRecDepth`: whether the default would do in this file has not been tried.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.PreThreeKeyOwn
import OnBytes.KeyLink.KeyCountPlanned
import OnBytes.KeyLink.KeyPreOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace TypedOracleCompiler.Compile.Batch.Cms
open OnBytes _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

open scoped ENNReal
open OnBytes.Slice
open OnBytes.K.Arm.Pub (D8 pub8 cfg8 key8 s0Of partKU preTQ_unseen_pub)
open OnBytes.KeyLink (ksPlanned asmSlot keyCount)
open OnBytes.Tie (preTQ plannedAt)
open _root_.Run (digToBytes)

variable {I X : Type} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {W : QueryLayout 256 (typedOracleCarrier L Bd aT aL)}

/-- The plain map behind the key file's reader: `asmSlot` (OnBytes/KeyLink/KeyPrePort.lean) at a
typing that sees the digest of the public files which stands in the chains at which the file is
read. -/
def asmSlotC {Out : Type}
    (ty : ByteArray → Params.TableName → OnBytes.Proof.TailRead → ByteArray → List ByteArray →
      Option Out) (k : Params.KeyChains) :
    ByteArray → Params.TableName → OnBytes.Proof.TailRead → Option Out :=
  asmSlot (ty k.oneTime.given.cfg) k

/-- **The key file's part.** -/
def keyAt8 {Out : Type} (pol KL lay : ByteArray)
    (ty : ByteArray → Params.TableName → OnBytes.Proof.TailRead → ByteArray → List ByteArray →
      Option Out) : D8 → ByteArray → OComp (rom 256) (Option Out) :=
  preTQ key8 cfg8 (ksPlanned pol KL lay) (asmSlotC ty)

/-- The key file's part's number, at a reference. -/
def cKey (p₀ : OnBytes.Model.Verify.Planned) (t₀ : Params.TableName) : ℕ :=
  keyCount p₀.chains.key t₀

/-- **Under every family of oracle functions, behind the public algorithm, the pin in the key file's
part is not seen.** -/
theorem keyAt8_unseen {Out : Type} (G : OnBytes.Tie.EntryGround) (pol KL lay : ByteArray)
    (g : Fam (rom 256))
    (ty : ByteArray → Params.TableName → OnBytes.Proof.TailRead → ByteArray → List ByteArray →
      Option Out)
    (uK : ByteArray) :
    (keyAt8 pol KL lay ty ((pub8 G pol KL lay).det g) uK).det g =
      (partKU (ksPlanned pol KL lay) (asmSlotC ty) (digToBytes (g () (s0Of pol lay KL))) uK).det
        g :=
  preTQ_unseen_pub G pol KL lay g (ksPlanned pol KL lay)
    (fun c k hk => by
      unfold ksPlanned at hk
      cases hq : plannedAt pol KL (some lay) c with
      | error e =>
        rw [hq] at hk
        cases hk
      | ok p =>
        rw [hq] at hk
        exact ⟨p, rfl, (Option.some.inj hk).symm⟩)
    (asmSlotC ty) uK

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.keyAt8_unseen
