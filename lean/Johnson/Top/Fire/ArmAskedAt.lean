-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/ArmAskedAt.lean: the reading that asks the oracle (`AskReader`,
Johnson/Top/Fire/ArmAsked.lean) at a ground G of the entry's link and three public files Z; that it
shares the arm's two constants; that it agrees with the tie's reading; and the tie and the bound,
both said of the one term.

Main names (namespace `OnBytes.K.Fire`):
  `zOf r recP strP`: what the arm takes in, as a plain function of what the asking half returns
    (`AskedE`, OnBytes/Tie/EntryAsked.lean): the two roots; recP of each table and its seeds; strP
    of what was read of the chain.
  `readerArm G Z r recP strP`: the key file's table by a plain parse (`keyAt`); the asking half
    (`typedER`): a twin of the program's reading of an entry file, and both tables' seeds, with
    the hashes asked of the oracle; then `zOf`. ITS ONE QUESTION AT THE STRING OF THE PARAMETER
    BYTES IS ANSWERED WITH THE ARM'S OWN CONSTANT AND NOT ASKED (`pinOn`, OnBytes/Slice/AtSet.lean).
    It asks at most `typedT` strings (OnBytes/Tie/EntryAskedCost.lean).
  `readerArm_pd`: under every oracle, the parameters' digest in what the asking half returns is
    `EntryRunTop.pdOf (entryXD G Z.digest)`: the digest in the arm's coding
    (`mAt`, Johnson/Top/TieArmAt.lean).
  `pd_oBits`: that constant is the value of the oracle made from the format's hash at that string.
  `readerArm_agrees`: `Agrees`, from two equations: hrec, hent.
  `pair_asked`: `ZeroSays` and `SoundSays` of `readerArm`, from `TieSays` and `BoundSays`.

Why the pin. The arm's coding holds the parameters' digest as a value of the format's hash. The
asking half asks the oracle for that digest (`asked_pd`, OnBytes/K/Oracle/AskedPd.lean). Unpinned,
under a random function the reading's chain would start from the function's answer and the arm's
from the format's hash: a file would have to pass two chains of verifier messages drawn apart, the
one term would say yes all but never, and `SoundSays` would say next to nothing (by reading; no
theorem). The reading alone is pinned; the arm's term is as in ArmPair.lean.

Limits, beside those of ArmAsked.lean.
  1. TWO CONSTANTS INSIDE THE ONE TERM ARE VALUES OF THE FORMAT'S HASH ON Z's PUBLIC FILES:
     `Z.digest` and `pdOf`. In `SoundSays` they are constants, fixed before the function is drawn,
     and the bound holds whatever they are. In `ZeroSays` they are the hash's own values. So they
     are fixed before the run, not before the function, and the step from a random function to the
     fixed one has to take that too as given. OnBytes/K/Oracle/ArmO.lean, on another checker, has in
     their place the oracle's own values at the public strings.
  2. The asking half reads the entry file by the text over a monad of the program's reader
     (`M.Entry.read`, OnBytes/ChecksWithHashAsArgument/M/Entry/File.lean), at the asking monad. Which text the
     program runs follows from what OnBytes/Main.lean calls: either the text of verify-on-bytes
     (`Entry.read`, OnBytes/Entry/File.lean), of which that is a twin, or, on a model's files, that
     same definition at the identity monad and the program's own hash. The program does not call the
     asking half or the reading. That the reading asks what the program hashes is not claimed. How
     the twin and that text are tied: the head of OnBytes/K/Oracle/ReaderAt.lean.
  3. The key file's table is parsed, no more: that dropping `Key.readTable`'s three tests gives a
     prover nothing is no theorem (`keyAt`, OnBytes/Tie/LinkPlain.lean).
  4. hrec and hent are premises here. That an input of the arm meets them is shown at no input in
     this file.
  For proofs only; no program imports this file.

-/
import Johnson.Top.Fire.ArmAsked
import OnBytes.K.Oracle.AskedAt
import OnBytes.K.Oracle.AskedPd
import OnBytes.Slice.OverSelf
import OnBytes.Tie.EntryAskedCost

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.K.Fire

open Rom
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig oBits)
open TypedOracleCompiler.Slice OnBytes.Tie OnBytes.K.Left OnBytes.K.Oracle
open OnBytes.Slice (pinOn det_pinOn det_pinOn_of_eq queryBound_pinOn noCoin_pinOn s0Of)

/-- The parameters' digest by the format's hash is the value, at the string of that call, of the
oracle made from the format's hash. -/
theorem pd_oBits (p : ByteArray) (hb : p.size ≤ 2 ^ 32 - 144) :
    bytesToDig (_root_.Fmt.formatHash 169 0 1 _root_.Fmt.zero32 p) = oBits () (s0Of p) := by
  have h := OnBytes.Slice.Shapes.call169_oBits 1 (by decide) p hb
  have h2 := congrArg bytesToDig h
  unfold _root_.Run.oB at h2
  rw [_root_.Run.TieTree.bytes_dig] at h2
  exact h2.symm

variable (G : EntryGround) (Z : Pub) (r : ArmIn)
  (recP : Params.TableName → List (List E × E) → r.L.Rec)
  (strP : _root_.Fmt.ChainOut → Option (OneProtocolProof 256 (batLC r.L r.aL)))

/-- What the arm takes in, as a plain function of what the asking half returns. -/
def zOf (a : AskedE) : Option (OutLA 256 r.L r.aL) :=
  (strP a.out).map fun π =>
    (bytesToDig a.first.root, bytesToDig a.further.root, recP a.first a.l0, recP a.further a.l1, π)

/-- The reading at a ground and three public files: the key file's table by a plain parse; the
asking half; then `zOf`. Its one question at the string of the parameter bytes is answered with the
arm's own constant, and not asked. -/
def readerArm : AskReader r (typedT G.q.link.table G.rs) where
  rd d := pinOn {s0Of (entryXD G Z.digest).base.params}
    (fun _ => EntryRunTop.pdOf (entryXD G Z.digest))
    (typedER (zOf r recP strP) (linkAtCfg G.q Z.digest)
      (keyAt G.q.link.table Z.digest d.key).2.2 d.ent)
  noCoin _ := noCoin_pinOn _ _ _ (G.typedER_asks _ _ _ _).1
  queries _ := queryBound_pinOn _ _ _ _ (G.typedER_asks _ _ _ _).2

/-- Reading and arm have one parameters' digest, under every oracle: in what the asking half returns
under g with the pin laid over, the digest is the arm's own constant. -/
theorem readerArm_pd (g : Fam (rom 256)) (first : Params.TableName) (ent : ByteArray) (a : AskedE)
    (h : askedAt (_root_.Run.oB (OnBytes.Slice.over {s0Of (entryXD G Z.digest).base.params}
      (fun _ => EntryRunTop.pdOf (entryXD G Z.digest)) g ())) (linkAtCfg G.q Z.digest) first ent =
        some a) :
    bytesToDig a.out.pd = EntryRunTop.pdOf (entryXD G Z.digest) := by
  rw [asked_pd _ _ _ _ _ h]
  unfold _root_.Run.oB
  rw [_root_.Run.TieTree.bytes_dig]
  exact OnBytes.Slice.over_mem _ g (Finset.mem_singleton.2 rfl)

/-- At the oracle made from the hash the reading makes of a run's files what the tie's reading makes
of them. hrec, hent: the arm's records and the tie's reading of the entry file are made by recP and
strP of the program's own seeds and of what the program's reader read. -/
theorem readerArm_agrees (hA : (G.q.link.table.answers == 0) = false) (hZ : G.SaysLines Z.pol)
    (hok : TypedOracleCompiler.Run.PQ.ok (entryXD G Z.digest).base = true) (R : Reading5 r.shape)
    (hrec : ∀ x t, r.recOf x t =
      (seedsUnder recordSeeds (linkAtCfg G.q Z.digest) t).map (recP t))
    (hent : ∀ x key ent, R.ent x key ent =
      match Entry.read (linkAtCfg G.q Z.digest) (keyAt G.q.link.table Z.digest key).2.2 ent with
      | .ok rr => (strP rr.chain.out).map fun π => (rr.further, π)
      | .error _ => none) :
    (readerArm G Z r recP strP).Agrees Z R := by
  intro F id table further o c cj πL hp e1 e2 e3 hc hcj he
  have hl : G.SaysLines F.pol := e1 ▸ hZ
  have hd : Params.configurationDigest [F.pol, F.lay, F.KL] = Z.digest := by
    rw [e1, e2, e3]
    rfl
  obtain ⟨rr, l0, l1, hr, hf, a0, a1, ea⟩ := asked_port G hA hp hl
  rw [hd] at hr a0 a1 ea
  have ht := table_at G hp hl Z.digest
  rw [hrec, a0] at hc
  rw [hrec, a1] at hcj
  rw [hent, ht, hr] at he
  obtain ⟨π, hπ, e⟩ := Option.map_eq_some_iff.1 he
  obtain rfl : π = πL := congrArg Prod.snd e
  obtain rfl := Option.some.inj hc
  obtain rfl := Option.some.inj hcj
  show (pinOn _ _ (typedER (zOf r recP strP) (linkAtCfg G.q Z.digest)
    (keyAt G.q.link.table Z.digest F.key).2.2 F.ent)).det oBits = _
  rw [det_pinOn_of_eq _ _ _ (fun x hx => by
      rw [Finset.mem_singleton.1 hx]
      exact pd_oBits _ (params_le_of_ok _ hok)),
    typedER_det, ← askedE_det, ht, ea]
  show zOf r recP strP ⟨table, further, l0, l1, rr.chain.out⟩ = _
  unfold zOf
  rw [hπ]
  rfl

/-- The tie and the bound, both said of the one term, at every input of the arm whose records and
whose reading of the entry file are made by recP and strP. -/
theorem pair_asked (hA : (G.q.link.table.answers == 0) = false) (hZ : G.SaysLines Z.pol)
    (hok : TypedOracleCompiler.Run.PQ.ok (entryXD G Z.digest).base = true) (R : Reading5 r.shape)
    (hrec : ∀ x t, r.recOf x t =
      (seedsUnder recordSeeds (linkAtCfg G.q Z.digest) t).map (recP t))
    (hent : ∀ x key ent, R.ent x key ent =
      match Entry.read (linkAtCfg G.q Z.digest) (keyAt G.q.link.table Z.digest key).2.2 ent with
      | .ok rr => (strP rr.chain.out).map fun π => (rr.further, π)
      | .error _ => none)
    {εs : ENNReal} (h : TieSays r Z R ∧ BoundSays r εs) :
    ZeroSays (readerArm G Z r recP strP) Z ∧ SoundSays (readerArm G Z r recP strP) εs :=
  ⟨zero_files _ h.1 (readerArm_agrees G Z r recP strP hA hZ hok R hrec hent), bound_files _ h.2⟩

end OnBytes.K.Fire
