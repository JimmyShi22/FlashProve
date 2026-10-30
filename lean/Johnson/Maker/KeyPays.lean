-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/KeyPays.lean: what is owed at a key file (`KeyOwes`, Johnson/Maker/LeftAtKey.lean), at
plain data and a run that are made of the public files: five of its rows are paid from what a good
reading gives (OnBytes/Maker/GoodKey.lean).

In LeftAtKey.lean the plain data W and the run are free letters. Here two equations pin them: W is
made of the three lists of rounds R that the dry runs of the program's own blocks state at a fixed
key that fits (`dataOf`; `dryKey`, OnBytes/Maker/Files.lean), and the run is the run of a key file's
reduction (`runOf`; `keyRun`, OnBytes/Maker/PortAccept.lean): the program's own decision on three
views, at the letter `key`. They stay letters with equations, so that a caller can lay another
spelling of the same data.

  `KeyGoodT`        the readings that are spoken of: good readings at which `typeFile` returns, the
                    silent rounds' test says yes and a further condition X of the caller holds
  `KeyDebts`        what is then owed
  `KeyDebts.owes`   it gives `KeyOwes`
  `vTA_of_port'`    the program's yes and `KeyDebts` give the yes of `verifyOfflineProof` at whatever string
                    `typeFile` returns at the fixed reading of the key file, if the silent rounds'
                    test says yes and X holds there

The nine rows of `KeyDebts`. Three tests on the data, which a program can evaluate: `ok`, `shapes`,
`salts`. Two that fix the caller's own letters: `depth` (the wiring's depth), `cfgIs` (cfg). One on
the public files: `cfgSize` (that digest has 32 bytes). One on the letters `key` and `recOf`:
`keyOf` (at the tables of the readings that are spoken of, the key written of the table's record is
the program's key of the table). One on the verifier's messages under g: `draws` (six clauses). And
`rest`: nine hypotheses of `LeftHoles`, in its words.

Beside the record, one premise bounds K from below (no round of the data has more blocks).
Paid against `KeyOwes`: `work`, `places`, `reads`, `run`, `runSize`; `depth` becomes an equation
with the parameters' own number.

Where the statement is idle. Where `typeFile` returns nothing, the silent rounds' test says no or X
fails: also at an honest file, if a letter is laid wrong. A wrong sb is of that kind: nothing pins
sb to the plans' bytes of a salt; the tables' own tests fail at another number, and `typeFile`
returns nothing. X is meant for a test on what was read that a program can evaluate and that holds
no g: the statement is worth what X is worth, and at an X that holds the yes itself it says nothing.

What stays free. All letters stand under one "for all" with the files, so each may be chosen after
seeing them. Pinned by a premise or a row: u, p, k, R, W, the run (at `key`), cfg, the wiring's
depth of a key's tree, pp's two lengths (to sb and sFS). Free: the types; f; K above its bound; a;
sb (it is tested, not pinned); sFS (tied by `saltLen`, a debt within `rest`); `key` and `recOf` but
for `keyOf`; the silent test silK (a test that says yes to everything takes a conjunct out of the
decision); the fixed values tFk, tJk, t3k, tFp, tJp, t3p; what the silent rounds send, pF, pJ, p3,
which are maps from the reading; cA; the proof file's data, silent test and run (DP, silP, runP);
the entry's part eL and its wire record wL; the object's letters Z; the bodies b and their type; the
two other depths; pp beyond its two lengths; g; and of the program's yes: the ID and the further
table.

Who uses what. The sentences at a key file (Johnson/Maker/Page/PortKey.lean and the files over it)
use `dataOf` and `runOf` of this file, through `dataM_eq` and `runM_eq`
(Johnson/Maker/KeyAtMakers.lean). They do not go through `KeyDebts` or `vTA_of_port'`.

Not claimed. Any row of `KeyDebts`. That `typeFile` returns: that is NOT a consequence of the
program's yes (OnBytes/Maker/Page/CollidesBytes.lean names the case). The parameters k are those
that the program plans from the public files, and R is what `dryKey` gives at key₀: equations, which
are premises. key₀ is any key with the item 0 that fits the parameters' shape: by
OnBytes/Maker/FilesFree.lean R does not hang on which. One direction only. Nothing on soundness.


-/
import Johnson.Maker.LeftAtKey
import OnBytes.Maker.GoodKey
import OnBytes.Maker.RunSize

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ OnBytes.RunA TypedOracleCompiler.Joined TypedOracleCompiler.Joined.K Rom
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Compile.Batch.Cms (Bodies typedOracleCarrier cmsTA verifyOfflineProof)
open OnBytes.TieK (KeyGood KeyPub)
open OnBytes.Params (Rounds)

/-- The plain data of three lists of rounds. -/
@[reducible] def dataOf (R : Rounds × Rounds × Rounds) : Three.Whole :=
  Three.Whole.of R.1 R.2.1 R.2.2

/-- The run of a key file's reduction at these data, under the verdict of the makers' tests. -/
@[reducible] def runOf {Rc : Type} (a : ℕ) (R : Rounds × Rounds × Rounds) (key : Rc → TableKey)
    (k : Params.KeyChains) : Rc → View → View → View → Bool :=
  keyRun (dataOf R) (okAt a (some R)) key k

section Key
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed]
  (f : _root_.Fmt.Fld) (K a : ℕ) (W : Three.Whole) (DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : Seed × Ans → TFk → TJk → T3k → Bool)
  (runK : Seed × Ans → View → View → View → Bool)
  (silP : X × (Seed × Ans) → TFp → TJp → T3p → Bool)
  (runP : X × (Seed × Ans) → View → View → View → Bool)
  (eL : LinkProtocolWithLeafCoding (Seed × Ans) a)
  (Z : Letters I X RI Seed Ans a
    (wholeDesc (ckP f) ((WholeD.of a W).at a) tFk tJk t3k silK runK).proto eL.QL
    (wholeDesc (ckP f) (DP.at a) tFp tJp t3p silP runP).batch)
  (wL : TypedOracleCompiler.Iop.ProtocolQueryLayout 256 (K + 1)
    (⟨eL.QL, eL.aL⟩ : BatchInteractiveOracleProof ((Seed × Ans) × (Seed × Ans)) (twoExternalStrings (2 ^ a) SgX)))
  (Bd : Type) (depthReq depthReqT depthReqL : ℕ)
  (b : Bodies (objF f a (WholeD.of a W) DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z)
    Bd)
  (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (K + 1)
    (typedOracleCarrier (objF f a (WholeD.of a W) DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z)
      Bd (chainsOf (ckP f) ((WholeD.of a W).at a) tFk tJk t3k).ann
      eL.aL)))
  (sb sFS : ℕ) (cfg : ByteArray) (recOf : Params.TableName → Seed × Ans)
  (cA : Ans → List (Dig 256)) (pF : Dat → TFk) (pJ : Dat → TJk) (p3 : Dat → T3k)
  (u : KeyPub) (k : Params.KeyChains) (key₀ : TableKey) (R : Rounds × Rounds × Rounds)
  (key : Seed × Ans → TableKey) (X : Dat → Prop)

/-- the typing -/
local notation "Θ" => typingKey f K a W DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
  depthReq depthReqT depthReqL b g sb sFS cfg recOf cA pF pJ p3

/-- The readings that are spoken of: the good readings at the public files u at which the typing of
the whole file returns, the silent rounds' test says yes and the caller's further condition X
holds. -/
@[reducible] def KeyGoodT (d : Dat) : Prop :=
  KeyGood u d ∧ TypedKey f a W tFk tJk t3k silK runK sb cfg pF pJ p3 d ∧
    SilentKey silK recOf pF pJ p3 d ∧ X d

/-- the readings that are spoken of -/
local notation "Δ" => KeyGoodT f a W tFk tJk t3k silK runK sb cfg recOf pF pJ p3 u X

/-- **What is owed at a key file**, at data and a run made of the public files. -/
structure KeyDebts : Prop where
  /-- the tests under which the makers lay their data pass -/
  ok : okAt a (some R) = true
  shapes : shapesFit a W = true
  salts : saltsFit sb W = true
  /-- the letter cfg is the digest under which the key file's binding tree is hashed, and it has 32
  bytes -/
  cfgIs : cfg = keyCfg u
  cfgSize : cfg.size = 32
  /-- the wiring's depth of a key's request tree is the parameters' -/
  depth : depthReqT = k.oneTime.binding.logLeaves
  /-- at the table of a reading that is spoken of, the key written of the table's record is the
  program's key of the table -/
  keyOf : ∀ d, Δ d → ∀ κ, tableKey k.shared.given.plan.field k.shared.given.cfg
    (Key.tailPublic k noTable).lin.fold.index d.1 0 = some κ → key (recOf d.1) = κ
  /-- the verifier's messages that the three chains have under g give the draws that were read, but
  for the digests, and the proofs of work pass -/
  draws : ∀ d, Δ d → ∀ a' b' e', (Θ).RunsTo d a' b' e' →
    DrawsHeldA (ckP f) (WholeD.of a W) tFk tJk t3k d.2.r (TypedOracleCompiler.Joined.glue a' b' e').1
  /-- the nine -/
  rest : Owes (Θ) (Δ) (keyShape u) (keyCfg u)

variable (p : Model.Verify.Planned) (hp : Model.Verify.planned u.pol u.KL (some u.lay) = .ok p)
  (hk : k = p.chains.key) (h0 : key₀.item = 0)
  (hf : key₀.fits (Key.tailPublic k noTable).lin.fold.index = true) (hR : dryKey k key₀ = some R)
  (hW : W = dataOf R) (hrun : runK = runOf a R key k)
include hp hk h0 hf hR hW hrun

/-- **It gives what is owed at a key file.** -/
theorem KeyDebts.owes
    (H : KeyDebts f K a W DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd depthReq
      depthReqT depthReqL b g sb sFS cfg recOf cA pF pJ p3 u k R key X)
    (hblocks : ∀ d ∈ (WholeD.of a W).ds₁ ++ ((WholeD.of a W).ds₂ ++ (WholeD.of a W).ds₃),
      (bsRound f d.entry d.kind).b ≤ K) :
    KeyOwes f K a W DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd depthReq
      depthReqT depthReqL b g sb sFS cfg recOf cA pF pJ p3 (Δ) (keyShape u) (keyCfg u) := by
  subst hk hW hrun
  have P := fun d (hg : KeyGood u d) => good_pays u p hp key₀ h0 hf R hR d hg a H.ok H.shapes
    (sealBare_of_fits (okAt_parts H.ok).fits)
  have hs : keyShape u = p.chains.key.oneTime.binding := by
    unfold keyShape
    rw [hp]
  exact
    { blocks := hblocks
      work := by
        have e : dataAt a (some R) = dataOf R := if_pos H.ok
        rw [← e]
        exact dataAt_work a (some R)
      depth := by rw [hs]; exact H.depth
      places := fun d hg => by rw [H.depth]; exact (P d hg.1).places
      draws := H.draws
      reads := fun d hg => ⟨_, _, _, (P d hg.1).gives.fits⟩
      run := fun d hg => keyRun_yesA _ _ key p.chains.key d.1 d.2.r (recOf d.1) H.ok
        (H.keyOf d hg d.2.r.key (P d hg.1).key) (P d hg.1).gives.roots (P d hg.1).gives.sealed
        (P d hg.1).gives.okWords (P d hg.1).yes
      salts := H.salts
      runSize := fun d hg => by
        obtain ⟨file, j, real, real2, -, -, -, T⟩ := good_chains u p hp d hg.1
        exact runOfTree_32 _ _ _ _ d.2.r file _ _ _ _ _ _ _ _ _ T.toRead.first_read
          T.toRead.shared_read T.toRead.second_read
      cfgSize := H.cfgSize
      rest := H.rest }

/-- **Where the program says yes to a whole call, the compiled verifier for a key file has the value
yes at whatever string the typing of the whole file returns, if the silent rounds' test says yes and
X holds there**, if what is owed holds at the file's public files, and if no round of the data has
more than K blocks. -/
theorem vTA_of_port' (pp : _root_.Compile.Params) (hMT : pp.sMT = 256 + 8 * sb)
    (hFS : pp.sFS = sFS) (F : OnBytes.K.Files) (hu : u = ⟨F.pol, F.lay, F.KL⟩)
    (H : KeyDebts f K a W DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd depthReq
      depthReqT depthReqL b g sb sFS cfg recOf cA pF pJ p3 u k R key X)
    (hblocks : ∀ d ∈ (WholeD.of a W).ds₁ ++ ((WholeD.of a W).ds₂ ++ (WholeD.of a W).ds₃),
      (bsRound f d.entry d.kind).b ≤ K)
    (id : String) (table further : Params.TableName)
    (h : OnBytes.K.PortYesAt F id table further) :
    ∃ d, TieK.readKeyChains F.pol F.lay F.KL F.key = some (table, d) ∧ d.copy = 0 ∧
      ∀ π, typeFile (ckP f) a W tFk tJk t3k silK runK sb cfg (pF (table, d)) (pJ (table, d))
          (p3 (table, d)) d.salt d.path d.r = some π →
        silK (recOf table) (pF (table, d)) (pJ (table, d)) (p3 (table, d)) = true →
        X (table, d) →
        (verifyOfflineProof (wireF f K a (WholeD.of a W) DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
                         depthReq depthReqT depthReqL b) cA pp (bytesToDig table.root) (recOf table)
          π).det g = true := by
  have O := H.owes f K a W DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
    depthReq depthReqT depthReqL b g sb sFS cfg recOf cA pF pJ p3 u k key₀ R key X p hp hk h0 hf hR
    hW hrun hblocks
  subst hu
  exact vTA_of_port f K a W DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
    depthReq depthReqT depthReqL b g sb sFS cfg recOf cA pF pJ p3 pp hMT hFS F X O id table further
    h

end Key

end OnBytes.Maker
