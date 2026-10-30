-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/LeftAtKey.lean: where the verifier program says yes to a whole call (`PortYesAt`,
OnBytes/K/Top.lean), the compiled verifier that the verifier with a record runs for a key file
(`verifyOfflineProof`, Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean) has the value yes under fixed oracle functions: the
statement, at the typing `typingKey` (Johnson/Maker/TypingAKey.lean), with all that is owed in one
record.

OnBytes/TypedOracleCompiler/Joined/K/LeftOfChains.lean has the statement for any typing, under seventeen named
hypotheses (`LeftHoles`). At `typingKey` eight of them are derived here from the rows of `KeyOwes`.

  `Owes`          nine of the seventeen, for any typing, in the words of `LeftHoles`
  `Owes.holes`    with the other eight, `LeftHoles`
  `typingKey_laws`, `typingKey_wire`, `typingKey_depth`   three at `typingKey`: the joining round is
                  shared and coherent (no hypothesis); the laws of the wire record (from two tests
                  on the data's numbers); the depth of the request tree (it is a letter of the
                  wiring, so this is an equation between two numbers)
  `typingKey_opened`   four: the openings at the three chains' rounds and of the stored table are as
                  the strict format asks (`fileKey_openedA`, Johnson/Maker/OpenedAtA.lean)
  `typingKey_accept`   the eighth: the decision says yes at the three chains' transcripts in a row
                  (`accept_threeA`, OnBytes/Maker/AcceptAtA.lean). The hypotheses of these two are
                  rows of `KeyOwes`
  `TypedKey`      the typing of the whole file (`typeFile`, OnBytes/Maker/TypeFile.lean) returns a
                  string at a reading
  `SilentKey`     the test on what the silent rounds send says yes at a reading
  `KeyOwes`       what is owed at a key file, of the readings that meet a predicate Good
  `vTA_of_port`   the program's yes and `KeyOwes` give: the fixed reading of the key file returns
                  data, and `verifyOfflineProof` has the value yes at whatever string `typeFile` returns at them,
                  if the silent rounds' test says yes there

Of which readings it is asked. In `vTA_of_port` Good is: a good reading at the file's public files
(`KeyGood`: the reading of any key file that the program accepts there, whoever wrote it) at which
`typeFile` returns and the silent rounds' test says yes. Neither holds g, and where silK, pF, pJ, p3
are written functions a program can evaluate both at a reading (for the first: the test
`typeReturns`, OnBytes/Maker/TypeTest.lean). A letter X lets the caller add a further condition on
the reading: it stands in Good and, at the reading of the file at hand, before the yes. It is meant
for a test on what was read that a program can evaluate and that holds no g. The statement is worth
what X is worth: at an X that nothing meets, or that holds the yes itself, it says nothing. So the
sentence is: UNDER `KeyOwes`, the program's yes, the converter's value, the yes of that test and X
give the yes of `verifyOfflineProof`. Where `typeFile` returns nothing, or the test says no, the statement is idle:
also at an honest file, if a letter is laid wrong. That the converter returns is NOT a consequence
of the program's yes: the shipped reader ties two openings of one position by digests alone, and
`typeFile` makes its tables only if they hold one column and one salt (the hypothesis `collides` of
`port_key`, Johnson/Maker/Page/PortKey.lean, names that case;
OnBytes/Maker/Page/CollidesBytes.lean).

The rows of `KeyOwes`. On the data: `blocks`, `work`, `depth`, `salts`, `cfgSize`. On each such
reading: `runSize`, `places` (the binding tree as read has the wiring's number of leaves), `reads`
(the data fit what was read), `run` (the run says yes at the record of the table). On the
verifier's messages that the three chains have under g: `draws` (they give the draws that were
read, but for the digests, and the proofs of work pass). And `rest`: the nine.

Who uses what. The sentences at a key file (Johnson/Maker/Page/PortKey.lean) use three names of this
file: `TypedKey`, `typingKey_laws`, `typingKey_wire`. They build their own `LeftHoles` and do not go
through `vTA_of_port`, whose one caller is `vTA_of_port'` (Johnson/Maker/KeyPays.lean).

Not claimed. Any row of `KeyOwes`. No member of it is shown at the real tables by
Johnson/Maker/KeyPays.lean. In particular nothing is said on how g answers the chains' queries
(`draws`; in `rest`: `node`, `leaf`, `sealAt`, the four walks). One direction only. Nothing on
soundness.


-/
import Johnson.Maker.TypingAKey
import Johnson.Maker.DetGood
import OnBytes.Maker.AcceptAtA
import OnBytes.Maker.TypingFlags
import Johnson.Maker.OpenedAtA

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run _root_.Run.PQ OnBytes.RunA TypedOracleCompiler.Joined TypedOracleCompiler.Joined.K Rom
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Compile.Batch.Cms (Bodies typedOracleCarrier cmsTA verifyOfflineProof)
open OnBytes.TieK (KeyGood)

/-- **Nine of the hypotheses of `LeftHoles`**, for any typing: those on the oracle functions, on the
numbers of roots and on the salt. -/
structure Owes (T : TypingA) (Good : Dat → Prop) (shape : Params.LinBindingShape)
    (cfg : ByteArray) : Prop where
  /-- g answers the request tree's node oracle with the program's hash of a vertex -/
  node : NodeCoded T.g cfg
  /-- g answers the request tree's leaf oracle with the program's hash of a leaf -/
  leaf : LeafCoded T.g shape.logLeaves cfg shape.saltBytes T.rsOf
  /-- few trees a component, and as many roots read for each chain as its rounds have trees -/
  fits : ∀ d, Good d → TypedOracleCompiler.Joined.Fits T.F (T.k₁ d) (T.k₂ d) (T.k₃ d)
  /-- the first chain's salt has sFS bits -/
  saltLen : ∀ d, Good d → (T.salt d).length = T.sFS
  /-- g answers the query to g that holds the chaining value in which the first chain ends with that
  chain's seal as read -/
  sealAt : ∀ d, Good d → ∀ a b e, T.RunsTo d a b e → ∀ ρ₁, a.2.2 = .loc ρ₁ →
    T.g (OracleName.g T.F.t) (qSeal₁ T.F.t T.F.D T.F.embP (T.prf d) ρ₁ (rtJ T.F.D T.F.wq (T.prf d) a)) =
      bytesToDig d.2.seal1
  /-- the walk of each forest of chain 1's rounds ends, under g, in its trees' roots -/
  walk₁ : ∀ d, Good d → ∀ a b e, T.RunsTo d a b e → ∀ F₁,
    forestsB T.G.c₁ T.G.A₁ (wire₁ T.F.wq) (symb₁ T.F.embS) a.2.1
      (rd₁ T.F.D T.F.wq (T.xAt d) (T.prf d) a b e) (op₁ T.F.D (T.prf d)) = some F₁ →
    ∀ R ∈ F₁, walkP T.g R R.reads = true
  /-- of chain 2's rounds -/
  walk₂ : ∀ d, Good d → ∀ a b e, T.RunsTo d a b e → ∀ F₂,
    forestsB T.G.c₂ T.G.A₂ (wire₂ T.F.wq) (symb₂ T.F.embS) b.2.1
      (rd₂ T.F.D T.F.wq (T.xAt d) (T.prf d) a b e) (op₂ T.F.D (T.prf d)) = some F₂ →
    ∀ R ∈ F₂, walkP T.g R R.reads = true
  /-- of chain 3's rounds -/
  walk₃ : ∀ d, Good d → ∀ a b e, T.RunsTo d a b e → ∀ F₃,
    forestsB T.G.c₃ T.G.A₃ (wire₃ T.F.wq) (symb₃ T.F.embS) e.2.1
      (rd₃ T.F.D T.F.wq (T.xAt d) (T.prf d) a b e) (op₃ T.F.D (T.prf d)) = some F₃ →
    ∀ R ∈ F₃, walkP T.g R R.reads = true
  /-- of the external strings -/
  walkE : ∀ d, Good d → ∀ a b e, T.RunsTo d a b e → ∀ Fe,
    forestExt T.F.wq.ext T.F.embE (T.cmsAt d) (readE T.F.D T.F.wq (T.xAt d) (glue a b e).1)
      (T.prf d).ext = some Fe →
    ∀ R ∈ Fe, walkP T.g R R.reads = true

/-- With the other eight, `LeftHoles`. -/
theorem Owes.holes {T : TypingA} {Good : Dat → Prop} {shape : Params.LinBindingShape}
    {cfg : ByteArray} (H : Owes T Good shape cfg) (hl : T.G.Laws) (hw : T.F.wq.OKG)
    (hd : T.W.dReq T.F.t = shape.logLeaves)
    (ho : ∀ d, Good d → ∀ a b e, T.RunsTo d a b e →
      TypedOracleCompiler.Joined.Opened T.sMT T.G.c₁ T.G.A₁ (wire₁ T.F.wq) a.2.1
          (rd₁ T.F.D T.F.wq (T.xAt d) (T.prf d) a b e) (op₁ T.F.D (T.prf d)) ∧
        TypedOracleCompiler.Joined.Opened T.sMT T.G.c₂ T.G.A₂ (wire₂ T.F.wq) b.2.1
          (rd₂ T.F.D T.F.wq (T.xAt d) (T.prf d) a b e) (op₂ T.F.D (T.prf d)) ∧
        TypedOracleCompiler.Joined.Opened T.sMT T.G.c₃ T.G.A₃ (wire₃ T.F.wq) e.2.1
          (rd₃ T.F.D T.F.wq (T.xAt d) (T.prf d) a b e) (op₃ T.F.D (T.prf d)) ∧
        OpenedE T.sMT T.F.wq.maxDepth T.F.wq.ext (readE T.F.D T.F.wq (T.xAt d) (glue a b e).1)
          (T.prf d).ext)
    (ha : ∀ d, Good d → ∀ a b e, T.RunsTo d a b e →
      T.F.D.accept (T.xAt d) (T.F.wq.ext.build fun p => ((T.prf d).ext p).map Opening.sym)
        (Tr.app (s := T.G.c₁) (t := T.G.c₂ ++ T.G.c₃) (tr₁ T.F.D T.F.wq (T.prf d) a)
          (Tr.app (s := T.G.c₂) (t := T.G.c₃) (tr₂ T.F.D T.F.wq (T.prf d) b)
            (tr₃ T.F.D T.F.wq (T.prf d) e))) = true) :
    LeftHoles T Good shape cfg :=
  { H with
    laws := hl
    wire := hw
    depth := hd
    opened₁ := fun d hg a b e hr => (ho d hg a b e hr).1
    opened₂ := fun d hg a b e hr => (ho d hg a b e hr).2.1
    opened₃ := fun d hg a b e hr => (ho d hg a b e hr).2.2.1
    openedE := fun d hg a b e hr => (ho d hg a b e hr).2.2.2
    accept := ha }

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

/-- the typing -/
local notation "Θ" => typingKey f K a W DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
  depthReq depthReqT depthReqL b g sb sFS cfg recOf cA pF pJ p3

/-- The typing of the whole file returns a string at the reading d. -/
def TypedKey (d : Dat) : Prop :=
  ∃ π, typeFile (ckP f) a W tFk tJk t3k silK runK sb cfg (pF d) (pJ d) (p3 d) d.2.salt d.2.path
    d.2.r = some π

/-- The test on what the silent rounds send says yes at the reading d, at its table's record. -/
def SilentKey (d : Dat) : Prop := silK (recOf d.1) (pF d) (pJ d) (p3 d) = true

theorem typingKey_laws : (Θ).G.Laws :=
  chainsOf_laws (ckP f) ((WholeD.of a W).at a) tFk tJk t3k

theorem typingKey_wire
    (bK : ∀ d ∈ (WholeD.of a W).ds₁ ++ ((WholeD.of a W).ds₂ ++ (WholeD.of a W).ds₃),
      (bsRound f d.entry d.kind).b ≤ K)
    (wK : ∀ d ∈ (WholeD.of a W).ds₁ ++ ((WholeD.of a W).ds₂ ++ (WholeD.of a W).ds₃),
      d.entry.work ≤ 64) : (Θ).F.wq.OKG :=
  wqWhole_okg_ckP f K ((WholeD.of a W).at a) tFk tJk t3k silK runK bK wK

theorem typingKey_depth : (Θ).W.dReq (Θ).F.t = depthReqT := rfl

/-- **The decision says yes at the three chains' transcripts in a row**, at a reading d and values
a', b', e' of the three chains under g. -/
theorem typingKey_accept (d : Dat)
    (typed : ∃ π, typeFile (ckP f) a W tFk tJk t3k silK runK sb cfg (pF d) (pJ d) (p3 d) d.2.salt
      d.2.path d.2.r = some π)
    (places : d.2.r.place.places = 2 ^ depthReqT) (a' b' e') (hr : (Θ).RunsTo d a' b' e')
    (draws : DrawsHeldA (ckP f) (WholeD.of a W) tFk tJk t3k d.2.r (glue a' b' e').1)
    (reads : ∃ S₁ S₂ S₃, ReadFits a W d.2.r S₁ S₂ S₃)
    (silent : silK (recOf d.1) (pF d) (pJ d) (p3 d) = true)
    (run : ∀ v₁ v₂ v₃, TwoLaws.ViewAlike (dropSeal d.2.r.first.view) v₁ →
      TwoLaws.ViewAlike d.2.r.shared.view v₂ → TwoLaws.ViewAlike d.2.r.second.view v₃ →
      runK (recOf d.1) v₁ v₂ v₃ = true) :
    (Θ).F.D.accept ((Θ).xAt d) ((Θ).F.wq.ext.build fun p => (((Θ).prf d).ext p).map Opening.sym)
      (Tr.app (s := (Θ).G.c₁) (t := (Θ).G.c₂ ++ (Θ).G.c₃) (tr₁ (Θ).F.D (Θ).F.wq ((Θ).prf d) a')
        (Tr.app (s := (Θ).G.c₂) (t := (Θ).G.c₃) (tr₂ (Θ).F.D (Θ).F.wq ((Θ).prf d) b')
          (tr₃ (Θ).F.D (Θ).F.wq ((Θ).prf d) e'))) = true := by
  obtain ⟨π, hπ⟩ := typed
  obtain ⟨S₁, S₂, S₃, hS⟩ := reads
  obtain ⟨h₁, h₂, h₃⟩ := hr
  have e := typingKey_prf f K a W DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
    depthReq depthReqT depthReqL b g sb sFS cfg recOf cA pF pJ p3 d π hπ places
  rw [e] at h₁ h₂ h₃ ⊢
  have fl := flags_glue_of_det g h₁ h₂ h₃
  exact accept_threeA (ckP f) K (chalP f K) a W tFk tJk t3k silK runK sb cfg (pF d) (pJ d) (p3 d)
    d.2.salt d.2.path d.2.r π hπ a' b' e' fl.1 fl.2 draws hS (recOf d.1) silent run

/-- **The openings are as the strict format asks**, at a reading d and values a', b', e' of the
three chains under g: four records. -/
theorem typingKey_opened (d : Dat)
    (typed : ∃ π, typeFile (ckP f) a W tFk tJk t3k silK runK sb cfg (pF d) (pJ d) (p3 d) d.2.salt
      d.2.path d.2.r = some π)
    (places : d.2.r.place.places = 2 ^ depthReqT) (a' b' e') (hr : (Θ).RunsTo d a' b' e')
    (draws : DrawsHeldA (ckP f) (WholeD.of a W) tFk tJk t3k d.2.r (glue a' b' e').1)
    (reads : ∃ S₁ S₂ S₃, ReadFits a W d.2.r S₁ S₂ S₃) (salts : saltsFit sb W = true)
    (runSize : ∀ j run, runOfTree W d.2.r j = some run → run.size = 32) (cfgSize : cfg.size = 32) :
    TypedOracleCompiler.Joined.Opened (Θ).sMT (Θ).G.c₁ (Θ).G.A₁ (wire₁ (Θ).F.wq) a'.2.1
        (rd₁ (Θ).F.D (Θ).F.wq ((Θ).xAt d) ((Θ).prf d) a' b' e') (op₁ (Θ).F.D ((Θ).prf d)) ∧
      TypedOracleCompiler.Joined.Opened (Θ).sMT (Θ).G.c₂ (Θ).G.A₂ (wire₂ (Θ).F.wq) b'.2.1
        (rd₂ (Θ).F.D (Θ).F.wq ((Θ).xAt d) ((Θ).prf d) a' b' e') (op₂ (Θ).F.D ((Θ).prf d)) ∧
      TypedOracleCompiler.Joined.Opened (Θ).sMT (Θ).G.c₃ (Θ).G.A₃ (wire₃ (Θ).F.wq) e'.2.1
        (rd₃ (Θ).F.D (Θ).F.wq ((Θ).xAt d) ((Θ).prf d) a' b' e') (op₃ (Θ).F.D ((Θ).prf d)) ∧
      OpenedE (Θ).sMT (Θ).F.wq.maxDepth (Θ).F.wq.ext
        (readE (Θ).F.D (Θ).F.wq ((Θ).xAt d) (glue a' b' e').1) ((Θ).prf d).ext := by
  obtain ⟨π, hπ⟩ := typed
  obtain ⟨S₁, S₂, S₃, hS⟩ := reads
  obtain ⟨h₁, h₂, h₃⟩ := hr
  have e := typingKey_prf f K a W DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
    depthReq depthReqT depthReqL b g sb sFS cfg recOf cA pF pJ p3 d π hπ places
  rw [e] at h₁ h₂ h₃ ⊢
  exact fileKey_openedA f K a W DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
    depthReq depthReqT depthReqL b g sb cfg (pF d) (pJ d) (p3 d) d.2.salt d.2.path d.2.r π hπ _ _
    a' b' e' h₁ h₂ h₃ hS.shape hS.bare salts runSize cfgSize hS.ls₁ hS.ls₂ hS.ls₃ draws.d₁ draws.d₂
    draws.d₃

/-- **What is owed at a key file.** Good: the readings that are spoken of. shape, cfgB: the binding
tree's shape and the digest under which it is hashed. -/
structure KeyOwes (Good : Dat → Prop) (shape : Params.LinBindingShape) (cfgB : ByteArray) :
    Prop where
  /-- no round of the file has more than K blocks -/
  blocks : ∀ d ∈ (WholeD.of a W).ds₁ ++ ((WholeD.of a W).ds₂ ++ (WholeD.of a W).ds₃),
    (bsRound f d.entry d.kind).b ≤ K
  /-- no round has more than 64 bits of work -/
  work : ∀ d ∈ (WholeD.of a W).ds₁ ++ ((WholeD.of a W).ds₂ ++ (WholeD.of a W).ds₃),
    d.entry.work ≤ 64
  /-- the wiring's depth of a key's request tree is the binding tree's -/
  depth : depthReqT = shape.logLeaves
  /-- the binding tree as read has the wiring's number of leaves -/
  places : ∀ d, Good d → d.2.r.place.places = 2 ^ depthReqT
  /-- the verifier's messages that the three chains have under g give the draws that were read, but
  for the digests, and the proofs of work pass -/
  draws : ∀ d, Good d → ∀ a' b' e', (Θ).RunsTo d a' b' e' →
    DrawsHeldA (ckP f) (WholeD.of a W) tFk tJk t3k d.2.r (glue a' b' e').1
  /-- the data fit what was read, under some three descriptions -/
  reads : ∀ d, Good d → ∃ S₁ S₂ S₃, ReadFits a W d.2.r S₁ S₂ S₃
  /-- the run says yes at the table's record, on all views that are the file's but for digests -/
  run : ∀ d, Good d → ∀ v₁ v₂ v₃, TwoLaws.ViewAlike (dropSeal d.2.r.first.view) v₁ →
    TwoLaws.ViewAlike d.2.r.shared.view v₂ → TwoLaws.ViewAlike d.2.r.second.view v₃ →
    runK (recOf d.1) v₁ v₂ v₃ = true
  /-- every stored table of the data has sb bytes of a salt -/
  salts : saltsFit sb W = true
  /-- each run's value under which a tree of the file was sent has 32 bytes -/
  runSize : ∀ d, Good d → ∀ j run, runOfTree W d.2.r j = some run → run.size = 32
  /-- the letter cfg has 32 bytes -/
  cfgSize : cfg.size = 32
  /-- the nine -/
  rest : Owes (Θ) Good shape cfgB

/-- What is owed gives the seventeen hypotheses at the typing, if at each reading that is spoken of
the typing returns and the silent rounds' test says yes. -/
theorem KeyOwes.holes {Good : Dat → Prop} {shape : Params.LinBindingShape} {cfgB : ByteArray}
    (H : KeyOwes f K a W DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd depthReq
      depthReqT depthReqL b g sb sFS cfg recOf cA pF pJ p3 Good shape cfgB)
    (ht : ∀ d, Good d → TypedKey f a W tFk tJk t3k silK runK sb cfg pF pJ p3 d)
    (hsil : ∀ d, Good d → SilentKey silK recOf pF pJ p3 d) :
    LeftHoles (Θ) Good shape cfgB :=
  H.rest.holes
    (typingKey_laws f K a W DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
      depthReq depthReqT depthReqL b g sb sFS cfg recOf cA pF pJ p3)
    (typingKey_wire f K a W DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
      depthReq depthReqT depthReqL b g sb sFS cfg recOf cA pF pJ p3 H.blocks H.work)
    H.depth
    (fun d hg a' b' e' hr =>
      typingKey_opened f K a W DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
        depthReq depthReqT depthReqL b g sb sFS cfg recOf cA pF pJ p3 d (ht d hg)
        (H.places d hg) a' b' e' hr (H.draws d hg a' b' e' hr) (H.reads d hg) H.salts
        (H.runSize d hg) H.cfgSize)
    fun d hg a' b' e' hr =>
      typingKey_accept f K a W DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
        depthReq depthReqT depthReqL b g sb sFS cfg recOf cA pF pJ p3 d (ht d hg)
        (H.places d hg) a' b' e' hr (H.draws d hg a' b' e' hr) (H.reads d hg) (hsil d hg)
        (H.run d hg)

/-- **Where the program says yes to a whole call, the compiled verifier for a key file has the value
yes at whatever string the typing of the whole file returns, if the silent rounds' test says yes
there**, and if what is owed holds of the good readings at the file's public files at which the
typing returns and that test says yes. X: a further condition of the caller on a reading. p: the
two lengths of salts are the typing's. -/
theorem vTA_of_port (p : _root_.Compile.Params) (hMT : p.sMT = 256 + 8 * sb) (hFS : p.sFS = sFS)
    (F : OnBytes.K.Files) (X : Dat → Prop)
    (H : KeyOwes f K a W DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd depthReq
      depthReqT depthReqL b g sb sFS cfg recOf cA pF pJ p3
      (fun d => KeyGood ⟨F.pol, F.lay, F.KL⟩ d ∧
        TypedKey f a W tFk tJk t3k silK runK sb cfg pF pJ p3 d ∧ SilentKey silK recOf pF pJ p3 d ∧
        X d)
      (keyShape ⟨F.pol, F.lay, F.KL⟩) (keyCfg ⟨F.pol, F.lay, F.KL⟩))
    (id : String) (table further : Params.TableName)
    (h : OnBytes.K.PortYesAt F id table further) :
    ∃ d, TieK.readKeyChains F.pol F.lay F.KL F.key = some (table, d) ∧ d.copy = 0 ∧
      ∀ π, typeFile (ckP f) a W tFk tJk t3k silK runK sb cfg (pF (table, d)) (pJ (table, d))
          (p3 (table, d)) d.salt d.path d.r = some π →
        silK (recOf table) (pF (table, d)) (pJ (table, d)) (p3 (table, d)) = true →
        X (table, d) →
        (verifyOfflineProof (wireF f K a (WholeD.of a W) DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
                         depthReq depthReqT depthReqL b) cA p (bytesToDig table.root) (recOf table)
          π).det g = true := by
  obtain ⟨d, hd, hc, hgood, hy⟩ :=
    key_det_good (Θ) F _ (H.holes (ht := fun _ hg => hg.2.1) (hsil := fun _ hg => hg.2.2.1)) id
      table further h
  refine ⟨d, hd, hc, fun π hπ hs hX => ?_⟩
  have y := hy ⟨hgood, ⟨π, hπ⟩, hs, hX⟩
  rw [typingKey_prf f K a W DP tFk tJk t3k tFp tJp t3p silK runK silP runP eL Z wL Bd
    depthReq depthReqT depthReqL b g sb sFS cfg recOf cA pF pJ p3 (table, d) π hπ
    (H.places (table, d) ⟨hgood, ⟨π, hπ⟩, hs, hX⟩)] at y
  rw [← fileKey_verifyA, hMT, hFS]
  exact y

end Key

end OnBytes.Maker
