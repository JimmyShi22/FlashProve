-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/Page/PortKey.lean: the sentence at a key file, for any family g of oracle functions
and any second arm KC. Where the verifier program says yes to a call: EITHER the typing of the
whole file returns a string at which the compiled verifier for a key file, at the makers' wiring,
has the value yes under g, OR KC.

Which verifier. The one that the library's compiler makes of a description built from the program's
own blocks: the description's decision is the program's own decision on the three chains, by design.
What crosses here is the compiler's layer: the chains' hashing, the seal, the openings, the walks,
the one leaf of the binding tree.

This file is the composition alone. What the composition needs is asked as six named hypotheses,
each in the letters of the file that is meant to pay it. Four speak of a file, and they speak of THE
FILE AT HAND alone: of the data d of the fixed reading of F.key. Two speak of g and not of the key
file.

  `frontK`, `joinK`, `seamK`   what the silent rounds of a key file send, as functions of a reading
  `vTA_of_verifyM`   where the written key file's verifier at the makers' values says yes under g,
                     so does the compiled verifier that the verifier with a record runs for a key
                     file (under `hMT`, `hFS`)
  `KeySays`      what the sentence concludes, as one named proposition, so that it can be stated at
                 values without being spelt again. That the reader of the table returns the
                 program's table is not a clause of it: it follows from the yes (`port_key_reads`,
                 OnBytes/Maker/Page/PortReads.lean)
  `port_key`     the sentence
  `port_key_returns`   where the test `typeReturns` says yes at the file at hand: the first arm,
                 under the five other hypotheses

The six hypotheses of `port_key`. Four under "the fixed reading of F.key returns (table, d)":
  `after`      at the string that `typeFile` returns and at whatever values the three chains have
               under g: the ten conditions of `AfterRuns` hold (OnBytes/TypedOracleCompiler/Joined/K/Left.lean:
               the decision among them, and in the decision the test silK on the silent rounds)
  `fits`       few trees a component, and as many roots read for each chain as its rounds have trees
  `saltLen`    the first chain's salt has sFS bits
  `collides`   the test `typeReturns` says yes, or KC
and without the key file in them (they hold the digest and the binding tree's shape that the planner
makes of the three public files):
  `node`, `leaf`   g answers the request tree's two oracles with the program's hashes
Of the seventeen hypotheses under which the library gives the yes (`LeftHoles`,
OnBytes/TypedOracleCompiler/Joined/K/LeftOfChains.lean) three are proved here (`laws`, `wire`, `depth`), ten are
read off `after`, four are asked by name. So in weight the sentence lies in `after`.
Beside them: the plan (`hp`), k (`hk`), the wiring's depth of a key's tree (`hdepth`), pp's two
lengths (`hMT`, `hFS`).

Why at the file at hand. Asked of every key file that the program accepts at these public files, a
hypothesis that fails at one of them, whoever wrote it, would make the whole statement idle.

Why g and KC are letters. The proof reads g through `after`, `node` and `leaf` alone, and KC through
`collides` alone. So one statement serves every family and every second arm at which these are paid.
With the two free the statement puts no limit on a caller: one may choose g after seeing the file,
and at a g that nothing recommends the yes is worth nothing; at KC := True `collides` costs nothing
and the sentence says nothing. It is a tool for statements at a WRITTEN g and a WRITTEN KC.
In this library `port_key` is called once, in `port_key_returns`, at KC := False with g a letter:
no theorem calls it at a written g or with KC a collision. `port_key_or`
(OnBytes/Maker/Page/CollidesAt.lean) has such a second arm: the
key file itself shows a collision of the hash.

The entry file's part p and the number of blocks p.K are letters of the makers: the sentence holds
at every one. They stand in the type of g, of the wiring and of the verifier. The entry file's part
holds no law but K ≥ kM: a protocol of no rounds with any wire record passes. So the sentence also
holds where p's wire record makes no sense. At such a p no theorem about the whole verifier with a
record applies, because that verifier's laws on the wiring fail. By its text the key file's own
verifier reads only the number p.K from p; no law says so.

Not claimed. Any of the six. That the makers' object is the one of which the soundness theorem
speaks. Nothing on the seed's test, the entry file or the proof file. `PortYesAt` is the yes of the
whole call. All letters stand under one "for all" with the files. One direction only. Nothing on
soundness.


-/
import Johnson.Maker.Page.AfterM
import Johnson.Maker.KeyAtMakers
import OnBytes.Maker.Page.CollidesBytes

set_option autoImplicit false

namespace OnBytes.Maker.Page

open Rom TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Compile.Batch
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ Hiop OnBytes.Maker OnBytes.Flat OnBytes.RunA
open TypedOracleCompiler.Run.SeedPage (LinkCode)
open TypedOracleCompiler.Run.PageG (Leaves)
open _root_.Compile.Joined (JoinMsg)
open OnBytes.Params (Rounds)
open OnBytes.TwoLaws (ViewAlike)

attribute [local instance] ConfLetters.finRnd ConfLetters.neRnd ConfLetters.finPad
  ConfLetters.nePad ConfLetters.finSeed ConfLetters.neSeed
open TypedOracleCompiler.Joined.K
open OnBytes.TieK (KeyGood KeyPub)

/-- What the first silent round of a key file sends, made of a reading. -/
def frontK (d : Dat) : FrontMsg (List E) := frontOf d.1.answers d.2.copy

/-- What the joining round sends. tJ: a fixed value, where the reading has none. -/
def joinK (tJ : JoinMsg (List E) ByteArray) (d : Dat) : JoinMsg (List E) ByteArray :=
  (joinOf d.1.answers d.2.r).getD tJ

/-- What the seam's round sends. t3: a fixed value, where the reading has none. -/
def seamK (t3 : ByteArray) (d : Dat) : ByteArray := (seamOf d.2.r).getD t3

variable {a : ℕ} (Kc : ConfLetters a) (f : _root_.Fmt.Fld)
  (tFk : FrontMsg (List E)) (tJk : JoinMsg (List E) ByteArray) (t3k : ByteArray)
  (tFp : FrontMsg (List E)) (tJp : JoinMsg (List E) ByteArray) (t3p : ByteArray)
  (silK : Kc.conf.Rec → FrontMsg (List E) → JoinMsg (List E) ByteArray → ByteArray → Bool)
  (silP : Kc.conf.X × Kc.conf.Rec → FrontMsg (List E) → JoinMsg (List E) ByteArray → ByteArray →
    Bool) (key : Kc.conf.Rec → TableKey)
  (k : Params.KeyChains) (rec₀ : Kc.conf.Rec) (c : Params.ProofChains)
  (block : Kc.conf.X → Blk Proof.FirstEnd) (z₀ : Kc.conf.X × Kc.conf.Rec) (p : LinkProtocolWithLeafCodingAndQueryLayout Kc.conf.Rec a
    (kM Kc f key k rec₀ c block z₀)) (N : ℕ) (early : Kc.conf.X → Kc.conf.X) (late : Option ℕ)
  (P : (filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early
    late).Provers)
  (cfg : ByteArray) (sb depthReq depthReqT depthReqL sFS : ℕ)
  (recOf : Params.TableName → Kc.conf.Rec) (cA : Kc.conf.Ans → List (Dig 256))
  (g : Fam (TypedOracleCompiler.Compile.Batch.typedOracleFamily 256 (p.K + 1)
    (TypedOracleCompiler.Compile.Batch.Cms.typedOracleCarrier
      ((filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early
        late).withProvers P) (List Bool)
      (filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late).annT
      (filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early
        late).annL)))

/-- the key file, written, at the makers' values -/
local notation "𝔉" => fileKeyM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N
    early late P sb depthReq depthReqT depthReqL
/-- the typing of a key file at the makers' values, under g -/
local notation "Θ" => typingKeyM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N
    early late P sb depthReq depthReqT depthReqL g sFS cfg recOf cA frontK (joinK tJk) (seamK t3k)

/-- Where the written key file's verifier at the makers' values says yes under g, so does the
compiled verifier that the verifier with a record runs for a key file, at the makers' wiring (under
`hMT`, `hFS`). -/
theorem vTA_of_verifyM (pp : _root_.Compile.Params) (hMT : pp.sMT = 256 + 8 * sb)
    (hFS : pp.sFS = sFS) (cm : Dig 256) (rec : Kc.conf.Rec) (π : (𝔉).Prf)
    (y : ((𝔉).verify (256 + 8 * sb) sFS (cm :: cA rec.2) rec π).det g = true) :
    (TypedOracleCompiler.Compile.Batch.Cms.verifyOfflineProof
      (wireM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P sb
        depthReq depthReqT depthReqL) cA pp cm rec π).det g = true := by
  have e := fileKey_verifyA f p.K a (dataK Kc key k rec₀) (dataP Kc
    key c block z₀) tFk tJk t3k tFp tJp t3p silK (runKM Kc key k rec₀) silP (runPM Kc key c block
    z₀) p.toLinkProtocolWithLeafCoding (lettersOf Kc f (dataK Kc key k rec₀) (dataP Kc key c
    block z₀) tFk tJk t3k tFp tJp t3p silK (runKM Kc key k rec₀) silP (runPM Kc key c block z₀)
    p.toLinkProtocolWithLeafCoding N early late P) p.wL (List Bool) depthReq
    depthReqT depthReqL (bodiesF f a (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp
    tJp t3p silK (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding (lettersOf Kc f
      (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p
    silK (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding N early late P) sb
      (embStored a sb)
    (prjStored a sb)) cA pp cm rec π
  rw [hMT, hFS] at e
  exact (congrArg (fun o => o.det g) e).symm.trans y

/-- **What the sentence at a key file concludes**: the fixed reading of F.key returns data d at the
program's table, the copy's number is 0, and EITHER the typing of the whole file returns a string at
which the compiled verifier for a key file has the value yes under g, OR KC. -/
def KeySays (pp : _root_.Compile.Params) (F : OnBytes.K.Files) (table : Params.TableName)
    (KC : Prop) : Prop :=
  ∃ d, TieK.readKeyChains F.pol F.lay F.KL F.key = some (table, d) ∧ d.copy = 0 ∧
    ((∃ π, typeFile (ckP f) a (dataAt a (dryKey k (key rec₀))) tFk tJk t3k silK
        (runKM Kc key k rec₀) sb cfg (frontK (table, d)) (joinK tJk (table, d))
        (seamK t3k (table, d)) d.salt d.path d.r = some π ∧
      (TypedOracleCompiler.Compile.Batch.Cms.verifyOfflineProof
        (wireM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P sb
          depthReq depthReqT depthReqL) cA pp (bytesToDig table.root) (recOf table) π).det g =
        true) ∨
      KC)

/-- **The sentence at a key file.** -/
theorem port_key (pp : _root_.Compile.Params) (hMT : pp.sMT = 256 + 8 * sb) (hFS : pp.sFS = sFS)
    (F : OnBytes.K.Files) (pl : Model.Verify.Planned)
    (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok pl) (hk : k = pl.chains.key)
    (hdepth : depthReqT = k.oneTime.binding.logLeaves)
    (id : String) (table further : Params.TableName) (KC : Prop)
    (after : ∀ d, TieK.readKeyChains F.pol F.lay F.KL F.key = some (table, d) → ∀ π,
      typeFile (ckP f) a (dataAt a (dryKey k (key rec₀))) tFk tJk t3k silK (runKM Kc key k rec₀) sb
        cfg (frontK (table, d)) (joinK tJk (table, d)) (seamK t3k (table, d)) d.salt d.path d.r =
        some π →
      ∀ a' b' e',
      (run₁ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin (bytesToDig table.root :: cA (recOf table).2)
        (recOf table) π).det g = some a' →
      (run₂ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin (bytesToDig table.root :: cA (recOf table).2)
        (recOf table) π a').det g = some b' →
      (run₃ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin (bytesToDig table.root :: cA (recOf table).2)
        (recOf table) π a' b').det g = some e' →
      AfterRuns (𝔉) g (256 + 8 * sb) (bytesToDig table.root :: cA (recOf table).2) (recOf table) π
        (bytesToDig d.seal1) a' b' e')
    (node : NodeCoded (Θ).g (keyCfg ⟨F.pol, F.lay, F.KL⟩))
    (leaf : LeafCoded (Θ).g (keyShape ⟨F.pol, F.lay, F.KL⟩).logLeaves (keyCfg ⟨F.pol, F.lay, F.KL⟩)
      (keyShape ⟨F.pol, F.lay, F.KL⟩).saltBytes (Θ).rsOf)
    (fits : ∀ d, TieK.readKeyChains F.pol F.lay F.KL F.key = some (table, d) →
      TypedOracleCompiler.Joined.Fits (Θ).F ((Θ).k₁ (table, d)) ((Θ).k₂ (table, d)) ((Θ).k₃ (table, d)))
    (saltLen : ∀ d, TieK.readKeyChains F.pol F.lay F.KL F.key = some (table, d) →
      ((Θ).salt (table, d)).length = sFS)
    (collides : ∀ d, TieK.readKeyChains F.pol F.lay F.KL F.key = some (table, d) →
      typeReturns (ckP f) a (dataAt a (dryKey k (key rec₀))) sb cfg d.r = true ∨ KC)
    (h : OnBytes.K.PortYesAt F id table further) :
    KeySays Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P cfg
      sb depthReq depthReqT depthReqL recOf cA g pp F table KC := by
  have ho := TieK.port_key_chains F id table further h
  obtain ⟨_, _, d, _, _, -, -, hd, -⟩ := TieK.readKeyChains_of F table ho
  have hgood : KeyGood ⟨F.pol, F.lay, F.KL⟩ (table, d) := ⟨F, rfl, rfl, rfl, ho, hd⟩
  have hplaces : d.r.place.places = 2 ^ depthReqT := by
    obtain ⟨file, j, real, real2, -, -, -, T⟩ :=
      good_chains ⟨F.pol, F.lay, F.KL⟩ pl hp (table, d) hgood
    rw [hdepth, hk]
    exact readPlace_places T.place_read
  have hprf : ∀ π,
      typeFile (ckP f) a (dataAt a (dryKey k (key rec₀))) tFk tJk t3k silK (runKM Kc key k rec₀) sb
        cfg (frontK (table, d)) (joinK tJk (table, d)) (seamK t3k (table, d)) d.salt d.path d.r =
        some π →
      (Θ).prf (table, d) = π := fun π hπ =>
    typingKey_prf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (table, d) π
      hπ hplaces
  have AR : ∀ x : Dat, (x = (table, d) ∧
      TypedKey f a (dataAt a (dryKey k (key rec₀))) tFk tJk t3k silK (runKM Kc key k rec₀) sb cfg
        frontK (joinK tJk) (seamK t3k) x) → ∀ a' b' e', (Θ).RunsTo x a' b' e' →
      AfterRuns (Θ).F (Θ).g (Θ).sMT ((Θ).cmsAt x) ((Θ).xAt x) ((Θ).prf x) (bytesToDig x.2.seal1) a'
        b' e' := by
    rintro _ ⟨rfl, π, hπ⟩ a' b' e' ⟨h₁, h₂, h₃⟩
    rw [hprf π hπ] at h₁ h₂ h₃ ⊢
    exact after d hd π hπ a' b' e' h₁ h₂ h₃
  have e1 : keyShape ⟨F.pol, F.lay, F.KL⟩ = pl.chains.key.oneTime.binding := by
    unfold keyShape
    rw [hp]
  have holes : LeftHoles (Θ) (fun x : Dat => x = (table, d) ∧
      TypedKey f a (dataAt a (dryKey k (key rec₀))) tFk tJk t3k silK (runKM Kc key k rec₀) sb cfg
        frontK (joinK tJk) (seamK t3k) x) (keyShape ⟨F.pol, F.lay, F.KL⟩)
      (keyCfg ⟨F.pol, F.lay, F.KL⟩) :=
    { laws := typingKey_laws _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      wire := typingKey_wire _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (blocksM Kc f key k rec₀ c block z₀ p) (dataAt_work a (dryKey k (key rec₀)))
      depth := by
        rw [e1, ← hk, ← hdepth]
        rfl
      node := node
      leaf := leaf
      fits := by
        rintro _ ⟨rfl, -⟩
        exact fits d hd
      saltLen := by
        rintro _ ⟨rfl, -⟩
        exact saltLen d hd
      sealAt := fun x hg a' b' e' hr => (AR x hg a' b' e' hr).sealAt
      opened₁ := fun x hg a' b' e' hr => (AR x hg a' b' e' hr).opened₁
      opened₂ := fun x hg a' b' e' hr => (AR x hg a' b' e' hr).opened₂
      opened₃ := fun x hg a' b' e' hr => (AR x hg a' b' e' hr).opened₃
      openedE := fun x hg a' b' e' hr => (AR x hg a' b' e' hr).openedE
      walk₁ := fun x hg a' b' e' hr => (AR x hg a' b' e' hr).walk₁
      walk₂ := fun x hg a' b' e' hr => (AR x hg a' b' e' hr).walk₂
      walk₃ := fun x hg a' b' e' hr => (AR x hg a' b' e' hr).walk₃
      walkE := fun x hg a' b' e' hr => (AR x hg a' b' e' hr).walkE
      accept := fun x hg a' b' e' hr => (AR x hg a' b' e' hr).accept }
  obtain ⟨d', hd', hc, -, hy⟩ := key_det_good (Θ) F _ holes id table further h
  obtain rfl : d = d' := congrArg Prod.snd (Option.some.inj (hd.symm.trans hd'))
  refine ⟨d, hd, hc, (collides d hd).imp (fun hr => ?_) fun x => x⟩
  obtain ⟨π, hπ⟩ := Option.isSome_iff_exists.1
    ((typeFile_isSome (ckP f) a (dataAt a (dryKey k (key rec₀))) tFk tJk t3k silK
      (runKM Kc key k rec₀) sb cfg (frontK (table, d)) (joinK tJk (table, d))
      (seamK t3k (table, d)) d.salt d.path d.r).trans hr)
  have y := hy ⟨rfl, π, hπ⟩
  rw [hprf π hπ] at y
  exact ⟨π, hπ, vTA_of_verifyM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N
    early late P sb depthReq depthReqT depthReqL sFS cA g pp hMT hFS (bytesToDig table.root)
    (recOf table) π y⟩

/-- **Where the test `typeReturns` says yes, the first arm holds**: the sentence with its second arm
`False`. -/
theorem port_key_returns (pp : _root_.Compile.Params) (hMT : pp.sMT = 256 + 8 * sb)
    (hFS : pp.sFS = sFS)
    (F : OnBytes.K.Files) (pl : Model.Verify.Planned)
    (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok pl) (hk : k = pl.chains.key)
    (hdepth : depthReqT = k.oneTime.binding.logLeaves)
    (id : String) (table further : Params.TableName)
    (after : ∀ d, TieK.readKeyChains F.pol F.lay F.KL F.key = some (table, d) → ∀ π,
      typeFile (ckP f) a (dataAt a (dryKey k (key rec₀))) tFk tJk t3k silK (runKM Kc key k rec₀) sb
        cfg (frontK (table, d)) (joinK tJk (table, d)) (seamK t3k (table, d)) d.salt d.path d.r =
        some π →
      ∀ a' b' e',
      (run₁ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin (bytesToDig table.root :: cA (recOf table).2)
        (recOf table) π).det g = some a' →
      (run₂ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin (bytesToDig table.root :: cA (recOf table).2)
        (recOf table) π a').det g = some b' →
      (run₃ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin (bytesToDig table.root :: cA (recOf table).2)
        (recOf table) π a' b').det g = some e' →
      AfterRuns (𝔉) g (256 + 8 * sb) (bytesToDig table.root :: cA (recOf table).2) (recOf table) π
        (bytesToDig d.seal1) a' b' e')
    (node : NodeCoded (Θ).g (keyCfg ⟨F.pol, F.lay, F.KL⟩))
    (leaf : LeafCoded (Θ).g (keyShape ⟨F.pol, F.lay, F.KL⟩).logLeaves (keyCfg ⟨F.pol, F.lay, F.KL⟩)
      (keyShape ⟨F.pol, F.lay, F.KL⟩).saltBytes (Θ).rsOf)
    (fits : ∀ d, TieK.readKeyChains F.pol F.lay F.KL F.key = some (table, d) →
      TypedOracleCompiler.Joined.Fits (Θ).F ((Θ).k₁ (table, d)) ((Θ).k₂ (table, d)) ((Θ).k₃ (table, d)))
    (saltLen : ∀ d, TieK.readKeyChains F.pol F.lay F.KL F.key = some (table, d) →
      ((Θ).salt (table, d)).length = sFS)
    (returns : ∀ d, TieK.readKeyChains F.pol F.lay F.KL F.key = some (table, d) →
      typeReturns (ckP f) a (dataAt a (dryKey k (key rec₀))) sb cfg d.r = true)
    (h : OnBytes.K.PortYesAt F id table further) :
    KeySays Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P cfg
      sb depthReq depthReqT depthReqL recOf cA g pp F table False :=
  port_key Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P cfg sb
    depthReq depthReqT depthReqL sFS recOf cA g pp hMT hFS F pl hp hk hdepth id table further False
    after node leaf fits saltLen (fun d hd => .inl (returns d hd)) h

end OnBytes.Maker.Page
