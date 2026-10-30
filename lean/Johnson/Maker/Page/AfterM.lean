-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/Page/AfterM.lean: at the two makers' values and an entry's part, and at the page's
value, the ten conditions of `AfterRuns` on what the compiled verifier of a key file, and of a proof
file, checks behind its three chains hold at the typing of a file that was read.

Johnson/Maker/Page/AfterG.lean has the ten fields of `AfterRuns` (OnBytes/TypedOracleCompiler/Joined/K/Left.lean)
under `gJ P Fmt.oracle` for a page P that is a letter, with premises on P. Here P is the page's
value `pageM` (Johnson/Maker/Page/At.lean) and the written files stand at the makers' own data,
decisions, letters and bodies (Johnson/EntryRec/AtMaker.lean, AtMakerA.lean). Paid here: the page's
digest and its field `leaf` (by unfolding); the read-back; that the page's family answers the file's
chain queries by the file's data as laid, and that the file's own queries are such queries
(Johnson/Maker/Page/At.lean); the two conditions on the round in which an instance is written (a key
file's queries hold no instance).

  `fileKeyM`, `fileProofM`   the two written files at the makers' values.
  `agreesM`            `LeafXAgrees` at the page's value, from one premise on its code of leaves.
  `afterRuns_keyM`     the ten fields at the key file.
  `afterRuns_proofM`   the ten fields at the proof file `fileProofA`.

The premises that stay. `PageOwes`. The dry run of the whole file at the key of the READING gives
the three lists of rounds (`hR`). The MAKERS' key has the item 0 and fits the shared chain's index
shape (`h0`, `hf`): then its dry run is the same (OnBytes/Maker/Page/OneData.lean), and so the
makers' data are the data of the file as read. For a proof file both dry runs stand at the makers'
block of the first chain; that this is the block of the reading is asked through `PageOwes` and `hR`
together, not shown. For a proof file: no round is named as the one in which an instance is written
late (`hl`). The page's field `leafX` is the code V of leaves, a free letter here. Of V it is asked
(`hV`): what it writes at a leaf query is the string of the page's own call there. That is a premise
on V, and through it on what the page's family answers at the leaves; it gives `LeafXAgrees` at all
bodies. Those of Johnson/Maker/Page/AfterG.lean on the interface, on the reading, on `typeFile`, the
silent rounds' test, the decision and the three chains' values under the page's family. None is
shown here.

Not claimed. `gJ P O` is a function of the typed query, no one-to-one coding (the head of
OnBytes/Maker/Page/Frame.lean). The fields of `Left` beside `after` (`laws`, `wire`, `fits`,
`saltLen`, `slotLt`, `pathLen`, `climb`): among them the climb in the request tree and the lengths
of the salt and the path, which the compiled verifier checks behind its chains too. Nothing on
soundness (index binding included), what a root fixes, opening-form binding, no two openings of a
commitment, correctness of extraction or whatever else names a committer or a prover.

-/
import Johnson.Maker.Page.AfterG
import Johnson.Maker.Page.At
import OnBytes.Maker.Page.OneData

set_option autoImplicit false

noncomputable section

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
  (cfg : ByteArray) (sR : ℕ) (req : ((filesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c
      block z₀ p N early
      late).withProvers P).XC → ByteArray × ByteArray)
  (p0 : PBt (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P)
      .test) (isP0 isP1 : PBt (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N
      early late P) .test → Bool) (cfgL : List (Dig 256))
  (sh : Rom.Bits) (hp0 : ∀ q, isP0 q = true ↔ q = p0) (hp1 : ∀ q, isP1 q = true ↔ q = p1M Kc f tFk
      tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P)
  (rest' : ByteArray) (Lk : LinkCode (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block
      z₀ p N early late P) (p.K + 1)) (V : Leaves (LM Kc f tFk tJk
      t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P))
  {file : ByteArray} {R₁ : Rounds} {dry : Proof.FirstEnd} {S₁ : Fmt.SpecX} {rr : Proof.TailRead}
  {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : Proof.SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds}
  {S₃ : Fmt.SpecX} {R₃ : Rounds}
  (sb depthReq depthReqT depthReqL : ℕ) (r₀ : Kc.conf.Rec)

/-- Where the code V of leaves writes the string of the page's own call, the page's value meets
`LeafXAgrees` at every body. -/
theorem agreesM
    (hV : ∀ q s c, V.lf.put q = some s → leafOf (fun b : List Bool => b) q = some c →
      bitsToBytes s = strOf c) (b : List Bool) :
    LeafXAgrees (pageM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late
      P cfg sR (_root_.Fmt.HO _root_.Fmt.oracle) req p0 isP0 isP1 cfgL sh hp0 hp1 rest' Lk V) b :=
  fun salt s c hs hc => hV ⟨b, salt⟩ s c hs hc

section Key

/-- The key file, written, at the makers' values, with strings of bits for bodies. -/
abbrev fileKeyM :=
  fileKey f p.K a (dataK Kc key k rec₀) (dataP Kc key c block z₀)
    tFk tJk t3k tFp tJp t3p silK (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding
      (lettersOf Kc f (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk
    tJk t3k tFp tJp t3p silK (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding N early
      late P) p.wL (List Bool) depthReq depthReqT depthReqL
    (bodiesF f a (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK (runKM
    Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding (lettersOf
    Kc f (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK (runKM Kc key
    k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding N early late P) sb (embStored a sb) (prjStored
      a sb))

/-- that file -/
local notation "𝔉" => fileKeyM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N
    early late P sb depthReq depthReqT depthReqL
/-- its rounds -/
local notation "𝒞" => chainsOf (ckP f) (dataK Kc key k rec₀) tFk tJk t3k
/-- the page's value -/
local notation "𝒜" => pageM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early
    late P cfg sR (_root_.Fmt.HO _root_.Fmt.oracle) req p0 isP0 isP1 cfgL sh hp0 hp1 rest' Lk V

/-- **All ten fields at the key file, at the makers' values and the page's value.** -/
theorem afterRuns_keyM {j : ℕ} (table : Params.TableName)
    (O : PageOwes (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime) file j R₁
      dry S₁ rr seal1 seal2 R₂ dry2 S₂ R₃' S₃ k.oneTime.given Params.labelOneTime
      (Params.OneTime.statement table) .inFile R₃ a sb p.K f cfg)
    (h0 : (key rec₀).item = 0) (hf : (key rec₀).fits (Key.tailPublic k table).lin.fold.index = true)
    (hR : dryKey k rr.key = some (R₁, R₂, R₃))
    (hV : ∀ q s c, V.lf.put q = some s → leafOf (fun b : List Bool => b) q = some c →
      bitsToBytes s = strOf c)
    (rest : List (Dig 256)) (x : Kc.conf.Rec) (π : (𝔉).Prf) (copy : ℕ)
    (pJ : JoinMsg (List E) ByteArray) (p3 : ByteArray) (hJ : joinOf table.answers rr = some pJ)
    (h3 : seamOf rr = some p3) (salt : ByteArray) (path : List ByteArray)
    (h : typeFile (ckP f) a (dataAt a (dryKey k (key rec₀))) tFk tJk t3k silK (runKM Kc key k rec₀)
      sb cfg (frontOf table.answers copy) pJ p3 salt path rr = some π)
    (z₁ : table.root.size = 32)
    (a' : Out 256 (𝒞).c₁) (b' : Out 256 (𝒞).c₂) (e' : Out 256 (𝒞).c₃)
    (h₁ : (run₁ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin (bytesToDig table.root :: rest) x π).det (gJ 𝒜
      _root_.Fmt.oracle) = some a')
    (h₂ : (run₂ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin (bytesToDig table.root :: rest) x π a').det (gJ
      𝒜 _root_.Fmt.oracle) = some b')
    (h₃ : (run₃ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin (bytesToDig table.root :: rest) x π a' b').det
      (gJ 𝒜 _root_.Fmt.oracle) = some e')
    (hsil : silK x (frontOf table.answers copy) pJ p3 = true)
    (hrun : ∀ v₁ v₂ v₃, ViewAlike (dropSeal rr.first.view) v₁ → ViewAlike rr.shared.view v₂ →
      ViewAlike rr.second.view v₃ → runKM Kc key k rec₀ x v₁ v₂ v₃ = true)
    (hz₀ : (Params.tableValue table).size < 2 ^ 64) :
    TypedOracleCompiler.Joined.K.AfterRuns (𝔉) (gJ 𝒜 _root_.Fmt.oracle) (256 + 8 * sb) (bytesToDig
              table.root :: rest) x π (bytesToDig seal1) a' b' e' :=
  have hW : dataAt a (dryKey k (key rec₀)) = Three.Whole.of R₁ R₂ R₃ :=
    (dataAt_read O.read h0 hf a k hR O.ok).2
  afterRuns_key_gJ f p.K a (dataAt a (dryKey k (key rec₀))) (dataP
    Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK (runKM Kc key k rec₀) silP (runPM Kc key c block
    z₀) p.toLinkProtocolWithLeafCoding (lettersOf Kc f (dataK Kc key k rec₀) (dataP Kc key c
    block z₀) tFk tJk t3k tFp tJp t3p silK (runKM Kc key k rec₀) silP (runPM Kc key c block z₀)
    p.toLinkProtocolWithLeafCoding N early late P) p.wL depthReq depthReqT
    depthReqL sb cfg k table O hW 𝒜 rfl rfl (fun _ _ => agreesM Kc f tFk tJk t3k tFp tJp t3p silK
      silP key k rec₀ c block z₀ p N early late P cfg sR req p0 isP0 isP1 cfgL sh hp0 hp1 rest' Lk
      V hV _) (fun _ _ _ s c
      hs hc => hV _ s c hs hc) (fun _ _ => agreesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀
        c block z₀ p N early late P cfg sR req p0 isP0 isP1 cfgL sh hp0 hp1 rest' Lk V hV _) (fun
        _ _ s c hs hc => hV _ s
      c hs hc) (rdK Kc f tFk tJk t3k tFp tJp t3p silK
    silP key k rec₀ c block z₀ p N early late P) (Quiet (LM Kc f tFk tJk t3k tFp tJp t3p silK silP
    key k rec₀ c block z₀ p N early late P) p0 (p1M Kc f tFk tJk t3k tFp tJp t3p silK silP key k
    rec₀ c block z₀ p N early late P) isP0 isP1 cfgL sh hp0 hp1 rest' (p.K + 1)) (hrdK Kc f tFk tJk
      t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late
    P) (speaksK Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P cfg
    sR (_root_.Fmt.HO _root_.Fmt.oracle) req p0 isP0 isP1 cfgL sh hp0 hp1 rest' Lk V
    _root_.Fmt.oracle) (fun cms x salt rtreq ρ0 c' pF pJ p3 => quietK Kc f tFk tJk t3k tFp tJp t3p
    silK silP key k rec₀ c block z₀ p N early late P (_root_.Fmt.HO _root_.Fmt.oracle) p0 isP0
    isP1 cfgL sh hp0 hp1 rest' cms x salt rtreq ρ0 c' pF pJ p3) rest x π copy pJ p3 hJ h3 salt path
    h z₁ (Or.inl rfl) (Or.inl rfl) a' b' e' h₁ h₂ h₃ hsil hrun hz₀

end Key

section Proof

/-- The proof file, written, at the makers' values, with strings of bits for bodies. -/
abbrev fileProofM :=
  fileProofA f p.K a (dataK Kc key k rec₀) (dataP Kc key c block z₀)
    tFk tJk t3k tFp tJp t3p silK (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding
      (lettersOf Kc f (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk
    tJk t3k tFp tJp t3p silK (runKM Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding N early
      late P) p.wL (List Bool) depthReq depthReqT depthReqL
    (bodiesF f a (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK (runKM
    Kc key k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding (lettersOf
    Kc f (dataK Kc key k rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK (runKM Kc key
    k rec₀) silP (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding N early late P) sb (embStored a sb) (prjStored
      a sb)) r₀

/-- that file -/
local notation "𝔉" => fileProofM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N
    early late P sb depthReq depthReqT depthReqL r₀
/-- its rounds -/
local notation "𝒞" => chainsOf (ckP f) (dataP Kc key c block z₀) tFp tJp t3p
/-- the page's value -/
local notation "𝒜" => pageM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early
    late P cfg sR (_root_.Fmt.HO _root_.Fmt.oracle) req p0 isP0 isP1 cfgL sh hp0 hp1 rest' Lk V

/-- **All ten fields at the proof file, at the makers' values and the page's value.** -/
theorem afterRuns_proofM {j : ℕ} (table : Params.TableName) (copy : ℕ) (request words : ByteArray)
    (blk :
    Blk Proof.FirstEnd)
    (O : PageOwes (Proof.tailPublic c table) blk (Proof.firstStart c.first) file j R₁ dry S₁ rr
      seal1 seal2 R₂ dry2 S₂ R₃' S₃ c.first.given Params.labelFirst (Params.First.statement table
      copy request words) .inFile R₃ a sb p.K f cfg)
    (h0 : (key z₀.2).item = 0)
    (hf : (key z₀.2).fits (Proof.tailPublic c table).lin.fold.index = true)
    (hR : dryProof c rr.key (block z₀.1) = some (R₁, R₂, R₃))
    (hV : ∀ q s c, V.lf.put q = some s → leafOf (fun b : List Bool => b) q = some c →
      bitsToBytes s = strOf c)
    (rest : List (Dig 256)) (x : Kc.conf.X × Kc.conf.Rec)
    (hreq : ((((𝔉).xin x).map (LM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N
      early late P).early).map req).getD default = (request, words)) (π : (𝔉).Prf)
    (pJ : JoinMsg (List E) ByteArray) (p3 : ByteArray) (hJ : joinOf table.answers rr = some pJ)
    (h3 : seamOf rr = some p3) (salt : ByteArray) (path : List ByteArray)
    (h : typeFile (ckP f) a (dataAt a (dryProof c (key z₀.2) (block z₀.1))) tFp tJp t3p silP (runPM
      Kc key c block z₀) sb cfg (frontOf table.answers copy) pJ p3 salt path rr = some π)
    (z₁ : table.root.size = 32)
    (hl : late = none)
    (a' : Out 256 (𝒞).c₁) (b' : Out 256 (𝒞).c₂) (e' : Out 256 (𝒞).c₃)
    (h₁ : (run₁ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin (bytesToDig table.root :: rest) x π).det (gJ 𝒜
      _root_.Fmt.oracle) = some a')
    (h₂ : (run₂ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin (bytesToDig table.root :: rest) x π a').det (gJ
      𝒜 _root_.Fmt.oracle) = some b')
    (h₃ : (run₃ (𝔉).t (𝔉).D (𝔉).wq (𝔉).embP (𝔉).xin (bytesToDig table.root :: rest) x π a' b').det
      (gJ 𝒜 _root_.Fmt.oracle) = some e')
    (hsil : silP x (frontOf table.answers copy) pJ p3 = true)
    (hrun : ∀ v₁ v₂ v₃, ViewAlike (dropSeal rr.first.view) v₁ → ViewAlike rr.shared.view v₂ →
      ViewAlike rr.second.view v₃ → runPM Kc key c block z₀ x v₁ v₂ v₃ = true)
    (hz₀ : (Params.tableValue table).size < 2 ^ 64) :
    TypedOracleCompiler.Joined.K.AfterRuns (𝔉) (gJ 𝒜 _root_.Fmt.oracle) (256 + 8 * sb) (bytesToDig
              table.root :: rest) x π (bytesToDig seal1) a' b' e' :=
  have hW : dataAt a (dryProof c (key z₀.2) (block z₀.1)) = Three.Whole.of R₁ R₂ R₃ :=
    (dataAt_readP O.read h0 hf a c (block z₀.1) hR O.ok).2
  afterRuns_proof_gJ f p.K a (dataK Kc key k rec₀) (dataAt a
    (dryProof c (key z₀.2) (block z₀.1))) tFk tJk t3k tFp tJp t3p silK (runKM Kc key k rec₀) silP
    (runPM Kc key c block z₀) p.toLinkProtocolWithLeafCoding (lettersOf Kc f (dataK Kc key k
    rec₀) (dataP Kc key c block z₀) tFk tJk t3k tFp tJp t3p silK (runKM Kc key k rec₀) silP (runPM
    Kc key c block z₀) p.toLinkProtocolWithLeafCoding N early late P) p.wL
    depthReq depthReqT depthReqL sb r₀ cfg c table copy request words blk req O hW 𝒜 rfl rfl
    (fun _ _ => agreesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early
      late P cfg sR req p0 isP0 isP1 cfgL sh hp0 hp1 rest' Lk V hV _) (fun _ _ => agreesM Kc f tFk
      tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P cfg sR req p0 isP0 isP1
      cfgL sh hp0 hp1 rest' Lk V hV _)
    (fun _ _ => agreesM Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early
      late P cfg sR req p0 isP0 isP1 cfgL sh hp0 hp1 rest' Lk V hV _) (fun _ => agreesM Kc f tFk tJk
      t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P cfg sR req p0 isP0 isP1
      cfgL sh hp0 hp1 rest' Lk V hV _) (rdP Kc f tFk tJk
      t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P) (fun _
    => True) (hrdP Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P)
    (speaksP Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀ c block z₀ p N early late P cfg sR
    (_root_.Fmt.HO _root_.Fmt.oracle) req p0 isP0 isP1 cfgL sh hp0 hp1 rest' Lk V _root_.Fmt.oracle)
    (fun cms x salt rtreq ρ0 c' pF pJ p3 => quietP Kc f tFk tJk t3k tFp tJp t3p silK silP key k rec₀
    c block z₀ p N early late P (_root_.Fmt.HO _root_.Fmt.oracle) req cms x salt rtreq ρ0 c' pF pJ
    p3) rest x hreq π pJ p3 hJ h3 salt path h z₁ (Or.inr fun n _ e => by subst hl; cases e) (Or.inr
      fun n _ e => by subst hl; cases e) a' b' e' h₁ h₂ h₃ hsil hrun hz₀

end Proof

end OnBytes.Maker.Page
