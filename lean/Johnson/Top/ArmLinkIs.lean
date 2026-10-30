-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmLinkIs.lean: Link's compiled verifier without the strict format, with the answers
alone in its list (`vLA'`, Johnson/TypedOracleCompiler/RecCompile/LinkAns.lean), says yes at an object with records
L and a wire W, at the typed oracle functions that the written encoding `ArmRead.implL2` reads out
of an oracle g: from one reading of the entry's chain at the hash over g.

What it is for: the same compiled verifier's entry arm (the two seeds' tests and the lax Link), run
at an object whose link is written at the shape at which the program's reader is tied; it is not yet
the object of the top's description. Here stands the lax Link alone.

`vLA'` is, by unfolding, `verifyB` (OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) at Link with its
annotation (`batLC L aL`), Link's wire record (`wLC W`), the wire's maps, the identity on plain
parts, nothing in the field x of the first query, and the list "the two roots, then both records'
answers as digests". That is the left side of `link_arm2` (OnBytes/K/Arm/LinkArm2.lean) at the
interface `typedOracleCarrier L Bd aT aL`. L, W and the object T are letters. For proofs only; the program
does not import this file.

The theorems speak only where `back` exists: a one-to-one writing, with a parser, of all typed
queries of the interface, so also of the instances and of the plain parts of the key file's and the
proof file's protocols. No file shows one at a written object.

Main theorems.
 `vLA_arm`        the yes of `vLA'` at letters L and W. Asked beside what `link_debts` asks: the
                  kind of L's external strings and W's number of blocks are the skeleton's (`hE`,
                  `hK`); `SameRun2` between (Link at the pair of records, Link's wire record, the
                  wire's map of symbols, the identity, the typed string) and (the skeleton at x, its
                  wiring, embS, the way `wayE` of plain parts and then back along pbF, π), once both
                  instances are fixed (`hs`); the wire's map of stored symbols agrees with embE
                  (`hemb`).
 `wLC_sib`        at an object `LrG T` (Johnson/EntryRec/Defs.lean) whose Link is the written link
                  over letters, and the wire `wireOf2 .. (wSib T K chal) ..`
                  (Johnson/EntryRec/WiringOfTypedOracleCarrier.lean, OklaSib.lean), Link's wire record is `sibW`
                  (OnBytes/K/Arm/SameSib.lean). By unfolding. That Link with the marks `Twin.allLo`
                  is `sibQ` stands in Johnson/Flat/ArmString.lean (`batLC_sib`).
 `vLA_sib`        the yes of `vLA'` at that object and wire, with bodies that are strings of bits
                  (`bodiesSib`), at the written encoding with pbF := `pbSib`, bd := the identity,
                  and the total code `Strings.cX` of stored symbols. The walks are paid from the
                  reading (`link_arm2_read`, OnBytes/K/Arm/LinkArmRead.lean). Of the twenty
                  equations of `SameRun2` eleven are paid from "the letters are the description's
                  own". Asked: what `link_arm2_read` asks of description, reading and typed answers;
                  seven equations on the letters; the two decisions agree at the two instances; the
                  nine equations between the two typed strings; `back`.

What is not claimed. That any premise holds at a file or at a written L and W. That `back` exists.
The seeds' two tests. Nothing on soundness.


-/
import OnBytes.K.Arm.LinkArmRead
import OnBytes.K.Arm.SameSib
import OnBytes.K.Arm.SibMaps
import Johnson.TypedOracleCompiler.RecCompile.LinkAns
import Johnson.EntryRec.OklaSib

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Compile.Batch.Cms OnBytes.K.Left OnBytes.Flat OnBytes.RunA
open TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.RowsE2 TypedOracleCompiler.Run.EntryFb
open TypedOracleCompiler.Slice.EntryFill TypedOracleCompiler.Slice.EntryChain TypedOracleCompiler.Slice.ArmRead
open TypedOracleCompiler.Compile.Batch.Carry
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD SOf inFile bodyS)
open OnBytes.Slice (seedEntry)
open OnBytes.K (fixB fixW fixP)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (View SgX CK XO)

variable {I0 X0 : Type} (L : HolographicProtocol I0 X0) (Bd : Type) (aT : RoundSplits L.offline.shape)
  (aL : RoundSplits L.link.shape) (W : QueryLayout 256 (typedOracleCarrier L Bd aT aL))
  {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (pd : Dig 256) (rest1 : ByteArray) (V : Leaves (Ls D d₁))
  (pbF : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .link) (annOf (typedOracleCarrier L Bd aT aL) .link) ≃
    PlainPart (shapeOf (Ls D d₁) .link) (annOf (Ls D d₁) .link))
  (bd : (typedOracleCarrier L Bd aT aL).Bd ≃ (Ls D d₁).Bd)
  (p0 p1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .test) (annOf (typedOracleCarrier L Bd aT aL) .test))
  (isP0 isP1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .test) (annOf (typedOracleCarrier L Bd aT aL) .test) → Bool)
  (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (isPL : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .link) (annOf (typedOracleCarrier L Bd aT aL) .link) → Bool)
  (hpL : ∀ p, isPL p = true ↔
    p = pbF.symm (p0E D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s)))
  (cA : L.OutOfDomainAnswer → List (Dig 256)) (tr : L.OutOfDomainAnswer → List T3) (hinj : Function.Injective cA)
  (hlen : ∀ a a', (cA a).length = (cA a').length) (htr : Function.Injective tr)
  (g : Fam (rom 256))

/-- **Link's compiled verifier without the strict format says yes**, at the written encoding with
W's number of blocks. -/
theorem vLA_arm (hK : W.K = D.K + 1) (back : StrCode (AllPts 256 W.K (typedOracleCarrier L Bd aT aL)))
    {X : Type} (dec : X → View → Bool) (x : X) (F : FitsE D) (hK0 : D.K + 1 < 2 ^ 48)
    (first further : OnBytes.Params.TableName) (c₀ c₁ : Dig 256) (st : ByteArray)
    (o : _root_.Fmt.ChainOut) (run : ByteArray) (pls : Plains (PQ.uL D.C D.ds))
    (A : EntryRead D pd g first further c₀ c₁ ⟨{ D.base with statement := st }, D.stored⟩ o run
      pls)
    (rec rec' : L.Rec) (a₀ : tr rec.2 = first.answers.map E.triple)
    (a₁ : tr rec'.2 = further.answers.map E.triple) (π : OneProtocolProof 256 (PSXE D dec).up)
    (hπ : assembleS D dec o = some π) (hok : TypedOracleCompiler.Run.PQ.ok D.base = true)
    (hokb : TypedOracleCompiler.Run.PQ.ok
      (inFile ({ D.base with statement := st } : _root_.Fmt.Spec)) = true)
    (hn : D.base.rand.isNone = false) (work : ∀ r ∈ D.ds, r.entry.work ≤ 64)
    (okx : PQ.okX D.ds D.a D.xs = true)
    (hD : ∀ t ∈ D.stored.flatten, t.sh.a = D.a ∧ t.item ≤ 1)
    (honce : (D.stored.flatten.map (·.item == 1)).Nodup)
    (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
      OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body (typedOracleCarrier L Bd aT aL))
    (embE : SgX → Body (typedOracleCarrier L Bd aT aL))
    (walks : ArmWalks.Walks D
      (readBlocks (implL2 D d₁ cfg hcfg pd rest1 V (typedOracleCarrier L Bd aT aL) pbF bd p0 p1 isP0 isP1 cfgL
        sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr (D.K + 1) (hK ▸ back)) g) embS embE
      (c₀ :: c₁ :: (cA rec.2 ++ cA rec'.2)) o)
    (hdec : dec x (_root_.Fmt.viewX ⟨{ D.base with statement := st }, D.stored⟩ o) = true)
    (hE : twoExternalStrings L.wordLength L.Symbol = twoExternalStrings (2 ^ D.a) SgX) (πL : OneProtocolProof 256 (batLC L aL))
    (hemb : HEq W.embE embE)
    (hs : SameRun2 (L := typedOracleCarrier L Bd aT aL) (t := .link) (fixB (batLC L aL) (rec, rec'))
      (fixB (PSXE D dec).up x) (fixW (wLC W) (rec, rec')) (fixW (wqXE D dec) x) W.embL embS id
      (fun z => pbF.symm (wayE D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) z))
      (fixP πL (rec, rec')) (fixP π x)) :
    (vLA' W cA c₀ c₁ rec rec' πL).det
      (readBlocks (implL2 D d₁ cfg hcfg pd rest1 V (typedOracleCarrier L Bd aT aL) pbF bd p0 p1 isP0 isP1 cfgL
        sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr W.K back) g) = true :=
  link_arm2 D d₁ cfg hcfg pd rest1 V (typedOracleCarrier L Bd aT aL) pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1
    rest isPL hpL cA tr hinj hlen htr g hK back dec x F hK0 first further c₀ c₁ st o run pls A rec.2
    rec'.2 a₀ a₁ π hπ hok hokb hn work okx hD honce embS embE walks hdec hE (batLC L aL) (wLC W)
    W.embL id (fun _ => none) (rec, rec') πL rfl W.embE hemb hs W.depthReqL

/-! ## At the object whose Link is the written link over letters -/

section Sib
variable {I X RI Seed Ans : Type} [Fintype RI] [Nonempty RI] [Fintype Seed] [Nonempty Seed] {a : ℕ}
  {C : CK} {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List XO}
  {dec2 : (Seed × Ans) × (Seed × Ans) → View → Bool}
  (T : RestR I X RI Seed Ans a (linkProtocolOfRoundData C ds a xs dec2))
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)

variable {aT : RoundSplits T.test.shape}
  (wT : ProtocolQueryLayout 256 (K + 1) (batTC (LrG T) aT)) (wB : ProtocolQueryLayout 256 (K + 1) T.bat)
  (depthReq depthReqT depthReqL salt : ℕ)
  (embT : (p : OPos T.test.shape) → OSym T.test.shape p → List Bool)
  (prjT : (p : OPos T.test.shape) → List Bool → Option (OSym T.test.shape p))
  (embB : (p : OPos T.bat.loc.shape) → OSym T.bat.loc.shape p → List Bool)
  (prjB : (p : OPos T.bat.loc.shape) → List Bool → Option (OSym T.bat.loc.shape p))

/-- Link's wire record is `sibW`. -/
theorem wLC_sib :
    wLC (wireOf2 (L := LrG T) (aT := aT) (aL := _root_.Run.Twin.allLo (SOf C ds)) (K + 1) wT
      (wSib T K chal) wB a depthReq depthReqT depthReqL (bodiesSib T salt embT prjT embB prjB)) =
      sibW C ds a xs K chal dec2 := rfl

variable {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) (hcfg : D.base.cfg.size = 32) (pd : Dig 256)
  (rest1 : ByteArray) (nb : ℕ) (hC : C = D.C) (hds : ds = D.ds)
  (p0 p1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) .test)
    (annOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) .test))
  (isP0 isP1 :
    PlainPart (shapeOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) .test)
    (annOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) .test) → Bool)
  (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (isPL : PlainPart (shapeOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) .link)
    (annOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) .link) → Bool)
  (hpL : ∀ p, isPL p = true ↔ p = (pbSib D C ds hC hds).symm
    (p0E D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s)))
  (cA : Ans → List (Dig 256)) (tr : Ans → List T3) (hinj : Function.Injective cA)
  (hlen : ∀ a a', (cA a).length = (cA a').length) (htr : Function.Injective tr)
  (g : Fam (rom 256))

/-- **Link's compiled verifier without the strict format says yes at the object whose Link is the
written link over letters**, at the wire with `wSib` and `bodiesSib`, at the written encoding. The
seven equations on the letters: `hC`, `hds`, `ha`, `hxs`, `hKl`, `hchal`, `hsalt`. The nine on the
two typed strings: `h1` to `h9`. -/
theorem vLA_sib (ha : a = D.a) (hxs : xs = D.xs) (hKl : K = D.K)
    (hchal : HEq chal (chalP D.base.plan.field D.K)) (hsalt : salt = D.base.plan.salt)
    (back : StrCode (AllPts 256 (K + 1)
      (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds)))))
    {X' : Type} (dec : X' → View → Bool) (x : X') (F : FitsE D) (hK0 : D.K + 1 < 2 ^ 48)
    (first further : OnBytes.Params.TableName) (c₀ c₁ : Dig 256) (st : ByteArray)
    (o : _root_.Fmt.ChainOut) (run : ByteArray) (pls : Plains (PQ.uL D.C D.ds))
    (A : EntryRead D pd g first further c₀ c₁ ⟨{ D.base with statement := st }, D.stored⟩ o run
      pls)
    (rec rec' : Seed × Ans) (a₀ : tr rec.2 = first.answers.map E.triple)
    (a₁ : tr rec'.2 = further.answers.map E.triple) (π : OneProtocolProof 256 (PSXE D dec).up)
    (hπ : assembleS D dec o = some π) (hok : TypedOracleCompiler.Run.PQ.ok D.base = true)
    (hokb : TypedOracleCompiler.Run.PQ.ok
      (inFile ({ D.base with statement := st } : _root_.Fmt.Spec)) = true)
    (hn : D.base.rand.isNone = false) (work : ∀ r ∈ D.ds, r.entry.work ≤ 64)
    (okx : PQ.okX D.ds D.a D.xs = true)
    (hD : ∀ t ∈ D.stored.flatten, t.sh.a = D.a ∧ t.item ≤ 1)
    (honce : (D.stored.flatten.map (·.item == 1)).Nodup)
    (hsame : ∀ t ∈ D.stored.flatten, t.sh.a = D.a ∧ t.salt = D.base.plan.salt)
    (hnb : nb = 8 * D.base.plan.salt)
    (hit : ∀ t ∈ D.stored.flatten, _root_.Fmt.itemRoot st t.item =
      some (if t.item == 1 then further.root else first.root))
    (hdec : dec x (_root_.Fmt.viewX ⟨{ D.base with statement := st }, D.stored⟩ o) = true)
    (hdec2 : dec2 (rec, rec') = dec x)
    (πL : OneProtocolProof 256 (batLC (LrG T) (_root_.Run.Twin.allLo (SOf C ds))))
    (h1 : πL.salt = π.salt) (h2 : πL.roots = π.roots) (h3 : HEq πL.plains π.plains)
    (h4 : HEq πL.opens π.opens) (h5 : HEq πL.ext π.ext) (h6 : πL.rtreq = π.rtreq)
    (h7 : πL.slot = π.slot) (h8 : πL.path = π.path) (h9 : πL.rsalt = π.rsalt) :
    (vLA' (wireOf2 (L := LrG T) (aT := aT) (aL := _root_.Run.Twin.allLo (SOf C ds)) (K + 1) wT
      (wSib T K chal) wB a depthReq depthReqT depthReqL (bodiesSib T salt embT prjT embB prjB))
      cA c₀ c₁ rec rec' πL).det
      (readBlocks (implL2 D d₁ D.base.cfg hcfg pd rest1 (KeyLeaves.leavesAt (L0 D d₁) nb D.base.cfg)
        (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds)))
        (pbSib D C ds hC hds) (Equiv.refl (List Bool)) p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL
        cA tr hinj hlen htr (K + 1) back) g) = true := by
  have hs := sameRun_sib
    (L := (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))))
    C ds a xs K chal dec2 D dec x (rec, rec') hC hds ha hxs hKl hchal hdec2
    (TypedOracleCompiler.StringsList.embT salt C ds)
    (embS2 D d₁ (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds)))
      (Equiv.refl (List Bool)) hok)
    (embT_sib D C ds hok salt hC hds hsalt) id
    (fun z => (pbSib D C ds hC hds).symm
      (wayE D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) z))
    (way_sib D C ds (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) hC hds) πL π h1 h2 h3
    h4 h5 h6 h7 h8 h9
  exact link_arm2_read D d₁ hcfg pd rest1 nb
    (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds)))
    (pbSib D C ds hC hds) (Equiv.refl (List Bool)) p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA
    tr hinj hlen htr g (congrArg (· + 1) hKl) back dec x F hK0 first further c₀ c₁ st o run pls A
    rec.2 rec'.2 a₀ a₁ π hπ hok hokb hn work okx hD honce hsame hnb hit TypedOracleCompiler.Strings.cX hdec
    (congrArg (fun n => twoExternalStrings (2 ^ n) SgX) ha)
    (batLC (LrG T) (_root_.Run.Twin.allLo (SOf C ds)))
    (wLC (wireOf2 (L := LrG T) (aT := aT) (aL := _root_.Run.Twin.allLo (SOf C ds)) (K + 1) wT
      (wSib T K chal) wB a depthReq depthReqT depthReqL (bodiesSib T salt embT prjT embB prjB)))
    (TypedOracleCompiler.StringsList.embT salt C ds) id (fun _ => none) (rec, rec') πL rfl
    (bodyS a salt).embE (heq_of_eq (embE_sib D a salt ha hsalt)) hs depthReqL

end Sib

end OnBytes.K.Arm
