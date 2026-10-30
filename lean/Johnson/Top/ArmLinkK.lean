-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmLinkK.lean: Link's compiled verifier without the strict format says yes at the object
whose Link is the written link over letters, at a wire with any number K of blocks that is at least
the description's own; and the hypothesis `link` of `EntryPart` (OnBytes/K/Parts.lean) there.

Johnson/Top/ArmLinkIs.lean (`vLA_sib`) and ArmLinkAt.lean (`link_field`) have both where K is the
description's own number `D.K` of blocks (`hKl`). Here that equation gives way to `D.K ≤ K`. The
texts are those files'; the pieces beneath are those at K: `sameRun_sibK`
(OnBytes/K/Arm/SameSibK.lean) and `link_armK_read` (OnBytes/K/Arm/LinkArmKAt.lean). For proofs only;
the program does not import this file.

Main theorems.
 `vLA_sibK`      the yes of `vLA'`. In the place of `hKl` and of "chal is the library's way at D.K":
                 `D.K ≤ K`; K + 1 is below 2 ^ 48; chal agrees with a way chalD over the
                 description's own kit (`hchal`) that fits the field's data (`hkit`) and whose wires
                 obey the sibling's laws (`wires`).
 `link_fieldK`   the field, at chalD := the library's way `chalP` at K blocks: `hkit` and `wires`
                 are shown. Asked in the place of `hKl`: `D.K ≤ K`; K + 1 is below 2 ^ 48.

What is not claimed. That the equations on the letters hold at any letters. That any K is the number
of blocks of a verifier of three files. The seeds' two tests. Nothing on soundness.


-/
import Johnson.Top.ArmLinkAt
import OnBytes.K.Arm.LinkArmKAt
import OnBytes.K.Arm.SameSibK

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

section SibK
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

/-- Link's compiled verifier without the strict format says yes at the object whose Link is the
written link over letters, at the wire with `wSib` and `bodiesSib` at K blocks, at the written
encoding with K + 1 blocks. The six equations on the letters: `hC`, `hds`, `ha`, `hxs`, `hchal`,
`hsalt`. The nine on the two typed strings: `h1` to `h9`. -/
theorem vLA_sibK (ha : a = D.a) (hxs : xs = D.xs) (hDK : D.K ≤ K)
    (chalD : ∀ e k, (Fin K → Dig 256) → D.C.Ch e k) (hchal : HEq chal chalD)
    (hkit : _root_.Run.PQ.KitFits D.base.plan.field D.C K chalD)
    (wires : (PQ.wqS D.C K chalD D.ds fun _ => true).OKG) (hsalt : salt = D.base.plan.salt)
    (back : StrCode (AllPts 256 (K + 1)
      (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds)))))
    {X' : Type} (dec : X' → View → Bool) (x : X') (F : FitsE D) (hK0 : K + 1 < 2 ^ 48)
    (first further : OnBytes.Params.TableName) (c₀ c₁ : Dig 256) (st : ByteArray)
    (o : _root_.Fmt.ChainOut) (run : ByteArray) (pls : Plains (PQ.uL D.C D.ds))
    (A : EntryRead D pd g first further c₀ c₁ ⟨{ D.base with statement := st }, D.stored⟩ o run
      pls)
    (rec rec' : Seed × Ans) (a₀ : tr rec.2 = first.answers.map E.triple)
    (a₁ : tr rec'.2 = further.answers.map E.triple) (π : OneProtocolProof 256 (PSXE D dec).up)
    (hπ : assembleS D dec o = some π) (hok : TypedOracleCompiler.Run.PQ.ok D.base = true)
    (hokb : TypedOracleCompiler.Run.PQ.ok
      (inFile ({ D.base with statement := st } : _root_.Fmt.Spec)) = true)
    (hn : D.base.rand.isNone = false) (okx : PQ.okX D.ds D.a D.xs = true)
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
  have hs := sameRun_sibK
    (L := (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))))
    C ds a xs K chal dec2 D dec x (rec, rec') hC hds ha hxs chalD hchal hdec2
    (TypedOracleCompiler.StringsList.embT salt C ds)
    (embS2 D d₁ (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds)))
      (Equiv.refl (List Bool)) hok)
    (embT_sib D C ds hok salt hC hds hsalt) id
    (fun z => (pbSib D C ds hC hds).symm
      (wayE D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) z))
    (way_sib D C ds (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) hC hds) πL π h1 h2 h3
    h4 h5 h6 h7 h8 h9
  exact link_armK_read D d₁ hcfg pd rest1 nb K
    (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds)))
    (pbSib D C ds hC hds) (Equiv.refl (List Bool)) p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA
    tr hinj hlen htr back g chalD dec x F hDK hK0 hkit wires first further c₀ c₁ st o run pls A
    rec.2 rec'.2 a₀ a₁ π hπ hok hokb hn okx hD honce hsame hnb hit TypedOracleCompiler.Strings.cX hdec
    (congrArg (fun n => twoExternalStrings (2 ^ n) SgX) ha)
    (batLC (LrG T) (_root_.Run.Twin.allLo (SOf C ds)))
    (wLC (wireOf2 (L := LrG T) (aT := aT) (aL := _root_.Run.Twin.allLo (SOf C ds)) (K + 1) wT
      (wSib T K chal) wB a depthReq depthReqT depthReqL (bodiesSib T salt embT prjT embB prjB)))
    (TypedOracleCompiler.StringsList.embT salt C ds) id (fun _ => none) (rec, rec') πL rfl
    (bodyS a salt).embE (heq_of_eq (embE_sib D a salt ha hsalt)) hs depthReqL

end SibK

section FieldK
open OnBytes.Slice OnBytes.Tie

variable (G : EntryGround) (Z : Pub) {I X RI : Type} [Fintype RI] [Nonempty RI] {a : ℕ}
  {C : CK} {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List XO}
  {dec2 : (SeedG G × AnsG G) × (SeedG G × AnsG G) → View → Bool}
  (T : RestR I X RI (SeedG G) (AnsG G) a (linkProtocolOfRoundData C ds a xs dec2))
  (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) {aT : RoundSplits T.test.shape}
  (wT : ProtocolQueryLayout 256 (K + 1) (batTC (LrG T) aT)) (wB : ProtocolQueryLayout 256 (K + 1) T.bat)
  (depthReq depthReqT depthReqL salt : ℕ)
  (embT : (p : OPos T.test.shape) → OSym T.test.shape p → List Bool)
  (prjT : (p : OPos T.test.shape) → List Bool → Option (OSym T.test.shape p))
  (embB : (p : OPos T.bat.loc.shape) → OSym T.bat.loc.shape p → List Bool)
  (prjB : (p : OPos T.bat.loc.shape) → List Bool → Option (OSym T.bat.loc.shape p))
  (d₁ : Sd1 G.q.link.table.cubeBits G.q.link.table.answers)
  (hcfg : (DG G Z).base.cfg.size = 32) (rest1 : ByteArray) (nb : ℕ)
  (hC : C = (DG G Z).C) (hds : ds = (DG G Z).ds)
  (p0 p1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) .test)
    (annOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) .test))
  (isP0 isP1 :
    PlainPart (shapeOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) .test)
    (annOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) .test) → Bool)
  (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (isPL : PlainPart (shapeOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) .link)
    (annOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) .link) → Bool)
  (hpL : ∀ p, isPL p = true ↔ p = (pbSib (DG G Z) C ds hC hds).symm
    (p0E (DG G Z) (earlyTwo (A := List T3 × List T3) d₁)
      (seedEntry G.q.link.table.cubeBits G.q.link.table.answers)))
  (cA : AnsG G → List (Dig 256))
  (hinj : Function.Injective cA) (hlen : ∀ a a', (cA a).length = (cA a').length)

/-- The hypothesis `link` of `EntryPart`, at the written link over letters, wired with K blocks. -/
theorem link_fieldK (hA : (G.q.link.table.answers == 0) = false) (hF : G.q.given.plan.field = .two)
    (hZ : G.SaysLines Z.pol)
    (HF : ∀ {F : Files} {id : String} {table further : Params.TableName},
      PortYesAt F id table further → G.SaysLines F.pol → ∀ c : ByteArray,
      Params.configurationDigest [F.pol, F.lay, F.KL] = c →
      ∃ (r : Entry.EntryRead) (l0 l1 : List (List E × E))
        (π : OneProtocolProof 256 (PSXE (entryXD G c) (decAt G c)).up),
        Entry.read (linkAtCfg G.q c) table F.ent = .ok r ∧ r.further = further ∧
        seedsUnder recordSeeds (linkAtCfg G.q c) table = some l0 ∧
        seedsUnder recordSeeds (linkAtCfg G.q c) further = some l1 ∧
        ArmFacts G c table further l0 l1 r.chain.out π)
    (ha : a = (DG G Z).a) (hxs : xs = (DG G Z).xs) (hDK : (DG G Z).K ≤ K) (hK0 : K + 1 < 2 ^ 48)
    (hchal : HEq chal (chalP (DG G Z).base.plan.field K))
    (hsalt : salt = (DG G Z).base.plan.salt) (hnb : nb = 8 * (DG G Z).base.plan.salt)
    (back : StrCode (AllPts 256 (K + 1)
      (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds)))))
    (hdec2 : ∀ rr, dec2 rr = decAt G Z.digest (recX rr))
    (str : OneProtocolProof 256 (PSXE (DG G Z) (decAt G Z.digest)).up →
      OneProtocolProof 256 (batLC (LrG T) (_root_.Run.Twin.allLo (SOf C ds)))) (hstr : StrLaws str) :
    ∀ (Fl : Files) (o : Model.Verify.Options) (id : String) (table further : Params.TableName)
      (r r' : RecP NZ G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers),
      o.id = some id → o.bits = 128 → PortYesAt Fl id table further →
      servedArm Z (stmOf Fl o) = true → recOfArm G Z (stmOf Fl o) table = some r →
      recOfArm G Z (stmOf Fl o) further = some r' →
      ∃ πL, (entArm G Z (decAt G Z.digest) (stmOf Fl o) Fl.key Fl.ent).map
          (fun u => (u.1, str u.2)) = some (further, πL) ∧
        (vLA' (wireOf2 (L := LrG T) (aT := aT) (aL := _root_.Run.Twin.allLo (SOf C ds)) (K + 1) wT
      (wSib T K chal) wB a depthReq depthReqT depthReqL (bodiesSib T salt embT prjT embB prjB))
          cA (bytesToDig table.root) (bytesToDig further.root) r r' πL).det
          (readBlocks (implL2 (DG G Z) d₁ (DG G Z).base.cfg hcfg (EntryRunTop.pdOf (DG G Z)) rest1
          (KeyLeaves.leavesAt (L0 (DG G Z) d₁) nb (DG G Z).base.cfg)
          (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds)))
          (pbSib (DG G Z) C ds hC hds) (Equiv.refl (List Bool)) p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest
          isPL hpL cA OnBytes.Flat.trAns hinj hlen trAns_sib_inj (K + 1) back) oBits) = true := by
  intro Fl o id table further r r' _ _ h hS hr hr'
  obtain ⟨e1, e2, e3⟩ := servedArm_pins hS
  have hl : G.SaysLines Fl.pol := servedArm_lines G hZ hS
  have ec : Params.configurationDigest [Fl.pol, Fl.lay, Fl.KL] = Z.digest := by
    show _ = Params.configurationDigest [Z.pol, Z.lay, Z.KL]
    rw [show Fl.pol = Z.pol from e1, show Fl.lay = Z.lay from e2, show Fl.KL = Z.KL from e3]
  obtain ⟨rd, l0, l1, π, hrd, -, s0, s1, A⟩ := HF h hl Z.digest ec
  obtain ⟨rd2, π2, hrd2, -, hπ2, hent⟩ :=
    entArm_port G hA h hl e1 e2 e3 (decAt G Z.digest) (stmOf Fl o)
  obtain rfl : rd2 = rd := Except.ok.inj (hrd2.symm.trans hrd)
  obtain rfl : π2 = π := Option.some.inj (hπ2.symm.trans A.typed)
  have er : recOne G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers table l0 =
      r := by
    unfold recOfArm at hr
    rw [s0] at hr
    exact Option.some.inj hr
  have er' : recOne G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers further l1 =
      r' := by
    unfold recOfArm at hr'
    rw [s1] at hr'
    exact Option.some.inj hr'
  subst er er'
  obtain ⟨n0, n1, k0, k1⟩ := answers_at G hA hF h hl
  have hx := recX_port G hA hF h hl l0 l1 rd2.chain.out
  obtain ⟨run, pls, R⟩ := A.read
  refine ⟨str π2, by rw [hent]; rfl, ?_⟩
  exact vLA_sibK T K chal wT wB depthReq depthReqT depthReqL salt embT prjT embB prjB (DG G Z) d₁
    hcfg (EntryRunTop.pdOf (DG G Z)) rest1 nb hC hds p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL
    cA OnBytes.Flat.trAns hinj hlen trAns_sib_inj oBits ha hxs hDK
    (chalP (DG G Z).base.plan.field K) hchal (_root_.Run.PQ.kit_pull (DG G Z).base.plan.field K)
    (wqS_okgP (DG G Z) K hDK A.ground.work) hsalt back (decAt G Z.digest)
    (xOfAskedC _ _ ⟨table, further, l0, l1, rd2.chain.out⟩) A.ground.fits hK0 table further
    _ _ (Params.Link.statement table further) rd2.chain.out run pls R _ _
    (trAns_anT _ _ _ n0 k0) (trAns_anT _ _ _ n1 k1) π2 A.typed A.ground.hok A.ground.hokb
    A.ground.hn A.ground.okx A.ground.hD A.ground.honce A.ground.hsame hnb
    A.ground.hit A.dec ((hdec2 _).trans (congrArg (decAt G Z.digest) hx)) (str π2)
    (hstr.salt π2) (hstr.roots π2) (hstr.plains π2) (hstr.opens π2) (hstr.ext π2) (hstr.rtreq π2)
    (hstr.slot π2) (hstr.path π2) (hstr.rsalt π2)

end FieldK

end OnBytes.K.Arm
