-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ArmLinkAt.lean: the hypothesis `link` of `EntryPart` (OnBytes/K/Parts.lean), in its own
words, at an object whose Link is the written link over letters, the wire with `wSib` and
`bodiesSib`, the written encoding `ArmRead.implL2`, and the three definitions of
OnBytes/K/ArmLetters.lean (`servedArm`, `recOfArm`, `entArm`): at a yes of the program on a served
statement the reading gives the program's own further table and a typed string, and Link's compiled
verifier without the strict format says yes on it.

What it is for: the same compiled verifier's entry arm (the two seeds' tests and the lax Link), run
at an object whose link is written at the shape at which the program's reader is tied; it is not yet
the object of the top's description. Here stands the lax Link alone.

The pieces. The yes of `vLA'`: Johnson/Top/ArmLinkIs.lean (`vLA_sib`). What a yes of the program
gives at a ground: OnBytes/K/Arm/ArmFacts.lean (`ArmFacts`), taken here as the hypothesis `HF` in
the words of `armFacts_full` and `armFacts_small`. The reading and the records:
OnBytes/K/ArmLetters.lean. The instance made of two records, and the answers as triples:
OnBytes/Flat/LinkSib.lean, LinkSibFit.lean, OnBytes/K/Left/SibFit.lean. The typed string at the
object's type is a letter `str` with nine laws (`StrLaws`). The object T, the wire's records, `str`,
the code cA of the answers and `back` are letters. For proofs only; the program does not import this
file.

The theorem speaks only where `back` exists: a one-to-one writing, with a parser, of all typed
queries of the interface, so also of the instances and of the plain parts of the key file's and the
proof file's protocols. No file shows one at a written object. The types of T, of the two records,
of d₁, cA and `str` hold the ground's three numbers (of rows' bits, of a cube's bits, of answers);
the written objects hold numerals: they meet by unfolding (`seedG_full` and its like,
Johnson/Top/ArmLinkSizes.lean).

Main definitions: `StrLaws`, `SeedG`, `AnsG`, `DG`.
Main theorem.
 `link_field`     the field. Asked: of the ground G: it has answers; its field is the one of two
                  words; Z's parameter file says G's lines; `HF`. Seven equations: the letters C,
                  ds, a, xs, K, chal, salt are those of the description `DG G Z`. The object's
                  decision at a pair of records is the run's decision at the instance made of the
                  pair (`hdec2`). `StrLaws str`. cA is one to one, with one number of digests.
                  Choices of the written encoding: nb = 8 * salt; d₁, hcfg, rest1; the seeds' data
                  p0, p1, isP0, isP1, cfgL, sh, rest; the test isPL of the first plain part; `back`.

What is not claimed. That the seven equations hold at any letters. That any Z's parameter file says
the ground's lines: until one does, no statement is served. That `back` exists. The seeds' two
tests. Nothing on soundness.


-/
import Johnson.Top.ArmLinkIs
import OnBytes.K.Arm.LinkArmAt
import OnBytes.K.ArmLetters
import OnBytes.Flat.LinkSibFit

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Compile.Batch.Cms OnBytes.K.Left OnBytes.Flat OnBytes.RunA OnBytes.Slice
open TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.RowsE2 TypedOracleCompiler.Run.EntryFb
open TypedOracleCompiler.Slice.EntryFill TypedOracleCompiler.Slice.EntryChain TypedOracleCompiler.Slice.ArmRead
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD SOf)
open OnBytes.Tie
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (View SgX CK XO)

/-- A way from typed strings of one protocol to typed strings of another keeps all nine fields. -/
structure StrLaws {Y Y' : Type} {E E' : ExtSpec} {Q : BatchInteractiveOracleProof Y E} {Q' : BatchInteractiveOracleProof Y' E'}
    (str : OneProtocolProof 256 Q → OneProtocolProof 256 Q') : Prop where
  salt : ∀ π, (str π).salt = π.salt
  roots : ∀ π, (str π).roots = π.roots
  plains : ∀ π, HEq (str π).plains π.plains
  opens : ∀ π, HEq (str π).opens π.opens
  ext : ∀ π, HEq (str π).ext π.ext
  rtreq : ∀ π, (str π).rtreq = π.rtreq
  slot : ∀ π, (str π).slot = π.slot
  path : ∀ π, (str π).path = π.path
  rsalt : ∀ π, (str π).rsalt = π.rsalt

/-- The seeds of one table's record, at a ground's numbers. -/
abbrev SeedG (G : EntryGround) : Type :=
  Fin G.q.link.table.answers → (Fin G.q.link.table.cubeBits → GE) × NZ

/-- The typed answers of one table's record, at a ground's numbers. -/
abbrev AnsG (G : EntryGround) : Type :=
  (Fin G.q.link.table.v → Bool) × Fin G.q.link.table.answers → GE

/-- The typed description of the entry's chain at a ground and the digest of three public files. It
is fixed before any run of the program. It is not fixed before the hash function: the digest of the
three files (`Params.configurationDigest`) and the digest of the parameters that the encoding holds
beside it (`EntryRunTop.pdOf`) are values of the program's own hash. -/
abbrev DG (G : EntryGround) (Z : Pub) : XD := entryXD G Z.digest

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

/-- **The hypothesis `link` of `EntryPart`, at the written link over letters.** -/
theorem link_field (hA : (G.q.link.table.answers == 0) = false) (hF : G.q.given.plan.field = .two)
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
    (ha : a = (DG G Z).a) (hxs : xs = (DG G Z).xs) (hKl : K = (DG G Z).K)
    (hchal : HEq chal (chalP (DG G Z).base.plan.field (DG G Z).K))
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
  exact vLA_sib T K chal wT wB depthReq depthReqT depthReqL salt embT prjT embB prjB (DG G Z) d₁
    hcfg (EntryRunTop.pdOf (DG G Z)) rest1 nb hC hds p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL
    cA OnBytes.Flat.trAns hinj hlen trAns_sib_inj oBits ha hxs hKl hchal hsalt back
    (decAt G Z.digest)
    (xOfAskedC _ _ ⟨table, further, l0, l1, rd2.chain.out⟩) A.ground.fits A.ground.hK table further
    _ _ (Params.Link.statement table further) rd2.chain.out run pls R _ _
    (trAns_anT _ _ _ n0 k0) (trAns_anT _ _ _ n1 k1) π2 A.typed A.ground.hok A.ground.hokb
    A.ground.hn A.ground.work A.ground.okx A.ground.hD A.ground.honce A.ground.hsame hnb
    A.ground.hit A.dec ((hdec2 _).trans (congrArg (decAt G Z.digest) hx)) (str π2)
    (hstr.salt π2) (hstr.roots π2) (hstr.plains π2) (hstr.opens π2) (hstr.ext π2) (hstr.rtreq π2)
    (hstr.slot π2) (hstr.path π2) (hstr.rsalt π2)

end OnBytes.K.Arm
