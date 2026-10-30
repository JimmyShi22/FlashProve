-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/TieArmAt.lean: the input of the entry's arm (`ArmIn`, Johnson/Top/TieArm.lean) at a
ground G of the entry's link and a digest c of the public files, with its coding and its seeds' wire
written; and, at its shape, the two seeds' fields of the tie for the entry file (`EntryPart`,
OnBytes/K/Parts.lean).

Main names.
 `mAt`          the coding: `implL2` (OnBytes/TypedOracleCompiler/Slice/ArmRead.lean) over the carrier of the typed
                oracles, at the description `entryXD G c`, at the wire's own number of digests W.K,
                with the leaves' code `KeyLeaves.leavesAt`, at the seeds' plain parts p0, p1 and the
                typed pieces and bytes of a table's name at c and the shape of G's tables: the
                coding at which `link_arm_at` (OnBytes/K/Arm/LinkArmAt.lean) has the lax Link's yes,
                at K' := W.K.
 `armAt`        the `ArmIn` with that coding and the seeds' wire
                `sdTest W (s0At W S0 c G.q.link.table) p0 p1`. It is `armOf`
                (Johnson/Top/TieSeedArm.lean) at written codes. The object L, the wire W, which
                statements are served (`Served`) and how a table is read as a record (`recOf`) are
                letters here; Johnson/Top/TieArmZ.lean fills both.
 `armAt_m`      its coding is `mAt`: by rfl.
 `seed0_at`, `seed1_at`   `EntryPart.seed0`, `EntryPart.seed1` at `(armAt …).shape`.
 `entryPart_at`   `EntryPart (armAt …).shape R`, from these two and the field `link` as a premise.
At three public files Z (c := `Z.digest`, `servedArm Z`, `recOfArm G Z`): Johnson/Top/TieArmZ.lean.

The description in the coding is `entryXD G c` at a c that is fixed before any run: meant is the
digest of three public files Z that are given beforehand, never the digest of the files of a run. A
served statement has Z's files (`servedArm_pins`, OnBytes/K/ArmLetters.lean), so the two digests
are then one.
The number of digests W.K is the wire's. For the arm alone, W may take the description's own number
(`(entryXD G c).K + 1`) as a term. Whether one number serves the key file, the entry file and the
proof file is a question of the whole verifier, not of the arm. The seeds' fields here hold at every
W.K with (room). The field `link`, as `link_arm_at` has it, asks W.K = (entryXD G c).K + 1. A count
that is no theorem (by a program over the planner's print, and by reading; not checked here): a
round of the proof file's first chain draws 396,672 trits, that is 12,396 words or 3,099 blocks,
while the entry's own number is 140 at the full size and 99 at the small example. So a wire that
serves all three files has W.K at least 3,100, which is not the entry's number and 1: the tie of the
entry file as it stands holds at a wiring for the arm alone, and the step to one wire for three
files wants the lemmas on the typed string and the walks at every K from the entry's number on.

Asked for the seeds' fields: (wire) S0's seed is `toSeed` of the program's own draws on the digests,
in the field of G's parameters, at the shape of G's tables; (room) W.K digests are enough; c has 32
bytes; W.K is below 2 ^ 48; `RecIsProgram`.

Not claimed. The field `link`: a premise here. That any L, W, S0, pbF, bd are as asked. Nothing on
how seeds are distributed; nothing on soundness (index binding included), opening-form binding, no
two openings, correctness of extraction or whatever else names a committer or a prover.

-/
import Johnson.Top.TieSeedRec
import OnBytes.K.Arm.LinkArmAt

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm

open _root_.Compile TypedOracleCompiler.Iop Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig oBits)
open TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.EntryFb (p0E e162 e162_is)
open TypedOracleCompiler.Run.LinkAlongM (laterM leafM)
open TypedOracleCompiler.Run.LinkFirstAns (lf0 lf0_is)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Slice.EntryFill (Ls L0 pinsE)
open TypedOracleCompiler.Slice.ArmRead (implL2)
open OnBytes.Slice (seedEntry)
open OnBytes.Tie (EntryGround)
open OnBytes.K

variable (G : EntryGround) (c : ByteArray)
  (d₁ : Sd1 G.q.link.table.cubeBits G.q.link.table.answers) (rest1 : ByteArray) (nb : ℕ)
  (hcfg : (entryXD G c).base.cfg.size = 32)
  {I X : Type} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout 256 (typedOracleCarrier L Bd aT aL)) (S0 : OutOfDomainSampleQueryLayout 256 W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig 256)) (toSeed : List (List E × E) → L.OutOfDomainSeed) (Served : UserStm → Prop)
  (recOf : UserStm → Params.TableName → Option L.Rec)
  (pbF : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .link) (annOf (typedOracleCarrier L Bd aT aL) .link) ≃
    PlainPart (shapeOf (Ls (entryXD G c) d₁) .link) (annOf (Ls (entryXD G c) d₁) .link))
  (bd : (typedOracleCarrier L Bd aT aL).Bd ≃ (Ls (entryXD G c) d₁).Bd)
  (p0 p1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .test) (annOf (typedOracleCarrier L Bd aT aL) .test))
  (isP0 isP1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .test) (annOf (typedOracleCarrier L Bd aT aL) .test) → Bool)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1)
  (isPL : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) .link) (annOf (typedOracleCarrier L Bd aT aL) .link) → Bool)
  (hpL : ∀ p, isPL p = true ↔
    p = pbF.symm (p0E (entryXD G c) (earlyTwo (A := List T3 × List T3) d₁)
      (seedEntry G.q.link.table.cubeBits G.q.link.table.answers)))
  (tr : L.OutOfDomainAnswer → List T3) (hinj : Function.Injective cA)
  (hlen : ∀ a a', (cA a).length = (cA a').length) (htr : Function.Injective tr)
  (back : StrCode (AllPts 256 W.K (typedOracleCarrier L Bd aT aL)))

/-- **The coding of the arm.** -/
abbrev mAt : OracleCoding (typedOracleFamily 256 W.K (typedOracleCarrier L Bd aT aL)) 256 :=
  implL2 (entryXD G c) d₁ (entryXD G c).base.cfg hcfg (EntryRunTop.pdOf (entryXD G c)) rest1
    (KeyLeaves.leavesAt (L0 (entryXD G c) d₁) nb (entryXD G c).base.cfg) (typedOracleCarrier L Bd aT aL) pbF
    bd p0 p1 isP0 isP1 (s0At W S0 c G.q.link.table).cfg (s0At W S0 c G.q.link.table).shape hp0 hp1
    (restOf G.q.link.table c) isPL hpL cA tr hinj hlen htr W.K back

/-- **The arm's input at the ground**: `armOf` at the codes of which `implL2` is made. -/
def armAt : ArmIn :=
  armOf W S0 cA c G.q.link.table Served recOf p0 p1 isP0 isP1 hp0 hp1
    (pinsE (entryXD G c) d₁ (entryXD G c).base.cfg hcfg (EntryRunTop.pdOf (entryXD G c)) rest1).l
    (pinsE (entryXD G c) d₁ (entryXD G c).base.cfg hcfg (EntryRunTop.pdOf (entryXD G c)) rest1).hlt
    (pinsE (entryXD G c) d₁ (entryXD G c).base.cfg hcfg (EntryRunTop.pdOf (entryXD G c)) rest1).hR
    (lf0 (typedOracleCarrier L Bd aT aL) .link
      (pbF.symm (p0E (entryXD G c) (earlyTwo (A := List T3 × List T3) d₁)
        (seedEntry G.q.link.table.cubeBits G.q.link.table.answers))) isPL
      (EntryRunTop.pdOf (entryXD G c)) cA tr hpL hinj hlen htr OnBytes.Params.labelLink)
    (lf0_is (typedOracleCarrier L Bd aT aL) .link _ isPL (EntryRunTop.pdOf (entryXD G c)) cA tr hpL hinj hlen
      htr OnBytes.Params.labelLink)
    (laterM (Ls (entryXD G c) d₁) (typedOracleCarrier L Bd aT aL) pbF)
    (e162 (pinsE (entryXD G c) d₁ (entryXD G c).base.cfg hcfg (EntryRunTop.pdOf (entryXD G c))
      rest1) W.K)
    (e162_is (pinsE (entryXD G c) d₁ (entryXD G c).base.cfg hcfg (EntryRunTop.pdOf (entryXD G c))
      rest1) W.K)
    (leafM (Ls (entryXD G c) d₁) (typedOracleCarrier L Bd aT aL) bd)
    (KeyLeaves.leavesAt (L0 (entryXD G c) d₁) nb (entryXD G c).base.cfg) (entryXD G c).base.cfg hcfg
    back

/-- Its coding is `mAt`. -/
theorem armAt_m :
    (armAt G c d₁ rest1 nb hcfg W S0 cA Served recOf pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr hinj
      hlen htr back).m =
      mAt G c d₁ rest1 nb hcfg W S0 cA pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr hinj hlen htr
        back := rfl

variable (wire : ∀ a, S0.seed a = toSeed (seedsOfDigs G.q.given.plan.field
    G.q.link.table.cubeBits G.q.link.table.answers a))
  (room : nBlocks G.q.link.table.cubeBits G.q.link.table.answers ≤ W.K) (hc : c.size = 32)
  (hK : W.K < 2 ^ 48)
  (hrec : RecIsProgram G.q.given.plan.field c G.q.link.table toSeed Served recOf)

include wire room hc hK hrec in
/-- **`EntryPart.seed0`** at the shape of `armAt`. -/
theorem seed0_at :
    ∀ Fl o id table further, o.id = some id → o.bits = 128 → PortYesAt Fl id table further →
      (armAt G c d₁ rest1 nb hcfg W S0 cA Served recOf pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr
        hinj hlen htr back).shape.Served (stmOf Fl o) →
      ∃ r, (armAt G c d₁ rest1 nb hcfg W S0 cA Served recOf pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL
          tr hinj hlen htr back).shape.recOf (stmOf Fl o) table = some r ∧
        (armAt G c d₁ rest1 nb hcfg W S0 cA Served recOf pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr
          hinj hlen htr back).shape.seed0 (stmOf Fl o) (bytesToDig table.root) r = true :=
  seed0_arm W S0 cA G.q.given.plan.field c G.q.link.table toSeed Served recOf p0 p1 isP0 isP1 hp0
    hp1 _ _ _ _ _ _ _ _ _ _ _ hcfg back wire room hc hK hrec

include wire room hc hK hrec in
/-- **`EntryPart.seed1`** at the same shape. -/
theorem seed1_at :
    ∀ Fl o id table further, o.id = some id → o.bits = 128 → PortYesAt Fl id table further →
      (armAt G c d₁ rest1 nb hcfg W S0 cA Served recOf pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr
        hinj hlen htr back).shape.Served (stmOf Fl o) →
      ∃ r, (armAt G c d₁ rest1 nb hcfg W S0 cA Served recOf pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL
          tr hinj hlen htr back).shape.recOf (stmOf Fl o) further = some r ∧
        (armAt G c d₁ rest1 nb hcfg W S0 cA Served recOf pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr
          hinj hlen htr back).shape.seed1 (stmOf Fl o) (bytesToDig further.root) r = true :=
  seed1_arm W S0 cA G.q.given.plan.field c G.q.link.table toSeed Served recOf p0 p1 isP0 isP1 hp0
    hp1 _ _ _ _ _ _ _ _ _ _ _ hcfg back wire room hc hK hrec

include wire room hc hK hrec in
/-- **The tie's three hypotheses for the entry file at the shape of `armAt`**, from the field `link`
alone. -/
theorem entryPart_at
    (R : Reading5 (armAt G c d₁ rest1 nb hcfg W S0 cA Served recOf pbF bd p0 p1 isP0 isP1 hp0 hp1
      isPL hpL tr hinj hlen htr back).shape)
    (link : ∀ Fl o id table further r r', o.id = some id → o.bits = 128 →
      PortYesAt Fl id table further →
      (armAt G c d₁ rest1 nb hcfg W S0 cA Served recOf pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr
        hinj hlen htr back).shape.Served (stmOf Fl o) →
      (armAt G c d₁ rest1 nb hcfg W S0 cA Served recOf pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr
        hinj hlen htr back).shape.recOf (stmOf Fl o) table = some r →
      (armAt G c d₁ rest1 nb hcfg W S0 cA Served recOf pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr
        hinj hlen htr back).shape.recOf (stmOf Fl o) further = some r' →
      ∃ πL, R.ent (stmOf Fl o) Fl.key Fl.ent = some (further, πL) ∧
        (armAt G c d₁ rest1 nb hcfg W S0 cA Served recOf pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL tr
          hinj hlen htr back).shape.vL (stmOf Fl o) (bytesToDig table.root)
          (bytesToDig further.root) r r' πL = true) :
    EntryPart (armAt G c d₁ rest1 nb hcfg W S0 cA Served recOf pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL
      hpL tr hinj hlen htr back).shape R :=
  ⟨seed0_at G c d₁ rest1 nb hcfg W S0 cA toSeed Served recOf pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL hpL
      tr hinj hlen htr back wire room hc hK hrec,
    seed1_at G c d₁ rest1 nb hcfg W S0 cA toSeed Served recOf pbF bd p0 p1 isP0 isP1 hp0 hp1 isPL
      hpL tr hinj hlen htr back wire room hc hK hrec, link⟩

end OnBytes.K.Arm
