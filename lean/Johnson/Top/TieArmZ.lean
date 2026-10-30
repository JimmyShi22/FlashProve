-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/TieArmZ.lean: the input of the entry's arm `armAt` (Johnson/Top/TieArmAt.lean) at three
public files Z that are given beforehand, and the tie's three hypotheses for the entry file at its
shape, from the field `link`.

Main names.
 `armZ`         `armAt` at c := `Z.digest`, Served := `servedArm Z`, recOf := `recOfArm G Z`
                (OnBytes/K/ArmLetters.lean), at an object `LrG T` (Johnson/EntryRec/Defs.lean) whose
                records are the records over the field at G's letters.
                Both places for a digest, that in a table's name (the seeds' queries) and that in
                the description (the leaves' and the link's codes), are filled with `Z.digest`.
 `entryPart_Z`  `EntryPart (armZ …).shape R`: `RecIsProgram` (`recIsProgram_arm`,
                Johnson/Top/TieSeedRec.lean) and "the digest has 32 bytes" are paid.

"Served" is no letter here: it is the test `servedAt Z` (OnBytes/K/Served.lean), a Bool on the
user's statement alone, by definition (`servedArm Z x := servedAt Z x`, OnBytes/K/ArmLetters.lean).

Asked: the tables of G have answers; Z's parameter file says G's lines; (wire) the seeds' wire's
seed is `seedOfC` of the program's own draws on the digests, in the field of G's parameters, at the
shape of G's tables; (room) W.K digests are enough; W.K is below 2 ^ 48; the field `link`.

Not claimed. The field `link`: a premise. That any T, W, S0, pbF, bd are as asked. Nothing on how
seeds are distributed; nothing on soundness (index binding included), opening-form binding, no two
openings, correctness of extraction or whatever else names a committer or a prover.

-/
import Johnson.Top.TieArmAt
import Johnson.EntryRec.Defs

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm

open _root_.Compile TypedOracleCompiler.Iop Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig oBits)
open TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.EntryFb (p0E)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Slice.EntryFill (Ls)
open OnBytes.Slice (seedEntry)
open OnBytes.Tie (EntryGround)
open OnBytes.K

variable (G : EntryGround) (rest1 : ByteArray) (nb : ℕ)

section AtZ
open OnBytes.RunA (RestR LrG)
open OnBytes.Slice (GE NZ)
open _root_.Run.PQ (SgX)

variable (Z : Pub) {I' X' RI : Type} [Fintype RI] [Nonempty RI] {a : ℕ}
  {Q : InteractiveOracleProof
    (((Fin G.q.link.table.answers → (Fin G.q.link.table.cubeBits → GE) × NZ) ×
        ((Fin G.q.link.table.v → Bool) × Fin G.q.link.table.answers → GE)) ×
      ((Fin G.q.link.table.answers → (Fin G.q.link.table.cubeBits → GE) × NZ) ×
        ((Fin G.q.link.table.v → Bool) × Fin G.q.link.table.answers → GE))) (twoExternalStrings (2 ^ a) SgX)}
  (T : RestR I' X' RI (Fin G.q.link.table.answers → (Fin G.q.link.table.cubeBits → GE) × NZ)
    ((Fin G.q.link.table.v → Bool) × Fin G.q.link.table.answers → GE) a Q)
  {Bd' : Type} {aT' : RoundSplits T.test.shape} {aL' : RoundSplits Q.shape}
  (W' : QueryLayout 256 (typedOracleCarrier (LrG T) Bd' aT' aL')) (S0' : OutOfDomainSampleQueryLayout 256 W'.K (LrG T) Bd' aT' aL')
  (cA' : (LrG T).OutOfDomainAnswer → List (Dig 256))
  (d₁' : Sd1 G.q.link.table.cubeBits G.q.link.table.answers)
  (hcfg' : (entryXD G Z.digest).base.cfg.size = 32)
  (pbF' : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd' aT' aL') .link)
      (annOf (typedOracleCarrier (LrG T) Bd' aT' aL') .link) ≃
    PlainPart (shapeOf (Ls (entryXD G Z.digest) d₁') .link) (annOf (Ls (entryXD G Z.digest) d₁') .link))
  (bd' : (typedOracleCarrier (LrG T) Bd' aT' aL').Bd ≃ (Ls (entryXD G Z.digest) d₁').Bd)
  (q0 q1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd' aT' aL') .test)
    (annOf (typedOracleCarrier (LrG T) Bd' aT' aL') .test))
  (isQ0 isQ1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd' aT' aL') .test)
    (annOf (typedOracleCarrier (LrG T) Bd' aT' aL') .test) → Bool)
  (hq0 : ∀ p, isQ0 p = true ↔ p = q0) (hq1 : ∀ p, isQ1 p = true ↔ p = q1)
  (isQL : PlainPart (shapeOf (typedOracleCarrier (LrG T) Bd' aT' aL') .link)
    (annOf (typedOracleCarrier (LrG T) Bd' aT' aL') .link) → Bool)
  (hqL : ∀ p, isQL p = true ↔
    p = pbF'.symm (p0E (entryXD G Z.digest) (earlyTwo (A := List T3 × List T3) d₁')
      (seedEntry G.q.link.table.cubeBits G.q.link.table.answers)))
  (tr' : (LrG T).OutOfDomainAnswer → List T3) (hinj' : Function.Injective cA')
  (hlen' : ∀ x y, (cA' x).length = (cA' y).length) (htr' : Function.Injective tr')
  (back' : StrCode (AllPts 256 W'.K (typedOracleCarrier (LrG T) Bd' aT' aL')))

/-- **The arm's input at a ground and three public files.** -/
def armZ : ArmIn :=
  armAt G Z.digest d₁' rest1 nb hcfg' W' S0' cA' (fun x => servedArm Z x = true) (recOfArm G Z) pbF'
    bd' q0 q1 isQ0 isQ1 hq0 hq1 isQL hqL tr' hinj' hlen' htr' back'

/-- **The tie's three hypotheses for the entry file at the shape of `armZ`**, from the field `link`,
the wire's two laws on the seeds and a bound. -/
theorem entryPart_Z (hA : (G.q.link.table.answers == 0) = false) (hZ : G.SaysLines Z.pol)
    (wire' : ∀ x, S0'.seed x = seedOfC G.q.link.table.cubeBits G.q.link.table.answers
      (seedsOfDigs G.q.given.plan.field G.q.link.table.cubeBits G.q.link.table.answers x))
    (room' : nBlocks G.q.link.table.cubeBits G.q.link.table.answers ≤ W'.K)
    (hK' : W'.K < 2 ^ 48)
    (R : Reading5 (armZ G rest1 nb Z T W' S0' cA' d₁' hcfg' pbF' bd' q0 q1 isQ0 isQ1 hq0 hq1 isQL
      hqL tr' hinj' hlen' htr' back').shape)
    (link : ∀ Fl o id table further r r', o.id = some id → o.bits = 128 →
      PortYesAt Fl id table further →
      (armZ G rest1 nb Z T W' S0' cA' d₁' hcfg' pbF' bd' q0 q1 isQ0 isQ1 hq0 hq1 isQL hqL tr' hinj'
        hlen' htr' back').shape.Served (stmOf Fl o) →
      (armZ G rest1 nb Z T W' S0' cA' d₁' hcfg' pbF' bd' q0 q1 isQ0 isQ1 hq0 hq1 isQL hqL tr' hinj'
        hlen' htr' back').shape.recOf (stmOf Fl o) table = some r →
      (armZ G rest1 nb Z T W' S0' cA' d₁' hcfg' pbF' bd' q0 q1 isQ0 isQ1 hq0 hq1 isQL hqL tr' hinj'
        hlen' htr' back').shape.recOf (stmOf Fl o) further = some r' →
      ∃ πL, R.ent (stmOf Fl o) Fl.key Fl.ent = some (further, πL) ∧
        (armZ G rest1 nb Z T W' S0' cA' d₁' hcfg' pbF' bd' q0 q1 isQ0 isQ1 hq0 hq1 isQL hqL tr'
          hinj' hlen' htr' back').shape.vL (stmOf Fl o) (bytesToDig table.root)
          (bytesToDig further.root) r r' πL = true) :
    EntryPart (armZ G rest1 nb Z T W' S0' cA' d₁' hcfg' pbF' bd' q0 q1 isQ0 isQ1 hq0 hq1 isQL hqL
      tr' hinj' hlen' htr' back').shape R :=
  entryPart_at G Z.digest d₁' rest1 nb hcfg' W' S0' cA'
    (seedOfC G.q.link.table.cubeBits G.q.link.table.answers) (fun x => servedArm Z x = true)
    (recOfArm G Z) pbF' bd' q0 q1 isQ0 isQ1 hq0 hq1 isQL hqL tr' hinj' hlen' htr' back' wire' room'
    (size_configurationDigest _) hK' (recIsProgram_arm G hA Z hZ) R link

end AtZ

end OnBytes.K.Arm
