-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/ArmPair.lean: the tie of the entry file to the entry's arm of the compiled verifier
(`exit_arm_served`, Johnson/Top/TieArmServed.lean) and the bound on that arm against every maker
(`arm_pr_one`, Johnson/TypedOracleCompiler/RecCompile/LinkAnsOne.lean) hold at ONE input, and speak there of one
function `verdict r`: the tie at `oBits`, the bound at a random g.

Definitions, statements and proofs. What it is for: a control. The two theorems are stated apart, in
different letters. Here Lean itself says that one wire, one wire of the record, one code of the
answers and one coding serve both; and which hypotheses are then left. The two are composed nowhere:
nothing here turns exit code 0 into a bound. The arm is a check built from the same definitions as
`innerCompiledVerifier`'s check of that file; it is not that check: the lax Link, a wiring and a
coding of its own (limit 2).

Main names (namespace `OnBytes.K.Fire`):
  `verdict r g z`: the verdict of the arm with the lax Link at an `ArmIn` r
    (Johnson/Top/TieArm.lean), at what `r.m` reads out of a function g, on two roots, two records
    and a typed string z.
  `TieSays r Z R`: the conclusion of `exit_arm_served`, whole, said with `verdict r oBits`.
  `BoundSays r εs`: the conclusion of `arm_pr_one` at r's own terms, said with `verdict r g`.
  `tie`, `pair`: both at every r that serves what passes `servedAt Z` (hZ), from `EntryPart` and the
    seven premises of `arm_pr_one`.
  `verdict_overOne`: `verdict r g z` is the value of the arm that asks g itself through `r.m`: the
    form in which Johnson/Flat/ArmSibFiles.lean states its bounds.
  `door_served`, `door_served_shut`: an r that serves no statement satisfies `EntryPart` vacuously;
    with the premise hZ of `exit_arm_served` no statement then passes `servedAt Z`.
  `pair_full`, `pair_small`: `TieSays` and `BoundSays` at `armSib` (Johnson/Top/TieArmSib.lean) at
    the two grounds, the written rest of the object, 141 | 100 blocks (the entry's own 140 | 99 and
    one more), the bound's own wire of the record and code of the answers. Five hypotheses, and
    three laws that say that the three tests tell their one plain part (hp0, hp1, hpL); the other
    binders are data, some with laws or instances in their types: `back` is a code with a parser
    (two laws, Rom/Hotel.lean), A has `mat_cut`, and R, P, hL have their instances. Five of the
    binders are idle: t, cfg, shape, pl0, pl1: the arm's wire of the record overwrites them.
  `pair_closedFull`, `pair_closedSmall`: the same at `armWrittenFull` | `armWrittenSmall`
    (Johnson/Top/ArmWrittenFull.lean, ArmWrittenSmall.lean), where the data of the wires, the seeds
    and the coding are written terms. Two hypotheses that stand by themselves.
  `pair_closedFull_at`, `pair_closedSmall_at`: at every Z whose parameter file begins with the 32
    lines. One hypothesis that stands by itself: the theorem on codes `Cb.BCHKS46At GF GE`. Three
    laws ride in the parameters A and sX (`A.mat_cut`, OnBytes/Slice/DecoderRec.lean; `sX.get_put`,
    `sX.put_get`, Iop/Ser.lean), and instances in R, P and hL. That the six types of A, R, G, P, hL,
    sX have a member together is not shown here.
  "closed" in these names means: at written values; letters are left: X, A, sX, R, G, P, hL, Z.
  In the six pairs at the two sizes (three at each) the theorem on codes stands before the
    conjunction, though the tie does not need it: the tie's half follows from `tie` and
    `entryPart_sib` (in the closed forms: `entryPart_writtenFull` | `entryPart_writtenSmall`), which
    have no such hypothesis.
  The 32 lines: `TestSaysLines.full32`, `small32` (OnBytes/K/Left/TestSaysLines.lean): copies of the
    first 32 lines of the examples' parameter files. That they are any file's lines rests on the
    sha256 sums in that file's head.

Limits.
  1. These are theorems of their own on the entry file's arm. They are no instance of the
     description of Johnson/Top/InnerCompiledVerifier.lean: an `ArmIn` has no field for a commitment's code,
     for an instance or for a cheating prover; its object `r.L` still carries the three honest
     provers, of which nothing is asked. In the closed forms the object is the three files' own
     where hL is the provers' own (Johnson/Flat/RestSib.lean, Johnson/Flat/WireAt.lean); the wire is
     not the one wiring's (`wireFullAt`, `wireSmallAt`, Johnson/Flat/WireAt.lean).
  2. The wiring and the coding are for the arm alone. 141 | 100 blocks are the entry's own count
     plus one; no number of blocks is shown to serve the key file, the entry file and the proof file
     together. The coding `r.m` writes the program's strings at the seeds' and the link's chain
     queries, at leaves and at vertices; all other typed queries, those of the key file's and the
     proof file's chains among them, it writes behind an escape (the head of
     Johnson/Top/TieArmSibK.lean).
  3. Each pair is a conjunction of two statements that are composed nowhere. `TieSays` speaks of one
     fixed function, Lean's BLAKE2b; `BoundSays` of a random function. The step from the one to the
     other is taken as given, and it is more than "a random function for a fixed one": the coding
     `r.m` and the record's wire `r.Sd` hold digests that are themselves values of the hash
     function. The reading of the files hashes too: by no theorem is the maker of the bound "the
     files' author, then this reading".
  4. What the arm promises (`LinkHolds`, Johnson/TypedOracleCompiler/RecCompile/LinkAnsPr.lean) is said of the words
     that the maker's typed log together with the arm's own log (`logOne`,
     Johnson/TypedOracleCompiler/RecCompile/LinkAnsOne.lean) fixes under the two roots, and has the way out "the
     first table decodes to nothing". It is as strong as the letter A: the decoder (`conf_D`,
     OnBytes/Slice/ConfOf.lean) gives nothing also at a collision seed and where `A.inRange` fails,
     and two tables decode to the same thing if their `A.mat` are equal; no meant A is written. The
     entry file alone closes nothing on an index.
  5. Exit code 0 covers WITHIN LIMITS as well as YES. `TieSays` asks three pins (the three public
     files are Z's) and two options (neither -policy nor -no-proof-of-work): a call that names
     -policy is not spoken of. No theorem says that the program's yes holds of any files: whether a
     call ends in 0 is seen by running the program.
  6. The lax Link, not the strict format. In the closed forms the wire records of the two big files,
     the four maps, `code` and `num` are the stand-ins of Johnson/Flat/ArmData.lean: the plainest,
     not the files' own, written so that the types are not empty. By the text of the arm (no theorem
     says it) neither its run nor the coding reads them; what the arm promises reads the session's
     wire of external strings, which is `oneExt`'s (Johnson/Flat/ArmSibMaker.lean). The arm's run
     does read the test of equality of seeds, and the coding reads the seed d₁: both are written
     terms of Johnson/Flat/ArmData.lean, and nothing is asked of them. The length of salts is the
     ground's own. X, A, sX, R, G, P, hL and Z's other bytes stay parameters.
  7. In a round with proof of work, the 2^-128 for each query includes the chance that the test bits
     of one fresh answer are all zero. Like all of `BoundSays`, this is a statement about queries to
     a random function. The bound contains the number `tVL r.W` of the arm's typed queries: 13545 |
     7975 at these wirings (`tVL_atFull`, `tVL_atSmall`, Johnson/Flat/ArmSibCount.lean).
  All that the heads of the files named above do not claim. For proofs only; no program imports this
  file.

-/
import Johnson.Top.TieArmServed
import Johnson.Top.TieArmSib
import Johnson.Top.ArmWrittenFull
import Johnson.Top.ArmWrittenSmall
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsOne
import Johnson.Flat.ArmSibFiles
import Johnson.Flat.ArmSeeds
import OnBytes.K.Left.SibJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.K.Fire

section General
open OnBytes.Shell (Steps opsIO World Event wholeReads kindOf Asked)
open Rom
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig oBits)

/-- The verdict of the arm with the lax Link at an `ArmIn`, as a function of the hash function. -/
def verdict (r : ArmIn) (g : Fam (rom 256)) (z : OutLA 256 r.L r.aL) : Bool :=
  (runA r.W (armL r.W r.Sd r.cA) (readBlocks r.m g) z).1

/-- What the tie says at r: the conclusion of `exit_arm_served`, whole, with `verdict` folded in. -/
def TieSays (r : ArmIn) (Z : Pub) (R : Reading5 r.shape) : Prop :=
  ∀ {args : List String} {s s' : World}, Shell.Run (_root_.main args) s 0 s' →
    ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event) (id : String)
      (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧
      ∃ (table further : OnBytes.Params.TableName), PortYesAt F id table further ∧
        (F.pol = Z.pol → F.lay = Z.lay → F.KL = Z.KL → a.options.policy = none →
          a.options.noProofOfWork = false →
          ∃ (c cj : r.L.Rec) (πL : OneProtocolProof 256 (batLC r.L r.aL)),
            r.recOf (stmOf F a.options) table = some c ∧
            r.recOf (stmOf F a.options) further = some cj ∧
            R.ent (stmOf F a.options) F.key F.ent = some (further, πL) ∧
            verdict r oBits (bytesToDig table.root, bytesToDig further.root, c, cj, πL) = true)

/-- What the bound says at r. -/
def BoundSays (r : ArmIn) (εs : ℝ≥0∞) : Prop :=
  ∀ (Mk : OComp (rom 256) (OutLA 256 r.L r.aL)) (t : ℕ), Mk.QueryBound t →
    Rom.Pr Mk.withTrace
        (fun g => {o | verdict r g o.1 = true ∧
          ¬ LinkHolds r.W (logOne r.W (armL r.W r.Sd r.cA) r.m (readBlocks r.m g) o) o.1.1 o.1.2.1
            o.1.2.2.1 o.1.2.2.2.1}) ≤
      (((t + tVL r.W) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + tVL r.W) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256

/-- The tie, at every r. -/
theorem tie (r : ArmIn) (Z : Pub) (hZ : ∀ x, servedAt Z x = true → r.Served x)
    (R : Reading5 r.shape) (A : EntryPart r.shape R) : TieSays r Z R :=
  fun h => exit_arm_served r Z hZ R A h

/-- The verdict is the value of the arm that asks the one function itself, through the coding. -/
theorem verdict_overOne (r : ArmIn) (g : Fam (rom 256)) (z : OutLA 256 r.L r.aL) :
    verdict r g z = ((armL r.W r.Sd r.cA z).overOne r.m).det g := by
  unfold verdict runA
  rw [det_withTrace, Rom.det_overOne]

/-- The tie and the bound at one r: both speak of `verdict r`. -/
theorem pair (r : ArmIn) (Z : Pub) (hZ : ∀ x, servedAt Z x = true → r.Served x)
    (R : Reading5 r.shape) (A : EntryPart r.shape R) {εL : Err r.L.link.shape} {εs : ℝ≥0∞}
    (hsL : r.L.link.Sound
      (fun rr y => r.L.decodeIndex y.1 rr.1 = none ∨ r.L.hasCollisionAt y.2 rr.2.1 ∨
        r.L.decodeIndex y.2 rr.2 = r.L.decodeIndex y.1 rr.1) εL)
    (hlL : r.L.link.IsLocal) (hcL : r.aL.Coherent) (hW : OKLA r.W) (hA : AnsOK r.cA)
    (hSd : r.Sd.Law εs) (hbL : Err.Below (Err.timesShared (2 ^ r.W.depthReqL) r.aL εL) εs) :
    TieSays r Z R ∧ BoundSays r εs :=
  ⟨tie r Z hZ R A,
    fun Mk t hq => arm_pr_one hsL hlL hcL hW hA hSd hbL (isArm_armL ..) r.m Mk t hq⟩

/-- An r that serves no statement satisfies `EntryPart` vacuously, whatever its wires, coding and
reading: so `exit_arm` (Johnson/Top/TieArm.lean) alone could say nothing about any statement. -/
theorem door_served (r : ArmIn) (R : Reading5 r.shape) (h : ∀ x, ¬ r.Served x) :
    EntryPart r.shape R :=
  ⟨fun _ _ _ _ _ _ _ _ hs => absurd hs (h _), fun _ _ _ _ _ _ _ _ hs => absurd hs (h _),
    fun _ _ _ _ _ _ _ _ _ _ hs => absurd hs (h _)⟩

/-- With the premise hZ of `exit_arm_served`, such an r leaves no statement that passes
`servedAt Z`. That shuts the door only together with `served_any` (OnBytes/K/ServedAny.lean): a run
that ends in 0 on Z's files, with neither of the two options, passes `servedAt Z`. -/
theorem door_served_shut (r : ArmIn) (Z : Pub) (hZ : ∀ x, servedAt Z x = true → r.Served x)
    (h : ∀ x, ¬ r.Served x) (x : UserStm) : servedAt Z x = false := by
  cases e : servedAt Z x with
  | false => rfl
  | true => exact absurd (hZ x e) (h x)

end General

open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Compile.Batch.Cms OnBytes.K.Left OnBytes.Flat OnBytes.RunA OnBytes.Slice
open TypedOracleCompiler.Run.EntryFb (p0E)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD SOf)
open OnBytes.Tie
open OnBytes.K OnBytes.K.Arm
open Cb Cb.Ood Hiop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (View SgX CK XO)

set_option maxRecDepth 40000

/-! ## The full size -/

section Full
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (F : Flat.Files (DecR.configurationOfStoredTable A R)) (P : F.Provers)
  (hL : Honest linkSibFull ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ))))
  {aT : RoundSplits (restSibFull A R F P hL).test.shape}
  (wT : ProtocolQueryLayout 256 (140 + 1) (batTC (LrG (restSibFull A R F P hL)) aT))
  (wB : ProtocolQueryLayout 256 (140 + 1) (restSibFull A R F P hL).bat) (depthReq depthReqT : ℕ)
  (embT : (p : OPos (restSibFull A R F P hL).test.shape) → OSym (restSibFull A R F P hL).test.shape p → List Bool)
  (prjT : (p : OPos (restSibFull A R F P hL).test.shape) → List Bool → Option (OSym (restSibFull A R F P hL).test.shape p))
  (embB : (p : OPos (restSibFull A R F P hL).bat.loc.shape) → OSym (restSibFull A R F P hL).bat.loc.shape p → List Bool)
  (prjB : (p : OPos (restSibFull A R F P hL).bat.loc.shape) → List Bool → Option (OSym (restSibFull A R F P hL).bat.loc.shape p))
  (Z : Pub) (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t)
    (annOf (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT
      (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) t))
  (code : (LrG (restSibFull A R F P hL)).Rec → List (Dig 256))
  (num : ℕ → Plains (restSibFull A R F P hL).bat.loc.shape → Bool)
  (dS : DecidableEq (Fin 1 → (Fin 29 → GE) × NZ))

/-- The seed that the bound's own wire of the record draws from the digests is the program's own
drawing, in the ground's letters: the premise (wire) of `entryPart_sib`, in its own spelling. -/
theorem wire_full (x : Fin (140 + 1) → Dig 256) :
    (sdAtFull (restSibFull A R F P hL) (List Bool) aT
      (wAtFull (restSibFull A R F P hL) 140 wT wB depthReq depthReqT recordGround.q.given.plan.salt embT prjT embB prjB)
      t cfg shape pl0 pl1 code num fr_seed_fits dS).seed x =
      seedOfC recordGround.q.link.table.cubeBits recordGround.q.link.table.answers
        (seedsOfDigs recordGround.q.given.plan.field recordGround.q.link.table.cubeBits
          recordGround.q.link.table.answers x) :=
  wire_recSeedK recT recLg recS (140 + 1) fr_seed_fits x

variable
  (d₁ : Sd1 recordGround.q.link.table.cubeBits recordGround.q.link.table.answers)
  (hcfg : (DG recordGround Z).base.cfg.size = 32) (rest1 : ByteArray)
  (p0 p1 : PlainPart (shapeOf (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) .test)
    (annOf (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) .test))
  (isP0 isP1 :
    PlainPart (shapeOf (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) .test)
    (annOf (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) .test) → Bool)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1)
  (isPL : PlainPart (shapeOf (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) .link)
    (annOf (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))) .link) → Bool)
  (hpL : ∀ p, isPL p = true ↔ p = (pbSib (DG recordGround Z) (ckP .two) dsFull (sibLetters_full Z.digest).1 (sibLetters_full Z.digest).2.1).symm
    (p0E (DG recordGround Z) (earlyTwo (A := List T3 × List T3) d₁)
      (seedEntry recordGround.q.link.table.cubeBits recordGround.q.link.table.answers)))
  (back : StrCode (AllPts 256 (140 + 1)
    (typedOracleCarrier (LrG (restSibFull A R F P hL)) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull)))))


variable (str : OneProtocolProof 256 (PSXE (DG recordGround Z) (decAt recordGround Z.digest)).up →
  OneProtocolProof 256 (batLC (LrG (restSibFull A R F P hL)) (_root_.Run.Twin.allLo (SOf (ckP .two) dsFull))))

/-- **The tie and the bound at one input, at the full size.** Two statements on one function
`verdict r`, composed nowhere: the tie is at Lean's BLAKE2b, the bound at a random function.
Hypotheses: the theorem on codes (the tie does not need it); Z's parameter file says the ground's
lines; the session's wire of external strings is lawful; the description's digest has 32 bytes; the
way between the two types of typed strings keeps the nine fields. All other binders are data; the
laws among them: the three tests tell their one plain part (hp0, hp1, hpL); `back` is a code with a
parser (two laws); A has `mat_cut`; R, P, hL have their instances. Five of them are idle: t, cfg,
shape, pl0, pl1. -/
theorem pair_full (hA : BCHKS46At GF GE) (hZ : recordGround.SaysLines Z.pol) (hB : wB.ext.OK)
    (hstr : StrLaws str) :
    TieSays (armSib recordGround Z (restSibFull A R F P hL) 140 (chalP .two 140) wT wB depthReq depthReqT 0
    recordGround.q.given.plan.salt embT prjT embB prjB
    (sdAtFull (restSibFull A R F P hL) (List Bool) aT
      (wAtFull (restSibFull A R F P hL) 140 wT wB depthReq depthReqT recordGround.q.given.plan.salt embT prjT embB prjB)
      t cfg shape pl0 pl1 code num fr_seed_fits dS) d₁ hcfg rest1
    (8 * (DG recordGround Z).base.plan.salt) (sibLetters_full Z.digest).1 (sibLetters_full Z.digest).2.1 p0 p1 isP0 isP1 hp0 hp1
    isPL hpL (cAAtFull (restSibFull A R F P hL)) (ansOK_atFull (restSibFull A R F P hL)).inj (ansOK_atFull (restSibFull A R F P hL)).len back) Z
      (readSib recordGround Z (restSibFull A R F P hL) 140 (chalP .two 140) wT wB depthReq depthReqT 0
    recordGround.q.given.plan.salt embT prjT embB prjB
    (sdAtFull (restSibFull A R F P hL) (List Bool) aT
      (wAtFull (restSibFull A R F P hL) 140 wT wB depthReq depthReqT recordGround.q.given.plan.salt embT prjT embB prjB)
      t cfg shape pl0 pl1 code num fr_seed_fits dS) d₁ hcfg rest1
    (8 * (DG recordGround Z).base.plan.salt) (sibLetters_full Z.digest).1 (sibLetters_full Z.digest).2.1 p0 p1 isP0 isP1 hp0 hp1
    isPL hpL (cAAtFull (restSibFull A R F P hL)) (ansOK_atFull (restSibFull A R F P hL)).inj (ansOK_atFull (restSibFull A R F P hL)).len back str) ∧
    BoundSays (armSib recordGround Z (restSibFull A R F P hL) 140 (chalP .two 140) wT wB depthReq depthReqT 0
    recordGround.q.given.plan.salt embT prjT embB prjB
    (sdAtFull (restSibFull A R F P hL) (List Bool) aT
      (wAtFull (restSibFull A R F P hL) 140 wT wB depthReq depthReqT recordGround.q.given.plan.salt embT prjT embB prjB)
      t cfg shape pl0 pl1 code num fr_seed_fits dS) d₁ hcfg rest1
    (8 * (DG recordGround Z).base.plan.salt) (sibLetters_full Z.digest).1 (sibLetters_full Z.digest).2.1 p0 p1 isP0 isP1 hp0 hp1
    isPL hpL (cAAtFull (restSibFull A R F P hL)) (ansOK_atFull (restSibFull A R F P hL)).inj (ansOK_atFull (restSibFull A R F P hL)).len back) ((2 : ENNReal)⁻¹ ^ 128) :=
  ⟨tie _ Z (fun _ h => h) _
      (entryPart_sib recordGround Z (restSibFull A R F P hL) 140 (chalP .two 140) wT wB depthReq depthReqT 0
    recordGround.q.given.plan.salt embT prjT embB prjB
    (sdAtFull (restSibFull A R F P hL) (List Bool) aT
      (wAtFull (restSibFull A R F P hL) 140 wT wB depthReq depthReqT recordGround.q.given.plan.salt embT prjT embB prjB)
      t cfg shape pl0 pl1 code num fr_seed_fits dS) d₁ hcfg rest1
    (8 * (DG recordGround Z).base.plan.salt) (sibLetters_full Z.digest).1 (sibLetters_full Z.digest).2.1 p0 p1 isP0 isP1 hp0 hp1
    isPL hpL (cAAtFull (restSibFull A R F P hL)) (ansOK_atFull (restSibFull A R F P hL)).inj (ansOK_atFull (restSibFull A R F P hL)).len back str
        record_answers record_field hZ (fun h hl c ec => armFacts_full h hl c ec)
        (sibLetters_full Z.digest).2.2.1 (sibLetters_full Z.digest).2.2.2 (sibK_full Z.digest)
        (sibChal_full Z.digest) (sibSalt recordGround Z.digest) rfl
        (fun rr => (congrFun (decRun_full Z.digest) (recX rr)).symm) hstr
        (wire_full A R F P hL wT wB depthReq depthReqT embT prjT embB prjB t cfg shape pl0 pl1 code
          num dS)
        (by rw [full_cube, full_answers]; exact room_recSeedK fr_seed_fits) (by norm_num)),
    fun Mk tq hq =>
      atFull_arm_one (restSibFull A R F P hL) (restSibFull_dcd A R F P hL) (restSibFull_coll A R F P hL) (List Bool)
        aT (wAtFull (restSibFull A R F P hL) 140 wT wB depthReq depthReqT recordGround.q.given.plan.salt embT prjT embB prjB) .test
        (TypedOracleCompiler.Run.SeedVals.cfgL Z.digest)
        (TypedOracleCompiler.Run.SeedVals.shapeBits recordGround.q.link.table.code.logN
          recordGround.q.link.table.code.ell recordGround.q.link.table.code.r
          recordGround.q.link.table.v recordGround.q.link.table.answers
          recordGround.q.link.table.saltBytes) p0 p1 code num fr_seed_fits dS hA
        (okla_sibFull 140 (restSibFull A R F P hL) (le_of_eq frD_K) wT wB hB depthReq depthReqT 0
          recordGround.q.given.plan.salt embT prjT embB prjB)
        (isArm_armL ..) _ Mk tq hq⟩

end Full

section ClosedFull
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (G : FilesParameters X RecFull) (P : (threeProtocolsFromDryRunAtFullSize A R G).Provers)
  (hL : Honest linkSibFull ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 29 → GE) × NZ))))
  (Z : Pub) (sX : Ser X)

/-- **The tie and the bound at the input whose wires', seeds' and coding's data are written.** Two
statements on one function `verdict r`, composed nowhere. Two hypotheses that stand by themselves:
the theorem on codes (the tie does not need it); Z's parameter file says the ground's lines. An
instance of `pair_full`. -/
theorem pair_closedFull (hA : BCHKS46At GF GE) (hZ : recordGround.SaysLines Z.pol) :
    TieSays (armWrittenFull A R G P hL Z sX) Z (readWrittenFull A R G P hL Z sX) ∧
    BoundSays (armWrittenFull A R G P hL Z sX) ((2 : ENNReal)⁻¹ ^ 128) :=
  pair_full (hA := hA) (hZ := hZ) (hB := oneExt_ok _ _) (hstr := strLaws_full _ Z) ..

/-- **The same at every Z whose parameter file begins with the example's 32 lines.** Two statements
on one function `verdict r`, composed nowhere. One hypothesis that stands by itself is left: the
theorem on codes (the tie does not need it). Three laws ride in the parameters A and sX
(`A.mat_cut`, `sX.get_put`, `sX.put_get`), and instances in R, P and hL; that the six types of A, R,
G, P, hL, sX have a member together is not shown here. more: what follows the 32 lines; lay, KL: the
two other public files. -/
theorem pair_closedFull_at (hA : BCHKS46At GF GE) (more lay KL : ByteArray) :
    TieSays
      (armWrittenFull A R G P hL ⟨TestSaysLines.bytesOf TestSaysLines.full32 ++ more, lay, KL⟩ sX)
      ⟨TestSaysLines.bytesOf TestSaysLines.full32 ++ more, lay, KL⟩
      (readWrittenFull A R G P hL ⟨TestSaysLines.bytesOf TestSaysLines.full32 ++ more, lay, KL⟩
        sX) ∧
    BoundSays
      (armWrittenFull A R G P hL ⟨TestSaysLines.bytesOf TestSaysLines.full32 ++ more, lay, KL⟩ sX)
      ((2 : ENNReal)⁻¹ ^ 128) :=
  pair_closedFull A R G P hL _ sX hA (full_says_of_prefix more)

end ClosedFull

/-! ## The small example -/

section Small
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X)
  (R : (srS.toDecR srZ 524285).RelationsAndEncoding A) (F : Flat.Files (DecR.configurationOfStoredTable A R)) (P : F.Provers)
  (hL : Honest linkSibSmall ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ))))
  {aT : RoundSplits (restSibSmall A R F P hL).test.shape}
  (wT : ProtocolQueryLayout 256 (99 + 1) (batTC (LrG (restSibSmall A R F P hL)) aT))
  (wB : ProtocolQueryLayout 256 (99 + 1) (restSibSmall A R F P hL).bat) (depthReq depthReqT : ℕ)
  (embT : (p : OPos (restSibSmall A R F P hL).test.shape) → OSym (restSibSmall A R F P hL).test.shape p → List Bool)
  (prjT : (p : OPos (restSibSmall A R F P hL).test.shape) → List Bool → Option (OSym (restSibSmall A R F P hL).test.shape p))
  (embB : (p : OPos (restSibSmall A R F P hL).bat.loc.shape) → OSym (restSibSmall A R F P hL).bat.loc.shape p → List Bool)
  (prjB : (p : OPos (restSibSmall A R F P hL).bat.loc.shape) → List Bool → Option (OSym (restSibSmall A R F P hL).bat.loc.shape p))
  (Z : Pub) (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT
             (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t)
    (annOf (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT
      (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) t))
  (code : (LrG (restSibSmall A R F P hL)).Rec → List (Dig 256))
  (num : ℕ → Plains (restSibSmall A R F P hL).bat.loc.shape → Bool)
  (dS : DecidableEq (Fin 1 → (Fin 19 → GE) × NZ))

/-- The seed that the bound's own wire of the record draws from the digests is the program's own
drawing, in the ground's letters: the premise (wire) of `entryPart_sib`, in its own spelling. -/
theorem wire_small (x : Fin (99 + 1) → Dig 256) :
    (sdAtSmall (restSibSmall A R F P hL) (List Bool) aT
      (wAtSmall (restSibSmall A R F P hL) 99 wT wB depthReq depthReqT smallRecordGround.q.given.plan.salt embT prjT embB prjB)
      t cfg shape pl0 pl1 code num sr_seed_fits dS).seed x =
      seedOfC smallRecordGround.q.link.table.cubeBits smallRecordGround.q.link.table.answers
        (seedsOfDigs smallRecordGround.q.given.plan.field smallRecordGround.q.link.table.cubeBits
          smallRecordGround.q.link.table.answers x) :=
  wire_recSeedK srT 19 1 (99 + 1) sr_seed_fits x

variable
  (d₁ : Sd1 smallRecordGround.q.link.table.cubeBits smallRecordGround.q.link.table.answers)
  (hcfg : (DG smallRecordGround Z).base.cfg.size = 32) (rest1 : ByteArray)
  (p0 p1 : PlainPart (shapeOf (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) .test)
    (annOf (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) .test))
  (isP0 isP1 :
    PlainPart (shapeOf (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) .test)
    (annOf (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) .test) → Bool)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1)
  (isPL : PlainPart (shapeOf (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) .link)
    (annOf (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))) .link) → Bool)
  (hpL : ∀ p, isPL p = true ↔ p = (pbSib (DG smallRecordGround Z) (ckP .two) dsSmall (sibLetters_small Z.digest).1 (sibLetters_small Z.digest).2.1).symm
    (p0E (DG smallRecordGround Z) (earlyTwo (A := List T3 × List T3) d₁)
      (seedEntry smallRecordGround.q.link.table.cubeBits smallRecordGround.q.link.table.answers)))
  (back : StrCode (AllPts 256 (99 + 1)
    (typedOracleCarrier (LrG (restSibSmall A R F P hL)) (List Bool) aT (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall)))))


variable (str : OneProtocolProof 256 (PSXE (DG smallRecordGround Z) (decAt smallRecordGround Z.digest)).up →
  OneProtocolProof 256 (batLC (LrG (restSibSmall A R F P hL)) (_root_.Run.Twin.allLo (SOf (ckP .two) dsSmall))))

/-- **The tie and the bound at one input, at the small example.** Two statements on one function
`verdict r`, composed nowhere: the tie is at Lean's BLAKE2b, the bound at a random function.
Hypotheses: the theorem on codes (the tie does not need it); Z's parameter file says the ground's
lines; the session's wire of external strings is lawful; the description's digest has 32 bytes; the
way between the two types of typed strings keeps the nine fields. All other binders are data; the
laws among them: the three tests tell their one plain part (hp0, hp1, hpL); `back` is a code with a
parser (two laws); A has `mat_cut`; R, P, hL have their instances. Five of them are idle: t, cfg,
shape, pl0, pl1. -/
theorem pair_small (hA : BCHKS46At GF GE) (hZ : smallRecordGround.SaysLines Z.pol) (hB : wB.ext.OK)
    (hstr : StrLaws str) :
    TieSays (armSib smallRecordGround Z (restSibSmall A R F P hL) 99 (chalP .two 99) wT wB depthReq depthReqT 0
    smallRecordGround.q.given.plan.salt embT prjT embB prjB
    (sdAtSmall (restSibSmall A R F P hL) (List Bool) aT
      (wAtSmall (restSibSmall A R F P hL) 99 wT wB depthReq depthReqT smallRecordGround.q.given.plan.salt embT prjT embB prjB)
      t cfg shape pl0 pl1 code num sr_seed_fits dS) d₁ hcfg rest1
    (8 * (DG smallRecordGround Z).base.plan.salt) (sibLetters_small Z.digest).1 (sibLetters_small Z.digest).2.1 p0 p1 isP0 isP1 hp0 hp1
    isPL hpL (cAAtSmall (restSibSmall A R F P hL)) (ansOK_atSmall (restSibSmall A R F P hL)).inj (ansOK_atSmall (restSibSmall A R F P hL)).len back) Z
      (readSib smallRecordGround Z (restSibSmall A R F P hL) 99 (chalP .two 99) wT wB depthReq depthReqT 0
    smallRecordGround.q.given.plan.salt embT prjT embB prjB
    (sdAtSmall (restSibSmall A R F P hL) (List Bool) aT
      (wAtSmall (restSibSmall A R F P hL) 99 wT wB depthReq depthReqT smallRecordGround.q.given.plan.salt embT prjT embB prjB)
      t cfg shape pl0 pl1 code num sr_seed_fits dS) d₁ hcfg rest1
    (8 * (DG smallRecordGround Z).base.plan.salt) (sibLetters_small Z.digest).1 (sibLetters_small Z.digest).2.1 p0 p1 isP0 isP1 hp0 hp1
    isPL hpL (cAAtSmall (restSibSmall A R F P hL)) (ansOK_atSmall (restSibSmall A R F P hL)).inj (ansOK_atSmall (restSibSmall A R F P hL)).len back str) ∧
    BoundSays (armSib smallRecordGround Z (restSibSmall A R F P hL) 99 (chalP .two 99) wT wB depthReq depthReqT 0
    smallRecordGround.q.given.plan.salt embT prjT embB prjB
    (sdAtSmall (restSibSmall A R F P hL) (List Bool) aT
      (wAtSmall (restSibSmall A R F P hL) 99 wT wB depthReq depthReqT smallRecordGround.q.given.plan.salt embT prjT embB prjB)
      t cfg shape pl0 pl1 code num sr_seed_fits dS) d₁ hcfg rest1
    (8 * (DG smallRecordGround Z).base.plan.salt) (sibLetters_small Z.digest).1 (sibLetters_small Z.digest).2.1 p0 p1 isP0 isP1 hp0 hp1
    isPL hpL (cAAtSmall (restSibSmall A R F P hL)) (ansOK_atSmall (restSibSmall A R F P hL)).inj (ansOK_atSmall (restSibSmall A R F P hL)).len back) ((2 : ENNReal)⁻¹ ^ 128) :=
  ⟨tie _ Z (fun _ h => h) _
      (entryPart_sib smallRecordGround Z (restSibSmall A R F P hL) 99 (chalP .two 99) wT wB depthReq depthReqT 0
    smallRecordGround.q.given.plan.salt embT prjT embB prjB
    (sdAtSmall (restSibSmall A R F P hL) (List Bool) aT
      (wAtSmall (restSibSmall A R F P hL) 99 wT wB depthReq depthReqT smallRecordGround.q.given.plan.salt embT prjT embB prjB)
      t cfg shape pl0 pl1 code num sr_seed_fits dS) d₁ hcfg rest1
    (8 * (DG smallRecordGround Z).base.plan.salt) (sibLetters_small Z.digest).1 (sibLetters_small Z.digest).2.1 p0 p1 isP0 isP1 hp0 hp1
    isPL hpL (cAAtSmall (restSibSmall A R F P hL)) (ansOK_atSmall (restSibSmall A R F P hL)).inj (ansOK_atSmall (restSibSmall A R F P hL)).len back str
        small_record_answers small_record_field hZ (fun h hl c ec => armFacts_small h hl c ec)
        (sibLetters_small Z.digest).2.2.1 (sibLetters_small Z.digest).2.2.2 (sibK_small Z.digest)
        (sibChal_small Z.digest) (sibSalt smallRecordGround Z.digest) rfl
        (fun rr => (congrFun (decRun_small Z.digest) (recX rr)).symm) hstr
        (wire_small A R F P hL wT wB depthReq depthReqT embT prjT embB prjB t cfg shape pl0 pl1 code
          num dS)
        (by rw [small_cube, small_answers]; exact room_recSeedK sr_seed_fits) (by norm_num)),
    fun Mk tq hq =>
      atSmall_arm_one (restSibSmall A R F P hL) (restSibSmall_dcd A R F P hL) (restSibSmall_coll A R F P hL) (List Bool)
        aT (wAtSmall (restSibSmall A R F P hL) 99 wT wB depthReq depthReqT smallRecordGround.q.given.plan.salt embT prjT embB prjB) .test
        (TypedOracleCompiler.Run.SeedVals.cfgL Z.digest)
        (TypedOracleCompiler.Run.SeedVals.shapeBits smallRecordGround.q.link.table.code.logN
          smallRecordGround.q.link.table.code.ell smallRecordGround.q.link.table.code.r
          smallRecordGround.q.link.table.v smallRecordGround.q.link.table.answers
          smallRecordGround.q.link.table.saltBytes) p0 p1 code num sr_seed_fits dS hA
        (okla_sibSmall 99 (restSibSmall A R F P hL) (le_of_eq srD_K) wT wB hB depthReq depthReqT 0
          smallRecordGround.q.given.plan.salt embT prjT embB prjB)
        (isArm_armL ..) _ Mk tq hq⟩

end Small

section ClosedSmall
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X)
  (R : (srS.toDecR srZ 524285).RelationsAndEncoding A) (G : FilesParameters X RecSmall) (P : (threeProtocolsFromDryRunAtSmallSize A R G).Provers)
  (hL : Honest linkSibSmall ((DecR.configurationOfStoredTable A R).I ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ)) ×
    (((DecR.configurationOfStoredTable A R).Pad × (DecR.configurationOfStoredTable A R).Rnd) × (Fin 1 → (Fin 19 → GE) × NZ))))
  (Z : Pub) (sX : Ser X)

/-- **The tie and the bound at the input whose wires', seeds' and coding's data are written.** Two
statements on one function `verdict r`, composed nowhere. Two hypotheses that stand by themselves:
the theorem on codes (the tie does not need it); Z's parameter file says the ground's lines. An
instance of `pair_small`. -/
theorem pair_closedSmall (hA : BCHKS46At GF GE) (hZ : smallRecordGround.SaysLines Z.pol) :
    TieSays (armWrittenSmall A R G P hL Z sX) Z (readWrittenSmall A R G P hL Z sX) ∧
    BoundSays (armWrittenSmall A R G P hL Z sX) ((2 : ENNReal)⁻¹ ^ 128) :=
  pair_small (hA := hA) (hZ := hZ) (hB := oneExt_ok _ _) (hstr := strLaws_small _ Z) ..

/-- **The same at every Z whose parameter file begins with the example's 32 lines.** Two statements
on one function `verdict r`, composed nowhere. One hypothesis that stands by itself is left: the
theorem on codes (the tie does not need it). Three laws ride in the parameters A and sX
(`A.mat_cut`, `sX.get_put`, `sX.put_get`), and instances in R, P and hL; that the six types of A, R,
G, P, hL, sX have a member together is not shown here. more: what follows the 32 lines; lay, KL: the
two other public files. -/
theorem pair_closedSmall_at (hA : BCHKS46At GF GE) (more lay KL : ByteArray) :
    TieSays
      (armWrittenSmall A R G P hL ⟨TestSaysLines.bytesOf TestSaysLines.small32 ++ more, lay, KL⟩ sX)
      ⟨TestSaysLines.bytesOf TestSaysLines.small32 ++ more, lay, KL⟩
      (readWrittenSmall A R G P hL ⟨TestSaysLines.bytesOf TestSaysLines.small32 ++ more, lay, KL⟩
        sX) ∧
    BoundSays
      (armWrittenSmall A R G P hL ⟨TestSaysLines.bytesOf TestSaysLines.small32 ++ more, lay, KL⟩ sX)
      ((2 : ENNReal)⁻¹ ^ 128) :=
  pair_closedSmall A R G P hL _ sX hA (small_says_of_prefix more)

end ClosedSmall

end OnBytes.K.Fire
