-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/TieArmSib.lean: the tie's three hypotheses for the entry file (`EntryPart`,
OnBytes/K/Parts.lean), as one theorem, at the input of the entry's arm `armZ`
(Johnson/Top/TieArmZ.lean) at the object whose Link is the written link over letters, and the wire
with `wSib` and `bodiesSib` (Johnson/EntryRec/OklaSib.lean).

The two seeds' fields are Johnson/Top/TieArmZ.lean's; the field `link` is `link_field`
(Johnson/Top/ArmLinkAt.lean). Both speak of one coding: `mAt` at this wire is the coding of
`link_field`, by unfolding.

Main names.
 `wireSib`      the wire.
 `armSib`       `armZ` at that wire, at the correspondence `pbSib` of the plain parts, bodies as
                they are, and the answers as triples by `Flat.trAns`.
 `readSib`      the reading of the three files: of the key file and the entry file, `entArm`
                (OnBytes/K/ArmLetters.lean), then a way `str` from the typed strings of the written
                link to those of the object's Link. The other two readings give nothing: `EntryPart`
                does not read them.
 `entryPart_sib`   `EntryPart (armSib …).shape (readSib …)`.
 `exit_sib`      `exit_arm` (Johnson/Top/TieArm.lean) at these: from the exit code 0 of the program
                to the yes of the run of the entry's arm with the lax Link, with the arm's terms
                written out.

"Served" is no letter here: it is the test `servedAt Z` (OnBytes/K/Served.lean), a Bool on the
user's statement alone, by definition (`servedArm Z x := servedAt Z x`, OnBytes/K/ArmLetters.lean).
`exit_full` and `exit_small` (Johnson/Top/TieArmSizes.lean) pay it from the exit code but for three
pins and two options.

Asked. Of the ground G: it has answers; its field is the one of two words; Z's parameter file says
G's lines; `HF`: what a yes of the program gives at G (in the words of `armFacts_full` and
`armFacts_small`, OnBytes/K/Arm/ArmFacts.lean). Seven equations: the letters C, ds, a, xs, K, chal,
salt are those of the description `entryXD G Z.digest`. The object's decision at a pair of records
is the run's decision at the instance made of the pair. `StrLaws str`. cA is one to one, with one
number of digests. nb = 8 * salt. Of the seeds' wire: (wire), (room). K + 1 is below 2 ^ 48.

What goes with `entryPart_sib` and `exit_sib`.
 1. They are theorems of their own on the entry file's arm, and no instance of the description of
    the theorem on innerCompiledVerifier: the object `LrG T` is not shown to be that description's object.
 2. The wiring is for the arm alone: K is the entry's own number of blocks (`hKl`). No K is shown to
    be the number of blocks of the whole verifier. See the head of Johnson/Top/TieArmAt.lean.
 3. One fixed function stands on this side, Lean's BLAKE2b. The bound on an arm (`arm_pr_one`,
    Johnson/TypedOracleCompiler/RecCompile/LinkAnsOne.lean) is over a random function. The two are composed nowhere.
    The coding and the seeds' data hold two digests that are values of the hash function: the digest
    of the three public files (`Z.digest`) and the digest of the parameter bytes
    (`EntryRunTop.pdOf`).
 4. What the arm promises (`LinkHolds`, Johnson/TypedOracleCompiler/RecCompile/LinkAnsPr.lean) has the way out "the
    first table decodes to nothing". The entry file alone closes nothing on an index.
 5. The exit code 0 covers WITHIN LIMITS as well as YES. `exit_sib` concludes under "the statement
    is served at Z" (`servedArm`, OnBytes/K/ArmLetters.lean). That test asks, among other things,
    that the three public files are Z's and that the call names neither -policy nor
    -no-proof-of-work. No theorem says that the program's yes holds of any files.
 6. It is the lax Link, not the strict format. The wire records wT and wB, of the key file's and the
    proof file's protocols, are letters: stand-ins for those of a whole verifier.
 7. How far it has been read: the last line of this head.
Not claimed. That any of these holds at any letters. `exit_sib` speaks of one fixed function, Lean's
BLAKE2b, in the place of a random function: the step from the one to the other is taken as given,
and no bound on a maker of false strings is composed with it here. This is a wiring for the arm
alone: see the head of Johnson/Top/TieArmAt.lean. Nothing on soundness (index binding included),
opening-form binding, no two openings, correctness of extraction or whatever else names a committer
or a prover.

-/
import Johnson.Top.TieArmZ
import Johnson.Top.ArmLinkAt

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Compile.Batch.Cms OnBytes.K.Left OnBytes.Flat OnBytes.RunA OnBytes.Slice
open TypedOracleCompiler.Run.EntryFb (p0E)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD SOf)
open OnBytes.Tie
open OnBytes.K
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (View SgX CK XO)

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

/-- The wire: Link's wire record is the written link's; a leaf's body is a string of bits. -/
abbrev wireSib :
    QueryLayout 256 (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) :=
  wireOf2 (L := LrG T) (aT := aT) (aL := _root_.Run.Twin.allLo (SOf C ds)) (K + 1) wT
    (wSib T K chal) wB a depthReq depthReqT depthReqL (bodiesSib T salt embT prjT embB prjB)

variable
  (S0 : OutOfDomainSampleQueryLayout 256 (K + 1) (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds)))
  (d₁ : Sd1 G.q.link.table.cubeBits G.q.link.table.answers)
  (hcfg : (DG G Z).base.cfg.size = 32) (rest1 : ByteArray) (nb : ℕ)
  (hC : C = (DG G Z).C) (hds : ds = (DG G Z).ds)
  (p0 p1 : PlainPart (shapeOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) .test)
    (annOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) .test))
  (isP0 isP1 :
    PlainPart (shapeOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) .test)
    (annOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) .test) → Bool)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1)
  (isPL : PlainPart (shapeOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) .link)
    (annOf (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds))) .link) → Bool)
  (hpL : ∀ p, isPL p = true ↔ p = (pbSib (DG G Z) C ds hC hds).symm
    (p0E (DG G Z) (earlyTwo (A := List T3 × List T3) d₁)
      (seedEntry G.q.link.table.cubeBits G.q.link.table.answers)))
  (cA : AnsG G → List (Dig 256))
  (hinj : Function.Injective cA) (hlen : ∀ a a', (cA a).length = (cA a').length)
  (back : StrCode (AllPts 256 (K + 1)
    (typedOracleCarrier (LrG T) (List Bool) aT (_root_.Run.Twin.allLo (SOf C ds)))))

/-- **The arm's input at the written link over letters.** -/
def armSib : ArmIn :=
  armZ G rest1 nb Z T
    (wireSib G T K chal wT wB depthReq depthReqT depthReqL salt embT prjT embB prjB) S0 cA d₁ hcfg
    (pbSib (DG G Z) C ds hC hds) (Equiv.refl (List Bool)) p0 p1 isP0 isP1 hp0 hp1 isPL hpL
    OnBytes.Flat.trAns hinj hlen trAns_sib_inj back

variable (str : OneProtocolProof 256 (PSXE (DG G Z) (decAt G Z.digest)).up →
  OneProtocolProof 256 (batLC (LrG T) (_root_.Run.Twin.allLo (SOf C ds))))

/-- **The reading of the files.** -/
def readSib :
    Reading5 (armSib G Z T K chal wT wB depthReq depthReqT depthReqL salt embT prjT embB prjB S0 d₁
      hcfg rest1 nb hC hds p0 p1 isP0 isP1 hp0 hp1 isPL hpL cA hinj hlen back).shape where
  key := fun _ _ => none
  ent := fun x key ent => (entArm G Z (decAt G Z.digest) x key ent).map fun u => (u.1, str u.2)
  prf := fun _ _ _ _ => none

/-- **The tie's three hypotheses for the entry file, at the written link over letters.** -/
theorem entryPart_sib (hA : (G.q.link.table.answers == 0) = false)
    (hF : G.q.given.plan.field = .two) (hZ : G.SaysLines Z.pol)
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
    (hdec2 : ∀ rr, dec2 rr = decAt G Z.digest (recX rr)) (hstr : StrLaws str)
    (wire : ∀ x, S0.seed x = seedOfC G.q.link.table.cubeBits G.q.link.table.answers
      (seedsOfDigs G.q.given.plan.field G.q.link.table.cubeBits G.q.link.table.answers x))
    (room : nBlocks G.q.link.table.cubeBits G.q.link.table.answers ≤ K + 1)
    (hK : K + 1 < 2 ^ 48) :
    EntryPart (armSib G Z T K chal wT wB depthReq depthReqT depthReqL salt embT prjT embB prjB S0 d₁
      hcfg rest1 nb hC hds p0 p1 isP0 isP1 hp0 hp1 isPL hpL cA hinj hlen back).shape
      (readSib G Z T K chal wT wB depthReq depthReqT depthReqL salt embT prjT embB prjB S0 d₁ hcfg
        rest1 nb hC hds p0 p1 isP0 isP1 hp0 hp1 isPL hpL cA hinj hlen back str) :=
  entryPart_Z G rest1 nb Z T
    (wireSib G T K chal wT wB depthReq depthReqT depthReqL salt embT prjT embB prjB) S0 cA d₁ hcfg
    (pbSib (DG G Z) C ds hC hds) (Equiv.refl (List Bool)) p0 p1 isP0 isP1 hp0 hp1 isPL hpL
    OnBytes.Flat.trAns hinj hlen trAns_sib_inj back hA hZ wire room hK _
    (link_field G Z T K chal wT wB depthReq depthReqT depthReqL salt embT prjT embB prjB d₁ hcfg
      rest1 nb hC hds p0 p1 isP0 isP1 _ _ hp0 hp1 _ isPL hpL cA hinj hlen hA hF hZ HF ha hxs hKl
      hchal hsalt hnb back hdec2 str hstr)

open OnBytes.Shell (Steps opsIO World Event wholeReads kindOf Asked) in
/-- **The tie for the entry file at the arm with the lax Link, at the written link over letters.**
If the program `verify-on-bytes` exits with code 0, then, at the files that this run has read and
the two tables that it threads from file to file: if the statement is served at Z, both tables are
read as records made of the program's own seeds and the tables' answers, the key file and the entry
file are read as the further table and a typed string, and the run of the entry's arm (the two
seeds' tests, then Link's compiled verifier without the strict format), at what the coding `mAt`
reads out of the oracle made from Lean's BLAKE2b, says yes at the two roots, the two records and
that string. -/
theorem exit_sib (hA : (G.q.link.table.answers == 0) = false)
    (hF : G.q.given.plan.field = .two) (hZ : G.SaysLines Z.pol)
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
    (hdec2 : ∀ rr, dec2 rr = decAt G Z.digest (recX rr)) (hstr : StrLaws str)
    (wire : ∀ x, S0.seed x = seedOfC G.q.link.table.cubeBits G.q.link.table.answers
      (seedsOfDigs G.q.given.plan.field G.q.link.table.cubeBits G.q.link.table.answers x))
    (room : nBlocks G.q.link.table.cubeBits G.q.link.table.answers ≤ K + 1)
    (hK : K + 1 < 2 ^ 48) {args : List String} {s s' : World}
    (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (q : Asked) (F : Files) (t : List Event) (id : String)
      (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof q ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      q.options.id = some id ∧ q.options.bits = 128 ∧
      ∃ (table further : Params.TableName), PortYesAt F id table further ∧
        (servedArm Z (stmOf F q.options) = true →
          ∃ (c cj : SeedG G × AnsG G)
            (πL : OneProtocolProof 256 (batLC (LrG T) (_root_.Run.Twin.allLo (SOf C ds)))),
            recOfArm G Z (stmOf F q.options) table = some c ∧
            recOfArm G Z (stmOf F q.options) further = some cj ∧
            (entArm G Z (decAt G Z.digest) (stmOf F q.options) F.key F.ent).map
              (fun u => (u.1, str u.2)) = some (further, πL) ∧
            (runA (wireSib G T K chal wT wB depthReq depthReqT depthReqL salt embT prjT embB prjB)
              (armL (wireSib G T K chal wT wB depthReq depthReqT depthReqL salt embT prjT embB prjB)
                (sdTest
                  (wireSib G T K chal wT wB depthReq depthReqT depthReqL salt embT prjT embB prjB)
                  (s0At
                    (wireSib G T K chal wT wB depthReq depthReqT depthReqL salt embT prjT embB prjB)
                    S0 Z.digest G.q.link.table) p0 p1) cA)
              (readBlocks (mAt G Z.digest d₁ rest1 nb hcfg
                (wireSib G T K chal wT wB depthReq depthReqT depthReqL salt embT prjT embB prjB) S0
                cA (pbSib (DG G Z) C ds hC hds) (Equiv.refl (List Bool)) p0 p1 isP0 isP1 hp0 hp1
                isPL hpL OnBytes.Flat.trAns hinj hlen trAns_sib_inj back) oBits)
              (bytesToDig table.root, bytesToDig further.root, c, cj, πL)).1 = true) :=
  exit_arm _ _ (entryPart_sib G Z T K chal wT wB depthReq depthReqT depthReqL salt embT prjT embB
    prjB S0 d₁ hcfg rest1 nb hC hds p0 p1 isP0 isP1 hp0 hp1 isPL hpL cA hinj hlen back str hA hF hZ
    HF ha hxs hKl hchal hsalt hnb hdec2 hstr wire room hK) h

end OnBytes.K.Arm
