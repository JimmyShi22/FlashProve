-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryRunMain.lean: the top of the run on an entry file: the trusted function on a
typed value, the damages behind the converter, and the plays.

What is trusted, said whole.
(t1) Off the three public files and the ground's typed constants, by plain computation inside
     `prepE` and `playE`: `stdEntry`; the digest c := `configurationDigest`; the parameters q :=
     `linkAtCfg G.q c`; and of these the verifier itself: the description `entryXD G c`, the
     decision `decRun q …`, the pins and the family `famAt`, `d1Run`, `pinsFit`.
(t2) `whyOutE`.

Untrusted: the converter proper, which takes the key file and the entry file to a typed value (cms,
x, π). It is `convE` or `convLax` (the port's own `Entry.read` or the lenient reader, and
`recordSeeds`), and then `assembleS`.

The trusted function `whyOutE` takes (cms, x, π) to "YES" or to the stage that refuses: "L" (not two
roots), "S" (the seeds' two chains and the comparison: `cmpE`) or "V:clause" (the lax verifier's
evaluable form: `laxE`, `whyE`). The family F of typed oracles is a parameter. `whyOutE_yes`: "YES"
↔ two roots ∧ cmpE = true ∧ laxE = true. By `cmpE_eq`, `laxE_eq` and `judgeRunEL_det_and` these two
are `(judgeRunEL … o).det F`.

At which F: `famAt`. At safe = true it is `famOf` (`famSafe`: the page's own writing side;
`famOf_eq`: it is `readBlocks` (the page) `Run.oBits` at every query). At safe = false it is
`famFastE`, a stand-in: as a family it is not the page's.

The decision is `Tie.entryDecR q` at `keysOfX` of the instance. Nothing is marked noncomputable.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryRunBytes
import OnBytes.TypedOracleCompiler.Slice.EntryDamageX
import OnBytes.TypedOracleCompiler.Slice.EntryJudgeRun
import OnBytes.TypedOracleCompiler.Slice.EntryDamage
import OnBytes.TypedOracleCompiler.Slice.EntryProbe
import OnBytes.TypedOracleCompiler.Slice.KeysOfX
import OnBytes.TypedOracleCompiler.Slice.EntryFill
import OnBytes.TypedOracleCompiler.Run.PageEFast
import OnBytes.TypedOracleCompiler.Slice.EntryRunTop
import OnBytes.Slice.SeedDrawnCode
import OnBytes.TypedOracleCompiler.Slice.SeedsBack

set_option autoImplicit false

namespace TypedOracleCompiler.Slice

open OnBytes.Tie (EntryGround)
open OnBytes.Slice (GE NZ seedEntry seedOfDrawnC)
open OnBytes Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD bodyS)

/-- The decision, as a function of an instance: the port's own decision of the link at the two
keys written of the instance. -/
def decRun (q : Params.Link) (v lg s : ℕ) (x : XE AnsT lg s) : _root_.Run.PQ.View → Bool :=
  OnBytes.Tie.entryDecR q (keysOfX v lg s (anT v s) x).1 (keysOfX v lg s (anT v s) x).2

/-- The fixed value that a first query holds in the place of seeds. -/
def d1Run (lg s : ℕ) : Sd1 lg s := fun _ => (fun _ => 0, ⟨1, one_ne_zero⟩)

/-- A clause's name. -/
def whyName : TypedOracleCompiler.Run.Thin.Why → String
  | .chain => "chain" | .own => "own" | .ext => "ext" | .few => "few" | .formed => "formed"
  | .walks => "walks" | .req => "req" | .accept => "accept" | .yes => "yes"

section
variable {lg s : ℕ} [DecidableEq (Sd1 lg s)] (D : XD) (hok : TypedOracleCompiler.Run.PQ.ok D.base = true)
  (d₁ : Sd1 lg s) (dec : XE AnsT lg s → _root_.Run.PQ.View → Bool)
  (F : Fam (typedOracleFamily 256 (D.K + 1)
    (LXE (Bd := List Bool) D (earlyTwo (A := AnsT × AnsT) d₁) (TSE D (seedEntry lg s)))))

/-- THE TRUSTED FUNCTION, ON A TYPED VALUE. -/
def whyOutE (cms : List (Dig 256)) (x : XE AnsT lg s) (π : OneProtocolProof 256 (PSXE D dec).up) : String :=
  if cms.length = 2 then
    if cmpE D (earlyTwo d₁) (seedEntry lg s) (seedOfDrawnC lg s) F cms 0 x.2 then
      match whyE D dec (bodyS D.a D.base.plan.salt) (ownES D hok) (earlyTwo d₁)
          (fun _ => TSE D (seedEntry lg s)) F cms x π with
      | .yes => "YES"
      | w => "V:" ++ whyName w
    else "S"
  else "L"

/-- Its yes: two roots; the seeds' comparison says yes; the lax verifier's evaluable form says
yes. -/
theorem whyOutE_yes (cms : List (Dig 256)) (x : XE AnsT lg s) (π : OneProtocolProof 256 (PSXE D dec).up) :
    whyOutE D hok d₁ dec F cms x π = "YES" ↔
      cms.length = 2 ∧
      cmpE D (earlyTwo d₁) (seedEntry lg s) (seedOfDrawnC lg s) F cms 0 x.2 = true ∧
      laxE D dec (bodyS D.a D.base.plan.salt) (ownES D hok) (earlyTwo d₁)
        (fun _ => TSE D (seedEntry lg s)) F cms x π = true := by
  rw [← whyE_yes]
  unfold whyOutE
  by_cases h2 : cms.length = 2
  · rw [if_pos h2]
    by_cases hc : cmpE D (earlyTwo d₁) (seedEntry lg s) (seedOfDrawnC lg s) F cms 0 x.2 = true
    · rw [if_pos hc]
      cases whyE D dec (bodyS D.a D.base.plan.salt) (ownES D hok) (earlyTwo d₁)
        (fun _ => TSE D (seedEntry lg s)) F cms x π <;> simp [h2, hc, whyName]
    · rw [if_neg hc]
      simp [hc]
  · rw [if_neg h2]
    simp [h2]

end

/-! ## The plays -/

/-- One damage behind the converter. `none`: the honest play. Places are numbers into the lists
of what the honest file opens (`ownPlaces`, `storedPlaces`). -/
inductive Dmg where
  | none
  /-- (d1), (d2): bit 0 of root i -/
  | root (i : Nat)
  /-- (d3), (d4): bit 0 of word 0 of answer i of the first table | of the copy -/
  | ans0 (i : Nat) | ans1 (i : Nat)
  /-- (d5), (d6): coordinate 0 of seed 0's point | seed 0's factor, in the first table's seeds -/
  | seed0 | fac0
  /-- (d7), (d8): value j of round k | round k's nonce, on the chain as read -/
  | val (k j : Nat) | nonce (k : Nat)
  /-- (d9), (d10): word i of the column at own place n | stored place n -/
  | ownWord (n i : Nat) | stoWord (n i : Nat)
  /-- (d11): digest l of the path at own place n | stored place n -/
  | ownPath (n l : Nat) | stoPath (n l : Nat)
  /-- (d12): the leaf's salt's last bit at own place n | stored place n -/
  | ownSalt (n : Nat) | stoSalt (n : Nat)
  /-- (d13): the chain's salt's first bit -/
  | salt
  /-- (d14): stored places n and m exchanged (of one table, else nothing is turned) -/
  | stoSwap (n m : Nat)
  /-- (d15), (d16): a third root | one root alone -/
  | third | alone
  /-- (d17): eight bits more on the leaf's salt at stored place n -/
  | stoSaltLong (n : Nat)
  /-- (d18), (d19): one triple more at the end of the first table's answers | the last one dropped
  -/
  | ansMore | ansLess
  /-- (d20): both tables exchanged: roots, answers and seeds -/
  | swapTables
  /-- (d22): at stored place n: the file's salt's first eight bytes moved to the column's end
  (`stoShift`) -/
  | stoShift (n : Nat)
  deriving Repr

namespace Dmg

/-- On the chain as read. -/
def onO : Dmg → Fmt.ChainOut → Fmt.ChainOut
  | .val k j => Damage.O.val k j
  | .nonce k => Damage.O.nonce k
  | _ => id

/-- On the roots. -/
def onC : Dmg → List (Dig 256) → List (Dig 256)
  | .root i => Damage.atL i Damage.flipD
  | .third => DamageX.third
  | .alone => DamageX.alone
  | .swapTables => List.reverse
  | _ => id

/-- On the instance. -/
def onX {lg s : ℕ} : Dmg → XE AnsT lg s → XE AnsT lg s
  | .ans0 i, x => DamageX.ans0 x i
  | .ans1 i, x => DamageX.ans1 x i
  | .seed0, x => if h : 0 < s ∧ 0 < lg then DamageX.seed0 x ⟨0, h.1⟩ ⟨0, h.2⟩ else x
  | .fac0, x => if h : 0 < s then DamageX.fac0 x ⟨0, h⟩ else x
  | .ansMore, x => ((x.1.1 ++ [(0, 0, 0)], x.1.2), x.2)
  | .ansLess, x => ((x.1.1.dropLast, x.1.2), x.2)
  | .swapTables, x => ((x.1.2, x.1.1), (x.2.2, x.2.1))
  | _, x => x

/-- On the typed string. own, sto: the places that the honest file opens. -/
def onS {X : Type} {D : XD} {dec : X → _root_.Run.PQ.View → Bool} (own sto : List (ℕ × ℕ)) :
    Dmg → OneProtocolProof 256 (PSXE D dec).up → OneProtocolProof 256 (PSXE D dec).up
  | .ownWord n i => Damage.S.addOneToWordAtOwnOpening (own.getD n (0, 0)).1 (own.getD n (0, 0)).2 i
  | .stoWord n i => Damage.S.stoWord (sto.getD n (0, 0)).1 (sto.getD n (0, 0)).2 i
  | .ownPath n l => Damage.S.ownPath (own.getD n (0, 0)).1 (own.getD n (0, 0)).2 l
  | .stoPath n l => Damage.S.stoPath (sto.getD n (0, 0)).1 (sto.getD n (0, 0)).2 l
  | .ownSalt n => Damage.S.ownSalt (own.getD n (0, 0)).1 (own.getD n (0, 0)).2
  | .stoSalt n => Damage.S.stoSalt (sto.getD n (0, 0)).1 (sto.getD n (0, 0)).2
  | .salt => Damage.S.salt
  | .stoSwap n m =>
    if (sto.getD n (0, 0)).1 = (sto.getD m (0, 0)).1 then
      Damage.S.stoSwap (sto.getD n (0, 0)).1 (sto.getD n (0, 0)).2 (sto.getD m (0, 0)).2
    else id
  | .stoShift n => Damage.S.stoShift (sto.getD n (0, 0)).1 (sto.getD n (0, 0)).2
  | .stoSaltLong n => Damage.S.sto (sto.getD n (0, 0)).1 (sto.getD n (0, 0)).2 fun op =>
      { op with salt := op.salt ++ List.replicate 8 false }
  | _ => id

/-- Does the damage turn anything? A place beyond what the honest file opens, two stored places
of two tables, a round or value that is not there, A VALUE THAT IS A ROOT (`got` leaves it), A NONCE
AT A ROUND WITHOUT WORK (the typed plain part has no place for it): then the play would run the
HONEST value: it must say so and not be read as a verdict. -/
def applies (own sto : List (ℕ × ℕ)) (o : Fmt.ChainOut) (works : List ℕ) (n0 n1 lg s : ℕ) :
    Dmg → Bool
  | .none => true
  | .root i => i < 2
  | .ans0 i => i < n0
  | .ans1 i => i < n1
  | .seed0 => 0 < s && 0 < lg
  | .fac0 => 0 < s
  | .val k j => ((o.rounds.toList[k]?).bind fun r => r.vals[j]?).elim false fun v =>
      match v with
      | .root _ => false
      | _ => true
  | .nonce k => k < o.rounds.size && works.getD k 0 != 0
  | .ownWord n _ | .ownPath n _ | .ownSalt n => n < own.length
  | .stoWord n _ | .stoPath n _ | .stoSalt n | .stoSaltLong n | .stoShift n => n < sto.length
  | .stoSwap n m => n < sto.length && m < sto.length && n != m &&
      (sto.getD n (0, 0)).1 == (sto.getD m (0, 0)).1
  | .ansLess => 0 < n0
  | _ => true

end Dmg

/-- `PageEFast.famFastE` at pins computed off the description and the tables' shape: NO PIN IS TYPED
BY HAND. -/
def famRun {lg s : ℕ} (D : XD) (hcfg : D.base.cfg.size = 32) (d₁ : Sd1 lg s)
    (sh : Params.IndexShape) :
    Fam (typedOracleFamily 256 (D.K + 1)
      (LXE (Bd := List Bool) D (earlyTwo (A := AnsT × AnsT) d₁) (TSE D (seedEntry lg s)))) :=
  PageEFast.famFastE
    (EntryFill.pinsE D d₁ D.base.cfg hcfg
      (_root_.Run.bytesToDig (Fmt.formatHash 169 0 1 Fmt.zero32 D.base.params))
      (FirstName.restOf D.base.cfg sh.code.logN sh.code.ell sh.code.r sh.v sh.answers
        sh.saltBytes)) (D.K + 1)

/-- WHICH FAMILY A PLAY TAKES. safe = true: `EntryRunTop.famOf` (its famSafe: THE PAGE's OWN
WRITING SIDE; `famOf_eq`: it IS `readBlocks (partOf …).m Run.oBits`, at every oracle and query): THE
PLAY THAT COUNTS. safe = false: `famFastE`: A STAND-IN: as a family it is NOT the page's. -/
def famAt {lg s : ℕ} (safe : Bool) (D : XD) (hcfg : D.base.cfg.size = 32) (d₁ : Sd1 lg s)
    (sh : Params.IndexShape) :
    Fam (typedOracleFamily 256 (D.K + 1)
      (LXE (Bd := List Bool) D (earlyTwo (A := AnsT × AnsT) d₁) (TSE D (seedEntry lg s)))) :=
  if safe then EntryRunTop.famOf D hcfg d₁ sh else famRun D hcfg d₁ sh

/-- The pins fit the description: every stored table's salt has the plan's length, which is the
shape's; the label is the link's (`pinsE` writes `Params.labelLink` whatever D says); the stored
trees' depth is the shape's code's. -/
def pinsFit (D : XD) (sh : Params.IndexShape) : Bool :=
  (D.stored.flatten.all fun t => t.salt == D.base.plan.salt) && sh.saltBytes == D.base.plan.salt &&
    D.base.label == Params.labelLink && D.a == sh.code.logN

/-- THE STATEMENT OF A TYPED VALUE, AS ONE WORD: of a root, a record's seeds and a list of answers
IN THE VALUE (not in a file): the commitment ID as the format makes it of the digest c, the table's
name at that root, these seeds and these answers, with no told digest (`Key.commitmentIdAt`'s text,
R4.11), in hex. NO SEED IS DRAWN HERE: the word is a function of the value alone; that the value's
seeds are the drawn ones is what `whyOutE`'s stage "S" tests (`cmpE`), not a property of the word.
The first table's can be held against a set's commitment ID, which comes from outside the converter.
-/
def stmtId {lg s : ℕ} (sh : Params.IndexShape) (c : ByteArray) (r : Dig 256) (sd : Sd1 lg s)
    (a : AnsT) : String :=
  Fmt.hex (Fmt.publishedID c (Fmt.tableName (_root_.Run.digToBytes r) c sh.code.logN sh.code.ell
    sh.code.r sh.v sh.answers sh.saltBytes) (seedsFlat sd) a [])

/-- A PLAY: the converter; one damage behind it; the trusted function at the family that `safe`
names; AND THE STATEMENT OF THE VALUE THAT WAS JUDGED (a yes is a yes of the value, not of the
files). "C:…": the bytes' side refuses (std | converter); "P": the pins do not fit the description;
"DAMAGE-NOT-APPLIED": the damage would turn nothing; "A": the assembling gives nothing; else
`whyOutE`'s word. THE SECOND PART: the two tables' statement words of the value that was judged.
lax: which converter (`prepE`). -/
def playE (G : EntryGround)
    (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)
    (z : Params.StdSize) (safe lax : Bool) (dm : Dmg) (pol lay kl key ent : ByteArray) :
    String × String :=
  match prepE G z lax pol lay kl key ent with
  | .error e => ("C:" ++ e, "")
  | .ok p =>
    if !pinsFit (entryXD G p.c) G.q.link.table then ("P", "")
    else if !dm.applies (Damage.ownPlaces p.a.out) (Damage.storedPlaces (entryXD G p.c) p.a.out)
        p.a.out ((entryXD G p.c).ds.map (·.entry.work)) p.a.first.answers.length
        p.a.further.answers.length G.q.link.table.cubeBits
        G.q.link.table.answers then ("DAMAGE-NOT-APPLIED", "")
    else
    match assembleS (entryXD G p.c)
        (decRun p.q G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers)
        (dm.onO p.a.out) with
    | none => ("A", "")
    | some π =>
      let cms := dm.onC
        [_root_.Run.bytesToDig p.a.first.root, _root_.Run.bytesToDig p.a.further.root]
      let x : XE AnsT G.q.link.table.cubeBits G.q.link.table.answers :=
        dm.onX (xOfAskedC _ _ p.a)
      (whyOutE (entryXD G p.c) (hok p.c p.hc) (d1Run _ _) _
        (famAt safe (entryXD G p.c) p.hc (d1Run _ _) G.q.link.table) cms x
        (dm.onS (Damage.ownPlaces p.a.out) (Damage.storedPlaces (entryXD G p.c) p.a.out) π),
       "first " ++ stmtId G.q.link.table p.c (cms.getD 0 default) x.2.1 x.1.1 ++ " copy " ++
        stmtId G.q.link.table p.c (cms.getD 1 default) x.2.2 x.1.2)

/-- TWO PROBES BESIDE THE PLAYS (no play makes the DECISION refuse; `workE`). THE SEEDS'
COMPARISON IS SKIPPED ON PURPOSE: so this is NOT the trusted function. .1: the clause that the lax
verifier ALONE names on the damaged value (the seeds in an instance do not enter the chain: a first
query holds the fixed value d₁ in their place: so a value with other seeds should pass chain, own,
ext, few, formed, walks and fall at "accept", BY THE DECISION). .2: `workE`: the chain's run, then
`PQ.passSL`: accept's own conjunct on the proof of work, by itself. -/
def probeE (G : EntryGround)
    (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)
    (z : Params.StdSize) (safe : Bool) (dm : Dmg) (pol lay kl key ent : ByteArray) :
    String × String :=
  match prepE G z false pol lay kl key ent with
  | .error e => ("C:" ++ e, "")
  | .ok p =>
    if !dm.applies (Damage.ownPlaces p.a.out) (Damage.storedPlaces (entryXD G p.c) p.a.out)
        p.a.out ((entryXD G p.c).ds.map (·.entry.work)) p.a.first.answers.length
        p.a.further.answers.length G.q.link.table.cubeBits
        G.q.link.table.answers then ("DAMAGE-NOT-APPLIED", "")
    else
    match assembleS (entryXD G p.c)
        (decRun p.q G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers)
        (dm.onO p.a.out) with
    | none => ("A", "")
    | some π =>
      let cms := dm.onC
        [_root_.Run.bytesToDig p.a.first.root, _root_.Run.bytesToDig p.a.further.root]
      let x : XE AnsT G.q.link.table.cubeBits G.q.link.table.answers :=
        dm.onX (xOfAskedC _ _ p.a)
      let π' := dm.onS (Damage.ownPlaces p.a.out) (Damage.storedPlaces (entryXD G p.c) p.a.out) π
      let F := famAt safe (entryXD G p.c) p.hc (d1Run _ _) G.q.link.table
      (whyName (whyE (entryXD G p.c) _ (bodyS (entryXD G p.c).a (entryXD G p.c).base.plan.salt)
          (ownES (entryXD G p.c) (hok p.c p.hc)) (earlyTwo (d1Run _ _))
          (fun _ => TSE (entryXD G p.c) (seedEntry _ _)) F cms x π'),
       match workE (Bd := List Bool) (entryXD G p.c) _ (earlyTwo (d1Run _ _))
          (fun _ => TSE (entryXD G p.c) (seedEntry _ _)) F cms x π' with
       | none => "workE: none"
       | some b => "workE: some " ++ toString b)

/-- At the small example. -/
def probeSmall (safe : Bool) (dm : Dmg) (pol lay kl key ent : ByteArray) : String × String :=
  probeE OnBytes.Tie.smallRecordGround small_record_ok Params.stdSmall safe dm pol lay kl key ent

/-- At the small example. -/
def playSmall (safe lax : Bool) (dm : Dmg) (pol lay kl key ent : ByteArray) : String × String :=
  playE OnBytes.Tie.smallRecordGround small_record_ok Params.stdSmall safe lax dm pol lay kl key ent

end TypedOracleCompiler.Slice
