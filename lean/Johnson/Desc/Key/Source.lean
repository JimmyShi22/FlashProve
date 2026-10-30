-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Key/Source.lean: what a key file's description is made of, out of the three public
files, and the public tests on it. Definitions with code; public data only: no view and no value of
the field is read, but for the test on the instance. No theorem.

The three public files (policy, layout, the key's parameters) give the key's three chains as the
program reads them, and the planner's sized values. A description needs besides: the declared rounds
of the three chains, and for every tree what is told of it: its tenants, and for each tenant the
groups whose proximity test reads it. Here these are gathered in one record, and the record is
tested: against its own bytes, against what the rules make of the chains as read, and by the
public tests that the verifier program asks in front of or inside its run.

Main names.
  `groupRanges`, `groupFolded`, `groupOmega`, `groupOwn`, `groupsAtLabel`: the numbers of the
  groups, one list for the whole file, and which groups the messages of a sending join.
  `toldOfChain`, `toldOfPlans`, `toldOfMade`: what is told of a chain's trees, with the groups.
  `KeySource`: the record. It is made where the description is made (`sourceOf`,
  Johnson/Desc/Key/Desc.lean).
  `readAgainOk`: every value of the chains is the program's own reading of the bytes that they hold.
  `madeAgain`, `madeAgainOk`: the declared rounds and what is told, made again of the chains as read
  alone, are the record's.
  `twoDigitUnits`, `runsInUnits`, `unitsReached`, `weightsCovered`: the lookup on the numbers of two
  digits reads rows of units of two digits alone, and reaches every such unit whole.
  `sourceClauses`, `sourceOk`, `sourceFailing`: the public tests, by name.
  `keyWordsBelow`, `instanceOk`: the test on the instance alone.

Limits. `groupsAtLabel` bears the key file's form alone: the folded row's group and Omega's differ
in code (a shared split), W's and Omega's do not; `sourceClauses` asks that form. That the bytes
which the chains hold are the bytes that are hashed is the frame's matter. That the seeds of the key
are those of the table's name is the frame's too. The comments name the lines of the verifier
program (under OnBytes/) after which each clause is written; nothing holds a clause against these
lines. `weightsCovered` says nothing of a unit of four digits (of such a unit the key's proof of the
ranges covers the bytes alone: OnBytes/Plan/FromLayout.lean), nor that the layout's units are the
model's. `twoDigitUnits` halves a unit's rows (at an odd number the last row would lie in no
stretch), and no clause here asks that their number is even. On the verifier's road it is: `madeAt`
(Johnson/Desc/Key/Road.lean) returns only where the planner has found `Plan.unitsOk` of the same
layout (rows a multiple of the digits: OnBytes/Plan/Units.lean); this is read off the texts, and no
theorem states it. At the full size the planner's lookups are the written ones
(`Lk6.AtPlan.looksOf_full`, Johnson/Top/H/LooksAtPlan.lean). Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.Key.Xi
import Johnson.Desc.ProofFile.Told
import OnBytes.Plan.FromLayout

set_option autoImplicit false

namespace VerifiableInference.Desc.Key

open OnBytes OnBytes.Params
open VerifiableInference.Desc (FileDescription Chain Block)
open Johnson.G (Sending ChainSends)
open Johnson.G.OfPlan (Made Sent ownMasks Decl3)

/-! ## 1 The groups told -/

/-- The groups' numbers, one list for the whole file: the first stage's group of each of the four
tests; stage i's (from 1) is the first's + i. -/
def groupRanges : Nat := 100
def groupFolded : Nat := 200
def groupOmega : Nat := 250
def groupOwn : Nat := 300

/-- The number behind "stage " in a code switch's label. -/
def stageOfLabel (label : String) : Nat := (((label.splitOn "stage ").getLast?).bind
    (·.toNat?)).getD 0

/-- For each oracle message of a sending, in order: the groups that it joins, in the order of
joining (Wf.lean:346-347 · Lin.lean:186-192 | :270-277 | :343-346 · Prox.lean:221). A message behind
the list's end joins none. It bears
the key file's form alone: the folded row's group and Omega's differ in code (a shared split), W's
and Omega's do not. -/
def groupsAtLabel (label : String) : List (List Nat) :=
  if label == "the index-mask message" then [[groupOwn]]
  else if label == "the multiplicities" then [[groupRanges]]
  else if label == "W" then [[groupOwn]]
  else if label == "the folded row" then [[groupFolded]]
  else if label == "Omega" then [[groupOmega, groupOwn], [groupOmega, groupFolded]]
  else if label.startsWith "the ranges' test, " then [[groupRanges + stageOfLabel label]]
  else if label.startsWith "the folded row's test, " then [[groupFolded + stageOfLabel label]]
  else if label.startsWith "Omega's test, " then [[groupOmega + stageOfLabel label]]
  else if label.startsWith "the own test, " then [[groupOwn + stageOfLabel label]]
  else []

/-- `ProofFile.rootsOfSent`'s text, with the groups: a message without a sample joins none. -/
def rootsWithGroups (codes : Codes) (sent : List OracleNotice) (gs : List (List Nat)) :
    Option (List ProofFile.Root) :=
  (layTrees codes sent.toArray).map fun L =>
    L.shapes.toList.zipIdx.map fun t =>
      let mine := (sent.zipIdx.filter fun y => L.tree.getD y.2 0 == t.2).mergeSort fun a b =>
        L.part.getD a.2 0 ≤ L.part.getD b.2 0
      { logLength := t.1.logN, words := t.1.mainWidth + t.1.maskWidth
        tenants := mine.map fun y =>
          { ProofFile.tenantOf y.1 with
            groups := if y.1.shape.answers != 0 then gs.getD y.2 [] else [] } }

/-- What is told of a tree, with every tenant's groups struck. -/
def withoutGroups (r : ProofFile.Root) : ProofFile.Root :=
  { r with tenants := r.tenants.map fun t => { t with groups := [] } }

/-- `ProofFile.toldChain`'s text, with the groups; refused unless, with the groups struck, it is that
function's own table. -/
def toldOfChain (at_ : String) (c : ChainSends) (P : Fmt.Plan) (extra : List Sent)
    (held : Option OracleNotice) : Except String (List ProofFile.Root) := do
  let plain ← ProofFile.toldChain at_ c P extra held
  let off := P.entries.length - P.rounds.length
  let l ← (c.sends.mapM fun x => (rootsWithGroups c.codes x.sent
      (groupsAtLabel x.label)).map fun l => l.map fun r => (x.entry - 1 - off, r)).elim
    (.error (at_ ++ ": the oracle messages of a sending cannot be placed in trees")) .ok
  let more : List (Nat × ProofFile.Root) := extra.map fun t =>
    (t.round, { logLength := t.a, words := t.W, tenants := held.toList.map ProofFile.tenantOf })
  let mine := ((l.flatten ++ more).mergeSort fun a b => a.1 ≤ b.1).map (·.2)
  if mine.map withoutGroups != plain then throw (at_ ++
      ": the tenants with groups, the groups struck, are not the tenants' table")
  pure mine

/-- What is told of the three chains' trees, at a shape, three plans and three chains' sendings. -/
def toldOfPlans (S : LinShape) (P₀ P₁ P₂ : Fmt.Plan) (c : ChainSends × ChainSends × ChainSends) :
    Except String (List ProofFile.Root × List ProofFile.Root × List ProofFile.Root) := do
  let mask := S.testOmega.head?.map fun st => foldMaskNotice (ioppFoldShape st {})
  let t₀ ← toldOfChain "the tenants, first chain" c.1 P₀ [] none
  let t₁ ← toldOfChain "the tenants, shared chain" c.2.1 P₁ (ownMasks c.2.1.codes S P₁.rounds) mask
  let t₂ ← toldOfChain "the tenants, second chain" c.2.2 P₂ [] none
  pure (t₀, t₁, t₂)

/-- The same, of the planner's answer and the sendings. -/
def toldOfMade (m : Made) : Except String (List ProofFile.Root × List ProofFile.Root × List ProofFile.Root) :=
  toldOfPlans m.p.chains.made.sized.key.once.shape m.p.chains.key.oneTime.given.plan
      m.p.chains.key.shared.given.plan m.p.chains.key.second.given.plan m.key

/-! ## 2 One source -/

/-- What is made of the three public files alone. -/
structure KeySource where
  k : KeyChains
  /-- the planner's sized values, by which the sendings, the declared rounds and the tenants were
  cut (Johnson/G/Sends.lean:139-150; RoundsOfPlan.lean:397-400) -/
  cutShape : LinShape
  cutCodes : Codes × Codes × Codes
  cutIdx : OracleNotice
  cutRanges : WfPublic
  cutSamples : Nat
  D : Decl3
  told : List ProofFile.Root × List ProofFile.Root × List ProofFile.Root
  /-- the units of rows of the committed matrix, as the layout that both sides form from the public
  files has them (OnBytes/Plan/FromLayout.lean) -/
  units : List Plan.RowUnit

/-! ## 2b The values against their own bytes; the declared rounds and the tenants against the values
-/

/-- Two chains' parameters as read are the same: the bytes, the plan word by word, the digest, the
items. -/
def sameGiven (a b : Given) : Bool :=
  a.bytes == b.bytes && a.plan.field == b.plan.field && a.plan.salt == b.plan.salt &&
      a.plan.nonce == b.plan.nonce && a.plan.posB == b.plan.posB &&
    a.plan.samples == b.plan.samples && a.plan.saved == b.plan.saved &&
        a.plan.entries == b.plan.entries && a.cfg == b.cfg && a.items == b.items

/-- Two keys' three chains are the same, field by field. -/
def sameKeyChains (a b : KeyChains) : Bool :=
  sameGiven a.oneTime.given b.oneTime.given && a.oneTime.indexMasks == b.oneTime.indexMasks &&
      a.oneTime.ranges == b.oneTime.ranges && a.oneTime.binding == b.oneTime.binding &&
    a.oneTime.codes == b.oneTime.codes && a.oneTime.lin == b.oneTime.lin &&
        sameGiven a.shared.given b.shared.given && a.shared.codes == b.shared.codes &&
        a.shared.lin == b.shared.lin &&
    sameGiven a.second.given b.second.given

/-- **"read"**: every value of k is the program's own reading (Params/Chains.lean:254-262;
Given.lean:49-51) of the bytes that k itself holds as the bytes as they are hashed. That these are
the bytes that are hashed is the frame's matter. -/
def readAgainOk (k : KeyChains) : Bool :=
  match KeyChains.read k.oneTime.given.bytes k.shared.given.bytes k.second.given.bytes with
  | some k' => sameKeyChains k' k
  | none => false

/-- Johnson/G/Sends.lean:123-135 (the function `one` inside `sendsOf`), its text, at a plan's
entries as read. -/
def sendsOfChain (file : String) (ch : Nat) (codes : Codes) (l : List Johnson.G.Listed)
    (es : List Fmt.Entry) : Except String ChainSends := do
  let R := es.toArray
  let seeds := es.zipIdx.filter fun r => r.1.name == "SEND seed"
  unless seeds.length == l.length do
    throw s!"{file} {ch}: {l.length} sendings listed, {seeds.length} entries SEND seed"
  let out ← (seeds.zip l).mapM fun (r, s) => do
    unless treesOf codes s.sent.toArray == some r.1.roots do
      throw s!"{file} {ch}, entry {r.2 + 1} ({s.label}): the trees are not the entry's roots"
    match R[r.2 + 1]? with
    | some b => pure (⟨r.2 + 1, s.label, s.sent, r.1, b⟩ : Sending)
    | none => throw s!"{file} {ch}, entry {r.2 + 1}: no entry behind it"
  pure ⟨file, ch, codes, out⟩

/-- The key's three chains' sendings, of k alone: the three lists of Johnson/G/Sends.lean:139-146,
at the values as read. -/
def sendsOfKey (k : KeyChains) : Except String (ChainSends × ChainSends × ChainSends) := do
  let o := k.oneTime
  let K := o.lin
  let x := o.ranges
  let a := o.given.plan.samples
  let w ← Johnson.G.wSend K
  let sh ← Johnson.G.linSharedSends K a
  pure (← sendsOfChain "key" 0 o.codes
          ([⟨"the index-mask message", [o.indexMasks]⟩, ⟨"the multiplicities",
              (Wf.messageOf x).toList⟩] ++
            Johnson.G.ioppSends "the ranges' test" a x.choice.masksRide 1 x.stages ++
                [w]) o.given.plan.entries,
        ← sendsOfChain "key" 1 o.codes sh k.shared.given.plan.entries,
        ← sendsOfChain "key" 2 o.codes (Johnson.G.ioppSends "the own test" a K.choice.masksRide 1
            K.testOwn) k.second.given.plan.entries)

/-- The declared rounds and the tenants with their groups, of k alone: the rule (`fileOf`,
Johnson/G/RoundsOfPlan.lean:367, with `declKOf`'s two last arguments) and `toldOfPlans`, at
`sendsOfKey`. -/
def madeAgain (k : KeyChains) : Except String (Decl3 × (List ProofFile.Root × List ProofFile.Root × List
    ProofFile.Root)) := do
  let c ← sendsOfKey k
  let D ← Johnson.G.OfPlan.fileOf "key file" k.oneTime.lin k.oneTime.given.plan k.shared.given.plan
      k.second.given.plan c.1 c.2.1 c.2.2
    (fun ts _ => Johnson.G.OfPlan.onceOpens ts) (fun t => t.tag == .indexMask)
  pure (D, ← toldOfPlans k.oneTime.lin k.oneTime.given.plan k.shared.given.plan k.second.given.plan
      c)

/-- **"made"**: Y.D and Y.told are these, whole. -/
def madeAgainOk (Y : KeySource) : Bool :=
  match madeAgain Y.k with
  | .ok x => decide (x.1 = Y.D) && x.2 == Y.told
  | .error _ => false

/-! ## 3 The public tests -/

/-- Blk.newGroup (Ground.lean:1269-1275) and what of Blk.join is public (Ground.lean:1288-1294): the
group's two codes are there, the mask code's words no longer than the main code's; each member's
shape says that it is
sampled; its main rows, if it has any, are under the group's code, its mask rows under the group's
mask code. -/
def joinPublicOk (codes : Codes) (code maskCode : Nat) (members : List OracleShape) : Bool :=
  (match codes.base[code]?, codes.mask[maskCode]? with
   | some c, some z => decide (z.logN ≤ c.logN)
   | _, _ => false) &&
  members.all fun s => s.answers != 0 && (s.mainRows == 0 || s.code == code) && (s.maskRows == 0 ||
      s.maskCode == maskCode)

/-- ioppVerify's two public tests (Prox.lean:244 | :251): the stages' sizes fit, and the group's
codes are the first stage's. (That the layout's k, h are the first stage's is asked in the steps.)
-/
def testPublicOk (codes : Codes) (samples : Nat) (stages : List IoppStage)
    (code maskCode : Nat) : Bool :=
  ioppOk codes stages samples && stages.head?.any fun t => t.code == code && t.maskCode == maskCode

/-! ### The lookup on the numbers of two digits reaches every unit of two digits

`Wf.admitted` asks that some lookup takes single entries as keys and reaches every row of the
matrix: so every entry is a byte. That a number of two digits lies in its range is the second
lookup's matter, and nothing there asks which rows that lookup reads: it is what the planner lays
(`shapeOfUnits`, OnBytes/Plan/Units.lean; C++: wf_units.h). Here it is asked of the lookups as read,
against the layout's units. The four tests on runs are the texts of `inUnit`, `chk1`, `stretchesOf`
and `chk2` of Johnson/Top/H/KeyPairs.lean, which are general in the list T; that file imports the
library's model and runs them at the reference model's units alone. -/

/-- For each unit of two digits: the first row of its low digits, and the number of rows of each
digit. -/
def twoDigitUnits (units : List Plan.RowUnit) : List (Nat × Nat) :=
  (units.filter (·.digits == 2)).map fun u => (u.firstRow, u.rows / 2)

/-- The run lies inside a stretch of T and has its number of rows as stride. -/
def runInUnit (T : List (Nat × Nat)) (r : WfRun) : Bool :=
  T.any fun t => r.stride == t.2 && decide (t.1 ≤ r.firstRow) &&
      decide (r.firstRow + r.places ≤ t.1 + t.2)

/-- Every run of the lookup does. -/
def runsInUnits (T : List (Nat × Nat)) (l : WfLookup) : Bool := l.parts.all fun p =>
    p.runs.all (runInUnit T)

/-- The stretches of rows of the runs that lie inside the stretch t and have its stride. -/
def stretchesIn (l : WfLookup) (t : Nat × Nat) : List (Nat × Nat) :=
  l.parts.flatMap fun p =>
    (p.runs.filter fun r => r.stride == t.2 && decide (t.1 ≤ r.firstRow) &&
        decide (r.firstRow + r.places ≤ t.1 + t.2)).map fun r => (r.firstRow, r.firstRow + r.places)

/-- Every stretch of T is reached, without a gap, by the runs inside it that have its stride. -/
def unitsReached (T : List (Nat × Nat)) (l : WfLookup) : Bool :=
  T.all fun t => Wf.noGap (t.1 + t.2) t.1 ((stretchesIn l t).mergeSort fun a b =>
      decide (a.1 ≤ b.1))

/-- **"weights"**: some lookup has the table, the digits' weights and the offset of the numbers of
two digits; each of its runs lies inside a unit of two digits; and every such unit is reached whole.
-/
def weightsCovered (units : List Plan.RowUnit) (x : WfPublic) : Bool :=
  let T := twoDigitUnits units
  x.lookups.any fun l => l.d == Plan.weightBits && l.digitWeight == [1,
      UInt64.ofNat (2 ^ Plan.byteBits)] && l.offset == UInt64.ofNat (2 ^ (Plan.weightBits - 1)) &&
      runsInUnits T l && unitsReached T l

/-- **The public tests by name.** o: the one-time chain's values: what chain 1's steps read. s: the
shared chain's: what chains 2 and 3's steps read. -/
def sourceClauses (Y : KeySource) : List (String × Bool) :=
  let o := Y.k.oneTime
  let s := Y.k.shared
  let S := o.lin
  let T := s.lin
  let a := o.given.plan.samples
  let m := o.indexMasks.shape
  let x := o.ranges
  let all := Y.told.1 ++ Y.told.2.1 ++ Y.told.2.2
  [ -- Key/File.lean, check, first line
    ("field", o.given.plan.field == .two),
    -- Params/Chains.lean:258-261 (KeyChains.read)
    ("setting", sameSetting o.given s.given && sameSetting o.given Y.k.second.given &&
        s.given.record.isNone && Y.k.second.given.record.isNone),
    ("codes", sameItem o.given s.given "codes" && o.codes == s.codes),
    ("shape", sameItem o.given s.given "the test on the table" && S == T),
    -- a description's plans are the declared rounds themselves: so `planOk` does not hold their
    -- entries against the rounds of k's plans, which the tests on the plan read: asked here
    ("rounds", Y.D.1.map (·.entry) == o.given.rounds && Y.D.2.1.map (·.entry) == s.given.rounds &&
        Y.D.2.2.map (·.entry) == Y.k.second.given.rounds),
    -- the values against their own bytes
    ("read", readAgainOk Y.k),
    -- the declared rounds and the tenants against the values
    ("made", madeAgainOk Y),
    -- what the declared rounds and the tenants were cut by
    ("cut", Y.cutShape == S && Y.cutCodes.1 == o.codes && Y.cutCodes.2.1 == o.codes &&
        Y.cutCodes.2.2 == o.codes && Y.cutIdx == o.indexMasks && Y.cutRanges == x &&
        Y.cutSamples == a),
    -- what this form of the blocks and of `groupsAtLabel` bears: masks ride and go ahead; the
    -- folded row's group and Omega's differ in code, W's and Omega's do not
    ("form", x.choice.masksRide && T.choice.masksRide && T.masksAhead && T.sharedSplitNeeded &&
        !T.ownSplitNeeded),
    -- Ground.lean:915 (Blk.runNamed)
    ("lengths", o.codes.lengthsOk),
    -- Key/Fixed.lean (fixedOk), conjunct by conjunct; linOk again at Lin.lean:201 and :258;
    -- Wf.admitted again, in the run, at Wf.lean:292
    ("lin", linOk o.codes S),
    ("ranges", Wf.admitted o.codes x (Wf.matrixOf S)),
    -- blocks/frame/wf_units.h; OnBytes/Plan/Units.lean (shapeOfUnits): asked of the lookups as read
    ("weights", weightsCovered Y.units x),
    -- Lkp.lean:782 (Lkp.verify: Blk.must S.ok), at each lookup as the block WF hands it
    -- (Wf.lean:320)
    ("lookups", (Wf.lookupsOf x (Wf.matrixOf S)).all (·.ok)),
    ("binding", o.binding.logLeaves == 0),
    ("messageId", x.messageId == 1),
    ("idx", m.mainRows == 0 && m.maskRows != 0 && decide (1 ≤ m.answers) &&
        decide (m.maskCode < o.codes.mask.size)),
    ("idxRoom", decide (Wf.indexMaskEntries x (Wf.matrixOf S) ≤ Send.freeMaskEntries m.maskRows
        (o.codes.mask.getD m.maskCode default).ell m.answers)),
    -- Wf.lean:296
    ("samples", x.message.shape.answers == a),
    -- Lin.lean:431-442 (memberRowsFit), what of it is public
    ("member", m.mainRows == 0 && decide (0 < m.maskRows) && decide (0 < m.answers) &&
        m.maskCode == S.ownMaskCode && decide (0 < S.kCol) && !(x.lookups.flatMap
        (·.parts)).isEmpty),
    -- Prox.lean:244 | :251-252, at the four tests
    ("test.rng", testPublicOk o.codes a x.stages x.message.shape.code x.message.shape.maskCode),
    ("test.U", testPublicOk s.codes a T.testU T.fold.u.code T.sharedMaskCode),
    ("test.O", testPublicOk s.codes a T.testOmega T.omega.code T.sharedMaskCode),
    ("test.own", testPublicOk s.codes a T.testOwn T.w.code T.ownMaskCode),
    -- Ground.lean:1269-1275 | :1288-1294, at the four first groups
    ("join.rng", joinPublicOk o.codes x.message.shape.code x.message.shape.maskCode
        [x.message.shape]),
    ("join.U", joinPublicOk s.codes T.fold.u.code T.sharedMaskCode [T.fold.u, T.sharedSplit]),
    ("join.O", joinPublicOk s.codes T.omega.code T.sharedMaskCode [T.omega, T.sharedSplit]),
    ("join.own", joinPublicOk s.codes T.w.code T.ownMaskCode [m, T.w, T.omega]),
    -- Lin.lean:250-254 | :269 | :309 (linAloneInItsTree): what a later chain's test reads too has a
    -- tree to itself
    ("alone", Y.told.2.1.all fun r => !(r.tenants.any fun t => t.groups.contains groupOwn) ||
        r.tenants.length == 1),
    -- the groups told: a tenant joins a group just if it says that it is sampled
    ("grouped", all.all fun r => r.tenants.all fun t => t.sampled != t.groups.isEmpty) ]

/-- All clauses hold. -/
def sourceOk (Y : KeySource) : Bool := (sourceClauses Y).all (·.2)

/-- The names of the clauses that fail. -/
def sourceFailing (Y : KeySource) : List String := ((sourceClauses Y).filter (!·.2)).map (·.1)

/-- Every word of the key is below the prime (OnBytes/Field/Ext.lean:45 okE): the record's answers,
each seed's point, each seed's factor. The key is no view: the test on the views' words does not
reach it. -/
def keyWordsBelow (k : TableKey) : Bool := k.record.all okE && k.seeds.all fun z => z.z.all okE &&
    okE z.beta

/-- **The test on the instance alone**: the key names the statement's item 0; its sizes fit the
table's shape (Foldeq.lean, TableKey.fits); every word of it is below the prime; no seed of the
record has the factor 0 (isZeroE: on words
below the prime this says that the element is 0: Ext.lean:47-48). That the seeds are those of the
table's name is the frame's. -/
def instanceOk (S : LinShape) (x : Xi) : Bool :=
  x.key.item == 0 && x.key.fits S.fold.index && keyWordsBelow x.key &&
      x.key.seeds.all fun z => !isZeroE z.beta

end VerifiableInference.Desc.Key
