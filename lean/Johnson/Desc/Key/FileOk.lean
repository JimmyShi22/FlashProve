-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/FileOk.lean: the tests on the plan that tie a key file's three chains, by name.
Definitions only, all computable; nothing is proved here.

A block's own test on the plan looks at its own place. What ties places and chains is asked here, of
public values alone: the three chains' values as read back from the parameter bytes, the declared
rounds, the tenants as told, the planner's sized values and plans. Each test is a pair of a name and
a Boolean, so that a print can say which one fails. The chains are numbered first, second (shared),
third; the verifier program calls the third `second`.

Main names.
  Source: what the description is made of.
  fileClauses: all the tests by name.
  joinsGroup, shapeClauses, planClauses, stagesAsSized: its parts that are written here.
  testBase, openedByPlan, openedAsTold: which test's stage opens which tree, off the declared
    rounds; held against the tenants as told.
  chainOfGroup, toldAndOpened, growRenaming, openedInBlocks: the like, held against the
    description's own roots, up to a renaming of groups.

Limits. A test's name is its only word: it is no proposition. The level of security hangs on three
tests together: "prices" (`keyOk`, Johnson/Desc/MadeOk.lean) prices the planner's plans; "priced"
and "declared" say that these are the plans in the parameter bytes and the declared rounds. `Source`
is a free record: that Y, chains and set come of one maker is asked only as far as "cut", "priced",
"declared" and the last of `shapeClauses` tie them; `set` is held against nothing. `openedInBlocks`
does not ask that a later chain's test which opens a tree is told by the block that sends the tree.
Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.Source
import Johnson.Desc.Key.Places
import Johnson.Desc.Key.Ranges
import Johnson.Desc.Key.Plan.Eight
import Johnson.Desc.MadeOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

open OnBytes OnBytes.Params

/-- What the description is made of. -/
structure Source where
  /-- the three chains' public values, the declared rounds and the tenants as told -/
  Y : KeySource
  /-- what the planner has sized, planned and read back of all chains; the key's parts are read -/
  chains : Model.Verify.Chains
  /-- the sized key's setting -/
  set : Setting

/-- The three public conditions under which a message of the shape s is a member of a group with
these two codes: it counts an answer; its main rows, if it has any, stand under the group's code;
its mask rows, if it has any, under the group's mask code. -/
def joinsGroup (code maskCode : Nat) (s : OracleShape) : Bool :=
  s.answers != 0 && (s.mainRows == 0 || s.code == code) && (s.maskRows == 0 ||
      s.maskCode == maskCode)

/-- **Twelve tests on the three chains' public values, by name.** made: the shape off which the
declared rounds and the tenants are made. -/
def shapeClauses (k : KeyChains) (made : LinShape) : List (String × Bool) :=
  let a := k.oneTime
  let S := k.shared.lin
  let idx := a.indexMasks.shape
  let split := ((linMessageOmega S)[1]?).map (·.shape)
  [("the three plans' field is the one that the steps are typed at",
      a.given.plan.field == .two && k.shared.given.plan.field == .two &&
      k.second.given.plan.field == .two),
   ("the program's own Key.admitted at the one-time chain's values", Key.admitted a),
   ("the lookups' own message's answers are the plan's samples",
       a.ranges.message.shape.answers == a.given.plan.samples),
   ("the index-mask message fits the own group (memberRowsFit's public half)",
      idx.mainRows == 0 && decide (0 < idx.maskRows) && decide (0 < idx.answers) &&
          idx.maskCode == S.ownMaskCode && decide (0 < S.kCol)),
   ("ioppOk at chain 3's test", ioppOk k.shared.codes S.testOwn k.second.given.plan.samples),
   ("join: the lookups' own message and the ranges' group",
       (a.ranges.stages.head?.any fun t => joinsGroup t.code t.maskCode a.ranges.message.shape)),
   ("join: G_u and the split's message and the folded row's group",
       joinsGroup S.fold.u.code S.sharedMaskCode S.fold.u &&
       split.any (joinsGroup S.fold.u.code S.sharedMaskCode)),
   ("join: Omega and the split's message and Omega's group",
       joinsGroup S.omega.code S.sharedMaskCode S.omega &&
       split.any (joinsGroup S.omega.code S.sharedMaskCode)),
   ("join: the index-mask message, W and Omega and the own group",
       joinsGroup S.w.code S.ownMaskCode idx && joinsGroup S.w.code S.ownMaskCode S.w &&
       joinsGroup S.w.code S.ownMaskCode S.omega),
   ("one setting in the three chains; the same items «codes» and «the test on the table» in chains \
         1 and 2; no record's entry in chains 2 | 3 (KeyChains.read's own tests)",
      sameSetting a.given k.shared.given && sameSetting a.given k.second.given &&
          sameItem a.given k.shared.given "codes" &&
          sameItem a.given k.shared.given "the test on the table" &&
        k.shared.given.record.isNone && k.second.given.record.isNone),
   ("chains 1 and 2 hold the same codes and the same shape, by value",
       decide (a.codes = k.shared.codes) && decide (a.lin = S)),
   ("the shape off which the declared rounds and the tenants are made is that shape",
       decide (made = S))]

/-- The number of the first stage's group of the t-th test (from 1) of chain c (from 0):
`groupRanges`, `groupFolded`, `groupOmega`, `groupOwn`. Nothing for a test that a key file has
not. -/
def testBase (c t : Nat) : Option Nat :=
  match c, t with
  | 0, 1 => some groupRanges
  | 1, 1 => some groupFolded
  | 1, 2 => some groupOmega
  | 2, 1 => some groupOwn
  | _, _ => none

/-- **Which test's which stage opens which tree, off the declared rounds alone**: triples (the
sender's chain from 0, the tree's number there, the group). A test begins at a round named "BAT";
its j-th round (from 0) that opens trees opens the members of its stage j's group. A round that
opens trees in front of a chain's first test, or in a test that a key file has not, gives the group
`noId`, which nobody is told to join. -/
def openedByPlan (D : Johnson.G.OfPlan.Decl3) : List (Nat × Nat × Nat) :=
  [D.1, D.2.1, D.2.2].zipIdx.flatMap fun c =>
    (c.1.foldl (fun (a : List (Nat × Nat × Nat) × Nat × Nat) d =>
      if d.entry.name == "BAT" then (a.1, a.2.1 + 1, 0)
      else if d.opens.isEmpty then a
      else
        let g := ((testBase c.2 a.2.1).map (· + a.2.2)).getD noId
        (a.1 ++ d.opens.map fun o => match o.2 with
          | .own n => (c.2, n, g)
          | .taken ch sent => (ch, sent, g), a.2.1, a.2.2 + 1)) ([], 0, 0)).1

/-- **The test "opened"**: at every sampled tenant as told, the groups that it is told to join are
just the groups whose tests' stages open its tree. -/
def openedAsTold (Y : KeySource) : Bool :=
  let O := openedByPlan Y.D
  [Y.told.1, Y.told.2.1, Y.told.2.2].zipIdx.all fun c => c.1.zipIdx.all fun r =>
    let want := ((O.filter fun o => o.1 == c.2 && o.2.1 == r.2).map (·.2.2)).mergeSort (· ≤ ·)
    r.1.tenants.all fun t => !t.sampled || t.groups.mergeSort (· ≤ ·) == want

/-- The chain (from 0) in which the test of a group runs, by `openedByPlan`'s numbers. -/
def chainOfGroup (g : Nat) : Nat :=
  if g < groupFolded then 0 else if g < groupOwn then 1 else 2

/-- For each sampled tenant that the blocks of chain c (from 0) tell: the groups that it is told to
join; the groups, by `openedByPlan`'s numbers, whose tests' stages open its tree and run in chain c
itself; and all such groups. -/
def toldAndOpened (T : VerifiableInference.Desc.BookPlan.SentOraclesByChain) (D : Johnson.G.OfPlan.Decl3)
    (c : Nat) : List (List Nat × List Nat × List Nat) :=
  let O := openedByPlan D
  (T.getD c []).zipIdx.flatMap fun r =>
    let all := (O.filter fun o => o.1 == c && o.2.1 == r.2).map (·.2.2)
    (r.1.tenants.filter (·.sampled)).map fun t => (t.groups, all.filter (chainOfGroup · == c), all)

/-- A renaming of labels grows by a pair where just one label and just one number of a tenant are
still free. The numbers: those of the own chain's tests, or, where no test of the own chain opens
the tree, all. One to one by its make. -/
def growRenaming (ρ : List (Nat × Nat)) (p : List Nat × List Nat × List Nat) : List (Nat × Nat) :=
  match p.1.filter (fun x => !ρ.any (·.1 == x)),
      (if p.2.1.isEmpty then p.2.2 else p.2.1).filter (fun y => !ρ.any (·.2 == y)) with
  | [x], [y] => (x, y) :: ρ
  | _, _ => ρ

/-- **The test "opened" on the description's own roots.** The kinds' blocks number their groups each
in its own way, and chain by chain; and of a tree that a later chain's test opens too, the sending's
block tells its own chain's group alone. So, for each chain: there is a renaming of its blocks'
labels, one to one, found by `growRenaming` in three passes, under which, for every sampled tenant
of the description's own roots, every group that it is told to join is one whose test's stage opens
its tree, none twice, and every test of its own chain that opens its tree is among them. A tenant
without a sample joins no group. Not asked: that a later chain's test which opens the tree is told;
of the tenants as told `openedAsTold` asks that. -/
def openedInBlocks (T : VerifiableInference.Desc.BookPlan.SentOraclesByChain)
    (D : Johnson.G.OfPlan.Decl3) : Bool :=
  ((List.range 3).all fun c =>
    let ps := toldAndOpened T D c
    let ρ := (List.range 3).foldl (fun r _ => ps.foldl growRenaming r) []
    ps.all fun p =>
      let I := p.1.filterMap fun x => (ρ.find? (·.1 == x)).map (·.2)
      I.length == p.1.length && I.eraseDups.length == I.length && I.all p.2.2.contains &&
          p.2.1.all I.contains) &&
    T.all fun c => c.all fun r => r.tenants.all fun t => t.sampled || t.groups.isEmpty

/-- **Nine tests on the plans' entries, by name**: `Plan.clausesAt` at the numbers of rounds that
this description's own blocks take of the three chains (the two seals' rounds not counted), and
"plan.seal": the first and the second (shared) chain's plans end in a round named "SEAL"; the third
chain's plan (the program's `second`) has none. -/
def planClauses (k : KeyChains) (r₁ r₂ r₃ : Nat) : List (String × Bool) :=
  Plan.clausesAt k (r₁ - 1) (r₂ - 1) r₃ ++
  [("plan.seal: chains 1 and 2 end in a round SEAL; chain 3 has none",
      (k.oneTime.given.rounds.getLast?).any (·.name == "SEAL") &&
      (k.shared.given.rounds.getLast?).any (·.name == "SEAL") &&
      !k.second.given.rounds.any (·.name == "SEAL"))]

/-- **A test's sized stages are what the values in the parameter bytes say**: the place's numbers
have a stage for each stage of the shape; the two codes' three numbers are those of the codes under
the stage's two numbers; k and h are the stage's; the place names just these pairs of numbers. The
numbers of positions are the planner's: their prices are `keyOk`'s matter. -/
def stagesAsSized (codes : Codes) (st : List IoppStage) (N : H2U.PlaceNums) : Bool :=
  N.nums.stages.length == st.length && N.idx == st.map (fun s => (s.code, s.maskCode)) &&
    (N.nums.stages.zip st).all fun x =>
      match codes.base[x.2.code]?, codes.mask[x.2.maskCode]? with
      | some c, some z =>
        decide (x.1.C = ⟨c.logN, c.ell, c.r⟩) && decide (x.1.Z = ⟨z.logN, z.ell, z.r⟩) &&
          x.1.k == x.2.k && x.1.h == x.2.h
      | _, _ => false

/-- **The tests on the plan that tie the chains, by name.** r₁ r₂ r₃: the rounds that this
description's own blocks take of the three chains. `sourceClauses`, `shapeClauses` and
`planClauses`; then: the prices; that the priced plans are those in the parameter bytes;
`openedAsTold`; that the declared rounds' entries are the plans' rounds; `stagesAsSized` at the four
proximity tests; that the digest is not 32 zero bytes; and, at the three later proximity tests'
places, what the ranges' test's seat asks on the plan (`asksOnPlan`). Of `asksOnPlan`'s four
questions three are ASKED TWICE at these places: the proximity test's own test on the plan asks
`p.early`, `p.answers == 1` and `cutOk` itself (Johnson/Desc/K12/JoinGuarded.lean); the fourth,
`spendOk`, no other test asks: it follows from that test's yes by a theorem
(`H2K.Made.spendOk_of_planOk`, Johnson/Desc/K12/Law/SpendMade.lean).
Where the plan has no place for Omega's test, "stages.O" asks that the shape has no such test, and
"k12.O" is true. -/
def fileClauses (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    (r₁ r₂ r₃ : Nat) : List (String × Bool) :=
  let k := X.Y.k
  let c := X.chains
  sourceClauses X.Y ++ shapeClauses k c.made.sized.key.once.shape ++ planClauses k r₁ r₂ r₃ ++
  [("prices: every round of the key's three plans holds at the target 128, with at most 32 bits of \
        work (Desc.keyOk, Desc/MadeOk.lean)", VerifiableInference.Desc.keyOk c.made),
   ("priced: the plans that are priced are the plans in the parameter bytes, entry by entry",
       decide (c.made.key.map (·.plan.entries) = [k.oneTime.given.plan.entries,
       k.shared.given.plan.entries, k.second.given.plan.entries])),
   ("opened: a sampled tenant as told joins just the groups whose tests' stages open its tree",
       openedAsTold X.Y),
   ("declared: the declared rounds' entries are the rounds of the plans in the parameter bytes",
      decide (X.Y.D.1.map (·.entry) = k.oneTime.given.rounds) &&
          decide (X.Y.D.2.1.map (·.entry) = k.shared.given.rounds) &&
          decide (X.Y.D.2.2.map (·.entry) = k.second.given.rounds)),
   ("stages.rng", stagesAsSized k.oneTime.codes k.oneTime.ranges.stages N),
   ("stages.U", stagesAsSized k.shared.codes k.shared.lin.testU P.U),
   ("stages.O",
      match P.O with
      | some nO => stagesAsSized k.shared.codes k.shared.lin.testOmega nO
      | none => k.shared.lin.testOmega.isEmpty),
   ("stages.own", stagesAsSized k.shared.codes k.shared.lin.testOwn P.W),
   ("digest: the digest handed in is not 32 zero bytes (OnBytes/Key/Table.lean: tableOk)",
       k.oneTime.given.cfg != Fmt.zero32),
   ("k12.U: at the folded row's test's place, on the plan: what the ranges' test's seat asks on \
         the plan (Key.asksOnPlan)", asksOnPlan (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U)),
   ("k12.O: the same at Omega's test's place, where the shared chain has one",
      match P.O with
      | some nO => asksOnPlan (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO)
      | none => true),
   ("k12.own: the same at the own test's place",
      asksOnPlan (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W))]

end VerifiableInference.Desc.Key
