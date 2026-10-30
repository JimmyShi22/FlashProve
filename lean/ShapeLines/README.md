# ShapeLines: the run on shapes at the stored full-size files, shown by closed lines

Terms: [TERMS.md](../TERMS.md); words: [GLOSSARY.md](../GLOSSARY.md).

## In short

`ShapeLines/` is the third Lean library of `lean/lakefile.toml`, beside the main library and
`AtFullSide/`. It holds computed facts about one input: the library's written copies of the public
files of the stored full-size example. The main library does not import it.

- **What it says.** The proof file's first chain is a list of 358 blocks, called members here. A
  member's checks on structure can be run on a *shape*, which keeps of the chain's state what they
  read or update, and no field element. The main statement, `runOnShapes_toEnd`
  (`FirstChainRuns.lean`), says that at those files this run on shapes, started from the first
  shape, returns a written value after all 358 members.
- **How.** Lean's kernel computes. Shapes along the run are written out as Lean terms (`Borders/`:
  most of this folder's bytes). A *closed line* is an equation whose left side is a closed term;
  many say that the run from one written value returns the next. One of them, `frontMember_line`
  (`Front/FrontMember.lean`), states `atXLC (fun X => wholeB (runH closingHint X 0 1 startShA)
  border1) = true`: from the first shape, member 0 returns `border1`. Its proof term is `Eq.refl
  true` (tactic `kernel_rfl`, `Johnson/Unfolds/KernelRfl.lean`): the kernel evaluates the left side
  when it checks the declaration. Ordinary theorems join the lines.
- **`Door/`** holds one more closed line with its control (`endOk_358`, `endOk_start`, by `decide
  +kernel`) and theorems over the joined facts; its files' heads say what these show.
- **Who imports it.** `AtFullSide/Honest/TheOneObjectValue.lean` and
  `AtFullSide/Honest/LastSocketsFilled.lean`; through them the files that state
  `AtFullSide.Honest.complete_in_scope`,
  `VerifiableInference.Compilation.zkOnServedRequests_inScope` and
  `VerifiableInference.Compilation.finalAtT1_filled`. What these say, and under which hypotheses, is
  told where they stand.
- **Why a library of its own.** Lake sets Lean's command-line options library by library. These
  files are compiled with a thread stack of 256 MiB (`--tstack=262144`); `AtFullSide/` has 128 MiB,
  at which one line here ends with "deep recursion". They are also heavy: see "How to build, and
  what it costs".
- **How to build.** `lake build ShapeLines`. The library is no default target, but `AtFullSide` is
  one and imports it, so a plain `lake build` compiles nearly all of these files as well.
- **What it must not be taken for.** The closed lines and their joins are facts on shapes, at the
  full size alone: no field element is read, and no member is shown to accept. A closed line is
  checked by Lean's kernel, once, when its file is compiled. See "Limits" below and `lean/LIMITS.md`
  (L69).

## What this library is for

Paths. A file named without a folder lies in `Johnson/AtFull/Shape/`; `Lines/…` lies there too.
`ClosingHint.lean`, `FirstChainRuns.lean`, `README.md`, `Front/`, `Layers/`, `Attention/`, `Head/`,
`Back/`, `Borders/`, `Equations/` and `LastChain/` lie in this folder; so does `Door/`, of which
this page says no more than the lines above: below, "this library" means this folder without
`Door/`. `Johnson/…`, `OnBytes/…`, `AtFullSide/…`, `E2E/…` and `lakefile.toml` lie in `lean/`.

`first_chain_debts` and `first_chain_debts_halved` (`RuleAtTable.lean`) have a premise `hyes`: the
*run on shapes* over the first chain's 358 members returns when it is started from a first shape.
These two laws conclude AcceptedJ and NextJ at the first chain's members. That file's head calls
these two debts of a rule on the whole proof file, which it names `file_acceptsJ`, and says what
else that rule asks and where it ends; the rule is no part of this library. Files outside this
library take the two as fields (`AtFullSide/Honest/ThreadsAtTheTerm.lean`); what these files reach
is theirs to say. The theorems on the honest provers lie above this library (`lean/LIMITS.md`, L88
to L93). `table_yes_of_runsAll` (`JoinTable.lean`) draws `hyes` at `startShA` from facts of the form
`RunsAll m n a b` (`JoinAll.lean`): at every record that `publicOfO` returns at the stored full-size
public files, the n members from member m on, started from the shape a, return the shape b.
`RuleAtTable.lean`'s head says that no theorem shows that the run returns, and `JoinTable.lean`'s
that the library shows no fact of this form: both files lie in the main library, which does not
import this one. The facts are shown here.

This library shows 28 such facts, each starting where the one before ends, and joins them:

| piece | members | where |
|---|---|---|
| the front | 0 | `Front/` |
| the twelve layers' links (link l, l even, l < 24) | 14 l + 1 to 14 l + 14 | `Layers/` |
| the twelve attention links (link l, l odd, l < 24) | 14 l + 1 to 14 l + 14 | `Attention/` |
| the head's link | 337 to 352 | `Head/` |
| the finish | 353 | `Back/` |
| the proximity test to the seal | 354 to 357 | `Back/` |

`FirstChainRuns.lean` has the joined facts: `runOnShapes_toTest : RunsAll 0 354 startShA
border354LessPair`, `runOnShapes_toEnd : RunsAll 0 358 startShA border358`, `runOnShapes_atARecord`
(there is a record, and at it the run returns) and `runOnShapes_yes_underHead`: under the head at
`VerifierAndGoals.storedPublicFiles` and where baseOf returns, `table_yes_of_runsAll`'s conclusion.
The general laws that the pieces call lie in `JoinAll.lean` (`one_all`, `four_all`) and under
`Lines/`.

Beside the 28 pieces the library shows 25 facts of a second form, in `Equations/`. Let b be the
number of a member "the one equation": b = 14 l + 11 for l below 24, or b = 349. The shape that the
run on shapes returns from `startShA` over the first b members, that is the shape before member b,
passes the test `equationTest`: `RunsToTested 0 b (fun _ => startShA) equationTest`
(`Lines/JoinTested.lean`). `Equations/TestedBeforeEquations.lean` has the fact at all 25 numbers
(`firstChain_testedBeforeEquation`, `firstChain_testedBeforeHeadEquation`). It is meant for premises
that ask `eqSizesYes … = true` (`Johnson/Desc/ProofFile/Honest/K9/EqValuesJ.lean`). Each of the 25
files has one closed line, which runs one member, 14 l + 10 or 348, and tests its outcome; the
members before come of closed lines of the 28 pieces.

| fact | members run | where |
|---|---|---|
| the test's definition | | `Equations/EquationTest.lean` |
| a layers' link l (l even) | 14 l + 1 to 14 l + 10 | `Equations/LayersLink‹l›BeforeEquation.lean` |
| an attention link l (l odd) | 14 l + 1 to 14 l + 10 | `Equations/AttentionLink‹l›BeforeEquation.lean` |
| the head's link | 337 to 348 | `Equations/HeadLinkBeforeEquation.lean` |
| all 25, from `startShA` | 0 to b − 1 | `Equations/TestedBeforeEquations.lean` |
| three controls with their witnesses, and one line on a limit | | `Equations/EquationTestControls.lean` |

`LastChain/` holds six closed lines on the proof file's last chain (one fact, the same fact once
more under another name, three controls, of which one is on `startShA`, one on a limit) and one
call. The fact, `last_run_at_border358` (`LastChain/LastRunAtBorder358.lean`): a run of guards on
shapes over the last chain's four members returns, started from the shape that `doorShape` makes of
two ends: `handedOf border358`, and `writtenSharedEnd`. It is meant for a premise of
`last_end_accepts` and `taken_sources_accept` (`AtFullSide/LaterThreads/LastRunClosed.lean`), which
have further premises; no file of this library calls them by name (`sockets_three_at_the_letters`
reaches the first through `last_end_accepts_of_the_run`). `LastChain/LastRunControls.lean` has the
controls and the limit. `LastChain/SocketsThreeAt358.lean` states the fact once more as `lastRunAt
border358 = true`, the form in which `LastChainDebtsAtTheNames`
(`AtFullSide/LaterThreads/OwesAndYesThreeAtTheLetters.lean`) asks it, and lays it with
`runOnShapes_toEnd` into `sockets_three_at_the_letters`
(`AtFullSide/LaterThreads/SocketsThreeAtTheLetters.lean`): `sockets_three_at_358` concludes that
law's two statements, `Socket.owes₃` and `Socket.yes₃`, under the premises that stay: see "Limits".

## Words

- **First chain, member.** The proof file's first chain is a flat list of 358 blocks. A member is
  one of them, by its number, 0 to 357 (`Table.lean`).
- **Link.** Link l, for l = 0 to 23, is the fourteen members 14 l + 1 to 14 l + 14: a layers' link
  at even l, an attention link at odd l. The head's link has sixteen members. The ninth member of a
  link (the eleventh of the head's) is its *batching*.
- **Shape** (`ShA`, `FrameForm.lean`). A pair. Its first component is the *chain's shape*
  (`ChainSh`, `Johnson/Desc/First/Shape/Chain.lean`): nineteen components. By that file's head a
  part of the chain's state is meant to be there only if a guard on the structure reads it or an
  update needs it; it holds no field element, and some parts have no component. Its second component
  is the rows' makes.
- **Run on shapes.** The table's steps on shapes (`TableOfSteps.lean`), member after member.
- **Record.** The public record (`Verify.Public`) that `publicOfO` makes from the public files.
- **The table's second text** (in some heads: the text of the table over a record of letters).
  `shapeL (LWn X)`: the table's steps written over letters, some read off a record X, some written
  constants of the full size, with numerals that are constants too (`LettersRun.lean`,
  `LettersNumerals.lean`). So LWn X is no test on X; a run over this text may return where the
  table's first text would return an error, and is by itself no fact on the table's own run.
  `RunsAll` speaks of this text. `yes_of_publicN` (`YesAtZFullN.lean`) carries «it returns», not the
  value, from it to the table's own steps, under the head, baseOf's return and the layout file's
  size.
- **Second text of a step, light step.** A function that stands in for a step's function so that
  Lean's kernel can evaluate it. Some are proved equal to that function: `closeGFH` to `closeGF` (a
  link's closing), `batchGSL` to `batchGS` (a batching), `callsGL` to `callsG` (a lookup on the
  calls); `JoinHalves.lean` and `BatchSplit.lean` cut `batchGS` in two parts. Two are proved one way
  only: where they return, the cell of the table's second text returns the same:
  `layersBatchingLight` (the batching of a layers' link, if own comes of a hearing) and
  `headBatchingLight` (member 347).
- **atXLC, atXHC, atXLLight.** Frames that hand a test a record made by the makers' twins from the
  written files, with stand-ins where three further makers return nothing; under atXLC and atXHC
  sixteen counts are written as numerals (`AtX.lean`, `AtXCounts.lean`,
  `Lines/Layers/PublicRecordLight.lean`). Under atXLC the head's layout is its maker's whole run;
  under atXHC it is made without the tests on the calls' tables: the lines on members 340 to 347 are
  stated under atXHC. atXLLight is a second text of atXL, made by rewriting; what it spares is
  stated nowhere. A law carries a test's `true` under each frame to what `publicOfO` returns, under
  the layout file's size.
- **Border n, written value.** `Borders/` holds written values: closed terms in Lean source.
  `border‹n›` is a *candidate* for the shape before member n (`border358`: after the last member).
  The number is a label: that the run reaches the value is what the pieces before it show.
- **look, lookHeard, own.** Three of the chain's shape's nineteen components. Inside a link look and
  lookHeard hold the lookup's record; own is the record that the layers' own rounds (the fourth
  member of a layers' link) leave. They are long.
- **…LessPair.** A written value in which look and lookHeard are none (`PairAside.lean`). Inside a
  link the line after it starts from that value with the two components that the run before left,
  carried as a term. At 340, 353 and 354 the two are none in the run itself: the lines that end
  there compare all components, and the lines after start from the value as written.
- **…LessLayersParts.** A written value in which the long fields of look, lookHeard and own that
  `Lines/Layers/LayersPartsAside.lean` names are emptied; they are carried as a term likewise.
- **Row.** One of the entries of a batching's order (ten at an attention link). `JoinHalves.lean`
  calls it a run.
- **Claims, form.** What a batching gathers row by row; a linear form's shape (`FormSh`).
- **Test on the plan.** A Bool that reads the record's plan of a group of layers (group l / 2 at
  link l) and no shape. Ten of them give the test on the plan inside the step of the layers' own
  rounds.
- **The one equation.** The eleventh member of a link and the thirteenth of the head's link
  (`Table.lean`'s field `equation`).
- **equationTest.** `ProofFile.Honest.K9.oneShape` (`Johnson/Desc/ProofFile/Honest/K9/EqShape.lean`)
  at the chain's shape. By that file's head it is all that is left of what the table's test `oneV`
  at the one equation (`ValsBool.lean`) asks of the public data. It reads three of the nineteen
  components (link, led, core) and no field element. A pass does not by itself give `oneV`.
- **RunsToTested m n start t.** At every record that `publicOfO` returns: from `start X₀` the n
  members from member m on return some shape x, and t x = true. It does not say which shape. It is
  used where no value is written for the shape: the place lies inside a link. Its run is over the
  table's second text, like `RunsAll`'s, and like `RunsAll` it holds emptily where `publicOfO`
  returns nothing. `RunsToTested.atTable` and `.atState` (`Lines/JoinTested.lean`) carry a fact from
  member 0 to the table's own steps and to a state, by `run_of_public_numerals`
  (`JoinKeepsLastShape.lean`) and under its premises; the second takes `shapeJ` at the state as a
  premise.
- **The head, AtMgA.** "Under the head" means under the premise `AtMgA`; "under the head at a
  return" under `HeadAtReturn`, which files outside this library state. Neither is the head's link.
- **Shared chain, last chain.** Two further chains of the proof file, of twelve and of four members.
  In `LastChain/` "member" means a member of these, and "run on shapes" a run of their guards on
  shapes (the last chain's: `E2E/KeyShapeChain.lean`; the shared chain's:
  `Johnson/Desc/ProofFile/Honest/K12/AtFile/EndAtProof.lean`), not the table's steps.
- **End, handed.** What the last chain's start reads of the state at the end of an earlier chain.
  `handedOf c` (`AtFullSide/LaterThreads/FirstEndShape.lean`) returns an Option: none unless c's
  component atEnd has the form `some (_, _, some q)`; else a handed shape of eight fields, six read
  out of two of c's components (core, atEnd) and two marks set to true.
- **Mark.** A Bool in a shape that stands for a test on the state: on the statement (`tidy`) and on
  the pending row's weights (`weights`). A written value does not hold them. Laws give them:
  `tidy_at_head`, under `P5J.AtMg`, at every reached state; `weights_at_the_end`
  (`AtFullSide/LaterThreads/FirstEndShapeOfRun.lean`), under `HeadAtReturn`, at the states reached
  at 358.
- **Door.** The start of the last chain; `doorShape a b`
  (`AtFullSide/LaterThreads/DoorOnShapes.lean`) is its shape, of the two ends' shapes.
- **Hint.** See `ClosingHint.lean`; link 0's lines take `Layers/NoHint.lean`'s.
- **Closed line.** A theorem that is an equation with a closed left side, most often `‹a closed
  Bool› = true`, and that rests on one evaluation by Lean's kernel. The library (`Door/` aside) has
  297, each with one use of the tactic `kernel_rfl`, which lays the term `Eq.refl` of the right side
  and leaves the comparison of the two sides to the kernel: 259 in the 28 pieces (48 + 204 + 4 + 3),
  32 in `Equations/` (25 lines, 7 in the controls' file), 6 in `LastChain/`. Five end in `= false`
  and one in `= none`. In 127 of the 259 that term is the whole proof, and the kernel evaluates the
  Bool of the statement. In 132, eleven of each layers' link's seventeen (the ten tests on the plan
  and the merge's records), the kernel evaluates another Bool, the same test under atXLLight, and
  the law `atXLC_of_light` carries it to the statement. `Johnson/Unfolds/KernelRfl.lean` states
  terms for the tactic's use; one asks that each theorem's answer to `#print axioms` be read by
  name: for that see "How to build, and what it costs".

## How the pieces are cut

- An attention link: four lines: members 1 to 8 of the link; the batching in two parts, cut after
  the sixth of its ten rows; members 10 to 14 (`four_all`, `JoinAll.lean`).
- A layers' link: seventeen lines: ten tests on the plan; members 1 to 3; three lines for the
  layers' own rounds (the guards on the shape, the merge's records, a closed form of the shape after
  the member: its hearing is not evaluated); members 5 to 8; the batching's light step; members 10
  to 14 (`layersLink_runs`, `Lines/Layers/LayersLinkRuns.lean`).
- The head's link: four lines: 337 to 339; 340 to 346; 347 by its light step; 348 to 352
  (`Lines/JoinRecords.lean`, `Lines/TailLight.lean`, `Lines/Head/`).
- The front, the finish, and 354 to 357: one line each.

## How to build, and what it costs

`ShapeLines` is a Lake library of its own and no default target. Two files of the default target
`AtFullSide` import it (`AtFullSide/Honest/LastSocketsFilled.lean`,
`AtFullSide/Honest/TheOneObjectValue.lean`), so a plain `lake build` builds it too, but for three
files that these two do not reach: `Equations/EquationTestControls.lean`,
`LastChain/LastRunAtBorder358.lean` and `LastChain/LastRunControls.lean`. A plain `lake build`
reaches `Door/` too. `lake build ShapeLines` builds the whole folder. Either way the tree beneath is
built first; `Equations/` and `LastChain/` import files of that tree which the 28 pieces do not
need. In the first two calls of the build told below as many of this folder's files were seen
compiling at a time as `LEAN_NUM_THREADS` said (56 and 48), and in that build's samples the largest
process stayed under 49 GiB resident. So `LEAN_NUM_THREADS` is to be set to what the machine's
memory bears.

The build in five calls that is told below, its answers on axioms and the figures in the two tables
are of these files and of the tree beneath as they stand here. The other figures of this section (on
thread stacks, on caps of address space, on the build at `LEAN_NUM_THREADS=16`, on lines stated
otherwise) are not of these files as they stand: they were measured on texts that differ from them
in comments and in names, or on lines and values that are not in the tree.

`lakefile.toml` hands Lean a thread stack of 256 MiB for its files (`--tstack=262144`). The head's
link's first piece ended with the kernel's "deep recursion detected" at 128 MiB, and went through at
256 MiB, 512 MiB, 1 GiB and 2 GiB. The 258 other lines of the 28 pieces have gone through at 128 MiB
too. At 2 GiB six lines of attention links ended with `std::bad_alloc` under a cap of 64 GiB of
address space a process, and went through in a second build under a cap of 120 GiB; read here as the
threads' stacks, each reserved whole as address space.

One build of the whole folder, over the compiled tree beneath, on one machine, held to 84 cores and
960 GiB of memory, in five calls, one after the other: 39 minutes. By name, `ClosingHint.lean` and
the 178 written values: 16 minutes at `LEAN_NUM_THREADS=56`. `lake build ShapeLines.FirstChainRuns`:
310 modules, the 259 closed lines among them: 16 minutes at `LEAN_NUM_THREADS=48`; in samples taken
every ten seconds all processes together had at most 595 GiB of memory of their own, and the largest
process 48.6 GiB resident. `Equations/`, 28 modules: 4 minutes at `LEAN_NUM_THREADS=40`.
`LastChain/`, three modules: half a minute. `lake build ShapeLines` then built the four files of
`Door/`: a minute and a half. Lake's own times for these 524 modules add up to 20.2 hours; the
dearest, `Borders/CarriedForm50.lean`, took 879 seconds. The 32 law files of `Lines/` stood compiled
with the tree beneath.

That build's logs have 691 answers to `#print axioms` for the files of this library outside `Door/`
and of `Lines/`: each theorem of these files has one; those of modules that stood compiled are there
as Lake replays them. For `Door/` they have nine more: one for each of its theorems but
`theOpenFiles_end`, and one for each of its two definitions. All were sorted by program: none names
an axiom beyond propext, Classical.choice and Quot.sound.

The figures below are from that build: Lake's own time for each line's module, and the greatest
resident memory of its process in samples taken every five seconds. These samples are a second
series, apart from the one taken every ten seconds, so their greatest values need not agree.
Resident memory includes mapped files: the compiled files of the tree beneath, which the processes
share.

| closed lines | how many | seconds | GiB resident |
|---|---|---|---|
| an attention link's members 1 to 8 | 12 | 212 to 268 | 31.3 to 38.4 |
| an attention link's batching, first part | 12 | 167 to 210 | 30.0 to 34.4 |
| an attention link's batching, second part | 12 | 168 to 214 | 29.2 to 34.6 |
| an attention link's members 10 to 14 | 12 | 179 to 410 | 25.1 to 48.6 |
| a test on a group's plan | 120 | 36 to 166 | 14.0 to 26.8 |
| a layers' link's members 1 to 3 | 12 | 62 to 144 | 17.5 to 25.2 |
| the own rounds' guards | 12 | 40 to 62 | 14.8 to 16.7 |
| the merge's records | 12 | 56 to 101 | 17.9 to 25.7 |
| the shape after the own rounds | 12 | 41 to 63 | 14.7 to 17.5 |
| a layers' link's members 5 to 8 | 12 | 124 to 152 | 26.2 to 29.0 |
| a layers' link's batching, by the light step | 12 | 77 to 106 | 20.0 to 22.7 |
| a layers' link's members 10 to 14 | 12 | 72 to 319 | 18.6 to 44.9 |
| the head's link, 337 to 339 | 1 | 258 | 36.9 |
| 340 to 346 | 1 | 146 | 28.7 |
| 347, by the light step | 1 | 170 | 31.9 |
| 348 to 352 | 1 | 283 | 43.1 |
| the front | 1 | 45 | 14.1 |
| 353 | 1 | 114 | 21.8 |
| 354 to 357 | 1 | 64 | 16.9 |

One other whole build of the 28 pieces, at `LEAN_NUM_THREADS=16`, is told here for one figure, on
which the full check's bound on Lean processes rests (`lean/scripts/RULES.txt`): by samples taken
every five seconds, the greatest resident memory of one process was 49.1 GiB, at an attention link's
members 10 to 14.

A written value's module took up to 879 seconds and 13.7 GiB (texts of 0.5 to 1 MB: 147 to 497
seconds; of 1.5 MB and more, the largest of 1.9 MB: 609 to 879 seconds). Modules with one value of 5
to 5.5 MB each, which are not in the tree, were not through after 47 minutes. So long forms that
several values hold have modules of their own (`carriedForm‹i›`).

The 38 lines of `Equations/` and `LastChain/` have run at a thread stack of 256 MiB alone. Under a
cap of 32 GiB of address space the process of `LastChain/SocketsThreeAt358.lean` could not start its
threads. The figures below are from the build told above, file by file, as in the first table; a
process of a few seconds is seen in few samples.

| file | closed lines | seconds | GiB resident |
|---|---|---|---|
| `Equations/LayersLink‹l›BeforeEquation.lean`, each | 1 | 54 to 60 | 16.6 to 17.0 |
| `Equations/AttentionLink‹l›BeforeEquation.lean`, each | 1 | 48 to 52 | 15.7 to 16.1 |
| `Equations/HeadLinkBeforeEquation.lean` | 1 | 53 | 16.5 |
| `Equations/EquationTestControls.lean` | 7 | 244 | 17.9 |
| `LastChain/LastRunAtBorder358.lean` | 1 | 10 | 10.6 |
| `LastChain/LastRunControls.lean` | 4 | 13 | 11.1 |
| `LastChain/SocketsThreeAt358.lean` | 1 | 21 | 13.6 |

What was measured where a line is stated otherwise than one might expect, each in single builds
under a cap of 64 GiB of address space a process unless said: members 340, 341, 342 and 347, one a
line, ran out of memory under atXLC; under atXHC 340, 341 and 342 passed in 96 to 112 seconds at 8
to 10 GiB of their own. Member 347 over the table's own cell ran out of memory under atXHC too, and
ended with exit code 134 under a cap of 120 GiB. Member 350 over the table's own cell was rejected
by the kernel ("declaration type mismatch"); beneath that cell stands the core library's merge sort.
Members 1 to 4 of link 0 over the table's own cells, in one line under a cap of 300 GiB, gave no
answer within 30 minutes; members 1 to 3 alone returned in 38 seconds.

## Limits

- At `VerifierAndGoals.storedPublicFiles`'s written copies of the public files alone: the stored
  full-size example's, whose weights are synthetic. No Lean code ties these copies to the package's
  folder of examples (`AtX.lean`). Nothing is shown at the other named set of files,
  `VerifierAndGoals.zGap`. The three files are the parameter file, the layout file and the scale
  file: no proof file, request or reply is read by any line.
- `publicOfO` is taken at `OnBytes.secondHashFunction`, the format's second hash function, which
  makes some of its digests beside its hash H (`OnBytes/Hash/SecondHashFunction.lean`).
- "By Lean's kernel" means: once, inside the build. No second checker has replayed these files. The
  joined facts rest besides on evaluations by the kernel in the tree beneath (`decide +kernel`;
  `JoinTable.lean`'s head lists some). The layout file's size (`lay_size`) rests on
  `AtFullSide/Layout/TieRfl.lean`, whose head reports that the program `leanchecker` fails at that
  module, while a replay inside Lean passes at a thread stack of 128 MB. That head also says that a
  file which imports `AtFullSide/Layout/Size.lean` belongs in the library `AtFullSide`; the files
  here import it from a library of their own, which keeps that sentence's reason: they do not lie
  beneath the main library. By its head nothing in `Johnson/Unfolds/KernelRfl.lean` enforces three
  of its six terms of use; what the release's full check does with this library is told in
  `lean/LIMITS.md` (L69).
- The written values came from evaluations of the run on shapes outside this library, started from
  the first state's shape. The modules of the 28 pieces, of their join and of `Equations/` were
  written by programs, round the values' texts; the three files of `LastChain/` are written by hand.
  Neither these programs, nor the texts, nor the programs that evaluated them are in the tree.
  Nothing rests on them: where a value is wrong, the kernel rejects the line that ends at it. One
  part is compared by no line: the second component of the twelve
  `shapeBehindSixthRowOfLink‹l›LessPair`, which no statement uses.
- An inner written value says nothing of the parts that are set aside there.
- That no line evaluates the hearing of the layers' own rounds is no theorem: it is seen in the
  lines' cost alone.
- `RunsAll` does not say that `publicOfO` returns a record; `record_there` and `RunsAll.ex`
  (`JoinAll.lean`) give one under the layout file's size.
- `startShA` is the first state's shape only under the head and at a request that passes
  (`start_shA`, `RuleAtTable.lean`).
- The joined fact pays one premise among several of `RuleAtTable.lean`'s laws. The values, the fits,
  the head, baseOf's return and the thread's list are other premises, and the rule that these laws
  serve asks more than their two conclusions. Among the values is the table's test at member 354,
  `testV`, of which one mark said no at the one honest run that has been evaluated, while the
  sub-protocol's own test accepted (`TestReturnsFrame.lean`'s head): the law asks more there than
  that run gives.
- `runOnShapes_yes_underHead` stands under the head and under baseOf's return. Both are premises;
  that they can be met together is not shown here. In the two laws that take `hyes` the thread, what
  is said and the falls are free letters, so their conclusions can hold emptily.
- `Equations/`: at three of the 25 places (link 0, link 1, the head's link) a control shows that the
  test says no at the shape one member before. At one place (link 0) a line shows that it says yes
  at the shape one member after as well (`layersLink0_testAfterMember11_yes`). So a pass does not
  say that the shape is the one before the one equation and no other. That members 14 l + 11 and 349
  are of the kind "the one equation" is `Table.lean`'s numbering; no law of this library ties a kind
  to a number; `cell_at` (`Johnson/Desc/ProofFile/Honest/K9/EqValuesJ.lean`) does.
- `LastChain/`: the fact reads none of the three public files. In their place stand written sizes
  and places of the full size alone (`realSized`: typed numbers; that the planner's sizes at the
  release's files are these is no theorem: `Johnson/Desc/K1/Law/CondReal.lean`). `writtenSharedEnd`
  is written out nowhere: the line also runs the shared chain's twelve guards, from the shape of a
  state at a made key. It says that the run returns and not what it returns. That the first chain's
  run reaches `border358` is `runOnShapes_toEnd`, not this line. The two controls on a mark show
  that the Bool is false; by the guards' text it is the first of the four guards that returns an
  error there; no control reaches the three later guards. With the mask set to none the run returns
  all the same.
- `sockets_three_at_358` is conditional on `HeadAtReturn`, on the base maker's return (not the
  online maker's), on a `P : OpenLast h O`, which holds two propositions, and on four debts
  (standRest, readyReturns, tied, indexInRange). All are premises here: that they can be met, one by
  one or together, is not shown in this library; what is known of each is the law's head's to say.
  Its conclusions are implications from a stand of the last chain's thread before each member; that
  there is such a stand is not shown here either. The two debts that this library pays are spent at
  one place in the law, the acceptance at the chain's last member.
- All other facts of this library are facts on shapes. No member of any of the three chains is shown
  to accept.
- Nothing on soundness, completeness or hiding.
