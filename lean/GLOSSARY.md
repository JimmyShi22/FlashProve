# Words of this library

Terms: [TERMS.md](TERMS.md), with their Lean names. This page explains the words that the comments
of the Lean files use, the short labels in the names of files and folders, and many of the folders
of `Johnson/`. What is proved, and under which assumptions: [README.md](README.md),
[THEOREM.md](THEOREM.md), [LIMITS.md](LIMITS.md). This page is the home of no theorem and of no
limit: what an entry tells of one is a gloss.

Lean checks neither this page nor any comment: where a comment and a statement differ, the statement
counts (L23; on this page, outside code marks, an L with a number is an entry of LIMITS.md). A
denial on this page (no theorem on soundness, nothing on hiding) is meant in the widest sense of its
word. Paths are from `lean/`, but for those that start with `docs/`, `prover/` or `examples/`, which
are from the repository's top. A directory named without `OnBytes/` in front, such as `Iop/`, is not
the one of that name under `OnBytes/`. A word with senses by directory says so; a word's sense in
`Policy/` is stated only where its entry names that directory. An entry that says only "see", with a
declaration, gives the place of the definition and no more.

## How the files are written

Many statements are written twice. A definition in the namespace `Spec` states a proposition
(`def Spec.x : Prop`, or `def x : Prop` inside `namespace Spec`), and a theorem of the same name
outside that namespace proves it (`theorem x : Spec.x`), often in a sister file whose name ends in
`Proofs.lean`. To see what a theorem says, read the definition of the same name. In
`VerifiableInference/` a theorem's statement stands at the theorem. Mind the `variable` lines above
a statement: they are part of it (L38).

A full check audits every declaration for axioms other than `propext`, `Classical.choice` and
`Quot.sound` ([CHECKING.md](CHECKING.md)). Which of the three a theorem uses it reports only for the
theorems listed in `scripts/top-theorems.txt`.

In a comment, "nothing assumed" does not mean "no hypotheses": a hypothesis that the statement names
itself, such as valid settings or a lawful table of scales, may remain. In most files the words
stand as "Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as
proofs", of that file's own statements.

Comments speak of "the technical report", or "the report": a technical report on this protocol that
is not public. The report is not in this repository, and whether the comments agree with it has not
been checked ([CREDITS.md](CREDITS.md)). "By a reading" (in some folders "by inspection") marks a
sentence that rests on somebody's reading of a text, not on a theorem; no outside referee stands
behind it.

In `Fmt/` and `Run/`, names with "Theirs" or "their" (`Fmt.M1.Theirs`) mean the
programs': their format, their files and their verifier.

Under `OnBytes/`, `verify`, `verify -key` and `verify -leaf` are commands of `verify-on-bytes`, the
Lean text below `OnBytes.Main`: a hand translation of `cp_verify` into Lean, from which this
repository builds no stand-alone program (one test, `tools/accepts/`, compiles it and has Lean load
the compiled code while it evaluates files of `lean/Ask/`); it is not the Lean verifier `verify` of
THEOREM.md. A path or name marked "[not in this library]" is not in this repository: wherever a
comment says that such a file or declaration proves, shows, holds or tests something, read it as not
proved (not tested) here.

## The words

- **97**: positions that the first stage of the link's proximity test samples (`frPar`).
- **abort set**: see withheld.
- **acceptance policy, score policy**: see first choice. Under `OnBytes/`: the parameter file's
  lines that say how close the checked tokens must be to the top choice.
- **AccLaw**: perfect completeness of one strategy at one instance x and input oracles y, given the
  work checks, outside a set B.
- **agreement**: mutual correlated agreement of a code at a radius, as a count (`Enc.MCAat`).
- **allotment**: see `LdAllot`, Cb/Part/LdPartAllot.lean.
- **altered copy, false proof, re-cut file**: files that a verifier should refuse: an honest file
  with bytes changed, cut off or added; a cheating prover's file; a file made from a nonce that
  fails one round's work test (`recut`).
- **annotation**: of a batch protocol: which rounds are local or shared (`RAnn`, `RoundSplits`).
- **argument string**: the proof of one compiled protocol for one slot (`OneProtocolProof`).
- **argument system**: one record of the model, an honest committer, an honest prover and a verifier
  (`ArgumentSystem`). In `Compile/`, `ZKCP/`: see scheme.
- **arrangement**: how a group's rows are laid onto a cube before the fold (`StdArr`).
- **assembled lookup**: the lookup sub-protocol as one chain. (`LkAsm2`, Cb/Ld/LdLkpAsm2.lean)
- **assembly**: in file heads: a file that only puts together other files' statements.
- **assumed statement**: a proposition on the mutual correlated agreement of Reed-Solomon codes
  below the Johnson radius (`BCHKS46At`), a hypothesis of many theorems. This library proves it in
  `Cb/Bridge/` from files that AI systems adapted from ArkLib and Mathlib (`ThirdParty/`; LIMITS.md,
  L15); where a theorem takes it as a premise it is assumed there. Under `OnBytes/Params/`, "the
  assumed theorem" is a paper's theorem: no proposition of Lean and no hypothesis of a theorem.
- **`AtConst`, `AtHead`**: statements taken at terms of Johnson/P5J/MgAtAll.lean: `AtConst` at
  `mgAtAll h`; `AtHead` under the one premise `AtMgA`, which comments call «the head» (not the
  model's output head).
- **`...AtName`, `_at_name`**: stated at the terms written in the key file's rows, not free letters.
- **atom**: a factor of a condition's terms (`Atom`, Cb/Req/ReqSpec.lean).
- **audit**: see full check.
- **`…B`, `Says`, `_says`**: `…B`: a test returning a `Bool`. `…Says`: what follows where it holds.
- **bad values, bad sets**: per round, verifier messages fixed before the draw (`BadFam`).
- **bare, called**: of a lemma. Bare: a hypothesis there. Called: from a theorem, so no hypothesis.
- **base case**: the last block of a tower, a reduction to the trivial statement (`ldBaseEnd`).
- **base joint**: see stage.
- **"BAT", "LINK"**: rounds of the format's plan. "BAT" samples the element that combines the open
  claims (`rBatN`). "LINK", with a proof-of-work check, samples the positions read (`rLink`).
- **batch, batch IOP**: the slots that one prover call serves; a protocol for it
  (`BatchInteractiveOracleProof`).
- **batched claim, stmG, firstFits**: the one linear claim made of a group's open claims (`stmG`).
  `firstFits`: the group fits the proximity test's first stage.
- **batching**: In `Cb/`: a step in which many rows become one (`LdBatD`). In `Johnson/Desc/K12/`: a
  proximity test's part that makes a group's open claims one (`Parts.bat`). Kind `K9`: a link's
  claims become one, each under a power of one sampled element.
- **batLC, batTC, wTC, wLC, wBC**: `batTC`, `batLC`: the protocol structure's `offline` and `link`,
  each with an annotation of its rounds. `wTC`, `wLC`, `wBC`: the parts of the compilation data for
  the key file's protocol, the link and the proof file's protocol.
- **below the Johnson radius**: a radius e with n (n - d) < (n - e)² (`InJohnson`).
- **below κ**: see error.
- **beyond half the distance**: see unique decoding.
- **BindsWith**: see properties of an argument system.
- **blinded**: see `IOR`, Ior/Ior.lean; `InteractiveOracleProof`, Iop/InteractiveOracleProof.lean.
- **block**: In `Johnson/`: a sub-protocol, an entry of a chain's list (`Block`,
  Johnson/Desc/Block.lean). In `Cb/`, `Ior/`, `Hiop/`: one reduction with honest side, extractor and
  numbers (`LdBlock`). In `Blocks/`: a step on plain vectors. In `Rom/`: one hash answer. In
  `Inst/`: a part of a layer. Under `OnBytes/`: most often a function on the verifier's side alone,
  with no honest side, extractor or numbers (`Blk`).
- **body**: the part of a segment before its closing (`LdSeg`); a hash tree leaf's content (`Body`).
- **`Book`**: the verifier state's trees and where each oracle message lies (`TreeBook`).
- **border, boundary, in front of, behind, `338` … `346`**: border k lies in front of sub-protocol k
  in a chain's flat list (`borderAt`); at full size 338 is the next token, 341 the output head, 346
  the merge. `Border` (Johnson/Desc/Third/State.lean) is another thing.
- **bridge, bridge-to-fold**: the one-round step heading a run on a group (`ldBridge`; `LdFoldD`).
- **budget**: In Ladder.lean: 2^48, the honest side's hash queries for one commitment and one
  request. "The budgets" are two numbers of 2^64: beyond that many queries of the adversary or of
  the parser these goals say nothing. Also `Nums`; `Comp.bud`.
- **build-time test**: a `#guard` line: it must evaluate to true, or the file does not compile.
- **builder**: a record of parameters, or what makes protocol parts from it.
- **dataAtFiles, flashProveData, descriptionOfDataOnBytes, asDescriptionFiles,
  atSecondHashFunction**: In `Johnson/Goal/`: `flashProveData`, the library's `DescriptionData`;
  `dataAtFiles L Z`, its data at files `Z`, with the link's decision behind a gate (see gate);
  `descriptionOfDataOnBytes L`, the `Description` made of it; `asDescriptionFiles Z`, the files as
  an `OnBytes.K.Pub`; `atSecondHashFunction D`, `D` at the second hash function.
- **bundle**: what is asked of a reduction (`Good`) or sub-protocol (`SubData`); a group (`GPack`).
- **by a reading, by reading, by inspection**: rests on a reading, not on a theorem.
- **By calls:, By:, How.**: lines in a file's head: what its proofs call, and how they go.
- **by choice**: see picked by choice.
- **by its text**: by inspection of a definition's Lean text; no theorem states it.
- **by report**: on another's word about a file or a run, not on a reading of the code or on a
  theorem; not opened or checked here.
- **byte coins**: what the honest prover picks for one compiled file (`ByteCoins`).
- **call, `Calls`, `Key`**: One call of the prover: see session. In `Blocks/`, `Inst/`, `Cm/`: one
  use of a table (`Calls`). In `Johnson/Desc/Kinds/`: a table with the columns of keys looked up in
  it (`Key`). In `Rom/`: an adversary's move. In `Fmt/`: one hash evaluation.
- **`Calm`**: two relations between verifier states (`IM.Calm`, `Meaning.K2.Calm`).
- **can serve, CanServe**: every token is in the vocabulary, the output is not empty, and the model
  has a value on the whole window (VerifiableInference/CanServe.lean).
- **cap, caps**: `cap i`: the largest nonce that the work search tries in round i; running out is a
  term of the completeness error. Not `capT`, `capB` of Johnson/Flat/Last/LastCutCap.lean.
- **carried part**: what a reduction passes on unchanged. (`IOR.keep`, Ior/Frame.lean)
- **carrier**: the protocol structure without index and provers (`typedOracleCarrier`); on the hash,
  `carryF`.
- **`Carry`, `Carried`, `Meaning.Carry`**: a property surviving the assembly holds of every block.
- **cell, cells**: one value at a place in a segment's matrix; the witness of the indexed relation.
  At the output head: integers committed to, each meant to be a signed byte (`Cells`).
- **chain**: In `Ior/`, `Cb/`, `Hiop/`: reductions in a row. In `Fmt/`, `Run/`, `OnBytes/`: a
  Fiat-Shamir transcript kept as a hash chain. In `Johnson/Desc/`: blocks run in order (`Chain`).
  "The parameters of a chain" are something else: what the program derives for it.
- **chain query, chain oracle**: the query that draws a round's verifier message; its oracle
  (`OracleName`).
- **check.py**: see full check.
- **checked token**: see true request.
- **claim**: Mostly part of the explicit statement, often one linear constraint (`Claim`). In
  `Alg/`: a sumcheck's claimed sum. In `VerifiableInference/`: a predicate (`SoundForWith`).
- **closed fact, closed test**: a proposition about constants alone: many are checked by Lean's
  kernel, some proved otherwise, some stay premises. A closed test: a Boolean function of them.
- **closed segment, last segment, closed body**: a segment with an entry step, a body and a closing;
  all of a request's segments but the last are closed.
- **closing**: the last part of a test, link or segment: down to the trivial statement (`LdTc`). See
  `Link.close`.
- **code**: Mostly a linear code: see code with encoder. In `Rom/`, `Compile/`: a bit string under a
  coding. In `ZKCP/`: a key's value; a key may have none. In `VerifiableInference/`: `codeUnderTag`.
- **code complex, complex**: a finite family of codes or components (`LdCode.fam`, `Cx`).
- **code switch, kept members**: a step to a new code: a new word is sent and the old one read at
  drawn positions (`LdSw`, `Parts.switch`). Block kind K2. What carries over: kept members.
- **code with encoder**: a linear code by its generator matrix (`Enc`, Code/Iface.lean).
- **coding**: how the one hash function stands for the typed oracles. (`OracleCoding`,
  Rom/Family.lean)
- **coins**: The committer's: a number up to a bound. The prover's: `Draw`, free variables: no
  clause puts a distribution on them. The interactive provers': `Honest.Coin`. See byte coins.
- **collision**: a word-and-seed property, left abstract; there the index decoder gives nothing.
- **column (of a tree)**: all rows' words at one position (`MsgV.col`).
- **commitment**: what a committer publishes for the weights, one hash value (`Commitment`). Under
  `OnBytes/`: what the programs' committer made once for the weights, no `Commitment`.
- **commitment ID**: two things bear this name. On the pages it is also a word for the commitment
  that `verify` takes, 256 bits (`Commitment`; TERMS.md, table 1). In the Lean files under `Fmt/`
  and `OnBytes/` it is a string of bytes, no term of the type `Commitment`: a hash of the public
  files' digest, the first stored table's data and its out-of-domain seeds and answers
  (`publishedID`, Fmt/Rules4.lean; R4.11).
- **commitmentOpeningError**: a function of further encodings and queries.
- **compilation data**: see wire.
- **compiled verifier, evaluable form**: the verifier that the compiler makes from an IOP written in
  Lean (`innerCompiledVerifier`). `verifyOneProtocol` (Compile/Batch/Verifier.lean) is the compiled
  verifier of one IOP, not of the three together. In `VerifiableInference/`, a scheme's verifier.
  Evaluable: `verifyP`.
- **compiler**: the map from an interface to a scheme in the random-oracle model. Not
  the Lean compiler, except in the comments of `OnBytes/Guard/`.
- **completeness error, α**: the bound on rejecting the honest commitment and proof (`alphaAll`). In
  `EndFits`, `LastFits`: a parameter.
- **CompleteOn**: see properties of an argument system.
- **CompleteSoundZeroKnowledgeOn**: see VerifiableInference/MoreStatements.lean.
- **component**: interleaved rows under one code (`Comp`); the shared or a slot's part of a message.
- **conditions (of a segment)**: its identities and keys (`SegSpec.Holds`, Cb/Req/ReqSpec.lean).
- **conditions on data**: no one notion: the hypotheses of the record that a file names.
- **configuration**: In `Hiop/`, `Cb/`, `Cm/`: the data over which sub-protocols are stated
  (`ConfigurationWithOutOfDomainSample`). In `Inst/Model/`: `Params`. In `Fmt/`: the public files
  behind the digest. Under `OnBytes/`: none of these types, most often the public files. The small
  test configuration is written out in the library, not read from public files.
- **configuration's digest, public file**: the hash of a list of public files (`configDigest`).
- **constant, closed constant**: the value of `Meaning` joining the kinds' lemmas (`P5J.mgAtAll`).
- **constraint relation**: the relation of a predicate on messages (`Con`;
  `ConfigurationWithOutOfDomainSample.Left.Rlin`).
- **control**: a negative test: an altered input that a check must reject, beside the honest one.
- **copy, the copy's file, the copy's number**: a second encoding of the index; the proof brings it,
  the key does not hold it. Comments call its file the entry file. (`Draw.n`)
- **core**: Of a witness: what a joint's map reads. Of a test: without its closing (`LdLinP.core`).
- **corner, vertex**: a vertex of the Boolean cube (`corner`); in `Fmt/`, also a hash tree's node.
- **correctness of extraction**: When the committer is the honest one, the index that the extractor
  names is the very index that was committed (`ExtractsCommittedWeights`). It reads the honest
  committer, which at the Lean verifier's system is the constant committer (a committer that returns
  one constant whatever the weights, and so commits to nothing; the committer of the six lines is
  another: the one that `compile` makes (`Johnson/Face/Compiler.lean`), which encodes the weights
  and hashes the key), so of that system it cannot be stated with any content. It is proved of
  illustrative committers (TERMS.md, table 3), which are written in Lean, not of `cp_commit`; so
  are, for some of them, binding of the commitment (`BindsWith`) and no two openings
  (`NoTwoOpenings`). There "binding" is not index binding.
- **cost ledger**: in `Policy/`, six numbers held at each position under a policy (`Hid`). The names
  claim nothing: no theorem here says that they stay hidden.
- **counted position**: a position in a request's range, below the window's last.
- **`Counted`, «the counted form»**: the proposition `P5J.AtMgA.Kind h L K6`.
- **cover**: see `Nums`, Ior/Chain.lean.
- **`cp_verify`**: the C++ verifier: key file, one copy's file and one request's proof, in one call.
- **cut, `Cut`, `compCut`, `HeadCuts`**: In `Blocks/`: what is said between two stages (`Cut`). In
  `Iop/`: a division of a message (`RCut`). In `OnBytes/Slice/`: the entry below which two tables
  are compared (`Par.cut`). `compCut w`: the pair (cells, mask row) read off the witness `w`.
  `HeadCuts`: a named premise of Johnson/P5J/MeansQ.lean.
- **debt, owes, owed; payer, pays, paid; what is left**: in comments, words for the hypotheses of a
  theorem. A hypothesis is discharged where another theorem derives it, often from further premises
  that stay, and open where it stays a premise. Comments call a hypothesis a debt, what supplies it
  its payer, a discharged hypothesis paid, an open one owed or left; "what is left" is the open
  hypotheses.
- **decision**: a function from a view, and in `Johnson/` the instance, to accept or reject (`dec`,
  `FileDescription.run`). The link's is one of four conditions of its verifier's accept.
- **decodes**: a table differs from some table of code words in at most a fixed number of columns
  (2,200 of 16,384 at the small test configuration), below half the distance. Not the largest such
  number: a table with more bad columns does not decode, even where one table of code words is the
  nearest.
- **deferred programming**: see `Step.run`, Rom/Defer.lean.
- **demand**: see `Bears`, Ior/Bears.lean; `LdTc`, Cb/Ld/LdLinCloseChain.lean.
- **dense**: each written-out variable is named once and what is read lies inside the stored array
  (`DenseTensor`). Of rows and claims that are not dense the proof that the link proof's own
  verifier accepts its honest prover says nothing.
- **description, statement, shapes**: Under `OnBytes/`: what the reader must know before it parses a
  chain; the public values that the chain's proof refers to; the sizes of its messages. Description
  alone: the IOP as written in Lean (`FileDescription`; `VerifierAndGoals.Description`). In `Cb/`,
  `CompileK/`, `Hiop/`, `Ior/`: a text: the technical report; see technical report. In `Fmt/`:
  `Spec`, or a text that belongs to the programs.
- **discipline**: see `SafeO`, Compile/Batch/SpecDiscipline.lean.
- **disclosed view, view**: see `DView`. In `Fmt/`, `Run/`, `Johnson/Desc/`: what a decision reads
  of a transcript (`View`, Fmt/View.lean), not what the statements on simulators compare.
- **domain (of the hash)**: the calls at which `hDom` is true (Fmt/Rules23.lean).
- **door, `Door`**: the entry into a proximity test (`door_yes`); `door_premises` derives its three
  structures, not its four equations, under premises of its own, three of which it only passes on.
  `Door`: a cheap test on public values alone (`lawsAsk`).
- **draw, draws, drawn**: to sample: the verifier's random choice in a round. Mostly a round's
  verifier challenges (`Drawn`); that a `sealed` round draws nothing else is a Boolean test, not a
  theorem. The prover's draw: see coins.
- **`Due`, `Paid`, `Left`, «bill», «owed», «pays», «spends»**: words for premises (see debt): a bill
  is a structure that gathers them (`K6DueMg`); paid: discharged; left, owed: open; spends: takes as
  a premise. In another sense, of the protocol, «owes»: has to state.
- **encoded index, prover encoded index**: the word that a committer sends as the oracle for an
  index: any word. A prover encoded index is what the honest prover keeps of it.
  (`ConfigurationWithOutOfDomainSample.PIdx`)
- **encoding randomness, RI**: the encoder's second argument.
  (`HolographicProtocol.EncodingRandomness`, Hiop/RecInterface.lean)
- **end claim**: what a sumcheck or a grand product claims after its last round.
- **Ends, DrawFit, JoinRest, TableOwes**: clause lists: `Ends` on a value of the typed runs,
  `DrawFit` on the prover's coins, `JoinRest` on `home_yes`'s premises, `TableOwes` on a table's
  salts.
- **entry**: In `Cb/`: a coordinate of an oracle message's message (`Sig.Ent`). In `Compile/`,
  `Rom/`: a query with its answer (`QA`). In `Fmt/`, `Run/`, `Decl/`, `Johnson/`: a row of a plan, a
  round's name and numbers (`Entry`); one for the tables' out-of-domain sample is no round.
- **entry file, key file**: an entry file (the copy's file; `docs/` says leaf file) holds a head, a
  stored copy's root and a chain's bytes; a key file a head and the first table's root
  (Fmt/M3Entry.lean).
- **entry step**: see closed segment.
- **entry tests, the door, row n**: the online protocol's own list of fourteen tests on the public
  files; an issue of the list is a prefix of it. (`LPFD.lawsAsk`, Johnson/Desc/Laid/ProofAsks.lean)
- **environment**: gives the next instance and witness from the index and the proofs so far. (`Env`)
- **error, list of errors, full list**: In `Iop/`, `Ior/`, `Cb/`: for each round a number, not a
  probability: how many verifier messages may let a losing prover escape (`Err`); the full list: all
  values. In `ZKCP/`, `Compile/`: a probability. Under `OnBytes/`: see round, target.
- **evader, zero-evader**: seeds with coefficient vectors, such that a non-zero vector is
  annihilated by at most a given number of seeds. (`Evader.OK`, Cb/Gen/BatEvader.lean)
- **executable form, step-by-step form**: a second term, which Lean's evaluator can run (TERMS.md).
- **external openings**: the queries to the two input oracles, as a list. (`XO`, Run/PlanQX.lean)
- **external oracles**: see statement.
- **extractor, extractorAt**: a function of which a property on soundness speaks: to weights or
  nothing (`extractorAt`), to an index and a witness (`Extractor`), to an input witness (`Know`).
- **fall**: a further set of verifier messages excepted from completeness, beside the abort set; its
  bounds are terms of the completeness error. (`Falls`, Johnson/Prover/All/OfHonest.lean)
- **family**: In `Cb/`, `Cm/`: a condition at each
  vertex of a cube (`Fam`), or one sending's messages. In `Rom/`: the typed oracles (`OSpec`).
- **family of keys**: see key.
- **`Field`, `Field...` (in file names)**: a file on fields of `FoldFacts` or of `LPFD.The21`.
- **fifty later places, the 52 places**: K1's two places in each of 25 links; with two more, the 52.
- **filler**: a written term in a parameter's place that is not the thing meant: a coding that
  encodes nothing, provers that send fixed messages, a test that says yes to all.
- **filling, 𝔏, `h.free`**: values for what the chains' statements leave open. (`P5J.Free`)
- **final linear test**: the check of the masked message against the linear claim.
- **final system, final statement, honest part, honest provers, served request, well-formed request,
  files in use, public stop, private stop, the bit of a request, the label of a reply**: see
  TERMS.md, table 6.
- **first chain, shared chain, second chain, last chain**: the three lists of sub-protocols of the
  key file's and the proof file's protocol; "second" and "last" are one list. (`FileDescription`)
- **first choice, exact match, acceptance policy**: The first choice, or greedy token, is the least
  token with a greatest logit (`IsGreedy`). An acceptance policy is a clip, a bound on the mean cost
  and a limit on the positions above the clip (`AcceptancePolicy`). Exact match: every covered token
  has logit gap zero (`RinfS`); in `VerifiableInference/`, each output token is the model's next
  token.
- **first sending**: see sending.
- **`Flat`, `Cut`**: a chain as one list of blocks (`Chain.blocksInOrder`); the cut `k` comes after
  `k` blocks.
- **fold**: a step of several rounds that combines a table's rows into one word. (`foldV`)
- **folded message, folded row**: a table's rows combined under eq(r, gamma); its oracle message.
- **forest**: In `Cb/Ld/`: a family of keys of weights-formedness, or a lookup's product trees. In
  `Blocks/`: a lookup's keys as trees. In `Compile/`, `Run/`: checks of opened leaves (`Forest`).
- **form's half, values' half**: `BodyInv`'s premises on public data and on the prover's values.
- **form, `Form`**: In `Johnson/Desc/Kinds/`: an affine expression with public coefficients in
  hidden scalars and committed entries. In `Cb/Ld/`: a linear form on entries. In `Blocks/`,
  `Cb/Req/`: an affine function of entries (`Form`) or cells (`CForm`). Also a statement's version.
- **format page, edition, issue**: docs/format/FORMAT.md, the programs' file format: it comes with
  the programs, not with this library. An edition is a version of it; an issue, of a toy's text.
- **format's hash (H)**: BLAKE2b with a 16-byte label and 32 further bytes (`formatHashFastForm`):
  every hash of the format but the digests of the second hash function. "Every g": the 256-bit
  oracle beneath it.
- **four counts**: bounds on a reduction's rounds, oracles and verifier messages.
- **frame, `Frame`**: The kind `frame`: the verifier's own rows between the sub-protocols, which
  belong to no kind of sub-protocol (`KindName.frame`). In the state: a `ReqFrame`, which tracks the
  segment. In `Johnson/Prover/Link/`, `Johnson/Goal/Conditions/`: the link's protocol with open
  parameters, `accLaw_link`, the test `sizeNumbersFitAtFullSize`, or `completeOn_of_public`.
- **free empty slots**: a form of the scheme with batches. (`argBU`, Compile/Batch/StarU.lean)
- **free entry**: an entry that is a coin of the sender, a mask of coming blocks. (`Sig.StdL`)
- **fresh**: a property asked of a prefix's honest side: given all that the prefix shows, the
  block's own masks are uniform and independent of the rest of what it reads. (`Honest.Fresh`,
  Ior/KnowCollRulesMask.lean)
- **a front verifier**: a term that takes a commitment ID, a prompt, output tokens and the files,
  and asks the hash as an oracle (`PortArmsC`, Johnson/Top/OnFilesPortC.lean).
- **front, `Front`, front reduction**: In `Blocks/`, `Inst/`, `Top/`: a reduction whose verifier
  rejects or ends in one index claim. In `Cb/`, `Cm/`: the first part of a closing, segment
  or body. In `Johnson/Desc/K12/`: a proximity test's first part, without a round; the link's six
  front blocks stand before that test and are not the field `front` of its `Chain`. The front round:
  a file's first round.
- **full call, closing lines**: a call of a stand-alone program that one may build from
  `verify-on-bytes` (this repository builds none) on key file, copy's file and proof; what it prints
  above its last line.
- **full check, audit, script**: see CHECKING.md. In `Inst/`, to audit a relation: to read its
  definitions. "Audited", in `Run/` and the name of Rom/EagerAudited.lean: of the
  definitions of `ZKCP/Defs.lean` (see literal definition); it reports no audit.
- **full message**: see code with encoder.
- **full parameters, tiny parameters**: in `Fmt/`, `Run/`: the sizes of a toy's proof files.
- **full size, small size, full-size parameter set**: two parameter sets as Lean terms (`frPar`,
  `srPar`), not the full parameters of `Fmt/`. That the full size's numbers are those of
  prover/examples/target_full_f2 is not tested in this library.
- **further encoding, further encodings**: an encoding of the whole index beside the first: a scheme
  with l of them commits to all weights l + 1 times. Lean names say leaf: no leaf of a hash tree.
- **further reads**: a budget among the numbers of an IOR. (`Nums`, Ior/Chain.lean)
- **further witness**: a stage's witness beside its open messages. (`LdStage`)
- **G3'pol**: the completeness goal of Ladder.lean: at the two stored sets of public files, the
  honest side is rejected with probability at most 2^-40, within 2^48 hash queries, for every output
  that can be served and meets the acceptance policy that the files state, whether it is the model's
  own output or not. No theorem concludes it. At `theDescription` the honest side is a constant one:
  a committer that returns one constant and a prover that hands over empty files, whatever the
  weights; so the goal has no content there (TERMS.md, note 8). Another statement on completeness is
  proved of the final system `compile (flashProve setup)`, which has the same verifier, with the
  honest committer and prover that `compile` makes in the place of that constant side:
  `completeOnCanServe`, one of the six theorems (see there).
- **gate**: two opposite things. In Ladder.lean's head: a branch that accepts every request. In
  `Johnson/Goal/`, `Johnson/Flat/Dec/`: a decision behind a Boolean; shut, everything is rejected.
- **ghost**: In `Cb/Obj/`: a witness part that `idxRelsG` does not read. In `Cb/Part/`, `Cm/`:
  integer cells of a builder's witness. In `Compile/`, `Run/`: an oracle name of the analysis alone.
- **goal, the goals, `Ladder.lean`, `Ladder/`**: the six theorems (see there); and, on this page and
  in comments, the propositions of Ladder.lean (`G3'pol`, `G7`, `G8`, `G9` and their like), each
  about a `Description`; its head numbers their limits. The IOP of Ladder.lean's goals is
  `theDescription`. A theorem of the form of one of Ladder.lean's propositions at another
  `Description` is not a goal.
- **Goldilocks**: the prime field of `VerifiableInference/` (`F`). The model's constraints are
  checked modulo a prime p, of which the proofs of `Inst/Model/` and `Cm/` ask that 2^61 - 1 ≤ p
  (`Big`, Inst/Model/Bound/Base.lean).
- **group, member, `Group`**: In `Cb/`, `Cm/`: oracle messages, its members, tested together at one
  radius (`Grp`). In `Fmt/` and the verifier's statement: such a list with flags for kept (`Group`).
  In `Inst/`, `Cm/`: consecutive layers.
- **`Grows`, `GR`**: the verifier's statement `T'` extends `T`. (Johnson/Desc/Grows.lean)
- **guard**: a proved statement beside a theorem, most often an instance that meets its hypotheses.
  In `Cm/`: a condition on a term. In `Fmt/`, `Run/`: a `#guard` test. Under `OnBytes/`, no proved
  statement: a `#guard` test, a command of `OnBytes/Guard/`, or a verifier's run-time test.
- **guest, guests, host, rider**: A host is a kind of sub-protocol whose random point also tests its
  guests, other kinds' identities. The lookup `K3` is a host; in the IOP as written in Lean it is
  handed no guest, so its run of claims "guests" makes no claim (the limit:
  Johnson/Desc/Block.lean). In the kinds' laws: two forms of the output head; the rider says both
  are 0. `…Riders`: claims that a row neither closes nor reads.
- **the hand-written Lean verifier**: `verify-on-bytes`, not the Lean verifier `verify`; it is not
  proved sound. See `verify-on-bytes`.
- **`Hands`**: what block `k` hands on to point `k + 1`. (Johnson/IMR/HandsDef.lean)
- **hash query, query**: In `VerifiableInference/`: a bit string put to the hash function; bounds
  count a repeated query each time. In `Iop/`, `Ior/`, `Cb/`, `Blocks/`: a reading of one oracle
  position. In `Inst/`, `Cm/`: attention's query. In `Fmt/`, `Run/`: see chain query.
- **hash term**: a summand of a bound: queries, or their square, over hash values.
- **head, `Head`, from the head, under the head**: A file's top comment. Of the model: its output
  head and the first chain's last segment. "From the head", "under the head" (`P5J.AtMgA`,
  Johnson/P5J/MgAtAll.lean): the standing hypotheses, which hold at public files in scope that parse
  once the tests on the public files have passed. That the tests pass is proved at written copies of
  the stored files, in a side library, and evaluated or unknown elsewhere: see live.
- **`hear`, `Heard`, hearing**: a segment's blocks before its batching; what the walk keeps.
- **hiding conditions**: ten conditions on the public files needed for the design's hiding argument.
  They are necessary, not sufficient: files that meet them are not thereby shown to hide anything.
- **hiding polynomial, hiding sum**: the random polynomial added to a sumcheck's claim, and its sum.
  The name claims nothing about hiding. (`hU`, Cb/Ld/LdHide.lean)
- **hit**: see miss.
- **holds an index**: `hold` makes from an index the messages encoded; `held` reads an index, or
  nothing, off any message. A message on which `held` returns an index need not be of that form.
- **home, homeR b Z, homeT, committerCoinCountLessOne, namedGen**: the compiler's input built from
  `descriptionOfDataOnBytes flashProveData` at files `Z`, with two fixed values in the place of the
  verifier's two public readings; `theDescription` is that same term. In `Johnson/Prover/Home/`: an
  honest prover.
- **honest bits**: a lookup's multiplicity bits as the honest prover forms them. (`hbit`)
- **honest side**: the honest prover as data. (`Honest`, Iop/InteractiveOracleProof.lean)
- **honest, altered, false**: *honest*: the regular programs' unchanged output. *altered*: an honest
  call with one small change. *false*: a cheating prover's or committer's output, with consistent
  hashes. *control*: a call on valid files paired with these.
- **HonFit**: a named hypothesis behind `CompleteOn`: the completeness of three protocols, on
  provers given as parameters. It proves nothing by itself. (Johnson/Prover/All/OfHonest.lean)
- **house**: the authors of a group of files; «another house's X»: other authors wrote X.
- **ideal oracle**: a random oracle; one independent oracle for each kind of query, and one query
  for a round's challenge stands for all the hash calls of that round.
- **idle**: in comments: of a statement, vacuous (true because its hypothesis is never met, so that
  it says nothing); of a premise or a value, read by nothing. An idle prover (`idleRecs`) stops at
  every verifier message (its abort set is everything); it is no honest prover of anything. With it
  the clauses of `LastFits` hold only at a completeness error of at least 3, where the conclusion
  bounds nothing (`three_le_idleAlpha`).
- **`IM`**: a namespace of `Johnson/IMR/`; the letters say nothing about the content.
- **in front of, behind**: order in the protocol: before X, after X.
- **in scope, InScope**: a Boolean test on the three public files (Ladder.lean): the reader accepts
  them, the layout file is the stored full-size example's, the parameter file is that example's but
  for eight numbers (`FreeLines`), and 2^8 ≤ theta.
- **in the clear**: see plain part.
- **index binding**: (in full: index-binding knowledge soundness): the soundness notion of a scheme
  (`HasIndexBinding`, ZKCP/Defs.lean). `Sound` is this notion for a claim without a witness, so the
  soundness theorem on `verify` is index binding (`indexBinding_of_verify_at`). In `Hiop/`: a
  property of the interactive protocols, round by round: not a bound on a scheme.
- **index decoder**: from an encoded index to an index or nothing.
  (`ConfigurationWithOutOfDomainSample.D`, Hiop/RecConf.lean)
- **index privacy**: see `HasStrongIndexPrivacyWith`; `HasIndexPrivacy` is weaker than index privacy
  as TERMS.md defines it, in spite of its name (ZKCP/Defs.lean; TERMS.md).
- **index, index matrix**: the first argument of an indexed relation; what the honest committer
  encodes. For the model: a well-formed matrix of digits, off which the weights are read (`Idx`).


- **input oracle, stored string, stored symbol**: the link's two strings, which no message sends.
- **instance**: the second argument of an indexed relation; for the model, a request.
- **integer model, top choice**: the version of the model that the proofs refer to: every step is
  defined on integers; it is not the floating-point model. The *top choice* is the highest-scoring
  token, ties going to the lowest number. Johnson/Goal/Conditions/HomeEnd.lean leaves open whether
  the lookups of `theDescription` admit every value of that model (GAPS.md).
- **integer program**: see model.
- **interface**: the record of algorithms that the compiler takes. (`BatchProtocol`, Iop/Batch.lean)
- **Inv0, Front0, Groups**: premises of `linkYes_of` (Johnson/Prover/Link/LinkJoinE.lean), proved in
  Johnson/Prover/Link/LinkJoinF.lean.
- **IOP as written in Lean**: see description.
- **IOR, reduction**: an interactive oracle reduction of fixed shape. (`IOR`, Ior/Ior.lean)
- **item, parameter list, public item, open**: A parameter list is what is asked of one
  sub-protocol, an item one such property. In `Fmt/`, `Run/`: a named byte string. In
  Johnson/Desc/First/Borders.lean: a named claim on the witness; a public item: a test on the state.
- **ivk folder**: (docs: *public key directory*): `key.bin` and the copies' files `leaf/<k>.bin`.
- **joining round**: a batch protocol's first shared round. (`RoundSplits.FmtFrom`,
  Iop/BatchFmt.lean)
- **joint**: the honest relation, a relaxed one, a set of statements and a map to a witness's core
  (`Rels`, Ior/Chain.lean). In a tower: a code, a form and a radius. In `Cb/Part/`: what a builder
  carries between segments. Under `OnBytes/Slice/`: a predicate between two blocks.
- **`K1` … `K15`, kind**: a kind of sub-protocol; `K14`, `K15` have no place on the first chain.
- **`K1`, `K01…`**: sending an encoding with an out-of-domain sample; no answer is compared here.
- **`K2`**: code switching: a folded row is sent again under a shorter code. (`KindName.K2`)
- **`K3`**: lookup argument: meant to show each key is in its table. (Johnson/Desc/First/Look/)
- **`K4`**: the layers' own rounds. (`KindName.K4`; `OnBytes.Road.K4.k04_of_head`)
- **"K04_law"**: comments' name for the law of the kind K4; its Lean name is `K04Law`.
- **`K5`, `K05`, `attentionKind`**: the rounds of one attention segment.
  (Johnson/Desc/First/Att/K5AttentionKind.lean)
- **`K6`, `K06`**: the output head's own rounds. (Johnson/Desc/Kinds/Head.lean) `K06_law`,
  `K06_means`, `K06_condition`, `K06_rounds`: comments' names for entries of a list of lemmas wanted
  for this kind, no Lean names; a file `K06….lean` serves one of them, and its head says how far.
- **`K7`, `K07`, `Reply`**: «the next token», «the reply»: the prover names it in the clear.
- **`K8`**: the draw of the approximate range proof ("the smallness test"), the check that committed
  values are small integers within a looser bound than honest values meet. (Johnson/Desc/First/K8/)
- **`K9`**: the batching: the round that samples the batching coefficients. (`KindName.K9`)
- **`K10`**: the closing of a link. (Johnson/P5J/K10Free.lean)
- **`K11`**: the merge of the claims on the committed table. (Johnson/K11R/KindAtFree.lean)
- **`K12`, `K12...`**: the proximity test. (Johnson/Loose/H2K12/K12AtHead.lean)
- **`K13`**: combines the linear claims on the committed matrix of weights into one.
- **`K14`, `K15`**: linear constraints of a batch; a kind of the copy's file. In
  `VerifierAndGoals.AtTheName.KindsLaws`, which has one law for each kind of sub-protocol, their two
  fields (`k14`, `k15`) are vacuous: these kinds have no place on the first chain.
- **`Keeps`, `SeatKeeps`, `…_keeps`**: a block keeps `R` if its accepting decisions preserve it.
- **kept, held, kept rows**: marked for later segments to read; a test's statement is over the kept
  oracle messages alone (`LdRunD`). Held: read as a slot of the folded word (`LdHeld`).
- **key**: Of a scheme: what the committer makes from an index, a verifier's key and a prover's key.
  Of a lookup: a value that has to lie in its table. Of the theorem's verifier: the pair of the
  first table's root and its OOD sample, held by the verifier of `innerCompiledVerifier_sound`; the
  commitment is the hash of its code. Under `OnBytes/`, `Johnson/`, also a table key, the key file,
  or a tree's number in a view (`treeKey`). Only the first is the key of a scheme.
- **key file, proof file**: `key.bin`: the first table's Merkle root and the committer's proofs
  about it. Proof file: what a client receives. The key file is not the "key" of the theorems.
- **key maker**: a committer that may cheat, in the experiment of index binding. (`bindingExp`)
- **`KeySeat...`, `KeyScopeNums...`**: facts on the key file's sampled messages, some had by
  evaluation at the full size's written values, some from equations in scope. (`Johnson/RunOne/`)
- **`KeySend...`**: the sendings of the key file's first chain. (`Johnson/RunOne/`)
- **kit**: In `Run/`, `Johnson/`: each round's challenge space (`CK`).
- **knowledge soundness, round-by-round knowledge soundness**: the library's name for a property of
  sub-protocols, blocks and reductions (`Know`, Ior/Know.lean). The soundness theorem on `verify` is
  index-binding knowledge soundness in its witness-free case: the extractor names the index (the
  weights) from the commitment and the committer's hash queries alone, and nothing is extracted from
  the prover ([TERMS.md](TERMS.md), note 1). Of the protocol as a whole: soundness as an IOP
  (TERMS.md, table 6).
- **`Laid`, `LaidAlone`, `alone`**: a chain's block is the supplied one inside the wrappers.
- **larger library**: in comments, a larger set of Lean files, not all of which are in this
  repository ([LIMITS.md](LIMITS.md), L25).
- **last segment**: see closed segment.
- **LastFits, EndFits**: named hypotheses from which `completeOn_end` derives `CompleteOn` for the
  argument system of a stand-in description (see there). (Johnson/Goal/Conditions/HomeEnd.lean)
- **a law file, no sub-protocol imports it, no running text imports it, NO BLOCK IMPORTS THIS
  FILE**: no file that defines a sub-protocol imports this one.
- **law, laws, the kind's law**: a lemma. A kind's law, in the counted form: its soundness lemma on
  every place of that kind (`P5J.AtMgA.Kind`). Of a record: a condition on its data (`LdCode.Laws`).
- **lawful table of scales**: the model's rescaling numbers, meeting `Scales.Lawful`. (Cm/Rel2.lean)
- **lawful work**: see proof of work.
- **layer**: a layer of the model. In `Iop/`, `Blocks/`, `Compile/`: a part of the
  construction. In `Cb/Part/`: one segment's part of the further witness.
- **layout**: how a message's coordinates are divided by use (`Sig.StdL`). In `Johnson/Desc/`: a
  group's members and rows (`GroupLayout`). Layout file: layout.txt, a public file.
- **lays, laid, lays in**: to put in place. To lay a theorem in: to supply it for a hypothesis.
- **LCoins, free parameters**: what the honest link prover's theorems leave quantified. (`LCoins`)
- **leaf, leaf salt**: a leaf of a hash tree, and its salt; in some names, a further encoding.
- **the Lean verifier (`verify`)**: see THEOREM.md. On these pages `verify` takes the hash function
  as an argument. The definition `VerifiableInference.leanVerifier`
  (AtFullSide/Face/TheSixLines.lean), whose docstring opens "The Lean verifier", is the compiled
  verifier with BLAKE2b. How the two stand to each other: LIMITS.md, "What is proved, and of which
  object".
- **lean-verify**: see THEOREM.md.
- **least-bound check, numbers that hold**: In `IntegerModel/Bounds/`,
  `VerifiableInference/Bounds/`: one of the two checks in the premise on the weights of the
  completeness theorem at weights that pass a worst-case check
  (`VerifiableInference.Compilation.theHonestPart_complete_where_some_worst_case_check_passes`;
  TERMS.md), a test with given numbers. "Numbers that hold": each stretch bound that the least-bound
  check reads is at least 0, and no vector of whole numbers gets longer by more than that factor
  when it is multiplied with its matrix. To pass the least-bound check is not enough (L27).
  (`leastBoundWorstCaseCheck`, `LeastBoundNumbers.Hold`, IntegerModel/Bounds/LeastBoundCheck.lean)
- **ledger, `Fork`, `WellLaid`**: the verifier's running list of the open segment's hidden scalars,
  by «slot» (`Fork`, OnBytes/Model/Hide.lean). In `Lib….lean` files: the cost ledger of `Policy/`.
  In comments also the files Johnson/Desc/K14/Law/Ledger*.lean, whose heads account for which
  hypothesis is proved in which file.
- **lenient reader**: see strict reader.
- **lens**: a pair of maps that read a part of an object and write it back. (Prob/LensLaw.lean)
- **letter, letters**: a parameter of a statement that is left a variable, not set to a written
  term, or a field of a structure that holds data; also the explicit values that a file defines.
  Letter for letter: word for word. The pages say "open parameter".
- **level**: a step of Lin for one linear claim (`levelsShape`); a forest's entries at one depth
  (`lvl`); a hash tree's vertices at one depth. A security level is the field's plain word.
- **`Lib`, the library**: in `OnBytes/`: the rest of `lean/`. In `Lib….lean` files, which lead to
  `Policy.HeadCl`, «the library's» marks names of `Policy/` and `Inst/`.
- **lies below, lies above**: a declaration lies below a theorem whose statement or proof uses it.
- **lifetime, lifetime game**: see `LifeB`, Compile/Batch/SpecLifeStar.lean.
- **Lin, run of Lin**: the protocol on linear claims on vectors sent encoded, with a proximity test;
  a run is one execution.
- **linear test**: see test for linear constraints.
- **link**: (1) The sub-protocol for the equality of two encoded indices
  (`HolographicProtocol.link`, Hiop/RecInterface.lean). In `Johnson/Prover/`, `Johnson/Goal/`: the
  first and the copy; the copy's file holds its proof, the link proof. In `Hiop/`, `Compile/`: the
  first and a further encoding; the key holds the link proof of each. (2) In `Fmt/M3*.lean`,
  `OnBytes/Slice/`, `OnBytes/Entry/`, `OnBytes/Tie/`: the protocol of a copy's file, between the
  first table and a further copy (`linkVerify`, OnBytes/Iop/Link.lean): as a definition, another
  thing than (1). Its lax form lacks the further test that a proof string has the strict format
  (`vLA'`). (3) In `Johnson/Desc/`, `Johnson/IMR/`, `OnBytes/Model/`: a segment (`Place.link`;
  `ReqLink`); not the link proof. (4) "The chain of links": a small test protocol, without model,
  key or table (`linksVerify`). (5) In `Ior/`: a step of a chain of reductions (`Iop.IOR.Link`).
- **list**: the codewords within a radius of a word. (`LdCode.ListAt`, Cb/Ld/LdRel.lean)
- **list of rounds**: see shape.
- **literal definition, literal form**: what a scheme has to meet as in `ZKCP/Defs.lean`, against
  `ZKCP/Gen.lean`. In `Cb/Ld/`: the field's form of round-by-round knowledge soundness.
- **live vertex, dead vertex**: a cube's vertex where a family has a say, or not. (`liveAt`)
- **live, protocolDataWellFormed, the live test**: the tests on the public files: a Boolean test on
  the three public files alone (`verify` makes further ones); where one fails, `verify` rejects
  everything (`FlashProve.protocolDataWellFormed`). That it returns true is proved, in the side
  library, at the written copy of the full-size example under every acceptance policy in scope
  (`theLive_zAt`); no theorem ties the copies to the files on disk (TERMS.md). "No files in scope
  are known at which `protocolDataWellFormed` rejects"; "whether `protocolDataWellFormed` accepts at
  all of it is not said here" (Johnson/Goal/Description/LiveSaysNo.lean). `protocolDataWellFormed`
  reads no proof: a yes is no sign that `verify` accepts any proof. It is one of the conditions on
  the public files under which most statements of table 6 are stated (TERMS.md, table 6, the row on
  public files in use).
- **local round, shared round**: the verifier message is drawn for each slot apart, or once for all.
- **local transcript**: the transcript of one slot of a batch. (`BTr.slot`)
- **locations**: the step in which the verifier reads an open word at drawn long positions.
- **long position, native position**: a long position is of the transformed word, a native one of
  the word as sent. Radii count long positions. (`LdCode`)
- **lookup table**: a public table of the model (such as exponentials). Not a committed table.
- **looser than exact match**: of a policy: it admits a request that exact match refuses.
- **`Lot`, `lot`**: a named table of blocks for some places of the first chain. (`ProofFile.Lot`)
- **made-up data**: the test values of the small test protocols and of Lean files' tests.
- **main theorem**: in comments mostly `innerCompiledVerifier_sound`, the theorem on
  `innerCompiledVerifier`. Elsewhere most often a file's own theorem, or a form of which the file
  asserts nothing.
- **`mark`, `guardMark`**: the field `failed`: the name of the first failed test.
- **mask code**: the code of a stage's 2^h mask rows, beside the main code `C`. (`Stage`)
- **mask, masked**: see `MaskData`, Ior/Masked.lean; `Masked`, Blocks/BlockHon.lean.
- **matrix of digits**: see index.
- **MatrixNums**: the numbers m0 and k_lo of the committed matrix. (Johnson/Flat/Claims.lean)
- **`Meaning.K2`**: conditions on the verifier's state; despite the name, not the code switch alone.
- **`Meaning.NamedAsk`**: a test on public data, `namedB`. (Johnson/Goal/Meaning/NamedAsk.lean)
- **Means, HeadOrdLB**: the relations of `means_of_served`. (Johnson/Goal/Meaning/Row.lean)
- **member, no member, may be empty, `Member`, `Toy`**: a concrete value that meets all hypotheses
  of a statement. "No member": no theorem is known to give one without premises, so the statement
  may hold only for want of a case. Of the standing hypotheses one exists at public files in scope
  that parse, wherever all the tests on the public files pass (`P5J.head_exists_at_name`); see live.
  A «toy» is built by hand from synthetic values; it reads no file.
- **message**: what a party sends in a round. Of a word: the vector that the encoder takes.
- **`Mg`, `mgAll`**: «meaning»: what open claims between sub-protocols say. (`mgAll`)
- **miss**: in `Policy/Rel/`, a counted position whose token is not the model's first choice.
- **model**: this library's integer program (`model`, IntegerModel/Model.lean). Under `OnBytes/`:
  the one of which the programs' proofs speak, not `model`, which no file there imports.
- **model checks, model options**: the verifier's tests of the model; lines that choose among them.
- **model output**: tokens each of which is the model's next one. (`ArgumentSystem.IsModelOutput`)
- **model weights, valid weights**: integer arrays that pass `weightsAreValid`. In `Blocks/`,
  `Alg/`, `Compile/`, `Prob/`: coefficients or costs.
- **the model's duty**: what whoever supplies a model has to prove of it. (`LdModelDuty`)
- **move**: In `Cb/`, one step from stage to stage. (`LdMv`, Cb/Req1/LdSeg.lean)
- **`Msgs`, `Told`, `toldMsgs`**: the oracle messages of a statement, or that a block declares.
- **the name, at the name**: in comments, `VerifierAndGoals.theDescription`: the protocol that the
  programs are written to run, as Lean describes it, one closed term. That this is what the programs
  run is not proved.
- **named entries**: see `LdWfP`, Cb/Ld/LdWf.lean.
- **named extractor**: an extractor that a property takes as an argument. (`Know`)
- **named hypothesis**: a field of a structure of propositions that a theorem takes as an argument
  (`CompilerSoundnessConditionsWithMeaning` for the theorem on `innerCompiledVerifier`). A
  hypothesis, not an axiom: Lean's list of axioms does not show it. One that is not proved is a
  limit of the theorem.
- **`Named`, `named`**: see `Meaning.NamedAsk`. In `FlagsNamed`: a number given explicitly.
- **naming**: In `Cb/Part/`, where a segment's rows and columns are in a body's matrix. (`LdPartNm`)
- **next-message function**: a prover given as a function to each round's message. (`MsgV`)
- **no two answers**: the library's own notion (TERMS.md): under one commitment and public files in
  scope that state exact match, no prover gets two different outputs of the same length accepted for
  one prompt in one list of at most N proofs, except with probability at most N times the error of
  the soundness theorem on `verify`, taken at the hash queries for the whole list. Not "no two
  openings": it says nothing of opening a commitment, nothing of `cp_commit`, and nothing under a
  tolerant policy. (`ZKCP.NoTwoAnswers`)
- **nonce**: see proof of work.
- **not within half the distance**: see unique decoding.
- **NoTwoOpenings**: see properties of an argument system.
- **numbers (of a reduction)**: its list of errors and further numbers. (`Nums`, Ior/Chain.lean)
- **object, protocol object, protocol**: In `Cb/Obj/`: what the sub-protocols are made from
  (`LdObj`). Under `OnBytes/Slice/`, the written protocol is another thing: one chain's (`written`).
- **offline**: see phase.
- **offline test, offline IOP**: the test whose proof the key holds for the first encoding.
- **Older, `secondHashFunction`**: `secondHashFunction` is the format's second hash function; the
  word Older in some names (`extractor_atOlder`, `bindsWith_atOlder`) means that function: see
  second hash function.
- **online**: see phase.
- **OOD, out-of-domain sample**: of a committed table: seeds with the answers of the table's rows
  under the sample map at them. (`recZ`, OnBytes/Slice/RecordRead.lean)
- **open rows**: see pending row.
- **open, `Open`**: in the statement, no test having closed it (`LdStage`). A link is open in `s` if
  `s.link?` returns its context. `IM.Open` names the values that `onlineDescription` computes.
- **opening (of a commitment), opener**: In `VerifiableInference/`: weights and randomness at which
  the system's committer returns the given commitment; an opener returns them (`BindsWith`). Of a
  scheme's key, in `ZKCP/`, `Rom/`: an index and a number at which its committer returns that key.
  In `Compile/`: an opened position of a hash tree (`Opening`). Under `OnBytes/`, `Johnson/`, never
  in the first two senses: a Merkle tree's columns read at sampled positions.
- **oracle message**: the data of one word that the prover sends, tested only as a whole. (`OMsg`)
- **oracles left**: see what a preamble leaves.
- **outcome**: see run function.
- **overrun, overrun term**: see `binTail`, Compile/Spec.lean.
- **owed, `rowsRead`**: of `rowsRead`, an open hypothesis (see debt) that is a condition on the
  three public files (a second reading returns, with one radius for each shape), which follows from
  the fourteenth entry test: a test of the verifier, not proved for all files in scope. It holds at
  `VerifierAndGoals.storedPublicFiles`, in a side library; see live.
- **own (column, tree), wanted**: over the oracle messages that a protocol's prover sends (`frOwn`);
  wanted positions: those that a round's samples ask to be opened (`wantedX`).
- **own masks**: see `LkAsm2.swAll`, Cb/Ld/LdLkpMaskAsm2.lean.
- **`Own`, `own`**: belonging to the segment at hand. (Johnson/Goal/Meaning/OwnInv.lean)
- **pack**: a request's part of the object's data (`LdReqPack`); a group for a closing (`GPack`).
- **packing, lane**: rows of cells, the lanes, combined into one with powers of a radix (`RngPar`).
  In `Johnson/Prover/Link/`: a folding stage's further table (`packedN`).
- **pad**: see `ConfigurationWithOutOfDomainSample`, Hiop/RecConf.lean; `Sample.pad`; `Stage`,
  Blocks/Stage.lean.
- **pad (LCoins.pad), the tails, the further row, the packing of W**: the link's first tree: two
  folds and the further row. (Johnson/Prover/Link/FrontCols.lean)
- **padding**: of a request: see prompt. Also of a lookup, and hash-tree leaves with no symbol.
- **paid, owed, spent, pays, payer, `…_paid`, `…Debts`**: see debt: a debt is a named hypothesis; to
  pay it is to supply it: by a theorem that derives it, often from further premises that stay, or,
  of a caller, at the call. A premise is paid where it is so supplied, owed where it is open, spent
  where it is used. A file or lemma named `…Paid` or `…_paid` states such a hypothesis as a lemma of
  its own, or restates a statement without some of its named hypotheses: others may stay. Not the
  Lean names `owedOk`, `DrawOwes`, `GoodOwesB`.
- **parameter bytes, schedule**: the serialization of a chain's parameters, among them its schedule,
  its list of rounds; the chain's first hash includes it. (`paramsBytes`, Fmt/Rules4.lean)
- **parameter list**: see item.
- **parser**: In `Run/`, from a proof file's bytes to a verifier's input, or a refusal. (`parseW`)
- **pending row, open rows, final batching**: a tensor row that a segment leaves open; the final
  batching joins them; open rows are shown at a request's end. (`LdORE`, Cb/Obj/LdObjectReqEnd.lean)
- **phase, offline, online**: the offline phase is the offline IOP: preamble, then test for linear
  constraints (`SubsR.offline`, Hiop/RecBuild.lean); the online phase is a session.
- **picked by choice, by choice**: taken by Lean's axiom of choice; no term is written out for it.
- **piece, tail**: In `Ior/`, parts of a chain; a tail ends at a statement without oracles. In
  `Cm/`, a summand of an atom. In `Fmt/`, a row's `r` entries beside its message.
- **`Pinned`, `Pins`, «pinned», «(pin)»**: fixed by something stated earlier. A `…Pinned` file
  states what follows where a test accepts that compares the public data with literals (`madeRow`).
  The type `Pinned` is a plain pair and itself asks nothing; «(pin)» asks what a decoder makes of
  it.
- **place**: In `Johnson/`, a sub-protocol's chain, link and number (`Place`,
  Johnson/Desc/Block.lean). In `Cb/`, a cell's address (`Place`, Cb/Req/ReqSpec.lean). In `Fmt/`, an
  offset in bytes.
- **plain head**: see head.
- **plain part**: what the verifier reads in full of a prover message. (`Round`, Iop/Shape.lean)
- **plan**: In `Cb/`, of closing a test for linear constraints: which groups of oracle
  messages are tested (`LdLinPp`, Cb/Ld/LdLinClosePlanP.lean). In `Fmt/`, `Run/`, `Johnson/`, the
  part of a chain's parameters that lists its entries (`Plan`, Fmt/Plan.lean); a test on the plan
  reads no proof and no state (`Block.planOk`). In `Iop/`, a re-shaping of rounds (`XPlan`). Under
  `OnBytes/Params/`, see `Planned`.
- **the plan's entry**: see entry.
- **the plan's share**: the premises of the form's half on public numbers alone. Nothing in
  `foldCuts_of_nums` ties `ownMask` to `P12.early`, which the IOP asks on the plan.
- **`Planes`**: the bit planes of the lookup argument's counts. (Johnson/Desc/Kinds/HeadCaller.lean)
- **`PlanK6`, `Pads`**: public tests on where data lie in oracle messages: `pads…`, that no read
  lies at a pad, the mask on an OOD answer. (Johnson/Desc/Kinds/PlanK6Test.lean)
- **planner**: reads the three public files, returns the plan of checks. (`Model.Verify.planned`)
- **policy file, policyFile**: the parameter file, policy.txt. `policyFile v`: the stored example's,
  its eight free numbers set to v. (Ladder/Stored.lean)
- **preamble**: reduces weights-formedness, or a request, to claims on index and oracles. (`SubsR`)
- **printer, printed form**: writes three compiled runs as the bytes the parser reads. (`printRaw`)
- **the program's reader, check, planner**: the text of which the theorems on `Shell.program` are
  stated. On a model's files and on a plan `main` does not run it: it runs the second writing (see
  there), at the identity monad and the program's own two hashes; theorems give the two the same
  values there. The five test commands run the first text.
- **program, programs**: The programs are the implementation that comes with this Lean code. The
  integer program is another thing, a definition in Lean: see model. In `Rom/`, an oracle algorithm
  as a Lean term (`OComp`). "By program" names scripts outside the tree. Under `OnBytes/`, "the
  program" is most often a stand-alone program that one may build from `verify-on-bytes` (this
  repository builds none), the verifier in Lean there (it is not independent of `cp_verify`:
  LIMITS.md, L22); "the two programs" are it and the C++ verifier `cp_verify`.
- **promise, `onAt`, `pubP`**: In `Johnson/`, the condition at a border on the public side, beside
  the relation there, which speaks of the witness (`onAt`, Johnson/Desc/First/Borders.lean). `pubP`,
  what a public item says beside its own test, is at the library's constant meaning a real statement
  at two of the 22 kinds of public item (`left`, `leftOn`), and true or false by definition at the
  others. That no border asks an item at which it is false is evaluated, at two written lists of
  places, not proved; that nothing more is meant at an item is a reading, not a theorem. Of a check:
  a bound is on the check saying yes while its promise fails; the promise speaks of the words read
  off the lists of hash queries, not of a file's bytes (`KeyHoldsCD`).
- **prompt, output tokens, padding**: In `VerifiableInference/`, lists of tokens; the padding is a
  proof's first part. In `Inst/`, `Cm/`, a request's prompt is its whole window: see request.
- **proof file**: what a client receives for one request; see key file.
- **proof of work, work, proof-of-work bits**: the prover must find a nonce such that the test bits
  of the verifier message are zero; one attempt in 2^w succeeds. (`Round.grind`, Iop/Grind.lean)
- **properties of an argument system**: definitions, each bounding an event's probability by its
  error argument. `Sound`: by an extractor from a commitment and the committer's queries.
  `SoundAndBinding`: the clause of `Sound` and, for the same extractor and error, of `BindsWith`.
  `SoundOpened`: no extractor occurs. `Complete`, `CompleteOn`, and for the others
  VerifiableInference/MoreStatements.lean: see TERMS.md.
- **protocol**: see object.
- **protocol description**: a verifier written as data (`FileDescription`, Johnson/Desc/Block.lean).
  Not the goals' `Description`.
- **protocol structure, HolographicProtocol**: the holographic IOP with an untrusted committer
  (`HolographicProtocol`, Hiop/RecInterface.lean): protocols `offline`, the key file's; `link`;
  `onlineBatch`, the proof file's.
- **protocol with slots**: see batch.
- **proved**: of a Lean theorem. Under `OnBytes/Model/`, `OnBytes/Params/`, and "proves" in other
  parts of `OnBytes/` and elsewhere, also of what the provider's files are meant to cover, not of
  Lean.
- **"the proved lemma"**: the wording of `verify-on-bytes`' printed lines and of comments for a
  source of a proximity term, which `cp_verify` prints as "the bound within a third of the
  distance": proved on paper, in the paper that this protocol builds on (see `lean/CREDITS.md`, "The
  paper that this protocol builds on"). Not proved in Lean for this program: nothing in
  `OnBytes/Params/` proves it, and no theorem ties the planner's number to it.
- **prover encoded index**: see encoded index.
- **the prover has lost, round-by-round sound**: `Doomed` (Iop/Rbr.lean): whatever the prover sends,
  at most that round's error many verifier messages lead to a position in which it has not lost.
  `InteractiveOracleProof.Sound`: it has lost at the start at every statement outside the language.
  Nothing is said about positions in which it has not lost. Under `OnBytes/Slice/`, `Sound` is this,
  not `Sound` of an argument system.
- **prover's key**: see key.
- **the prover's number**: what the written member's prover samples first. (`homeCoins`)
- **provider, committer**: runs the model and produces proofs; committing, it is the committer.
- **proximity term**: the part of a round's error figure from testing closeness to code words.
- **pruned openings, whole paths**: checking opened leaves by one walk per forest, or one path per
  leaf (`checkPrunedOpenings`). `parseFullW` makes no test of work and compares no root.
- **public bad set**: see `Honest`, Ior/Honest.lean; `Honest`, Iop/InteractiveOracleProof.lean.
- **public files, config folder**: `policy.txt`, `layout.txt`, `KL.bin`, written by the provider.
  Not the "configuration" of the library's theorems.
- **public reading**: an algorithm that asks the hash and gives a value
  (`LayoutsByPublicReading.Pub`). See told.
- **`Pure`, `onlineDescription`, `onlineFirstChainBlockTables`, `onlineDescriptionFromPublicPart`**:
  `ProofFile.onlineDescription`, the proof file's IOP.
- **quantization parameters**: see settings.
- **`Quiet`, `quiet`**: a relation of two verifier states; a quiet block has no round.
- **radius**: how many positions may differ from a codeword: a count, not a fraction. (`OMsg`)
- **random oracle, ideal hash, perfect hash**: a uniformly random function, only queried.
- **range check**: In `Cb/`, a check of bounds for cells. No lookup is run in it: that the digits
  are in their tables is a clause of its output joint. The bounds are those of its input joint, not
  the window's. (`RngPar`)
- **re-cut**: see altered copy.
- **`Reach`, reached, `ReachedAt`, `Rch`, `RchAt`**: the first `k` blocks of a chain accept and end
  in the state. `Rch` is a parameter. (`Reach`, Johnson/Top/H0/Walk/Reach.lean)
- **read-out**: see `LkAsm.rd`, Cb/Ld/LdLkpAsm.lean.
- **reader, decision function**: In `Fmt/`: bytes to a value, or a refusal (`Rd`). Under `OnBytes/`,
  it is meant to recompute every hash and check every Merkle opening; the decision function tests
  equations.
- **reading**: In `Cb/Part/`, `Cm/`, of an atom: items adding up to its multilinear extension
  (`Reading`, Cm/TargetRead.lean). In `Cb/Gen/`, of codes. See wide reading.
- **`Reads`, `Read`, «a read», the reads' place, the digits' place**: a read is a vector of sums of
  a committed matrix's cells under public weights. The reads' place and the digits' place are a
  link's two uses of the kind K1, at its moments 1 and 2. (Johnson/Desc/K1/Places.lean)
- **`Rec`, `RecAll`, `RecRel`**: short for record: the verifier's state.
- **record**: In `Hiop/`, `Cond/`, `Cb/Ld/`, a seed and an answer beside an encoded index
  (`ConfigurationWithOutOfDomainSample.Rec`, Hiop/RecConf.lean): a committed table's OOD sample.
  Under `Johnson/`, "the record" or "the carried record" is mostly the verifier's state (`S`), which
  is not that sample; "the public record" is `W`. Elsewhere a Lean structure.
- **record of protocols**: see interface.
- **reduction**: see IOR.
- **reference, reference request, reference segment, reference settings**: the sizes of the one
  model treated (`ppref`). In `Fmt/` and `Run/`, a reference program, or the reference, is a program
  outside `lean/`, other than the programs, that made test files, tables or the data of a traced run
  for these files, or against which their results were compared.
- **relation pair, relaxed relation, relaxed witness, relaxation**: two indexed relations, the
  second the relaxation, with a larger bound on the cells. (`RelPair`, ZKCP/Gen.lean; `Rno`)
- **relations' side**: a configuration's part with a model's two relations. (`RelSide`)
- **reply token**: see request.
- **the report**: see technical report.
- **request tree**: the hash tree over a batch's slots. (`QueryLayout`, Iop/BatchWire.lean)
- **request, checked token, next token**: For the model: a window of a fixed number of tokens, a
  range of positions, a reply of one token (`Instance`, Inst/Model/Program.lean). Position i checks
  token i + 1, a checked token; the last checks the next token. In `Compile/`, `ZKCP/`, any
  instance. In `Cb/`, also that part of the protocol.
- **reshaping**: data that carry words between codes. (`Reshape`, Cb/Ld/LdBatShape.lean)
- **rider, rides, rides with, rides along, ride**: what is carried through a step unchanged. In
  `Blocks/`, a second zero test: no further message or check. In `Johnson/`, of code, a ride: one
  evaluation of executable Lean definitions on given files; "a run's word": known from such an
  evaluation on those files, not from a theorem.
- **`Rng...`**: files on the proximity test behind the key file's range lookups.
- **road, below, under**: A declaration lies below or under a theorem, or on its road, if it is
  used, at any depth, in its statement or proof. In `Run/`, see `Road`.
- **`Roots`**: how many Merkle roots a chain has received. (Johnson/IMR/RootsSeat.lean)
- **round, target**: one prover message and one verifier challenge. The target is the bits that
  every round's error figure must reach by itself (`sec` in the parameter file).
- **round-by-round knowledge soundness**: see knowledge soundness.
- **rounds' data, ds**: each round's plan entry, kind, items, trees. (`RD`)
- **row**: In `Cb/`, a linear claim: a form with a target, the value that it has to take
  (`Slf.Holds`, Cb/Ld/LdRel.lean). Else the usual sense.
- **`Row…`, `K6On`, `K6In`, `K6Out`**: before a step of `K6`, what it opens, what it closes.
- **run**: one execution of a protocol or program. In `Cb/`, also of a proximity test (`LdRun`).
- **run function, outcome**: a file to accepted, or the stage that refuses. (`Who`, Fmt/M1Tiny.lean)
- **run of record, final check, trial, trial build**: a run of the full check, of the independent
  checker, or the Lean verifier's reference run, over the files as they ship (for the independent
  checker: the Lean code, comments apart). Every other run is a trial.
- **run value, run's value, first value**: the run's value and the first value are the two hashes at
  a chain's start (`runValueW`, Fmt/Rules4.lean); a run value is one in a whole file (`File.runOf`).
- **the running committer**: the illustrative committer on byte strings (`Bind.Twin.commitW`; as an
  algorithm from a table to the commitment ID, `Bind.Twin.twinID`; Johnson/Bind/README.md). It
  models one part of `cp_commit`. "Running" says only that Lean has code for it: it is not
  `cp_commit`, no theorem ties the two, and it has run at small sizes alone; at the full size, where
  the theorems on it stand, it cannot be run.
- **`Runs`, «run of claims»**: a named function that states a list of forms.
- **sample, sample map**: a set of seeds, each giving a matrix (`Sample`, Cb/Gen/OodDec.lean); the
  sample is a seed with the prover's answers (`OMsg.Smp`). In `Rom/`, to draw at random.
- **sampler**: a map at a uniform element; of commitment randomness (`Description.sample`).
- **says yes, yes, says no, refuses, a refusal**: to accept and to reject.
- **schedule**: see parameter bytes.
- **scheme, committer**: an argument in the random-oracle model: keys where an argument system has a
  commitment, a request where that has a prompt and output tokens. (`Arg`, ZKCP/Defs.lean)
- **`Scope`, `InScope`, «the goals' scope»**: public files that pass `VerifierAndGoals.InScope`. See
  in scope. A name with `InScope` or `_in_scope` has that test among its premises; most have further
  premises.
- **score policy**: see acceptance policy.
- **seal**: the digest that a chain's last round draws; no proof of work comes before it.
- **seam**: in `Compile/Joined/`, the first round of a file's third chain (`Chains.r3`).
- **seat, `Seat`, `seatAt`, `Seated`, `seatedAs`**: Mostly the functions through which a kind of
  sub-protocol reads and writes the verifier's state (`K3.Seat`). Also what the proof file's IOP is
  assembled from (`ProofFile.pureSeat`). In `Johnson/Goal/Description/`, a part of `theDescription`,
  from the public files and nothing of the proof. Else a position.
- **second checker, independent checker**: the independent checker (nanoda), a proof checker other
  than Lean's own kernel. It is not in this repository. See CHECKING.md; LIMITS.md, L25.
- **second hash function**: a second, fixed hash function, built on BLAKE2b's compression function
  (OnBytes/Hash/SecondHashFunction.lean). It is never asked as an oracle; the format page counts it
  as a second assumption.
- **second writing ("the twin"), first writing ("the port"), "over a monad", "the hash is asked"**:
  the second writing is the text under `OnBytes/ChecksWithHashAsArgument/M/`: the checks written
  once more, the hash an argument. "The port" is the first writing: this program's text outside
  `OnBytes/ChecksWithHashAsArgument/`, which follows `cp_verify`'s source; "the twin" is the second.
  Theorems named `_port`: the two agree at the identity monad and the program's own hash.
- **seed**: In `Cb/`, `Hiop/`, a verifier message from which coefficients are computed. In
  `Compile/`, `Rom/`, of committer and prover (`SeedOracle`). In `Fmt/`, of an OOD sample.
- **seed record**: a key's OOD sample: a seed with its answers. Else see record.
- **seeds set aside**: OOD seeds at which `HonFit` asks no acceptance; `HonFit.prZ` asks that at
  every index with an instance in `Yes` their probability is at most ζ
  (Johnson/Prover/All/OfHonest.lean).
- **segment, segment 24, piece**: a piece of a request's part of the protocol and of the model
  (`LdSeg`, Cb/Req1/LdSeg.lean); many comments call it a link. At full size number 24 is the output
  head's. Piece k is its k-th sub-protocol, from 1; comments under `Johnson/P4SR/` count from 0.
- **sending, sender, standard sender**: a step in which the prover sends oracle messages and answers
  with samples (`LdSendD`, Cb/Req1/LdSegKit.lean). A sender is the honest prover's part in it.
- **`Sends`, `SendsAt`, `SendsOn`**: what a block appends to the book. (Johnson/IMR/SendsFold.lean)
- **session**: one call of the prover; as a protocol, a request's preamble in every slot, then a
  batch's test for linear constraints (`SubsR.session`, Hiop/RecBuild.lean). In session-augmented
  index binding one prover hands in one list of requests with proofs, at once; it sees no decision
  of the verifier before it hands the list in, and it sees no honest proof.
- **setting, settings, valid settings**: In `IntegerModel/` and `VerifiableInference/`, the model's
  sizes and quantization parameters (`Settings`, IntegerModel/Model.lean), valid if they pass
  `settingsAreValid`. In `Inst/Model/`, a table of scales with an acceptance policy
  (`ScalesAndPolicy`, Inst/Model/ProgTests.lean). Under `OnBytes/`, a parameter set: how far codes
  are tested, whether proof of work is counted (`Setting`).
- **shape**: the list of a protocol's rounds (`Shape`, Iop/Shape.lean). In `Fmt/`, what an opening
  needs to know of a hash tree. Under `OnBytes/`, mostly a record of public numbers.
- **shared part**: see annotation.
- **shared point**: the verifier's message ψ* of one round of a linear test. (`pt`,
  Cb/Ld/LdLinChain.lean)
- **shared table's constant (`Sh.`)**: a named term of the shared chain's statements.
- **shift**: In `Cb/`, a block that joins lookups (`ShiftP`); in `Inst/`, a number of bits.
- **the shipped Lean verifier**: in comments of Lean files, `verify-on-bytes` (root
  `OnBytes/Main.lean`), not the Lean verifier `verify`; it is not proved sound, and this repository
  builds no stand-alone program from it. See `verify-on-bytes`.
- **side library**: the second Lean library, `AtFullSide`: files that Lean compiles with a larger
  thread stack, and what depends on them, the theorems on the honest provers among them (TERMS.md,
  table 6). Files under `E2E/` and `Johnson/` import it. It rests on a third library, `ShapeLines`:
  closed facts on the stored full-size layout that Lean's kernel evaluates; no default target, a
  thread stack of 256 MiB.
- **signature**: a statement's oracle messages; not a digital signature. (`Sig`, Cb/Ld/LdSig.lean)
- **simulator**: see `simulatorK`, CompileK/Main.lean.
- **the six theorems, the six lines**: `sound`, `soundAndBinding`, `completeOnCanServe`,
  `zeroKnowledgeOnCanServe`, `refusedHandsOutNoProof`, `repliesFit`
  (AtFullSide/Face/TheSixLines.lean), each about `compile (flashProve setup)` at a public setup.
  What each says, and what it does not: LIMITS.md, "What is proved, and of which object" and L93.
  They are not the same six as the fields of the final statement, the structure
  `FinalStatementOneBit` (TERMS.md, table 6); how the two stand to each other: LIMITS.md, L93. In
  the comments of some Lean files "the six lines" has another sense: in the files that state or
  prove the final statement, its six fields; in the files `FinalBinding*.lean`, the six fields of
  `BindingOf`.
- **sizes**: the sizes of a toy or of a copy's file; not the parameter bytes. (`Par`,
  Fmt/M1Types.lean)
- **skeleton**: In `Run/`, protocol data (`RS`); in `Johnson/Prover/Link/`, the record of the two
  tests at the chain's start, made of public numbers alone (`skelOf`).
- **slack**: the extra bits that a sampler draws (`kapSl`, Iop/DrawOf.lean). Of an approximate range
  check: the gap between the bound in the relation and the larger one in the relaxed relation.
- **slot**: one of the places of a batch: one request or empty (`BatchProtocol`, Iop/Batch.lean). In
  `Cm/`, rows of a segment's matrix; in `Cb/`, a part of a folded word.
- **small examples, full size, small test configuration**: the first two are configurations of the
  real protocol. The third belongs to the C++ library's small test protocols; it involves no model.
- **(Snd-B)**: round-by-round soundness of a batch protocol (`BatchInteractiveOracleProof.SndB`).
- **Sound, SoundAndBinding, SoundOpened**: see properties of an argument system.
- **spare oracle**: a further typed oracle that makes the coding onto. (`OracleName`)
- **spelling**: a value's bytes in `Fmt/` (`Undoes`); in `Cb/Part/`, a way of writing a Lean term.
- **split, splitting**: In `Cb/`, a step from one row on two groups to a row on each. In `Iop/`, one
  round turned into several (`RCut`, Iop/Split.lean). In `Rom/`, one random oracle split into two.
- **stage, stage's numbers**: In `Cb/`, a joint over oracle messages with samples (`LdStage`,
  Cb/Req1/LdSegKit.lean); in a tower, one fold with its code switch. In `Blocks/`, a block with its
  honest side and errors (`Stage`, Blocks/Stage.lean). Under `OnBytes/` and `Johnson/`, a level of a
  proximity test (`Sg`, OnBytes/Slice/Stage.lean), or a part of a full call: key, entry, request.
- **stand-in description**: in comments, a `Description` used in place of `theDescription`. (At
  `theDescription` the honest side is a constant one: a committer that returns one constant and a
  prover that hands over empty files, whatever the weights; nothing on completeness can be said
  there.) A theorem at such a description, even one of a goal's form such as `G9_theWider`, is not a
  goal.
- **stand-in system**: in comments, what the pages call an illustrative system: a system that keeps
  the Lean verifier's verifier and extractor and has an illustrative committer (`theCpp`,
  `theWideDigits`, `plainSystemAt`; TERMS.md, table 3).
- **standard conditions**: named conditions that the public files must meet before any call can
  pass. If one is missed, the best possible result is `NOT-A-VERIFICATION`.
- **standing hypotheses**: see head.
- **state**: Of a form: the part of the explicit statement on which its coefficients depend. Of a
  builder: the segments built so far. A state function says whether the prover has lost
  (`IsKState`).
- **statement on codes, theorem on codes**: The theorem on codes is Theorem 4.6 of the full version,
  ePrint 2025/2055, of the paper by Ben-Sasson, Carmon, Haböck, Kopparty and Saraf published at STOC
  2026; the accounting takes it as given, and no proof of it is verified here. The Lean library
  proves the statement that stands in that theorem's place (the statement on codes, `Cb.BCHKS46At`:
  ours, and not that theorem), from files that AI systems adapted from ArkLib and Mathlib
  (`ThirdParty/`; LIMITS.md, L15). That this statement follows from the cited theorem is by reading,
  not machine-checked. Where the accounting applies it: OnBytes/LIMITS.md.
- **statement, explicit part, implicit part, trivial statement, `Statement`, `st`**: a statement has
  an explicit part, which the verifier holds, and an implicit part: oracles (`IOR`, Ior/Ior.lean).
  The trivial statement has neither. `st` is the verifier's (`Statement`, OnBytes/Iop/Ground.lean).
- **step without rounds**: a reduction with no round. (`IOR.pure`, Ior/Frame.lean)
- **stored examples**: `examples/accepted-proof`, `examples/accepted-proof-clipped-gap`,
  `examples/full-size`. Their pages say that the weights are made up; nothing in the files shows it.
- **stored table, first table, copy**: the committer's Reed-Solomon encoding of the weights under a
  Merkle tree. The first table is of the first encoding; a copy is another table for the same
  weights with fresh randomness.
- **StratLaw**: a premise on a prover's runs and field words. (Johnson/Prover/Print/StratLaw.lean)
- **stream**: the model's residual stream: the vector at each position that the layers add to.
- **stretch, stretch bound, stretch numbers**: In `IntegerModel/Bounds/`,
  `VerifiableInference/Bounds/`: a stretch bound is a number given for a matrix: it is at least 0,
  and no vector of whole numbers gets longer by more than that factor when it is multiplied with its
  matrix. (`StretchBound`, IntegerModel/Bounds/LengthCheck.lean) See least-bound check.
- **strict reader, lenient reader**: The strict reader renders the format page's verifier up to its
  decision (`wholeChain`). A lenient one makes no test of work and compares no root (`laxWhole`).
- **string**: a string of bits, as the one hash function takes it; query counts count these. In
  `Iop/` and `Ior/`, an oracle message. Under `OnBytes/`, an external oracle.
- **strong (encoding)**: see `ConfigurationWithOutOfDomainSample.Strong`, Hiop/RecRows.lean.
- **structural conditions**: conditions on a chain's schedule that `OnBytes/Tie/` needs. A
  description from which an opening was left out by mistake still meets them, and its compiled
  verifier checks less. A separate function, `eachOnce`, tests that every tree is opened exactly
  once; that it says yes is proved at some fixed parameter strings.
- **sub-proof**: under `OnBytes/`: the part of a request's proof that covers one link: a group of
  layers, the attention of such a group, or the output head.
- **sub-protocols**: the protocol's parts (`SubsR`, Hiop/RecSubs.lean), or one used as a move.
- **switch**: see code switch.
- **table key**: what a verifier is given of one committed table. (`TableKey`)
- **table of joints, the table**: one row for each sub-protocol of a chain: which named claims it
  closes, opens, and leaves open. It is definitions only; it proves nothing. Each Borders… file says
  its limits in its head. (`rowOf`, Johnson/Desc/First/Borders.lean)
- **table's name**: a committed table's root and OOD answers, not the encoded weights. (`TableName`)
- **table, table of scales**: Of words: a family of words of equal length. Of a lookup: the values a
  key may take (`Tab`, Cb/Req/ReqSpec.lean). Often a table of scales: see lawful table of scales.
- **tag**: which compiled protocol of an interface is meant. (`Tag`, Compile/Oracles.lean)
- **target**: see row; round, target.
- **tau, taus**: In `IntegerModel/Bounds/`, `VerifiableInference/Bounds/`: a list of whole numbers
  that is given to the least-bound check beside the stretch bounds. It may be any list: nothing is
  asked of it. (`LeastBoundNumbers.taus`, IntegerModel/Bounds/LeastBoundCheck.lean)
- **technical report, the report**: a technical report on this protocol that is not public: see
  CREDITS.md. The report is not in this repository.
- **tensor form, tensor row, tensors**: a linear form on the index's matrix (`IdxFmt.form`,
  Cb/Gen/Tensor.lean); a tensor row is a claim on one. For tensors: see model weights.
- **term**: In `Cb/Obj/`, a sub-protocol as data (`LdObj`); of a condition, a product of atoms.
- **test bits, main code, mask code, row variables**: see OnBytes/Slice/README.md; proof of work.
- **test for linear constraints, linear test**: the proximity test after a preamble. (`SubsR`)
- **theWider, the written member**: a stand-in description with the goals' verifier, and its
  explicit member.
- **`ThreeAtFree...`**: files of `Johnson/P5J/` that derive `h.Three h.free` from `h`, each naming
  the premises that it leaves; the last, `three_at_free_head_alone`, leaves none but `h`.
- **tidy**: rules that rewrite byte coins to the lengths that the printer asks; not one to one
  (`ByteCoins.tidy`, OnBytes/Prover/Print/Tidy.lean). Under `Johnson/Desc/AtSeats/`, a property.
- **tie, tied, t1 to t5**: a lemma that connects two texts, or that two forms of one thing agree
  (`Spec.planDraws_tie`, Run/PlanDraws.lean). Under `Johnson/Desc/`, t1 to t5 let a kind's soundness
  lemma be used at the table of joints (`TiedAt`, Johnson/Desc/Sound/ChainOfPromises.lean). Under
  `OnBytes/`, a theorem: if a function of this program accepts some bytes, the library's compiled
  verifier accepts them too, under stated hypotheses (in some, equations on the configuration files
  as read, which no theorem proves of any files), and for a key file only its first chain. It says
  nothing about what that verifier's yes is worth.
- **told, LayoutsByPublicReading**: the compiler's inputs that depend on digests of the public
  files. (`LayoutsByPublicReading`)
- **top, the top, top theorems**: a theorem whose conclusion is one of the goals' statements
  (`sound_of_verify_at`, Johnson/Goal/Skeleton/SoundOfVerifyAt.lean).
- **tower**: folds and code switches, down to a base case. (`LdTower`, Cb/Ld/LdTower.lean)
- **toy**: a small example; in `Fmt/` and `Run/`, a small test protocol. (`QT`, Run/ToyQ.lean)
- **trace**: Of the model: its cells (`Trace`); of an algorithm: its queries with their answers.
- **track**: see `Core.Track`, Blocks/StageTrack.lean.
- **transcript**: all messages of one execution of an interactive protocol. (`Tr`, Iop/Shape.lean)
- **transformation**: see long position.
- **true request**: a request on whose prompt the integer program runs at the index's weights, with
  greedy checked tokens and the matching reply. (`IsTrueRequest`)
- **try, tries**: the nonces of a proof of work's search; in `Fmt/`, a rejection-sampling step.
- **two named sets of files**: the two stored sets of public files, at which `G3'pol` speaks, as
  Lean terms (`storedPublicFiles`, `zGap`); their tie to the repository's folder is said in the head
  of Ladder/Stored.lean.
- **typed**: as a Lean term of a stated type, not bytes of a file (`TypedProof`, Ladder.lean).
- **typed oracle, typed query**: one of several independent random oracles, one for each kind of
  query (`OSpec`, Rom/OSpec.lean). One typed query can be many strings to the one hash function.
- **unique decoding, half the distance, within a third**: e is within half the distance d if twice e
  is below d (`OMsg.Half`, Cb/Req1/LdReqJohn.lean), within a third if three times e is below d.
- **user's statement, served, pins**: the three public files, the request, the reply and the options
  of a call (`stmOf`, OnBytes/K/Top.lean). The tie of `exit_innerCompiledVerifier`
  (Johnson/Top/TieInnerCompiledVerifier.lean; it holds only under six hypotheses that are not
  proved: by its file's head none is proved at any input, and a hypothesis may be false, not only
  unproved; no soundness of this program follows from it) speaks of statements that are served
  (`servedAt`, OnBytes/K/Served.lean): the public files are Z's, byte for byte (the three pins); the
  options name an ID and neither `-policy` nor `-no-proof-of-work`; the printed digest and the
  planner return; and the end of the call, computed without the three files' checks, is a yes. It is
  another thing than the tests on the public files that some theorems take as a premise and that
  this program does not run.
- **vector floor**: the level of blocks on plain vectors. (`Block`, Blocks/Block.lean)
- **verifier**: Of an argument system: `ArgumentSystem`, VerifiableInference/Statements.lean. Of a
  scheme: `Arg`, ZKCP/Defs.lean. Of a protocol: `InteractiveOracleProof`,
  Iop/InteractiveOracleProof.lean. Under `OnBytes/`, an argument system's or a scheme's verifier is
  named only where a page or a head says that nothing there is tied to it; see compiled verifier,
  program.
- **verifier message, challenge**: what the verifier sends at a round's end. (`Round`)
- **verifier on bytes**: proof file to yes or no. (`verify`, Fmt/M1View.lean; not
  `VerifierAndGoals.verify`)
- **verifier's key**: see key.
- **`verify-on-bytes`**: the Lean text below `OnBytes.Main` (`OnBytes/Main.lean`): a hand
  translation of `cp_verify` into Lean, from which this repository builds no stand-alone program. It
  is not the Lean verifier, `verify`, and it is not proved sound (THEOREM.md).
- **`verify()`, `innerCompiledVerifier`**: the verifier that the library's compiler makes from an
  IOP written in Lean. It takes typed values, not files, and asks the hash as an oracle.
  `VerifierAndGoals.verify` runs it behind a test on the public files, two public readings and a
  parser. The theorem on `innerCompiledVerifier` (`innerCompiledVerifier_sound`) holds under 16
  named hypotheses (`CompilerSoundnessConditionsWithMeaning`), of which four are left in general at
  the two IOPs of Johnson/Flat/TwoSizes.lean (LIMITS.md); a toy meets all sixteen (`two_holes`,
  Johnson/Top/Toy/CompilerSoundnessConditionsAtSmallExample.lean). The soundness theorem on `verify`
  is another theorem: its only hypotheses are three on the public files (THEOREM.md). "verify()"
  stands for `innerCompiledVerifier` under `OnBytes/` and `Ask/`, and for `verify` elsewhere, on
  GAPS.md among them (LIMITS.md, L53).
- **verifyAtKeyRoot**: the scheme's verifier over the typed oracles.
  (Johnson/TypedOracleCompiler/RecCompile/FrontRootAns.lean)
- **`…W`**: marks a written value: a closed term for the full-size model, on which Lean's kernel can
  evaluate a test (`placesW`, `linksW`, `zW`). In `SampleAtW`, `shW` and in comments, W is the
  oracle message of that name, which a commitment after the last segment sends.
- **`W`, `Wp`, `hS`, `iU3`**: what the configuration files give. (OnBytes/Model/VerifyPublic.lean)
- **walk**: over Lean's compiled record: a program that starts at a theorem and follows every name
  in Lean's compiled record of its statement and proof, and so on down. It shows which declarations
  occur there, not what each is used for. Every walk is a trial. Of a hash tree: see pruned
  openings.
- **weights-formedness**: the relation that the encoded index encodes the prover's message and
  randomness, and that the message comes from an index.
- **what a preamble leaves, oracles left**: oracles, claims and their condition.
  (`ConfigurationWithOutOfDomainSample.Left`)
- **what else is claimed**: what a move carries along beside its claims. (`LdBatD`)
- **whole test**: from a group's joint to the trivial statement. (`LdRunD`)
- **`Whole`, `whole`**: `Whole R b`: `b` preserves `R` on states. (Johnson/Desc/FoldKeeps.lean)
- **wide**: may read the instance, external oracle and whole transcript. (`SndBKT`)
- **wide reading**: not wide: see `wfWide`, Cb/Ld/LdWfMasks.lean.
- **window, window event**: Of a range check: from -D up to, but not including, D (`InWin`). Of a
  request: its prompt positions.
- **wire, wiring, wire record**: the data that the compiler needs beside a protocol to write the
  compiled verifier (`QueryLayout`, Iop/BatchWire.lean). In `Cb/`, a structure of conditions.
- **wired**: of an interface: the decoder inverts the encoder. (`BatchProtocol.Wired`,
  Iop/Batch.lean)
- **withheld, withheld set**: where no acceptance is asked of a prover. (`Honest.withheld`)
- **witness map**: reads a witness off an instance and a local transcript. (`SndBK`, Ior/Batch.lean)
- **word**: a vector of symbols on a code's positions, codeword or not (`LdCode.Word`,
  Cb/Ld/LdRel.lean). In `Fmt/`, `Run/` and `Johnson/`, also a fixed-size integer (`u64`).
- **written value, written cut, closed fact**: A written value is typed into a Lean file as a
  literal. No theorem is known to say at all files in scope that it is what the public files give:
  an entry test compares the two when `verify` runs. The written cut divides the three chains into
  sub-protocols. A closed fact is a statement on such literals alone.
- **written, explicit**: given by an explicit definition, as against a hypothesis or an existence
  statement.
- **`Wt`, `Wa`, the claim on the weights**: the claim on the head weights for the merge. (`wtK6`)
- **`Z`, `AtZ`**: the IOP's public part (`ProofFile.Pub`); in some files the public files
  (`VerifierAndGoals.PublicFiles`).
- **zAt**: `storedPublicFiles` under another acceptance policy.
  (Johnson/Goal/Files/ScopeAtPolicies.lean)
- **zero knowledge, exact**: see `Honest.Exact`, Ior/Honest.lean; `Exact`, Ior/Batch.lean.
- **zeroE**: the element 0 of the cubic extension field. (`zeroE`, OnBytes/Field/Ext.lean)
- **ZeroKnowledge, ZeroKnowledgeOn**: see `ZeroKnowledge` in VerifiableInference/Statements.lean.

## The folders of `Johnson/`

Most names of folders and namespaces (`P5J`, `LPFD`, `H2K12`, `Loose`, `Face`, `AtFullSide`, `T1`
and their like) are working labels of parts of the library: they say little or nothing of the
content. Not every folder has an entry here, and not every word of the comments has one above.

- **`Johnson/Bridge/`**: Carries `Cb.BCHKS46At` (`Cb/Bridge/CodeListRSProved.lean`, whose head says
  on what its proof rests) to the numbers of the proximity tests: Boolean tests for each kind of
  sub-protocol, what follows where they accept. `...AtWritten`: evaluated at numerals; their heads
  say what ties these numerals to a file's list of rounds, and what does not.
- **`Johnson/Desc/AtSeats/`**: Lemmas on K1, K13, K14 at the description's values. `Fit/`: rounds.
- **`Johnson/Desc/AtSeats/Queue/`**: One file: a proposition fixed by a definition, with no theorem.
- **`Johnson/Desc/Book/`**: The book of commitment trees (`TreeBook`): where messages stand.
- **`Johnson/Desc/First/Att/`**: The sub-protocol K5 (attention) and the theorems about it.
- **`Johnson/Desc/First/Batch/`**: Step kind `K9`, the batching draw and the one equation; `K9Law`.
- **`Johnson/Desc/First/Close/`**: Step kind `K10`, the closing of a segment, with lemmas in `Law/`.
- **`Johnson/Desc/First/K8/`**: `K8`, the draw of the approximate range proof ("the smallness
  test"), its lemma. Many of its lemmas have hypotheses: most of the files' heads name them.
  LawTeeth.lean, LawParted.lean: controls in which a weakened decision fails it.
- **`Johnson/Desc/First/Link/`**: Checks on public numbers: `rowsMadeB` (RowsRun.lean) is check 14
  of `LPFD.lawsAsk`; the four `K9…Ask.lean` are not in that list, and the verifier does not run
  them. `Law/`: the kinds' lemmas joined for one segment, under `LinkOwes`, `LinkList`.
- **`Johnson/Desc/First/Look/`**: The lookup argument (kind `K3`), the sub-protocol that is meant to
  show that every key of a group of table look-ups stands in its table.
- **`Johnson/Desc/First/Walk/`**: The book-keeping rows' text, as plain functions on the state.
- **`Johnson/Desc/K1/`**: The kind K1 as a block. `Law/`: up to its 52 places on the first chain.
- **`Johnson/Desc/K12/`**: The proximity test (kind K12): the verifier tests that committed words
  lie close to codewords.
- **`Johnson/Desc/K13/`**: The K13 step, agreement with `OnBytes/` functions, and `Law/`.
- **`Johnson/Desc/K14/`**: The kind K14 and the proof file's shared chain, with `Law/`.
- **`Johnson/Desc/K15/`**: Block kind K15: the rounds of the copy's file's chain alone ("the link").
- **`Johnson/Desc/Key/`**: The key file's protocol in blocks (three chains). `Laid/`: what an
  accepting run writes. `Plan/`: eight Boolean tests on a key file's plans, on public data only.
- **`Johnson/Desc/Kinds/`**: `K6` (output head), `K7` (the round naming the next token), with
  `Law/`.
- **`Johnson/Desc/Laid/`**: The Lean verifier's value for the proof file: it builds
  `ProofFile.onlineDescription`, runs its checks and `LPFD.lawsAsk`, and returns data and decision
  or a rejection (`proofDataAndDecisionOfPublicFiles`).
- **`Johnson/Desc/Link/`**: The copy's file's protocol: one chain, "the link";
  `linkDecisionAtParameterFile`.
- **`Johnson/Desc/OnPlan/`**: Boolean tests that read the planner's output alone.
- **`Johnson/Desc/Own/`**: Small tests that several kinds share; agreement with `OnBytes/`.
- **`Johnson/Desc/Part/`**: The masked sumcheck, which several kinds call (`MaskedSum4.lean`).
- **`Johnson/Desc/Plain/Leaves/`**: `FileDescription.Hears`: a heard reply, once written, stays.
- **`Johnson/Desc/Reply/`**: One file: the round REPLY of a proof file's first chain.
- **`Johnson/Desc/Sound/MgAt/`**: Lemmas under named premises on what kinds' lemmas ask of `mgAll`.
- **`Johnson/Desc/Third/`**: The last chain of a proof file's description. `Law/`: its first step.
- **`Johnson/Face/`, `VerifiableInference/Final/`, `AtFullSide/Face/`**: the compiler, the final
  statement and the statements on the honest provers; the namespace is
  `VerifiableInference.Compilation` (TERMS.md, table 6).
- **`Johnson/Flat/Told/`**: Values of `LayoutsByPublicReading`
  (`Johnson/Top/InnerCompiledVerifierByPublicReading.lean`), and lemmas.
- **`Johnson/G/`**: `Switch…`: the code switch at its 25 places; under premises on the sizes that
  these files do not show the planner's sizes to meet, its output equals numeral tables.
- **`Johnson/Goal/`**: What is stated or proved of the goals' own terms (`verify`, `InScope`,
  `theDescription`). At its top: soundness at `theDescription` from named hypotheses, which stay
  hypotheses there (without them: `Johnson/Goal/Skeleton/`), and forms with `SoundAndBinding`,
  `SoundOpened`, which are stated of illustrative systems: `theDescription` with an illustrative
  committer laid in, written in Lean; no theorem ties it to the program that commits.
- **`Johnson/Goal/Conditions/`**: Statements at `theDescription`, at a copy with a committer written
  in Lean (an illustrative one: no theorem ties it to the program that commits), or general in the
  IOP: rows on soundness, `BindsWith`, `NoTwoOpenings`, `G9`, the extractor. Many have hypotheses:
  each file's head names them. `KeySound` and `EntrySound` are proved by `keySound_holds`,
  `entrySound`.
- **`Johnson/Goal/Description/`**: `VerifierAndGoals.theDescription`, part by part (line "State":
  what it is).
- **`Johnson/Goal/Files/`**: `filesRead`. `ScopeAtNarrowNorm.lean`: tests by evaluation, no theorem,
  that three sets of public files are in scope: the stored full-size files with other values written
  in (MF ≤ KF + 11). Whether a table fitted to a model has such exponents is not said.
- **`Johnson/Goal/Meaning/`**: What the protocol's claims mean for the integer model. In file names
  "Hid" is the witness of the relation (what the prover does not send): no statement on hiding the
  weights. `K2Share/`: the code switch alone.
- **`Johnson/Goal/Numbers/`, `PlanValues/`, `Scope/`, `Written/`**: At public files in the goals'
  scope, the planner's output is a written value of the full size; some under a named premise, which
  the file's head tells.
- **`Johnson/Goal/PolicyAndBinding.lean`**: States theorems of the form of the goals `G8bits` and
  `G9bits` at the illustrative system `theWideDigits`, whose committer corresponds to no program of
  this repository, whose sampler gives 0 and whose prover hands over empty files; no theorem says
  that `verify` accepts a proof under its commitments. No new goal is stated.
- **`Johnson/Goal/Reads/`**: The verifier's further public reading (`readMore`).
- **`Johnson/Goal/Skeleton/`**: The theorem `sound_of_verify_at`, its further forms, their steps.
- **`Johnson/Goal/Tie/`**: The tie between `VerifierAndGoals.verify` and the form that a run calls:
  `TieSteps.lean`, `TieWhole.lean` equate the two under named premises (at the format's own hash
  function, two of these premises are proved). They are equations of values and claim no soundness.
- **`Johnson/H2K5R/`**: Ties `Johnson/Desc/First/Att/` (K5) to the IOP as written in Lean.
- **`Johnson/HB/`**: `LLHARD/`: the values written for the full-size plan, and tests giving them.
- **`Johnson/IMR/`**: Lemmas on `ProofFile.onlineDescription`; `MeetsPolicyAtPort.lean` sets
  `MeetsPolicy` beside `aboveClip`, `policyEmpty`, at exponent 8 alone: that the programs compute
  the same is not proved.
- **`Johnson/K11R/`, `P1L20R/`**: The merge's and book-keeping rows' lemmas, from the standing
  hypotheses.
- **`Johnson/K1PenR/`**: `Johnson/Desc/First/K8/LawCondK1.lean` at other names. No new argument.
- **`Johnson/K8Q14R/`, `K8Q21R/`, `K8Q33R/`, `K8Q35R/`, `K8Q42R/`**: The smallness test (K8) at the
  25 links: `IM.k8_tau_128` (in scope, where `IM.Open` holds, tau = 128); `P5J.At.smallRun_links`;
  `K8Q33.cellsIn_at_draw`, under the premises that the file's head lists; under `P5J.AtMgA`,
  `K8Q35.smallPlan_at`, `K8Q35.seated_at_head`, and, at the format's second hash function, at the
  full model size only, `cellsPlan_at_head`, `nums_at_head`.
- **`Johnson/LinkSim/`**: The link proof (see TERMS.md); `homeExactAt` (`AtHome/HomeExactAll.lean`).
- **`Johnson/Loose/`**: `H2K12/`: lemmas on the proximity test (K12) at the stored full-size files.
- **`Johnson/LPFE1R/`**: Lemmas that supply hypotheses of the statements on `K9` and `K10`.
- **`Johnson/LPFFrame/`**: A step from a law on a whole file's decision (`run`) to `AccLaw`. Its
  premise is shown of no strategy, and the files name none of the goals.
- **`Johnson/LPFK10R/`, `LPFK9R/`**: Carry statements on `K10`, `K9` to the proof file's IOP.
- **`Johnson/Meaning/`**: Six files tie `PlanesLaw.lean` (bit planes) to feed-forward segments.
- **`Johnson/P1HeadR/`**: In scope, `frontB2` accepts at the 25 code switches, under premises.
- **`Johnson/P1K2R/`**: Code switching's lemma at its 25 places, under `P5J.AtMgA`.
- **`Johnson/P1K8R/`**: The soundness lemma of `K8` at its 25 places, under `P5J.AtMgA`. No file
  here claims soundness of the protocol.
- **`Johnson/P1K9R/`**: Premises of the batching's lemma (`K9`) at the lookups' runs.
- **`Johnson/P2LawR/`**: Mostly theorems that serve the law of the last chain.
- **`Johnson/P2R0R/`**: Lemmas, each under premises that it names, for the last chain's first row.
- **`Johnson/P4R/`, `Johnson/P4SR/`**: The IOP around the output head. Cited as `P4/…`.
- **`Johnson/P5J/`**: Lemmas on batching and closing under `P5J.AtMgA`, the standing hypotheses.
- **`Johnson/P5T/`**: `…Full.lean` evaluates a check; `…AtMg.lean` carries it under `P5J.AtMg`.
- **`Johnson/Prover/`**: `Link/`: the link proof's honest prover, written in Lean (see TERMS.md).
- **`Johnson/PV/`**: Between the verifier of the theorems and a form that runs on files: an encoding
  of hash queries as bytes, one-to-one and onto in `LawsAny.lean` under named premises that these
  files do not show to hold of any data; a run's arguments; and a route from named hypotheses to the
  goals `G7`, `G8`, `G9`, none of them met outright in these files. Neither `G9` nor completeness
  under a policy is proved of `theDescription`, whose honest side is a constant one (TERMS.md, note
  8). The six theorems are about the final system, which has the same verifier, with the honest
  committer and prover that `compile` makes in the place of that constant side (`finalSystem`,
  `Johnson/Face/FinalStatement.lean`).
- **`Johnson/PVR/`**: The executable form of `verify`. Where `rideOf`, `verdictFrom`, `verdictThe`
  return a verdict, it is the value of `VerifierAndGoals.verify` at the hash function made from the
  same function on bytes; where they return no verdict, the theorems say nothing.
  `SoundOfTheForm.lean`, `SoundOfTheFormEvents.lean`: on every parsed proof file its verdict is
  `verify`'s decision, and soundness of its own decision, both where the functions on bytes answer
  with 32 bytes.
- **`Johnson/Road/`**: Mostly compares the program under OnBytes/Model/ with Inst/Model/ on lookups,
  as theorems under named public premises or evaluations at example sizes. `K4/`: kind K4.
- **`Johnson/RunOne/`**: One run of the key file's description. `Law/`: places. `Sound/`: its text.
- **`Johnson/Stored/`**: Where `K6` and `K7` meet the verifier's state: each one's "seat".
- **`Johnson/TocK8R/`**: In scope, `IM.Open` gives the premises of `k08_sits_front` at the 25 links.
- **`Johnson/Top/Fire/Code/`**: Joins blocks' laws to soundness statements for key file and copy's
  file.
- **`Johnson/Top/H/Keep/`**: What the lookup (`K3`) changes in the state and its ledger of slots.
- **`Johnson/Top/H0/`**: Code switching's definition (`Tw/K2/`, `Tw/K2C/`), and soundness lemmas
  with ties to the table of joints for `K2`, `K11` and the book-keeping rows (`Walk/`). Many have
  hypotheses: most of the files' heads name them.
- **`Johnson/Top/H0/Fill/`**: One layer of a `Meaning` value, a filling of the table (not of
  parameters).
- **`Johnson/Top/H0/H2K/`**: Three helpers of the switch under `OnBytes/`, as formulas in the field.
- **`Johnson/Top/H0/K11Caller/`, `MergeLaw/`**: The merge's lemma and parameters.
- **`Johnson/Top/H0/K2Caller/`**: Code switching's lemma at one place: `sel_law` at a row.
- **`Johnson/Top/H0/K2Hands/`, `K2Hears/`**: What the code switch hands on and reads.
- **`Johnson/Top/H0/K2Ties/`**: Code switching's ties to the table of joints, under `K2Owes`.
- **`Johnson/Top/H0/Opts/`**: Lemmas that derive the accept of named tests on public parameters.
- **`Johnson/Top/H0/StepLaws/`**: What an accept of `Block.step` says.
- **`Johnson/Unfolds/`**: Holds the tactic `kernel_rfl`, which closes a = b with the term Eq.refl b
  so that the kernel, not the elaborator, compares the two sides (KernelRfl.lean).
