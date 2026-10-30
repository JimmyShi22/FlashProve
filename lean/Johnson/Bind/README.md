# Properties of an illustrative system in Lean (`lean/Johnson/Bind/`)

Terms: [TERMS.md](../../TERMS.md).

In the Lean verifier's system (`lean/TERMS.md`) the honest committer is the constant committer (a
committer that returns one constant whatever the weights, and so commits to nothing; the committer
of the six lines is another: the one that `compile` makes (`Johnson/Face/Compiler.lean`), which
encodes the weights and hashes the key). This folder holds one more illustrative committer and one
more illustrative system (`lean/TERMS.md`, table 3); it adds no honest committer of the programs'.
Binding as one of the six theorems (`soundAndBinding`), at the honest part's committer:
[LIMITS.md](../../LIMITS.md), L93.

1. An *illustrative committer on byte strings* (`Bind.Twin.commitW`) that makes the format's own
   hash calls. It models one part of `cp_commit`; no theorem ties them. It is executable text, run
   at small sizes alone. The part: it encodes the table of weights, builds the Merkle tree over it,
   samples the OOD answers, and derives the commitment ID; not the proofs in the key file, not the
   copies, nothing else of the program.
2. The illustrative system `theCpp`: a system that keeps the Lean verifier's verifier and extractor
   and has that committer in the constant committer's place.
3. "The tie": at the full size, where the plan's leaf salts have 40 bytes (`SaltAt`), at every hash
   function the committer's commitment ID equals the value of a second illustrative committer, which
   the library has as mathematics that cannot be run ("the written committer") and about which it
   has a theorem.

**Read first:** `Twin.lean` (the committer), `Cpp/Defs.lean` (the statements), `Cpp/TheTie.lean`
(the main theorems and what each rests on).

**Words.** More in `lean/GLOSSARY.md` and under "Words" in the head of `Cpp/Defs.lean`.

- *Correctness of extraction* (`ExtractsCommittedWeights`): from an honest commitment and that run's
  hash queries the index extractor gives, but for a stated error, the weights that were committed
  to.
- *Binding of the commitment*, here always in the opening form (`BindsWith`; both in
  `lean/VerifiableInference/MoreStatements.lean`): but for a stated error, nobody opens a
  commitment, by naming weights and randomness from which the committer gives it, to weights that
  the extractor does not give. It is not what the theorem on soundness states: that has the form of
  index-binding knowledge soundness and speaks of every commitment, whoever made it.
- *Weights*: the index. *Commitment ID*: the index verification key: in these theorems the 256 bits
  alone; the key file comes with every proof (`lean/TERMS.md`, table 1). *Coins*: the committer's
  random values: *tails and pads*, the two kinds that are encoded with a row, and each leaf's salt.
  *OOD answers*: evaluations of each row of the table at a point sampled from the root
  (out-of-domain), published with the root. *The frame of the strings*: the fixed fields that the
  format lays around a hashed string. *Free*: a free variable; the statement holds for every choice
  of it. *Commit field*: the place of `theCpp` where the committer stands. `G9bits`: a goal of
  `lean/Ladder/Bits.lean` (`lean/TERMS.md`, table 2).

## What is proved

> Of an illustrative system, which keeps the Lean verifier's verifier and extractor and has an
> illustrative committer (it models one part of `cp_commit`; no theorem ties them), Lean proves, at
> that system's own extractor, correctness of extraction and binding of the commitment (in the
> opening form), at files in scope where the tests on the public files pass. It proves soundness
> after an honest commitment: after that committer has committed to fixed weights w, no prover makes
> the Lean verifier accept an output that does not meet the files' policy at w, but for the stated
> error, on average over honest commitments. That is no test of the committer. These theorems do not
> say that the tests pass or anything is accepted.

What goes with this statement: [LIMITS.md](../../LIMITS.md), L61. All probability is that of other
files' theorems, in part over coding theory that AI systems adapted from third-party Lean. Three
further limits:

- **Exact match.** The library's own form (`soundAtCommitted_exact`) lets an accepted empty output
  pass: the empty output is the model's at all weights; `soundAtCommitted_exact_nonempty` bars it.
- **What the tie cannot see.** The encoder's symbol function, the frame of the strings and the
  weights' digits are one Lean text on both sides of its equation, so an error in them shows on
  neither side; only the first two are reached from outside, by the evaluations at a small shape.
- **The goals.** Correctness of extraction and binding of the commitment (in the opening form) are
  not the goal `G9bits` (`lean/Ladder/Bits.lean`): they do not reach all files in scope; binding in
  that form is proved in one of the six theorems, `soundAndBinding`, for `compile`'s own committer
  ([LIMITS.md](../../LIMITS.md), L93), not for this folder's illustrative committer; and soundness
  after an honest commitment is none of the goals.

### The premises, and which statement stands under which

Z: three public files. *Read* (`readFiles Z = .ok pp`): the library's reader accepts the parameter
file and the scale file, and returns pp. *In scope* (`InScope`, `lean/Ladder.lean`): they are read;
the layout file is that of the library's written copy of the stored full-size example; the parameter
file is that copy's but for eight numbers, written as the reader read them; and one of the eight,
theta, is at least 2^8. So only the scale file and eight numbers may vary. `protocolDataWellFormed`:
the tests on the public files; where they fail, `verify` rejects all. Free in every statement that
has them: the prover, and the generator g from a secret seed to the coins (a function: it is handed
two answers of the hash function and may ask it nothing). In every theorem on the committer the hash
function is a variable, a random oracle where a probability stands; the format's own hash enters in
tests, in the definitions that they run, and in `Eval/` alone (its second hash function apart, which
is one fixed, named function in every statement at `theCpp`).

- `tieAt`, `tieKeyAt` (the tie; the key's bytes): `SaltAt Z`. `extractsCommitted`, `bindsAt`: in
  scope, read, the tests on the public files pass. In `bindsAt` the opener may name a seed or any
  coins. These reach everything that the written committer can read except salts that do not begin
  with the files' digest (`reach`); `both` adds those (stated from the tie at Z).
  `noTwoOpenings_live` (`Cpp/NoTwoOpeningsAtLive.lean`): in scope, read, the tests on the public
  files pass; no two openings there, at twice `bindsAt`'s error.
- `soundAtCommitted`, `soundAtCommitted_own` (the experiment written out), `soundAtCommitted_at` (at
  each single randomness; of a further illustrative system for each randomness: `theCpp` with a
  sampler that always gives that randomness, `Cpp/SoundAtCommittedAt.lean`): in scope, read.
  `soundAtCommitted_exact`, `soundAtCommitted_exact_nonempty`: and the files' policy is exact match.
  `soundAtCommitted_zFull`, `soundAtCommitted_zGap`, `soundAtCommitted_exact_zFull`: no premise.
- `SaltAt` (the tie's one premise) holds, in scope, exactly where the planner returns a plan; no
  theorem outside `AtFullSide/` shows it at any files; that the tests on the public files pass gives
  it.
- `g8bits_cpp` (soundness under the files' policy carries over) by itself bars nothing against a
  committer who commits to weights under which every output meets the policy: it means something
  only together with correctness of extraction at the same extractor, and with knowing who made the
  commitment, which no theorem says.
- `g9bits_cpp` takes "the planner returns at all files in scope" as a premise, which is not proved;
  if it were false, the goal would be false at `theCpp` (argued, no theorem).
- A control: that committer run at a table of zeros, which does not read the weights, fails the tie,
  correctness of extraction, binding of the commitment (in the opening form) and no two openings
  (`blindTwin_fails`); it is not shown to fail soundness after an honest commitment.
- With the committer left free the tie is met by the written committer itself, so all content lies
  in which text stands there (`Cpp/Vapid.lean`).

## What is run, not proved

- **At each build**, by `#guard` lines, at toy sizes and at the small stored example: the committer
  against the format's known answers and against copies with one step changed; the plan's salt
  length (40) at `storedPublicFiles` and `zGap` (the library's written copies of the two stored sets
  of public files: [LIMITS.md](../../LIMITS.md), L69).
- **Once, outside the build:** the tests on the public files (`protocolDataWellFormed`) at these two
  copies (they pass; the side library has both as theorems: `AtFullSide.Top.theLive_zFull`,
  `AtFullSide.Top.theLive_zGap`), and at `storedPublicFiles` with an empty scale file (they fail)
  (told in the head of `Cpp/SaltAtNamed.lean`). Too heavy for the build, so no file here repeats it.
- **Twice, against the program:** two runs of `cp_commit`, by builds that nothing ties to this
  repository's sources, at the small stored example's three public files, on synthetic weights,
  under one and the same public seed (so they hide nothing): one by a production build, one by a
  build made for the tests, on plain synthetic weights, which the production build rejects at these
  files. At each run a faster text of the committer, proved equal to it, with two further Lean
  texts, for the table and for the coins, of which no theorem on the committer speaks, gave all
  8,388,608 leaf digests, the root, the 256 OOD answers and the commitment ID of the run. Six
  negative tests at each run, each a small change, came as foretold. A reader cannot repeat this:
  the Lean texts that make the two runs' tables and coins, and the programs that were run, are not
  in this library. No run at this seed can test one rule of the text that makes the first run's
  table: its rule for values halfway between two neighbours, in the first rounding (as binary32
  rounds), never reaches an integer at this seed.
- **From such a run to `twinID`:** that a program with its printed output computes the chain of the
  committer's steps is a reading: no theorem speaks of input and output; and a run is compiled code,
  which rests on Lean's compiler and runtime too. From that chain to the value of `twinID` at one
  named hash function, at the shape and table that ran: a theorem (`runIsTerm`,
  `Eval/RunIsTerm.lean`). What stands in the commit field is the same Lean definition, at another
  shape and table: there nothing has been run; and at the shape that ran this library has no tie, no
  binding of the commitment and no correctness of extraction.
- **By no run in Lean:** the table at weights as the theorems take them (`entryOf`: the library's
  own placing of a model's digits, compared with the programs' nowhere); any other size, so not the
  full size, where the theorems stand and nothing can be run; any other seed.
- **Nowhere:** a block of coins that needs a second try; a salt's value at or above the prime before
  its reduction; other tails, pads and salts (both runs bear the same); the key file's proofs and
  its copies; weights of a real model; a third run; nor anything else not named in this section.

An agreement of values at two runs is no theorem that the program computes what the Lean committer
computes. It says nothing on correctness of extraction, on a binding of the commitment, on soundness
or on index privacy, nor on anything else that a theorem could state.
