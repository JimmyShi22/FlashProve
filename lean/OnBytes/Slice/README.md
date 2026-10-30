# OnBytes/Slice

Terms: [TERMS.md](../../TERMS.md).

Theorems on one protocol of `verify-on-bytes`, the Lean text below `OnBytes.Main`: a hand
translation of `cp_verify` into Lean, from which this repository builds no stand-alone program; one
test (`tools/accepts/`) compiles it and has Lean load the compiled code while it evaluates files of
`lean/Ask/`. It is not `verify`, the Lean verifier that is proved sound in the random-oracle model,
at exact match ([lean/THEOREM.md](../../THEOREM.md)). Below, "the program" is a stand-alone program
built from that text; this repository builds none. No soundness theorem reaches a call that checks a
real proof, and no theorem bounds the chance that the program accepts a false file. The program
follows `cp_verify`'s source text, so the two programs are not independent. Below, `verify`, `verify
-key` and `verify -leaf` are commands of `verify-on-bytes`.

## What the folder is about

One protocol of the C++ programs' file format, the link between the first table and a copy, with
out-of-domain (OOD) answers (in the Lean files: a record). The files define its rounds and hold the
link at radii below the Johnson radius; these take the library's statement on Reed-Solomon codes
(`Cb.BCHKS46At`) as a hypothesis, which the library proves elsewhere
(`Cb/Bridge/CodeListRSProved.lean`), and have Rec, Seed, Joh or Bchks in their names; bounds for
checkers that these files define, which ask one random oracle, and a join of three such checkers
(`OneWorld*.lean`, `Part*.lean`, `Join*.lean`); and the written rounds of a key file's three chains
(`Key*.lean`). These checkers are not the program, which does not call them, and no probability is
stated there of the program or of BLAKE2b. Each file's head tells what it holds.

## What no theorem here says

None of these theorems is the theorem of THEOREM.md, none bounds the chance that the program's own
check accepts a false file, and none reaches a call that checks a real proof. Nothing on the C++
verifier. The soundness of the step by which an array of one link of a request's proof is read in a
later link is stated by no theorem of this folder. The general statements are written out for a
chain of exactly three stages (ChainSem.lean, ChainCloses.lean, BlkChain.lean), the last without row
variables. So nothing is said by these general statements of a chain with another number of stages.

## Where the first table does not decode, and the key

The relation also holds where the first table does not decode. That disjunct is harmless only once a
test on the key is proved sound for this same decoder at a radius of at most the one within which a
table decodes. Here the key is not checked. So as far as these theorems go, whoever publishes a
first table that is far from every table of code words can have any copy accepted.

## The vocabulary

[GLOSSARY.md](../../GLOSSARY.md) has the words of the whole library, the Lean folders beside
OnBytes/ (a path such as Iop/Rbr.lean is the library's).

- A table (the first table, or a copy): meant to be a table of code words, one row a code word,
  committed to by the root of a hash tree over its columns. It decodes if it is within a radius,
  counted in columns, of a table of code words, to that table's messages. The copy: a second such
  table, meant to hold the same rows' messages under fresh random tails.
- The link: the protocol that is meant to show of two roots that the copy holds the same rows'
  messages. The language (`Sz.Lang`, LinkAt.lean): the first table does not decode, or the copy
  decodes to the same rows' messages. A copy's file (in Lean names: entry; TERMS.md: a further
  encoding of the index) holds the copy's root and a non-interactive proof of the link. The key is
  the file that holds the first table's root (TERMS.md: a part of the proof, not the index
  verification key).
- The written link, or written protocol (`written`, LinkSound.lean): the link as an interactive
  protocol in the types of the format. A verifier message, or challenge value, is a round's hash
  blocks and test bits, not a tuple of drawn values. A round that asks for b bits of work has b test
  bits, and the verifier refuses unless all of them are 0 (Iop/Grind.lean). The sampler's number w
  bounds how many strings of hash blocks give one tuple of drawn values.
- A decision: a verifier's last step, from what was read (a view) to yes or no. A description
  (`XD`): the list of one chain's rounds and openings. The compiled verifier of one IOP
  (`verifyOneProtocol`): what the library's compiler (the BCS transformation; Compile/Batch/), not
  Lean's, makes of the written link. A Link string is a non-interactive proof in its types. An
  interface (`BatchProtocol`) holds three interactive protocols, Test, Link and Batch; a wiring
  (`QueryLayout`) says how their messages become leaves and hash inputs.
- Typed oracles: one independent random oracle for each kind of query (leaf, node, a round's
  challenge and so on). The experiment: a maker, any algorithm with access to them, puts out two
  roots and a Link string, and that compiled verifier runs under the same oracles. The maker wins if
  it accepts and the two strings read off the joint trace are outside the language.
- A trace: the list of the queries to the oracles with their answers, in order. The string read off
  a trace under a root: the leaves that the trace's tree queries determine under that root, and a
  fixed filling elsewhere.
- In one world: maker and verifier run under the same random oracles, so that the bound is a
  probability. In two worlds: a set of traces has a bound under random oracles, and a yes is a yes
  under BLAKE2b.
- Has lost, error count, share, round-by-round sound (`Doomed`, Iop/Rbr.lean;
  `InteractiveOracleProof.Sound`, Iop/InteractiveOracleProof.lean). The definition goes from the end
  backward, for a list of error counts, one for each round. After the last round the prover has lost
  if the verifier refuses the transcript. Before a round it has lost if, whatever it sends, at most
  the round's count of the round's verifier messages lead to a position in which it has not lost. A
  count divided by the number of its round's verifier messages is its share. The protocol is
  round-by-round sound for a language with these counts if, for every statement outside the
  language, the prover has lost before the first round. With counts as large as the rounds' numbers
  of verifier messages this holds of every protocol: all content is in the sizes of the counts. It
  bounds each round by itself. The one bound on a probability that these theorems draw from it is
  the bound on the experiment; none is drawn for a cheating prover of the interactive protocol, and
  none for a false file.

## More terms

- "view" (`Fmt.View`, Fmt/View.lean). What a decision is given: the rounds with their sent and drawn
  values, and a list of opened columns, each entry a key, a position and a column.
- "stage" (`Sg`, Stage.lean). One stage of the proximity test: main code, mask code (of the mask
  rows, further rows of a tree), numbers of row variables and of drawn positions. A mask code that
  is shorter than the main code is taken as repeated to the tree's length (`ldRep`, LinkAt.lean):
  each leaf holds mask symbols of its own, and nothing makes two leaves agree. A longer one is not
  covered.
- "group, kept member" (`Group`, OnBytes/Iop/Ground.lean). A group is a list of oracle messages that
  one proximity test covers. A kept member's main rows are read and tested with the group and not
  folded with it. The statements on a fold say nothing of the forms on kept members; the ties
  (`GroupTie`, `FoldedOk`) and the statements on a code switch ask that a row has none.
- "small test configuration": the sizes of a toy chain of an entry (`toySg1`, `toySg2`, `toySg3`,
  OnBytes/Slice/ToySg.lean). The library's toy files that the C++ test tool
  (blocks/frame/handover_files.cpp) writes are in OnBytes/Entry/RecordToyFiles.lean: their sizes are
  not these.

## TopAny.lean

From "the compiled verifier of one IOP accepts" to a statement on traces, for every description D of
a chain that opens the first table and a copy, and every decision dec. The one hypothesis: the
protocol made from D and dec is round-by-round sound for a language Lg of pairs of strings, a free
variable, with error counts εL (`SoundLAny D dec Lg e`: with counts that are each at most e as a
share). Two conditions on the description can be evaluated (`within_work`, `within_okx`).

Main theorems: `psofX_up`, `okgAny`, `verifyBS_ann`, `embPX_eq`, `vls_any` (over
`Run.Twin.allLo_eq`): the compiled verifier of one slot is the compiled Link verifier of the whole
wiring. `experiment_any`: a bound on the experiment. `top_any`, `compiled_top`, `session_top`,
`check_top`: the statement on traces, from a yes of the library's run function, of the compiled
verifier of one slot (`CompiledAcceptsX`), of the decision on a chain that a session of the program
has read, and of `Entry.check`. `badAny_rare`: an algorithm with t queries to the typed random
oracles reaches the named set with probability at most t e + 2 t^2 / 2^256, if every count is at
most e as a share; t counts the makers' queries and the verifier's. `badAny_mono`, `badAny_stable`,
`badAny_run`: further lemmas on the set.

**The named set of bad traces.** The four statements on traces speak of one, `badAny D dec εL`. A
trace is bad if it shows one of three events (`linkBad`, LinkClause.lean):

- a clash in a hash tree (the library's `EM`): the answer of a new query to a leaf or node oracle,
  of trees over messages or of request trees, occurs at an entry before it in the list: as such an
  answer, in the input of a node query, as a root field of a challenge query or of a query to the
  oracle g, or as an announced root;
- a clash in a chain (the library's `EF`): the link value in the answer of a new challenge query, or
  the answer of a new query to g, occurs at an entry before it: as such a value, as a chain field of
  such a query, or as the input of a query to the leaf oracle of request trees;
- a lucky step (the library's `StepEvent` of `stepS`): the answer of a new challenge query that is
  rooted in the list before it turns the round-by-round state of its transcript, with the error
  counts εL, from lost to not lost.

A query is new if the same query with the same answer does not stand before it in the list. The link
value of a challenge query is the part of its answer that the next query of the hash chain takes in;
a query's chain fields are its fields for such values; the oracle g and the request trees belong to
the library's Batch protocol, which has no rounds here. For every trace that holds the verifier's
queries and answers and shows none of the three, Lg holds of the two strings that are read off the
trace under the two roots. The typed string is made from what `readIn` reads from some byte offset
of the file, which is not shown to be the one that `Entry.check` used. Whether a given list with
BLAKE2b's answers shows one of the three events no theorem says; for the lucky step no procedure is
given.

**Which trace: the reader's duty.** The hypothesis on the trace is membership: the verifier's
queries with their answers are in it, in whatever order, among whatever other entries, which need
not carry BLAKE2b's answers. The statement says something on the two tables only of a trace that
also holds, in their order and before the verifier's queries, the queries by which the two trees
were made. For a language of this kind, off a trace that determines few non-zero columns under each
root, such as the verifier's queries alone, both strings decode to the all-zero messages, and the
conclusion holds whatever the file (read off the definitions: what a trace does not determine is
read as zero columns; no theorem states it). By the same reading (not machine-checked) the
verifier's own queries alone, in their own order, seem to form a bad trace as soon as one opening is
checked: the roots occur in the chain's queries, which come first, and a tree query that is answered
by a root is then a clash in a hash tree. Whoever runs the program does not hold the maker's list.

**The chief limit of the statements on traces.** That some trace with an accepted run's queries and
the trees' queries shows none of the three events is not proved. The two clashes hang on BLAKE2b's
answers in that list. The lucky step hangs on completeness of the interactive protocol, round by
round (not TERMS.md's property of an argument system): in each round more verifier messages than the
round's count must lead on to a position that is not lost, which a test on one honest file does not
touch. So, as far as theorems and tests go, it is not excluded that every such trace is bad; then
what the statements say of traces is vacuous.

**The size of the counts.** Nothing is asked in the four statements on the size of the counts. If
one round's count is as large as that round's set of challenge values, the hypothesis holds for
every language, the empty one too (by the definition of round-by-round soundness; no theorem here
states it). By `badAny_run` the set then holds every trace with an accepted run's queries: what the
statement says of traces is vacuous. It says something only together with `badAny_rare` at the same
counts and a small e.

### Not claimed

- That the one hypothesis holds for any language of interest. Every file of this library that names
  it takes it as a hypothesis or hands it on from one description to another: none shows it of a
  description (by a search of the Lean files for the name and for its unfolded form). All content
  lies in a named Lg, named counts and a computed e.
- That any trace with an accepted run's queries lies outside the named set. No theorem gives one.
- No bound on the probability that a false file is accepted: the bound on the named set speaks of
  random typed oracles, the verifier's yes of BLAKE2b. Between them stand, among other things: the
  assumption that the hash behaves like a random oracle; laws of the spelling of typed queries as
  hash calls (`Run.PQ.famX`), which are not proved; and the step from a family of typed oracles to
  one oracle on strings.
- That one set serves all copies' files. In `check_top` description and decision are made from the
  parameters and the two tables' names, and the copy's name is in the file. So the bound on the set
  is for a name that is fixed beforehand; nothing is said of a maker who chooses that name after
  queries to the oracles.
- That the typed first query reads the roots. In `compiled_top` and `session_top` the function that
  gives the statement's bytes from the two roots is a free variable; a constant function meets the
  hypothesis on it too. `check_top` has the program's own function (`entryStatement`).
- That the two roots are the right ones: no key is checked. What the interface `D.L dec` has for an
  index, an encoder, a decoder and honest parties are trivial ones that mean nothing; the statements
  speak of the two strings themselves, not of what they decode to.
