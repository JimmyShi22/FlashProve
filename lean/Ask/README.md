# lean/Ask: running compiled verifiers on the stored example

Terms: [TERMS.md](../TERMS.md).

**No soundness: a test. A yes from these runs is not a verification.** The Lean files in this
directory are not part of the library: `lake build` does not compile them, and no file imports them.
Each is run by `lake env lean`: it reads files from disk, runs code of the library on them and
prints what it finds. The comment at the top of each file says what it reads, its command, how long
it takes, what its output means and what it does not mean. This page holds what these comments
share. To run the executable form of `verify`, the Lean verifier (not the C++ verifier that users
run by default) that is proved sound in the random-oracle model, at exact match:
[lean/THEOREM.md](../THEOREM.md), "The executable form, and how to run it".

| file | what it runs |
|---|---|
| `KeyCompiledSmall.lean` | the compiled verifier of the key file's IOP, on the example's key file |
| `ProofCompiledSmall.lean` | the compiled verifier of the proof file's IOP, on the example's proof file |
| `AllCompiledSmall.lean` | the checks of the example's key file, copy's file and proof file, joined to one ID |
| `…Controls.lean` (three files) | the run of the same name without `Controls`, and then six (`All`: five) more runs, each with one change |
| `KeyThirdChainSmall.lean`, `KeyThirdChainFull.lean` | a check of one hash chain of a key file; no parsed files; two of the changed copies still get a yes: known limits |
| `SharedChain.lean` | the decision on a proof file's shared hash chain (`Johnson/Desc/Shared/`), on a stored proof and 36 changed copies; no theorem is proved about it; without `--load-dynlib` one call at `examples/accepted-proof` took twelve and a half minutes and printed nothing until its end (measured once) |
| `Entry….lean` (four files) | checks of the copy's file: see each file's comment |

Below, "the six" means the first three rows with their controls. The stored example is
`examples/accepted-proof`, of a small synthetic model. On its key file, proof file, the copy's file,
chain, first table and copy: `lean/GLOSSARY.md`. Where this page and the comments say "third chain",
the glossary has "second". The comments call the copy's file the entry file; the pages under `docs/`
and `tools/`, the variable `ASK_PARSED_LEAF` and some printed lines call it a leaf file. Paths that
begin with `lean/`, `tools/`, `docs/` or `examples/` count from the repository's top, the others
from `lean/`.

What a yes does say: on this one example, the parsed forms of files that the prover program made
pass every test of the Lean definition that is run, with the format's BLAKE2b calls in the place of
its typed oracles. The controls show that some of these tests can say NO. Nothing follows on false
proofs.

## What is run

The compiled verifier of one IOP, `verifyOneProtocol`
(`OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean`; the comments here say "the compiled
verifier"), is the verifier of one slot of a batch that the form of this library's compiler under
`OnBytes/TypedOracleCompiler/` (its verifier's side alone) makes from the description of one
interactive protocol, here the key file's or the proof file's. It is not the whole verifier of the
scheme. The library has another definition of that name (`Compile/Batch/Verifier.lean`, in the
compiler's other form); no theorem carries a statement from one to the other. The verifier takes
typed values, not a file's bytes: `tools/parser/` turns the prover's files into *parsed files*,
which a short Lean reader loads. What the user claims (the commitment ID, the request, the reply,
the three public parameter files) is never taken from the parser's output.

## Before a run

1. Build the library ([CHECKING.md](../CHECKING.md), step 4).
2. Make the parsed files, from the repository's top directory
   ([tools/parser/README.md](../../tools/parser/README.md)):

```sh
W=$(mktemp -d) && echo "W=$W"
tools/parser/parse_files.sh examples/accepted-proof/config examples/accepted-proof/ivk \
  examples/accepted-proof/example.req examples/accepted-proof/example.proof \
  "${W:?first run the line with mktemp}/work"
```

   Its last line begins `PARSED AND READ BACK:` and names the directory in which `key.parsed.bin`,
   `leaf-0.parsed.bin` and `proof.parsed.bin` lie.
3. In `lean/`, in the shell in which you will type the command, with that directory's path:

```sh
export ASK_PARSED=/path/to/key.parsed.bin   # for the proof file's runs: proof.parsed.bin
# for AllCompiledSmall.lean and its controls, all three:
export ASK_PARSED_KEY=/path/to/key.parsed.bin
export ASK_PARSED_LEAF=/path/to/leaf-0.parsed.bin
export ASK_PARSED_PROOF=/path/to/proof.parsed.bin
```

4. Type the file's command, which stands in the file's comment at `Command:`, with the time and
   memory at `Takes:`. For `KeyCompiledSmall.lean`:

```sh
LEAN_ABORT_ON_PANIC=1 lake env lean -j1 --tstack=4000000 Ask/KeyCompiledSmall.lean
```

`--tstack=4000000` gives each of Lean's threads a stack of 4,000,000 KB, and `-j1` lets Lean use one
worker thread. Do not set a tight limit on the address space (`ulimit -v`): every thread reserves
its whole stack, and under a tight limit Lean cannot create its threads. `ASK_K` need not be set: an
answer of the hash chain has `ASK_K` + 2 blocks of 256 bits, and if the variable is not set, or is
not a number, the key file's and the proof file's runs take what the protocol's rounds need. If it
is set, the key file's run takes it as it is, and its test "plan 6" says NO if that is fewer than
the rounds need; the proof file's run takes the greater of the two. `AllCompiledSmall.lean` does not
read it.

## The faster way

By the plain command Lean interprets all the code. To let it call compiled code, make one shared
library out of the compiled modules of `verify-on-bytes`, the Lean text below `OnBytes.Main`: a hand
translation of `cp_verify` into Lean, from which this repository builds no stand-alone program. In
`lean/`:

```sh
lake query +OnBytes.Main:transImports > libvob.modules &&
  echo OnBytes.Main >> libvob.modules &&
  lake build $(sed 's/.*/+&:c.o.export/' libvob.modules) &&
  sed 's,\.,/,g; s,.*,.lake/build/ir/&.c.o.export,' libvob.modules > libvob.objects &&
( while read -r o; do c=${o%.o.export}; l=${c%.c}.olean
    [ "$o" -nt "$c" ] && [ "$o" -nt ".lake/build/lib/lean/${l#.lake/build/ir/}" ] ||
      { echo "older than its .c or its .olean: $o"; exit 1; }
  done < libvob.objects ) &&
  echo "checked $(wc -l < libvob.objects) objects: none is older than its .c or its .olean" &&
  lake env leanc -shared -o libvob.so $(cat libvob.objects)
```

The first two lines list `OnBytes.Main` and every module that it imports, directly or through others
(200 modules); the third has Lake compile each of them to a native object; the fourth writes these
objects' paths to `libvob.objects`. The block's last print says `checked 200 objects`. Another
number than 200 means that the list is not the one meant here. Then add `--load-dynlib=./libvob.so`
to the command, before `--tstack`. The loop refuses an object that is not newer than its own `.c`
file and its module's `.olean` file; then no library is made, and a `libvob.so` that lay there stays
and still loads: remove it, and use the plain command, or build in a fresh copy of the repository
and run the block there. The block writes `libvob.modules`, `libvob.objects` and `libvob.so` in
`lean/`, replacing files of these names without asking. Remake `libvob.so` whenever the library has
been rebuilt: one that was made before a source file changed still loads, the old code runs and no
error is shown.

## How to read the output

The lines of a run go to the error stream; the error that ends a failed run goes to standard output.
Each file's comment goes through its own lines. A test prints its name and `yes` or `NO`. `ANSWER`
is yes only if every test says yes, and a yes is followed by a line that begins `THIS YES IS NOT A
VERIFICATION`. Lean ends with status 0 only after a yes (for a file of controls: only if the
unchanged file or files get a yes and every changed one ends as expected).

## What a yes does not mean

Each file's comment lists its own limits. These hold of all six:

- The library does not prove the soundness of the key file's or the proof file's protocol that is
  run here, the small example's. The theorem on the compiled verifier `innerCompiledVerifier` (not
  `verify`; the files' comments write "verify()" for it), `innerCompiledVerifier_sound`, takes 16
  named hypotheses, and at the example's size `innerCompiledVerifierSoundFromDryRunAtSmallSize`
  takes four of them, unproved, and the statement on codes; among them, in the place of that
  soundness, `keySound` and `proofSound` (`Johnson/Top/InnerCompiledVerifier.lean`).
  `Johnson/Flat/TwoSizes.lean`'s own comment says that the example's protocol cannot meet
  `proofSound` at the claim written for that size; no theorem says so. If that comment is right,
  `innerCompiledVerifierSoundFromDryRunAtSmallSize` says nothing of this example. No theorem derives
  a bound on the error of the checks that are run here from `keySound` or `proofSound` alone, and no
  theorem links a yes to `innerCompiledVerifier`.
- The protocols' own checks (in the key file's run: the test "accept 9") are written by hand,
  following the C++ verifier. The compiler does not make them.
- The runs do not ask how many bits of security the public parameter files give: files with too few
  rounds and queries are not refused on that ground. That accounting is written in the text of
  `verify-on-bytes` (`OnBytes/Model/VerifyAccount.lean`); these runs do not call it.
- The runs are evaluations: Lean's kernel checks nothing of them, and the full check
  ([CHECKING.md](../CHECKING.md)) does not run them: it reads their text and counts them in its
  digest.
- Each is one run on one stored example, of a small synthetic model, and judges under exact match
  alone. At an example with another acceptance policy the answer is NO, whatever the files hold.
- The run values (the values with which a chain begins) of a file's first and third chains are taken
  as the parsed file gives them. The key file's and the proof file's checks draw the seeds of the
  table's out-of-domain sample themselves and do not ask the oracle queries that test them. Most of
  the decoder's tests (`Carrier.read`, `OnBytes/Maker/Carrier.lean`) are the decoder's alone: no
  theorem here says what they test.
- A yes is about the parsed file. Nothing here compares that file with the key file or the proof
  file itself: whatever the parser writes counts as sent by the prover.
- Where a printed line says that an oracle query "has a hash call in the format", what is tested is
  that the coding of oracle queries into hash calls (`okJ`, `OnBytes/Maker/Page/Guard.lean`) writes
  a string for that query (not for every block of an answer, and for two kinds of query not at all:
  each file's comment). That the call lies in the format's own domain, or that the query fits, is
  not tested.
- The format uses two hash functions: standard BLAKE2b, and a second, fixed hash function, built on
  BLAKE2b's compression function. Only the first is a parameter of the definitions that a run
  evaluates, and the theorems that a run cites hold at every function in its place; none speaks of
  BLAKE2b there, of an evaluation, or of the run with its print. The second is a fixed public
  function inside the definitions: it digests public data and the request file, and it is never an
  oracle. Which four lookup tables a parameter file names rests on it. Taking BLAKE2b as a random
  oracle while a second, fixed hash function on the same compression function stands beside it is an
  assumption on the two together; the format page (`docs/format/FORMAT.md`) counts the second as an
  assumption of its own, and no theorem of the library examines the pair.
- The key file's run and the proof file's run each check one file alone. The proof file's run alone
  prints: "The table under this proof is the prover's word: not tied to your commitment ID here."
  `AllCompiledSmall.lean` joins the checks to one commitment ID; its comment says what stays
  unjoined.
- These runs are not the verifier program that ships, `cp_verify`, which is written in C++, and they
  are no part of it, nor of the text of `verify-on-bytes`. Neither `cp_verify` nor that text is
  proved sound: no stand-alone verifier program is. What is proved sound, in the random-oracle model
  and at exact match, is the Lean definition `verify`. A command that runs it, `lean-verify`
  (`tools/lean-verify/`), is tied to that definition by a proof that its executable form computes
  the same verdict; no theorem says that its Lean reader cuts the user's three files as the format
  means; the proof reaches it as five files from a parser outside Lean, which is not verified: to
  the soundness theorem a wrong parsed file is the prover's choice: it can cost an honest proof its
  accept, and do no more than a prover can; the Lean compiler and runtime are trusted, not proved.
  In that sense no stand-alone verifier program is proved sound, and `cp_verify`, the C++ verifier
  that ships, is not `verify`. Nor are these runs the command `lean-verify`
  ([lean/THEOREM.md](../THEOREM.md), "The executable form, and how to run it").
