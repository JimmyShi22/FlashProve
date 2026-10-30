-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ask/SharedChain.lean: an asking file. No soundness: a test. It is no part of the library: nothing
imports it, and `lake build` does not take it. It is the entry point of the command in
Johnson/Desc/Shared/Main.lean, which tries the decision on a proof file's shared hash chain
(`Desc.Shared.descSharedZ`, Johnson/Desc/Shared/Par.lean) on a stored proof and on 36 changed copies
of its input. A proof file holds three hash chains; this is about the middle one alone.

Reads: seven files under the folder that is its first argument: config/policy.txt,
  config/layout.txt, config/KL.bin, ivk/leaf/0.bin, example.req, example.y and example.proof.
  Without an argument the folder is examples/accepted-proof as seen from the directory in which the
  command is typed, so from lean/ the folder must be named. It writes nothing.

Command: from lean/, behind a build, with libvob.so made as Ask/README.md says ("The faster way"):
    LEAN_ABORT_ON_PANIC=1 lake env lean --load-dynlib=./libvob.so --tstack=4000000 --run \
      Ask/SharedChain.lean ../examples/accepted-proof
  The like with ../examples/full-size in the folder's place, and with --plant behind the folder.
  Without --load-dynlib=./libvob.so it is the same command, and Lean interprets all the code.
  With --plant the expected place of the first changed input is set wrong on purpose, to show that
  the command is able to fail: the exit status must then be 1.

Takes: in Lean's interpreter alone: no figure is given. With the library's compiled code loaded, on
  one machine: about 7 seconds and 0.8 GB at examples/accepted-proof, about 41 seconds and 2.9 GB at
  examples/full-size. These were measured with the entry point in another file, started from an
  evaluation in Lean and not by the command line above.

Its print means: first lines that are no tests: what the command is, its arguments, the folder, the
  seven files' sizes, and the chain's numbers of rounds and of opened columns. Then a line for the
  stored proof and a line for each changed input: the label; YES or no, the decision's answer;
  "stopped at:" with the place where the run stopped ("-": nowhere); and "as expected", or "NOT AS
  EXPECTED: EXPECTED" with the place that Main.lean expects. The good answer is YES for the stored
  proof and no for every changed input. Then what the places' names mean, a line "Result" with three
  counts, and a last line with the exit status: 0 if every line is as expected; 1 if not; 2 if
  nothing was tried, because the arguments were not understood, a file could not be read, or the
  input could not be made from the files.

It does not mean: a YES is no verification of the proof file. It says that this one chain's checks,
  as the files under Johnson/Desc/Shared/ write them, pass on the view that the parser in the text
  of verify-on-bytes has made of the file. The other two chains, the key file, the entry file,
  every hash, every proof of work and every opening of a tree are outside that decision, and no
  theorem is proved about it. A no at a changed input says that some check of the named step refuses
  that input: not which check, and nothing on false proofs at large. The changes are made in memory
  after the files have been read, and some change drawn values, which a prover cannot choose. Much
  of what runs is code of the text of verify-on-bytes. The heads of Main.lean and Fold.lean under
  Johnson/Desc/Shared/ tell the rest.

What this file prints, and what this comment says of it, are not machine-checked.
-/
import Johnson.Desc.Shared.Main

/-- The command's entry point. -/
def main (args : List String) : IO UInt32 := Desc.Drive.entry args
