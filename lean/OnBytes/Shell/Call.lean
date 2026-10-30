-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/Call.lean: from the arguments of a call to its ending.

Main definitions: `usage`, `needAll`, `judgeFiles`, `Kind`, `kindOf`, `Kind.run`, `call`. What is
not claimed: no theorem is stated here. The theorems are in the files OnBytes/Shell/At*.lean.
-/
import OnBytes.Shell.Ask
import OnBytes.Shell.Toys
import OnBytes.Shell.Whole

namespace OnBytes.Shell

/-- The usage text, for standard error: the forms of a call, then the last lines of standard output
with their exit codes (`Line.text`, OnBytes/Shell/Lines.lean; `Ending.status`,
OnBytes/Shell/Ask.lean). The last five forms are calls on the files of small test protocols. Such a
call can pass with fewer than 128 bits, if the caller names fewer with `-bits`; its exit code is
then 3. `verify -key` and `verify -leaf` that find no fault also end with 3, but with 14 below 128
bits, and with 14 under `-no-proof-of-work` if a round needs its work. -/
def usage : String :=
  "usage: verify-on-bytes verify <config folder> <ivk folder> <request file> <y file>\n" ++
  "           <proof file> -id <64 hex digits> [-bits N] [-no-proof-of-work] [-next-token]\n" ++
  "           [-policy kind,C,theta,cap,s,sh] [-show-stages] [-q] [-j N]\n" ++
  "       verify-on-bytes verify -key <config folder> <key file> [-id <64 hex digits>]\n" ++
  "           [-bits N] [-no-proof-of-work] [-show-stages] [-q] [-j N]\n" ++
  "       verify-on-bytes verify -leaf <config folder> <key file> <entry file>\n" ++
  "           [-id <64 hex digits>] [-bits N] [-no-proof-of-work] [-show-stages] [-q] [-j N]\n" ++
  "       verify-on-bytes plan <config folder> [-bits N]\n" ++
  "       verify-on-bytes product <public file> <proof file> [-bits N]\n" ++
  "       verify-on-bytes links <public file> <proof file> [-bits N]\n" ++
  "       verify-on-bytes key <public file 1> <public file 2> <key file> [-bits N]\n" ++
  "       verify-on-bytes entry <public file 1> <public file 2> <key file> <entry file>\n" ++
  "           [-bits N]\n" ++
  "       verify-on-bytes toy-proof <public file 1> <public file 2> <key or entry file>\n" ++
  "           <number of the stored copy> <request file> <reply file> <claims file>\n" ++
  "           <proof file> [-bits N]\n" ++
  "product, links, key, entry and toy-proof are test calls: they check files of small test\n" ++
  "protocols and are no verification of a model's files.\n" ++
  "-no-proof-of-work: for a caller who wants the checks alone, without proof of work, to carry\n" ++
  "the target that the parameter file (policy.txt) sets. if a round meets that target only\n" ++
  "with its proof of work counted, every check is made and the call ends at best with\n" ++
  "NOT-A-VERIFICATION; a line that begins with 'the call:' says how many such rounds there\n" ++
  "are. if no round needs its work, the option changes nothing.\n" ++
  "the last line of standard output, and the exit code:\n" ++
  "  YES                               0  passed\n" ++
  "  WITHIN LIMITS: ...                0  passed under the policy shown, named with -policy\n" ++
  "  NOT-A-VERIFICATION               14  no check failed, but the call does not qualify\n" ++
  "  NO: <name>                        1  a check failed\n" ++
  "  NOT CHECKED: <name>               5  nothing was verified\n" ++
  "  PART PASSED: key (or leaf)        3  -key or -leaf found no fault; no verification\n" ++
  "  TEST FILES PASSED                 3  a test call found no fault; no verification\n" ++
  "  PLAN ONLY: no proof was checked   4  a plan call\n" ++
  "  input-unreadable-..., or none     2  no result: an unreadable file or a bad command line\n" ++
  "  not to be relied on              15  a line was not written: take the call as not made\n" ++
  "a whole call (verify without -key or -leaf) qualifies only if it names the ID with -id,\n" ++
  "asks for no fewer than 128 bits and meets the standard parameter form\n" ++
  "(lean/OnBytes/GLOSSARY.md). any other outcome, also the exit code 1 without a last line\n" ++
  "NO: <name>, is a broken run and no result.\n" ++
  "research code: no security level is claimed; what is proved about it and what is not:\n" ++
  "lean/OnBytes/README.md"

/-- Reads the files at the paths in their order and goes on with `got` followed by the files' bytes
in the same order. L holds the lists by which names are printed. -/
def needAll (L : Lists) :
    List String → List ByteArray → (List ByteArray → Ask Ending) → Ask Ending
  | [], got, next => next got
  | p :: ps, got, next => need L p fun b => needAll L ps (got ++ [b]) next

/-- The note on the bits, if fewer than the threshold `Model.bar` (OnBytes/Model/Frame.lean), 128,
are asked. -/
def bitsNote (bits : Nat) : List Note := if bits < Model.bar then [.bits bits] else []

/-- Takes `-bits N` off the end of the arguments. Returns the arguments before it and N, or all
arguments and 128 if they do not end in `-bits N`. Returns `none` if N is not spelled as `decimal`
asks or is above 1000000. -/
def cutBits (args : List String) : Option (List String × Nat) :=
  match args.reverse with
  | x :: "-bits" :: rest => (decimal 1000000 x).map fun v => (rest.reverse, v)
  | _ => some (args, Model.bar)

/-- Reads the files at the paths, prints the notes, and ends the call with the verdict that v gives
on the files' bytes, and with what w says on proof of work. If v returns `none`, because it expects
another number of files, the call ends in a fault; `toyKind` gives each v its number of paths. -/
def judgeFiles (L : Lists) (paths : List String) (notes : List Note)
    (v : List ByteArray → Option Verdict)
    (w : List ByteArray → Work) : Ask Ending :=
  needAll L paths [] fun files =>
    match v files with
    | some x => sayAll (notes.map fun n => (Line.note n).text L) (finishTest L (w files) x)
    | none => faultWith "verify-on-bytes: internal fault"

/-- What the arguments of a call ask for. -/
inductive Kind where
  /-- a call on the files of a test protocol: their paths, the notes that it prints before its last
  line, the verdict on the files' bytes, and what the accounting says on proof of work -/
  | toy (paths : List String) (notes : List Note) (v : List ByteArray → Option Verdict)
    (w : List ByteArray → Work)
  /-- a whole call: its five paths and its options -/
  | whole (config ivk request y proof : String) (a : Asked)
  /-- a call on a key file alone -/
  | keyPart (config key : String) (a : Asked)
  /-- a call on an entry file alone -/
  | leafPart (config key entry : String) (a : Asked)
  /-- a planning call: the configuration folder and the requested bits -/
  | plan (config : String) (bits : Nat)
  /-- a bad command line: the words for standard error -/
  | bad (words : String)

/-- Reads the arguments of a call on the files of a test protocol, after `-bits N` has been taken
off their end. -/
def toyKind (bits : Nat) : List String → Kind
  | ["product", p, f] => .toy [p, f] (bitsNote bits)
    (fun
      | [pb, fb] => some (product bits pb fb)
      | _ => none)
    (fun l => productWork bits (l.headD .empty))
  | ["links", p, f] => .toy [p, f] (bitsNote bits)
    (fun
      | [pb, fb] => some (links bits pb fb)
      | _ => none)
    (fun l => linksWork bits (l.headD .empty))
  | ["key", p1, p2, f] => .toy [p1, p2, f] (bitsNote bits)
    (fun
      | [p1b, p2b, fb] => some (key bits p1b p2b fb)
      | _ => none)
    (fun l => keyWork bits (l.headD .empty) (l.getD 1 .empty))
  | ["entry", p1, p2, k, f] => .toy [p1, p2, k, f] (bitsNote bits ++ [.keyFile])
    (fun
      | [p1b, p2b, kb, fb] => some (entry bits p1b p2b kb fb)
      | _ => none)
    (fun l => entryWork bits (l.headD .empty) (l.getD 1 .empty))
  | ["toy-proof", p1, p2, t, number, rq, rp, cl, f] =>
    .toy [p1, p2, t, rq, rp, cl, f] (bitsNote bits ++ [.tableFile])
    (fun
      | [p1b, p2b, tb, rqb, rpb, clb, fb] =>
        some (toyProof bits p1b p2b tb number rqb rpb clb fb)
      | _ => none)
    (fun l => toyProofWork bits (l.headD .empty) (l.getD 1 .empty))
  | _ => .bad usage

/-- The words for standard error when the options are refused. -/
def badWords : BadOptions → String
  | .usage => usage
  | .idForm => "-id requires 64 hex digits"
  | .policyForm => "-policy requires kind,C,theta,cap,s,sh"

/-- Reads the options of a call on one file alone. The options `-next-token` and `-policy` belong to
a whole call: with one of them the command line is bad, as in cp_verify (cpMain,
verifier/src/cp_verify.cpp). -/
def partOptions (options : List String) : Except String Asked :=
  match readOptions options {} with
  | .error e => .error (badWords e)
  | .ok a => if a.options.nextToken || a.options.policy.isSome then .error usage else .ok a

/-- Reads the arguments of a call. -/
def kindOf : List String → Kind
  | "verify" :: "-key" :: config :: key :: options =>
    match partOptions options with
    | .error w => .bad w
    | .ok a => .keyPart config key a
  | "verify" :: "-leaf" :: config :: key :: entry :: options =>
    match partOptions options with
    | .error w => .bad w
    | .ok a => .leafPart config key entry a
  | "verify" :: config :: ivk :: request :: y :: proof :: options =>
    match readOptions options {} with
    | .error e => .bad (badWords e)
    | .ok a => .whole config ivk request y proof a
  | ["plan", config] => .plan config Model.bar
  | ["plan", config, "-bits", x] =>
    match decimal 1000000 x with
    | some v => .plan config v
    | none => .bad usage
  | args =>
    match cutBits args with
    | some (front, bits) => toyKind bits front
    | none => .bad usage

/-- What a call of a kind reads, prints and returns. C holds the checks on a model's files. -/
def Kind.run (C : Checks) : Kind → Ask Ending
  | .toy paths notes v w => judgeFiles C.lists paths notes v w
  | .whole config ivk request y proof a => Shell.whole C config ivk request y proof a
  | .keyPart config key a => Shell.keyPart C config key a
  | .leafPart config key entry a => Shell.leafPart C config key entry a
  | .plan config bits => planCall C config bits
  | .bad words => faultWith words

/-- The whole program: what a call with these arguments reads, prints and returns. -/
def call (C : Checks) (args : List String) : Ask Ending := (kindOf args).run C

end OnBytes.Shell
