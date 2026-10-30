-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/ToyRuns.lean: the parameter bytes of the two small runs "product" and "links", from
each run's one public file.

A small run has one public file: some lines of text from which its setting, codes, shapes and plan
follow. A verifier takes the file's text and the proof and nothing else. This file reads such a
text, sizes and plans the run as the C++ programs do, and spells the parameter bytes of the run's
one chain.

The bits. A public file names the target at which its run is sized. What a caller asks of every
round is the caller's own number, 128 unless it says otherwise, and a file whose target is below it
is refused. Proof of work counts toward the target: a round holds if its error times 2^-work is at
most 2^-target, and the work before a draw of positions is the file's own line, up to 40 bits. So
under a file with target 128 and 40 bits of work the draws of positions alone reach 88 bits.
ToyRun.needsWork says whether a round misses the target unless its work counts, and ToyRun.work
how many bits the file asks, so that a caller can tell the two kinds of yes apart.

One spelling. The text is read loosely. Then the text that the run itself would write is formed
from what was read, and the two must be equal byte for byte. So a file has one spelling, and what
the loose reading does with other texts does not matter.

The run "product": three vectors a, b, c with a[i] b[i] = c[i], in one oracle message. The run
"links": a chain of links. Link l shows c_l = x_l b_l, entry by entry, and x_(l+1) = c_l. Each link
has two oracle messages, of which the second, with c_l, is kept for the next link.

Main definitions: ToyNumbers, readToyText, toyText, toySetting, groupFromBelow, ToyRun,
productRun, linksRun, ToyRun.params, ToyRun.needsWork, ToyRun.work.
C++ counterpart: toy_text, toy_read_text, toy_setting, toy_size and toy_from_text in
blocks/toy/product.h; segments_size and segments_from_text in blocks/toy/segments.h.

Not claimed here: no theorem is stated.
-/
import OnBytes.Plan.Ranges
import OnBytes.Params.DeriveReq
import OnBytes.Iop.Req

namespace OnBytes.Plan

open OnBytes.Params

/-! ## The public file -/

/-- The numbers of a small run's public file. -/
structure ToyNumbers where
  /-- what the first line says of the run -/
  runWords : List UInt8 := []
  /-- the format's version -/
  format : List UInt8 := []
  /-- the lines of one number, by name, in their order -/
  numbers : List (String × Nat) := []
  /-- the further stages of the proximity test -/
  further : List StageLine := []

/-- The number under a name; the first one if there are several. -/
def ToyNumbers.get? (n : ToyNumbers) (name : String) : Option Nat := n.numbers.lookup name

/-- Cuts a list at every byte c. -/
def splitAt (c : UInt8) (l : List UInt8) : List (List UInt8) :=
  (l.foldr (fun x (acc : List UInt8 × List (List UInt8)) =>
    if x == c then ([], acc.1 :: acc.2) else (x :: acc.1, acc.2)) ([], [])) |> fun a => a.1 :: a.2

/-- A number of one to six decimal digits; nothing for any other word. The cap is meant to keep a
file from asking for a huge run. It does not bound the number of lines, and where no caller bounds a
number further (the code lengths of a further stage) 999999 is still huge. -/
def shortNumber (w : List UInt8) : Option Nat :=
  if !w.isEmpty && decide (w.length ≤ 6) && w.all fun c => 48 ≤ c && c ≤ 57 then
    some (w.foldl (fun v c => 10 * v + (c.toNat - 48)) 0)
  else none

/-- Takes one line in. While the lines are read, the two lists of n have their last member first. A
line of numbers has four of them (a stage) or one; the words are counted before any is read. -/
def takeToyLine (n : ToyNumbers) (line : List UInt8) : Option ToyNumbers :=
  match splitAt 32 line with
  | [] | [_] => none
  | name :: rest =>
    let behind := line.drop (name.length + 1)
    if name == "run".toUTF8.toList then some { n with runWords := behind }
    else if name == "format".toUTF8.toList then some { n with format := behind }
    else
      match rest, String.fromUTF8? ⟨name.toArray⟩ with
      | [a, b, c, d], some "stage" => do
        pure { n with further :=
          ⟨← shortNumber a, ← shortNumber b, ← shortNumber c, ← shortNumber d⟩ :: n.further }
      | [a], some word =>
        if word == "stage" then none
        else (shortNumber a).map fun x => { n with numbers := (word, x) :: n.numbers }
      | _, _ => none

/-- Reads a public file's text. Every line ends with a line feed. -/
def readToyText (text : ByteArray) : Option ToyNumbers :=
  let lines := splitAt 10 text.toList
  if lines.getLast? != some [] then none
  else (lines.dropLast.foldlM takeToyLine {}).map fun n =>
    { n with numbers := n.numbers.reverse, further := n.further.reverse }

/-- The public file that a run writes. numbers: the run's own lines, after the setting's six. Of
the first line's words only what comes before their first zero byte is written, as in the C++
programs, which hand these words on as a string that a zero byte ends. So a file with a zero byte
in its first line is not in its one spelling. -/
def toyText (runWords : List UInt8) (s : Setting) (numbers : List (String × Nat))
    (further : List StageLine) : ByteArray :=
  let line := fun (x : String × Nat) => x.1 ++ " " ++ toString x.2 ++ "\n"
  "run ".toUTF8 ++ ⟨(runWords.takeWhile (· != 0)).toArray⟩ ++ ("\nformat H821\n" ++
    String.join (([("target", s.target), ("work-on-positions", s.workQuery.request),
      ("salt-bytes", s.saltBytes), ("nonce-bytes", s.nonceBytes),
      ("position-bytes", s.positionBytes), ("samples", s.samples)] ++ numbers).map line) ++
    String.join (further.map fun x =>
      "stage " ++ toString x.k ++ " " ++ toString x.h ++ " " ++ toString x.logN ++ " " ++
        toString x.maskLogN ++ "\n")).toUTF8

/-- The setting that a small run's file speaks of: the second of the format's two fields (the prime
2^64 - 2^32 + 1, which `Setting` has unless told otherwise), and the file's six numbers. Nothing if
one of the six is missing, if the format's version is not the one that toyText writes, if the target
is above 256 or the work above 40, if a nonce has fewer than 1 or more than 8 bytes, or if a listed
position has more than 8. On the last two the C++ routine that reads the file says nothing, but the
C++ channel ends the process under such a setting (blocks/chain/rounds.h), so no such file gets a
yes there. -/
def toySetting (n : ToyNumbers) : Option Setting := do
  let target ← n.get? "target"
  let work ← n.get? "work-on-positions"
  let salt ← n.get? "salt-bytes"
  let nonce ← n.get? "nonce-bytes"
  let position ← n.get? "position-bytes"
  let samples ← n.get? "samples"
  if n.format != "H821".toUTF8.toList || 256 < target || 40 < work then none
  if nonce < 1 || 8 < nonce || 8 < position then none
  pure { target := target, workQuery := ⟨work, 0, 0⟩, saltBytes := salt, nonceBytes := nonce,
         positionBytes := position, samples := samples }

/-! ## Sizing -/

/-- Positions and random entries of a run's first group, from below. A row gets as many random
entries as positions are drawn (tailFor), and the number of draws depends on the rate, so both are
raised in turns until they settle. batched: the largest number of rows that are batched on the
group. The first argument bounds the turns. If they run out, the last group is returned with the
larger number of positions, unsettled, as the C++ loop leaves them. Nothing if no slack below the
Johnson radius holds the group's rounds at the target. -/
def groupFromBelow (s : Setting) (batched : Nat) : Nat → GroupSize → Nat → Option (GroupSize × Nat)
  | 0, g, t => some (g, t)
  | fuel + 1, g, t =>
    let g1 : GroupSize :=
      { g with main := { g.main with r := tailFor t }, mask := { g.mask with r := tailFor t } }
    let g2 := sizeGroup s .request g1 { cubeBits := stageCubeBits g1, batchedRows := batched }
    let a := analysis s g2
    if a.bad then none
    else
      let more := scopePositions s .request a.mainAt.agree (margin s)
      if more ≤ t then some (g2, t) else groupFromBelow s batched fuel g2 more

/-- Everything that is fixed before a small run. -/
structure ToyRun where
  /-- the public file -/
  text : ByteArray
  /-- the plan of the run's one chain -/
  plan : Planned
  /-- the items of the chain's parameter bytes after the digest of the public file -/
  items : List (String × ByteArray)

/-- True if the run has a round that misses the target unless its proof of work counts. -/
def ToyRun.needsWork (r : ToyRun) : Bool := r.plan.needsWork

/-- The bits of proof of work that the run's file asks before a draw of positions. -/
def ToyRun.work (r : ToyRun) : Nat := r.plan.set.workQuery.request

/-- The parameter bytes of a small run's chain. -/
def ToyRun.params (r : ToyRun) : ByteArray :=
  Fmt.paramsBytes r.plan.plan (Fmt.configDigest [r.text]) r.items

/-- The mask entries that the sumcheck of a b = c on 2^vars places takes. -/
def productMasks (vars : Nat) : Nat := 1 + 2 * vars + 2 + 2

/-- The rounds of the claim a b = c on 2^vars places: the point, then the sumcheck. -/
def productRounds (vars : Nat) : Planning Unit := do
  planZero vars
  planPsc { degree := List.replicate vars 3 }

/-- The name under which a public file is refused whose target is below what the caller asks. -/
def securityBits : String := "security-bits"

/-- The names of their own under which the routines of this file refuse. -/
def names : List String := [securityBits]

/-! ## The run "product" -/

/-- Sizes and plans the run "product" from its public file. bits: what the caller asks of every
round. Refused if the text is not the one spelling of a file with this run's lines, if no admissible
numbers follow, if a round does not hold at the file's target with its work counted, or if that
target is below bits. The words after "run" in the first line are not compared with the run's name.
They enter the digest of the file. -/
def productRun (text : ByteArray) (bits : Nat := 128) : Except String ToyRun := do
  let n ← orRefuse (readToyText text)
  let s ← orRefuse (toySetting n)
  let logLen ← orRefuse (n.get? "log-length")
  let logN ← orRefuse (n.get? "log-n")
  let maskLogN ← orRefuse (n.get? "mask-log-n")
  if logLen < 1 || 20 < logLen || 24 < logN || 24 < maskLogN then throw notAdmitted
  if toyText n.runWords s [("log-length", logLen), ("log-n", logN), ("mask-log-n", maskLogN)]
      n.further != text then throw notAdmitted
  let shape : GroupSize :=
    { main := { logN := logN, ell := 2 ^ logLen }
      mask := { logN := maskLogN, overE := true,
                ell := pow2AtLeast (max (productMasks logLen + s.samples) (2 * 2 + 1)) }
      k := 2
      h := 0 }
  let rows := 3 + s.samples
  let (g, t) ← orRefuse (groupFromBelow s rows 16 shape 0)
  let solved ← orRefuse (solveStages s .request g t n.further)
  let (stages, codes) := ioppStages solved {}
  if !sizedFits codes stages solved then throw notAdmitted
  let oracle : OracleNotice :=
    ⟨{ code := 0, mainRows := 3, mainDeg := 1, maskRows := 1, maskCode := 0,
       answers := s.samples }, 0⟩
  let plan ← finishHeld s .request do
    planSend [⟨cubeBitsOf codes oracle.shape, [g]⟩]
      (← must ((linMaskNotice stages 0).bind fun m => treesOf codes #[oracle, m]))
    productRounds logLen
    planIopp solved rows 0 true
  if s.target < bits then throw securityBits
  pure ⟨text, plan,
    [("codes", spellCodes codes), ("the oracle message a, b, c", spellNotice oracle),
     ("the stages of the proximity test", spellStages stages),
     ("the choices of the proximity test", spellChoice ⟨true⟩)]⟩

/-! ## The run "links" -/

/-- The links of the run "links": each has an oracle message of its own, with the link's mask row,
and one for the product, which is kept for the next link if there is one. The first link's own
message has two rows. -/
def toyLinks (links answers : Nat) : List ReqLink :=
  fillLinks <| withAnswers answers ((List.range links).map fun l =>
    ⟨0, [⟨{ mainRows := if l == 0 then 2 else 1, maskRows := 1 }, 0, 0, 0⟩,
         ⟨{ mainRows := 1 }, 0, 0, if l + 1 < links then 1 else 0⟩]⟩)

/-- A test on the table that is never read: the run "links" has no table, and nothing rides in its
first message. -/
def noTable : LinSized where
  lines := { kLo := 0, matrixRows := 0, folded := default, omega := default, own := default,
             requests := 1, inputMaskRows := 0, oneTime := false }
  shape := default
  input := default
  table := default
  folded := ⟨{}, 0, []⟩
  omega := ⟨{}, 0, []⟩
  own := ⟨{}, 0, []⟩
  batches := 0

/-- Sizes and plans the run "links" from its public file. bits: what the caller asks of every round.
Refused if the text is not the one spelling of a file with this run's lines, if no admissible
numbers follow, if a round does not hold at the file's target with its work counted, or if that
target is below bits. The words after "run" in the first line are not compared with the run's name.
A row has 2^log-length entries, and a vector half as many. slots = 2: a main row and one kept row
side by side. The group is sized for 16 + 4 * 4 * target batched rows: the rows of a sub-proof, the
samples, and four generator rows for each position. -/
def linksRun (text : ByteArray) (bits : Nat := 128) : Except String ToyRun := do
  let n ← orRefuse (readToyText text)
  let s ← orRefuse (toySetting n)
  let links ← orRefuse (n.get? "links")
  let logEll ← orRefuse (n.get? "log-length")
  let logN ← orRefuse (n.get? "log-n")
  let maskLogN ← orRefuse (n.get? "mask-log-n")
  if links < 1 || 64 < links || logEll < 2 || 20 < logEll || 24 < logN || 24 < maskLogN then
    throw notAdmitted
  if toyText n.runWords s [("links", links), ("log-length", logEll), ("log-n", logN),
      ("mask-log-n", maskLogN)] n.further != text then throw notAdmitted
  let vars := logEll - 1
  let link := toyLinks links s.samples
  let groups := (reqGroups (shapeOfLinks link s.samples)).toList
  let k := (groups.take links).foldl (fun x g => max x g.k) 0
  let shape : GroupSize :=
    { main := { logN := logN, ell := 2 ^ logEll }
      mask := { logN := maskLogN, overE := true,
                ell := pow2AtLeast (max (productMasks vars + s.samples) (2 * k + 1)) }
      k := k
      h := 0
      slots := 2 }
  let (g, t) ← orRefuse (groupFromBelow s (16 + 4 * 4 * s.target) 16 shape 0)
  let lastGroup ← orRefuse groups.getLast?
  let last : GroupSize := { g with k := lastGroup.k, h := lastGroup.h, slots := 1 }
  let solved ← orRefuse (solveStages s .request last t n.further)
  let (stages, codes) := ioppStages solved {}
  let req : ReqShape :=
    { code := 0, maskCode := 0, link := link, atStart := [], answers := s.samples, last := stages,
      choice := ⟨true⟩ }
  if !reqOk codes req then throw notAdmitted
  let plan ← finishHeld s .request (reqPlan
    { set := s, codes := codes, link := ⟨g, t⟩, last := ⟨last, t, solved⟩, request := req,
      batch := noTable }
    { links := link, openRows := List.replicate links 3, plan := fun _ _ => productRounds vars,
      pendingRows := 0, matrixRows := 0 })
  if s.target < bits then throw securityBits
  pure ⟨text, plan, [("codes", spellCodes codes), ("the chain of links", spellReq req)]⟩

end OnBytes.Plan
