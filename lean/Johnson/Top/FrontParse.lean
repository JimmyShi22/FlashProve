-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/FrontParse.lean: a parser made of four parts, for the frame of
Johnson/Top/FrontParts.lean; and what "parse, then the arm" gives for the proof file and for the
request.

AT LETTERS: IT CANNOT BE RUN: it says something only at a written r and a written parser, and none
is given here.

In that frame a part of the front verifier is no place for a term: it is a field of `FrontParts`, a
proposition on the front verifier `p.port`, the one parser `p.reader` and an arm. For the proof file
a term comes in at two places: the arm at `r.armP`, and the reading of the proof file inside the
parser.
  `proofPart_of_parseThen`: where the front verifier has the check "parse, then `liftPC r`", the
    field `proofPart` holds by definition: no tie, no way out. The like of `entryPart_of_parseThen`.
  `evaluate_parseThen_none`: where the builder makes no instance, "parse, then the arm" says no.
  `request_of_parseThen`: where the front verifier has a check "parse, then an arm" and says yes,
    the builder has made an instance: the field `request` holds by definition too.
  `ParseParts r Files`: a parser in four parts: the further tokens; the reading of the key file
    (what of the public data stands in a key, root, record, the test's string); of the entry file
    (the further root, its record, the link's string); of the proof file (the number of the stored
    copy, the session's string). The last three are algorithms over the hash function and may fail.
  `layParts`: what the four return, laid as the frame's typed proof. The frame's parser is total:
    where a reading fails, its string is left out, and the arm refuses a proof without its string.
    The session's string is left out unless all three readings return.
  `ParseParts.reader`, `evaluate_reader`, `reader_budget`: the one parser, its value at g, and its
    budget of queries: the sum of the three readings'.
  `liftPC_layParts`: on what is laid, `liftPC r` says yes at g exactly if the three readings
    returned and `r.armP` says yes at g at: the key's reading's public part; the ENTRY's reading's
    root and record; the instance; the proof's reading's number and string.
  `parseThen_proof_yes_iff`: so, at a parser made of parts, the yes of "parse, then `liftPC r`" at
    g.

WHO BRINGS WHAT, BY THE FRAME's TYPES. Prompt and output tokens are arguments of the front verifier
and of the parser; the commitment is an argument of the front verifier alone: no part of the parser
sees it. The instance is built of prompt, output and the further tokens. The further tokens, the key
WITH ITS PUBLIC PART (`r.C`), the number of the stored copy and all strings are what the parser
makes of the prover's files. The public files reach an arm through r alone; that the arm tests the
key's public part lies in the arm's bound. In `front_sound` the parser enters by its budget alone
(the error is ε (t + n) + δ t): what it returns counts as the prover's; that is the frame's theorem,
under its hypotheses, and nothing of it is proved here. That r and the parts hold nothing of the
hash function is asked by nothing here.

What is not claimed. All that the head of Johnson/Top/FrontParts.lean does not claim. r, p and the
four parts are letters: with parts that build what the arm likes instead of parsing the files, all
here holds and says nothing. WHAT KIND OF TERM `r.armP` IS this file does not say, and three kinds
are to be kept apart: (1) the compiler's verifier at a description that states the protocol round by
round; (2) the compiler's verifier at a flat description, whose rounds are a dry run's list and
whose decision is the verifier program's own blocks run on the views: the compiler's shell around
hand-written blocks; (3) a text written by hand after the C++ verifier. `proofPart` is paid by
definition at all three alike. WHAT A FIELD PAID BY DEFINITION IS WORTH. Of the two debts of the
proof file, the tie falls and the arm's bound (`CoreArmsCD.proofArm`) stays as it was. What the tie
would have given beside soundness, that the arm says yes where a hand-written check does, is then
owed as acceptance: a front verifier that accepts nothing meets all fields. At an arm of kind (2)
the bound rests on the soundness of the flat description's protocol, a named hypothesis that nothing
in this library proves. That the key file's and the proof file's arms begin with the test of the
record's seed against the hash function is asked by nothing here: it lies in the arms' bounds: an
arm without it lets a prover name the seed. And a field paid by definition is worth what the program
that ships RUNS: where a program runs another verifier, its exit code 0 says nothing of a front
verifier with this check without a tie between the two at the program's hash function. At a format
in which the request that a prover names reaches the proof's queries through the earlier mode's
digest alone, a fixed public function, no bound below 1 is to be had for an arm that spells what the
format spells (by thought). This file names no string: what is hashed stands in
`r.armP` and in the parts. No count of any reading's queries is given: at a parser made of parts
`budget` comes down to the three readings' counts, each at every file, an adversary's too; they stay
hypotheses. That an honest prover's files are accepted is not said. No probability; no bound. For
proofs only; the program does not import this file.


-/
import Johnson.Top.FrontParts
import Rom.OneOfCount
import Rom.Prefix

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {r : InputArmsC}

section Part

variable (p : PortArmsC r)

/-- The proof file's part, where it is "parse, then the arm", is paid by definition: no tie, no way
out. -/
theorem proofPart_of_parseThen {g : Hash} {c : Commitment} {prompt output : List Token}
    {F : p.Files} {x : r.X}
    (h : (p.withCheck (parseThen p (liftPC r))).Yes g c prompt output F)
    (hx : r.build (prompt, output) (p.parsed g prompt output F).1 = some x) :
    (liftPC r (p.parsed g prompt output F).2.1 x (p.parsed g prompt output F).2.2).det
      (fun _ => g) = true :=
  (evaluate_parseThen p (liftPC r) g prompt output F x hx).symm.trans (p.yes_withCheck _ h).2

/-- Where the builder makes no instance, "parse, then the arm" says no. -/
theorem evaluate_parseThen_none (arm : r.C × KeyRoot 256 r.L → r.X → OfflineLinkOnlineProof 256 r.L r.aT r.aL →
      Rom.OComp (rom 256) Bool) (g : Hash) (prompt output : List Token) (F : p.Files)
    (hx : r.build (prompt, output) (p.parsed g prompt output F).1 = none) :
    (parseThen p arm prompt output F).evaluate g = false := by
  unfold parseThen
  rw [DeterministicAlgorithm.evaluate_andThen]
  show (match r.build (prompt, output) (p.parsed g prompt output F).1 with
    | some x => deterministicOf (Rom.ofRom (arm (p.parsed g prompt output F).2.1 x
        (p.parsed g prompt output F).2.2))
    | none => .done false).evaluate g = _
  rw [hx]
  all_goals rfl

/-- Where a front verifier with the check "parse, then an arm" says yes, the builder has made an
instance. -/
theorem request_of_parseThen (arm : r.C × KeyRoot 256 r.L → r.X → OfflineLinkOnlineProof 256 r.L r.aT r.aL →
      Rom.OComp (rom 256) Bool) {g : Hash} {c : Commitment} {prompt output : List Token}
    {F : p.Files} (h : (p.withCheck (parseThen p arm)).Yes g c prompt output F) :
    ∃ x, r.build (prompt, output) (p.parsed g prompt output F).1 = some x := by
  cases hx : r.build (prompt, output) (p.parsed g prompt output F).1 with
  | some x => exact ⟨x, rfl⟩
  | none =>
    exact absurd ((evaluate_parseThen_none p arm g prompt output F hx).symm.trans
      (p.yes_withCheck _ h).2) Bool.false_ne_true

end Part

/-- A parser in four parts. The three readings are algorithms over the hash function and may fail.
None sees the commitment. Where a reading draws a number, the one parser takes it as 0. -/
structure ParseParts (r : InputArmsC) (Files : Type) where
  /-- the further tokens -/
  aux : List Token → List Token → Files → List Token
  /-- the key file: what of the public data stands in a key, root and record; the test's string -/
  key : List Token → List Token → Files →
    Rom.OComp (rom 256) (Option ((r.C × KeyRoot 256 r.L) × OneProtocolProof 256 (batTC r.L r.aT)))
  /-- the entry file: the further root, its record, the link's string -/
  ent : List Token → List Token → Files →
    Rom.OComp (rom 256) (Option (Dig 256 × r.L.Rec × OneProtocolProof 256 (batLC r.L r.aL)))
  /-- the proof file: the number of the stored copy, the session's string -/
  prf : List Token → List Token → Files → Rom.OComp (rom 256) (Option (ℕ × OneProtocolProof 256 r.L.onlineBatch))

variable (r) in
/-- What the four parts return, laid as the frame's typed proof. Where a reading fails its string is
left out; the session's string is left out unless all three readings return. -/
def layParts (a : List Token)
    (k : Option ((r.C × KeyRoot 256 r.L) × OneProtocolProof 256 (batTC r.L r.aT)))
    (e : Option (Dig 256 × r.L.Rec × OneProtocolProof 256 (batLC r.L r.aL)))
    (q : Option (ℕ × OneProtocolProof 256 r.L.onlineBatch)) :
    List Token × ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL) :=
  (a, ((k.map fun k => k.1).getD r.π₀.1,
    { copy := (q.map fun q => q.1).getD 0
      piT := k.map fun k => k.2
      link := match e with
        | some e => (e.1, e.2.1, some e.2.2)
        | none => (r.π₀.2.link.1, r.π₀.2.link.2.1, none)
      piB := match k, e, q with
        | some _, some _, some q => some q.2
        | _, _, _ => none }))

/-- On what is laid, the proof file's arm says yes at g exactly if the three readings returned and
the input's arm says yes at g on what they returned. -/
theorem liftPC_layParts (g : Fam (rom 256)) (a : List Token)
    (k : Option ((r.C × KeyRoot 256 r.L) × OneProtocolProof 256 (batTC r.L r.aT)))
    (e : Option (Dig 256 × r.L.Rec × OneProtocolProof 256 (batLC r.L r.aL)))
    (q : Option (ℕ × OneProtocolProof 256 r.L.onlineBatch)) (x : r.X) :
    (liftPC r (layParts r a k e q).2.1 x (layParts r a k e q).2.2).det g = true ↔
      ∃ k' e' q', k = some k' ∧ e = some e' ∧ q = some q' ∧
        (r.armP k'.1.1 e'.1 x e'.2.1 q'.1 q'.2).det g = true := by
  cases k with
  | none => exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨_, _, _, h, _⟩ => nomatch h⟩
  | some k' =>
    cases e with
    | none => exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨_, _, _, _, h, _⟩ => nomatch h⟩
    | some e' =>
      cases q with
      | none =>
        exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨_, _, _, _, _, h, _⟩ => nomatch h⟩
      | some q' =>
        exact ⟨fun h => ⟨k', e', q', rfl, rfl, rfl, h⟩, fun ⟨_, _, _, h1, h2, h3, h⟩ =>
          Option.some.inj h1 ▸ Option.some.inj h2 ▸ Option.some.inj h3 ▸ h⟩

section Parts

variable {Files : Type} (R : ParseParts r Files)

/-- The four parts one after the other, as one algorithm over the hash function. -/
def ParseParts.tree (prompt output : List Token) (F : Files) :
    Rom.OComp (rom 256) (List Token × ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL)) :=
  (R.key prompt output F).bind fun k => (R.ent prompt output F).bind fun e =>
    (R.prf prompt output F).bind fun q => .pure (layParts r (R.aux prompt output F) k e q)

/-- The one parser. -/
def ParseParts.reader (prompt output : List Token) (F : Files) :
    DeterministicAlgorithm (List Token × ((r.C × KeyRoot 256 r.L) × OfflineLinkOnlineProof 256 r.L r.aT r.aL)) :=
  deterministicOf (Rom.ofRom (R.tree prompt output F))

/-- Its value at g: the parts' values at g, laid. -/
theorem ParseParts.evaluate_reader (g : Hash) (prompt output : List Token) (F : Files) :
    (R.reader prompt output F).evaluate g =
      layParts r (R.aux prompt output F) ((R.key prompt output F).det fun _ => g)
        ((R.ent prompt output F).det fun _ => g) ((R.prf prompt output F).det fun _ => g) := by
  unfold ParseParts.reader ParseParts.tree
  rw [OnBytes.K.evaluate_ofRom]
  simp only [Rom.OComp.det_bind]
  all_goals rfl

/-- The one parser's budget of queries: the sum of the three readings'. -/
theorem ParseParts.reader_budget {nK nE nP : ℕ}
    (hK : ∀ prompt output F, (R.key prompt output F).QueryBound nK)
    (hE : ∀ prompt output F, (R.ent prompt output F).QueryBound nE)
    (hP : ∀ prompt output F, (R.prf prompt output F).QueryBound nP)
    (prompt output : List Token) (F : Files) :
    (R.reader prompt output F).toRandomized.QueryBound (nK + (nE + nP)) := by
  have h : (R.tree prompt output F).QueryBound (nK + (nE + (nP + 0))) :=
    Rom.OComp.QueryBound.bind (hK prompt output F) fun _ =>
      Rom.OComp.QueryBound.bind (hE prompt output F) fun _ =>
        Rom.OComp.QueryBound.bind (hP prompt output F) fun _ => trivial
  exact queryBound_deterministicOf _ _ (Rom.queryBound_ofRom _ _ h)

end Parts

/-- **"Parse, then the arm" for the proof file, at a parser made of parts: its yes at g.** -/
theorem parseThen_proof_yes_iff (p : PortArmsC r) (R : ParseParts r p.Files)
    (hp : p.reader = R.reader) (g : Hash) (prompt output : List Token) (F : p.Files) :
    (parseThen p (liftPC r) prompt output F).evaluate g = true ↔
      ∃ x k e q, r.build (prompt, output) (R.aux prompt output F) = some x ∧
        (R.key prompt output F).det (fun _ => g) = some k ∧
        (R.ent prompt output F).det (fun _ => g) = some e ∧
        (R.prf prompt output F).det (fun _ => g) = some q ∧
        (r.armP k.1.1 e.1 x e.2.1 q.1 q.2).det (fun _ => g) = true := by
  have hl : p.parsed g prompt output F =
      layParts r (R.aux prompt output F) ((R.key prompt output F).det fun _ => g)
        ((R.ent prompt output F).det fun _ => g) ((R.prf prompt output F).det fun _ => g) := by
    unfold PortArmsC.parsed
    rw [hp]
    exact R.evaluate_reader g prompt output F
  constructor
  · intro h
    cases hx : r.build (prompt, output) (p.parsed g prompt output F).1 with
    | none =>
      rw [evaluate_parseThen_none p _ g prompt output F hx] at h
      exact absurd h Bool.false_ne_true
    | some x =>
      rw [evaluate_parseThen p _ g prompt output F x hx, hl] at h
      obtain ⟨k, e, q, h1, h2, h3, h4⟩ := (liftPC_layParts _ _ _ _ _ x).1 h
      rw [hl] at hx
      exact ⟨x, k, e, q, hx, h1, h2, h3, h4⟩
  · rintro ⟨x, k, e, q, hx, h1, h2, h3, h4⟩
    have hx' : r.build (prompt, output) (p.parsed g prompt output F).1 = some x := by
      rw [hl]
      exact hx
    rw [evaluate_parseThen p _ g prompt output F x hx', hl]
    exact (liftPC_layParts _ _ _ _ _ x).2 ⟨k, e, q, h1, h2, h3, h4⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.proofPart_of_parseThen
#print axioms VerifiableInference.OnPublicFiles.evaluate_parseThen_none
#print axioms VerifiableInference.OnPublicFiles.request_of_parseThen
#print axioms VerifiableInference.OnPublicFiles.liftPC_layParts
#print axioms VerifiableInference.OnPublicFiles.ParseParts.evaluate_reader
#print axioms VerifiableInference.OnPublicFiles.ParseParts.reader_budget
#print axioms VerifiableInference.OnPublicFiles.parseThen_proof_yes_iff
