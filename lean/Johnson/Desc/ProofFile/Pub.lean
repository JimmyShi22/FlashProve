-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Pub.lean: what the proof file's description is computed from: the public
part, the instance, the tests on the instance, the first state, and the segments' records.
  `Pub`, `pubBy`     the public part, from the three public files (policy.txt, layout.txt, KL.bin)
  `InstPub`, `Inst`  the instance, as plain data: the request file's bytes, the table's key, and
                     the reply file's bytes, which say what is asked of the proof
  `lettersBy`, `blankBy`   the segments' records (Ground.lean), from the state `S` alone, and
                     those of a request of zeros
  `startS`           the first chain's first state
  `holdBy`, `okBy`   the tests on the instance
  `SecondHashFunctionArgument`        the type of the argument that stands for the second hash function
  `Road`             which functions compute the public part and the segments' records
`pubBy`, `lettersBy`, `blankBy`, `holdBy` and `okBy` take the functions that compute the planner's
record and the segments' records as arguments. The proof file's description passes PlanPlain.lean's
(OnlineDescriptionPublicPart.lean). The ones in or built on the program `verify-on-bytes` (`madeOf` of
Johnson/G/RoundsOfPlan.lean, `Verify.linksOf`) would reach its routines for the segments and its
hash functions; only test harnesses pass those.
What the proof file's description uses of `verify-on-bytes` and of what is built on it, all of
it on the plan or the instance and none on a proof: the planner's types, `declPOf` and `depthOf`
(Johnson/G/RoundsOfPlan.lean), `Proof.tailPublic`, `Head.stFromCall`, `Head.coveredOf`,
`Verify.words32`, `Verify.statementHeld`, `Maker.okSeeds`.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.ProofFile.Ground
import Johnson.Desc.ProofFile.Told
import Johnson.G.RoundsOfPlan
import Johnson.Desc.First.Driver.Cut
import Johnson.Desc.First.State
import OnBytes.Maker.Decide3
import OnBytes.Model.Verify
import Fmt.RequestItem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open OnBytes OnBytes.Model OnBytes.Model.Stages
open VerifiableInference.Desc.First

/-- A refusal, with a name in front of its words. -/
def atCall {α : Type} (name : String) (x : Except String α) : Except String α :=
  x.mapError fun e => name ++ ": " ++ e

/-- A refusal as a pair: where, and why. -/
def held {α : Type} (at_ : String) (y : Except String α) : Except (String × String) α :=
  y.mapError fun e => (at_, e)

/-- `none` as a refusal with the words `why`. -/
def orSay {α : Type} (why : String) (x : Option α) : Except String α :=
  x.elim (.error why) .ok

/-! ### The public part -/

/-- The public part: all that the description takes from the three public files. -/
structure Pub where
  /-- policy.txt and KL.bin, for the request's item -/
  pol : ByteArray
  KL : ByteArray
  /-- the planner's record -/
  made : Johnson.G.OfPlan.Made
  P : Par
  /-- the first chain's rounds, cut into `verify-on-bytes`'s named steps -/
  cuts : List Cut
  /-- the three chains' declared rounds -/
  D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound
  /-- the three chains' trees, each with what shares its leaves (Told.lean) -/
  told : List Root × List Root × List Root
  /-- the stored table's depth -/
  depth : Nat
  /-- the state before the first segment -/
  s₀ : S

namespace Pub

/-- `verify-on-bytes`'s record of all that follows from the public files (`Planned`,
OnBytes/Model/Verify.lean): the public record `X`, the seven chains, the segments. -/
def p (Z : Pub) : Verify.Planned := Z.made.p

/-- The first chain's parameters. -/
def first (Z : Pub) : Params.First := Z.p.chains.proof.first

/-- What is public about the two later chains. The table's name is left empty: `decide3` does not
read it (`decide3_table`, OnBytes/Maker/Decide3.lean). That no block of the later
chains reads it is not shown. -/
def tail (Z : Pub) : Proof.TailPublic := Proof.tailPublic Z.p.chains.proof Maker.noTable

/-- The three chains' entries of the plan. -/
def plans (Z : Pub) : List Fmt.Entry × List Fmt.Entry × List Fmt.Entry :=
  (Z.first.given.rounds, Z.tail.shared.given.rounds, Z.tail.second.given.rounds)

/-- The number of the first chain's rounds before `verify-on-bytes`'s step of the name `look` (such
as "G0.2.call"). Limit: if the table has no step of that name, the result is the number of all
rounds, and nothing shows it. Use `roundsBefore?` where that matters. -/
def roundsBefore (Z : Pub) (look : String) : Nat :=
  (Z.cuts.takeWhile fun c => c.look != look).foldl (fun n c => n + c.take) 0

/-- The same; `none` if the table has no step of that name. -/
def roundsBefore? (Z : Pub) (look : String) : Option Nat :=
  if Z.cuts.any fun c => c.look == look then some (Z.roundsBefore look) else none

end Pub

/-- How the state before the first segment and its parameters are computed. `word`: what a printout
says about it. -/
structure Starts where
  word : String
  par : Params.First → Par
  start : Par → Params.First → Option S

/-- The public part. `made` computes the planner's record, `st` the first state. -/
def pubBy (made : ByteArray → ByteArray → ByteArray → Except String Johnson.G.OfPlan.Made)
    (st : Starts) (pol lay KL : ByteArray) : Except String Pub := do
  let m ← atCall "the plan" (made pol lay KL)
  let first := m.p.chains.proof.first
  if !first.codes.lengthsOk then
    throw "the codes' lengths: a message's length is not a power of two"
  let D ← atCall "the declared rounds" (Johnson.G.OfPlan.declPOf m)
  let told ← toldOf m
  let depth ← atCall "the stored table's depth" (Johnson.G.OfPlan.depthOf m)
  let cuts ← orSay "the table of steps: the plan's names do not fit the grammar"
    (cutOf first.given.rounds)
  let P := st.par first
  let s₀ ← orSay "the first state: a test on the first chain's public parameters fails"
    (st.start P first)
  pure { pol := pol, KL := KL, made := m, P := P, cuts := cuts, D := D, told := told
         depth := depth
         s₀ := s₀ }

/-! ### The instance -/

/-- The instance without what is asked of the proof. -/
structure InstPub where
  /-- the request file's bytes -/
  request : ByteArray
  /-- the table's key -/
  key : TableKey

/-- The instance. -/
structure Inst where
  pub : InstPub
  /-- the reply file's bytes: the token that is asked about -/
  y : ByteArray

/-- The reply that is asked about, as a field element. -/
def Inst.asked (x : Inst) : E := ofNat ((Verify.words32 x.y).getD 0 0).toNat

/-! ### The segments' records, the first state, the tests on the instance -/

/-- What computes the segments' records, from the public record and the positions that the request
covers. `verify-on-bytes`'s `Verify.linksOf` puts its routine for each segment into the
field `run`; PlanPlain.lean's puts one there that refuses. Nothing here calls that field;
`lettersBy` and `holdBy` copy it. -/
abbrev LinksBy : Type := Verify.Public → Head.Covered → Except String (Array LinkH)

/-- The segments' records, from the state alone: from the request's words in it and the
reply that was heard, or the token 0 until one is heard. -/
def lettersBy (mk : LinksBy) (Z : Pub) (s : S) : Except String Ground := do
  let W := Z.p.X
  let cov ← if s.out.reply.isNone then s.coveredAt W.T W.P.h.V 0 else s.covered W.T W.P.h.V
  let links ← mk W cov
  pure ⟨Z.p.built.links.zipWith (fun b l => { b with run := l.run }) links, Z.first, W, cov⟩

/-- The segments' records for a request of zeros that covers its first position alone. A block that
does not depend on the request is computed from these. -/
def blankBy (mk : LinksBy) (Z : Pub) : Option Ground :=
  let T := Z.p.X.T
  (lettersBy mk Z (Z.s₀.withReq (Array.replicate T 0 ++ #[0, 1]))).toOption

/-- The first chain's first state: the public part's state before the first segment, with the
request's words written into it. If the tests on the request that need no reply fail, it is the
blank state, which is marked as failed. This is the text of State.lean's `S.startReq?`, with the
value of `S.start?` taken from the public part, so that it is computed once and not per instance.
-/
def startS (Z : Pub) (p : InstPub) : S :=
  let s := Z.s₀.withReq (Verify.words32 p.request)
  if s.reqOk Z.p.X.T Z.p.X.P.h.V then s else S.blank

/-- The type of a function that can stand for the second hash function (`secondHashFunction`,
OnBytes/Hash/SecondHashFunction.lean): from a number and bytes to bytes. It is `SecondHashFunctionType` of lean/Ladder.lean,
written out, since this file does not import that one. The caller of the description supplies the
function. It is used for the request's item in the tests on the instance (`holdBy`) and in computing
the public part (`Road.pub`). Whether the term `onlineDescription` reaches a hash function by name is
not checked here. -/
abbrev SecondHashFunctionArgument : Type := Nat → ByteArray → ByteArray

/-- The tests on the instance, the first five in `verify-on-bytes`'s order: the files' lengths; the
request and the reply; the request's item; the comparison of that item with the public record; the
segments' records; the key's seeds (OnBytes/Maker/OkView.lean). A refusal says which test failed.
The request's item is `Fmt.requestItem o` (Fmt/RequestItem.lean), which takes the hash as an
argument. At the second hash function it equals `Proof.requestItem` on all files (`requestItem_eq`,
OnBytes/Tie/Decl/RequestItemLaw.lean).
`statementHeld` compares three digests in the item with the field `digests` of the public record. So
that record has to be computed with the same `o`; PlanPlain.lean's is. With `verify-on-bytes`'s
planner every instance is refused here unless `o` is the second hash function. -/
def holdBy (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : Pub) (x : Inst) :
    Except (String × String) Ground := do
  let W := Z.p.X
  held "the words test"
    (refuseIf (x.pub.request.size % 4 != 0 || x.y.size % 4 != 0) "statement-required")
  let so ← held "the request and the reply"
    (Head.stFromCall (Verify.words32 x.pub.request) (Verify.words32 x.y) W.T)
  let cov ← held "the request and the reply" (Head.coveredOf so W.T W.P.h.V)
  let item ← held "the request's item"
    ((Fmt.requestItem o Z.pol Z.KL x.pub.request).elim (.error "internal-request-item") .ok)
  held "the statement's test" (Verify.statementHeld W item)
  let links ← held "the links' records" (mk W cov)
  held "the table's key"
    (refuseIf (!Maker.okSeeds x.pub.key) "a word of a seed is not below the prime")
  pure ⟨Z.p.built.links.zipWith (fun b l => { b with run := l.run }) links, Z.first, W, cov⟩

/-- The same, as a yes or no. -/
def okBy (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : Pub) (x : Inst) : Bool :=
  (holdBy o mk Z x).toOption.isSome
/-- Which functions a description uses to compute the public part and the segments' records.
`word`: what a printout says about them. -/
structure Road where
  word : String
  /-- what a printout says about how the first state is computed -/
  start : String
  /-- `o` stands for the second hash function -/
  pub : SecondHashFunctionArgument → ByteArray → ByteArray → ByteArray → Except String Pub
  links : LinksBy

end ProofFile
