-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeySendJobs.lean: the three sendings of a key file's one-time chain (its first chain), each as a
job (`SendJob`) for the honest prover's part of a sending (`sendPart`; both in
Johnson/Desc/ProofFile/Honest/K1/Part.lean). A sending is the kind of sub-protocol that is named K1
(Johnson/Desc/K1/Send.lean): in its first round the prover sends the trees of its oracle messages,
in its second the answers to the samples on them. The three send the index-mask message, the
lookups' own message, whose main rows hold the multiplicities, and the vector W.
E2E/KeyBookHeldK1Jobs.lean shows, at the written sizes of the key and at every `ride` that passes
the test `ridesOk` (E2E/KeyBookHeldK1.lean), that the parts at these jobs state exactly what the key
file's book has for them (`Stated`, E2E/KeyBookLends.lean; the book, `keyBook`, E2E/KeyBook.lean, is
the public table of how many coins each part of the prover has). General in the chain's parameters
one (`OneTime`, OnBytes/Params/Chains.lean) and in every other argument. Executable definitions
only: no theorem is stated.

A job has four fields. `P` (`K1.Par`) holds the sending's public parameters, among them its place
(`Place`: the label of a sub-protocol) and the notices of its messages (`OracleNotice`: an oracle
message as it is announced). `first` is the number that the sending's first message gets. `ride`
gives an `Option Ride` for each message's number in the sending: a `Ride`
(Johnson/Desc/ProofFile/Honest/K1/Coins.lean) is a table that is sent along in a sending and whose
mask rows are computed from fewer coins than they have entries, a fold's fresh table. `data` gives
the entries of the main rows that are not coins, by message, main row and place; it is given the
input and a `Front` (Johnson/Desc/ProofFile/Honest/Sum.lean: the challenges heard before the part,
the state that the parts pass on, the rounds shown before the part). In each job `P` is `sendingPar`
(Johnson/Desc/Key/One.lean) at the arguments at which the block for the same sending has it in the
key file's description, its protocol as written in Lean (`sendIndexMasks`, `sendOwnMessage`,
`sendW`, same file), word for word. The data are made of `idxData`, `msgData` and `wAt`
(E2E/KeyArrays.lean).

In the list: the type parameter `W` is the type of the prover's input, not the vector W, and `X` is
the type of the state that the parts pass on. `entry w y c` is the entry in row y and column c of
the committed matrix, read from the input w. heard is a list of challenges (`Fmt.Drawn`), numbered
from 0. N (`Pieces`) holds the numbers of the chain's places; groups holds, for each message, the
groups that it is told to join.

  `idxJob one N groups first`: the job of the index-mask message's sending ("idx.1.send" in
    Johnson/Desc/Key/One.lean), with the one notice `one.indexMasks`. No table is sent along, and
    `data` is `idxData`, which gives no entry
  `msgJob entry one N groups first ride`: the job of the sending of the lookups' own message
    ("msg.1.send"), with the notices `Wf.messageOf one.ranges`. `data` is `msgData` at the matrix
    `entry w`: in message 0 the planes of the multiplicities. It reads the input only
  `wJob entry one N groups first ride points a`: the job of W's sending ("w.1.send"), with the
    notices that `linMessageW one.lin` (OnBytes/Iop/Lin.lean) returns; `none` where it returns none.
    `data` has in message 0 the vector `wVec` at the weights `wWeights`, placed in the main rows by
    `laidE` (Johnson/Prover/Send/Core.lean) at the library's layout of W (`linLayW`,
    OnBytes/Iop/Lin.lean). It reads the input and the challenges heard before the part
  `wWeights one points a heard`: the weights on the matrix's rows in the one row that the batching
    of the lookups' rows on the matrix ("batt.1.batt") passes on: `handedWeights` at `pileOf`
    (E2E/KeyPile.lean), at the points `points heard` and at the challenges that a names. It reads
    neither the input nor a coin
  `wVec one entry g c`: entry c of W. For c below `2 ^ one.lin.kCol` it is `wAt`: the sum over the
    matrix's rows y of the weight of y (`weightAt g y`, Johnson/Desc/Key/KeyWords.lean, read in the
    field by `readE`) times `entry y c`. From there on it is 0
  `BattAt`: a structure of three public numbers, each the number of a challenge in heard: `sigma`,
    the batching's own sample; `eps`, the element that joins the sumcheck's hiding polynomial to the
    claim; `first`, the challenge of the first column variable. The challenge of column variable
    number i is read at `first + i`
  `elemAt heard i`: the first element of challenge number i of heard; 0 where there is none

Limits.
- The `data` of none of the three jobs reads the rounds shown before the part (`Front.seen`) or the
  state that the parts pass on (`Front.own`).
- points, the three numbers of `BattAt`, the places' numbers N, first, ride and groups are
  parameters: whoever builds the jobs supplies them, and nothing here computes or tests them.
  `points heard i f` is meant to be the point of the claim on the keys of part number f of lookup
  number i, computed from the challenges heard.
- `BattAt` counts over all challenges that the part's state has heard, from 0. That list has one
  entry for each round played (`play`, `Step.hear`, in the frame,
  Johnson/Desc/ProofFile/Honest/Frame.lean); in the first chain these are the chain's own rounds.
- That the verifier's decision on a sending, as the key file's description has it (`K1.decideSend`,
  Johnson/Desc/K1/Own.lean), accepts what `sendPart` sends at these jobs is not shown. `sendPart`
  returns an error where `sendFits` (Johnson/Desc/ProofFile/Honest/K1/Coins.lean) rejects a job;
  that it accepts these jobs is not shown here. No run of a part is evaluated here, and at the key's
  full size a run is too large to be evaluated.
- W is not placed by `layVec` or `wData` (E2E/KeyArrays.lean), and no statement compares their rule
  with `laidE` at `linLayW`.
- Nothing on hiding follows from this file.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K1.Part
import Johnson.Desc.Key.One
import E2E.KeyArrays
import E2E.KeyPile

set_option autoImplicit false

namespace AtPublicFiles.Key
open OnBytes OnBytes.Params
open OnBytes.Slice (GF GE readE)
open ProofFile.Honest (Front)
open ProofFile.Honest.K1 (SendJob Ride sendFits)
open VerifiableInference.Desc.Key (sendingPar Pieces weightAt)

variable {W X : Type}

/-- The first element of challenge number i of the list heard, counted from 0; 0 where the list has
no such challenge or the challenge has no element. -/
def elemAt (heard : List Fmt.Drawn) (i : Nat) : E :=
  (((heard[i]?).bind (·.elems.head?)).map E.ofTriple).getD zeroE

/-- Three public numbers. Each is the number of a challenge, counted from 0, in the list of all
challenges that the part's state has heard: `sigma`, the batching's own sample; `eps`, the element
that joins the hiding polynomial to the claim; `first`, the challenge of the first column variable.
`wWeights` reads the challenge of column variable number i at `first + i`. -/
structure BattAt where
  sigma : Nat
  eps : Nat
  first : Nat

/-- The weights on the matrix's rows in the row that the batching passes on (`handedWeights` at
`pileOf`, E2E/KeyPile.lean), as a function of public parameters and of the challenges heard only. -/
def wWeights (one : OneTime) (points : List Fmt.Drawn → Nat → Nat → List E) (a : BattAt)
    (heard : List Fmt.Drawn) : List Tensor :=
  handedWeights (pileOf (Wf.matrixOf one.lin) one.ranges.lookups (points heard))
    (elemAt heard a.sigma) (elemAt heard a.eps)
    ((List.range (Wf.matrixOf one.lin).kCol).map fun i => elemAt heard (a.first + i))

/-- The job of the index-mask message's sending: no table is sent along; `data` gives no entry. -/
def idxJob (one : OneTime) (N : Pieces) (groups : List (List Nat)) (first : Nat) : SendJob W X :=
  { P := sendingPar one N.idx "the index masks" #[one.indexMasks] groups
    first := first, ride := fun _ => none, data := fun _ _ => idxData }

/-- The job of the sending of the lookups' own message, whose main rows hold the multiplicities,
with what is sent along with it (`ride`). `data` reads the input only; the last argument of
`msgData` is the message length `ell` of the base code that the message's shape names. -/
def msgJob (entry : W → Nat → Nat → GF) (one : OneTime) (N : Pieces) (groups : List (List Nat))
    (first : Nat) (ride : Nat → Option Ride) : SendJob W X :=
  { P := sendingPar one N.msg "the lookups' own message and what rides with it"
      (Wf.messageOf one.ranges) groups
    first := first, ride := ride
    data := fun w _ => msgData (entry w) (Wf.matrixOf one.lin).kCol one.ranges.lookups
      (one.codes.base.getD one.ranges.message.shape.code default).ell }

/-- W as a vector: entry c is `wAt` at the weights g for a column c of the matrix, and 0 from c =
`2 ^ one.lin.kCol` on. -/
def wVec (one : OneTime) (entry : Nat → Nat → GF) (g : List Tensor) (c : Nat) : GE :=
  if c < 2 ^ one.lin.kCol then wAt (fun y => readE (weightAt g y)) entry one.lin.matrixRows c else 0

/-- The job of W's sending, with what is sent along with it (`ride`). In message 0 the vector `wVec`
is placed in the main rows by `laidE` at the library's own layout of W (`linLayW`,
OnBytes/Iop/Lin.lean). `none` where the shape has no message with W (`linMessageW`). -/
def wJob (entry : W → Nat → Nat → GF) (one : OneTime) (N : Pieces) (groups : List (List Nat))
    (first : Nat) (ride : Nat → Option Ride) (points : List Fmt.Drawn → Nat → Nat → List E)
    (a : BattAt) : Option (SendJob W X) :=
  (linMessageW one.lin).map fun msg =>
    { P := sendingPar one N.w "W and what rides with it" msg groups
      first := first, ride := ride
      data := fun w front msg r j =>
        if msg = 0 then some (.inr (Johnson.Prover.Send.laidE (linLayW one.codes one.lin)
          (wVec one (entry w) (wWeights one points a front.heard)) r j)) else none }

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.elemAt
#print axioms AtPublicFiles.Key.BattAt
#print axioms AtPublicFiles.Key.wWeights
#print axioms AtPublicFiles.Key.idxJob
#print axioms AtPublicFiles.Key.msgJob
#print axioms AtPublicFiles.Key.wVec
#print axioms AtPublicFiles.Key.wJob
