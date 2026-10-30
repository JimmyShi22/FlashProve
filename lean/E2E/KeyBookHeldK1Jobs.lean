-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyBookHeldK1Jobs.lean: the honest prover's parts for the three sendings of the key file's first
chain state exactly what the key file's book of coins has for them (`Stated`,
E2E/KeyBookLends.lean). The three sendings are the index-mask message, the multiplicities and W. The
parts are `sendPart` (Johnson/Desc/ProofFile/Honest/K1/Part.lean) at the jobs `idxJob`, `msgJob` and
`wJob` (E2E/KeySendJobs.lean). The three theorems are corollaries of `idx_stated`, `msg_stated` and
`w_stated` (E2E/KeyBookHeldK1.lean). They are at the written sizes of the full size only (`keyFull`,
Johnson/Goal/PlanValues/KeySizedReturns.lean) and are general in the jobs' other parameters.
`Stated` is the hypothesis on each part under which `key_lends` (E2E/KeyBookLendsNamed.lean) shows
that the frame (Johnson/Desc/ProofFile/Honest/Frame.lean: the types in which an honest prover is
written, and the functions that run it) gives the parts at a place their coins. Definitions,
theorems, and two tests that are theorems by evaluation in Lean's kernel.

Terms; the head of E2E/KeyBookHeldK1.lean has more. A book (`ProverCoinCounts`, in the frame) is the public
table of how many coins (random field elements) each part of a prover has; here it is `keyBook K`
(E2E/KeyBook.lean), computed from the public data K (`KeyPub`). A place (`Place`) is the label of a
sub-protocol; an address (`Addr`) is a place and the number of a part there. An entry (`Ahead`) is a
block of the coins of one part, its owner, that one other part, its spender, is given too.
`Stated B rows a p` says that three fields of the part p are what B has for the address a: its own
count of coins (`takes`) is the count of a's row in the table rows (0 if it has none), and the names
and counts of the entries that it spends and carries are those of the entries of B whose spender is
a. A notice (`OracleNotice`) is an oracle message as it is announced; a sending is the list of the
oracle messages of one prover's message. A job (`SendJob`) is what a caller gives `sendPart`: among
its fields are `P`, the sending's parameters (`K1.Par`, Johnson/Desc/K1/Send.lean, with the codes
`P.codes` and the notices `P.sent`), and `ride`, an `Option Ride` for each message's number, from 0.
A `Ride` (Johnson/Desc/ProofFile/Honest/K1/Coins.lean) is a table in a sending whose mask rows are
computed from fewer coins than they have entries: a fold's fresh table, given by the fold's rounds
`k` and a number `h` (2 ^ h rows); it has 2 k + 1 coins (`Ride.count`). A fill (`Fill`,
E2E/KeyBook.lean) says how a message's mask table is made of coins. `ridesOk ride ns k`
(E2E/KeyBookHeldK1.lean) is the executable test that, at every j below the size of ns, `ride j` and
the `Option Ride` of the fill that `fillOf k` gives notice number j are both `none` or have the same
`count`. The parameter one (`OneTime`, OnBytes/Params/Chains.lean) is what the parameter bytes of a
key's one-time chain hold; that chain is the key file's first.

  `idxJob_stated`, `msgJob_stated`, `wJob_stated`: under hK and h below, `sendPart` at `idxJob`, at
    `msgJob` and at every job that `wJob` returns is `Stated` at `keyBook K`, at the first chain's
    table `(keyBook K).first` and at the address ⟨idxPlace, 0⟩, ⟨msgPlace, 0⟩, ⟨wPlace, 0⟩. The
    second and the third hold at every `ride` that passes `ridesOk` at the written notices (hr); the
    `ride` of `idxJob` is `none` at every number. General in N, groups, first, entry, points and a,
    and in the types V, W and X
  `rides_full`: three values of `ride` pass `ridesOk` at the written notices: the one of `idxJob`,
    at the one notice `keyFull.once.input` and k = 0; `rideMsg`, at `Wf.messageOf keyFull.ranges.x`
    and `kRanges`; `rideW`, at the array that `linMessageW keyFull.once.shape` returns and `kOwn`.
    So `rideMsg` and `rideW` meet hr. By evaluation in Lean's kernel (`decide +kernel`)
  `rides_full_no`: a negative test: `rideW` fails `ridesOk` at the notices and the k at which
    `rideMsg` passes it. By evaluation in Lean's kernel
  `OneFull one`: a structure of four equations: the fields `codes`, `indexMasks`, `ranges` and `lin`
    of one are `keyFull.codes`, `keyFull.once.input`, `keyFull.ranges.x` and `keyFull.once.shape`:
    the codes, the index-mask message's notice, the public parameters of the proof of the ranges,
    and the shape of the test on the table. From these four fields the jobs' codes and notices are
    computed
  `rideMsg`, `rideW`: definitions: a `ride` for the sending of the multiplicities and one for W's.
    Each has a `Ride` at message number 1 and `none` at every other number: `rideMsg` one of 4
    rounds with h = 4, `rideW` one of 5 rounds with h = 1

By what. Each theorem is `idx_stated`, `msg_stated` or `w_stated` at the job. The job's codes are
`one.codes` by the definition of `sendingPar` (Johnson/Desc/Key/One.lean), so `h.codes` gives the
hypothesis on the codes. `sendingPar_sent` (E2E/KeyBookHeldK1.lean) says that the job's notices are
the array that `sendingPar` is given; by `h.idx`, `h.ranges` or `h.lin` that array is the written
one. The hypothesis on `ride` is the first clause of `rides_full`, or hr. `wJob_stated` first
unfolds `wJob` to get the array that `linMessageW` returns. Definitions: `fullPub`
(E2E/KeyBookAtWritten.lean); `kRanges`, `kOwn` (E2E/KeyBookHeldK1.lean); the places
(E2E/KeyPlaces.lean); `Wf.messageOf` (OnBytes/Iop/Wf.lean); `linMessageW` (OnBytes/Iop/Lin.lean).

Hypotheses. hK: `fullPub = some K`: K is the public data of the written sizes; `full_made`
(E2E/KeyBookPassesNamed.lean) shows that there is such a K. h: `OneFull one`. hr, of
`msgJob_stated`: `ridesOk ride` is true at `Wf.messageOf keyFull.ranges.x` and `kRanges`. hr, of
`wJob_stated`: `linMessageW keyFull.once.shape` returns an array, and `ridesOk ride` is true at it
and `kOwn`. hJ, of `wJob_stated`: `wJob` returns the job J; it returns nothing where
`linMessageW one.lin` returns nothing.

Limits.
- All limits of E2E/KeyBookHeldK1.lean. Among them: counts only. A sending's part spends and carries
  nothing. Which coin the part puts where in its rows is not compared with the book's order, except
  for where each message's coins begin (`starts_held`, E2E/KeyBookHeld.lean, at the tables
  `ridesOf P k`).
- The field `h` in `rideMsg` and in `rideW`, which says how many rows the table has, is compared
  with nothing here: `ridesOk` compares `Ride.count`, which reads the rounds `k` only. The test that
  reads `h` is `rideFits`, a clause of `sendFits` (K1/Coins.lean). Neither is evaluated here, and
  where a job fails `sendFits` both moves of `sendPart` return an error.
- Everything is at the one value `keyFull`. `OneFull one` is a hypothesis: it is proved of no value
  here. `five_in_scope` (Johnson/RunOne/Law/KeyInScope.lean) proves its four equations, under its
  own hypotheses, of `X.Y.k.oneTime`, where X is the source of the key file's description at public
  files in scope. It is not called here.
- `OneFull` says nothing of the fields `given` and `binding` of one. The jobs' parameters read
  `given` too (`P.gp`: the number of answers to a sample); the theorems need nothing of it.
- The place in a job's own parameters has the number `N.idx`, `N.msg` or `N.w`, and N is a free
  parameter. Nothing says that this place is the place of the address (`idxPlace`, `msgPlace`,
  `wPlace`).
- `sendPart` and `SendJob` are defined in K1/Part.lean, `Ride` and the part's count `dueR` in
  K1/Coins.lean; this file gets them through E2E/KeyBookHeldK1.lean and E2E/KeySendJobs.lean. If
  `(sendPart J).takes` is no longer `dueR J.P J.ride`, `takes_held` (E2E/KeyBookHeldK1.lean) no
  longer compiles, and with it the three theorems here.
- No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import E2E.KeyBookHeldK1
import E2E.KeySendJobs

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyBook
open OnBytes OnBytes.Params
open OnBytes.Slice (GF)
open ProofFile.Honest.K1 (Ride SendJob sendPart)
open VerifiableInference.Desc.Key (Pieces)
open AtPublicFiles.Key (idxJob msgJob wJob BattAt)
open Lk6.AtPlan (keyFull)

variable {V W X : Type}

/-- The four fields of the one-time chain's parameters from which the jobs' codes and notices are
computed are the written values of `keyFull`. -/
structure OneFull (one : OneTime) : Prop where
  codes : one.codes = keyFull.codes
  idx : one.indexMasks = keyFull.once.input
  ranges : one.ranges = keyFull.ranges.x
  lin : one.lin = keyFull.once.shape

/-- A `ride` for the sending of the multiplicities: at message number 1, from 0, a fold's fresh
table of 4 rounds, with h = 4; `none` at every other number. -/
def rideMsg (i : Nat) : Option Ride := if i == 1 then some ⟨4, 4⟩ else none

/-- A `ride` for W's sending: at message number 1, from 0, a fold's fresh table of 5 rounds, with
h = 1; `none` at every other number. -/
def rideW (i : Nat) : Option Ride := if i == 1 then some ⟨5, 1⟩ else none

theorem rides_full : ridesOk (fun _ => none) #[keyFull.once.input] 0 = true ∧
    ridesOk rideMsg (Wf.messageOf keyFull.ranges.x) kRanges = true ∧
    ((linMessageW keyFull.once.shape).map fun w => ridesOk rideW w kOwn) = some true := by
  decide +kernel

/-- A negative test: at the notices of the sending of the multiplicities, `ridesOk` rejects `rideW`,
put in the place of `rideMsg`. -/
theorem rides_full_no : ridesOk rideW (Wf.messageOf keyFull.ranges.x) kRanges = false := by
  decide +kernel

section
variable (K : KeyPub) (hK : fullPub = some K) (one : OneTime) (h : OneFull one) (N : Pieces)
  (groups : List (List Nat)) (first : Nat)
include hK h

theorem idxJob_stated :
    Stated (keyBook K) (keyBook K).first ⟨idxPlace, 0⟩
      (sendPart (V := V) (idxJob (W := W) (X := X) one N groups first)) :=
  idx_stated K hK _ h.codes (by rw [← h.idx]; exact sendingPar_sent _ _ _ _ _) rides_full.1

theorem msgJob_stated (entry : W → Nat → Nat → GF) (ride : Nat → Option Ride)
    (hr : ridesOk ride (Wf.messageOf keyFull.ranges.x) kRanges = true) :
    Stated (keyBook K) (keyBook K).first ⟨msgPlace, 0⟩
      (sendPart (V := V) (msgJob (X := X) entry one N groups first ride)) :=
  msg_stated K hK _ h.codes (by rw [← h.ranges]; exact sendingPar_sent _ _ _ _ _) hr

theorem wJob_stated (entry : W → Nat → Nat → GF) (ride : Nat → Option Ride)
    (hr : ((linMessageW keyFull.once.shape).map fun w => ridesOk ride w kOwn) = some true)
    (points : List Fmt.Drawn → Nat → Nat → List E) (a : BattAt) (J : SendJob W X)
    (hJ : wJob entry one N groups first ride points a = some J) :
    Stated (keyBook K) (keyBook K).first ⟨wPlace, 0⟩ (sendPart (V := V) J) := by
  unfold wJob at hJ
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.1 hJ
  rw [h.lin] at hw
  rw [hw] at hr
  exact w_stated K hK _ h.codes w hw (sendingPar_sent _ _ _ _ _) (Option.some.inj hr)

end

end AtPublicFiles.KeyBook

#print axioms AtPublicFiles.KeyBook.rides_full
#print axioms AtPublicFiles.KeyBook.rides_full_no
#print axioms AtPublicFiles.KeyBook.idxJob_stated
#print axioms AtPublicFiles.KeyBook.msgJob_stated
#print axioms AtPublicFiles.KeyBook.wJob_stated
#print axioms AtPublicFiles.KeyBook.OneFull
#print axioms AtPublicFiles.KeyBook.rideMsg
#print axioms AtPublicFiles.KeyBook.rideW
