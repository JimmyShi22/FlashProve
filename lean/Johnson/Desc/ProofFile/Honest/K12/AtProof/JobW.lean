-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/JobW.lean: what a caller supplies at the proof file's last
chain's proximity test (the place W): the job on a group of three members (`ManyJob`, RunMany.lean
in the folder above): the index-mask message, W, Omega: each member's rows by its own sender's text.
The state on entry, the sendings and the readers are parameters. Definitions with code, statements
and proofs.

  `csAt`, `csAt_f`, `csAt_e`, `rowsR_csAt`   a member's stretch, placed where its message's coins
                 begin; and `rowsR` at it is `rowsR` at any purse that agrees with the stretch on
                 the message's own coins
  `tabG`, `psOfRows`   one message's rows, as lists of words
  `memShape`, `memK1`   a message of a sending of the kind K1 as a member: K1's own `rowsR`
  `shapesW`, `treesW`   the members' shapes; what the first round of positions opens
  `jobW`        the job
  `jobW_members`, `jobW_fresh`, `jobW_p`, `msgOf_atPoint`   its public fields, by unfolding
  `wordsOfTrees`, `widthsB`, `widthsW`   a closed test: the trees' depths and widths are those of
                 the written place

Who hands what. The index-mask message: the first opening's job (`K1.firstJob`). W: W's sending's
job (`K1.wJobAt`), whose data D is a letter here: no filling holds that half
(K1/Law/RecordAtW.lean's head). Omega: `memOfSending` (JobShared.lean) at `K14.jobOmega`, with the
number of "LIN point" moved by n₁: the last chain's challenges begin with the first chain's
(`Ready.start₃`, Honest/Frame.lean; `heardFrom`, Honest/ForKinds.lean), and `omegaHonE` reads its
challenge by that number.

What may be said here on hiding, and no more
(a rule of use for whoever builds on this file;
no theorem):
«The state on entry reads the instance's public part, the rounds shown, and ALL columns opened in
front of this test, in the order of reading: the first chain's, the shared chain's, the last
chain's own. They are computed from the witness, the index, the stored tables' pads and encoding
randomness, AND THE RUN's COINS. Never a word on a simulator at this place without «given the
instance's public part, the rounds shown and all columns opened in front, in all three chains».
But for the stored tables' columns no one can hand a simulator these from outside: the simulators
of EVERY part in front must have made them: this test stands last, and its «given» is the whole
view in front. At a called part of the walk the field begins with the two earlier chains' views'
own columns (door_last_at_called); that what follows them are the last chain's view's is not
typed, and that each tree's budget counts them is typed by nobody.»

Limits.
- All parameters are tied to nothing here: q, `door`, the two K1 jobs, A, `readers`, `wit`, `ask`
  and n₁. n₁ is a duty of whoever lays the job: computed from the description's own list, not
  written by hand (Honest/ForKinds.lean), and it counts the sealing round's challenge.
- That `jobW`'s members are `membersW` at these sendings is `jobW_members` against `membersW`'s
  text; W's `msgK1` there takes no ride, and `membersW` lays all of W's sending but its last: the
  two agree where the sending has two messages and its ride is none at message 0.
- `firstsOf` lays the blocks in the job's order; that this is the order of the verifier's group is
  tried by nothing here: no `layFits` at W.
- jobW takes any K1 jobs: that a longer `heard` is harmless holds of jobs made by `firstJob` and
  `placeJob`, whose data cuts it (`RowData.at_`), by reading.
- `trees` is written by hand, off the written place's `first`; `widthsW` holds depths and widths,
  not which row lies where.
- Nothing here shows that a row read here is the row that the sender sent: that is a tie between
  `memK1`'s stretch and the book (the like at one member: CoinsTieBook.lean in the folder above).
- `Stretch` has lost its count; `csAt` reads it from the message's start on.
- No job is laid in a filling. `secondOf` (Doors.lean) takes it; nothing calls that here.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean in the folder above.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.MembersW
import Johnson.Desc.ProofFile.Honest.K12.JobShared
import Johnson.Desc.ProofFile.Honest.K12.RunJob
import Johnson.Desc.ProofFile.Honest.K1.PlaceW
import Johnson.Desc.ProofFile.Honest.K1.CoinsIn
import Johnson.Desc.ProofFile.Honest.K12.RowsCongr
import Johnson.Desc.K1.Law.TiesWritten
import Johnson.Desc.K12.Law.PlacesFull
import Johnson.Desc.ProofFile.Honest.K12.FitAtHead
import Johnson.Prover.Send.Front

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open OnBytes (OracleShape)
open OnBytes.Slice (GE ofE)
open Fmt.M1 (Stage)
open Fmt.M1.Own (PSt)
open Johnson.Prover.Send (Rows shapeAt)
open VerifiableInference.Desc.K12 (P12 T12)
open ProofFile.Honest.K12.Light (ManyJob Mem MemShape Piece firstsOf memOfSending depthOf treesOf selsOf)
open ProofFile.Honest.K14 (Ask)

variable {W X : Type}

/-- The coins of a count d, read off a stretch S whose coins begin at a. BELOW a EVERY PLACE READS
THE STRETCH's COIN 0 (the subtraction stops at 0); BEYOND THE STRETCH's COUNT A PLACE READS WHAT THE
STRETCH's MAKER GIVES (`stretchOf`: 0). `rowsR_csAt`: at message k neither is read. -/
def csAt (d a : Due) (S : Stretch) : Cs d :=
  ⟨fun i => S.f (i.val - a.f), fun i => S.e (i.val - a.e)⟩

/-- Coin number i of the stretch stands at a + i. -/
theorem csAt_f (d a : Due) (S : Stretch) (i : Nat) (h : a.f + i < d.f) :
    (csAt d a S).f ⟨a.f + i, h⟩ = S.f i := by
  show S.f (a.f + i - a.f) = _
  rw [Nat.add_sub_cancel_left]

/-- The same in the extension field. -/
theorem csAt_e (d a : Due) (S : Stretch) (i : Nat) (h : a.e + i < d.e) :
    (csAt d a S).e ⟨a.e + i, h⟩ = S.e i := by
  show S.e (a.e + i - a.e) = _
  rw [Nat.add_sub_cancel_left]

/-- **At message k `rowsR` reads the placed stretch only at `startR k + i`, i below the member's
count**: at any purse c that agrees with the stretch on the message's own coins the rows are those
at c: what stands below the start or beyond the count is not read. -/
theorem rowsR_csAt (P : VerifiableInference.Desc.K1.Par) (ride : Nat → Option K1.Ride)
    (data : Nat → Nat → Nat → Option (OnBytes.Slice.GF ⊕ GE)) (k : Nat) (hk : k < P.sent.size)
    (S : Stretch) (c : Cs (K1.dueR P ride))
    (hf : ∀ i, i < (K1.dueMsg P.codes (shapeAt P k) (ride k)).f →
      K1.cf c ((K1.startR P ride k).f + i) = S.f i)
    (he : ∀ i, i < (K1.dueMsg P.codes (shapeAt P k) (ride k)).e →
      K1.ce c ((K1.startR P ride k).e + i) = S.e i) :
    K1.rowsR P ride data (csAt _ (K1.startR P ride k) S) k = K1.rowsR P ride data c k := by
  refine ProofFile.Honest.K12.rowsR_congr P ride data _ _ k (fun i hi => ?_) fun i hi => ?_
  · have hb := K1.msg_in_f P ride k hk
    have h : (K1.startR P ride k).f + i < (K1.dueR P ride).f := by omega
    rw [hf i hi]
    show (if h' : _ then _ else _) = _
    rw [dif_pos h]
    exact csAt_f _ _ S i h
  · have hb := K1.msg_in_e P ride k hk
    have h : (K1.startR P ride k).e + i < (K1.dueR P ride).e := by omega
    rw [he i hi]
    show (if h' : _ then _ else _) = _
    rw [dif_pos h]
    exact csAt_e _ _ S i h

/-- r rows of n entries, as words. -/
def tabG (r n : Nat) (f : Nat → Nat → GE) : List (List Fmt.M1.E) :=
  (List.range r).map fun i => (List.range n).map fun j => ofE (f i j)

/-- **One message's rows in full, as lists of words.** `P := []`, `Pi := []`: the two fields that
`layFirst` does not read (RunLay.lean); no coin is due there: the first stage's fresh table comes of
the fresh stretch (Parts.lean). The default at `codes.mask.getD` hangs on P alone, and `widthsW`
holds the trees' widths at the written sizes. -/
def psOfRows (P : VerifiableInference.Desc.K1.Par) (k : Nat) (V : Rows) : PSt :=
  let s := shapeAt P k
  let c := P.codes.base.getD s.code default
  let z := P.codes.mask.getD s.maskCode default
  { M := tabG s.mainRows c.ell (V.main (s.mainDeg == 3))
    Rh := tabG s.mainRows c.r (V.mainTl (s.mainDeg == 3))
    W := tabG s.maskRows z.ell V.mask, Sg := tabG s.maskRows z.r V.maskTl, P := [], Pi := [] }

/-- A member's public numbers. fs: the first rows of its blocks. -/
def memShape (s : OracleShape) (fs : Option Nat × Option Nat) : MemShape :=
  ⟨fs.1.getD 0, s.mainRows, fs.2.getD 0, s.maskRows, s.mainDeg == 1⟩

/-- **Message number k of a sending of the kind K1, as a member.** lift: the sending's input, of the
test's. at_: the address of the sending's part. The rows are K1's `rowsR`, at the test's front. -/
def memK1 {Wd : Type} (J : K1.SendJob Wd X) (lift : W → Wd) (at_ : Addr) (k : Nat)
    (fs : Option Nat × Option Nat) : Mem W X :=
  { sent := msgK1 at_ J.P J.ride k
    shape := memShape (shapeAt J.P k) fs
    rows := fun w fr S => psOfRows J.P k (K1.rowsR J.P J.ride (J.data (lift w) fr)
      (csAt _ (K1.startR J.P J.ride k) S) k) }

/-- The three members' shapes. PI, PW: the two K1 sendings. sO: Omega's. -/
def shapesW (PI PW : VerifiableInference.Desc.K1.Par) (sO : OracleShape) : List OracleShape :=
  [shapeAt PI (PI.sent.size - 1), shapeAt PW 0, sO]

/-- What the first round of positions opens: the index-mask message's tree; W's, with the fresh
table; Omega's. -/
def treesW (q : P12) : List (Nat × List Piece) :=
  [(depthOf q 0, [.mask 0]), (depthOf q 1, [.main 1, .mask 1, .fresh]), (depthOf q 2, [.main 2])]

/-- **The job at the last chain's proximity test.** q: the test's parameters. door: the state on
entry, a parameter. JI, JW: the first opening's and W's sendings. A: the shared sendings' public
data. readers, wit, ask: their inputs, of the test's. n₁: how many challenges the first chain
has. `memOfSending`'s last `none`: no vector is handed: Omega's rows are its own data at `ask`. -/
def jobW {Xi : Type} (q : P12) (door : W → Front X → T12) (JI : K1.SendJob Readers X)
    (JW : K1.SendJob (K1.PlaceIn Xi) X) (A : ProofFile.Honest.K14.SendPub) (readers : W → Readers)
    (wit : W → K1.PlaceIn Xi) (ask : W → Ask) (n₁ : Nat) : ManyJob W X :=
  let JO := ProofFile.Honest.K14.jobOmega ⟨A.P, n₁ + A.atPoint⟩
  let fs := firstsOf (shapesW JI.P JW.P (JO.Q.sent.getD 0 default).shape)
  { p := q
    mems :=
      [memK1 JI readers senderI (JI.P.sent.size - 1) (fs.getD 0 (none, none)),
       memK1 JW wit senderW 0 (fs.getD 1 (none, none)),
       memOfSending JO senderO 0 (fs.getD 2 (none, none)) ask none]
    fresh := some (senderW, JW.P.sent.size - 1), rec₀ := door
    trees := treesW q }

section Fields
variable {Xi : Type} (q : P12) (door : W → Front X → T12) (JI : K1.SendJob Readers X)
  (JW : K1.SendJob (K1.PlaceIn Xi) X) (A : ProofFile.Honest.K14.SendPub) (readers : W → Readers)
  (wit : W → K1.PlaceIn Xi) (ask : W → Ask) (n₁ : Nat)

/-- Its parameters. -/
theorem jobW_p : (jobW q door JI JW A readers wit ask n₁).toRun.toTest.p = q := rfl

/-- **Its members are the group**: the first sending's last message; W's message 0; Omega's. -/
theorem jobW_members : (jobW q door JI JW A readers wit ask n₁).toRun.toTest.members =
    [msgK1 senderI JI.P JI.ride (JI.P.sent.size - 1), msgK1 senderW JW.P JW.ride 0,
      msgOf senderO (ProofFile.Honest.K14.jobOmega ⟨A.P, n₁ + A.atPoint⟩) 0] := rfl

/-- The first fresh table is the last message of W's sending. -/
theorem jobW_fresh : (jobW q door JI JW A readers wit ask n₁).toRun.toTest.fresh =
    some (senderW, JW.P.sent.size - 1) := rfl

end Fields

/-- A message's count does not read the number of "LIN point". -/
theorem msgOf_atPoint (a : Addr) (P : Desc.K14.P14) (m m' k : Nat) :
    msgOf a (ProofFile.Honest.K14.jobOmega ⟨P, m⟩) k = msgOf a (ProofFile.Honest.K14.jobOmega ⟨P, m'⟩) k := by
  simp only [msgOf, ProofFile.Honest.K14.jobOmega]

/-- A tree's depth and its words: a row over the base field is one word, others three. -/
def wordsOfTrees (s : Stage) (ms : List MemShape) (ts : List (Nat × List Piece)) :
    List (Nat × Nat) :=
  (treesOf s ms ts).map fun T => (T.1, (T.2.map fun r => if r.base then 1 else 3).sum)

/-- The test: at the written sendings and Omega's shape, the trees have the written place's depths
and words. -/
def widthsB (sO : OracleShape) : Bool :=
  let sh := shapesW VerifiableInference.Desc.K1.parGF VerifiableInference.Desc.K1.parWF sO
  let fs := firstsOf sh
  let ms := sh.zipIdx.map fun x => memShape x.1 (fs.getD x.2 (none, none))
  wordsOfTrees (H2K.Member.piWFull.nums.stages.headD default) ms (treesW H2K.Member.piWFull) ==
    H2K.Member.piWFull.nums.first.map fun x => (x.1.a, x.1.W)

set_option maxRecDepth 1000000 in
/-- **The trees' depths and widths are the written place's**, at the typed sizes over a proof file's
own codes, Omega's shape by its sending. An evaluation in Lean's kernel. -/
theorem widthsW : (VerifiableInference.Desc.K1.realSized.all fun y =>
    widthsB (((ProofFile.Honest.K14.jobOmega (ProofFile.Honest.K12.Light.planOf y.2 y.1.shape)).Q.sent.getD 0
      default).shape)) = true := by decide +kernel

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.csAt
#print axioms ProofFile.Honest.K12.AtProof.csAt_f
#print axioms ProofFile.Honest.K12.AtProof.csAt_e
#print axioms ProofFile.Honest.K12.AtProof.rowsR_csAt
#print axioms ProofFile.Honest.K12.AtProof.msgOf_atPoint
#print axioms ProofFile.Honest.K12.AtProof.tabG
#print axioms ProofFile.Honest.K12.AtProof.psOfRows
#print axioms ProofFile.Honest.K12.AtProof.memShape
#print axioms ProofFile.Honest.K12.AtProof.memK1
#print axioms ProofFile.Honest.K12.AtProof.shapesW
#print axioms ProofFile.Honest.K12.AtProof.treesW
#print axioms ProofFile.Honest.K12.AtProof.jobW
#print axioms ProofFile.Honest.K12.AtProof.jobW_p
#print axioms ProofFile.Honest.K12.AtProof.jobW_members
#print axioms ProofFile.Honest.K12.AtProof.jobW_fresh
#print axioms ProofFile.Honest.K12.AtProof.wordsOfTrees
#print axioms ProofFile.Honest.K12.AtProof.widthsB
#print axioms ProofFile.Honest.K12.AtProof.widthsW
