-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConst.lean: THE SHARED TABLE's CONSTANT: ONE NAMED FILLING OF THE TABLE
OF THE PROOF FILE's SECOND CHAIN. The laws at the chain's twelve sub-protocols (our files call them
    blocks) speak of five things: the
table's numbers, its meaning, its promise, the slot's own condition, and the extractor. Each is a
term over many letters. HERE every letter has ONE name, over two structures, so that a statement
that names the constant keeps its words when a letter is closed by a term.

  ShPlan          the plan at the seat: the kind's parameters Q, the description G, the door's plan
                  p for the second part, K1's radii at the two sendings.
  ShOpen          THE OPEN LETTERS, a field each: what no term closes (the first table's side,
                  the decoder's, the numbering over all three chains). THE LIST IS MEANT TO SHRINK:
                  a field that is closed leaves this structure and becomes a definition below.
  Sh.sentU … Sh.X the closed letters, a definition each: the two sendings' messages and layouts ·
                  the first tree's number · the members, their numbers, the readers of words · the
                  three messages' shapes · the tests laid in the promise's slot (XW at Y := smpK).
  Sh.nums, Sh.mg, Sh.pm, Sh.own, Sh.ex   **THE FIVE**: tiedNumbers … · mgK … · pmK … · ocEnd … · exK
                  …: the ledger's filling, with the table's files' filling for "LIN point"
                  (mgJoint, pmPoint) beneath it.
WHERE Sh.own IS ASSERTED, AND WHERE READ. Sh.own is the first chain's whole promise at its last
border (ocEnd) AND "the handed state is a reached last state of the first chain" (R). It is ASSERTED
in two places alone: at the joint of the first and the shared chain, by whoever makes the promise's
start (ocEnd from the first table's last border; R from the first chain's own fold: endAt₁_of,
ReachLinks.lean); behind each accepting step of a sub-protocol of the shared chain, which does not
turn the handed state (the rides: ocWith_rides). It is READ in one way alone: as a hypothesis of a
law (onQ₂ … k a). No theorem over this constant may conclude it of a state that it did not get from
one of the two places, and none may spend a fold fact at a state of which R is not in hand.
  Sh.tests, Sh.Tests   THE NAMED TESTS ON THE PARAMETERS, each a Bool with its name; Tests: all
      accept (Johnson/Desc/K14/Law/SharedConstTests.lean).
  Sh.tests_*      what each test gives, in the form in which the ledger's theorems ask it.
WHAT IS NOT HERE. No law. That the seat's own value is this plan (the one premise of the counted
form) is owed from the seating. The chain's pieces and their written data are the row's, by make:
they are no letters of the table.
What is not claimed. No soundness of a verifier; no level. That the tests say yes at a real plan:
    not shown here.

-/
import Johnson.Desc.Sound.JointFilling
import Johnson.Desc.Sound.AtOcEnd
import Johnson.Desc.Sound.StoredAlong
import Johnson.Desc.Sound.LettersFirst
import Johnson.Desc.Sound.PointReached
import Johnson.Desc.K14.Law.LedgerDoor
import Johnson.Desc.K14.Law.LedgerLetters
import Johnson.Desc.K14.Law.LedgerReader
import Johnson.Desc.K14.Law.LedgerSmpKOwed
import Johnson.Desc.K14.Law.LedgerMembersOwed

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)

/-- **The parameters at the seat.** -/
structure ShPlan (Xi : Type) where
  /-- the kind's parameters on the shared chain -/
  Q : P14
  /-- the IOP as written in Lean (our files call it the description) -/
  G : FileDescription Xi
  /-- the parameters of the kind's second part, on the last chain -/
  p : P₁₄
  /-- K1's radii at "send o_u" and at "send o_omega", by the message's place in its sending -/
  rad2 : ℕ → ℕ
  rad5 : ℕ → ℕ
  /-- the written list of rounds, each with its error bound; which file: 2 a proof file, 0 a key
      file
  -/
  Wr : OnBytes.Params.Rounds
  fl : ℕ

/-- **The open letters.** A field that a term closes leaves this structure. -/
structure ShOpen (P₀ P₁ Cells Tok : Type) (Q : P14) where
  /-- one numbering of the tenants over all three chains -/
  arr : ℕ → ℕ → ℕ
  c₀ : Cells
  /-- the first table's side -/
  get : P₁ → P₀ × First.S
  smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf Q.codes s.l).om i).Smp
  ms₁ : List Mem
  N₁ : Numbers
  links : List ModelPart
  Mg₁ : Meaning P₀ (Wit Cells Tok MsgT)
  Pw : Where
  /-- "p is a reached last state of the first chain": another file's term (reached, at the first
      chain's last border); a letter until it is laid -/
  R : P₁ → Prop
  /-- "LIN point" -/
  matC : Cells → Nat → Nat → GE
  /-- the decoder's -/
  held : ((ixOf2 Q.par.S.fold 0 2852142980 (rankLib Q.par.S.fold)).Row ×
    Fin Q.par.S.fold.index.code.ell → GE) → Option Cells

namespace Sh

variable {Xi P₀ P₁ Cells Tok : Type} (A : ShPlan Xi) (O : ShOpen P₀ P₁ Cells Tok A.Q)

/-! ## The closed letters -/

/-- The messages of "send o_u". -/
def sentU : Array OracleNotice := (withU A.Q.S).getD #[]
/-- The two sendings' layouts of trees. -/
def layU : TreeLay := (layTrees A.Q.codes (sentU A)).getD default
def layO : TreeLay := (layTrees A.Q.codes (withOmega A.Q.S)).getD default
/-- The number of the shared chain's first tree, counted through the file. -/
def t₁ : ℕ := (VerifiableInference.Desc.oraclesOf A.G.first.blocksInOrder).length
/-- The sampled members, their numbers in the chain's statement, and who has which number. -/
def ms : List Mem := msSh A.Q.S (A.rad2 0) (A.rad5 0) (A.rad5 1) (t₁ A) (layU A) (layO A)
def oNo : Mem → ℕ := oNoSh (sentU A).size
def mem : ℕ → Option Mem :=
  memK A.Q.S (A.rad2 0) (A.rad5 0) (A.rad5 1) (t₁ A) (layU A) (layO A) (sentU A).size
def num : Msg2 → ℕ := numSh (sentU A).size
/-- The fixed reader of a typed message. -/
def rd : (x : Mem) → ((sigOf A.Q.codes x.1.l).om x.2).Msg → Part → ℕ → GE := rdK A.Q.codes
/-- How a sample is read off the chain's state. -/
def smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf A.Q.codes s.l).om i).Smp :=
  smpSt A.Q.codes (oNo A) stSh
/-- The letter Y: each of o_u, o_omega, o_sp passes K12's test on a member's sample. -/
def Y : ℕ → St → Bool :=
  smpK A.Q.codes A.Q.S.fold.u A.Q.S.omega A.Q.S.sharedSplit (sentU A).size
/-- **The tests laid in the promise's slot**: XK with the door, at the plan's three shapes. -/
def X : ℕ → St → Bool :=
  XW A.Q (sentU A) (layU A) (layO A) (A.Q.S.fold.u, A.Q.S.omega, A.Q.S.sharedSplit, Y A)
    (sentU A).size A.p

/-- The first chain's statement, read off its state. -/
def stOf₁ : P₀ × First.S → Statement := stFirst
/-- The decoder's rank: the library's. -/
def rank : ((Fin A.Q.par.S.fold.index.v → Bool) →
    Fin (A.Q.par.S.fold.index.code.r + A.Q.par.S.fold.index.code.ell) → GE) → Nat :=
  rankLib A.Q.par.S.fold
/-- W's member: the first of the first chain's sampled members that sits at W's number. (Where there
is none: a member of the shared chain's, which no theorem then reads.) -/
def xW : Mem :=
  (O.ms₁.find? fun m => decide (m.1.seat m.2 = O.N₁.w)).getD
    (memSh A.Q.S (A.rad2 0) (A.rad5 0) (A.rad5 1) (t₁ A) (layU A) (layO A) .oU)
/-- The reader of the witness's tables at the first chain's state: by that state's own book. -/
def tabP₁ : P₀ × First.S → Wit Cells Tok MsgT → Nat → MsgT :=
  tabFirst O.arr
/-- "LIN point"'s row weights, read off what the first chain's reader gives at the handed state. -/
def gOf : P₁ → Nat → GE := gLaid O.Pw O.get

/-- The first chain's places, as the table's walk lists them. -/
def ps : List VerifiableInference.Desc.Place :=
  VerifiableInference.Desc.First.flatPlaces true O.links true

/-- Two idle values: every field that is read of them is overlaid by the fillings above them. -/
def idleM : MeaningS St P₁ (Wit Cells Tok MsgT) :=
  { pin := fun _ _ _ _ _ => True, pinT := fun _ _ _ => True, pin₁ := fun _ _ _ _ _ => True
    nearU := fun _ _ _ => True, recRow := fun _ _ => True, omU := fun _ _ => True
    row := fun _ _ _ => True, claimM := fun _ _ _ => True, dot := fun _ _ _ _ => True
    ev := fun _ _ _ => True, unmarked1 := fun _ => True }
def idleP : PromMeaning St :=
  { tablePromise := fun _ _ => True, noColl := fun _ _ _ _ => True, shown := fun _ _ _ => True
    held := fun _ _ _ => true, shape := fun _ _ => true, nothingLeft := fun _ => true }

/-! ## The five -/

/-- **The numbers.** -/
def nums : NumbersS := tiedNumbers O.N₁ (numbersSh (t₁ A) (layU A) (layO A) (0, 0) (0, 0))

/-- The decoder of the table. -/
def decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells :=
  decK A.Q.par 0 2852142980 (rank A) O.held

/-- **The first table's own meaning.**

The law at "LIN point" asks what the joint says of five fields: four as equations and the
fifth, one way, at reached states (Sh.Joint, Johnson/Desc/K14/Law/SharedConstJoint.lean): so the two
tables meet at the joint in one text. -/
def mg₁ : Meaning P₀ (Wit Cells Tok MsgT) := O.Mg₁

/-- **The slot's own condition**: the first chain's whole promise at its last border, at a reached
last state of the first chain. The fenced condition is asserted only of states that a run or a fold
hands on; no law may read it at a state that it did not get from one. -/
def own : P₁ → Strs → Prop := ocWith (ocEnd O.get O.N₁ (mg₁ A O) O.links (ps A O)) O.R

theorem own_ocEnd {p : P₁} {y : Strs} (h : own A O p y) :
    ocEnd O.get O.N₁ (mg₁ A O) O.links (ps A O) p y := h.1

theorem own_R {p : P₁} {y : Strs} (h : own A O p y) : O.R p := h.2

/-- The table's files' filling for "LIN point", beneath the ledger's. -/
def pm₀ : PromMeaning St :=
  pmPoint A.Q.codes A.G (smp₂ A) (ms A) A.Q.par 0 2852142980 (rank A) O.held
    (fun s : St => s.st) (fun s : St => shiftBook (nums A O).lo s.book) (pmZ A.Q.par idleP)
def mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT) :=
  tiedMeaning O.get (mg₁ A O)
    (mgJoint A.Q.codes A.G O.arr O.get O.smp₁ O.ms₁ (xW A O) (smp₂ A) (ms A)
      (linLayW A.Q.codes O.Pw.lin) (fun q => stOf₁ (O.get q)) (fun q => tabP₁ A O (O.get q))
      (rgOf A.Q.codes O.arr (mem A) (rd A)) (omWK A.Q.codes O.arr (mem A) (rd A) (sentU A).size A.Q)
      A.Q.par 2852142980 (gOf A O) 0 2852142980 (rank A) O.held O.Pw O.matC
      (mgZ A.Q.codes O.arr (mem A) (rd A) (num A) idleM))

/-- **The meaning.** -/
def mg : MeaningS St P₁ (Wit Cells Tok MsgT) :=
  mgK A.Q.codes A.G O.arr (smp₂ A) (ms A) (decT₂ A O) (mg₀ A O) (mem A) (rd A) 2852142980
    A.Q.S.fold.columns (sentU A).size A.Q

/-- **The promise.** -/
def pm : PromMeaning St :=
  pmK A.Q.codes A.G (smp₂ A) (ms A) (decT₂ A O) (shiftBook (nums A O).lo) (pm₀ A O)
    A.Q.S.fold.columns 0 (sentU A).size A.Q (X A)

/-- **The extractor.** -/
def ex (Fr : Frame) :=
  exK (Tok := Tok) A.Q.codes A.G O.arr (smp₂ A) (ms A) (decT₂ A O) O.c₀ (nums A O) Fr

end Sh

end Desc.K14.Law
