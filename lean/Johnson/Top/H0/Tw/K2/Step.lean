-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/Tw/K2/Step.lean: the kind «the code switch», third file: THE SWITCH's ROW AT ONE STEP
TYPE (Step S := S → List Fmt.RoundView → List Col → Option (S × Nat): the step
says how many columns it took): a later link's first call, and the finish's switch, each as ONE step
that takes BOTH rounds («SEND seed» · «LOC»).

  S9        what crosses the border: the statement · the book · the roots received · the frame (the
  program's ReqFrame, whole) · the plain
            scalars that the row in front has heard (the round «REPLY»'s; none elsewhere) · whether
            the round closed last owes a count.
  Par9      what the step has of the plan and the place: the chain's first tree's number · the
  answers to a sample · the two rounds' entries.
  SendFn    THE SENDING AS A PLAIN FUNCTION, with the program's flag ownRound := false: AN ARGUMENT
  OF THE STEP:
            statement · book · roots · the announcements · the seed's entry · whether the round
            before owes a count · the two rounds ↦
            statement · book · roots · the messages' numbers · HOW MANY ITEMS OF THE SECOND ROUND IT
            TOOK | a refusal.
  firstE | firstStep     a later link's first call (with the words of the refusal | at the one type)
  finishE | finishStep   the finish's switch; it hands on the fresh mask's number in the frame's
  field mask
The bodies are Switch.lean's and First.lean's: here they are only laid in the program's order.
WHICH STEPS OF THE PROGRAM's TEXT, CUT STEP BY STEP, THE ROW STANDS FOR: at a layers' | attention
link that is not link 0: "0.call" (the whole ChainCheck.first, whose own first line and last
write stand in Cuts.lean): firstE · AT THE HEAD's LINK the text is cut in four: "0.front" (with
beginLink) · "0.call" («REPLY») · "1.call" (the switch alone) · "1.quiet": THERE switchE ALONE IS
LAID, AT
"1.call", over the frame that "0.front" has made: firstE is NOT laid there (beginLink would run
twice) · AT THE FINISH in three: "0.front" · "0.call" (the switch alone: switchE) · "0.quiet"
(finishBehind).
 [S1] the stretch has just two rounds
 [S2] as many plain scalars were heard in front as the link sends       Req.lean:330 (recvEs
 L.plain)
 [S3] the round «LOC» owes no count: its entry counts no rows           each step asks it of each of
 its own entries
 [S5] the sending took no more items than the second round's message holds   (no line of the
 program's: there the items are taken off one list, Ground.lean:759-776; here «took» is a number
 that another
      file's function hands back, and «items left» is a difference of natural numbers: without S5 a
      «took» too large would read as «none left» and G4 would pass)
 [S6] the sending laid as many trees as the entry «SEND seed» has roots   (no line of the program's:
 there the roots are taken off the message that the entry cuts. Here the roots are in no view; the
 count of trees comes back from another
      file's function, which makes it of the RECORD's announcements; the entry is the PLAN's:
      without S6 nothing at run time holds the two numbers together. Idle where the record's
      announcements are the plan's)
 [S4] the round closed in front of the stretch owes no count            Ground.lean:825
 (!c.ch.settled) at the sending's own close of «SEND seed»
 [G3] the round «SEND seed» owes no count: its entry counts no rows     Ground.lean:825 with
 :602-605: here a function of the plan's entry
ON THE CHANNEL (the program's close leaves entries := es · last := some e · askedRows := false · cur
:= none · left := t: Ground.lean:843-844): at the one
Step type the rounds are cut by the fold, so entries | left | cur are the fold's. «settled» (last |
askedRows) COMES FROM THE CALLER: that the
entry «LOC» counts no rows is asked here [S3]; S9.settled carries what the program's context would
say behind the step: eLoc.rows == 0.
No soundness: definitions with code.
-/
import Johnson.Top.H0.Tw.K2.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Tw.K2
open OnBytes

abbrev Step (S : Type) : Type := S → List Fmt.RoundView → List Col → Option (S × Nat)

structure S9 where
  st : Statement
  book : TreeBook
  roots : Nat
  frame : ReqFrame
  plain : List E := []
  settled : Bool := true

structure Par9 where
  firstTree : Nat
  samples : Nat
  eSeed : Fmt.Entry
  eLoc : Fmt.Entry

structure Sent where
  st : Statement
  book : TreeBook
  roots : Nat
  ids : Array Nat
  took : Nat

abbrev SendFn : Type :=
  Par9 → Statement → TreeBook → (roots : Nat) → (settled : Bool) → Array OracleNotice → Fmt.RoundView →
      Fmt.RoundView → Except String Sent

/-- What both forms share: the guard, the sending, the step behind it. behind: switchBehind (an
argument only so that a control can lay a
planted copy in its place). -/
def switchE (behind : SwIn → Except String SwOut) (P : Par9) (send : SendFn) (s : S9) (x : Front)
    (rS rL : Fmt.RoundView)
    (cols : List Col) : Except String (SwOut × Nat) := do
  if !s.settled then throw "S4: the round closed before the stretch owes a count of rows"
  if P.eLoc.rows != 0 then throw "S3: the entry LOC counts rows that nobody asks"
  if !switchGuard x.st x.f.rows x.T then
      throw ("G0: the target does not fit the carried rows: it is not so that " ++ targetWhy x.st
          x.f.rows x.T)
  let y ← send P x.st s.book s.roots s.settled (switchNotices x.T x.others) rS rL
  if rL.vals.length < y.took then
      throw "S5: the sending says that it took more items than the message holds"
  if y.roots != s.roots + P.eSeed.roots then
      throw "S6: the sending laid another number of trees than the entry SEND seed has roots"
  let w ← behind ⟨y.st, y.book, P.firstTree, cols, x.f.rows, x.T, x.f.group, y.ids, P.eLoc,
    P.eSeed.rows == 0, rL.drawn, rL.vals.length - y.took⟩
  pure (w, y.roots)

/-- A later link's first call, over a given step behind the sending. -/
def firstEW (behind : SwIn → Except String SwOut) (P : Par9) (send : SendFn) (s : S9) (rounds : List
    Fmt.RoundView)
    (cols : List Col) : Except String (S9 × List Col) :=
  match rounds with
  | [rS, rL] => do
    let x ← firstFront s.st s.frame
    if s.plain.length != x.plain then
        throw "S2: not as many plain scalars were heard as the link sends"
    let (w, roots) ← switchE behind P send s x rS rL cols
    let (S', f, _) ← firstBehind w.st x w.out s.plain
    pure (⟨S', w.book, roots, f, [], P.eLoc.rows == 0⟩, w.opened)
  | _ => .error "S1: the stretch has not two rounds"

/-- **A later link's first call.** -/
def firstE : Par9 → SendFn → S9 → List Fmt.RoundView → List Col → Except String (S9 × List Col) :=
    firstEW switchBehind

def firstStep (P : Par9) (send : SendFn) : Step S9 := fun s r c =>
  (firstE P send s r c).toOption.map fun x => (x.1, c.length - x.2.length)

/-- The finish's switch, over a given step behind the sending. -/
def finishEW (behind : SwIn → Except String SwOut) (P : Par9) (send : SendFn) (s : S9) (rounds :
    List Fmt.RoundView)
    (cols : List Col) : Except String (S9 × List Col) :=
  match rounds with
  | [rS, rL] => do
    let x ← finishFront s.st s.frame
    let (w, roots) ← switchE behind P send s x rS rL cols
    let mask ← finishBehind w.out
    pure (⟨w.st, w.book, roots, { x.f with mask := some mask }, [], P.eLoc.rows == 0⟩, w.opened)
  | _ => .error "S1: the stretch has not two rounds"

/-- **The finish's switch.** -/
def finishE : Par9 → SendFn → S9 → List Fmt.RoundView → List Col → Except String (S9 × List Col) :=
    finishEW switchBehind

def finishStep (P : Par9) (send : SendFn) : Step S9 := fun s r c =>
  (finishE P send s r c).toOption.map fun x => (x.1, c.length - x.2.length)

end Tw.K2
