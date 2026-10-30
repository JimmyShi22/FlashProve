-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/TieStated.lean: THE TIE OF
THE LINKS' ROWS TO THE TABLE OF THE KEY FILE'S FIRST CHAIN, STATED: DEFINITIONS ALONE,
NO THEOREM. The table (Johnson/RunOne/KeyRows1At.lean, KeyRowsAtFk.lean; with its history:
Johnson/Top/Fire/Code/KeyTablesR.lean) has a promise On₁' k and a claim Cl₁ k at each border k, at
letters B, at_, R, coll. The links' laws (LinkSeats.lean … LinksAtO.lean) hold between rows at
letters dec, cond, Oth, wd, mx. Here these letters are FILLED FROM THE TABLE'S OWN, and what a tie
by Leads.conseq asks at a border is written out.

Main names:
  atSt q: a record of the first chain that holds the statement q.2 and nothing else.
  PinsT: the stored table decodes to the witness's cells, and messages 0 and 1 of the witness are
    pinned (PINW, PIN: Johnson/Desc/Msg.lean).
  decT, condT, OthT, wdT, mxT: THE FILLING: the witness that is pinned, by choice · the two samples
    are held, no collision at them, none at the stored table's record's seed · the two messages'
    sample rows hold · the table's readings of a witness, read into the field.
  rowT l j: row j of the link of lookup number l at that filling, lifted.
  TiePromise l j, TieClaim l j: at border 2 + 6 l + j: the table's promise gives the row's
    condition; under the table's promise its claim holds exactly if the row's relation does.

Object: none of a description's text: the links' rows and the table.
User: none yet.
Letters: X, N, P, D; the table's B, at_, R, coll.

Limits. NOTHING IS PROVED HERE. That the promise behind a block is the table's again is not stated
here. Whether PinsT has a member at an honest word hangs on a filling of B. Nothing on soundness.

-/
import Johnson.RunOne.Law.LinksAtO
import Johnson.Top.Fire.Code.KeyTablesR

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.TieStated
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Key (Xi FirstState Source chainStart KRead Where FreeAt valOf matOf)
open Johnson.RunOne.KeyRows23 (BaseSt Fk fr₁ Cl₁)
open Johnson.RunOne.KeyRows1 (plan₁ meaning₁At)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD
open Johnson.RunOne.Law.PromKeyD
open Johnson.RunOne.Law.SeatsAtFK
open Johnson.RunOne.Law.LinkSeats
open Johnson.RunOne.Law.LinkAtPlan
open Johnson.RunOne.Law.LettersAt
open Johnson.RunOne.Law.FrontSteps
open LPFD (On₁')

variable {Cells Mm Smp Rec : Type} (X : Source) (N : H2U.PlaceNums)
  (P : VerifiableInference.Desc.Key.LaterPlaces) (D : WholeD) (B : BaseSt Cells Mm Smp Rec)
  (at_ : Where) (R : KRead Cells Mm) (coll : Strs → Rec → Prop)

/-- A record of the first chain that holds the statement q.2 and nothing else. -/
def atSt (q : Xi × Statement) : Xi × FirstState :=
  (q.1, { (chainStart q.2.codes {} : FirstState) with
    d := { (chainStart q.2.codes {} : FirstState).d with st := q.2 } })

/-- The stored table and the messages 0 and 1 are pinned to the witness. -/
def PinsT (q : Xi × Statement) (y : Strs) (w : Wit Cells Unit Mm) : Prop :=
  PINW B.h₁ (atSt q) y w ∧ PIN (Fk X N P) B.h₁ (at_ 0).1 (at_ 0).2 (atSt q) y w ∧
    PIN (Fk X N P) B.h₁ (at_ 1).1 (at_ 1).2 (atSt q) y w

open Classical in
/-- **The decoder**: the witness that is pinned, by choice. -/
def decT (a : (Xi × Statement) × (fr₁ D).E.Str) : Option (Wit Cells Unit Mm) :=
  if h : ∃ w, PinsT X N P B at_ a.1 (strsOf (fr₁ D) a.2) w then some h.choose else none

/-- **Its condition.** -/
def condT (a : (Xi × Statement) × (fr₁ D).E.Str) : Prop :=
  (hasSmp B.h₁ (at_ 0).1 (at_ 0).2 (atSt a.1) = true ∧
    hasSmp B.h₁ (at_ 1).1 (at_ 1).2 (atSt a.1) = true) ∧
  FreeAt B.h₁ coll (atSt a.1) (strsOf (fr₁ D) a.2) ∧
  NoColl (Fk X N P) B.h₁ (at_ 0).1 (at_ 0).2 (atSt a.1) (strsOf (fr₁ D) a.2) ∧
  NoColl (Fk X N P) B.h₁ (at_ 1).1 (at_ 1).2 (atSt a.1) (strsOf (fr₁ D) a.2)

/-- **What else rides**: the two messages' sample rows hold. -/
def OthT (q : Xi × Statement) (w : Wit Cells Unit Mm × Unit) : Prop :=
  ∀ y, (meaning₁At X.Y.k.oneTime R).srow 0 (atSt q) y w.1 ∧
    (meaning₁At X.Y.k.oneTime R).srow 1 (atSt q) y w.1

/-- The words, read. -/
def wdT (w : Wit Cells Unit Mm) : Means.Words GE :=
  fun o part i => readE (valOf (plan₁ X.Y.k.oneTime) R w o part i)

/-- The matrix, read. -/
def mxT (w : Wit Cells Unit Mm) (r c : ℕ) : GE :=
  readE (OnBytes.ofF (matOf (plan₁ X.Y.k.oneTime) R w r c))

/-- **Row j of the link of lookup number l, at the filling, lifted.** -/
def rowT (l j : ℕ) : JointRow (Xi × FirstState) (fr₁ D) :=
  upF fun p₀ => rows7 p₀ X.Y.k.oneTime X.set X.Y.k.oneTime.ranges.messageId
    (Wf.matrixOf X.Y.k.oneTime.lin) (Lof X.Y.k.oneTime)
    (handed (cntO X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
      (Lof X.Y.k.oneTime)) (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape))
    (handed (cntK X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
      (Lof X.Y.k.oneTime)) (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape))
    0 (wdT X R) (mxT X R) (fun a => decT X N P D B at_ (pullK a.1, a.2))
    (fun a => condT X N P D B at_ coll (pullK a.1, a.2))
    X.Y.k.oneTime.ranges.lookups.length
    (PromL X.Y.k.oneTime X.Y.k.oneTime.ranges.messageId (Wf.matrixOf X.Y.k.oneTime.lin)
      (Lof X.Y.k.oneTime) 0 X.Y.k.oneTime.ranges.lookups.length
      (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.ranges.message.shape)
      (ledOf X.Y.k.oneTime.codes X.Y.k.oneTime.indexMasks.shape) fun _ => True)
    l Unit (fun x w => OthT X R (pullK x) w) j

/-- **The promises' tie at border 2 + 6 l + j.** -/
def TiePromise (l j : ℕ) : Prop :=
  ∀ b, On₁' X N P D B at_ R coll (2 + 6 * l + j) b → (rowT X N P D B at_ R coll l j).on b

/-- **The claims' tie at border 2 + 6 l + j**, both ways, under the table's promise. -/
def TieClaim (l j : ℕ) : Prop :=
  ∀ b, On₁' X N P D B at_ R coll (2 + 6 * l + j) b →
    (Cl₁ X N P D B at_ R (2 + 6 * l + j) b ↔ (rowT X N P D B at_ R coll l j).rel b)

end Johnson.RunOne.Law.TieStated
