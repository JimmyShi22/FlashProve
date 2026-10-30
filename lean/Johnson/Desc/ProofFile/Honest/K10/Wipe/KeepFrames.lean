-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/KeepFrames.lean: the closing of a segment (K10): the three steps that frame each
link of the first chain (lay, opened, clear: Johnson/Desc/First/Walk/Frame.lean, FrameZero.lean,
Johnson/Desc/First/Close/TailHead.lean, laid link by link by framesOf, Johnson/Top/H0/Walk/FrameLot.lean) commute with
the wiping of the chain's state (wipeS, Honest/K10/WipeS.lean: the state with these targets set to zero: those of the
statement's rows, of the carried rows in each frame that the state holds and, at the finish, of the batched row; the
rows on the table (the pile out.pending, and the claim at the chain's end) keep theirs). Five definitions with code; the
rest are theorems.

What is proved. For each such step f: f (wipeS s) = (f s).map wipeS. That is: f refuses with the same word at both
states, or its value at the wiped state is its value at the state, wiped.
  wipeFr, wipeAttStart, wipeLayStart, wipeBk, wipeRO   the wiping on what the lines below return
  front_wipe, attFirstQuiet_wipe, layFirstQuiet_wipe, indexMasksAt_wipe, layFirstQuietZero_wipe, back_wipe   the walk's
                   lines without a round, which are handed a state of the calls or a link's context whole
  pendingRowO_wipe   the pending row's function: of the oracle messages it reads and writes one ledger
  layFront_comm, openAtt_comm, openLay_comm, openLayZero_comm, clearWith_comm, tailHead_comm   the steps themselves
  countsLay_wipe, countsAtt_wipe, countsHead_wipe, leftLay_wipe, leftHead_wipe   what the clearing asks first
  **frames2**      for every row of framesOf: Fn2 wipeS of lay, opened and clear: the field frames of SeatKeeps2
                   (Wipe/Lots2.lean) at wipeS

By what. Each text is unfolded and followed bind by bind and arm by arm (Wipe/Carry.lean). What it asks of the state
goes by the laws of Wipe/WipeLaws.lean. What it asks of a state of the calls or of a link's context unfolds to the same
term at the wiped value and at the value. None of these steps writes a target that the wiping sets to zero (clear lays a
row on the pile, whose target the wiping leaves), so the equation holds as it stands, and Fn2.of_comm (Wipe/Alike.lean)
makes Fn2 of it.

Limits. The laws speak of all states, reachable or not. Nothing is said of the head's front and opening nor of the
finish's two steps (Wipe/KeepFront.lean). No property of the protocol is claimed: nothing is said on its soundness,
completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Carry
import Johnson.Desc.ProofFile.Honest.K10.Wipe.WipeLaws
import Johnson.Top.H0.Walk.FrameLot
import Johnson.Goal.Meaning.KeepsDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (Oracle TensorRow)
open OnBytes.Model (ChainCheck LinkCtx Fork Tail2 HTailF2 WsForkOut WsLay)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Pend (pendingRowO)
open VerifiableInference.Desc.First.Close (countsHead leftHead tailHead)
open Johnson.Desc.First.Walk

/-! ## 1 The walk's lines without a round -/

/-- A link's context beside the walk's result, the context wiped. -/
def wipeFr (y : LinkCtx × OnBytes.Proof.LinksResult) : LinkCtx × OnBytes.Proof.LinksResult := (wipeCtx y.1, y.2)

/-- What an attention link's first step without a round lays, its context wiped. -/
def wipeAttStart (a : AttStart) : AttStart := { a with L := wipeCtx a.L }

/-- What a layers' link's first step without a round lays, its context wiped. -/
def wipeLayStart (a : LayStart) : LayStart := { a with L := wipeCtx a.L }

/-- What the lines behind a sub-proof return, the state of the calls wiped. -/
def wipeBk (y : ChainCheck × Option WsForkOut) : ChainCheck × Option WsForkOut := (wipeCheck y.1, y.2)

/-- A row on the weight table beside the oracle messages, these wiped. -/
def wipeRO (y : TensorRow × Array Oracle) : TensorRow × Array Oracle := (y.1, y.2.map wipeOr)

/-- The lines behind a link's first call lay the state of the calls whole into the link's context: at the wiped one, the
context wiped. -/
theorem front_wipe (X : LinkPub) (l : Nat) (c : ChainCheck) (out : OnBytes.Proof.LinksResult) :
    front X l (wipeCheck c) out = (front X l c out).map wipeFr := by
  unfold front
  exact Carry.iteE _ rfl (Carry.iteE _ rfl rfl)

/-- An attention link's first step without a round, at the wiped state of the calls, returns its value wiped. -/
theorem attFirstQuiet_wipe (X : LinkPub) (l ns : Nat) (tl₀ : HTailF2) (c : ChainCheck)
    (out : OnBytes.Proof.LinksResult) :
    attFirstQuiet X l ns tl₀ (wipeCheck c) out = (attFirstQuiet X l ns tl₀ c out).map wipeAttStart := by
  unfold attFirstQuiet
  rw [front_wipe]
  refine Carry.iteE _ rfl ?_
  cases front X l c out with
  | error e => rfl
  | ok y =>
    obtain ⟨L, o⟩ := y
    rfl

/-- A layers' link's first step without a round, at the wiped state of the calls, returns its value wiped. -/
theorem layFirstQuiet_wipe (X : LinkPub) (l : Nat) (p4 : Bool) (g : Nat) (Tp : Tail2) (Fp : Fork) (ns : Nat)
    (c : ChainCheck) (out : OnBytes.Proof.LinksResult) :
    layFirstQuiet X l p4 g Tp Fp ns (wipeCheck c) out =
      (layFirstQuiet X l p4 g Tp Fp ns c out).map wipeLayStart := by
  unfold layFirstQuiet
  rw [front_wipe]
  refine Carry.iteE _ rfl ?_
  cases front X l c out with
  | error e => rfl
  | ok y =>
    obtain ⟨L, o⟩ := y
    exact Carry.iteE _ rfl (Carry.iteE _ rfl rfl)

/-- The number of the index-mask message is the same at the wiped arguments: of a message the ledger alone is read. -/
theorem indexMasksAt_wipe (room : Nat) (c : ChainCheck) (os : Array Oracle) :
    indexMasksAt room (wipeCheck c) (os.map wipeOr) = indexMasksAt room c os := by
  have e0 : (wipeCheck c).frame.atStart = c.frame.atStart := rfl
  unfold indexMasksAt
  rw [e0]
  cases c.frame.atStart[0]? with
  | none => rfl
  | some im =>
    dsimp only
    rw [Array.getElem?_map]
    cases os[im]? with
    | none => rfl
    | some x => rfl

/-- Link 0's first step without a round, at the wiped arguments, returns its value wiped. -/
theorem layFirstQuietZero_wipe (X : LinkPub) (p4 : Bool) (g : Nat) (Tp : Tail2) (Fp : Fork) (ns room : Nat)
    (c : ChainCheck) (out : OnBytes.Proof.LinksResult) (os : Array Oracle) :
    layFirstQuietZero X p4 g Tp Fp ns room (wipeCheck c) out (os.map wipeOr) =
      (layFirstQuietZero X p4 g Tp Fp ns room c out os).map wipeLayStart := by
  unfold layFirstQuietZero
  rw [indexMasksAt_wipe]
  cases indexMasksAt room c os with
  | error e => rfl
  | ok im =>
    dsimp only
    rw [front_wipe]
    cases front X 0 c { out with indexMasks := im } with
    | error e => rfl
    | ok y =>
      obtain ⟨L, o⟩ := y
      exact Carry.iteE _ rfl (Carry.iteE _ rfl rfl)

/-- The lines behind a sub-proof hand the context's state of the calls on whole: at the wiped context, wiped. -/
theorem back_wipe (X : LinkPub) (o : Option WsForkOut) (C : LinkCtx) (F : Fork) :
    back X o (wipeCtx C) F = (back X o C F).map wipeBk := by
  unfold back
  refine Carry.iteE _ rfl (Carry.iteE _ rfl (Carry.iteE _ ?_ rfl))
  cases o <;> rfl

/-! ## 2 The pending row -/

/-- **The pending row's function**, at the wiped messages: the same refusal, or the same row, and the messages that it
returns are those that it returns at the messages, wiped. -/
theorem pendingRowO_wipe (lay : WsLay) (im : Nat) (o : WsForkOut) (n : Nat) (Sh : OnBytes.Params.LinShape)
    (os : Array Oracle) :
    pendingRowO lay im o n Sh (os.map wipeOr) = (pendingRowO lay im o n Sh os).map wipeRO := by
  have hl : ((os.map wipeOr)[im]?).bind (·.ledger) = (os[im]?).bind (·.ledger) := by
    rw [Array.getElem?_map]
    cases os[im]? <;> rfl
  unfold pendingRowO
  rw [hl]
  refine Carry.unlessE _ ?_
  refine Carry.unlessE _ ?_
  refine Carry.unlessE _ ?_
  refine Carry.unlessE _ ?_
  refine Carry.headE _ fun x => ?_
  obtain ⟨first, last⟩ := x
  refine Carry.unlessE _ ?_
  refine Carry.unlessE _ ?_
  refine Carry.unlessE _ ?_
  refine Carry.unlessE _ ?_
  refine Carry.headE _ fun Gamma => ?_
  cases VerifiableInference.Desc.Own.weightsOnRows Sh first (Gamma.extract first last) with
  | none => rfl
  | some g =>
    dsimp only
    cases (os[im]?).bind (·.ledger) with
    | none => rfl
    | some l =>
      dsimp only
      cases VerifiableInference.Desc.First.Pend.takeEntry l with
      | none => rfl
      | some y =>
        obtain ⟨c, l'⟩ := y
        have hm : (os.modify im fun x => { x with ledger := some l' }).map wipeOr =
            (os.map wipeOr).modify im fun x => { x with ledger := some l' } :=
          map_modify_comm os im (fun x => { x with ledger := some l' }) wipeOr
            (fun x => { x with ledger := some l' }) fun _ => rfl
        show (Except.ok (_, (os.map wipeOr).modify im fun x => { x with ledger := some l' }) :
            Except String (TensorRow × Array Oracle)) =
          Except.ok (_, (os.modify im fun x => { x with ledger := some l' }).map wipeOr)
        rw [hm]

/-! ## 3 Lay and opened -/

/-- The tests in front of a link's first call commute with the wiping. -/
theorem layFront_comm (l : Nat) (s : S) : layFront l (wipeS s) = (layFront l s).map wipeS := by
  unfold layFront
  rw [atBetween_wipe]
  refine Carry.headE _ fun _ => ?_
  refine Carry.headE _ fun _ => ?_
  refine Carry.headE _ fun _ => ?_
  rfl

/-- The step behind an attention link's first call commutes with the wiping. -/
theorem openAtt_comm (P : AttPar) (s : S) : openAtt P (wipeS s) = (openAtt P s).map wipeS := by
  unfold openAtt
  rw [atBetween_wipe]
  refine Carry.headE _ fun _ => ?_
  refine Carry.headE _ fun _ => ?_
  refine Carry.bindE wipeAttStart wipeS (attFirstQuiet_wipe P.X P.l P.ns P.tl₀ s.check s.out) fun a => ?_
  exact enterAtt?_wipe { s with out := a.out } a.L a.F a.tl

/-- The step behind a layers' link's first call commutes with the wiping. -/
theorem openLay_comm (P : LayPar) (s : S) : openLay P (wipeS s) = (openLay P s).map wipeS := by
  unfold openLay
  rw [atBetween_wipe]
  refine Carry.headE _ fun _ => ?_
  refine Carry.headE _ fun _ => ?_
  refine Carry.bindE wipeLayStart wipeS
    (layFirstQuiet_wipe P.X P.l P.p4 P.g P.Tp P.Fp P.ns s.check s.out) fun a => ?_
  exact enterLay?_wipe { s with out := a.out } a.L a.F P.tl₀

/-- The step behind link 0's first call commutes with the wiping. -/
theorem openLayZero_comm (P : LayPar) (fvs : List Bool) (kCol : Nat) (s : S) :
    openLayZero P fvs kCol (wipeS s) = (openLayZero P fvs kCol s).map wipeS := by
  unfold openLayZero
  rw [atBetween_wipe]
  refine Carry.headE _ fun _ => ?_
  refine Carry.headE _ fun _ => ?_
  refine Carry.bindE wipeLayStart wipeS
    (layFirstQuietZero_wipe P.X P.p4 P.g P.Tp P.Fp P.ns (roomOf fvs kCol) s.check s.out s.st.oracles) fun a => ?_
  exact enterLay?_wipe { s with out := a.out } a.L a.F P.tl₀

/-! ## 4 Clear -/

/-- The counts at a layers' link's end are the same at the wiped state. -/
theorem countsLay_wipe (NM : Nat) (s : S) : countsLay NM (wipeS s) = countsLay NM s := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl

/-- The counts at an attention link's end are the same at the wiped state. -/
theorem countsAtt_wipe (nLin : Nat) (s : S) : countsAtt nLin (wipeS s) = countsAtt nLin s := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl

/-- The counts at the head's link's end are the same at the wiped state. -/
theorem countsHead_wipe (s : S) : countsHead (wipeS s) = countsHead s := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl

/-- What a layers' sub-proof left for its row is the same at the wiped state. -/
theorem leftLay_wipe (s : S) : leftLay (wipeS s) = leftLay s := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl

/-- What the head's sub-proof left for its row is the same at the wiped state. -/
theorem leftHead_wipe (s : S) : leftHead (wipeS s) = leftHead s := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl

/-- **The clearing of a link** commutes with the wiping, if its counts and its reader of what is left are the same at
the wiped state, and its row's function commutes with the wiping of the messages. -/
theorem clearWith_comm (X : LinkPub) {counts : S → Except String Unit} {left : S → Option WsForkOut} {row : RowFn}
    (hc : ∀ s, counts (wipeS s) = counts s) (hl : ∀ s, left (wipeS s) = left s)
    (hr : ∀ im w n os, row im w n (os.map wipeOr) = (row im w n os).map wipeRO) (s : S) :
    clearWith X counts left row (wipeS s) = (clearWith X counts left row s).map wipeS := by
  unfold clearWith
  rw [link?_wipe, fork?_wipe, hc s, hl s]
  cases s.link? with
  | none => cases s.fork? <;> rfl
  | some C =>
    cases s.fork? with
    | none => rfl
    | some F =>
      refine Carry.headE _ fun _ => ?_
      refine Carry.bindE wipeBk wipeS (back_wipe X (left s) C F) fun y => ?_
      obtain ⟨c, o⟩ := y
      cases o with
      | none => exact leaveLink?_wipe s
      | some w =>
        have e : row (wipeS s).out.indexMasks w X.NCL (wipeS s).st.oracles =
            (row s.out.indexMasks w X.NCL s.st.oracles).map wipeRO := hr _ _ _ _
        dsimp only [wipeBk]
        rw [e]
        cases row s.out.indexMasks w X.NCL s.st.oracles with
        | error e' => rfl
        | ok z =>
          obtain ⟨r, os⟩ := z
          exact leaveLink?_wipe { s with out := pendingKept s.out r, st := { s.st with oracles := os } }

/-- The step behind the head's closing commutes with the wiping. -/
theorem tailHead_comm (X : LinkPub) (lay : WsLay) (lin : OnBytes.Params.LinShape) (s : S) :
    tailHead X lay lin (wipeS s) = (tailHead X lay lin s).map wipeS :=
  clearWith_comm X countsHead_wipe leftHead_wipe (fun im w n os => pendingRowO_wipe lay im w n lin os) s

/-! ## 5 The frame, link by link -/

open Johnson.Desc.First.Walk.Seat in
/-- **Every row of the frame**: lay, opened and clear have like outcomes at two states that are equal once wiped. -/
theorem frames2 {built : Array OnBytes.Model.Stages.LinkH} {first : OnBytes.Params.First}
    {W : OnBytes.Model.Verify.Public} {fs : List LinkFrame} (h : framesOf built first W = .ok fs) :
    ∀ f ∈ fs, Fn2 wipeS f.lay ∧ Fn2 wipeS f.opened ∧ Fn2 wipeS f.clear := by
  intro f hf
  have hrow : ∀ im w n os, rowOf W first im w n (os.map wipeOr) = (rowOf W first im w n os).map wipeRO :=
    fun im w n os => pendingRowO_wipe W.layers.wsLay im w n first.lin os
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := Meaning.K2.mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact ⟨Fn2.of_comm (layFront_comm l), Fn2.of_comm (fun _ => rfl), Fn2.of_comm (tailHead_comm _ _ _)⟩
  · split at e
    · split at e
      · cases e
      · cases e
        exact ⟨Fn2.of_comm (layFront_comm 0), Fn2.of_comm (openLayZero_comm _ _ _),
          Fn2.of_comm (clearWith_comm _ (countsLay_wipe _) leftLay_wipe hrow)⟩
    · split at e
      · cases e
      · cases e
        exact ⟨Fn2.of_comm (layFront_comm l), Fn2.of_comm (openAtt_comm _),
          Fn2.of_comm (clearWith_comm (left := fun _ => none) _ (countsAtt_wipe _) (fun _ => rfl) hrow)⟩
      · cases e
        exact ⟨Fn2.of_comm (layFront_comm l), Fn2.of_comm (openLay_comm _),
          Fn2.of_comm (clearWith_comm _ (countsLay_wipe _) leftLay_wipe hrow)⟩

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.wipeFr
#print axioms ProofFile.Honest.K10.wipeAttStart
#print axioms ProofFile.Honest.K10.wipeLayStart
#print axioms ProofFile.Honest.K10.wipeBk
#print axioms ProofFile.Honest.K10.wipeRO
#print axioms ProofFile.Honest.K10.front_wipe
#print axioms ProofFile.Honest.K10.attFirstQuiet_wipe
#print axioms ProofFile.Honest.K10.layFirstQuiet_wipe
#print axioms ProofFile.Honest.K10.indexMasksAt_wipe
#print axioms ProofFile.Honest.K10.layFirstQuietZero_wipe
#print axioms ProofFile.Honest.K10.back_wipe
#print axioms ProofFile.Honest.K10.pendingRowO_wipe
#print axioms ProofFile.Honest.K10.layFront_comm
#print axioms ProofFile.Honest.K10.openAtt_comm
#print axioms ProofFile.Honest.K10.openLay_comm
#print axioms ProofFile.Honest.K10.openLayZero_comm
#print axioms ProofFile.Honest.K10.countsLay_wipe
#print axioms ProofFile.Honest.K10.countsAtt_wipe
#print axioms ProofFile.Honest.K10.countsHead_wipe
#print axioms ProofFile.Honest.K10.leftLay_wipe
#print axioms ProofFile.Honest.K10.leftHead_wipe
#print axioms ProofFile.Honest.K10.clearWith_comm
#print axioms ProofFile.Honest.K10.tailHead_comm
#print axioms ProofFile.Honest.K10.frames2
