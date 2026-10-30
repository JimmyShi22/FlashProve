-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/SitsYes.lean: **THE STEP's OWN YES, LAID INTO THE LAW's CONCLUSION, AT THE
FILE's OWN PIECE.** Statements and proofs. The game's conclusion says of the state behind only that
it is the way out of SOME return of the kind's block. What the next block's promise must live on is
more: that this return is what the kind's STEP put out from the state that the door in laid. A law,
and what a yes gives for certain, are one law (`leads_and_kept`, GrownPromise.lean): so it costs no
chance.
  `StepYes ft K enter leave s s'`: the door lets s in as t; K's step says yes from t on some rounds
    and columns, putting out t'; the way out lays s' of s and t'.
  `seat_stepYes`: a seat's piece (p.b = K.inside enter leave) puts out only so.
  `leads_seat_yes`: so its plain law holds with `StepYes` beside its conclusion, at the same errors.
  `leads_held_sits_yes`: and so at the file's own piece (p.b = held B, B sitting on K), by
    `leads_held_sits` (LeadsSits.lean).
  `k12_game_sitsVY` | `k12_game_sitsY` | `k12_game_sitsOY`: the game's three forms, with it.
THE RIDER. `StepYes` is a fact of a yes. A block that says no to all has it at no transcript. One
that says yes to all has the `StepYes` of ITS OWN step: it hands on only what that step keeps.
Limits. Nothing on soundness. What the proximity test's step keeps: BookAppends.lean,
ShapesAppend.lean, MaskOfYes.lean.

-/
import Johnson.Desc.K12.Coin.LeadsSits
import Johnson.Desc.K12.Coin.GrownPromise

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open H2K.JointK (Sits)

/-- The door lets s in; the kind's step says yes; the way out lays s'. -/
def StepYes {S T Cl : Type} (ft : ℕ) (K : Block T Cl) (enter : S → Except String T)
    (leave : S → T → Except String S) (s s' : S) : Prop :=
  ∃ (t t' : T) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (k : ℕ),
    enter s = .ok t ∧ K.step ft t rs cols = .ok (t', k) ∧ leave s t' = .ok s'

/-- A seat's piece puts out only so. -/
theorem seat_stepYes {S T Cl W : Type} {C : PQ.CK} {F : Frame} (K : Block T Cl)
    (enter : S → Except String T) (leave : S → T → Except String S) (p : Piece C F S Cl W)
    (hp : p.b = K.inside enter leave) (h0 : p.back = []) (a : S × F.E.Str)
    (τ : Iop.Tr (uLT C p.ds)) (b : S × F.E.Str) (h : p.ior.red.out a τ = some b) :
    StepYes F.ft K enter leave a.1 b.1 := by
  obtain ⟨_, k, hst, _⟩ := yes_step p h0 a τ b h
  rw [hp] at hst
  obtain ⟨t, t', e1, e2, e3⟩ := (Seat.step_inside _ enter K leave _ _ _ _ k).1 hst
  exact ⟨t, t', _, _, k, e1, e2, e3⟩

/-- **The seat's law, with the step's own yes beside its conclusion.** -/
theorem leads_seat_yes {S T Cl W : Type} {C : PQ.CK} {F : Frame} (K : Block T Cl)
    (enter : S → Except String T) (leave : S → T → Except String S) (p : Piece C F S Cl W)
    (hp : p.b = K.inside enter leave) (h0 : p.back = []) (on : S × F.E.Str → Prop)
    (Q : S × F.E.Str → S × F.E.Str → Prop) (h : p.ior.red.Leads on Q p.err) :
    p.ior.red.Leads on (fun a b => Q a b ∧ StepYes F.ft K enter leave a.1 b.1) p.err :=
  leads_and_kept h fun a τ b _ hb => seat_stepYes K enter leave p hp h0 a τ b hb

/-- **The same at the file's own piece.** -/
theorem leads_held_sits_yes {P S T Cl Cl' W : Type} {F : Frame} (K : Block T Cl)
    (enter : S → Except String T) (leave : S → T → Except String S) (B : Block S Cl')
    (hS : Sits B K enter leave) (base : ℕ) (ds : List RDT) (err : Err (uLT (ckP .two) ds))
    (p : Piece (ckP .two) F (P × S) Cl' W) (hb : p.b = held (P := P) B) (h0 : p.back = [])
    (hbase : p.base = base) (hds : p.ds = ds) (herr : HEq p.err err)
    (on : S × F.E.Str → Prop) (Q : S × F.E.Str → S × F.E.Str → Prop)
    (h : (pieceOf (C := ckP .two) (F := F) (W := W) (K.inside enter leave) base ds []
      ⟨fun _ _ w => w, err⟩).ior.red.Leads on Q err) :
    p.ior.red.Leads (fun a => on (a.1.2, a.2))
      (fun a b => (Q (a.1.2, a.2) (b.1.2, b.2) ∧ StepYes F.ft K enter leave a.1.2 b.1.2) ∧
        b.1 = (a.1.1, b.1.2)) p.err :=
  leads_held_sits K enter leave B hS base ds err p hb h0 hbase hds herr on
    (fun a b => Q a b ∧ StepYes F.ft K enter leave a.1 b.1)
    (leads_seat_yes K enter leave _ rfl rfl on Q h)

section
variable (P S Cl' : Type) (enter : S → Except String T12) (leave : S → T12 → Except String S)
  (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (L mC mS mW : Sg → ℕ → ℕ)
  (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT) (e : ℕ)
  (εt : Err (uLT (ckP .two) dt)) (B : Block S Cl')
  (hS : Sits B (proximityTestKind guardedProximityTestParts π : Block T12 Unit) enter leave)
  (p : Piece (ckP .two) F (P × S) Cl' W) (hb : p.b = held (P := P) B) (h0 : p.back = [])
  (hbase : p.base = base) (hds : p.ds = dB :: dt)
  (herr : HEq p.err ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
include hS hb h0 hbase hds herr

/-- The numbering by labels: nothing promised. First arm. -/
theorem k12_game_sitsVY (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ)
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt) (hr : ∀ s, rad s = r s.st)
    (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e) (hpl : LabelsPub π num nl base) :
    p.ior.red.Leads (fun _ => True)
      (fun a b => ((∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
          QN π (NTuple F π (nuOf π nl t) rad rd) (t, a.2)) ∧
        StepYes F.ft (proximityTestKind guardedProximityTestParts π : Block T12 Unit) enter leave a.1.2 b.1.2) ∧
        b.1 = (a.1.1, b.1.2))
      p.err :=
  leads_held_sits_yes _ enter leave B hS base (dB :: dt) (e, εt) p hb h0 hbase hds herr _ _
    (k12_gameSeatV S enter leave F W π num nl L mC mS mW rad rd base dB dt (fun _ _ w => w) e εt r
      hA hr hj hb1 hle hpl)

/-- A fixed numbering, under `FirstOpens`. First arm. -/
theorem k12_game_sitsY (no : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ)
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt) (hr : ∀ s, rad s = r s.st)
    (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e) :
    p.ior.red.Leads (fun a => ∀ t, enter a.1.2 = .ok t → FirstOpens π num no base t)
      (fun a b => ((∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
          QN π (NTuple F π no rad rd) (t, a.2)) ∧
        StepYes F.ft (proximityTestKind guardedProximityTestParts π : Block T12 Unit) enter leave a.1.2 b.1.2) ∧
        b.1 = (a.1.1, b.1.2))
      p.err :=
  leads_held_sits_yes _ enter leave B hS base (dB :: dt) (e, εt) p hb h0 hbase hds herr _ _
    (k12_gameSeat S enter leave F W π num no L mC mS mW rad rd base dB dt (fun _ _ w => w) e εt r
      hA hr hj hb1 hle)

/-- The own mask's arm, under `FirstOpensOwn`. -/
theorem k12_game_sitsOY (no : ℕ → ℕ) (v₀ : ℕ)
    (hA : AtPlaceOwn F π num L mC mS mW rad base dB dt εt)
    (hP : PayPub π rad dB.entry.rows v₀) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0])
    (hlog : dB.entry.logN ≤ 64) (hle : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e) :
    p.ior.red.Leads (fun a => ∀ t, enter a.1.2 = .ok t → FirstOpensOwn π num no base t)
      (fun a b => ((∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
          QN π (NTuple F π no rad rd) (t, a.2)) ∧
        StepYes F.ft (proximityTestKind guardedProximityTestParts π : Block T12 Unit) enter leave a.1.2 b.1.2) ∧
        b.1 = (a.1.1, b.1.2))
      p.err :=
  leads_held_sits_yes _ enter leave B hS base (dB :: dt) (e, εt) p hb h0 hbase hds herr _ _
    (k12_gameSeatO S enter leave F W π num no L mC mS mW rad rd base dB dt (fun _ _ w => w) e v₀ εt
      hA hP h1 hlog hle)

end

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.seat_stepYes
#print axioms VerifiableInference.Desc.K12.Coin.leads_seat_yes
#print axioms VerifiableInference.Desc.K12.Coin.leads_held_sits_yes
#print axioms VerifiableInference.Desc.K12.Coin.k12_game_sitsVY
#print axioms VerifiableInference.Desc.K12.Coin.k12_game_sitsY
#print axioms VerifiableInference.Desc.K12.Coin.k12_game_sitsOY
