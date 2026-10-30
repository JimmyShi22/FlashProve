-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/LeadsSits.lean: **A PLAIN LAW AT A SEAT GOES OVER TO WHATEVER BLOCK SITS ON
THE KIND's BLOCK BEHIND THAT SEAT's DOORS.** Statements and proofs. For the row K12_sits, its second
arm ("or its yes gives that law's premise"): the join of `Sits`
(Johnson/Desc/K12/Law/Sits.lean) with the game of the proximity test at a seat.
`Sits B K enter leave`: B declares K's rounds; B's yes on the plan gives K's; wherever B's STEP says
yes, the door lets in, K's step says yes on the same rounds and columns, taking as many columns, and
the way out lays B's own record behind. It holds of an entry behind guards, joined with a block
without a round, retyped, renamed: where `Alike` (one decision) fails.
  `step_of_sits`: then wherever B's step says yes, the step of `K.inside enter leave` says the same
    yes: the premise of `run_of_step` (OneWay.lean) at "the two records behind are one".
  `leads_sits`: GENERAL IN K: q.b sits on K behind (enter, leave) · p.b = K.inside enter leave · one
    base, data, rounds put back, errors · p leads from on to Q ⇒ q leads from on to THE VERY Q.
  `leads_held_sits`: FROM THE SEAT's PIECE TO THE FILE's OWN: general in K, the promise and the
    conclusion: a plain law of the piece of `K.inside enter leave` stands at any piece p with p.b =
    held B, B sitting on K: read at the chain's own part of the record; what is held rides.
  `k12_game_sitsV` | `k12_game_sits` | `k12_game_sitsO`: **the game at the file's own piece**, in
    its three forms: the numbering by labels, nothing promised (first arm) · a fixed numbering under
    `FirstOpens` (first arm) · under `FirstOpensOwn` (the own mask's arm): each under the other
    premises of `k12_game_alikeV` | `_alike` | `_alikeO`, with their very conclusions, `Sits` in
    `Alike`'s place.
THE RIDER. ONE WAY: the law goes to a B that says yes ONLY WHERE the seat does. B := no to all sits
on every K with K's rounds, and has every law for nothing. B := yes to all sits on K only if K's
step says yes on every record that the door lays (`sits_yesAll`): and such a K has no law whose
conclusion can fail.
Limits. That a written description's entry at a place of the kind sits so is left to the kind's
files (`firstEntry_sits`, `guEntry_sits`, `omegaEntry_sits`, `ownEntry_sits`, SitsChains.lean,
and the cuts there). Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.OneWay
import Johnson.Desc.K12.Coin.GameLabels
import Johnson.Desc.K12.Coin.GameSeat
import Johnson.Desc.K12.Law.Sits
import Johnson.Desc.K12.SeatLaws

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

/-- Wherever B's step says yes, the seat's step says the same yes. -/
theorem step_of_sits {S T Cl Cl' : Type} {B : Block S Cl'} {K : Block T Cl}
    {enter : S → Except String T} {leave : S → T → Except String S} (h : Sits B K enter leave)
    (ft : ℕ) (s s' : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (k : ℕ)
    (hB : B.step ft s rs cols = .ok (s', k)) :
    (K.inside enter leave).step ft s rs cols = .ok (s', k) :=
  (Seat.step_inside ft enter K leave s s' rs cols k).2 (h.step ft s s' rs cols k hB)

/-- **A plain law at the seat goes over to whatever sits there.** -/
theorem leads_sits {S T Cl Cl' W W' : Type} {C : PQ.CK} {F : Frame} (K : Block T Cl)
    (enter : S → Except String T) (leave : S → T → Except String S) (p : Piece C F S Cl W)
    (q : Piece C F S Cl' W') (hp : p.b = K.inside enter leave) (hS : Sits q.b K enter leave)
    (h1 : q.base = p.base) (h2 : q.ds = p.ds) (h3 : q.back = p.back) (h4 : HEq q.err p.err)
    (on : S × F.E.Str → Prop) (Q : S × F.E.Str → S × F.E.Str → Prop)
    (h : p.ior.red.Leads on Q p.err) : q.ior.red.Leads on Q q.err := by
  refine leads_guarded p q h1 h2 h4 (fun s v s' hq => ?_) on Q h
  obtain ⟨s'', hs, rfl⟩ := run_of_step p q (fun _ a b => a = b)
    (by rw [hS.rounds, hp]; rfl) h3
    (fun s rs cols s' k hB => ⟨s', by rw [hp]; exact step_of_sits hS _ s s' rs cols k hB, rfl⟩)
    s v s' hq
  exact hs

/-- The rider: a B that always says yes sits on K only if K's step says yes wherever the door lets
in on what B is shown. -/
theorem sits_yesAll {S T Cl Cl' : Type} {B : Block S Cl'} {K : Block T Cl}
    {enter : S → Except String T} {leave : S → T → Except String S} (h : Sits B K enter leave)
    (ft : ℕ) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (hB : ∃ s' k, B.step ft s rs cols = .ok (s', k)) :
    ∃ t t' k, enter s = .ok t ∧ K.step ft t rs cols = .ok (t', k) := by
  obtain ⟨s', k, hb⟩ := hB
  obtain ⟨t, t', e1, e2, _⟩ := h.step ft s s' rs cols k hb
  exact ⟨t, t', k, e1, e2⟩

/-- **From the seat's piece to the file's own**: general in K, in the promise and in the conclusion:
a plain law of the piece of `K.inside enter leave` stands at any piece whose block is `held B`, B
sitting on K behind these doors: read at the chain's own part of the record; what is held rides. -/
theorem leads_held_sits {P S T Cl Cl' W : Type} {F : Frame} (K : Block T Cl)
    (enter : S → Except String T) (leave : S → T → Except String S) (B : Block S Cl')
    (hS : Sits B K enter leave) (base : ℕ) (ds : List RDT) (err : Err (uLT (ckP .two) ds))
    (p : Piece (ckP .two) F (P × S) Cl' W) (hb : p.b = held (P := P) B) (h0 : p.back = [])
    (hbase : p.base = base) (hds : p.ds = ds) (herr : HEq p.err err)
    (on : S × F.E.Str → Prop) (Q : S × F.E.Str → S × F.E.Str → Prop)
    (h : (pieceOf (C := ckP .two) (F := F) (W := W) (K.inside enter leave) base ds []
      ⟨fun _ _ w => w, err⟩).ior.red.Leads on Q err) :
    p.ior.red.Leads (fun a => on (a.1.2, a.2))
      (fun a b => Q (a.1.2, a.2) (b.1.2, b.2) ∧ b.1 = (a.1.1, b.1.2)) p.err :=
  leads_alike
    (pieceOf (C := ckP .two) (F := F) (W := W) (held (P := P) B) base ds []
      ⟨fun _ _ w => w, err⟩) p (by rw [hb]; exact ⟨rfl, rfl, rfl⟩) hbase hds h0 herr _ _
    (leads_lift (S := P × S) Prod.snd (fun t s => (t.1, s))
      (pieceOf (C := ckP .two) (F := F) (W := W) B base ds [] ⟨fun _ _ w => w, err⟩).under
      on Q (fun _ _ => rfl) (fun _ _ _ => rfl)
      (leads_under _ rfl _ _
        (leads_sits K enter leave
          (pieceOf (C := ckP .two) (F := F) (W := W) (K.inside enter leave) base ds []
            ⟨fun _ _ w => w, err⟩)
          (pieceOf (C := ckP .two) (F := F) (W := W) B base ds [] ⟨fun _ _ w => w, err⟩)
          rfl hS rfl rfl rfl HEq.rfl _ _ h)))

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

/-- **The game at the file's own piece**, the numbering by labels: nothing promised. First arm. -/
theorem k12_game_sitsV (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ)
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt) (hr : ∀ s, rad s = r s.st)
    (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e) (hpl : LabelsPub π num nl base) :
    p.ior.red.Leads (fun _ => True)
      (fun a b => (∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
        QN π (NTuple F π (nuOf π nl t) rad rd) (t, a.2)) ∧ b.1 = (a.1.1, b.1.2))
      p.err :=
  leads_held_sits _ enter leave B hS base (dB :: dt) (e, εt) p hb h0 hbase hds herr _ _
    (k12_gameSeatV S enter leave F W π num nl L mC mS mW rad rd base dB dt (fun _ _ w => w) e εt r
      hA hr hj hb1 hle hpl)

/-- The same at a fixed numbering, under the promise `FirstOpens`. First arm. -/
theorem k12_game_sits (no : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ)
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt) (hr : ∀ s, rad s = r s.st)
    (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e) :
    p.ior.red.Leads (fun a => ∀ t, enter a.1.2 = .ok t → FirstOpens π num no base t)
      (fun a b => (∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
        QN π (NTuple F π no rad rd) (t, a.2)) ∧ b.1 = (a.1.1, b.1.2))
      p.err :=
  leads_held_sits _ enter leave B hS base (dB :: dt) (e, εt) p hb h0 hbase hds herr _ _
    (k12_gameSeat S enter leave F W π num no L mC mS mW rad rd base dB dt (fun _ _ w => w) e εt r
      hA hr hj hb1 hle)

/-- The second arm (the first fold sends its own mask), under the promise `FirstOpensOwn`. -/
theorem k12_game_sitsO (no : ℕ → ℕ) (v₀ : ℕ)
    (hA : AtPlaceOwn F π num L mC mS mW rad base dB dt εt)
    (hP : PayPub π rad dB.entry.rows v₀) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0])
    (hlog : dB.entry.logN ≤ 64) (hle : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e) :
    p.ior.red.Leads (fun a => ∀ t, enter a.1.2 = .ok t → FirstOpensOwn π num no base t)
      (fun a b => (∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
        QN π (NTuple F π no rad rd) (t, a.2)) ∧ b.1 = (a.1.1, b.1.2))
      p.err :=
  leads_held_sits _ enter leave B hS base (dB :: dt) (e, εt) p hb h0 hbase hds herr _ _
    (k12_gameSeatO S enter leave F W π num no L mC mS mW rad rd base dB dt (fun _ _ w => w) e v₀ εt
      hA hP h1 hlog hle)

end

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.leads_sits
#print axioms VerifiableInference.Desc.K12.Coin.sits_yesAll
#print axioms VerifiableInference.Desc.K12.Coin.leads_held_sits
#print axioms VerifiableInference.Desc.K12.Coin.k12_game_sitsV
#print axioms VerifiableInference.Desc.K12.Coin.k12_game_sits
#print axioms VerifiableInference.Desc.K12.Coin.k12_game_sitsO
