-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameAlike.lean: **THE GAME OF THE PROXIMITY TEST AT THE PIECE THAT A
DESCRIPTION HOLDS, AT WHATEVER TYPE OF CLAIMS.** Statements; each proof is one call of `leads_alike`
(Alike.lean) over GameHeld.lean.

GameHeld.lean's law stands at a piece whose block IS `held` of the seat, at the claims' type Unit. A
description carries a later chain's blocks to its own type of claims and lays a clause to their
tests on the plan. Here the piece's block need only be ALIKE to `held` of the seat: one name, the
same declared rounds, one decision.
  `k12_game_alike` | `k12_game_alikeO`: the law.
  `alike_carried`: `held` of the seat, carried to another type of claims with any test on the plan
    in the place of its own, is alike to `held` of the seat: the form in which `Chain.retype` and
    `Chain.blocksInOrder` hand a block to `piecesAt`.
Limits: those of GameHeld.lean, but for "F.Cl is Unit". NO SOUNDNESS IS CLAIMED.

-/
import Johnson.Desc.K12.Coin.GameHeld
import Johnson.Desc.K12.Coin.Alike

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pin (NTuple)
open H2K.Pub (PayPub johOk batV0)
open H2K.First (batOneOk)

/-- A block carried to another type of claims, with any test on the plan, and held. -/
theorem alike_carried {P S Cl Cl' : Type} (b : Block S Cl) (ok : Bool) :
    Alike (held (P := P) b) (held (P := P) { (b.retype (Cl' := Cl')) with planOk := ok }) :=
  ((alike_retype b).trans (alike_plan _ ok)).held

/-- **The game at any piece, at any type of claims, whose block is alike to the held seat**, first
arm. -/
theorem k12_game_alike (P S Cl' : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ)
    (no : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (e : ℕ) (εt : Err (uLT (ckP .two) dt)) (r : Fmt.M1.Stage → ℕ)
    (p : Piece (ckP .two) F (P × S) Cl' W)
    (hb : Alike (held (P := P) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave)) p.b)
    (h0 : p.back = []) (hbase : p.base = base) (hds : p.ds = dB :: dt)
    (herr : HEq p.err ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt)
    (hr : ∀ s, rad s = r s.st) (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e) :
    p.ior.red.Leads (fun a => ∀ t, enter a.1.2 = .ok t → FirstOpens π num no base t)
      (fun a b => (∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
        QN π (NTuple F π no rad rd) (t, a.2)) ∧ b.1 = (a.1.1, b.1.2))
      p.err :=
  leads_alike
    (pieceOf (C := ckP .two) (F := F) (W := W)
      (held (P := P) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave)) base (dB :: dt) []
      ⟨fun _ _ w => w, (e, εt)⟩) p hb hbase hds h0 herr _ _
    (k12_game_held P S enter leave F W π num no L mC mS mW rad rd base dB dt e εt r _ rfl rfl
      rfl rfl HEq.rfl hA hr hj hb1 hle)

/-- **The game at any piece, at any type of claims, whose block is alike to the held seat**,
second arm. -/
theorem k12_game_alikeO (P S Cl' : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ)
    (no : ℕ → ℕ) (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT)
    (dt : List RDT) (e v₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
    (p : Piece (ckP .two) F (P × S) Cl' W)
    (hb : Alike (held (P := P) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave)) p.b)
    (h0 : p.back = []) (hbase : p.base = base) (hds : p.ds = dB :: dt)
    (herr : HEq p.err ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
    (hA : AtPlaceOwn F π num L mC mS mW rad base dB dt εt)
    (hP : PayPub π rad dB.entry.rows v₀) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0])
    (hlog : dB.entry.logN ≤ 64) (hle : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e) :
    p.ior.red.Leads (fun a => ∀ t, enter a.1.2 = .ok t → FirstOpensOwn π num no base t)
      (fun a b => (∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
        QN π (NTuple F π no rad rd) (t, a.2)) ∧ b.1 = (a.1.1, b.1.2))
      p.err :=
  leads_alike
    (pieceOf (C := ckP .two) (F := F) (W := W)
      (held (P := P) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave)) base (dB :: dt) []
      ⟨fun _ _ w => w, (e, εt)⟩) p hb hbase hds h0 herr _ _
    (k12_game_heldO P S enter leave F W π num no L mC mS mW rad rd base dB dt e v₀ εt _ rfl rfl
      rfl rfl HEq.rfl hA hP h1 hlog hle)

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.alike_carried
#print axioms VerifiableInference.Desc.K12.Coin.k12_game_alike
#print axioms VerifiableInference.Desc.K12.Coin.k12_game_alikeO
