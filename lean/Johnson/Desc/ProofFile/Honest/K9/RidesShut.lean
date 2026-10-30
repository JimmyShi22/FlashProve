-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/RidesShut.lean: THE STATEMENT "RIDES PAST" (`RidesPastS`, Honest/Thread/PaysS.lean) AT THE SUB-PROTOCOL "THE SEGMENT IS
SHUT" OF EACH OF THE 25 SEGMENTS, at the first chain's letters (`lettersHead`) with a family f of the kinds' clauses of
"keeps": an item that is open there, and that the row neither shuts nor owes, passes over it.

Why. The step writes the open segment's book-keeping alone (`ShutKeeps`: s' = s.putLink …): the statement, the list of
commitment trees, `out`, the rows on the table and what is left for the pending row stay.

  `shutSort`, `shut_open_sorts`   by Lean's kernel, at the 25 numbers 14 l + `IM.nAt l` + 6: every open item that the row neither shuts nor
                      owes is unmarked, pinW, pile, pinI, a part of `parts4` of some segment, or wo, carry, pinKept of some segment
  `shut_open_bites`   a control: with carry struck from the test the answer turns
  `shut_open_cases`   the same at one segment and one item
  `shut_of_keeps`     from the thread's keeps at that number, under hf, the step's own clause `ShutKeeps`
  **`k9_ridesPastS_shut`**   `RidesPastS` there, at every Said. f is a variable, with hf: f at this kind gives this kind's clause.
                      hc: the letter carryX says the same in front of and behind the laying of a shut book-keeping
  **`k9_ridesPastS_shut_exact`**   that at carryX := `carryExact`, where hc is the library's `carryExact_shut`

Limits. The library's hypothesis `AtMgA` is a premise. Nothing here says that any item holds at any state. This file proves no
property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.KeepsBehind
import Johnson.Desc.ProofFile.Honest.Thread.FirstRows
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.ProofFile.Honest.Thread.PinRides
import Johnson.Desc.ProofFile.Honest.Thread.HeadPinW
import Johnson.Desc.ProofFile.Honest.Thread.RowPileRides
import Johnson.Desc.ProofFile.Honest.Thread.CarryRides
import Johnson.Desc.ProofFile.Honest.Thread.WoClose
import Johnson.Desc.ProofFile.Honest.Thread.ArmsQuiet
import Johnson.Desc.ProofFile.Honest.K4.Law.WoRidesHead
import Johnson.Desc.K10.Honest.CarryAtLink
import Johnson.Goal.HonestTrace.ConstrAtThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc
open VerifiableInference.Desc.First (S Item)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K2.Honest (carryExact)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

/-- True of the sorts of item that pass over "the segment is shut". -/
def shutSort : Item → Bool
  | .unmarked | .pinW | .pile | .pinI => true
  | .wo _ | .carry _ | .pinKept _ => true
  | .constr _ q => P5J.parts4.contains q
  | _ => false

/-- At the shut of segment l: each open item passes the test t, or the row shuts or owes it. -/
def shutRowTest (t : Item → Bool) (l : Nat) : Bool :=
  (fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
    (FirstRows.rows P5J.At.links P5J.At.ps) (14 * l + IM.nAt l + 6)).all fun i =>
    (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 6)).shuts.contains i ||
      (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 6)).owes.contains i || t i

set_option maxRecDepth 1000000 in
theorem shut_open_sorts : ((List.range 25).all fun l => shutRowTest shutSort l) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with carry struck from the test the answer turns. -/
theorem shut_open_bites :
    ((List.range 25).all fun l =>
      shutRowTest (fun i => shutSort i && !(match i with | .carry _ => true | _ => false)) l) = false := by
  decide +kernel

theorem shut_open_cases {l : Nat} (hl : l < 25) {i : Item}
    (h1 : i ∈ fwdOpen (VerifiableInference.Desc.First.start P5J.At.links)
      (FirstRows.rows P5J.At.links P5J.At.ps) (14 * l + IM.nAt l + 6))
    (h2 : i ∉ (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 6)).shuts)
    (h3 : i ∉ (FirstRows.rows P5J.At.links P5J.At.ps (14 * l + IM.nAt l + 6)).owes) :
    i = .unmarked ∨ i = .pinW ∨ i = .pile ∨ i = .pinI ∨ (∃ m, i = .wo m) ∨ (∃ m, i = .carry m) ∨
      (∃ m, i = .pinKept m) ∨ (∃ m q, q ∈ P5J.parts4 ∧ i = .constr m q) := by
  have t := List.all_eq_true.1 (List.all_eq_true.1 shut_open_sorts l (List.mem_range.2 hl)) i h1
  rw [Bool.or_eq_true, Bool.or_eq_true] at t
  rcases t with (t | t) | t
  · exact absurd (List.contains_iff_mem.1 t) h2
  · exact absurd (List.contains_iff_mem.1 t) h3
  · cases i with
    | unmarked => exact Or.inl rfl
    | pinW => exact Or.inr (Or.inl rfl)
    | pile => exact Or.inr (Or.inr (Or.inl rfl))
    | pinI => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    | wo m => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩))))
    | carry m => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩)))))
    | pinKept m => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨m, rfl⟩))))))
    | constr m q =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m, q, List.contains_iff_mem.1 t, rfl⟩))))))
    | _ => simp [shutSort] at t

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (f : KindName → Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- From the thread's keeps at the shut's number: the step's own clause. -/
theorem shut_of_keeps (hf : ∀ pl s s', f KindName.K9 pl s s' → k9KeepsAt cF Zp pl s s') {l : ℕ} (hl : l < 25)
    {s s' : TS}
    (hK : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps (14 * l + IM.nAt l + 6) s s') :
    ShutKeeps s s' := by
  obtain ⟨Lk, p, ww, Qc, bE, bS, Sd, Hc⟩ := seats_at_head h hl
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e := Hc.atS
  rw [Sd.hears] at e
  have hb : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.bs[14 * l + IM.nAt l + 6]? =
      some bS := e
  have hk9 := hf _ _ _ ((head_keeps_kind h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hb
    (kind_shut_at h hl e) s s').1 hK)
  obtain ⟨-, -, e3⟩ := IM.k9Where_fields Hc.numbers
  have e1 := piece_at_seat h.scope h.reads O hl Hc.numbers
  exact shut_of_k9KeepsAt Hc (by show _ + 3 + 2 = p.pieceEq + 2; omega) hk9

/-- **"Rides past" at "the segment is shut".** -/
theorem k9_ridesPastS_shut (hf : ∀ pl s s', f KindName.K9 pl s s' → k9KeepsAt cF Zp pl s s')
    (hc : ∀ (m : ℕ) (s : TS) (L : LinkCtx), s.link? = some L → ∀ (z : ProofFile.InstPub) (y y' : Strs) (v : WtF),
      carryX m (z, s) y v → carryX m (z, s.putLink (Desc.K9.closed L L.check.frame)) y' v)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (l : ℕ) (hl : l < 25) :
    RidesPastS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said (14 * l + IM.nAt l + 6) := by
  have hSK : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.keeps
      (14 * l + IM.nAt l + 6) s s' → ShutKeeps s s' :=
    fun s s' hK => shut_of_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd f w hf hl hK
  obtain ⟨Lk, p, ww, Qc, bE, bS, Sd, Hc⟩ := seats_at_head h hl
  have e := Hc.atS
  rw [Sd.hears] at e
  have hb : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread.bs[14 * l + IM.nAt l + 6]? =
      some bS := e
  have hp := head_place h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hb
  refine ridesPastS_shares _ _ fun i h1 h2 h3 => ?_
  rcases shut_open_cases hl h1 h2 h3 with e | e | e | e | ⟨m, e⟩ | ⟨m, e⟩ | ⟨m, e⟩ | ⟨m, q, hq, e⟩ <;> rw [e]
  · exact ridesPastAtS_of _ _ (ridesPastAt_unmarked h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w
      fun s s' hK => (hSK s s' hK).mark)
  · exact ridesPastAtS_of _ _ (ridesPastAt_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w _)
  · exact ridesPastAtS_of _ _ (ridesPastAt_pile h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w
      fun s s' hK => by
        obtain ⟨L, _, rfl⟩ := (hSK s s' hK).laid
        exact ⟨(putLink_four s _).1, (putLink_four s _).2.1, putLink_rows s _⟩)
  · exact ridesPastAtS_of _ _ (ridesPastAt_pinI h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w
      fun s s' hK => (shutKeeps_four (hSK s s' hK)).1)
  · exact K4.k4_ridesPastAtS_wo_head h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w Said _ m hp
      fun _ s _ _ s' _ hK => shutKeeps_four (hSK s s'
        ((head_keeps h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w hp s s').2 hK))
  · exact ridesPastAtS_of _ _ (ridesPastAt_carry_of h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w m
      fun s s' hK z y y' v h0 => by
        obtain ⟨L, hL, rfl⟩ := (hSK s s' hK).laid
        exact hc m s L hL z y y' v h0)
  · exact ridesPastAtS_of _ _ (ridesPastAt_pinKept h H Q test carryX item n₁ n₂ b₀ Vd Rd (kpBy f) w m
      fun s s' hK => (shutKeeps_four (hSK s s' hK)).1)
  · exact ridesPastAtS_of _ _ (OnBytes.HonestTrace.ridesPastAt_constr h H Q test carryX item n₁ n₂ b₀ Vd Rd
      (kpBy f) w _ m hq)

/-- **That at the letter `carryExact`.** -/
theorem k9_ridesPastS_shut_exact (hf : ∀ pl s s', f KindName.K9 pl s s' → k9KeepsAt cF Zp pl s s')
    (arr : ℕ → ℕ → ℕ) (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (l : ℕ) (hl : l < 25) :
    RidesPastS (lettersHead h H Q test (carryExact Zp arr) item n₁ n₂ b₀ Vd Rd (kpBy f) w).thread Said
      (14 * l + IM.nAt l + 6) :=
  k9_ridesPastS_shut h H Q test (carryExact Zp arr) item n₁ n₂ b₀ Vd Rd f w hf
    (fun m _ _ hL z y y' v h0 => (K10.LeftIs.carryExact_shut Zp arr m z z hL y y' v).1 h0) Said l hl

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.shut_open_sorts
#print axioms ProofFile.Honest.K9.shut_open_bites
#print axioms ProofFile.Honest.K9.shut_open_cases
#print axioms ProofFile.Honest.K9.shut_of_keeps
#print axioms ProofFile.Honest.K9.k9_ridesPastS_shut
#print axioms ProofFile.Honest.K9.k9_ridesPastS_shut_exact
