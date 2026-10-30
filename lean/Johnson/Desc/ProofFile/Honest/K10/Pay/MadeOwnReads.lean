-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeOwnReads.lean: the reads' data (`u3Rows`, Johnson/HonestTrace/U3Rows.lean: the array "U3" of a segment's moment 1) are ready at
every list of challenges that fits the declared rounds and reaches the sending, where the seat passes the public test and the
maker of the segment's vector returns at the challenges in front of the sending. General in the public part, the ground and the
covered positions: no head, no thread.

  `fit_take`          a beginning of a list that fits declared rounds fits the beginning of these rounds
  `heardWhy_none`     the three clauses of the test on what was heard
  `vals_ready`        the values' field `ready` at a segment of the shape
  `reads_ready_none`  at an address that is no seat's the filling is ready at every list
  **`reads_ready`**    at a seat's address

THE ONE PREMISE THAT READS A CHALLENGE BEYOND ITS FORM is hv: the maker `SegVals.vec` returns at the challenges in front of the
sending. It is a premise here.

Limits. hfitS (the public test `u3Fits` at the seat) and hv are premises. Nothing on what the data hold.
-/
import Johnson.HonestTrace.U3Fit.ReadsLight
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open OnBytes.Model (Head.Covered)
open OnBytes.HonestTrace (Seat seatAt pairOf heardOf)
open OnBytes.HonestTrace.U3 (SegVals valsAt u3Seats u3Fits u3Vals u3Rows heardWhy errOf ask)
open OnBytes.HonestTrace.U3.Fit (u3Fits_halves seatHalf valsHalf lookup_graph)

/-- A beginning of a list that fits declared rounds fits the beginning of these rounds. -/
theorem fit_take : ∀ {ds : List Fmt.DeclaredRound} {hs : List Fmt.Drawn} (n : Nat),
    drawsFit ds hs = true → drawsFit (ds.take n) (hs.take n) = true
  | _, _, 0, _ => by
    rw [List.take_zero, List.take_zero]
    rfl
  | [], [], _ + 1, _ => rfl
  | [], _ :: _, _ + 1, h => by simp [drawsFit] at h
  | _ :: _, [], _ + 1, h => by simp [drawsFit] at h
  | d :: ds, R :: hs, n + 1, h => by
    have h' : (drawFit d R && drawsFit ds hs) = true := h
    obtain ⟨a, b⟩ := Eq.mp (Bool.and_eq_true _ _) h'
    rw [List.take_succ_cons, List.take_succ_cons]
    show (drawFit d R && drawsFit (ds.take n) (hs.take n)) = true
    rw [a, fit_take n b]
    rfl

/-- The three clauses of the test on what was heard. -/
theorem heardWhy_none {Z : Pub} {V : SegVals} {hd : List Fmt.Drawn} (h1 : hd.length = V.front)
    (h2 : drawsFit (Z.D.1.take V.front) hd = true) (h3 : ∃ v, V.vec hd = .ok v) :
    heardWhy Z V hd = none := by
  obtain ⟨v, h3⟩ := h3
  show errOf ((ask "U3: the challenges are not as many as the rounds in front of the sending"
      (hd.length == V.front)).bind fun _ =>
    (ask "U3: a challenge has not the form that its round declares"
      (drawsFit (Z.D.1.take V.front) hd)).bind fun _ => (V.vec hd).bind fun _ => pure ()) = none
  rw [beq_iff_eq.2 h1, h2, h3]
  rfl

/-- The values' field `ready` at a segment of the shape. -/
theorem vals_ready {Z : Pub} {G : Ground} {cov : Head.Covered} {l : Nat} {V : SegVals}
    (hl : l < G.first.shape.link.length) (hV : valsAt Z G cov l = .ok V) {hd : List Fmt.Drawn}
    (hw : heardWhy Z V hd = none) : (u3Vals Z G cov).ready hd l = true := by
  unfold u3Vals
  dsimp only
  rw [lookup_graph _ _ _ (List.mem_range.2 hl), hV]
  show (heardWhy Z V hd).isNone = true
  rw [hw]
  rfl

/-- At an address that is no seat's the filling is ready at every list. -/
theorem reads_ready_none {Z : Pub} {G : Ground} {cov : Head.Covered} {a : MsgAddr}
    (hs : seatAt (u3Seats Z G) a = none) (heard : List Fmt.Drawn) :
    (u3Rows Z G cov).readyAt heard a = true := by
  have hp : pairOf (u3Seats Z G) a = none := by
    unfold pairOf
    rw [hs]
    rfl
  have hh : heardOf (u3Seats Z G) a = 0 := by
    unfold heardOf
    rw [hs]
    rfl
  have hfind : ((u3Seats Z G).map fun s => (s.addr, u3Fits Z G cov s)).find?
      (fun x => x.1 == a) = none := by
    rw [List.find?_map]
    have hs' : (u3Seats Z G).find? (fun s => s.addr == a) = none := hs
    show Option.map _ ((u3Seats Z G).find? fun s => s.addr == a) = _
    rw [hs']
    rfl
  show (decide (heardOf (u3Seats Z G) a ≤ heard.length) &&
    (((pairOf (u3Seats Z G) a).all fun x =>
        layFits G.first.shape G.first.layout &&
          msgFits G.first.codes G.first.shape G.first.layout x.1 x.2 &&
          (u3Vals Z G cov).ready (heard.take (heardOf (u3Seats Z G) a)) x.1) &&
      (((u3Seats Z G).map fun s => (s.addr, u3Fits Z G cov s)).find?
        fun x => x.1 == a).all (·.2))) = true
  rw [hp, hfind, hh]
  simp

/-- **THE READS' DATA ARE READY** at a seat's address. -/
theorem reads_ready {Z : Pub} {G : Ground} {cov : Head.Covered} {a : MsgAddr} {s : Seat}
    (hs : seatAt (u3Seats Z G) a = some s) (hseg : s.seg < G.first.shape.link.length)
    (hfitS : u3Fits Z G cov s = true) {heard : List Fmt.Drawn}
    (hfit : drawsFit (Z.D.1.take heard.length) heard = true) (hlen : s.heard ≤ heard.length)
    (hv : ∀ V, valsAt Z G cov s.seg = .ok V → ∃ v, V.vec (heard.take s.heard) = .ok v) :
    (u3Rows Z G cov).readyAt heard a = true := by
  have hone : u3Fits Z G cov s = true := hfitS
  rw [u3Fits_halves, Bool.and_eq_true] at hfitS
  obtain ⟨hA, hB⟩ := hfitS
  unfold seatHalf at hA
  simp only [Bool.and_eq_true] at hA
  obtain ⟨⟨⟨⟨-, hlay⟩, hmsg⟩, -⟩, -⟩ := hA
  unfold valsHalf at hB
  cases hV : valsAt Z G cov s.seg with
  | error e =>
    rw [hV] at hB
    cases hB
  | ok V =>
    rw [hV] at hB
    have hfr : V.front = s.heard := beq_iff_eq.1 (Eq.mp (Bool.and_eq_true _ _) hB).1
    have hp : pairOf (u3Seats Z G) a = some (s.seg, s.array.message) := by
      unfold pairOf
      rw [hs]
      rfl
    have hh : heardOf (u3Seats Z G) a = s.heard := by
      unfold heardOf
      rw [hs]
      rfl
    have hfind : ((u3Seats Z G).map fun s => (s.addr, u3Fits Z G cov s)).find?
        (fun x => x.1 == a) = some (s.addr, u3Fits Z G cov s) := by
      rw [List.find?_map]
      have hs' : (u3Seats Z G).find? (fun s => s.addr == a) = some s := hs
      show Option.map _ ((u3Seats Z G).find? fun s => s.addr == a) = _
      rw [hs']
      rfl
    have hl1 : (heard.take s.heard).length = V.front := by
      rw [List.length_take, hfr]
      omega
    have hf1 : drawsFit (Z.D.1.take V.front) (heard.take s.heard) = true := by
      have k := fit_take s.heard hfit
      rw [List.take_take, Nat.min_eq_left hlen] at k
      rw [hfr]
      exact k
    have hrd := vals_ready hseg hV (heardWhy_none hl1 hf1 (hv V hV))
    show (decide (heardOf (u3Seats Z G) a ≤ heard.length) &&
      (((pairOf (u3Seats Z G) a).all fun x =>
          layFits G.first.shape G.first.layout &&
            msgFits G.first.codes G.first.shape G.first.layout x.1 x.2 &&
            (u3Vals Z G cov).ready (heard.take (heardOf (u3Seats Z G) a)) x.1) &&
        (((u3Seats Z G).map fun s => (s.addr, u3Fits Z G cov s)).find?
          fun x => x.1 == a).all (·.2))) = true
    rw [hp, hfind, hh]
    simp only [Option.all_some, hlay, hmsg, hrd, hone, Bool.and_self, Bool.and_true,
      decide_eq_true_eq]
    exact hlen

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.fit_take
#print axioms ProofFile.Honest.K10.heardWhy_none
#print axioms ProofFile.Honest.K10.vals_ready
#print axioms ProofFile.Honest.K10.reads_ready_none
#print axioms ProofFile.Honest.K10.reads_ready
