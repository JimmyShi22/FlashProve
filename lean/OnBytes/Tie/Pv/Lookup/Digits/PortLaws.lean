-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Digits/PortLaws.lean: the laws `CbQ.DatQ.DatOK` of the digits' numbering at
the verifier's own record of a smallness test, for a variable record, from a Bool test on the shape.

The test walks over the pieces of the two calls, the combinations (tau), the trees' numbers (2^rK),
the joint rows (2^d) and the tables' values. It never walks over the joint keys (2^v) or the digits
(2 mz tau), so it runs at full size.

Main names:
  `TailOK tl`, `tailTest`, `tailOK_of_test`: what is asked of the shape: `Port.OK`; two calls; for
    each piece Cp = mz ≤ CP, CP * Rp = 2^b, off + 2^b ≤ 2^n, its rows below tau; every combination
    lies in a piece; two pieces of a call whose rows or keys meet are one; one count for each call,
    on the trees' numbers.
  `dgP_fwd`, `dgP_bwd`: `posN` and `digAtN` are inverse to each other.
  `count_period`: the count of a predicate that reads its argument modulo b alone.
  `shapeTest`, `dgP_port_ok`: shapeTest tl pp = true gives (portQ tl).DatOK (2^t2D0) (2^t2D1) pp.
Limits: `DatOK` says that the numbering is lawful, not that it is the verifier's: a piece moved by
one key still passes `shapeTest`. PortSeam.lean has the stricter test. That the test follows from
the success of the verifier's own routines is not shown.

-/
import OnBytes.Tie.Pv.Lookup.Digits.PortDat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.DgP
open OnBytes OnBytes.Model CbQ Cb.LdLkp Cb.Lkp

/-- Two pieces agree in all that the maps read. -/
def Piece.same (p p' : Piece) : Prop :=
  p.off = p'.off ∧ p.r0 = p'.r0 ∧ p.Rp = p'.Rp ∧ p.CP = p'.CP ∧ p.Cp = p'.Cp ∧ p.b = p'.b

instance (p p' : Piece) : Decidable (Piece.same p p') := by unfold Piece.same; infer_instance

/-- What is asked of the shape. -/
structure TailOK (tl : HTailF2) : Prop where
  port : Port.OK tl.f9
  nc   : tl.f9.NC = 2
  pc   : ∀ q < tl.f9.NC, ∀ p ∈ piecesL tl q, p.Cp = tl.mz ∧ p.Cp ≤ p.CP ∧ p.CP * p.Rp = 2 ^ p.b ∧
           p.off + 2 ^ p.b ≤ 2 ^ Port.nOf tl.f9 q ∧ p.r0 + p.Rp ≤ tl.tau
  rows : ∀ q < tl.f9.NC, ∀ u < tl.tau, (pieceAt tl q u).isSome = true
  one  : ∀ q < tl.f9.NC, ∀ p ∈ piecesL tl q, ∀ p' ∈ piecesL tl q,
           ((p.r0 < p'.r0 + p'.Rp ∧ p'.r0 < p.r0 + p.Rp) ∨ (p.off < p'.off + 2 ^ p'.b ∧ p'.off <
               p.off + 2 ^ p.b)) →
           Piece.same p p'
  cnt  : ∀ c < tl.f9.NC, 2 ^ tl.f9.dT * Nat.count (fun y => Port.fK tl.f9 y = c) (2 ^ tl.f9.rK) =
           padCnt (padsP tl.f9) ((portQ tl).zRow c) + tl.mz * tl.tau

/-- The same as a Bool test. -/
def tailTest (tl : HTailF2) : Bool :=
  decide (Port.OK tl.f9) && decide (tl.f9.NC = 2) &&
  decide (∀ q < tl.f9.NC, ∀ p ∈ piecesL tl q, p.Cp = tl.mz ∧ p.Cp ≤ p.CP ∧ p.CP * p.Rp = 2 ^ p.b ∧
    p.off + 2 ^ p.b ≤ 2 ^ Port.nOf tl.f9 q ∧ p.r0 + p.Rp ≤ tl.tau) &&
  decide (∀ q < tl.f9.NC, ∀ u < tl.tau, (pieceAt tl q u).isSome = true) &&
  decide (∀ q < tl.f9.NC, ∀ p ∈ piecesL tl q, ∀ p' ∈ piecesL tl q,
    ((p.r0 < p'.r0 + p'.Rp ∧ p'.r0 < p.r0 + p.Rp) ∨ (p.off < p'.off + 2 ^ p'.b ∧ p'.off < p.off + 2
        ^ p.b)) →
    Piece.same p p') &&
  decide (∀ c < tl.f9.NC, 2 ^ tl.f9.dT * Nat.count (fun y => Port.fK tl.f9 y = c) (2 ^ tl.f9.rK) =
    padCnt (padsP tl.f9) ((portQ tl).zRow c) + tl.mz * tl.tau)

theorem tailOK_of_test {tl : HTailF2} (h : tailTest tl = true) : TailOK tl := by
  simp only [tailTest, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

variable {tl : HTailF2}

/-- Forwards: a digit's joint key is below 2^v, leads back to the digit, and is a key of the digit's
call. -/
theorem dgP_fwd (hT : TailOK tl) {q c u : ℕ} (hq : q < 2) (hc : c < tl.mz) (hu : u < tl.tau) :
    posN tl q c u < 2 ^ tl.f9.v ∧ digAtN tl (posN tl q c u) = some (q, c, u) ∧
      Port.fK tl.f9 (posN tl q c u) = q := by
  obtain ⟨_, _, h3, _, _, h6⟩ := hT.port
  have hqN : q < tl.f9.NC := by rw [hT.nc]; exact hq
  obtain ⟨_, hn, hb⟩ := h6 q hqN
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (hT.rows q hqN u hu)
  have hmem : p ∈ piecesL tl q := List.mem_of_find?_eq_some hp
  have hpred := List.find?_some hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred
  obtain ⟨hCp, hCP, hRC, hoff, _⟩ := hT.pc q hqN p hmem
  have hcCp : c < p.Cp := by rw [hCp]; exact hc
  have hcCP : c < p.CP := lt_of_lt_of_le hcCp hCP
  have hr : u - p.r0 < p.Rp := by omega
  obtain ⟨inner, hinner⟩ : ∃ inner, inner = c + p.CP * (u - p.r0) := ⟨_, rfl⟩
  have hin : inner < 2 ^ p.b := by
    rw [← hRC, hinner]
    calc c + p.CP * (u - p.r0) < p.CP + p.CP * (u - p.r0) := by omega
      _ = p.CP * (u - p.r0 + 1) := by ring
      _ ≤ p.CP * p.Rp := Nat.mul_le_mul_left _ hr
  obtain ⟨kn, hknd⟩ : ∃ kn, kn = p.off + inner := ⟨_, rfl⟩
  have hkn : keyNo tl q c u = kn := by
    unfold keyNo
    rw [hp, hknd, hinner]
    rfl
  have hknlt : kn < 2 ^ (Port.io tl.f9 q + tl.f9.dT) := by rw [← hn]; omega
  obtain ⟨s1, s2⟩ := Cb.ldLkpShift_split _ _ _ hknlt
  obtain ⟨b1, b2, _⟩ := hb _ s1
  obtain ⟨e1, e2, e3⟩ := Cb.ldLkpShift_num tl.f9.dT tl.f9.rK (kn % 2 ^ tl.f9.dT)
    (Port.fst tl.f9 q + kn / 2 ^ tl.f9.dT) s2 (lt_of_lt_of_le b1 h3)
  have hpos : posN tl q c u =
      (Port.fst tl.f9 q + kn / 2 ^ tl.f9.dT) + 2 ^ tl.f9.rK * (kn % 2 ^ tl.f9.dT) := by
    unfold posN posK
    rw [hkn]
  have ht : treeOf tl.f9 (posN tl q c u) = Port.fst tl.f9 q + kn / 2 ^ tl.f9.dT := by
    unfold treeOf
    rw [hpos, e3]
  refine ⟨by rw [hpos]; exact e1, ?_, ?_⟩
  · have hk : knOf tl.f9 (posN tl q c u) = kn := by
      unfold knOf
      rw [ht, b2, hpos, e2, Nat.add_sub_cancel_left, Nat.mod_add_div]
    unfold digAtN
    rw [ht, if_pos b1, b2, hk]
    have hex : (pieceK tl q kn).isSome = true := by
      unfold pieceK
      rw [List.find?_isSome]
      refine ⟨p, hmem, ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.1 hex
    have hmem' : p' ∈ piecesL tl q := List.mem_of_find?_eq_some hp'
    have hpred' := List.find?_some hp'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred'
    obtain ⟨o1, o2, o3, o4, o5, _⟩ := hT.one q hqN p hmem p' hmem' (Or.inr ⟨by omega, by omega⟩)
    rw [hp']
    show cut p' q kn = _
    have hsub : kn - p'.off = c + p.CP * (u - p.r0) := by rw [← o1, ← hinner]; omega
    have hCPpos : 0 < p.CP := by omega
    unfold cut
    rw [hsub, ← o4, ← o3, ← o5, ← o2, Nat.add_mul_div_left _ _ hCPpos, Nat.div_eq_of_lt hcCP,
        Nat.zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcCP, if_pos ⟨hr, hcCp⟩]
    have e : p.r0 + (u - p.r0) = u := by omega
    rw [e]
  · unfold Port.fK
    rw [hpos, e3, if_pos b1, b2]

/-- Backwards: a joint key that leads to a digit is that digit's joint key. -/
theorem dgP_bwd (hT : TailOK tl) {X q c u : ℕ} (hX : X < 2 ^ tl.f9.v) (hd : digAtN tl X = some (q,
    c, u)) :
    q < 2 ∧ c < tl.mz ∧ u < tl.tau ∧ posN tl q c u = X := by
  obtain ⟨_, _, _, h4, _, _⟩ := hT.port
  unfold digAtN at hd
  by_cases hy : treeOf tl.f9 X < tl.f9.NT
  · rw [if_pos hy] at hd
    obtain ⟨y, hyd⟩ : ∃ y, y = treeOf tl.f9 X := ⟨_, rfl⟩
    obtain ⟨kn, hknd⟩ : ∃ kn, kn = knOf tl.f9 X := ⟨_, rfl⟩
    rw [← hyd] at hy
    rw [← hyd, ← hknd] at hd
    obtain ⟨c1, c2, c3⟩ := h4 y hy
    obtain ⟨q0, hq0⟩ : ∃ q0, q0 = Port.co tl.f9 y := ⟨_, rfl⟩
    rw [← hq0] at hd c1 c2 c3
    have hq2 : q0 < 2 := by rw [← hT.nc]; exact c1
    obtain ⟨p, hp, hcut⟩ := Option.bind_eq_some_iff.1 hd
    have hmem : p ∈ piecesL tl q0 := List.mem_of_find?_eq_some hp
    have hpred := List.find?_some hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred
    obtain ⟨hCp, _, _, _, hrow⟩ := hT.pc q0 c1 p hmem
    unfold cut at hcut
    obtain ⟨r, hrd⟩ : ∃ r, r = (kn - p.off) / p.CP := ⟨_, rfl⟩
    obtain ⟨c', hcd⟩ : ∃ c', c' = (kn - p.off) % p.CP := ⟨_, rfl⟩
    rw [← hrd, ← hcd] at hcut
    by_cases hcond : r < p.Rp ∧ c' < p.Cp
    · rw [if_pos hcond] at hcut
      simp only [Option.some.injEq, Prod.mk.injEq] at hcut
      obtain ⟨rfl, rfl, rfl⟩ := hcut
      refine ⟨hq2, by rw [← hCp]; exact hcond.2, by omega, ?_⟩
      -- the piece by rows is the same piece
      have hex : (pieceAt tl q0 (p.r0 + r)).isSome = true := by
        unfold pieceAt
        rw [List.find?_isSome]
        refine ⟨p, hmem, ?_⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        omega
      obtain ⟨p', hp'⟩ := Option.isSome_iff_exists.1 hex
      have hmem' : p' ∈ piecesL tl q0 := List.mem_of_find?_eq_some hp'
      have hpred' := List.find?_some hp'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hpred'
      obtain ⟨o1, o2, _, o4, _, _⟩ := hT.one q0 c1 p hmem p' hmem' (Or.inl ⟨by omega, by omega⟩)
      have hkey : keyNo tl q0 c' (p.r0 + r) = kn := by
        unfold keyNo
        rw [hp']
        show inP p' _ _ = kn
        unfold inP
        rw [← o1, ← o2, ← o4, Nat.add_sub_cancel_left, hcd, hrd, Nat.mod_add_div]
        omega
      unfold posN posK
      rw [hkey]
      obtain ⟨x1, _⟩ := Cb.ldLkpShift_split tl.f9.dT tl.f9.rK X hX
      have hf : y - Port.fst tl.f9 q0 < 2 ^ Port.io tl.f9 q0 := by omega
      obtain ⟨_, n2, n3⟩ := Cb.ldLkpShift_num (Port.io tl.f9 q0) tl.f9.dT (y - Port.fst tl.f9 q0) (X
          / 2 ^ tl.f9.rK) hf x1
      have hkn' : kn = X / 2 ^ tl.f9.rK + 2 ^ tl.f9.dT * (y - Port.fst tl.f9 q0) := by
        rw [hknd]
        unfold knOf
        rw [← hyd, ← hq0]
      rw [hkn', n2, n3, Nat.add_sub_cancel' c2, hyd]
      unfold treeOf
      exact Nat.mod_add_div X _
    · rw [if_neg hcond] at hcut
      exact absurd hcut (by simp)
  · rw [if_neg hy] at hd
    exact absurd hd (by simp)

/-- The count of a predicate that reads its argument modulo b alone. -/
theorem count_period (P : ℕ → Prop) [DecidablePred P] (b : ℕ) (hP : ∀ X, P X ↔ P (X % b)) :
    ∀ a, Nat.count P (b * a) = a * Nat.count P b
  | 0 => by simp
  | a + 1 => by
    have e : Nat.count (fun k => P (b * a + k)) b = Nat.count P b := by
      rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range]
      refine congrArg Finset.card (Finset.filter_congr fun k _ => ?_)
      exact (hP _).trans (by rw [Nat.mul_add_mod]; exact (hP k).symm)
    rw [Nat.mul_succ, Nat.count_add, count_period P b hP a, e]
    ring

theorem qOf_beq {q : ℕ} (hq : q < 2) : qOf (q == 1) = q := by
  interval_cases q <;> rfl

theorem qOf_lt (b : Bool) : qOf b < 2 := by cases b <;> decide

/-- The test on the shape: the tail's, and the two parts of testOK that walk over rows and calls. -/
def shapeTest (tl : HTailF2) (pp : ℕ) : Bool :=
  tailTest tl && testRow (portQ tl) (2 ^ t2D0) (2 ^ t2D1) && testCall (portQ tl) pp

/-- `DatOK` of `portQ tl`, for a variable record, from the test on the shape. It says that the
numbering
is lawful. That it is the verifier's asks more of the record: `portTest` (PortSeam.lean). -/
theorem dgP_port_ok {pp : ℕ} (h : shapeTest tl pp = true) : (portQ tl).DatOK (2 ^ t2D0) (2 ^ t2D1)
    pp := by
  simp only [shapeTest, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hT := tailOK_of_test h1
  refine dgP_ok_of_parts (portQ tl) ?_ ?_ ?_ h2 h3
  · rintro ⟨b, ⟨c, hc⟩, ⟨u, hu⟩⟩
    obtain ⟨f1, f2, f3⟩ := dgP_fwd hT (qOf_lt b) hc hu
    refine ⟨f1, ?_, f3⟩
    show digAtP tl (posN tl (qOf b) c u) = _
    unfold digAtP
    rw [f2]
    simp only [dif_pos hc, dif_pos hu]
    cases b <;> rfl
  · intro X hX
    refine ⟨fun p hp => ?_, ((Cb.port_lt tl.f9 hT.port).1 X)⟩
    have hd : digAtP tl X = some p := Option.mem_def.1 hp
    unfold digAtP at hd
    cases hN : digAtN tl X with
    | none => rw [hN] at hd; exact absurd hd (by simp)
    | some t =>
      obtain ⟨q, c, u⟩ := t
      obtain ⟨g1, g2, g3, g4⟩ := dgP_bwd hT hX hN
      rw [hN] at hd
      simp only [dif_pos g2, dif_pos g3, Option.some.injEq] at hd
      subst hd
      show posN tl (qOf (q == 1)) c u = X
      rw [qOf_beq g1]
      exact g4
  · intro c hc
    have hc2 : c < 2 := by
      have e : (portQ tl).nc = 2 := hT.nc
      omega
    have hper : ∀ X, Port.fK tl.f9 X = c ↔ Port.fK tl.f9 (X % 2 ^ tl.f9.rK) = c := fun X => by
      unfold Port.fK
      rw [Nat.mod_mod]
    have e1 : ((Finset.range (2 ^ (portQ tl).v)).filter fun X => (portQ tl).fK X = c).card =
        2 ^ tl.f9.dT * Nat.count (fun y => Port.fK tl.f9 y = c) (2 ^ tl.f9.rK) := by
      rw [← Nat.count_eq_card_filter_range]
      show Nat.count (fun X => Port.fK tl.f9 X = c) (2 ^ (tl.f9.dT + tl.f9.rK)) = _
      rw [pow_add, Nat.mul_comm (2 ^ tl.f9.dT)]
      exact count_period _ _ hper _
    have e2 : (Finset.univ.filter fun p : Bool × Pl tl => (portQ tl).call p.1 = c).card = tl.mz *
        tl.tau := by
      have e3 : (Finset.univ.filter fun p : Bool × Pl tl => (portQ tl).call p.1 = c) =
          ({c == 1} : Finset Bool) ×ˢ (Finset.univ : Finset (Pl tl)) := by
        ext ⟨b, i⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
            Finset.mem_singleton, and_true]
        show qOf b = c ↔ b = (c == 1)
        interval_cases c <;> cases b <;> decide
      rw [e3, Finset.card_product, Finset.card_singleton, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin,
        Fintype.card_fin, Nat.one_mul]
    rw [e1, e2]
    exact hT.cnt c hc

#print axioms dgP_fwd
#print axioms dgP_bwd
#print axioms count_period
#print axioms dgP_port_ok

end OnBytes.DgP
