-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/Join.lean: the extension of the joint key vector at any point, written as
a sum over the calls, each call at a point of its own.

Statements and proofs, over the library's Blocks.ext and Blocks.eqN and over the jointKey of
OnBytes/Tie/Pv/Lookup/Ends/Joint.lean. "The port" is the Lean verifier under OnBytes/.
Main names:
  `join_identity`: under Prem h, for any field E, any key vectors kv, any θ and α and any point pt:
    α less the extension of the joint key vector (h.v = dT + rK variables) at pt is
    `joinRhs h kv θ α pt`. That is the sum over the calls c of
    eC c * (α - c θ - the extension of call c's key vector at the call's own point zkC c), plus the
    sum over the trees y from NT on of
    eq(the last rK coordinates of pt, y) * (α - call 0's padding row).
  `Prem h`: seven clauses on the numbers of the port's record Forest.Shape. For every call: it has
    no more trees than the forest has numbers; its first tree is a multiple of the number of its
    trees; the trees from its first on are marked as its own; its trees lie below NT; its keys fill
    its trees. Every tree below NT is some call's. NT ≤ 2^rK.
  `premOK`, `prem_of_ok`: the seven clauses as a test with a Bool answer; premOK h = true gives
    Prem h.
  `eC`, `zkC`: the weight and the point of a call, as functions of pt and the shape's numbers.
The proof reads the library's Blocks.LkPar.CallsOK.ext_leafK (Blocks/LookupCalls.lean) at these
numbers (`lkP`, `clP`, `Prem.callsOK`, `Prem.keysOf`); `ext_rest` has the trees from NT on.
Limits: join_identity stands under Prem h alone. The file does not say that pt is the point at which
the port's key side ends; that the port's form of a call's keys is the extension of kv c; that every
value of Forest.shape has Prem (that is shape_prem in OnBytes/Tie/Pv/Lookup/Ends/ShapePrem.lean);
anything on a round, a message or a mask.

-/
import Blocks.LookupCalls
import OnBytes.Tie.Pv.Lookup.Ends.Joint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Ends

open Finset Blocks OnBytes.Model

/-- Call c has 2^(iotaN h c) trees; 0 if the shape has no such entry. -/
def iotaN (h : Forest.Shape) (c : ℕ) : ℕ := h.iota.getD c 0

/-- The number of call c's first tree. -/
def firstN (h : Forest.Shape) (c : ℕ) : ℕ := h.first.getD c 0

/-- The call to which tree y belongs. -/
def callN (h : Forest.Shape) (y : ℕ) : ℕ := h.callOf.getD y 0

/-- Call c has 2^(nN h c) keys; 0 if the shape has no call c. -/
def nN (h : Forest.Shape) (c : ℕ) : ℕ := ((h.calls[c]?).map fun k => k.n).getD 0

/-- The seven clauses, as one decidable proposition: every quantifier is bounded. -/
abbrev PremP (h : Forest.Shape) : Prop :=
  (∀ c < h.NC, iotaN h c ≤ h.rK) ∧
  (∀ c < h.NC, firstN h c % 2 ^ iotaN h c = 0) ∧
  (∀ c < h.NC, ∀ τ < 2 ^ iotaN h c, callN h (firstN h c + τ) = c) ∧
  (∀ c < h.NC, firstN h c + 2 ^ iotaN h c ≤ h.NT) ∧
  (∀ y < h.NT, ∃ c < h.NC, firstN h c ≤ y ∧ y < firstN h c + 2 ^ iotaN h c) ∧
  h.NT ≤ 2 ^ h.rK ∧
  (∀ c < h.NC, nN h c = h.dT + iotaN h c)

/-- **What the join asks of a shape's numbers.** -/
structure Prem (h : Forest.Shape) : Prop where
  /-- a call has no more trees than the forest has numbers -/
  le : ∀ c < h.NC, iotaN h c ≤ h.rK
  /-- a call's first tree is a multiple of the number of its trees -/
  dvd : ∀ c < h.NC, firstN h c % 2 ^ iotaN h c = 0
  /-- the trees from a call's first on are marked as that call's -/
  own : ∀ c < h.NC, ∀ τ < 2 ^ iotaN h c, callN h (firstN h c + τ) = c
  /-- a call's trees lie below NT -/
  inNT : ∀ c < h.NC, firstN h c + 2 ^ iotaN h c ≤ h.NT
  /-- every tree below NT is some call's -/
  cover : ∀ y < h.NT, ∃ c < h.NC, firstN h c ≤ y ∧ y < firstN h c + 2 ^ iotaN h c
  /-- the trees' numbers have rK bits -/
  nt : h.NT ≤ 2 ^ h.rK
  /-- a call's keys fill its trees -/
  n : ∀ c < h.NC, nN h c = h.dT + iotaN h c

/-- The test of the seven clauses. -/
def premOK (h : Forest.Shape) : Bool := decide (PremP h)

/-- The test gives the clauses. -/
theorem prem_of_ok {h : Forest.Shape} (e : premOK h = true) : Prem h :=
  have p : PremP h := of_decide_eq_true e
  ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩

variable {E : Type} [Field E]

/-- **The weight of call c**: eq(the first rK - iota_c of the last rK coordinates of pt, the call's
first tree without its last iota_c bits). -/
def eC (h : Forest.Shape) (pt : ℕ → E) (c : ℕ) : E :=
  eqN (h.rK - iotaN h c) h.dT pt (firstN h c / 2 ^ iotaN h c)

/-- **The point of call c**: the last iota_c coordinates of pt, then its first dT. -/
def zkC (h : Forest.Shape) (pt : ℕ → E) (c i : ℕ) : E :=
  if i < iotaN h c then pt (h.dT + h.rK - iotaN h c + i) else pt (i - iotaN h c)

/-- The library's parameters of a forest at the shape's numbers; what the join does not read: 0. -/
def lkP (E : Type) [Field E] (h : Forest.Shape) : LkPar E where
  D := h.dT
  σ := h.rK
  r := 0
  lp := 0
  NT := h.NT
  tb := fun _ _ => 0
  t0 := fun _ => 0
  φ := fun _ => 0

/-- The calls as the library's ranges of trees. -/
def clP (h : Forest.Shape) (c : Fin h.NC) : LkCall := ⟨iotaN h c, firstN h c / 2 ^ iotaN h c⟩

/-- Key number i of tree y, moved by its call's shift. -/
def keyT (h : Forest.Shape) (kv : ℕ → ℕ → E) (θ : E) (y i : ℕ) : E :=
  kv (callN h y) ((y - firstN h (callN h y)) * 2 ^ h.dT + i) + (callN h y : E) * θ

/-- Key number k of call c, moved by the call's shift. -/
def keyC (h : Forest.Shape) (kv : ℕ → ℕ → E) (θ : E) (c : Fin h.NC) (k : ℕ) : E :=
  kv c k + ((c : ℕ) : E) * θ

/-- jointKey with its local names written out. -/
theorem jointKey_eq (h : Forest.Shape) (kv : ℕ → ℕ → E) (θ : E) (X : ℕ) :
    jointKey h kv θ X =
      if X % 2 ^ h.rK < h.NT then keyT h kv θ (X % 2 ^ h.rK) (X / 2 ^ h.rK)
      else (tauN h 0 (t0N h 0) : E) := rfl

/-- The library's leaf of the key side at these parameters. -/
theorem leafK_eq (h : Forest.Shape) (key : ℕ → ℕ → E) (α : E) (X : ℕ) :
    (lkP E h).leafK key α X =
      if X % 2 ^ h.rK < h.NT then α - key (X % 2 ^ h.rK) (X / 2 ^ h.rK) else 0 := rfl

/-- A call's first tree is its prefix times the number of its trees. -/
theorem Prem.first_eq {h : Forest.Shape} (hp : Prem h) {c : ℕ} (hc : c < h.NC) :
    firstN h c / 2 ^ iotaN h c * 2 ^ iotaN h c = firstN h c :=
  Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (hp.dvd c hc))

/-- The library's four clauses on calls as ranges of trees. -/
theorem Prem.callsOK {h : Forest.Shape} (hp : Prem h) : (lkP E h).CallsOK (clP h) where
  le := fun c => hp.le c c.2
  inNT := fun c => by
    show (firstN h c / 2 ^ iotaN h c + 1) * 2 ^ iotaN h c ≤ h.NT
    rw [Nat.add_mul, hp.first_eq c.2, Nat.one_mul]
    exact hp.inNT c c.2
  cover := fun y hy => by
    obtain ⟨c, hc, h1, h2⟩ := hp.cover y hy
    refine ⟨⟨c, hc⟩, ?_⟩
    have hτ : y - firstN h c < 2 ^ (clP h ⟨c, hc⟩).e := by
      show y - firstN h c < 2 ^ iotaN h c
      omega
    have h3 := ((clP h ⟨c, hc⟩).has_block hτ (clP h ⟨c, hc⟩).pre).mpr rfl
    have h4 : (clP h ⟨c, hc⟩).pre * 2 ^ (clP h ⟨c, hc⟩).e + (y - firstN h c) = y := by
      show firstN h c / 2 ^ iotaN h c * 2 ^ iotaN h c + (y - firstN h c) = y
      rw [hp.first_eq hc]
      omega
    rwa [h4] at h3
  disj := fun c c' y hy hy' => by
    have key : ∀ d : Fin h.NC, (clP h d).Has y → callN h y = d := by
      intro d hd
      have h1 : y / 2 ^ iotaN h d = firstN h d / 2 ^ iotaN h d := hd
      have h2 := Nat.div_add_mod' y (2 ^ iotaN h d)
      rw [h1, hp.first_eq d.2] at h2
      have h3 := hp.own d d.2 (y % 2 ^ iotaN h d) (Nat.mod_lt _ (Nat.two_pow_pos _))
      rwa [h2] at h3
    exact Fin.ext ((key c hy).symm.trans (key c' hy'))

/-- The trees' keys are the calls' keys, in the library's numbering. -/
theorem Prem.keysOf {h : Forest.Shape} (hp : Prem h) (kv : ℕ → ℕ → E) (θ : E) :
    (lkP E h).KeysOf (clP h) (keyT h kv θ) (keyC h kv θ) := by
  intro c τ hτ i _
  show keyT h kv θ (firstN h c / 2 ^ iotaN h c * 2 ^ iotaN h c + τ) i =
    keyC h kv θ c (τ * 2 ^ h.dT + i)
  rw [hp.first_eq c.2]
  unfold keyT keyC
  rw [hp.own c c.2 τ hτ, Nat.add_sub_cancel_left]

/-- The equality factors of a point sum to 1. -/
theorem sum_eqN_one (g : ℕ) (pt : ℕ → E) : ∑ x ∈ range (2 ^ g), eqN g 0 pt x = 1 := by
  have h := ext_const g (1 : E) pt
  unfold Blocks.ext at h
  simpa using h

/-- The trees from NT on, which hold one constant K. -/
theorem ext_rest (h : Forest.Shape) (hnt : h.NT ≤ 2 ^ h.rK) (K : E) (pt : ℕ → E) :
    ext (h.dT + h.rK) (fun X => if X % 2 ^ h.rK < h.NT then 0 else K) pt =
      ∑ y ∈ Ico h.NT (2 ^ h.rK), eqN h.rK h.dT pt y * K := by
  rw [ext_two, sum_comm]
  have h1 : ∀ y ∈ range (2 ^ h.rK),
      (∑ x ∈ range (2 ^ h.dT), eqN h.dT 0 pt x * eqN h.rK h.dT pt y *
          (if (x * 2 ^ h.rK + y) % 2 ^ h.rK < h.NT then 0 else K)) =
        if y < h.NT then 0 else eqN h.rK h.dT pt y * K := by
    intro y hy
    have hm : ∀ x, (x * 2 ^ h.rK + y) % 2 ^ h.rK = y := fun x => by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (mem_range.mp hy)]
    simp only [hm]
    by_cases hy' : y < h.NT
    · simp only [if_pos hy', mul_zero, sum_const_zero]
    · simp only [if_neg hy']
      rw [← sum_mul, ← sum_mul, sum_eqN_one, one_mul]
  have hz : ∑ y ∈ Ico 0 h.NT, (if y < h.NT then (0 : E) else eqN h.rK h.dT pt y * K) = 0 :=
    sum_eq_zero fun y hy => if_pos (mem_Ico.mp hy).2
  rw [sum_congr rfl h1, range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le _) hnt, hz, zero_add]
  exact sum_congr rfl fun y hy => if_neg (not_lt.mpr (mem_Ico.mp hy).1)

/-- **The join's right side**: the calls, each under its weight at its own point, and the trees from
NT on. -/
def joinRhs (h : Forest.Shape) (kv : ℕ → ℕ → E) (θ α : E) (pt : ℕ → E) : E :=
  ∑ c ∈ range h.NC, eC h pt c * (α - (c : E) * θ - ext (nN h c) (kv c) (zkC h pt c)) +
    ∑ y ∈ Ico h.NT (2 ^ h.rK), eqN h.rK h.dT pt y * (α - (tauN h 0 (t0N h 0) : E))

/-- **The join.** Under Prem h, α less the extension of the joint key vector at pt is joinRhs. -/
theorem join_identity {h : Forest.Shape} (hp : Prem h) (kv : ℕ → ℕ → E) (θ α : E) (pt : ℕ → E) :
    α - ext h.v (jointKey h kv θ) pt = joinRhs h kv θ α pt := by
  unfold joinRhs
  have h0 : α - ext h.v (jointKey h kv θ) pt =
      ext (h.dT + h.rK) (fun X => (lkP E h).leafK (keyT h kv θ) α X +
        (if X % 2 ^ h.rK < h.NT then 0 else α - (tauN h 0 (t0N h 0) : E))) pt := by
    have h1 : α - ext h.v (jointKey h kv θ) pt =
        ext (h.dT + h.rK) (fun X => α - jointKey h kv θ X) pt := by
      rw [ext_sub, ext_const]
      rfl
    rw [h1]
    refine ext_congr (fun X _ => ?_) pt
    rw [jointKey_eq, leafK_eq]
    by_cases hy : X % 2 ^ h.rK < h.NT
    · rw [if_pos hy, if_pos hy, if_pos hy, add_zero]
    · rw [if_neg hy, if_neg hy, if_neg hy, zero_add]
  rw [h0, ext_add, ext_rest h hp.nt]
  congr 1
  have h2 := (hp.callsOK (E := E)).ext_leafK hp.nt (hp.keysOf kv θ) α pt
  refine h2.trans ?_
  rw [sum_range]
  refine sum_congr rfl fun c _ => ?_
  have h3 : ext ((clP h c).e + (lkP E h).D) (keyC h kv θ c) ((lkP E h).zCall (clP h c) pt) =
      ext (nN h c) (kv c) (zkC h pt c) + ((c : ℕ) : E) * θ := by
    have h4 : (clP h c).e + (lkP E h).D = nN h c := by
      rw [hp.n c c.2]
      exact Nat.add_comm _ _
    rw [h4]
    show ext (nN h c) (fun k => kv c k + ((c : ℕ) : E) * θ) _ = _
    rw [ext_add, ext_const]
    congr 1
    refine ext_congr_point (fun t _ => ?_) _
    show (if t < iotaN h c then pt (h.dT + (h.rK - iotaN h c) + t) else pt (t - iotaN h c)) =
      if t < iotaN h c then pt (h.dT + h.rK - iotaN h c + t) else pt (t - iotaN h c)
    rw [Nat.add_sub_assoc (hp.le c c.2)]
  rw [h3]
  show eC h pt c * (α - (ext (nN h c) (kv c) (zkC h pt c) + ((c : ℕ) : E) * θ)) = _
  ring

end OnBytes.Ends

#print axioms OnBytes.Ends.prem_of_ok
#print axioms OnBytes.Ends.join_identity
