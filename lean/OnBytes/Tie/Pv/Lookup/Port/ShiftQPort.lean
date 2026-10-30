-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Port/ShiftQPort.lean.
The maps, sizes and tags of the shift at the record of a forest that the Lean verifier under
OnBytes/ (here: the port) holds: computable terms on OnBytes.Model.Forest.Shape.

  fK X: the tree's number y is the low rK bits of X; below NT its call is callOf[y]; a tree of
  padding alone (y ≥ NT) goes with call 0.
  fT Y: the number c is the low cK bits of Y; the call is min c (NC - 1).     tag c := (c : E).
  tab Y: row (Y / 2^cK) % 2^k of its call's table: a shorter table is repeated.
  key X: below NT: entry x + 2^dT · (y % 2^iota) of its call's key vector, x := X / 2^rK; from NT
  on: row t0 of call 0's table.
  T c t (call c's table) and K c i (call c's key vector, its own padding places in it) are
  arguments.
Main definitions and statements.
  Port.OK h: the conditions on the public numbers; decidable. Among them: every tree y < NT lies in
  the run of trees of the call that callOf names, and each call's run is named so.
  port_in_iff: under OK the shift's in-claim at these maps is "for every call c < NC: InTable n_c
    k_c (K c) (T c)": the library's InTable, call by call, each at its own sizes.
  port_prover: under OK, Port.key is Port.keyP, the index as the port's test prover writes it
    (OnBytes/Model/TestLookProver.lean).
  port_ok: under OK and NC ≤ the characteristic, what the block asks (ShiftQ.Ok) holds, with several
    := decide (1 < NC). port_sizes: v, d, several are forestSize's (OnBytes/Model/RoundSizes.lean),
    by rfl.
What is not proved. That these maps are the ones by which the port's verifier reads a forest
(OnBytes/Model/Look.lean, OnBytes/Model/Forest.lean): no statement here ties them to it. That every
output of Forest.shape meets Port.OK.

-/
import Cb.Pv.Lookup.Shift.ShiftQAsm
import OnBytes.Model.RoundSizes

set_option autoImplicit false

namespace Cb.LdLkp
namespace Port
open Cb.Lkp

abbrev Sh : Type := OnBytes.Model.Forest.Shape

def nOf (h : Sh) (c : ℕ) : ℕ := ((h.calls[c]?).map (·.n)).getD 0
def kOf (h : Sh) (c : ℕ) : ℕ := ((h.calls[c]?).map (·.k)).getD 0
def t0Of (h : Sh) (c : ℕ) : ℕ := ((h.calls[c]?).map (·.t0)).getD 0
def io (h : Sh) (c : ℕ) : ℕ := h.iota.getD c 0
def fst (h : Sh) (c : ℕ) : ℕ := h.first.getD c 0
def co (h : Sh) (y : ℕ) : ℕ := h.callOf.getD y 0

/-- the call of the key X -/
def fK (h : Sh) : ℕ → ℕ := fun X => if X % 2 ^ h.rK < h.NT then co h (X % 2 ^ h.rK) else 0
/-- the call of the row Y -/
def fT (h : Sh) : ℕ → ℕ := fun Y => min (Y % 2 ^ h.cK) (h.NC - 1)
/-- is θ drawn? -/
def several (h : Sh) : Bool := decide (1 < h.NC)

section
variable {E : Type} [Field E]

/-- the joint table, not shifted -/
def tab (h : Sh) (T : ℕ → ℕ → E) : ℕ → E := fun Y => T (fT h Y) (Y / 2 ^ h.cK % 2 ^ kOf h (fT h Y))
/-- the joint keys, not shifted -/
def key (h : Sh) (T K : ℕ → ℕ → E) : ℕ → E := fun X =>
  if X % 2 ^ h.rK < h.NT then
    K (co h (X % 2 ^ h.rK)) (X / 2 ^ h.rK + 2 ^ h.dT *
        (X % 2 ^ h.rK % 2 ^ io h (co h (X % 2 ^ h.rK))))
  else T 0 (t0Of h 0)

/-- The joint keys as the port's test prover lays them (`prove`, OnBytes/Model/TestLookProver.lean):
"y - first[c] says which of its call's trees tree y is". -/
def keyP (h : Sh) (T K : ℕ → ℕ → E) : ℕ → E := fun X =>
  if X % 2 ^ h.rK < h.NT then
    K (co h (X % 2 ^ h.rK)) ((X % 2 ^ h.rK - fst h (co h (X % 2 ^ h.rK))) * 2 ^ h.dT + X / 2 ^ h.rK)
  else T 0 (t0Of h 0)

/-- The shift's data (`ShiftQ`) at a forest h. -/
def Q {St M : Type} (h : Sh) (T : St → ℕ → ℕ → E) (K : St → M → ℕ → ℕ → E) : ShiftQ E St M where
  v := h.v
  d := h.d
  fK := fK h
  fT := fT h
  key := fun st m => key h (T st) (K st m)
  tab := fun st => tab h (T st)
  tag := fun c => (c : E)

end

/-- What is asked of the public numbers. -/
def OK (h : Sh) : Prop :=
  1 ≤ h.NC ∧ h.NC ≤ 2 ^ h.cK ∧ h.NT ≤ 2 ^ h.rK ∧
  (∀ y < h.NT, co h y < h.NC ∧ fst h (co h y) ≤ y ∧ y < fst h (co h y) + 2 ^ io h (co h y)) ∧
  t0Of h 0 < 2 ^ kOf h 0 ∧
  ∀ c < h.NC, kOf h c ≤ h.kT ∧ nOf h c = io h c + h.dT ∧
    ∀ b < 2 ^ io h c, fst h c + b < h.NT ∧ co h (fst h c + b) = c ∧ (fst h c + b) % 2 ^ io h c = b

instance (h : Sh) : Decidable (OK h) := by unfold OK; infer_instance

end Port
end Cb.LdLkp

namespace Cb.Spec
open Cb.Lkp Cb.LdLkp

/-- The in-claim at the port's value: each call's keys lie in that call's table. -/
def port_in_iff : Prop :=
  ∀ (E : Type) [Field E] (h : Port.Sh) (T K : ℕ → ℕ → E), Port.OK h →
    (AllInQ h.v h.d (Port.fK h) (Port.fT h) (Port.key h T K) (Port.tab h T) ↔
      ∀ c < h.NC, InTable (Port.nOf h c) (Port.kOf h c) (K c) (T c))

/-- The verifier's cut of a tree's number (its low iota bits: zk in OnBytes/Model/Look.lean) and the
test prover's (y - first[c]) give one key vector. -/
def port_prover : Prop :=
  ∀ (E : Type) [Field E] (h : Port.Sh) (T K : ℕ → ℕ → E), Port.OK h → ∀ X,
      Port.key h T K X = Port.keyP h T K X

/-- Both maps land below NC. -/
def port_lt : Prop :=
  ∀ (h : Port.Sh), Port.OK h → (∀ X, Port.fK h X < h.NC) ∧ ∀ Y, Port.fT h Y < h.NC

/-- What the block asks holds at the port's value. -/
def port_ok : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (p : ℕ) [CharP E p] (St J : Type) (h : Port.Sh)
      (T : St → ℕ → ℕ → E)
      (K : St → (J → E) → ℕ → ℕ → E),
    Port.OK h → h.NC ≤ p → (Port.Q h T K).Ok (Port.several h)

/-- The sizes and the test "several" are `forestSize`'s (OnBytes/Model/RoundSizes.lean). -/
def port_sizes : Prop :=
  ∀ (E : Type) [Field E] (St M : Type) (h : Port.Sh) (T : St → ℕ → ℕ → E) (K : St → M → ℕ → ℕ → E),
    (Port.Q h T K).v = (OnBytes.Model.forestSize h).v ∧
    (Port.Q h T K).d = (OnBytes.Model.forestSize h).d ∧
    Port.several h = (OnBytes.Model.forestSize h).shifted ∧
    2 ^ (Port.Q h T K).d = 2 ^ (h.kT + h.cK)

end Cb.Spec

namespace Cb
open Cb.Lkp Cb.LdLkp

theorem port_lt : Spec.port_lt := by
  intro h ⟨h1, _, _, h4, _, _⟩
  refine ⟨fun X => ?_, fun Y => lt_of_le_of_lt (Nat.min_le_right _ _) (by omega)⟩
  unfold Port.fK
  split_ifs with hl
  · exact (h4 _ hl).1
  · exact h1

theorem port_prover : Spec.port_prover := by
  intro E _ h T K ⟨_, _, _, h4, _, h6⟩ X
  unfold Port.key Port.keyP
  by_cases hlt : X % 2 ^ h.rK < h.NT
  · rw [if_pos hlt, if_pos hlt]
    obtain ⟨hc, hlo, hhi⟩ := h4 _ hlt
    obtain ⟨y, hy⟩ : ∃ y, y = X % 2 ^ h.rK := ⟨_, rfl⟩
    rw [← hy] at hc hlo hhi ⊢
    obtain ⟨c, hcd⟩ : ∃ c, c = Port.co h y := ⟨_, rfl⟩
    rw [← hcd] at hc hlo hhi ⊢
    obtain ⟨_, _, hb⟩ := h6 c hc
    obtain ⟨_, _, hm⟩ := hb (y - Port.fst h c) (by omega)
    rw [Nat.add_sub_cancel' hlo] at hm
    rw [hm, Nat.add_comm, Nat.mul_comm]
  · rw [if_neg hlt, if_neg hlt]

theorem port_in_iff : Spec.port_in_iff := by
  intro E _ h T K ⟨h1, h2, h3, h4, h5, h6⟩
  constructor
  · intro hA c hc i hi
    obtain ⟨_, hn, hb⟩ := h6 c hc
    rw [hn] at hi
    obtain ⟨hbq, hxq⟩ := ldLkpShift_split (Port.io h c) h.dT i hi
    obtain ⟨hy, hco, hmod⟩ := hb _ hbq
    obtain ⟨y, hyd⟩ : ∃ y, y = Port.fst h c + i / 2 ^ h.dT := ⟨_, rfl⟩
    rw [← hyd] at hy hco hmod
    obtain ⟨e1, e2, e3⟩ := ldLkpShift_num h.dT h.rK (i % 2 ^ h.dT) y hxq (lt_of_lt_of_le hy h3)
    obtain ⟨Y, _, hf, he⟩ := hA _ e1
    have hfK : Port.fK h (y + 2 ^ h.rK * (i % 2 ^ h.dT)) = c := by
      unfold Port.fK
      rw [e3, if_pos hy, hco]
    have hkey : Port.key h T K (y + 2 ^ h.rK * (i % 2 ^ h.dT)) = K c i := by
      unfold Port.key
      rw [e3, e2, if_pos hy, hco, hmod, Nat.mod_add_div]
    rw [hkey] at he
    rw [hfK] at hf
    refine ⟨Y / 2 ^ h.cK % 2 ^ Port.kOf h c, Nat.mod_lt _ (by positivity), ?_⟩
    rw [he]
    unfold Port.tab
    rw [hf]
  · intro hC X hX
    obtain ⟨hx, _⟩ := ldLkpShift_split h.dT h.rK X hX
    by_cases hlt : X % 2 ^ h.rK < h.NT
    · have hc := (h4 _ hlt).1
      obtain ⟨c, hcd⟩ : ∃ c, c = Port.co h (X % 2 ^ h.rK) := ⟨_, rfl⟩
      rw [← hcd] at hc
      obtain ⟨hk, hn, _⟩ := h6 c hc
      have hb : X % 2 ^ h.rK % 2 ^ Port.io h c < 2 ^ Port.io h c := Nat.mod_lt _ (by positivity)
      obtain ⟨i1, _, _⟩ := ldLkpShift_num (Port.io h c) h.dT _ _ hb hx
      obtain ⟨t, ht, he⟩ := hC c hc _ (by rw [hn]; exact i1)
      have ht' : t < 2 ^ h.kT := lt_of_lt_of_le ht (Nat.pow_le_pow_right (by norm_num) hk)
      obtain ⟨e1, e2, e3⟩ := ldLkpShift_num h.kT h.cK t c ht' (lt_of_lt_of_le hc h2)
      have hfT : Port.fT h (c + 2 ^ h.cK * t) = c := by
        unfold Port.fT
        rw [e3]
        exact Nat.min_eq_left (by omega)
      refine ⟨_, e1, ?_, ?_⟩
      · rw [hfT]
        unfold Port.fK
        rw [if_pos hlt, hcd]
      · unfold Port.key Port.tab
        rw [if_pos hlt, hfT, e2, Nat.mod_eq_of_lt ht, ← hcd]
        exact he
    · obtain ⟨hk, _, _⟩ := h6 0 h1
      have ht' : Port.t0Of h 0 < 2 ^ h.kT :=
        lt_of_lt_of_le h5 (Nat.pow_le_pow_right (by norm_num) hk)
      obtain ⟨e1, e2, e3⟩ := ldLkpShift_num h.kT h.cK (Port.t0Of h 0) 0 ht' (lt_of_lt_of_le h1 h2)
      have hfT : Port.fT h (0 + 2 ^ h.cK * Port.t0Of h 0) = 0 := by
        unfold Port.fT
        rw [e3]
        exact Nat.min_eq_left (Nat.zero_le _)
      refine ⟨_, e1, ?_, ?_⟩
      · rw [hfT]
        unfold Port.fK
        rw [if_neg hlt]
      · unfold Port.key Port.tab
        rw [if_neg hlt, hfT, e2, Nat.mod_eq_of_lt h5]

theorem port_ok : Spec.port_ok := by
  intro E _ _ p _ St J h T K hOK hp
  obtain ⟨hK, hT⟩ := port_lt h hOK
  by_cases hN : 1 < h.NC
  · have e : Port.several h = true := decide_eq_true hN
    rw [e]
    intro st
    exact tagsQ_of_lt E h.v h.d h.NC (Port.fK h) (Port.fT h) _ _ (fun X _ => hK X) (fun Y _ => hT Y)
      (natTag_inj E p h.NC hp)
  · have e : Port.several h = false := decide_eq_false hN
    rw [e]
    intro X _ Y _
    have a := hK X
    have b := hT Y
    show Port.fT h Y = Port.fK h X
    omega

theorem port_sizes : Spec.port_sizes := fun _ _ _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩

end Cb
