-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoJoinAt.lean.
The lookup of a sub-proof: the end of its key side, at the lookup's own value and last state.

OnBytes/Tie/Pv/Lookup/Port/FoJoin.lean says of ANY masked claim on the joint key vector that it
holds exactly if the byte-level
verifier's form of the join is 0. This file brings that to the typed lookup of a sub-proof, forA E h
L:
its keys are the joint key vector, its numbers meet what the join asks, and the claim that its chain
leaves on the keys has a point, a mask form and a target that are read off the chain's last state.

States:
  prem_of_port, ok_prem: the test of the shape's public numbers (FoNums.ok) gives the seven clauses
    that the join asks (OnBytes.Ends.Prem).
  tauN_eq, jointKey_port, forA_key: the joint key vector of OnBytes/Tie/Pv/Lookup/Ends/Joint.lean is
  the
    lookup's own key vector, moved by the shift.
  dense_val: the value of a sparse form is the sum over all places of its coefficient times the
    reading.
  cEndAt, cEnd_ok: the hidden value at the end of the key side, as a form off the last state's
    trace; it meets CEok.
  join_at: AT EVERY LAST STATE o OF THE LOOKUP's CHAIN: the first clause of the lookup's output
    claim (the masked claim on the keys holds) is: the verifier's form of the join is 0.
  KFent, KFent_ok: the premise on the caller's forms can be met: where a call's keys are entries,
    the form that lists them meets KFok.
  cEndU, cEndU_ok: every masked claim has a form that meets CEok.
Premises of join_at: FoNums.ok h = true, and KFokAt at the reading at which the claim is said.

-/
import OnBytes.Tie.Pv.Lookup.Port.FoJoin
import OnBytes.Tie.Pv.Lookup.Forest.FoHole
import OnBytes.Tie.Pv.Lookup.Forest.FoState

set_option autoImplicit false

namespace Fo
open TwV FoNums Finset OnBytes.Model OnBytes.Ends Cb Cb.LdLkp Cb.Fo Tw3

/-! ### The numbers -/

theorem prem_of_port {h : FoNums.Sh} (H : Port.OK h) : Prem h := by
  obtain ⟨_, _, h3, h4, _, h6⟩ := H
  have two : ∀ c < h.NC, fst h c + 2 ^ io h c ≤ h.NT := fun c hc => by
    have := ((h6 c hc).2.2 (2 ^ io h c - 1) (Nat.sub_lt (Nat.pow_pos (by decide)) (by decide))).1
    have hpos : 0 < 2 ^ io h c := Nat.pow_pos (by decide)
    show Port.fst h c + 2 ^ Port.io h c ≤ h.NT
    have this' : Port.fst h c + (2 ^ Port.io h c - 1) < h.NT := this
    have hpos' : 0 < 2 ^ Port.io h c := hpos
    omega
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc τ hτ => ((h6 c hc).2.2 τ hτ).2.1, two,
      fun y hy => ?_, h3, fun c hc => ?_⟩
  · have h1 : 2 ^ io h c ≤ 2 ^ h.rK := le_trans (le_trans (Nat.le_add_left _ _) (two c hc)) h3
    exact (Nat.pow_le_pow_iff_right (show 1 < 2 by decide)).mp h1
  · have := ((h6 c hc).2.2 0 (Nat.pow_pos (by decide))).2.2
    rwa [Nat.add_zero] at this
  · exact ⟨_, (h4 y hy).1, (h4 y hy).2.1, (h4 y hy).2.2⟩
  · exact ((h6 c hc).2.1).trans (Nat.add_comm _ _)

theorem ok_prem {h : FoNums.Sh} (H : FoNums.ok h = true) : Prem h := prem_of_port (ok_portOK H)

/-- The two readings of a call's table agree where the shape has the call. -/
theorem tauN_eq (h : FoNums.Sh) (c t : ℕ) (hc : c < h.calls.size) : FoNums.tauN h c t =
    OnBytes.Ends.tauN h c t := by
  unfold FoNums.tauN OnBytes.Ends.tauN
  have e : h.calls[c]? = some h.calls[c] := Array.getElem?_eq_getElem hc
  rw [e, Array.getD_eq_getD_getElem?, e]
  rfl

/-! ### The keys -/
section
variable {E : Type} [Field E]

/-- The joint key vector is the lookup's own, moved by the shift. -/
theorem jointKey_port {h : FoNums.Sh} (H : Port.OK h) (T kv : ℕ → ℕ → E) (θ : E)
    (hT : T 0 (Port.t0Of h 0) = (OnBytes.Ends.tauN h 0 (t0N h 0) : E)) (X : ℕ) :
    jointKey h kv θ X = Port.key h T kv X + ((Port.fK h X : ℕ) : E) * θ := by
  rw [port_prover E h T kv H X]
  unfold jointKey Port.keyP Port.fK
  by_cases hl : X % 2 ^ h.rK < h.NT
  · simp only [if_pos hl]
    rfl
  · simp only [if_neg hl, hT]
    simp

end

/-! ### Sparse forms -/
section
variable {P K : Type} [Fintype P] [DecidableEq P] [CommRing K]

theorem dense_val (μ : P → K) : ∀ cf : List (P × K), ∑ j, dense cf j * μ j =
    (cf.map fun pc => pc.2 * μ pc.1).sum
  | [] => by simp [dense]
  | pc :: f => by
    simp only [dense_cons, add_mul, Finset.sum_add_distrib, List.map_cons, List.sum_cons]
    rw [dense_val μ f]
    congr 1
    simp

end

/-! ### That the premises can be met -/
section
variable {P K : Type} [CommRing K]

/-- Where call c's key number i is the entry pl c i: the form that lists the entries under their
weights. -/
def KFent (pl : ℕ → ℕ → P) (zk : ℕ → List K) (c : ℕ) : AffK P K :=
  ((List.range (2 ^ (zk c).length)).map fun i => (pl c i, eqN (zk c).reverse i), 0)

theorem KFent_ok (h : FoNums.Sh) (pl : ℕ → ℕ → P) (zk : ℕ → List K) : KFok h
    (fun μ c i => μ (pl c i)) zk (KFent pl zk) := by
  intro μ c _
  unfold AffK.val KFent extL
  simp only [List.map_map, add_zero]
  rfl

end

section
variable {E N : Type} [Field E] [Fintype N]

/-- Every masked claim has a form for its hidden value. (It lists all places: it stands in
statements alone.) -/
noncomputable def cEndU (c : MCl E N) (α : E) : AffK N E :=
    (Finset.univ.toList.map fun i => (i, c.mf i), α - c.tg)

theorem cEndU_ok (c : MCl E N) (α : E) : CEok c α (cEndU c α) := by
  intro μ
  unfold AffK.val cEndU
  simp only [List.map_map]
  rw [add_comm]
  congr 1
  exact Finset.sum_map_toList Finset.univ fun i => c.mf i * μ i

end

/-! ### At the lookup's value -/
section
variable (E : Type) [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]
    (h : FoNums.Sh) (L : Lay E St₀ J₀)

/-- The lookup's keys are the joint key vector of the calls' key vectors. -/
theorem forA_key (H : FoNums.ok h = true) (st : St₀) (θ : E) (μ : Option J₀ → E) :
    (forA E h L).key (st, θ) μ = jointKey h (forK E L st μ) θ := by
  funext X
  refine (jointKey_port (ok_portOK H) (forT E h st) (forK E L st μ) θ ?_ X).symm
  obtain ⟨⟨_, a2, _, _, _, _, a7⟩, _⟩ := ok_parts H
  show ((FoNums.tauN h 0 (FoNums.t0Of h 0) : ℕ) : E) = _
  rw [tauN_eq h 0 _ (by omega)]
  rfl

variable {E h L}

/-- The hidden value at the end of the key side, off the trace of the last state: the target at the
keys' top less the incoming form. -/
noncomputable def cEndAt (o : (forA E h L).XB) : AffK (Option J₀) E :=
  (scale (-1) (incTop (numsA (forA E h L) ((forA E h L).rd o).1).ledK
      (TwV.fK (numsA (forA E h L) ((forA E h L).rd o).1) (traceOf (forA E h L) o))
          (traceOf (forA E h L) o).keys.reverse),
    (traceOf (forA E h L) o).kT)

theorem cEnd_ok (o : (forA E h L).XB) :
    CEok ((forA E h L).clK ((forA E h L).oldT o)) (traceOf (forA E h L) o).lam (cEndAt o) := by
  intro μ
  unfold AffK.val cEndAt
  rw [clK_tg, ← dense_val]
  simp only [clK_mf (forA E h L) ((forA E h L).rd o).1 o]
  have e : ∀ a b c : E, a + b = c - (c - b) + a := fun a b c => by ring
  exact e _ _ _

/-- **The end of the key side, at the lookup's own last state.** -/
theorem join_at (H : FoNums.ok h = true) (o : (forA E h L).XB) (KF : ℕ → AffK (Option J₀) E)
    (μ : Option J₀ → E)
    (hKF : KFokAt h (forK E L ((forA E h L).rd o).1.1)
        (zkOf h ((forA E h L).clK ((forA E h L).oldT o))) KF μ) :
    ((forA E h L).rd o).2.1.Holds ((forA E h L).v' + 1)
        ((forA E h L).key ((forA E h L).rd o).1 μ) μ ↔
      AffK.val (joinK h ((forA E h L).rd o).1.2 (traceOf (forA E h L) o).lam
        (eK h (zyOf h ((forA E h L).clK ((forA E h L).oldT o))))
            (zyOf h ((forA E h L).clK ((forA E h L).oldT o))) KF (cEndAt o)) μ = 0 := by
  have hk : (forA E h L).key ((forA E h L).rd o).1 μ =
      jointKey h (forK E L ((forA E h L).rd o).1.1 μ) ((forA E h L).rd o).1.2 :=
    forA_key E h L H ((forA E h L).rd o).1.1 ((forA E h L).rd o).1.2 μ
  have hv : (forA E h L).v' + 1 = h.v := (ok_v H).symm
  rw [hk, hv]
  exact join_form (ok_prem H) (forK E L ((forA E h L).rd o).1.1) ((forA E h L).rd o).1.2
      (traceOf (forA E h L) o).lam
    ((forA E h L).clK ((forA E h L).oldT o)) KF (cEndAt o) μ hKF (cEnd_ok o)

end
end Fo
