-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Psc/PscWhole.lean: one whole masked sumcheck of the sub-proofs
(OnBytes/Model/Psc.lean), from its beginning to its claim: what its state holds after each routine,
in the words of the flat step on plain data.

Definitions, and theorems with their proofs. The routines are called one after the other by their
callers, with other calls between them, so the statement is on the state `Psc` that they hand on.
`Ran p first mu eps zd rs` says of a state p: the sumcheck began at the slot `first` with the sum mu
and the element eps; its variables so far are summed under equality weights, given by the pairs zd
(the point's coordinate, the number of coefficients); the rounds so far are rs (message, challenge);
the running claim is the program's `claimAfter` of these. That mu is the sum that was received is
`pscBegin_ok`'s part.

Main names:
  `Ran`; `ran_begin`, `ran_push`: the beginning has it with no variable; a round adds one pair and
    one round.
  `weight_eq2`, `weight_eq`: the weights of the two forms of round that sum under the equality
    polynomial.
  `ran_roundIn2`, `ran_roundIn`, `ran_ends`: the routines `roundIn` (forms eq2, eq) and `pscEnds`.
  `ran_takeSc`: for every reading ρ: the flat step `TwV.takeSc` on the plain data (`flH`) gives the
    state's eps, challenges and running claim, read. The shown values are an argument: the step
    hands back, read, the values that stand in the plain data; that they are the values that
    `pscEnds` has received is `ran_ends`' part.
  `ran_walk`: what `Psc.walk` computes: the weights `walkK`, and a product that reads 1.
  `ran_row`, `ran_rowK`: the value of the claim that the sumcheck leaves (`Psc.rowForm`), term by
    term; the second with the weights written out.

Limits: equality weights alone. Nothing is said where a routine fails. Nothing on soundness, on an
honest prover or on hiding.


-/
import OnBytes.Tie.Pv.Psc.FlatTie
import OnBytes.Tie.Pv.Psc.PscView

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.PscRun
open OnBytes OnBytes.Model OnBytes.PscTie TwV

/-- The state of a sumcheck whose variables so far are summed under equality weights. -/
structure Ran (p : Psc) (first : Nat) (mu eps : E) (zd : List (E × Nat))
    (rs : List (List E × E)) : Prop where
  first_eq : p.first = first
  eps_eq : p.eps = eps
  vars_eq : p.vars.toList = eqW zd
  r_eq : p.r.toList = rs.map (·.2)
  claim_eq : p.claim = OnBytes.Psc.claimAfter (eqW zd) rs (addE mu (mulE eps p.target))
  fits : Fits zd rs

/-- One more variable and one more round that fit. -/
theorem fits_snoc : ∀ {zd : List (E × Nat)} {rs : List (List E × E)} (p : E × Nat)
    (r : List E × E), Fits zd rs → r.1.length + 1 = p.2 → Fits (zd ++ [p]) (rs ++ [r])
  | [], [], _, _, _, h => ⟨h, trivial⟩
  | _ :: _, _ :: _, p, r, h, h' => ⟨h.1, fits_snoc p r h.2 h'⟩
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim

/-- `claimAfter` with one more weight and one more round at the end. -/
theorem claimAfter_snoc : ∀ (ws : List OnBytes.Psc.Weight) (rs : List (List E × E))
    (w : OnBytes.Psc.Weight) (q : List E) (g R : E), ws.length = rs.length →
    OnBytes.Psc.claimAfter (ws ++ [w]) (rs ++ [(q, g)]) R =
      OnBytes.Psc.polyAt (w.complete q (OnBytes.Psc.claimAfter ws rs R)) g
  | [], [], w, q, g, R, _ => by
    rw [List.nil_append, List.nil_append, claimAfter_cons]
    simp only [OnBytes.Psc.claimAfter]
  | v :: ws, (q', g') :: rs, w, q, g, R, h => by
    rw [List.cons_append, List.cons_append, claimAfter_cons, claimAfter_cons,
      claimAfter_snoc ws rs w q g _ (by simpa using h)]
  | [], _ :: _, _, _, _, _, h => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h

/-- The state that `pscBegin` returns, with no variable and no round. -/
theorem ran_begin (C : Aff) (target mu eps : E) (first : Nat) :
    Ran { start := C, started := true, target := target, first := first, eps := eps,
          claim := addE mu (mulE eps target) } first mu eps [] [] :=
  ⟨rfl, rfl, rfl, rfl, by simp only [eqW, List.map_nil, OnBytes.Psc.claimAfter], trivial⟩

/-- A round adds one pair and one round. -/
theorem ran_push {p : Psc} {first : Nat} {mu eps : E} {zd : List (E × Nat)}
    {rs : List (List E × E)} (h : Ran p first mu eps zd rs) (z : E) (d : Nat) (sent : Array E)
    (g : E) (hs : sent.size + 1 = d) (p' : Psc) (h1 : p'.first = p.first) (h2 : p'.eps = p.eps)
    (h3 : p'.target = p.target) (h4 : p'.vars = p.vars.push (OnBytes.Psc.Weight.equality z d))
    (h5 : p'.r = p.r.push g)
    (h6 : p'.claim =
      OnBytes.Psc.polyAt ((OnBytes.Psc.Weight.equality z d).complete sent.toList p.claim) g) :
    Ran p' first mu eps (zd ++ [(z, d)]) (rs ++ [(sent.toList, g)]) := by
  have e : eqW (zd ++ [(z, d)]) = eqW zd ++ [OnBytes.Psc.Weight.equality z d] := by
    simp only [eqW, List.map_append, List.map_cons, List.map_nil]
  have hl : (eqW zd).length = rs.length := by
    simp only [eqW, List.length_map]
    exact h.fits.length
  refine ⟨h1.trans h.first_eq, h2.trans h.eps_eq, ?_, ?_, ?_, ?_⟩
  · rw [h4, Array.toList_push, h.vars_eq, e]
  · rw [h5, Array.toList_push, h.r_eq, List.map_append, List.map_cons, List.map_nil]
  · rw [h6, e, claimAfter_snoc _ _ _ _ _ _ hl, h3, ← h.claim_eq]
  · refine fits_snoc _ _ h.fits ?_
    show sent.toList.length + 1 = d
    rw [Array.length_toList]
    exact hs

/-- A round of the form eq2 is summed under equality weights, with three coefficients. -/
theorem weight_eq2 (z : E) (degree : Nat) :
    RoundForm.eq2.weight z degree = some (OnBytes.Psc.Weight.equality z 3) := rfl

/-- A round of the form eq is summed under equality weights, with degree + 1 coefficients. -/
theorem weight_eq (z : E) (degree : Nat) (w : OnBytes.Psc.Weight)
    (h : RoundForm.eq.weight z degree = some w) :
    w = OnBytes.Psc.Weight.equality z (degree + 1) := by
  unfold RoundForm.weight at h
  split at h
  · exact (Option.some.inj h).symm
  · simp at h

/-- A round of the form eq2. -/
theorem ran_roundIn2 {p : Psc} {first : Nat} {mu eps : E} {zd : List (E × Nat)}
    {rs : List (List E × E)} (hp : Ran p first mu eps zd rs) (z : E) (degree : Nat) (F G : Fork)
    (c c' : Ctx) (g : E) (p' : Psc) (h : roundIn .eq2 p z degree F c = .ok (((g, p'), G), c')) :
    ∃ sent : Array E, sent.size = 2 ∧ Evs [.read 2 sent, .ans .pscRound g] c c' ∧ G = took F 2 ∧
      p'.target = p.target ∧ p'.start = p.start ∧ p'.started = p.started ∧
      p'.rowMade = p.rowMade ∧ p'.ended = false ∧
      Ran p' first mu eps (zd ++ [(z, 3)]) (rs ++ [(sent.toList, g)]) := by
  obtain ⟨w, sent, he, hw, -, hs, hev, rfl, rfl⟩ := roundIn_ok _ _ _ _ _ _ _ _ _ _ h
  obtain rfl : OnBytes.Psc.Weight.equality z 3 = w :=
    Option.some.inj ((weight_eq2 z degree).symm.trans hw)
  have hs' : sent.size + 1 = 3 := hs
  refine ⟨sent, by omega, hev, rfl, rfl, rfl, rfl, rfl, he, ?_⟩
  exact ran_push hp z 3 sent g hs' _ rfl rfl rfl rfl rfl rfl

/-- A round of the form eq, of a degree that the caller gives. -/
theorem ran_roundIn {p : Psc} {first : Nat} {mu eps : E} {zd : List (E × Nat)}
    {rs : List (List E × E)} (hp : Ran p first mu eps zd rs) (z : E) (degree : Nat) (F G : Fork)
    (c c' : Ctx) (g : E) (p' : Psc) (h : roundIn .eq p z degree F c = .ok (((g, p'), G), c')) :
    ∃ sent : Array E, sent.size = degree ∧ Evs [.read degree sent, .ans .pscRound g] c c' ∧
      G = took F degree ∧ p'.target = p.target ∧ p'.start = p.start ∧ p'.started = p.started ∧
      p'.rowMade = p.rowMade ∧ p'.ended = false ∧
      Ran p' first mu eps (zd ++ [(z, degree + 1)]) (rs ++ [(sent.toList, g)]) := by
  obtain ⟨w, sent, he, hw, -, hs, hev, rfl, rfl⟩ := roundIn_ok _ _ _ _ _ _ _ _ _ _ h
  obtain rfl := weight_eq z degree w hw
  have hs' : sent.size + 1 = degree + 1 := hs
  refine ⟨sent, by omega, hev, rfl, rfl, rfl, rfl, rfl, he, ?_⟩
  exact ran_push hp z (degree + 1) sent g hs' _ rfl rfl rfl rfl rfl rfl

/-- The round in Y and the round of the end values. Y's pair has the coordinate `zeroE`, which every
reading takes to 0. -/
theorem ran_ends {p : Psc} {first : Nat} {mu eps : E} {zd : List (E × Nat)}
    {rs : List (List E × E)} (hp : Ran p first mu eps zd rs) (degreeInY n : Nat) (F G : Fork)
    (c c' : Ctx) (e : Nat) (p' : Psc) (h : pscEnds p degreeInY n F c = .ok (((e, p'), G), c')) :
    ∃ (sent : Array E) (beta : E) (v : Array E), sent.size = degreeInY ∧ v.size = n ∧
      Evs [.read degreeInY sent, .ansNZ .pscY beta, .read n v, .empty .pscValues] c c' ∧
      e = F.next + degreeInY ∧ (took F (degreeInY + n)).hideRun e v beta = some G ∧
      p'.target = p.target ∧ p'.start = p.start ∧ p'.started = p.started ∧
      p'.rowMade = p.rowMade ∧ p'.ended = true ∧
      Ran p' first mu eps (zd ++ [(zeroE, degreeInY + 1)]) (rs ++ [(sent.toList, beta)]) := by
  obtain ⟨sent, beta, v, -, -, -, hs, hv, hev, he, hG, rfl⟩ := pscEnds_ok _ _ _ _ _ _ _ _ _ h
  refine ⟨sent, beta, v, hs, hv, hev, he, hG, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact ran_push hp zeroE (degreeInY + 1) sent beta (by omega) _ rfl rfl rfl rfl rfl rfl

/-- Equality weights paired with challenges. -/
theorem zip_eqW : ∀ (zd : List (E × Nat)) (gs : List E),
    (eqW zd).zip gs = (zd.zip gs).map fun x => (OnBytes.Psc.Weight.equality x.1.1 x.1.2, x.2)
  | [], _ => by simp [eqW]
  | _ :: _, [] => by simp [eqW]
  | a :: zd, g :: gs => by
    have ih := zip_eqW zd gs
    simp only [eqW, List.map_cons, List.zip_cons_cons] at ih ⊢
    rw [ih]

section Read
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- The flat step gives what the state holds. -/
theorem ran_takeSc {p : Psc} {first : Nat} {mu eps : E} {zd : List (E × Nat)}
    {rs : List (List E × E)} (h : Ran p first mu eps zd rs) (values : Option (List E))
    (rest : Rounds K) :
    takeSc (flH ρ mu eps rs values ++ rest) (ρ.val p.target) (zd.map fun x => ρ.val x.1)
        values.isSome =
      (⟨ρ.val p.eps, p.r.toList.map ρ.val, ρ.val p.claim, (values.getD []).map ρ.val⟩, rest) := by
  rw [takeSc_eq ρ zd mu eps p.target rs values rest h.fits, h.eps_eq, h.r_eq, ← h.claim_eq,
    List.map_map]
  rfl

/-- What `Psc.walk` computes. -/
theorem ran_walk {p : Psc} {first : Nat} {mu eps : E} {zd : List (E × Nat)}
    {rs : List (List E × E)} (h : Ran p first mu eps zd rs) :
    p.walk.1.map ρ.val = walkK ((zd.zip rs).map fun x => (x.1.2, ρ.val x.2.2)) ∧
      ρ.val p.walk.2 = 1 := by
  have e : zipT p.vars.toList p.r.toList =
      ((zd.zip (rs.map (·.2))).map fun x => (OnBytes.Psc.Weight.equality x.1.1 x.1.2, x.2)) := by
    rw [zipT_eq, h.vars_eq, h.r_eq, zip_eqW]
  unfold Psc.walk
  rw [e]
  obtain ⟨h1, h2⟩ := hidingWalk_eq ρ (zd.zip (rs.map (·.2)))
  refine ⟨?_, h2⟩
  rw [h1]
  congr 1
  rw [List.zip_map_right, List.map_map]
  rfl

/-- The value of the claim that the sumcheck leaves. -/
theorem ran_row {p : Psc} {first : Nat} {mu eps : E} {zd : List (E × Nat)}
    {rs : List (List E × E)} (h : Ran p first mu eps zd rs) (W : World K) (S0 : E) (kept : Aff) :
    (p.rowForm S0 kept).value ρ W =
      sumFrom (fun j x => ρ.val x * W.slot j) first p.walk.1 +
        ρ.val eps * (ρ.val p.target - p.start.value ρ W) + ρ.val eps * kept.value ρ W -
        (ρ.val p.claim - ρ.val eps * ρ.val S0) := by
  rw [Psc.rowForm_value, (ran_walk ρ h).2, h.first_eq, h.eps_eq, mul_one]

/-- A sum over read elements is the sum over the list of their readings. -/
theorem sumFrom_val (g : Nat → K) : ∀ (l : List E) (s : Nat),
    sumFrom (fun j x => ρ.val x * g j) s l = sumFrom (fun j y => y * g j) s (l.map ρ.val)
  | [], _ => rfl
  | x :: l, s => by
    simp only [sumFrom, List.map_cons]
    rw [sumFrom_val g l (s + 1)]

/-- The same with the weights written out. -/
theorem ran_rowK {p : Psc} {first : Nat} {mu eps : E} {zd : List (E × Nat)}
    {rs : List (List E × E)} (h : Ran p first mu eps zd rs) (W : World K) (S0 : E) (kept : Aff) :
    (p.rowForm S0 kept).value ρ W =
      sumFrom (fun j y => y * W.slot j) first
          (walkK ((zd.zip rs).map fun x => (x.1.2, ρ.val x.2.2))) +
        ρ.val eps * (ρ.val p.target - p.start.value ρ W) + ρ.val eps * kept.value ρ W -
        (ρ.val p.claim - ρ.val eps * ρ.val S0) := by
  rw [ran_row ρ h, sumFrom_val, (ran_walk ρ h).1]

end Read

end OnBytes.PscRun

#print axioms OnBytes.PscRun.ran_roundIn2
#print axioms OnBytes.PscRun.ran_roundIn
#print axioms OnBytes.PscRun.ran_ends
#print axioms OnBytes.PscRun.ran_takeSc
#print axioms OnBytes.PscRun.ran_walk
#print axioms OnBytes.PscRun.ran_row
#print axioms OnBytes.PscRun.ran_rowK
