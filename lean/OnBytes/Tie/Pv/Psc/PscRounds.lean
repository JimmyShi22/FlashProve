-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Psc/PscRounds.lean: rounds of one form in a row (`roundsIn`,
OnBytes/Model/Look.lean): what a run that returns has read, drawn and left, for the two forms that
sum under the equality polynomial.

Definitions, and theorems with their proofs.

Main names:
  `evRounds ns`: the calls of the channel's routines that make up the rounds ns (message,
    challenge).
  `EqForm form dOf`: a round of this form, of the degree that the caller gives, is summed under
    equality weights, and its polynomial has dOf degree coefficients. `eqForm_eq2` (3), `eqForm_eq`
    (degree + 1).
  `ran_roundInG`: one round. `ran_roundsIn`: the rounds in a row: the state's law (`Ran`,
    OnBytes/Tie/Pv/Psc/PscWhole.lean) is carried on by one pair and one round for each member of the
    caller's list; the array returned holds the challenges in the order of the rounds.
  `took_took`, `took_zero`: slots taken twice; none taken.
  `Evs.split`; `evRounds_took`, `ends_took`: these calls as rounds of a view.
  `evWhole`, `whole_took`: the calls of one whole sumcheck with end values, taken off a view, are
    the flat step's plain data (`flH`, OnBytes/Tie/Pv/Psc/FlatTie.lean).
  `evOpen`, `open_took`: the same for a sumcheck that shows no end values.

Limits: `whole_took` and `open_took` ask that no message is open where the sumcheck begins, so the
sum of the hiding polynomial is alone in its message; a caller that has received elements into that
message before is not reached: there the sum is the message's last element, and the flat step reads
the first. Nothing is said where a routine fails. Nothing on soundness, on an honest prover or on
hiding.


-/
import OnBytes.Tie.Pv.Psc.PscWhole
import OnBytes.Model.Look

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.PscRun
open OnBytes OnBytes.Model OnBytes.PscTie

/-- The calls that make up rounds of a sumcheck's variables. -/
def evRounds (ns : List (List E × E)) : List Ev :=
  ns.flatMap fun x => [.read x.1.length x.1.toArray, .ans .pscRound x.2]

/-- A round of this form is summed under equality weights. -/
def EqForm (form : RoundForm) (dOf : Nat → Nat) : Prop :=
  ∀ z degree w, form.weight z degree = some w → w = OnBytes.Psc.Weight.equality z (dOf degree)

/-- The form eq2: three coefficients. -/
theorem eqForm_eq2 : EqForm .eq2 fun _ => 3 := fun z degree _ h =>
  (Option.some.inj ((weight_eq2 z degree).symm.trans h)).symm

/-- The form eq: degree + 1 coefficients. -/
theorem eqForm_eq : EqForm .eq (· + 1) := fun z degree w h => weight_eq z degree w h

/-- Slots taken twice. -/
theorem took_took (F : Fork) (a b : Nat) : took (took F a) b = took F (a + b) := by
  simp only [took, Nat.add_assoc]

/-- No slot taken. -/
theorem took_zero (F : Fork) : took F 0 = F := rfl

/-- One round of a form that sums under equality weights. -/
theorem ran_roundInG {form : RoundForm} {dOf : Nat → Nat} (hf : EqForm form dOf) {p : Psc}
    {first : Nat} {mu eps : E} {zd : List (E × Nat)} {rs : List (List E × E)}
    (hp : Ran p first mu eps zd rs) (z : E) (degree : Nat) (F G : Fork) (c c' : Ctx) (g : E)
    (p' : Psc) (h : roundIn form p z degree F c = .ok (((g, p'), G), c')) :
    ∃ sent : Array E, sent.size + 1 = dOf degree ∧
      Evs [.read sent.size sent, .ans .pscRound g] c c' ∧ G = took F sent.size ∧
      p'.target = p.target ∧ p'.start = p.start ∧ p'.started = p.started ∧
      p'.rowMade = p.rowMade ∧ p'.ended = p.ended ∧
      Ran p' first mu eps (zd ++ [(z, dOf degree)]) (rs ++ [(sent.toList, g)]) := by
  obtain ⟨w, sent, -, hw, -, hs, hev, rfl, rfl⟩ := roundIn_ok _ _ _ _ _ _ _ _ _ _ h
  obtain rfl := hf z degree w hw
  have hs' : sent.size + 1 = dOf degree := hs
  have hd : (OnBytes.Psc.Weight.equality z (dOf degree)).d - 1 = sent.size := by
    show dOf degree - 1 = sent.size
    omega
  rw [hd] at hev
  refine ⟨sent, hs', hev, by rw [hd], rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact ran_push hp z (dOf degree) sent g hs' _ rfl rfl rfl rfl rfl rfl

/-- The loop of `roundsIn`, from any array of challenges so far. -/
theorem ran_roundsLoop {form : RoundForm} {dOf : Nat → Nat} (hf : EqForm form dOf) {first : Nat}
    {mu eps : E} : ∀ (zs : List (E × Nat)) (acc : Array E) (p : Psc) (zd : List (E × Nat))
    (rs : List (List E × E)) (F G : Fork) (c c' : Ctx) (r : Array E) (p' : Psc),
    Ran p first mu eps zd rs →
    (zs.foldlM (fun (s : Array E × Psc) z => do
        let (r, q) ← roundIn form s.2 z.1 z.2
        pure (s.1.push r, q)) (acc, p) : SubM (Array E × Psc)) F c = .ok (((r, p'), G), c') →
    ∃ ns : List (List E × E), List.Forall₂ (fun z x => x.1.length + 1 = dOf z.2) zs ns ∧
      r.toList = acc.toList ++ ns.map (·.2) ∧ Evs (evRounds ns) c c' ∧
      G = took F (ns.map (·.1.length)).sum ∧
      p'.target = p.target ∧ p'.start = p.start ∧ p'.started = p.started ∧
      p'.rowMade = p.rowMade ∧ p'.ended = p.ended ∧
      Ran p' first mu eps (zd ++ zs.map fun z => (z.1, dOf z.2)) (rs ++ ns)
  | [], acc, p, zd, rs, F, G, c, c', r, p', hp, h => by
    rw [List.foldlM_nil, pure_ok] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h
    exact ⟨[], List.Forall₂.nil, by simp, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by simpa using hp⟩
  | z :: zs, acc, p, zd, rs, F, G, c, c', r, p', hp, h => by
    rw [List.foldlM_cons, bind_ok] at h
    obtain ⟨⟨acc1, p1⟩, F1, c1, h1, h⟩ := h
    rw [bind_ok] at h1
    obtain ⟨⟨g, q⟩, F2, c2, h2, h1⟩ := h1
    simp only [] at h1
    rw [pure_ok] at h1
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h1
    obtain ⟨sent, hs, hev, rfl, t1, t2, t3, t4, t5, hq⟩ := ran_roundInG hf hp _ _ _ _ _ _ _ _ h2
    obtain ⟨ns, hn, hr, hev', rfl, u1, u2, u3, u4, u5, hq'⟩ :=
      ran_roundsLoop hf zs _ _ _ _ _ _ _ _ _ _ hq h
    refine ⟨(sent.toList, g) :: ns, List.Forall₂.cons (by simpa using hs) hn, ?_, ?_, ?_,
      u1.trans t1, u2.trans t2, u3.trans t3, u4.trans t4, u5.trans t5, ?_⟩
    · rw [hr]
      simp
    · have e : evRounds ((sent.toList, g) :: ns) =
          [.read sent.size sent, .ans .pscRound g] ++ evRounds ns := by
        simp [evRounds]
      rw [e]
      exact Evs.append hev hev'
    · rw [took_took]
      simp
    · simpa using hq'

/-- Rounds of one form in a row. -/
theorem ran_roundsIn {form : RoundForm} {dOf : Nat → Nat} (hf : EqForm form dOf) {p : Psc}
    {first : Nat} {mu eps : E} {zd : List (E × Nat)} {rs : List (List E × E)}
    (hp : Ran p first mu eps zd rs) (zs : List (E × Nat)) (F G : Fork) (c c' : Ctx) (r : Array E)
    (p' : Psc) (h : roundsIn form p zs F c = .ok (((r, p'), G), c')) :
    ∃ ns : List (List E × E), List.Forall₂ (fun z x => x.1.length + 1 = dOf z.2) zs ns ∧
      r.toList = ns.map (·.2) ∧ Evs (evRounds ns) c c' ∧ G = took F (ns.map (·.1.length)).sum ∧
      p'.target = p.target ∧ p'.start = p.start ∧ p'.started = p.started ∧
      p'.rowMade = p.rowMade ∧ p'.ended = p.ended ∧
      Ran p' first mu eps (zd ++ zs.map fun z => (z.1, dOf z.2)) (rs ++ ns) := by
  obtain ⟨ns, h1, h2, h3⟩ := ran_roundsLoop hf zs #[] p zd rs F G c c' r p' hp h
  exact ⟨ns, h1, by simpa using h2, h3⟩

/-- The rounds of a sumcheck's variables, taken off a view. -/
theorem evRounds_took : ∀ (ns : List (List E × E)) (c c' : Ctx), Clean c → Evs (evRounds ns) c c' →
    ∃ rvs : List Fmt.RoundView, Took c rvs c' ∧ rvs.map (fun rv => (sentOf rv, drawnOf rv)) =
      ns.map fun x => (x.1, [x.2])
  | [], c, c', hc, h => by
    obtain rfl : c' = c := h
    exact ⟨[], Took.nil hc, rfl⟩
  | x :: ns, c, c', hc, h => by
    obtain ⟨c1, h1, c2, h2, h⟩ := h
    obtain ⟨rv, hr, hs, hd⟩ := round_read _ _ _ _ c c2 hc ⟨c1, h1, c2, h2, rfl⟩
    obtain ⟨rvs, ht, hm⟩ := evRounds_took ns c2 c' hr.2.1 h
    refine ⟨rv :: rvs, Took.append hr.took ht, ?_⟩
    rw [List.map_cons, List.map_cons, hm, hs, hd]

/-- Calls after calls, taken apart. -/
theorem Evs.split : ∀ {l m : List Ev} {c c' : Ctx}, Evs (l ++ m) c c' →
    ∃ c1, Evs l c c1 ∧ Evs m c1 c'
  | [], _, c, _, h => ⟨c, rfl, h⟩
  | _ :: _, _, _, _, ⟨d, h0, h1⟩ => by
    obtain ⟨c1, a, b⟩ := Evs.split h1
    exact ⟨c1, ⟨d, h0, a⟩, b⟩

/-- The calls of `pscEnds` are two rounds of the view. -/
theorem ends_took (a n : Nat) (sent v : Array E) (beta : E) (c c' : Ctx) (hc : Clean c)
    (h : Evs [.read a sent, .ansNZ .pscY beta, .read n v, .empty .pscValues] c c') :
    ∃ rv1 rv2, Took c [rv1, rv2] c' ∧ sentOf rv1 = sent.toList ∧ drawnOf rv1 = [beta] ∧
      sentOf rv2 = v.toList ∧ drawnOf rv2 = [] := by
  obtain ⟨c1, h1, c2, h2, c3, h3, c4, h4, rfl⟩ := h
  obtain ⟨rv1, r1, s1, d1⟩ := round_readNZ _ _ _ _ c c2 hc ⟨c1, h1, c2, h2, rfl⟩
  obtain ⟨rv2, r2, s2, d2⟩ := round_values _ _ _ c2 _ r1.2.1 ⟨c3, h3, _, h4, rfl⟩
  exact ⟨rv1, rv2, Took.append r1.took r2.took, s1, d1, s2, d2⟩

/-- The calls of one whole sumcheck with end values: the beginning, the rounds of the variables, the
round in Y, the round of the values. -/
def evWhole (mu eps : E) (ns : List (List E × E)) (sent : Array E) (beta : E) (v : Array E) :
    List Ev :=
  [.sum mu, .ans .pscEpsilon eps] ++ (evRounds ns ++
    [.read sent.size sent, .ansNZ .pscY beta, .read v.size v, .empty .pscValues])

/-- The calls of one whole sumcheck, taken off a view, are the flat step's plain data. -/
theorem whole_took {K : Type} [CommRing K] (ρ : Reading K) (mu eps : E) (ns : List (List E × E))
    (sent : Array E) (beta : E) (v : Array E) (c c' : Ctx) (hc : Clean c)
    (h : Evs (evWhole mu eps ns sent beta v) c c') :
    ∃ rvs : List Fmt.RoundView, Took c rvs c' ∧
      rvs.map (fun rv => ((sentOf rv).map ρ.val, (drawnOf rv).map ρ.val)) =
        flH ρ mu eps (ns ++ [(sent.toList, beta)]) (some v.toList) := by
  obtain ⟨c1, h1, h⟩ := Evs.split h
  obtain ⟨c2, h2, h3⟩ := Evs.split h
  obtain ⟨rv0, r0, s0, d0⟩ := round_sum _ _ _ c c1 hc h1
  obtain ⟨rvs, t1, m1⟩ := evRounds_took ns c1 c2 r0.2.1 h2
  obtain ⟨rv1, rv2, t2, s1, d1, s2, d2⟩ := ends_took _ _ _ _ _ c2 c' t1.2.1 h3
  refine ⟨[rv0] ++ (rvs ++ [rv1, rv2]), Took.append r0.took (Took.append t1 t2), ?_⟩
  have m2 : rvs.map (fun rv => ((sentOf rv).map ρ.val, (drawnOf rv).map ρ.val)) = flR ρ ns := by
    have := congrArg (List.map fun x : List E × List E => (x.1.map ρ.val, x.2.map ρ.val)) m1
    simpa [flR, List.map_map, Function.comp_def] using this
  simp only [List.map_append, List.map_cons, List.map_nil, m2, s0, d0, s1, d1, s2, d2, flH, flR,
    List.append_assoc, List.cons_append, List.nil_append]

/-- The calls of a sumcheck that shows no end values: the beginning and the rounds of the variables.
-/
def evOpen (mu eps : E) (ns : List (List E × E)) : List Ev :=
  [.sum mu, .ans .pscEpsilon eps] ++ evRounds ns

/-- These calls, taken off a view, are the flat step's plain data. -/
theorem open_took {K : Type} [CommRing K] (ρ : Reading K) (mu eps : E) (ns : List (List E × E))
    (c c' : Ctx) (hc : Clean c) (h : Evs (evOpen mu eps ns) c c') :
    ∃ rvs : List Fmt.RoundView, Took c rvs c' ∧
      rvs.map (fun rv => ((sentOf rv).map ρ.val, (drawnOf rv).map ρ.val)) =
        flH ρ mu eps ns none := by
  obtain ⟨c1, h1, h2⟩ := Evs.split h
  obtain ⟨rv0, r0, s0, d0⟩ := round_sum _ _ _ c c1 hc h1
  obtain ⟨rvs, t1, m1⟩ := evRounds_took ns c1 c' r0.2.1 h2
  refine ⟨[rv0] ++ rvs, Took.append r0.took t1, ?_⟩
  have m2 : rvs.map (fun rv => ((sentOf rv).map ρ.val, (drawnOf rv).map ρ.val)) = flR ρ ns := by
    have := congrArg (List.map fun x : List E × List E => (x.1.map ρ.val, x.2.map ρ.val)) m1
    simpa [flR, List.map_map, Function.comp_def] using this
  simp only [List.map_cons, List.map_nil, m2, s0, d0, flH, List.append_nil, List.cons_append,
    List.nil_append]

end OnBytes.PscRun

#print axioms OnBytes.PscRun.ran_roundsIn
#print axioms OnBytes.PscRun.evRounds_took
#print axioms OnBytes.PscRun.whole_took
#print axioms OnBytes.PscRun.open_took
