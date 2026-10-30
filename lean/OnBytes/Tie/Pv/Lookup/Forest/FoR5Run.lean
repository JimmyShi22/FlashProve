-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoR5Run.lean.
The rounds of the layer of the table's leaves and of the test on bits in the byte-level lookup
routine: what a run that returns has done.

The byte-level routine of a sub-proof's lookup (OnBytes.Model.Forest.pad) ends with two sumchecks:
one over the leaves of the table's side, which is left open (its claim is made later, with the
claims on the planes), and, at a fresh point, one that tests that the planes hold bits. This file
says, for every run of these lines that returns, which calls of the channel's routines lead from the
context before it to the one after it,
with which results, what the state of the sub-proof is afterwards, and what each returned value is
in terms of these results. No field arithmetic is read here.

 * `zdOf form zs`: for rounds of one form under equality weights: the pairs (coordinate of the
   equality point, number of coefficients). `evVars zd rs`: the calls of such rounds, from the
   messages and challenges rs. `FitsA zd rs`: as many rounds as variables, each message one element
   short of its number of coefficients. `slotsOf zd`: the slots that the rounds take. `after`:
   the state of a sumcheck after them.
 * `roundsIn_ok`: a run of `roundsIn` under a form with equality weights.
 * `R5D`: what the two sumchecks received and drew, as a record. `R5D.evs`: the calls, in order.
 * `leavesBits_ok`: from the eight lines of the routine, each as a run that returns: there is such a
   record; the calls are its calls; the returned values and the state are given by it.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoEv
import OnBytes.Tie.Pv.Psc.FlatTie

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie

/-- The pairs (coordinate of the equality point, number of coefficients) of rounds of one form. -/
def zdOf (form : RoundForm) (zs : List (E × ℕ)) : List (E × ℕ) :=
  zs.map fun z => (z.1, roundValues form z.2 + 1)

/-- The calls of the variables' rounds. -/
def evVars : List (E × ℕ) → List (Array E × E) → List Ev
  | p :: zd, r :: rs => .read (p.2 - 1) r.1 :: .ans .pscRound r.2 :: evVars zd rs
  | _, _ => []

/-- As many rounds as variables; each message is one element short of the number of coefficients. -/
def FitsA : List (E × ℕ) → List (Array E × E) → Prop
  | [], [] => True
  | p :: zd, r :: rs => r.1.size + 1 = p.2 ∧ FitsA zd rs
  | _, _ => False

/-- The slots that the rounds take. -/
def slotsOf (zd : List (E × ℕ)) : ℕ := (zd.map fun p => p.2 - 1).sum

/-- Messages as lists. -/
def lsOf (rs : List (Array E × E)) : List (List E × E) := rs.map fun r => (r.1.toList, r.2)

/-- The state of a sumcheck after rounds under equality weights. -/
def after (p : Psc) (zd : List (E × ℕ)) (rs : List (Array E × E)) : Psc :=
  { p with
    claim := OnBytes.Psc.claimAfter (eqW zd) (lsOf rs) p.claim
    vars := p.vars ++ (eqW zd).toArray
    r := p.r ++ (rs.map (·.2)).toArray }

private theorem took_took (F : Fork) (a b : ℕ) : took (took F a) b = took F (a + b) := by
  simp [took, Nat.add_assoc]

private theorem took5 (F : Fork) (a b : ℕ) :
    took (took (took (took (took F 1) a) 1) b) (2 + 1) =
      took F (F.next + 1 + a + 1 + b + 2 + 1 - F.next) := by
  simp only [took_took]
  congr 1
  omega

private theorem push_append {α : Type} (a : Array α) (x : α) (l : List α) :
    a.push x ++ l.toArray = a ++ (x :: l).toArray := by
  apply Array.ext'
  simp

private theorem after_nil (p : Psc) : after p [] [] = p := by
  cases p
  simp [after, eqW, lsOf, OnBytes.Psc.claimAfter]

private theorem after_cons (p : Psc) (z : E) (d : ℕ) (sent : Array E) (x : E) (zd : List (E × ℕ))
    (rs : List (Array E × E)) :
    after { p with
        claim := OnBytes.Psc.polyAt
          ((OnBytes.Psc.Weight.equality z d).complete sent.toList p.claim) x
        vars := p.vars.push (OnBytes.Psc.Weight.equality z d)
        r := p.r.push x } zd rs = after p ((z, d) :: zd) ((sent, x) :: rs) := by
  unfold after
  simp only [eqW, lsOf, List.map_cons, claimAfter_cons, push_append]

private theorem weight_eq (form : RoundForm) (hf : form.equality = true) (z : E) (degree : ℕ)
    (w : OnBytes.Psc.Weight) (h : form.weight z degree = some w) :
    w = OnBytes.Psc.Weight.equality z (roundValues form degree + 1) := by
  unfold RoundForm.weight at h
  split at h
  · exact (Option.some.inj h).symm
  · exact absurd h (by simp)

private theorem roundsGo_ok (form : RoundForm) (hf : form.equality = true) :
    ∀ (zs : List (E × ℕ)) (acc : Array E) (p : Psc) (F G : Fork) (c c' : Ctx) (r : Array E)
      (p' : Psc),
      (zs.foldlM
        (fun (s : Array E × Psc) (z : E × ℕ) => do
          let (r, q) ← roundIn form s.2 z.1 z.2
          pure (s.1.push r, q))
        (acc, p)) F c = .ok (((r, p'), G), c') →
      ∃ rs : List (Array E × E), FitsA (zdOf form zs) rs ∧ Evs (evVars (zdOf form zs) rs) c c' ∧
        G = took F (slotsOf (zdOf form zs)) ∧ r = acc ++ (rs.map (·.2)).toArray ∧
        p' = after p (zdOf form zs) rs := by
  intro zs
  induction zs with
  | nil =>
    intro acc p F G c c' r p' h
    rw [foldlM_nil_ok] at h
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ : ((r = acc ∧ p' = p) ∧ G = F) ∧ c' = c := by
      simpa [Prod.ext_iff] using h
    exact ⟨[], trivial, rfl, rfl, by simp, (after_nil _).symm⟩
  | cons z zs ih =>
    intro acc p F G c c' r p' h
    rw [foldlM_cons_ok] at h
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := h
    dsimp only at h1
    rw [bind_ok] at h1
    obtain ⟨⟨x, q⟩, G₁, c₂, h3, h4⟩ := h1
    dsimp only at h4
    rw [pure_ok] at h4
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (s₁ = (acc.push x, q) ∧ F₁ = G₁) ∧ c₁ = c₂ := by
      simpa [Prod.ext_iff] using h4
    obtain ⟨w, sent, _, hw, _, hsz, hev, rfl, rfl⟩ := roundIn_ok form p z.1 z.2 F _ c _ x _ h3
    obtain rfl := weight_eq form hf _ _ _ hw
    obtain ⟨rs, a1, a2, a3, a4, a5⟩ := ih _ _ _ _ _ _ _ _ h2
    refine ⟨(sent, x) :: rs, ⟨hsz, a1⟩, (evs_append [_, _] _ c c').2 ⟨_, hev, a2⟩, ?_, ?_, ?_⟩
    · rw [a3, took_took]
      rfl
    · rw [a4, push_append]
      rfl
    · rw [a5]
      exact after_cons p z.1 _ sent x _ rs

/-- A run of the rounds of one form under equality weights. -/
theorem roundsIn_ok (form : RoundForm) (hf : form.equality = true) (p : Psc) (zs : List (E × ℕ))
    (F G : Fork) (c c' : Ctx) (r : Array E) (p' : Psc)
    (h : roundsIn form p zs F c = .ok (((r, p'), G), c')) :
    ∃ rs : List (Array E × E), FitsA (zdOf form zs) rs ∧ Evs (evVars (zdOf form zs) rs) c c' ∧
      G = took F (slotsOf (zdOf form zs)) ∧ r = (rs.map (·.2)).toArray ∧
      p' = after p (zdOf form zs) rs := by
  obtain ⟨rs, a1, a2, a3, a4, a5⟩ := roundsGo_ok form hf zs #[] p F G c c' r p' h
  exact ⟨rs, a1, a2, a3, by rw [a4]; simp, a5⟩

/-! ### the two sumchecks -/

/-- What the two sumchecks received and drew. -/
structure R5D where
  /-- the leaves: the public target, the hiding polynomial's sum, the factor, the rounds -/
  tgL : E
  muL : E
  epsL : E
  rsL : List (Array E × E)
  /-- the fresh point, as drawn -/
  ptZ : Array E
  /-- the bits: the hiding polynomial's sum, the factor, the rounds -/
  muB : E
  epsB : E
  rsB : List (Array E × E)
  /-- the round in the further variable, its challenge, the shown value -/
  sentY : Array E
  beta : E
  v : Array E

/-- The leaves' variables: the point's coordinates in the array's order; degree 2 in a variable of
the rows, 1 in one of the planes, without the equality factor. -/
def zdL (m d : ℕ) (rho : Array E) : List (E × ℕ) :=
  zdOf .eq ((List.range m).map fun j => (rho.getD j zeroE, if j < d then 2 else 1))

/-- The bits' variables: the fresh point, reversed. -/
def zdB (ptZ : Array E) : List (E × ℕ) := zdOf .eq2 (ptZ.reverse.toList.map fun z => (z, 0))

/-- The first slot of the bits' sumcheck. -/
def firstB (m d : ℕ) (rho : Array E) (first : ℕ) : ℕ := first + 1 + slotsOf (zdL m d rho)

namespace R5D
variable (D : R5D) (m d : ℕ) (rho : Array E)

/-- The calls, in order. -/
def evs : List Ev :=
  [.sum D.muL, .ans .pscEpsilon D.epsL] ++ (evVars (zdL m d rho) D.rsL ++
    ([.point .zero m D.ptZ] ++ ([.sum D.muB, .ans .pscEpsilon D.epsB] ++
      (evVars (zdB D.ptZ) D.rsB ++
        [.read 2 D.sentY, .ansNZ .pscY D.beta, .read 1 D.v, .empty .pscValues]))))

/-- The leaves' sumcheck as the routine leaves it: no claim is made yet. -/
def leaves (C : Aff) (first : ℕ) : Psc :=
  after { start := C, started := true, target := D.tgL, first := first, eps := D.epsL,
          claim := addE D.muL (mulE D.epsL D.tgL) } (zdL m d rho) D.rsL

/-- The bits' sumcheck behind its variables' rounds. -/
def bits1 (first : ℕ) : Psc :=
  after { start := Aff.ofConst zeroE, started := true, target := zeroE,
          first := firstB m d rho first, eps := D.epsB,
          claim := addE D.muB (mulE D.epsB zeroE) } (zdB D.ptZ) D.rsB

/-- The bits' sumcheck behind the round in the further variable. -/
def bits2 (first : ℕ) : Psc :=
  { D.bits1 m d rho first with
    claim := OnBytes.Psc.polyAt ((OnBytes.Psc.Weight.atZero 3).complete D.sentY.toList
      (D.bits1 m d rho first).claim) D.beta
    vars := (D.bits1 m d rho first).vars.push (OnBytes.Psc.Weight.atZero 3)
    r := (D.bits1 m d rho first).r.push D.beta
    ended := true }

/-- The slot of the shown value. -/
def sBit (first : ℕ) : ℕ := firstB m d rho first + 1 + slotsOf (zdB D.ptZ) + 2

end R5D

private theorem publicPart_const (F : Fork) (x : E) : F.publicPart (Aff.ofConst x) = some x := rfl

/-- The eight lines, each as a run that returns. -/
theorem leavesBits_ok (m d : ℕ) (rho : Array E) (C : Aff)
    (F F1 F2 F3 F4 F5 F6 F7 F8 : Fork) (c c1 c2 c3 c4 c5 c6 c7 c8 : Ctx)
    (lv0 lv b0 b1 b2 b3 : Psc) (zb0 zb1 pt : Array E) (sBit : ℕ) (vBit : E) (row : Aff)
    (h1 : pscBegin C F c = .ok ((lv0, F1), c1))
    (h2 : roundsIn .eq lv0
      ((List.range m).map fun j => (rho.getD j zeroE, if j < d then 2 else 1)) F1 c1 =
        .ok (((zb0, lv), F2), c2))
    (h3 : SubM.point .zero m F2 c2 = .ok ((pt, F3), c3))
    (h4 : pscBegin (Aff.ofConst zeroE) F3 c3 = .ok ((b0, F4), c4))
    (h5 : roundsIn .eq2 b0 (pt.reverse.toList.map fun z => (z, 0)) F4 c4 =
      .ok (((zb1, b1), F5), c5))
    (h6 : pscEnds b1 2 1 F5 c5 = .ok (((sBit, b2), F6), c6))
    (h7 : SubM.shown sBit F6 c6 = .ok ((vBit, F7), c7))
    (h8 : pscRow b2 (subE (mulE vBit vBit) vBit) {} F7 c7 = .ok (((row, b3), F8), c8)) :
    ∃ D : R5D,
      F.publicPart C = some D.tgL ∧ FitsA (zdL m d rho) D.rsL ∧ FitsA (zdB D.ptZ) D.rsB ∧
      D.sentY.size = 2 ∧ D.v.size = 1 ∧ pt = D.ptZ ∧ Evs (D.evs m d rho) c c8 ∧
      lv = D.leaves m d rho C F.next ∧ zb0 = (D.rsL.map (·.2)).toArray ∧
      zb1 = (D.rsB.map (·.2)).toArray ∧ sBit = D.sBit m d rho F.next ∧
      b2 = D.bits2 m d rho F.next ∧
      (took F (D.sBit m d rho F.next + 1 - F.next)).hideRun sBit D.v D.beta = some F6 ∧
      F6.shown sBit = some vBit ∧
      F6.hideRun b2.first (Array.replicate b2.walk.1.length zeroE) (subE zeroE oneE) = some F8 ∧
      row = b2.rowForm (subE (mulE vBit vBit) vBit) {} := by
  obtain ⟨tgL, muL, epsL, a1, a2, rfl, rfl⟩ := pscBegin_ok C F F1 c c1 lv0 h1
  obtain ⟨rsL, b1', b2', rfl, rfl, rfl⟩ := roundsIn_ok .eq rfl _ _ _ _ _ _ _ _ h2
  obtain ⟨e3, rfl⟩ := (point_ok .zero m _ _ _ _ _).1 h3
  obtain ⟨tgB, muB, epsB, d1, d2, rfl, rfl⟩ := pscBegin_ok _ _ _ _ _ _ h4
  obtain rfl : zeroE = tgB := Option.some.inj ((publicPart_const _ _).symm.trans d1)
  obtain ⟨rsB, f1, f2, rfl, rfl, rfl⟩ := roundsIn_ok .eq2 rfl _ _ _ _ _ _ _ _ h5
  obtain ⟨sentY, beta, v, _, _, _, g1, g2, g3, rfl, g4, rfl⟩ := pscEnds_ok _ 2 1 _ _ _ _ _ _ h6
  obtain ⟨vB, k1, k2⟩ := (shown_ok _ _ _ _).1 h7
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (vBit = vB ∧ F7 = F6) ∧ c7 = c6 := by
    simpa [Prod.ext_iff] using k2
  obtain ⟨_, _, _, _, rfl, l1, rfl, _⟩ := pscRow_ok _ _ _ _ _ _ _ _ _ h8
  clear h1 h2 h3 h4 h5 h6 h7 h8
  refine ⟨⟨tgL, muL, epsL, rsL, pt, muB, epsB, rsB, sentY, beta, v⟩, a1, b1', f1, g1, g2, rfl,
    ?_, rfl, rfl, rfl, ?_, rfl, ?_, k1, l1, rfl⟩
  · exact (evs_append _ _ _ _).2 ⟨_, a2, (evs_append _ _ _ _).2 ⟨_, b2', (evs_append _ _ _ _).2
      ⟨_, e3, (evs_append _ _ _ _).2 ⟨_, d2, (evs_append _ _ _ _).2 ⟨_, f2, g3⟩⟩⟩⟩⟩
  · rfl
  · show (took F (F.next + 1 + slotsOf (zdL m d rho) + 1 + slotsOf (zdB pt) + 2 + 1 -
      F.next)).hideRun _ v beta = some _
    rw [← took5]
    exact g4

end Fo
