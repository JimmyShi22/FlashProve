-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Numbers.lean: the slot numbers that the hearing of kind K5 lays into its
record are
a function of the plan and of the ledger's next slot in front of the hearing alone: no value that
the prover
sends, and no element drawn, bears on one of them. So the closed parameters' places
(Att/K05Closed.lean) can
be made before the rounds, of public numbers.

Main names:
  `At s k`; `take_at`, `sum_at`, `batch_at`, `close_at`, `takes_at`, `units_at`: verb by verb; the
    like for
    the ledger's number of slots (`take_ns` … `units_ns`).
  `numsPlan x k`: the numbers, written out by the plan x from the slot k on.
  `numbers_of_plan`: where hear returns from a ledger F whose arrays have their length:
    numsOf h = numsPlan x F.next, and the ledger behind has as many slots as F.
  `closed_is_plan`: closedOf P0 Λ G'.ns (numsOf h) = closedOf P0 Λ F.ns (numsPlan x F.next), at the
    ledger behind
    the hearing and at every one with as many slots. (Stays alone does not keep that number.)

Sources: what Att/K5SaidAll.lean names.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Closed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends)

/-- The ledger's arrays have their length; its next slot is k; the open round's scalars so far are
some list. -/
def At (s : St) (k : ℕ) : Prop := Sized s.1 ∧ s.1.next = k ∧ ∃ pre, Open s.2.1 s.2.2 pre

/-- The slots of a sumcheck's coefficients. -/
def ownOf (vs : List Var) (e : Ends) : ℕ := MaskedSum.ownSlots (vs ++ [.point zeroE (e.dY + 1)])

theorem take_at {n j k : ℕ} {s s' : St} (h : take n s = some (j, s')) (a : At s k) : j = k ∧ At s' (k + n) := by
  obtain ⟨F, rs, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  obtain ⟨hz, hk, pre, ho⟩ := a
  obtain ⟨v, _, _, c3, c4, c5, _, _, c8⟩ := take_said h hz ho
  exact ⟨c4.trans hk, c5, by rw [c8]; exact congrArg (· + n) hk, _, c3⟩

theorem sum_at {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard} {k : ℕ} {s s' : St}
    (h : sum C (.sum vs e) s = some (hh, s')) (a : At s k) :
    hh.first = k ∧ hh.sEnd = k + ownOf vs e ∧ At s' (k + ownOf vs e + e.n) := by
  obtain ⟨F, rs, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  obtain ⟨hz, hk, pre, ho⟩ := a
  obtain ⟨e0, H, used, _, sd⟩ := sum_said h hz ho
  have hk' : F.next = k := hk
  subst e0
  exact ⟨sd.first.trans hk', by rw [sd.sEnd, hk']; rfl, sd.sized, by
    show G.next = _
    rw [sd.next, sd.sEnd, hk']
    rfl, [], open_zero _⟩

theorem batch_at {rows k : ℕ} {w : Array E} {s s' : St} (h : batch rows s = some (w, s')) (a : At s k) : At s' k := by
  obtain ⟨F, rs, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  obtain ⟨e1, e2, _⟩ := batch_spec h
  subst e1 e2
  exact ⟨a.1, a.2.1, [], open_zero _⟩

theorem close_at {n k : ℕ} {d : List E} {s s' : St} (h : close n s = some (d, s')) (a : At s k) : At s' k := by
  obtain ⟨F, rs, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  obtain ⟨e1, e2, _⟩ := close_spec h
  subst e1 e2
  exact ⟨a.1, a.2.1, [], open_zero _⟩

/-- Where n runs of three scalars begin. -/
def planesPlan : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, k => k :: planesPlan n (k + 3)

theorem takes_at : ∀ (n : ℕ) (js : List ℕ) (s s' : St) (k : ℕ), TakesRan 3 n js s s' → At s k →
    js = planesPlan n k ∧ At s' (k + 3 * n)
  | 0, [], s, s', k, h, a => by
    have e : s' = s := h
    subst e
    exact ⟨rfl, a⟩
  | n + 1, j :: js, s, s', k, ⟨s1, h1, h2⟩, a => by
    obtain ⟨e1, a1⟩ := take_at h1 a
    obtain ⟨e2, a2⟩ := takes_at n js s1 s' (k + 3) h2 a1
    exact ⟨by rw [e1, e2]; rfl, by rw [show k + 3 * (n + 1) = k + 3 + 3 * n by omega]; exact a2⟩
  | 0, _ :: _, _, _, _, h, _ => h.elim
  | _ + 1, [], _, _, _, h, _ => h.elim

/-- The slots of a sumcheck of products over n variables: its coefficients. -/
def own3 (n : ℕ) : ℕ := ownOf (List.replicate n (.plain 4)) ⟨2, 0⟩

/-- Where each unit's seven scalars, coefficients and end values begin. -/
def unitsPlan : List (ℕ × ℕ) → ℕ → List (ℕ × ℕ × ℕ)
  | [], _ => []
  | u :: us, k => (k, k + 7, k + 7 + own3 u.1) :: unitsPlan us (k + 7 + own3 u.1 + 2 * u.2)

/-- The next slot behind the units. -/
def unitsNext : List (ℕ × ℕ) → ℕ → ℕ
  | [], k => k
  | u :: us, k => unitsNext us (k + 7 + own3 u.1 + 2 * u.2)

theorem units_at : ∀ (us : List (ℕ × ℕ)) (os : List (ℕ × MaskedSum.Heard)) (s s' : St) (k : ℕ),
    UnitsRan us os s s' → At s k →
    (os.map fun o => (o.1, o.2.first, o.2.sEnd)) = unitsPlan us k ∧ At s' (unitsNext us k)
  | [], [], s, s', k, h, a => by
    have e : s' = s := h
    subst e
    exact ⟨rfl, a⟩
  | u :: us, o :: os, s, s', k, ⟨s2, ⟨s1, h1, h2⟩, h3⟩, a => by
    obtain ⟨e1, a1⟩ := take_at h1 a
    obtain ⟨e2, e3, a2⟩ := sum_at h2 a1
    obtain ⟨e4, a3⟩ := units_at us os s2 s' _ h3 a2
    refine ⟨?_, a3⟩
    rw [List.map_cons, e4, e1, e2, e3]
    rfl
  | [], _ :: _, _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, _, h, _ => h.elim

/-! ## The number of the ledger's slots stays -/

theorem take_ns {n j k : ℕ} {s s' : St} (h : take n s = some (j, s')) (a : At s k) : s'.1.ns = s.1.ns := by
  obtain ⟨F, rs, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  obtain ⟨_, _, _, r, rest, v, _, _, _, hG⟩ := take_spec h
  exact (hideRun_ok _ _ _ _ _ hG ⟨a.1.vp, a.1.mf, a.1.got⟩).ns

theorem sum_ns {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard} {k : ℕ} {s s' : St}
    (h : sum C (.sum vs e) s = some (hh, s')) (a : At s k) : s'.1.ns = s.1.ns := by
  obtain ⟨F, rs, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  obtain ⟨_, _, G1, f, a1, a2⟩ := sum_spec h
  obtain ⟨_, T, R, _, _, _, b4⟩ := MaskedSum.hear_spec a1
  have F1 := hideRun_ok _ _ _ _ _ b4 ⟨a.1.vp, a.1.mf, a.1.got⟩
  have F2 := hideRun_ok _ _ _ _ _ (row_write a2) F1.sized
  exact F2.ns.trans F1.ns

theorem batch_ns {rows : ℕ} {w : Array E} {s s' : St} (h : batch rows s = some (w, s')) : s'.1.ns = s.1.ns := by
  obtain ⟨F, rs, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  rw [(batch_spec h).1]

theorem close_ns {n : ℕ} {d : List E} {s s' : St} (h : close n s = some (d, s')) : s'.1.ns = s.1.ns := by
  obtain ⟨F, rs, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  rw [(close_spec h).1]

theorem takes_ns : ∀ (n : ℕ) (js : List ℕ) (s s' : St) (k : ℕ), TakesRan 3 n js s s' → At s k → s'.1.ns = s.1.ns
  | 0, [], s, s', _, h, _ => by
    have e : s' = s := h
    rw [e]
  | n + 1, _ :: js, s, s', k, ⟨s1, h1, h2⟩, a =>
    (takes_ns n js s1 s' (k + 3) h2 (take_at h1 a).2).trans (take_ns h1 a)
  | 0, _ :: _, _, _, _, h, _ => h.elim
  | _ + 1, [], _, _, _, h, _ => h.elim

theorem units_ns : ∀ (us : List (ℕ × ℕ)) (os : List (ℕ × MaskedSum.Heard)) (s s' : St) (k : ℕ),
    UnitsRan us os s s' → At s k → s'.1.ns = s.1.ns
  | [], [], s, s', _, h, _ => by
    have e : s' = s := h
    rw [e]
  | _ :: us, _ :: os, s, s', k, ⟨s2, ⟨s1, h1, h2⟩, h3⟩, a =>
    (units_ns us os s2 s' _ h3 (sum_at h2 (take_at h1 a).2).2.2).trans
      ((sum_ns h2 (take_at h1 a).2).trans (take_ns h1 a))
  | [], _ :: _, _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, _, h, _ => h.elim

/-! ## The whole -/

/-- The slots of the key's sumcheck's coefficients. -/
def ownKey (x : Params.AttentionRounds) : ℕ :=
  ownOf ((List.replicate x.lt 3 ++ List.replicate x.lgk (x.lt + 3) ++ List.replicate x.lt (x.lt + 2)).map .plain)
    ⟨x.lt + 1, 0⟩

section Plan
variable (x : Params.AttentionRounds) (k : ℕ)

/-- The next slot: behind the units · in front of each later stage. -/
def kB : ℕ := unitsNext x.score (k + 3 * x.planeMessages)
def kE : ℕ := kB x k + 5 + x.lt + 2
def kV : ℕ := kE x k + own3 x.e + 2 * x.pairs
def kM : ℕ := kV x k + 2
def kVD : ℕ := kM x k + own3 x.valueM + 2 * x.pairs
def kX : ℕ := kVD x k + own3 x.valueD + 2 * x.pairs
def kF : ℕ := kX x k + x.pairs
def kD : ℕ := kF x k + own3 x.attained + 2 * x.pairs
def kH : ℕ := kD x k + ownKey x + (x.Lam + x.pairs * x.lt)

/-- **The numbers, by the plan, from the slot k on.** -/
def numsPlan : Nums where
  planes := planesPlan x.planeMessages k
  units := unitsPlan x.score (k + 3 * x.planeMessages)
  five := kB x k
  bits := kB x k + 5
  two := kB x k + 5 + x.lt
  values := kV x k
  maxima := kX x k
  fE := kE x k
  eE := kE x k + own3 x.e
  fM := kM x k
  eM := kM x k + own3 x.valueM
  fVD := kVD x k
  eVD := kVD x k + own3 x.valueD
  fF := kF x k
  eF := kF x k + own3 x.attained
  fD := kD x k
  eD := kD x k + ownKey x
  fH := kH x k
  eH := kH x k + own3 x.bits

end Plan

/-- **The numbers that the hearing lays into its record are the plan's.** -/
theorem numbers_of_plan {x : Params.AttentionRounds} {F : Fork} {rs : List Fmt.RoundView} {h : Heard} {s' : St}
    (hh : hear x (F, rs, 0) = some (h, s')) (hz : Sized F) : numsOf h = numsPlan x F.next ∧ s'.1.ns = F.ns := by
  obtain ⟨sa, sb, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, pt, ha, hb, h1, h2, h3, h4, h5,
    h6, h7, h8, h9, _, h10, h11, h12, h13, h14, h15, h16⟩ := (hear_ran hh).ran
  have a0 : At (F, rs, 0) F.next := ⟨hz, rfl, [], open_zero _⟩
  obtain ⟨eP, aa⟩ := takes_at _ _ _ _ _ ha a0
  obtain ⟨eU, ab⟩ := units_at _ _ _ _ _ hb aa
  obtain ⟨e5, a1⟩ := take_at h1 ab
  obtain ⟨eI, a2⟩ := take_at h2 a1
  obtain ⟨e2, a3⟩ := take_at h3 a2
  obtain ⟨fE, eE, a4⟩ := sum_at h4 a3
  have a5 := batch_at h5 a4
  obtain ⟨eV, a6⟩ := take_at h6 a5
  obtain ⟨fM, eM, a7⟩ := sum_at h7 a6
  obtain ⟨fVD, eVD, a8⟩ := sum_at h8 a7
  have a9 := close_at h9 a8
  obtain ⟨eX, a10⟩ := take_at h10 a9
  have a11 := batch_at h11 a10
  obtain ⟨fF, eF, a12⟩ := sum_at h12 a11
  have a13 := batch_at h13 a12
  obtain ⟨fD, eD, a14⟩ := sum_at h14 a13
  have a15 := batch_at h15 a14
  obtain ⟨fH, eH, _⟩ := sum_at h16 a15
  refine ⟨?_, ?_⟩
  · unfold numsOf
    rw [eP, eU, e5, eI, e2, eV, eX, fE, eE, fM, eM, fVD, eVD, fF, eF, fD, eD, fH, eH]
    rfl
  · rw [sum_ns h16 a15, batch_ns h15, sum_ns h14 a13, batch_ns h13, sum_ns h12 a11, batch_ns h11, take_ns h10 a9,
      close_ns h9, sum_ns h8 a7, sum_ns h7 a6, take_ns h6 a5, batch_ns h5, sum_ns h4 a3, take_ns h3 a2, take_ns h2 a1,
      take_ns h1 ab, units_ns _ _ _ _ _ hb aa, takes_ns _ _ _ _ _ ha a0]

/-- **The closed parameters are made of the plan and of two numbers of the ledger in front of the
hearing**: at the ledger
G right behind the hearing, and at every later ledger G' with as many slots (the library's «Later»
keeps that number). -/
theorem closed_is_plan {K M0 X : Type} [Field K] [Fintype K] (P0 : Cb.Pv.Att.OwnPar K M0 X) {Mg : Type} (Λ : Lin P0 Mg)
    {x : Params.AttentionRounds} {F G : Fork} {rs rs' : List Fmt.RoundView} {lead : ℕ} {h : Heard}
    (hh : hear x (F, rs, 0) = some (h, G, rs', lead)) (hz : Sized F) (G' : Fork) (hn : G'.ns = G.ns) :
    closedOf P0 Λ G'.ns (numsOf h) = closedOf P0 Λ F.ns (numsPlan x F.next) := by
  obtain ⟨e1, e2⟩ := numbers_of_plan hh hz
  have e2' : G.ns = F.ns := e2
  rw [hn, e1, e2']

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.closed_is_plan
#print axioms VerifiableInference.Desc.First.Att.P.numbers_of_plan
