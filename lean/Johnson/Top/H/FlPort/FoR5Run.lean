-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoR5Run.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoR5Run.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  roundsGo_ok, roundsIn_ok, leavesBits_ok
and, because the library keeps them private to that file, copies of:
  took_took, took5, push_append, after_nil, after_cons, weight_eq, publicPart_const
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  FitsA, after, bits2, claimAfter_cons, evVars, leaves, lsOf, sBit, slotsOf, took, zdOf
The comments on the declarations are the library's, under the same swap: where they say "run" or
"view", read: on a tape.

Limits. What is proved here is proved of the flat functions alone, and a flat function tests less of
the plan than the program's routine (the paragraph "Not claimed" in the head of
OnBytes/K/Kc/Flat.lean). Nothing is said where a function refuses. A tie: it has no error term. If
the source file turns, this copy does not follow by itself. In the list of names a use by dot
notation on a hypothesis is not seen, and a short name may stand once too often. That no routine
in a context is reached from a statement or a proof here is meant, and is not shown in this
library.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoR5Run
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie

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
    ∀ (zs : List (E × ℕ)) (acc : Array E) (p : Psc) (F G : Fork) (c c' : Tape) (r : Array E)
      (p' : Psc),
      (zs.foldlM
        (fun (s : Array E × Psc) (z : E × ℕ) => do
          let (r, q) ← Fl.roundIn form s.2 z.1 z.2
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
    (F G : Fork) (c c' : Tape) (r : Array E) (p' : Psc)
    (h : Fl.roundsIn form p zs F c = .ok (((r, p'), G), c')) :
    ∃ rs : List (Array E × E), FitsA (zdOf form zs) rs ∧ Evs (evVars (zdOf form zs) rs) c c' ∧
      G = took F (slotsOf (zdOf form zs)) ∧ r = (rs.map (·.2)).toArray ∧
      p' = after p (zdOf form zs) rs := by
  obtain ⟨rs, a1, a2, a3, a4, a5⟩ := roundsGo_ok form hf zs #[] p F G c c' r p' h
  exact ⟨rs, a1, a2, a3, by rw [a4]; simp, a5⟩

namespace R5D
variable (D : R5D) (m d : ℕ) (rho : Array E)

end R5D

private theorem publicPart_const (F : Fork) (x : E) : F.publicPart (Aff.ofConst x) = some x := rfl

/-- The eight lines, each as a run that returns. -/
theorem leavesBits_ok (m d : ℕ) (rho : Array E) (C : Aff)
    (F F1 F2 F3 F4 F5 F6 F7 F8 : Fork) (c c1 c2 c3 c4 c5 c6 c7 c8 : Tape)
    (lv0 lv b0 b1 b2 b3 : Psc) (zb0 zb1 pt : Array E) (sBit : ℕ) (vBit : E) (row : Aff)
    (h1 : Fl.pscBegin C F c = .ok ((lv0, F1), c1))
    (h2 : Fl.roundsIn .eq lv0
      ((List.range m).map fun j => (rho.getD j zeroE, if j < d then 2 else 1)) F1 c1 =
        .ok (((zb0, lv), F2), c2))
    (h3 : Fl.point .zero m F2 c2 = .ok ((pt, F3), c3))
    (h4 : Fl.pscBegin (Aff.ofConst zeroE) F3 c3 = .ok ((b0, F4), c4))
    (h5 : Fl.roundsIn .eq2 b0 (pt.reverse.toList.map fun z => (z, 0)) F4 c4 =
      .ok (((zb1, b1), F5), c5))
    (h6 : Fl.pscEnds b1 2 1 F5 c5 = .ok (((sBit, b2), F6), c6))
    (h7 : Fl.shown sBit F6 c6 = .ok ((vBit, F7), c7))
    (h8 : Fl.pscRow b2 (subE (mulE vBit vBit) vBit) {} F7 c7 = .ok (((row, b3), F8), c8)) :
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


end Fo.Tp
