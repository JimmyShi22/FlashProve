-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Cut/CutWhole.lean: the stand-in for the masked sumcheck (`wholeStandIn`,
Johnson/Desc/First/Prod/Level.lean), cut into the library's flat functions. Theorems with their
proofs, each from the stand-in's yes, with the value, the ledger behind and the tape left spelled
out.

Main names:

  `stepW`, `stepR`: one turn of the stand-in's fold over its variables; one turn of
    `Fl.roundsIn`'s.
  `WholeCut`: `Fl.pscBegin`, the fold of `stepW`, `Fl.pscEnds` and `Fl.pscRow` return one after
    the other; the end values stand shown in the ledger behind `Fl.pscEnds`; the challenges handed
    back are that state's. `whole_ok`: where the stand-in returns, that holds.
  `rounds_level`: the fold of `stepW` over an order's coordinates gives `Fl.levelRounds` in that
    order.
  `rounds_bits`: the fold of `stepW` gives the fold of `stepR`, that is `Fl.roundsIn .eq2`.
  `begin_r`, `ends_r`: a sumcheck begins with no challenge; its end appends one.

Limits. One way alone: that `WholeCut` gives the stand-in's yes is not shown. `rounds_level` asks
that every member of the order is below mu and that the point has the coordinate that is read: the
caller pays. `lawfulFl` is an instance for every importer of this file. These are ties between
texts, equations on what they return: they have no error term. No routine in a context of the
verifier program's channel is named.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Cut.CutKit
import Johnson.Desc.First.Prod.Level

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3Cut
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundForm)
open First.Prod (wholeStandIn Whole)

/-- "Then" for flat functions keeps the laws of a monad. Used for `List.mapM_cons` alone. -/
instance lawfulFl : LawfulMonad Fl := LawfulMonad.mk' (m := Fl)
  (id_map := fun x => by
    funext F t
    show Fl.andThen x (fun a => Fl.ret (id a)) F t = x F t
    unfold Fl.andThen
    cases x F t with
    | none => rfl
    | some r =>
      obtain ⟨a, G, u⟩ := r
      rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x f g => by
    funext F t
    show Fl.andThen (Fl.andThen x f) g F t = Fl.andThen x (fun a => Fl.andThen (f a) g) F t
    unfold Fl.andThen
    cases x F t with
    | none => rfl
    | some r =>
      obtain ⟨a, G, u⟩ := r
      rfl)

/-! ## The shown values -/

/-- Reading shown values one after the other changes nothing, and each was there. -/
theorem mapShown_ok (s : Nat) : ∀ (l : List Nat) (F : Fork) (t : Tape) (ends : List E) (G : Fork)
    (u : Tape), (l.mapM fun i => Fl.shown (s + i)) F t = some (ends, G, u) →
    G = F ∧ u = t ∧ l.map (fun i => F.shown (s + i)) = ends.map some
  | [], F, t, ends, G, u, h => by
    rw [List.mapM_nil] at h
    obtain ⟨rfl, rfl, rfl⟩ := pureS h
    exact ⟨rfl, rfl, rfl⟩
  | i :: l, F, t, ends, G, u, h => by
    rw [List.mapM_cons] at h
    obtain ⟨v, F1, t1, h1, g1⟩ := bindS h
    obtain ⟨hv, e1, e2⟩ := shownS h1
    subst e1 e2
    obtain ⟨vs, F2, t2, h2, g2⟩ := bindS g1
    obtain ⟨e3, e4, hl⟩ := mapShown_ok s l _ _ vs F2 t2 h2
    subst e3 e4
    obtain ⟨e5, e6, e7⟩ := pureS g2
    subst e5 e6 e7
    exact ⟨rfl, rfl, by rw [List.map_cons, List.map_cons, hv, hl]⟩

/-- The same, value by value. -/
theorem shown_at {n s : Nat} {F : Fork} {ends : List E}
    (hl : (List.range n).map (fun i => F.shown (s + i)) = ends.map some) (i : Nat) (hi : i < n) :
    F.shown (s + i) = some (ends.getD i zeroE) := by
  have h1 : ((List.range n).map (fun i => F.shown (s + i)))[i]? = (ends.map some)[i]? := by rw [hl]
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_range hi] at h1
  cases he : ends[i]? with
  | none =>
    rw [he] at h1
    simp at h1
  | some v =>
    rw [he] at h1
    have h2 : some (F.shown (s + i)) = some (some v) := h1
    rw [Option.some.inj h2]
    simp [he]

/-! ## The rounds -/

/-- One turn of the stand-in's fold over its variables. -/
def stepW (p : Psc) (z : E) : Fl Psc := do
  let x ← Fl.roundIn .eq2 p z
  pure x.2

/-- One turn of the fold in `Fl.roundsIn`. -/
def stepR (form : RoundForm) (s : Array E × Psc) (z : E × Nat) : Fl (Array E × Psc) := do
  let (r, q) ← Fl.roundIn form s.2 z.1 z.2
  pure (s.1.push r, q)

theorem roundsIn_def (form : RoundForm) (p : Psc) (zs : List (E × Nat)) :
    Fl.roundsIn form p zs = zs.foldlM (stepR form) (#[], p) := rfl

theorem stepW_ok {p q : Psc} {z : E} {F G : Fork} {t u : Tape}
    (h : stepW p z F t = some (q, G, u)) :
    ∃ x, Fl.roundIn .eq2 p z 0 F t = some ((x, q), G, u) ∧ q.r = p.r.push x := by
  unfold stepW at h
  obtain ⟨⟨x, q'⟩, F1, t1, h1, h⟩ := bindS h
  obtain ⟨e1, e2, e3⟩ := pureS h
  subst e1 e2 e3
  obtain ⟨w, sent, -, -, -, -, -, -, e⟩ := Fo.Tp.roundIn_ok _ _ _ _ _ _ _ _ _ _ h1
  refine ⟨x, h1, ?_⟩
  rw [e]

/-- A sumcheck begins with no challenge. -/
theorem begin_r {C : Aff} {F G : Fork} {t u : Tape} {p : Psc}
    (h : Fl.pscBegin C F t = some (p, G, u)) : p.r = #[] := by
  obtain ⟨target, mu, eps, -, -, -, e⟩ := Fo.Tp.pscBegin_ok _ _ _ _ _ _ h
  rw [e]

/-- The end of a sumcheck appends one challenge. -/
theorem ends_r {p q : Psc} {dY n e : Nat} {F G : Fork} {t u : Tape}
    (h : Fl.pscEnds p dY n F t = some ((e, q), G, u)) : ∃ beta, q.r = p.r.push beta := by
  obtain ⟨sent, beta, v, -, -, -, -, -, -, -, -, e'⟩ := Fo.Tp.pscEnds_ok _ _ _ _ _ _ _ _ _ h
  exact ⟨beta, by rw [e']⟩

/-- **The stand-in's rounds over an order's coordinates give the flat level's rounds.** cs: the
challenges, in the order of the rounds. -/
theorem rounds_level (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (r : Array E) (p : Psc)
    (F : Fork) (t : Tape) (p1 : Psc) (F1 : Fork) (t1 : Tape),
    (∀ v ∈ order, v < mu ∧ mu - 1 - v < rho.size) →
    (order.map fun b => rho.getD (mu - 1 - b) zeroE).foldlM stepW p F t = some (p1, F1, t1) →
    ∃ cs : List E, cs.length = order.length ∧ p1.r.toList = p.r.toList ++ cs ∧
      Fl.levelRounds mu rho order r p F t =
        some (((order.zip cs).foldl (fun (r : Array E) x => r.set! (mu - 1 - x.1) x.2) r, p1),
          F1, t1)
  | [], r, p, F, t, p1, F1, t1, _, h => by
    rw [List.map_nil, List.foldlM_nil] at h
    obtain ⟨e1, e2, e3⟩ := pureS h
    subst e1 e2 e3
    exact ⟨[], rfl, by simp, rfl⟩
  | v :: order, r, p, F, t, p1, F1, t1, ho, h => by
    rw [List.map_cons, List.foldlM_cons] at h
    obtain ⟨q, F2, t2, h2, h⟩ := bindS h
    obtain ⟨x, hx, hr⟩ := stepW_ok h2
    obtain ⟨cs, hl, hc, hL⟩ := rounds_level mu rho order (r.set! (mu - 1 - v) x) q F2 t2 p1 F1 t1
      (fun w hw => ho w (List.mem_cons_of_mem _ hw)) h
    have hv := ho v (by simp)
    have e : (p.r.push x).toList ++ cs = p.r.toList ++ x :: cs := by simp
    refine ⟨x :: cs, by simp [hl], by rw [hc, hr, e], ?_⟩
    rw [Fl.levelRounds]
    refine bindM (mustM (by simp [hv.1, hv.2]) F t) ?_
    refine bindM hx ?_
    exact hL

/-- **The stand-in's rounds give the rounds of `Fl.roundsIn .eq2`.** cs: the challenges. -/
theorem rounds_bits : ∀ (zs : List E) (acc : Array E) (p : Psc) (F : Fork) (t : Tape) (p1 : Psc)
    (F1 : Fork) (t1 : Tape), zs.foldlM stepW p F t = some (p1, F1, t1) →
    ∃ cs : List E, cs.length = zs.length ∧ p1.r.toList = p.r.toList ++ cs ∧
      (zs.map fun z => (z, 0)).foldlM (stepR .eq2) (acc, p) F t =
        some (((acc.toList ++ cs).toArray, p1), F1, t1)
  | [], acc, p, F, t, p1, F1, t1, h => by
    rw [List.foldlM_nil] at h
    obtain ⟨e1, e2, e3⟩ := pureS h
    subst e1 e2 e3
    refine ⟨[], rfl, by simp, ?_⟩
    rw [List.map_nil, List.foldlM_nil, List.append_nil]
    rfl
  | z :: zs, acc, p, F, t, p1, F1, t1, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨q, F2, t2, h2, h⟩ := bindS h
    obtain ⟨x, hx, hr⟩ := stepW_ok h2
    obtain ⟨cs, hl, hc, hL⟩ := rounds_bits zs (acc.push x) q F2 t2 p1 F1 t1 h
    have e : (p.r.push x).toList ++ cs = p.r.toList ++ x :: cs := by simp
    have e' : (acc.push x).toList ++ cs = acc.toList ++ x :: cs := by simp
    refine ⟨x :: cs, by simp [hl], by rw [hc, hr, e], ?_⟩
    have hstep : stepR .eq2 (acc, p) (z, 0) F t = some ((acc.push x, q), F2, t2) := by
      unfold stepR
      exact bindM hx rfl
    rw [List.map_cons, List.foldlM_cons]
    refine bindM hstep ?_
    rw [hL, e']

/-! ## The whole -/

/-- **A masked sumcheck that makes its row at once, as a course of the flat functions**: from the
ledger F and the tape t, `Fl.pscBegin`, the fold of `stepW` over the coordinates zs, `Fl.pscEnds`
and `Fl.pscRow` return one after the other and leave G and u; the n end values stand shown in the
ledger behind `Fl.pscEnds`; w holds the first end slot, the row, and the challenges of the state
behind `Fl.pscEnds`. The lemmas on the tie's steps, on a level and on the bits are stated FROM
this, so that another text of the masked sumcheck can be tied to the flat pieces by showing this
of it. -/
def WholeCut (C : Aff) (zs : List E) (dY n : Nat) (e : List E → E) (F : Fork) (t : Tape) (w : Whole)
    (G : Fork) (u : Tape) : Prop :=
    ∃ (p0 : Psc) (F0 : Fork) (t0 : Tape) (p1 : Psc) (F1 : Fork) (t1 : Tape) (p2 : Psc) (F2 : Fork)
      (t2 : Tape) (ends : List E) (p3 : Psc),
      Fl.pscBegin C F t = some (p0, F0, t0) ∧
      zs.foldlM stepW p0 F0 t0 = some (p1, F1, t1) ∧
      Fl.pscEnds p1 dY n F1 t1 = some ((w.sEnd, p2), F2, t2) ∧
      (∀ i, i < n → F2.shown (w.sEnd + i) = some (ends.getD i zeroE)) ∧
      Fl.pscRow p2 (e ends) {} F2 t2 = some ((w.row, p3), G, u) ∧
      w.challenges = p2.r.toList

/-- **The stand-in's yes, cut.** -/
theorem whole_ok {C : Aff} {zs : List E} {dY n : Nat} {e : List E → E} {F G : Fork} {t u : Tape}
    {w : Whole} (h : wholeStandIn C zs dY n e F t = some (w, G, u)) :
    WholeCut C zs dY n e F t w G u := by
  unfold wholeStandIn at h
  obtain ⟨p0, F0, t0, h0, h⟩ := bindS h
  obtain ⟨p1, F1, t1, h1, h⟩ := bindS h
  obtain ⟨⟨sEnd, p2⟩, F2, t2, h2, h⟩ := bindS h
  obtain ⟨ends, F3, t3, h3, h⟩ := bindS h
  obtain ⟨⟨row, p3⟩, F4, t4, h4, h⟩ := bindS h
  obtain ⟨e1, e2, e3⟩ := pureS h
  subst e1 e2 e3
  obtain ⟨e4, e5, hs⟩ := mapShown_ok sEnd _ _ _ _ _ _ h3
  subst e4 e5
  exact ⟨p0, F0, t0, p1, F1, t1, p2, _, _, ends, p3, h0, h1, h2, shown_at hs, h4, rfl⟩

end VerifiableInference.Desc.K3Cut
