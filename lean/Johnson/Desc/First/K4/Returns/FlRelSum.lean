-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/FlRelSum.lean: TWO RUNS OF ONE TEXT (FlRel,
Johnson/Desc/First/K4/Returns/FlRel.lean): THE STEPS ON THE TAPE, AND HIDDEN VALUES ON THE LEDGER's
SHAPE. General laws: nothing is evaluated.

  alike_cons, alike_mk, recv_rel, recvLoop_rel, closeOne_rel, closeN_rel, closeRows_rel   the tape's
                  own functions at two tapes of one shape.
  SameSize        two arrays of one size.
  FlRel.read, readSum, answer, point, batch, empty   the calls on the rounds.
  gotRun, hide_sh, hideSteps_sh, **hideRun_sh**   FROM A RETURN ALONE: the ledger's shape behind a
                  run of hidden values is the shape in front with these slots marked.
  FlRel.hideRun   values of one number under the same slots.

Limits. The weak form of the frame. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.FlRel
import OnBytes.Desc.First.P1.PscSound
import OnBytes.Desc.First.P1.BatchPoint

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc Tsc Level)
open VerifiableInference.Desc.First.Shape

/-! ## The steps on the tape -/

theorem alike_cons {r r' : FlatRound} {t t' : Tape} (h : TapeAlike (r :: t) (r' :: t')) :
    roundSh r = roundSh r' ∧ TapeAlike t t' := by
  unfold TapeAlike at h
  rw [List.map_cons, List.map_cons] at h
  exact ⟨(List.cons.inj h).1, (List.cons.inj h).2⟩

theorem alike_mk {r r' : FlatRound} {t t' : Tape} (h1 : roundSh r = roundSh r')
    (h2 : TapeAlike t t') : TapeAlike (r :: t) (r' :: t') := by
  unfold TapeAlike at h2 ⊢
  rw [List.map_cons, List.map_cons, h1, h2]

/-- The next element of the open message. -/
theorem recv_rel {t t' u u' : Tape} {x x' : E} (h : TapeAlike t t') (h1 : recv t = some (x, u))
    (h2 : recv t' = some (x', u')) : TapeAlike u u' := by
  cases t with
  | nil => cases h1
  | cons r t =>
    cases t' with
    | nil => cases h2
    | cons r' t' =>
      obtain ⟨a, b⟩ := alike_cons h
      obtain ⟨nm, z, w, s, d⟩ := r
      obtain ⟨nm', z', w', s', d'⟩ := r'
      cases s with
      | nil => cases h1
      | cons y s =>
        cases s' with
        | nil => cases h2
        | cons y' s' =>
          obtain rfl : (⟨nm, z, w, s, d⟩ : FlatRound) :: t = u :=
            congrArg (·.2) (Option.some.inj h1)
          obtain rfl : (⟨nm', z', w', s', d'⟩ : FlatRound) :: t' = u' :=
            congrArg (·.2) (Option.some.inj h2)
          refine alike_mk ?_ b
          simp only [roundSh, List.length_cons, Prod.mk.injEq] at a ⊢
          exact ⟨a.1, a.2.1, a.2.2.1, by omega, a.2.2.2.2⟩

theorem recvLoop_rel : ∀ (n : Nat) (a a' : Array E) (t t' u u' : Tape) (v v' : Array E),
    a.size = a'.size → TapeAlike t t' → recvLoop n a t = some (v, u) →
    recvLoop n a' t' = some (v', u') → v.size = v'.size ∧ TapeAlike u u'
  | 0, a, a', t, t', u, u', v, v', ha, ht, h1, h2 => by
    obtain ⟨rfl, rfl⟩ : a = v ∧ t = u :=
      ⟨congrArg (·.1) (Option.some.inj h1), congrArg (·.2) (Option.some.inj h1)⟩
    obtain ⟨rfl, rfl⟩ : a' = v' ∧ t' = u' :=
      ⟨congrArg (·.1) (Option.some.inj h2), congrArg (·.2) (Option.some.inj h2)⟩
    exact ⟨ha, ht⟩
  | n + 1, a, a', t, t', u, u', v, v', ha, ht, h1, h2 => by
    unfold recvLoop at h1 h2
    cases e1 : recv t with
    | none =>
      rw [e1] at h1
      cases h1
    | some q =>
      cases e2 : recv t' with
      | none =>
        rw [e2] at h2
        cases h2
      | some q' =>
        obtain ⟨x, w⟩ := q
        obtain ⟨x', w'⟩ := q'
        rw [e1] at h1
        rw [e2] at h2
        exact recvLoop_rel n _ _ w w' u u' v v' (by rw [Array.size_push, Array.size_push, ha])
          (recv_rel ht e1 e2) h1 h2

/-- Two arrays of one size. -/
def SameSize (a b : Array E) : Prop := a.size = b.size

theorem FlRel.read (n : Nat) : FlRel SameSize (Fl.read n) (Fl.read n) :=
  FlRel.onTape fun t t' a u b u' ht h1 h2 =>
    recvLoop_rel n _ _ t t' u u' a b rfl ht h1 h2

theorem FlRel.readSum : FlRel (fun _ _ => True) Fl.readSum Fl.readSum :=
  FlRel.onTape fun _ _ _ _ _ _ ht h1 h2 => ⟨trivial, recv_rel ht h1 h2⟩

/-- A step that closes the first round and hands on the rest. -/
theorem closeOne_rel {name : String} {nz : Nat} {t t' u u' : Tape} {x x' : E}
    (h : TapeAlike t t') (h1 : closeOne name nz t = some (x, u))
    (h2 : closeOne name nz t' = some (x', u')) : TapeAlike u u' := by
  unfold closeOne at h1 h2
  split at h1
  · split at h2
    · split at h1
      · split at h2
        · obtain rfl := congrArg (·.2) (Option.some.inj h1)
          obtain rfl := congrArg (·.2) (Option.some.inj h2)
          exact (alike_cons h).2
        · cases h2
      · cases h1
    · cases h2
  · cases h1

theorem closeN_rel {name : String} {nz n : Nat} {t t' u u' : Tape} {d d' : List E}
    (h : TapeAlike t t') (h1 : closeN name nz n t = some (d, u))
    (h2 : closeN name nz n t' = some (d', u')) : d.length = d'.length ∧ TapeAlike u u' := by
  unfold closeN at h1 h2
  split at h1
  · split at h2
    · split at h1
      next c1 =>
        split at h2
        next c2 =>
          simp only [Bool.and_eq_true, beq_iff_eq] at c1 c2
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h1)
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h2)
          exact ⟨by rw [c1.2, c2.2], (alike_cons h).2⟩
        next => cases h2
      next => cases h1
    · cases h2
  · cases h1

theorem closeRows_rel {rows : Nat} {t t' u u' : Tape} {x x' : E}
    (h : TapeAlike t t') (h1 : closeRows rows t = some (x, u))
    (h2 : closeRows rows t' = some (x', u')) : TapeAlike u u' := by
  unfold closeRows at h1 h2
  split at h1
  · split at h2
    · split at h1
      · split at h2
        · obtain rfl := congrArg (·.2) (Option.some.inj h1)
          obtain rfl := congrArg (·.2) (Option.some.inj h2)
          exact (alike_cons h).2
        · cases h2
      · cases h1
    · cases h2
  · cases h1

theorem FlRel.answer (r : Model.RoundName) : FlRel (fun _ _ => True) (Fl.answer r) (Fl.answer r) :=
  FlRel.onTape fun _ _ _ _ _ _ ht h1 h2 => ⟨trivial, closeOne_rel ht h1 h2⟩

theorem FlRel.point (r : Model.RoundName) (n : Nat) :
    FlRel SameSize (Fl.point r n) (Fl.point r n) :=
  FlRel.onTape fun t t' a u b u' ht h1 h2 => by
    obtain ⟨x, hx, e1⟩ := Option.map_eq_some_iff.1 h1
    obtain ⟨y, hy, e2⟩ := Option.map_eq_some_iff.1 h2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e2
    obtain ⟨r1, r2⟩ := closeN_rel (d := x.1) (u := x.2) (d' := y.1) (u' := y.2) ht hx hy
    exact ⟨by show x.1.toArray.size = y.1.toArray.size; simpa using r1, r2⟩

theorem FlRel.batch (rows : Nat) : FlRel SameSize (Fl.batch rows) (Fl.batch rows) :=
  FlRel.onTape fun t t' a u b u' ht h1 h2 => by
    unfold Fl.batchOn at h1 h2
    split at h1
    · rename_i hr
      rw [if_pos hr] at h2
      obtain ⟨x, hx, e1⟩ := Option.map_eq_some_iff.1 h1
      obtain ⟨y, hy, e2⟩ := Option.map_eq_some_iff.1 h2
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e2
      exact ⟨by
        show (Model.powers x.1 rows).size = (Model.powers y.1 rows).size
        rw [OnBytes.Desc.First.P1.powers_size, OnBytes.Desc.First.P1.powers_size],
        closeRows_rel (x := x.1) (u := x.2) (x' := y.1) (u' := y.2) ht hx hy⟩
    · cases h1

theorem FlRel.empty (r : Model.RoundName) : FlRel (fun _ _ => True) (Fl.empty r) (Fl.empty r) :=
  FlRel.onTape fun t t' a u b u' ht h1 h2 => by
    obtain ⟨x, hx, e1⟩ := Option.map_eq_some_iff.1 h1
    obtain ⟨y, hy, e2⟩ := Option.map_eq_some_iff.1 h2
    obtain rfl := (Prod.mk.inj e1).2
    obtain rfl := (Prod.mk.inj e2).2
    exact ⟨trivial, (closeN_rel (d := x.1) (u := x.2) (d' := y.1) (u' := y.2) ht hx hy).2⟩

/-! ## Hidden values, on the ledger's shape -/

/-- The marks with n slots from j on marked, one by one. -/
def gotRun : List Bool → Nat → Nat → List Bool
  | g, _, 0 => g
  | g, j, n + 1 => gotRun (g.set j true) (j + 1) n

theorem hide_sh {F G : Fork} {j : Nat} {y f : E} (h : F.hide j y f = some G) :
    ledSh G = (ledSh F).setGot ((ledSh F).got.set j true) := by
  unfold Fork.hide at h
  split at h
  · obtain rfl := Option.some.inj h
    show LedSh.mk F.ns (F.vp.set! j y).size (F.mf.set! j f).size (F.gotF.set! j true).toList _ _ _
      _ _ _ _ _ _ = _
    simp [LedSh.setGot, ledSh, LedSh.mk, LedSh.ns, LedSh.shown, LedSh.factors, LedSh.got,
      LedSh.owed, LedSh.planClaims, LedSh.trees, LedSh.next, LedSh.coefs, LedSh.claims,
      LedSh.drawn, LedSh.handed, LedSh.shut]
  · cases h

theorem hideSteps_sh (f : E) : ∀ (l : List E) (j : Nat) (F : Fork) (y : Nat × Fork),
    l.foldlM (Fork.hideStep f) (j, F) = some y →
      ledSh y.2 = (ledSh F).setGot (gotRun (ledSh F).got j l.length)
  | [], j, F, y, h => by
    obtain rfl : (j, F) = y := by simpa using h
    rfl
  | e :: l, j, F, y, h => by
    rw [List.foldlM_cons] at h
    cases hs : Fork.hideStep f (j, F) e with
    | none =>
      rw [hs] at h
      cases h
    | some z =>
      rw [hs] at h
      have h1 : (F.hide j e f).map (fun H => (j + 1, H)) = some z := hs
      cases hh : F.hide j e f with
      | none =>
        rw [hh] at h1
        cases h1
      | some H =>
        rw [hh] at h1
        obtain rfl := Option.some.inj h1
        rw [hideSteps_sh f l (j + 1) H y h, hide_sh hh]
        rfl

theorem hideRun_sh {F G : Fork} {j : Nat} {v : Array E} {f : E}
    (h : F.hideRun j v f = some G) :
    ledSh G = (ledSh F).setGot (gotRun (ledSh F).got j v.size) := by
  unfold Fork.hideRun at h
  rw [← Array.foldlM_toList] at h
  cases hs : v.toList.foldlM (Fork.hideStep f) (j, F) with
  | none =>
    rw [hs] at h
    cases h
  | some x =>
    rw [hs] at h
    obtain rfl := Option.some.inj h
    rw [hideSteps_sh f v.toList j F x hs, Array.length_toList]

/-- Values of one number are laid under the same slots. -/
theorem FlRel.hideRun {j : Nat} {v v' : Array E} (hv : SameSize v v') (f f' : E) :
    FlRel (fun _ _ => True) (Fl.change (·.hideRun j v f)) (Fl.change (·.hideRun j v' f')) :=
  FlRel.change fun F F' G G' hF h1 h2 => by
    rw [hideRun_sh h1, hideRun_sh h2, hF, hv]

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.alike_cons
#print axioms OnBytes.Desc.First.K4.Rt.alike_mk
#print axioms OnBytes.Desc.First.K4.Rt.recv_rel
#print axioms OnBytes.Desc.First.K4.Rt.recvLoop_rel
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.read
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.readSum
#print axioms OnBytes.Desc.First.K4.Rt.closeOne_rel
#print axioms OnBytes.Desc.First.K4.Rt.closeN_rel
#print axioms OnBytes.Desc.First.K4.Rt.closeRows_rel
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.answer
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.point
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.batch
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.empty
#print axioms OnBytes.Desc.First.K4.Rt.hide_sh
#print axioms OnBytes.Desc.First.K4.Rt.hideSteps_sh
#print axioms OnBytes.Desc.First.K4.Rt.hideRun_sh
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.hideRun
#print axioms OnBytes.Desc.First.K4.Rt.SameSize
#print axioms OnBytes.Desc.First.K4.Rt.gotRun
