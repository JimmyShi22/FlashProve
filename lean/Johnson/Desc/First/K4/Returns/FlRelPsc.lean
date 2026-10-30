-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/FlRelPsc.lean: TWO RUNS OF ONE TEXT (FlRel,
Johnson/Desc/First/K4/Returns/FlRel.lean): THE MASKED SUMCHECK's STEPS. General laws: nothing is
evaluated.

  walkLen, **hidingWalk_len**, zip_degrees, **walk_sh**   the number of a hiding polynomial's
                  coefficients hangs on the variables' degrees alone: at every sumcheck, open or
                  not, whatever the degrees.
  PscAlike        two sumchecks of one shape (pscSh, Johnson/Desc/First/Shape/Parts.lean).
  rowForm_rel     a sumcheck's row at two sumchecks of one shape.
  FlRel.claimsIn, shown, publicPart, pscBeginAt, pscBegin, pscRound, roundIn, pscEnds, pscRow, with
  pscAlike_step, weightT_d, pscAlike_ended, pscAlike_rowMade   the steps.

Limits. The weak form of the frame. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.FlRelSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc Tsc Level)
open OnBytes.Desc.First.P1 (powers_eq powersFrom_length)
open VerifiableInference.Desc.First.Shape

/-! ## The number of a hiding polynomial's coefficients hangs on the degrees alone -/

/-- The number of coefficients, of the variables' numbers of coefficients of a round. -/
def walkLen : List Nat → Nat
  | [] => 0
  | [d] => d
  | d :: e :: rest => (d - 1) + walkLen (e :: rest)

theorem hidingWalk_len : ∀ vr : List (OnBytes.Psc.Weight × E),
    (OnBytes.Psc.hidingWalk vr).1.length = walkLen (vr.map (·.1.d))
  | [] => rfl
  | [(w, g)] => by
    show (OnBytes.Psc.powers oneE g w.d).length = w.d
    rw [powers_eq, powersFrom_length]
  | (w, g) :: y :: rest => by
    have ih := hidingWalk_len (y :: rest)
    show (OnBytes.Psc.powers (mulE (OnBytes.Psc.hidingWalk (y :: rest)).2 g) g (w.d - 1) ++
      (OnBytes.Psc.hidingWalk (y :: rest)).1).length = (w.d - 1) + walkLen ((y :: rest).map (·.1.d))
    rw [List.length_append, powers_eq, powersFrom_length, ih]

theorem zip_degrees {α β : Type} (f : α → Nat) : ∀ (l : List α) (m : List β),
    (l.zip m).map (fun x => f x.1) = (l.map f).take m.length
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l, b :: m => by
    rw [List.zip_cons_cons, List.map_cons, List.map_cons, List.length_cons, List.take_succ_cons,
      zip_degrees f l m]

/-- Two sumchecks of one shape. -/
def PscAlike (p p' : Psc) : Prop := pscSh p = pscSh p'

theorem walk_sh {p p' : Psc} (h : PscAlike p p') : p.walk.1.length = p'.walk.1.length := by
  have h1 : p.vars.toList.map (·.d) = p'.vars.toList.map (·.d) := congrArg PscSh.degrees h
  have h2 : p.r.size = p'.r.size := congrArg PscSh.challenges h
  have z1 := zip_degrees (fun w : OnBytes.Psc.Weight => w.d) p.vars.toList p.r.toList
  have z2 := zip_degrees (fun w : OnBytes.Psc.Weight => w.d) p'.vars.toList p'.r.toList
  unfold Psc.walk
  rw [zipT_eq, zipT_eq, hidingWalk_len, hidingWalk_len, z1, z2, h1, Array.length_toList,
    Array.length_toList, h2]

/-- A sumcheck's row at two sumchecks of one shape and two kept forms of one shape. -/
theorem rowForm_rel {p p' : Psc} (h : PscAlike p p') (S0 S0' : E) {kept kept' : Aff}
    (hk : SameSh kept kept') : SameSh (p.rowForm S0 kept) (p'.rowForm S0' kept') := by
  unfold SameSh
  have h1 : p.first = p'.first := congrArg PscSh.first h
  have h2 : affSh p.start = affSh p'.start := congrArg PscSh.start h
  rw [affSh_rowForm, affSh_rowForm, h1, h2, walk_sh h, hk]

/-! ## The steps of the masked sumcheck -/

theorem FlRel.claimsIn (n : Nat) : FlRel Eq (Fl.claimsIn n) (Fl.claimsIn n) := by
  unfold Fl.claimsIn
  refine FlRel.bind (FlRel.read n) fun v v' hv => ?_
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  refine FlRel.bind (FlRel.takeSlots n) fun j j' hj => ?_
  subst hj
  exact FlRel.bind (FlRel.hideRun hv _ _) fun _ _ _ => FlRel.pure rfl

theorem FlRel.shown (j j' : Nat) : FlRel (fun _ _ => True) (Fl.shown j) (Fl.shown j') :=
  FlRel.ask _ _

theorem FlRel.publicPart (a a' : Aff) :
    FlRel (fun _ _ => True) (Fl.publicPart a) (Fl.publicPart a') := FlRel.ask _ _

theorem FlRel.pscBeginAt (T T' : E) : FlRel PscAlike (Fl.pscBeginAt T) (Fl.pscBeginAt T') := by
  unfold Fl.pscBeginAt
  refine FlRel.bind (FlRel.takeSlots 1) fun f f' hf => ?_
  subst hf
  refine FlRel.bind FlRel.readSum fun _ _ _ => ?_
  exact FlRel.bind (FlRel.answer _) fun _ _ _ => FlRel.pure rfl

theorem FlRel.pscBegin {C C' : Aff} (h : SameSh C C') :
    FlRel PscAlike (Fl.pscBegin C) (Fl.pscBegin C') := by
  unfold Fl.pscBegin
  refine FlRel.bind (FlRel.publicPart C C') fun T T' _ => ?_
  refine FlRel.bind (FlRel.pscBeginAt T T') fun p p' hp => FlRel.pure ?_
  show PscSh.mk p.rowMade true (p.vars.toList.map (·.d)) p.r.size p.first (affSh C) p.ended =
    PscSh.mk p'.rowMade true (p'.vars.toList.map (·.d)) p'.r.size p'.first (affSh C') p'.ended
  have a1 : p.rowMade = p'.rowMade := congrArg PscSh.rowMade hp
  have a2 : p.vars.toList.map (·.d) = p'.vars.toList.map (·.d) := congrArg PscSh.degrees hp
  have a3 : p.r.size = p'.r.size := congrArg PscSh.challenges hp
  have a4 : p.first = p'.first := congrArg PscSh.first hp
  have a5 : p.ended = p'.ended := congrArg PscSh.ended hp
  rw [a1, a2, a3, a4, a5, h]

/-- One more variable and challenge. -/
theorem pscAlike_step {p p' : Psc} (h : PscAlike p p') {w w' : OnBytes.Psc.Weight}
    (hd : w.d = w'.d) (c c' r r' : E) :
    PscAlike { p with claim := c, vars := p.vars.push w, r := p.r.push r }
      { p' with claim := c', vars := p'.vars.push w', r := p'.r.push r' } := by
  show PscSh.mk p.rowMade p.started ((p.vars.push w).toList.map (·.d)) (p.r.push r).size p.first
      (affSh p.start) p.ended =
    PscSh.mk p'.rowMade p'.started ((p'.vars.push w').toList.map (·.d)) (p'.r.push r').size
      p'.first (affSh p'.start) p'.ended
  have a1 : p.rowMade = p'.rowMade := congrArg PscSh.rowMade h
  have a0 : p.started = p'.started := congrArg PscSh.started h
  have a2 : p.vars.toList.map (·.d) = p'.vars.toList.map (·.d) := congrArg PscSh.degrees h
  have a3 : p.r.size = p'.r.size := congrArg PscSh.challenges h
  have a4 : p.first = p'.first := congrArg PscSh.first h
  have a5 : p.ended = p'.ended := congrArg PscSh.ended h
  have a6 : affSh p.start = affSh p'.start := congrArg PscSh.start h
  rw [Array.toList_push, Array.toList_push, List.map_append, List.map_append, Array.size_push,
    Array.size_push, a0, a1, a2, a3, a4, a5, a6]
  show PscSh.mk _ _ (_ ++ [w.d]) _ _ _ _ = PscSh.mk _ _ (_ ++ [w'.d]) _ _ _ _
  rw [hd]

theorem FlRel.pscRound {p p' : Psc} (h : PscAlike p p') {w w' : OnBytes.Psc.Weight}
    (hd : w.d = w'.d) {draw : Tape → Option (E × Tape)}
    (hdraw : ∀ t t' a u b u', TapeAlike t t' → draw t = some (a, u) → draw t' = some (b, u') →
      TapeAlike u u') :
    FlRel (fun x x' : E × Psc => PscAlike x.2 x'.2) (Fl.pscRound p w draw)
      (Fl.pscRound p' w' draw) := by
  unfold Fl.pscRound
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  rw [hd]
  refine FlRel.bind (FlRel.read _) fun s s' _ => ?_
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  refine FlRel.bind (S := fun _ _ => True)
    (FlRel.onTape fun t t' a u b u' ht h1 h2 => ⟨trivial, hdraw t t' a u b u' ht h1 h2⟩)
    fun r r' _ => ?_
  exact FlRel.bind (FlRel.takeSlots _) fun _ _ _ => FlRel.pure (pscAlike_step h hd _ _ _ _)

theorem weightT_d {form : OnBytes.Model.RoundForm} {z : E} {degree : Nat}
    {w : OnBytes.Psc.Weight} (h : weightT form z degree = some w) :
    w.d = valuesT form degree + 1 := by
  unfold weightT at h
  split at h
  · obtain rfl := Option.some.inj h
    split <;> rfl
  · cases h

theorem FlRel.roundIn (form : OnBytes.Model.RoundForm) {p p' : Psc} (h : PscAlike p p') (z z' : E)
    (degree : Nat) :
    FlRel (fun x x' : E × Psc => PscAlike x.2 x'.2) (Fl.roundIn form p z degree)
      (Fl.roundIn form p' z' degree) := by
  unfold Fl.roundIn
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  refine FlRel.bind (S := fun w w' : OnBytes.Psc.Weight => w.d = w'.d)
    (FlRel.need fun a b ha hb => by rw [weightT_d ha, weightT_d hb]) fun w w' hd => ?_
  exact FlRel.pscRound h hd fun _ _ _ _ _ _ ht h1 h2 => closeOne_rel ht h1 h2

theorem pscAlike_ended {p p' : Psc} (h : PscAlike p p') :
    PscAlike { p with ended := true } { p' with ended := true } := by
  show PscSh.mk p.rowMade p.started (p.vars.toList.map (·.d)) p.r.size p.first (affSh p.start)
      true =
    PscSh.mk p'.rowMade p'.started (p'.vars.toList.map (·.d)) p'.r.size p'.first (affSh p'.start)
      true
  have a1 : p.rowMade = p'.rowMade := congrArg PscSh.rowMade h
  have a0 : p.started = p'.started := congrArg PscSh.started h
  have a2 : p.vars.toList.map (·.d) = p'.vars.toList.map (·.d) := congrArg PscSh.degrees h
  have a3 : p.r.size = p'.r.size := congrArg PscSh.challenges h
  have a4 : p.first = p'.first := congrArg PscSh.first h
  have a6 : affSh p.start = affSh p'.start := congrArg PscSh.start h
  rw [a0, a1, a2, a3, a4, a6]

theorem FlRel.pscEnds {p p' : Psc} (h : PscAlike p p') (dY n : Nat) :
    FlRel (fun x x' : Nat × Psc => x.1 = x'.1 ∧ PscAlike x.2 x'.2) (Fl.pscEnds p dY n)
      (Fl.pscEnds p' dY n) := by
  unfold Fl.pscEnds
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  refine FlRel.bind (FlRel.pscRound h rfl fun _ _ _ _ _ _ ht h1 h2 => closeOne_rel ht h1 h2)
    fun x x' hx => ?_
  obtain ⟨beta, q⟩ := x
  obtain ⟨beta', q'⟩ := x'
  refine FlRel.bind (FlRel.read n) fun v v' hv => ?_
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  refine FlRel.bind (FlRel.empty _) fun _ _ _ => ?_
  refine FlRel.bind (FlRel.takeSlots n) fun e e' he => ?_
  subst he
  exact FlRel.bind (FlRel.hideRun hv _ _) fun _ _ _ => FlRel.pure ⟨rfl, pscAlike_ended hx⟩

theorem pscAlike_rowMade {p p' : Psc} (h : PscAlike p p') :
    PscAlike { p with rowMade := true } { p' with rowMade := true } := by
  show PscSh.mk true p.started (p.vars.toList.map (·.d)) p.r.size p.first (affSh p.start) p.ended =
    PscSh.mk true p'.started (p'.vars.toList.map (·.d)) p'.r.size p'.first (affSh p'.start)
      p'.ended
  have a0 : p.started = p'.started := congrArg PscSh.started h
  have a2 : p.vars.toList.map (·.d) = p'.vars.toList.map (·.d) := congrArg PscSh.degrees h
  have a3 : p.r.size = p'.r.size := congrArg PscSh.challenges h
  have a4 : p.first = p'.first := congrArg PscSh.first h
  have a5 : p.ended = p'.ended := congrArg PscSh.ended h
  have a6 : affSh p.start = affSh p'.start := congrArg PscSh.start h
  rw [a0, a2, a3, a4, a5, a6]

theorem FlRel.pscRow {p p' : Psc} (h : PscAlike p p') (S0 S0' : E) {kept kept' : Aff}
    (hk : SameSh kept kept') :
    FlRel (fun x x' : Aff × Psc => SameSh x.1 x'.1 ∧ PscAlike x.2 x'.2) (Fl.pscRow p S0 kept)
      (Fl.pscRow p' S0' kept') := by
  unfold Fl.pscRow
  refine FlRel.bind (FlRel.must _ _) fun _ _ _ => ?_
  have h1 : p.first = p'.first := congrArg PscSh.first h
  have hh : FlRel (fun _ _ => True)
      (Fl.change (·.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE)))
      (Fl.change (·.hideRun p'.first (Array.replicate p'.walk.1.length zeroE)
        (subE zeroE oneE))) := by
    rw [h1]
    exact FlRel.hideRun (by
      show (Array.replicate _ zeroE).size = (Array.replicate _ zeroE).size
      rw [Array.size_replicate, Array.size_replicate, walk_sh h]) _ _
  refine FlRel.bind hh fun _ _ _ => ?_
  exact FlRel.pure ⟨rowForm_rel h S0 S0' hk, pscAlike_rowMade h⟩

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.hidingWalk_len
#print axioms OnBytes.Desc.First.K4.Rt.zip_degrees
#print axioms OnBytes.Desc.First.K4.Rt.walk_sh
#print axioms OnBytes.Desc.First.K4.Rt.rowForm_rel
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.claimsIn
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.shown
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.publicPart
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.pscBeginAt
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.pscBegin
#print axioms OnBytes.Desc.First.K4.Rt.pscAlike_step
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.pscRound
#print axioms OnBytes.Desc.First.K4.Rt.weightT_d
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.roundIn
#print axioms OnBytes.Desc.First.K4.Rt.pscAlike_ended
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.pscEnds
#print axioms OnBytes.Desc.First.K4.Rt.pscAlike_rowMade
#print axioms OnBytes.Desc.First.K4.Rt.FlRel.pscRow
#print axioms OnBytes.Desc.First.K4.Rt.walkLen
#print axioms OnBytes.Desc.First.K4.Rt.PscAlike
