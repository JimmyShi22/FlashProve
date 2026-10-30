-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Forward.lean: when the small steps of a flat function (Fl,
OnBytes/K/Kc/Flat.lean) and the routines of the masked sumcheck RETURN: on a tape whose next rounds
have the right shape, from a ledger with free slots ahead.

Main names:
  bind_eq, must_ok: "do" and a test, forward.
  head_of: a tape whose first shape is known.
  read_ok, answer_ok, point_ok: the calls on the tape.
  hide_some, hideRun_some: values are put under free slots.
  public_some: the public part of a form whose slots are filled.
  begin_ok, pscRound_ok: the sumcheck's first call, and one round of it.

Limits. Only that they return; what they return is in Kit.lean.

-/
import Johnson.Desc.First.Look.KeyLaw.Read
import OnBytes.Tie.Pv.Psc.PscHeld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundName RoundForm)
open OnBytes.PscRun (took Later Sized Filled)

variable {α β : Type}

theorem bind_eq {x : Fl α} {f : α → Fl β} {F G : Fork} {t u : Tape} {a : α}
    (h : x F t = some (a, G, u)) : (x >>= f) F t = f a G u := by
  show Fl.andThen x f F t = _
  unfold Fl.andThen
  rw [h]

theorem must_ok {b : Bool} (h : b = true) (F : Fork) (t : Tape) :
    Fl.must b F t = some ((), F, t) := by
  subst h
  rfl

/-- A tape whose first shape is known, with a name. -/
theorem head_of {t : Tape} {x : Shape} {L : List Shape} (h : t.map shapeOf = x :: L)
    (hx : x.1 ≠ "") : ∃ w sent drawn u, t = ⟨some x.1, x.2.2.2, w, sent, drawn⟩ :: u ∧
      sent.length = x.2.1 ∧ drawn.length = x.2.2.1 ∧ u.map shapeOf = L := by
  cases t with
  | nil => cases h
  | cons r u =>
    rw [List.map_cons] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    obtain ⟨nm, z, w, s, d⟩ := r
    subst h1
    cases nm with
    | none => exact absurd rfl hx
    | some nm => exact ⟨w, s, d, u, rfl, rfl, rfl, h2⟩

theorem recvLoop_ok : ∀ (pre : List E) (a : Array E) (nm : Option String) (z w : Nat) (s d : List E)
    (u : Tape), ∃ b : Array E,
      recvLoop pre.length a (⟨nm, z, w, pre ++ s, d⟩ :: u) = some (b, ⟨nm, z, w, s, d⟩ :: u) ∧
      b.size = a.size + pre.length
  | [], a, nm, z, w, s, d, u => ⟨a, rfl, rfl⟩
  | x :: pre, a, nm, z, w, s, d, u => by
    obtain ⟨b, h1, h2⟩ := recvLoop_ok pre (a.push x) nm z w s d u
    refine ⟨b, h1, ?_⟩
    rw [h2, Array.size_push, List.length_cons]
    omega

theorem read_ok (n : Nat) (F : Fork) (nm : Option String) (z w : Nat) (s d : List E) (u : Tape)
    (h : s.length = n) : ∃ b : Array E,
      Fl.read n F (⟨nm, z, w, s, d⟩ :: u) = some (b, F, ⟨nm, z, w, [], d⟩ :: u) ∧ b.size = n := by
  obtain ⟨b, h1, h2⟩ := recvLoop_ok s (Array.emptyWithCapacity n) nm z w [] d u
  rw [List.append_nil, h] at h1
  refine ⟨b, ?_, by rw [h2, h]; simp⟩
  show (recvN n _).map _ = _
  unfold recvN
  rw [h1]
  rfl

theorem closeOne_ok (name : String) (nz w : Nat) (x : E) (u : Tape) :
    closeOne name nz (⟨some name, nz, w, [], [x]⟩ :: u) = some (x, u) := by
  simp [closeOne]

theorem closeN_ok (name : String) (nz w : Nat) (d : List E) (u : Tape) :
    closeN name nz d.length (⟨some name, nz, w, [], d⟩ :: u) = some (d, u) := by
  simp [closeN]

theorem one_of {l : List E} (h : l.length = 1) : ∃ x, l = [x] := List.length_eq_one_iff.1 h

/-- A round in which nothing is sent and one element is drawn. -/
theorem answer_ok {r : RoundName} {F : Fork} {t : Tape} {L : List Shape} (hr : r.name ≠ "")
    (h : t.map shapeOf = (r.name, 0, 1, 0) :: L) :
    ∃ x u, Fl.answer r F t = some (x, F, u) ∧ u.map shapeOf = L := by
  obtain ⟨w, s, d, u, rfl, h1, h2, h3⟩ := head_of h hr
  obtain rfl : s = [] := List.length_eq_zero_iff.1 h1
  obtain ⟨x, rfl⟩ := one_of h2
  refine ⟨x, u, ?_, h3⟩
  show (closeOne r.name 0 _).map _ = _
  rw [closeOne_ok]
  rfl

/-- A round in which nothing is sent and n elements are drawn. -/
theorem point_ok {r : RoundName} {n : Nat} {F : Fork} {t : Tape} {L : List Shape} (hr : r.name ≠ "")
    (h : t.map shapeOf = (r.name, 0, n, 0) :: L) :
    ∃ x u, Fl.point r n F t = some (x, F, u) ∧ u.map shapeOf = L := by
  obtain ⟨w, s, d, u, rfl, h1, h2, h3⟩ := head_of h hr
  obtain rfl : s = [] := List.length_eq_zero_iff.1 h1
  have h2' : d.length = n := h2
  subst h2'
  refine ⟨d.toArray, u, ?_, h3⟩
  show (Fl.pointOn r.name d.length _).map _ = _
  unfold Fl.pointOn
  rw [closeN_ok]
  rfl

/-! ## The ledger -/

theorem hide_some {F : Fork} {j : Nat} (hF : Sized F) (hj : j < F.ns) (hf : ¬ Filled F j)
    (y factor : E) : ∃ G, F.hide j y factor = some G := by
  unfold Fork.hide
  have h3 : F.gotF.size = F.ns := hF.2.2
  have e : F.gotF.getD j true = F.gotF.getD j false := by
    simp [Array.getD_eq_getD_getElem?, h3, hj]
  have hf' : F.gotF.getD j false = false := by
    unfold Filled at hf
    simpa using hf
  rw [if_pos (by simp [hj, h3, e, hf'])]
  exact ⟨_, rfl⟩

theorem hideSteps_some (factor : E) : ∀ (l : List E) (first : Nat) (F : Fork), Sized F →
    first + l.length ≤ F.ns → (∀ i < l.length, ¬ Filled F (first + i)) →
    ∃ x, l.foldlM (Fork.hideStep factor) (first, F) = some x
  | [], first, F, _, _, _ => ⟨_, rfl⟩
  | y :: l, first, F, hF, hr, hf => by
    have hr' : first + (l.length + 1) ≤ F.ns := hr
    obtain ⟨G, hG⟩ := hide_some hF (j := first) (by omega) (by simpa using hf 0 (by simp)) y factor
    obtain ⟨-, -, g3, g4, -, -, -, g8⟩ := PscRun.hide_ok F G first y factor hF hG
    obtain ⟨x, hx⟩ := hideSteps_some factor l (first + 1) G g4 (by rw [g3.ns]; omega)
      (fun i hi => by
        rw [(g8 (first + 1 + i) (by omega)).2.2, show first + 1 + i = first + (i + 1) by omega]
        exact hf (i + 1) (by simpa using hi))
    refine ⟨x, ?_⟩
    have hs : Fork.hideStep factor (first, F) y = some (first + 1, G) := by
      show (F.hide first y factor).map _ = _
      rw [hG]
      rfl
    rw [List.foldlM_cons, hs]
    exact hx

theorem hideRun_some {F : Fork} {first : Nat} {v : Array E} (hF : Sized F)
    (hr : first + v.size ≤ F.ns) (hf : ∀ i < v.size, ¬ Filled F (first + i)) (factor : E) :
    ∃ G, F.hideRun first v factor = some G := by
  obtain ⟨x, hx⟩ := hideSteps_some factor v.toList first F hF (by simpa using hr)
    (by simpa using hf)
  unfold Fork.hideRun
  rw [← Array.foldlM_toList, hx]
  exact ⟨_, rfl⟩

theorem public_loop_some (F : Fork) : ∀ (l : List (Nat × E)) (v : E),
    (∀ x ∈ l, x.1 < F.ns ∧ Filled F x.1) →
    ∃ τ, l.foldlM (fun (v : E) (x : Nat × E) => (F.shown x.1).map fun y => addE v (mulE x.2 y)) v =
      some τ
  | [], v, _ => ⟨v, rfl⟩
  | x :: l, v, h => by
    obtain ⟨h1, h2⟩ := h x List.mem_cons_self
    have hs : F.shown x.1 = some (F.vp.getD x.1 zeroE) := (PscRun.shown_iff F x.1 _).2 ⟨h1, h2, rfl⟩
    obtain ⟨τ, hτ⟩ := public_loop_some F l (addE v (mulE x.2 (F.vp.getD x.1 zeroE)))
      fun y hy => h y (List.mem_cons_of_mem _ hy)
    refine ⟨τ, ?_⟩
    rw [List.foldlM_cons, hs]
    exact hτ

theorem public_some {F : Fork} {a : Aff} (h : AllShown F a) : ∃ τ, F.publicPart a = some τ := by
  unfold Fork.publicPart
  rw [← Array.foldlM_toList]
  exact public_loop_some F _ _ h

/-! ## The sumcheck's routines -/

theorem begin_ok {C : Aff} {F : Fork} {t : Tape} {L : List Shape} (hC : AllShown F C)
    (h : t.map shapeOf = (RoundName.pscEpsilon.name, 1, 1, 0) :: L) :
    ∃ τ mu eps u, Fl.pscBegin C F t =
        some ({ start := C, started := true, target := τ, first := F.next, eps := eps,
                claim := addE mu (mulE eps τ) }, took F 1, u) ∧ u.map shapeOf = L := by
  obtain ⟨w, s, d, u, rfl, h1, h2, h3⟩ := head_of h (by decide)
  obtain ⟨mu, rfl⟩ := one_of h1
  obtain ⟨eps, rfl⟩ := one_of h2
  obtain ⟨τ, hτ⟩ := public_some hC
  refine ⟨τ, mu, eps, u, ?_, h3⟩
  unfold Fl.pscBegin
  rw [bind_eq (a := τ) (G := F) (u := _) (by
    show (F.publicPart C).map _ = _
    rw [hτ]; rfl)]
  rfl

theorem pscRound_ok {p : Psc} {w : OnBytes.Psc.Weight} {name : RoundName} {nz : Nat} {F : Fork}
    {t : Tape} {L : List Shape} (hn : name.name ≠ "") (hf : w.fits = true)
    (hh : Model.weightHeld w = true)
    (h : t.map shapeOf = (name.name, w.d - 1, 1, nz) :: L) (hd : 1 ≤ w.d) :
    ∃ (sent : Array E) (x : E) (u : Tape),
      Fl.pscRound p w (closeOne name.name nz) F t =
        some ((x, { p with claim := OnBytes.Psc.polyAt (w.complete sent.toList p.claim) x,
                           vars := p.vars.push w, r := p.r.push x }), took F (w.d - 1), u) ∧
      u.map shapeOf = L ∧ sent.size + 1 = w.d := by
  obtain ⟨wr, s, d, u, rfl, h1, h2, h3⟩ := head_of h hn
  obtain ⟨x, rfl⟩ := one_of h2
  obtain ⟨b, hb, hbs⟩ := read_ok (w.d - 1) F (some name.name) nz wr s [x] u h1
  refine ⟨b, x, u, ?_, h3, by omega⟩
  unfold Fl.pscRound
  rw [bind_eq (must_ok (by rw [Bool.and_eq_true]; exact ⟨hf, hh⟩) F _), bind_eq hb,
    bind_eq (must_ok (by rw [hbs]; simp; omega) F _)]
  dsimp only
  rw [bind_eq (a := x) (G := F) (u := u) (by
    show (closeOne name.name nz _).map _ = _
    rw [closeOne_ok]; rfl), bind_eq (takeSlots_eq _ _ _)]
  rfl

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.hideRun_some
#print axioms VerifiableInference.Desc.K3.KeyLaw.begin_ok
#print axioms VerifiableInference.Desc.K3.KeyLaw.pscRound_ok
