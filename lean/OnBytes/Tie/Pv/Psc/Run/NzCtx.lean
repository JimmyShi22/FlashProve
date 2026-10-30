-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Psc/Run/NzCtx.lean: one premise on a context in the place of "the reading of beta is
not 0" at each masked sumcheck.

In the round "PSC Y" of a masked sumcheck the verifier's element beta is drawn by the rule that
never gives 0. The port's routines do not test that: Blk.close (OnBytes/Iop/Ground.lean) compares
the number of such draws that the caller names with the number in the plan's entry, and the numbers
of draws with the entry's, and returns what the view's round holds. That an element drawn under that
rule is not the word 0 is a property of the view: by the format's text its rule for such a draw
gives no 0, and the strict reader makes the view by that rule. That its reading is not 0 hangs on
the reading too. Here the property is stated once, of a reading and a context, and carried along a
run; for the reading in the library's field (`Reading.gl`) it follows from a property of the drawn
words alone.

Main names:
  `NzAt`: of a plan's entry and what a round has drawn: if all the entry's elements are drawn by the
    rule that never gives 0, the reading of each drawn element is not 0.
  `NzCtx`: of a context: the run is on a view, and `NzAt` holds of the k-th entry that is not yet
    used and the k-th round that is not yet closed, for every k.
  `Keeps`: a block keeps `NzCtx`: from a context with it, every success leaves a context with it.
  `keeps_pure`, `keeps_bind`, `keeps_recvE`, `keeps_recvEs`, `keeps_close`, `keeps_closeOne`,
    `keeps_closeEmpty`, `keeps_hearOne`, `keeps_hearMany`: the calls of which a masked sumcheck's
    listener is made keep it.
  `closeOne_nz`: a round that is closed for one element under the rule that never gives 0, from a
    context with `NzCtx`: the reading of that element is not 0.
  `parts_nz`: of the rounds of one masked sumcheck (`Parts`, OnBytes/Tie/Pv/Psc/Run/PscSeam.lean)
    heard from a context with `NzCtx`: the reading of beta is not 0, and the context that is left
    has `NzCtx`.
  `gl_ne_zero`, `nzAt_gl`: for `Reading.gl`: a triple of words below the prime that is not the
    triple of zeros does not read as 0; so `NzAt` holds if the drawn triples are such.

Limits: `NzCtx` at the context from which a chain's block starts is a premise: nothing here says
that a view which the strict reader makes has it, nor that its drawn words are below the prime and
not all 0. A reading that takes an element other than 0 to 0 need not have it. An entry only some of
whose elements are drawn by that rule is not spoken of. Calls other than those named are not
treated.
-/
import OnBytes.Tie.Pv.Psc.Run.PscSeam

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Model.Road
open OnBytes.Psc (Weight hearOne hearMany)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- If all the entry's elements are drawn by the rule that never gives 0, none reads as 0. -/
def NzAt (e : Fmt.Entry) (d : Fmt.Drawn) : Prop :=
  e.drawNZ = e.drawE → ∀ x ∈ d.elems, ρ.val (E.ofTriple x) ≠ 0

/-- The run is on a view, and the rounds that are not yet closed have `NzAt` at their entries. -/
def NzCtx (c : Ctx) : Prop :=
  c.ch.dry = false ∧ ∀ (k : Nat) (e : Fmt.Entry) (r : Fmt.RoundView), c.ch.entries[k]? = some e →
    c.ch.pending[k]? = some r → NzAt ρ e r.drawn

/-- A block keeps `NzCtx`. -/
def Keeps {α : Type} (b : Blk α) : Prop :=
  ∀ c a c', NzCtx ρ c → b.Yields c a c' → NzCtx ρ c'

theorem keeps_pure {α : Type} (a : α) : Keeps ρ (pure a : Blk α) := fun c x c' h y => by
  obtain ⟨_, rfl⟩ := (Blk.yields_pure _ _ _ _).1 y
  exact h

theorem keeps_bind {α β : Type} (b : Blk α) (f : α → Blk β) (hb : Keeps ρ b)
    (hf : ∀ a, Keeps ρ (f a)) : Keeps ρ (b >>= f) := fun c x c' h y => by
  obtain ⟨a, c1, y1, y2⟩ := (Blk.yields_bind _ _ _ _ _).1 y
  exact hf a c1 x c' (hb c a c1 h y1) y2

theorem keeps_recvE : Keeps ρ Blk.recvE := fun c x c' h y => by
  obtain ⟨r, rest, vs, e1, _, e3, e4⟩ := Blk.recvE_inv x c c' h.1 y
  refine ⟨e4.dry.symm ▸ h.1, fun k e r' he hr => ?_⟩
  rw [e4.entries] at he
  rw [e3] at hr
  cases k with
  | zero =>
    have hr' : r' = { r with vals := vs } := by simpa using hr.symm
    rw [hr']
    exact h.2 0 e r he (by rw [e1]; rfl)
  | succ k => exact h.2 (k + 1) e r' he (by rw [e1]; exact hr)

theorem keeps_recvEsInto : ∀ (n : Nat) (acc : Array E), Keeps ρ (Blk.recvEsInto n acc)
  | 0, acc => keeps_pure ρ acc
  | n + 1, acc => keeps_bind ρ _ _ (keeps_recvE ρ) fun x => keeps_recvEsInto n (acc.push x)

theorem keeps_recvEs (n : Nat) : Keeps ρ (Blk.recvEs n) :=
  keeps_bind ρ _ _ (keeps_recvEsInto ρ n #[]) fun a => keeps_pure ρ a.toList

theorem keeps_close (name : String) (kind : Fmt.Kind) (nz : Nat) :
    Keeps ρ (Blk.close name kind nz) := fun c d c' h y => by
  obtain ⟨e, es, r, rest, a1, _, _, a4, _, _, _, _, _, a10, a11, _, _, _, _, a16, _⟩ :=
    Blk.close_inv name kind nz d c c' h.1 y
  refine ⟨a16, fun k e' r' he hr => ?_⟩
  rw [a11] at he
  rw [a10] at hr
  exact h.2 (k + 1) e' r' (by rw [a1]; exact he) (by rw [a4]; exact hr)

theorem keeps_closeOne (name : String) (kind : Fmt.Kind) (nz : Nat) :
    Keeps ρ (Blk.closeOne name kind nz) := fun c x c' h y => by
  obtain ⟨d, y1, _⟩ := Blk.closeOne_inv name kind nz x c c' y
  exact keeps_close ρ name kind nz c d c' h y1

theorem keeps_closeEmpty (name : String) : Keeps ρ (Blk.closeEmpty name) :=
  keeps_bind ρ _ _ (keeps_close ρ name .nothing 0) fun _ => keeps_pure ρ ()

theorem keeps_hearOne (name : String) (kind : Fmt.Kind) (n nz : Nat) :
    Keeps ρ (hearOne name kind n nz) :=
  keeps_bind ρ _ _ (keeps_recvEs ρ n) fun q =>
    keeps_bind ρ _ _ (keeps_closeOne ρ name kind nz) fun g => keeps_pure ρ (q, g)

theorem keeps_hearMany : ∀ ns : List Nat, Keeps ρ (hearMany ns)
  | [] => keeps_pure ρ []
  | n :: ns => keeps_bind ρ _ _ (keeps_hearOne ρ "PSC round" .elems n 0) fun a =>
    keeps_bind ρ _ _ (keeps_hearMany ns) fun l => keeps_pure ρ (a :: l)

/-- One element drawn by the rule that never gives 0. -/
theorem closeOne_nz (name : String) (kind : Fmt.Kind) (x : E) (c c' : Ctx) (h : NzCtx ρ c)
    (y : (Blk.closeOne name kind 1).Yields c x c') : ρ.val x ≠ 0 := by
  obtain ⟨d, y1, hd⟩ := Blk.closeOne_inv name kind 1 x c c' y
  obtain ⟨e, es, r, rest, a1, _, a3, a4, _, a6, a7, _⟩ := Blk.close_inv name kind 1 d c c' h.1 y1
  have hE : e.drawNZ = e.drawE := by
    rw [a3, ← a7, hd]
    rfl
  have hn := h.2 0 e r (by rw [a1]; rfl) (by rw [a4]; rfl) hE x.triple (by rw [← a6, hd]; simp)
  exact hn

theorem hearOne_nz (name : String) (kind : Fmt.Kind) (n : Nat) (q : List E) (x : E) (c c' : Ctx)
    (h : NzCtx ρ c) (y : (hearOne name kind n 1).Yields c (q, x) c') : ρ.val x ≠ 0 := by
  unfold hearOne at y
  obtain ⟨q', c1, y1, y2⟩ := (Blk.yields_bind _ _ _ _ _).1 y
  obtain ⟨g, c2, y3, y4⟩ := (Blk.yields_bind _ _ _ _ _).1 y2
  obtain ⟨e1, _⟩ := (Blk.yields_pure _ _ _ _).1 y4
  have e2 : x = g := congrArg Prod.snd e1
  rw [e2]
  exact closeOne_nz ρ name kind g c1 c2 (keeps_recvEs ρ n c q' c1 h y1) y3

/-- The rounds of one masked sumcheck. -/
theorem parts_nz {c c1 c' : Ctx} {riders : List E} {mu eps : E} {ws : List Weight}
    {rs : List (List E × E)} {dY : Nat} {sentY : List E} {beta : E} {v : List E}
    (a : Parts c c1 c' riders mu eps ws rs dY sentY beta v) (h : NzCtx ρ c) :
    ρ.val beta ≠ 0 ∧ NzCtx ρ c' := by
  obtain ⟨c2, c3, c4, c5, h0, h1, h2, h3, h4, h5⟩ := a
  have k1 := keeps_recvEs ρ _ _ _ _ h h0
  have k2 := keeps_hearOne ρ _ _ _ _ _ _ _ k1 h1
  have k3 := keeps_hearMany ρ _ _ _ _ k2 h2
  have k4 := keeps_hearOne ρ _ _ _ _ _ _ _ k3 h3
  have k5 := keeps_recvEs ρ _ _ _ _ k4 h4
  exact ⟨hearOne_nz ρ _ _ _ _ _ _ _ k3 h3, keeps_closeEmpty ρ _ _ _ _ k5 h5⟩

/-! ## The reading in the library's field -/

/-- A triple of words below the prime that is not the triple of zeros does not read as 0. -/
theorem gl_ne_zero (x : Fmt.Ext3) (hok : Fmt.Fld.two.okE x = true) (hx : x ≠ Fmt.Fld.zeroE) :
    Reading.gl.val (E.ofTriple x) ≠ 0 := by
  intro h0
  have h1 : Slice.toE x = Slice.toE Fmt.Fld.zeroE := by
    rw [Slice.toE_zeroE]
    exact h0
  exact hx (Slice.toE_inj x Fmt.Fld.zeroE hok (by decide) h1)

/-- `NzAt` for that reading, from a property of the drawn words alone. -/
theorem nzAt_gl (e : Fmt.Entry) (d : Fmt.Drawn)
    (h : e.drawNZ = e.drawE → ∀ x ∈ d.elems, Fmt.Fld.two.okE x = true ∧ x ≠ Fmt.Fld.zeroE) :
    NzAt Reading.gl e d := fun he x hx => gl_ne_zero x (h he x hx).1 (h he x hx).2

end OnBytes.Model.Road

#print axioms OnBytes.Model.Road.gl_ne_zero
#print axioms OnBytes.Model.Road.closeOne_nz
#print axioms OnBytes.Model.Road.parts_nz
