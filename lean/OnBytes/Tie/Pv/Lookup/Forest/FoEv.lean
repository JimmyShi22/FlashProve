-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoEv.lean.
The calls of a run of the byte-level verifier's routine as rounds of plain data, and further laws on
"if the run returns".

A routine of a sub-proof runs in two states, the sub-proof's (Fork) and the channel's (Ctx), and may
fail. The plain data of a run are the calls of the channel's own routines that it made, each with
its result: `Ev`, `Ev.At`, `Evs` of OnBytes/Tie/Pv/Psc/PscRun.lean, which also has the laws of bind,
pure, lift, must, get, take, ask, change and takeSlots.

* `evs_append`, `evs_one`: the calls of a concatenation, and of one call, as equivalences.
* `flEv ρ l`: the calls as rounds of plain data, under a reading ρ: what is received is gathered
  until a call closes the message; that call gives the round's drawn values. `openAfter`: what is
  received and not yet closed. `flGo_append`, `openAfter_append`, `flEv_append`: the laws at a
  concatenation.
* Further laws, each as an equivalence on "returns": `mustAs_ok`, `slot_ok`, `owe_ok`, `shown_ok`,
  `publicPart_ok`, `foldlM_nil_ok`, `foldlM_cons_ok`; for the routines on the channel:
  `readSum_ok`, `answer_ok`, `read_ok`, `empty_ok`, `point_ok`.
* `rdA ρ z`, `rdRV ρ r`: an array of field elements, and a round of a view, read as plain data.
* `FilledA F a`: every slot that the form a names is a slot of the state F and is filled in it.

Limit: `Evs l c c'` says that the calls of l, made one after the other from the context c, return
what l records and lead to c'. A statement "there is l with Evs l c c'" on a run so ties l to the
run's two contexts, not to the routine's text. On a view with no message open the rounds between two
contexts are fixed (`Took`, OnBytes/Tie/Pv/Psc/PscView.lean).
Nothing here speaks of what a context holds.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoEnds
import OnBytes.Model.HideLaws
import OnBytes.Model.Look
import OnBytes.Tie.Pv.Psc.PscView
import OnBytes.Tie.Pv.Psc.PscFork
import OnBytes.Tie.Pv.Psc.PscWhole

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun

theorem evs_append : ∀ (l₁ l₂ : List Ev) (c c' : Ctx),
    Evs (l₁ ++ l₂) c c' ↔ ∃ c₁, Evs l₁ c c₁ ∧ Evs l₂ c₁ c'
  | [], l₂, c, c' => ⟨fun h => ⟨c, rfl, h⟩, fun ⟨_, h1, h2⟩ => h1 ▸ h2⟩
  | e :: l₁, l₂, c, c' => by
    constructor
    · rintro ⟨c₁, h1, h2⟩
      obtain ⟨c₂, h3, h4⟩ := (evs_append l₁ l₂ c₁ c').1 h2
      exact ⟨c₂, ⟨c₁, h1, h3⟩, h4⟩
    · rintro ⟨c₂, ⟨c₁, h1, h3⟩, h4⟩
      exact ⟨c₁, h1, (evs_append l₁ l₂ c₁ c').2 ⟨c₂, h3, h4⟩⟩

theorem evs_one (e : Ev) (c c' : Ctx) : Evs [e] c c' ↔ e.At c c' :=
  ⟨fun ⟨_, h1, h2⟩ => h2 ▸ h1, fun h => ⟨c', h, rfl⟩⟩

/-- Every slot that the form names is filled. -/
def FilledA (F : Fork) (a : Aff) : Prop := ∀ x ∈ a.slots.toList, x.1 < F.ns ∧ Filled F x.1

/-! ### the calls as rounds of plain data -/
section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- A round of a view as plain data. -/
def rdRV (r : Fmt.RoundView) : List K × List K := ((sentOf r).map ρ.val, (drawnOf r).map ρ.val)

/-- An array of field elements, read. -/
def rdA (z : Array OnBytes.E) : List K := z.toList.map ρ.val

/-- The rounds, from what is already received of the open message. -/
def flGo : List K → List Ev → Rounds K
  | _, [] => []
  | acc, .sum x :: l => flGo (acc ++ [ρ.val x]) l
  | acc, .read _ v :: l => flGo (acc ++ v.toList.map ρ.val) l
  | acc, .ans _ x :: l => (acc, [ρ.val x]) :: flGo [] l
  | acc, .ansNZ _ x :: l => (acc, [ρ.val x]) :: flGo [] l
  | acc, .empty _ :: l => (acc, []) :: flGo [] l
  | acc, .point _ _ v :: l => (acc, v.toList.map ρ.val) :: flGo [] l

/-- What is received and not yet closed. -/
def openAfter : List K → List Ev → List K
  | acc, [] => acc
  | acc, .sum x :: l => openAfter (acc ++ [ρ.val x]) l
  | acc, .read _ v :: l => openAfter (acc ++ v.toList.map ρ.val) l
  | _, .ans _ _ :: l => openAfter [] l
  | _, .ansNZ _ _ :: l => openAfter [] l
  | _, .empty _ :: l => openAfter [] l
  | _, .point _ _ _ :: l => openAfter [] l

/-- The calls of a run as rounds of plain data. -/
def flEv (l : List Ev) : Rounds K := flGo ρ [] l

theorem flGo_append : ∀ (l₁ l₂ : List Ev) (acc : List K),
    flGo ρ acc (l₁ ++ l₂) = flGo ρ acc l₁ ++ flGo ρ (openAfter ρ acc l₁) l₂
  | [], _, _ => rfl
  | .sum x :: l₁, l₂, acc => flGo_append l₁ l₂ (acc ++ [ρ.val x])
  | .read _ v :: l₁, l₂, acc => flGo_append l₁ l₂ (acc ++ v.toList.map ρ.val)
  | .ans _ x :: l₁, l₂, acc => congrArg ((acc, [ρ.val x]) :: ·) (flGo_append l₁ l₂ [])
  | .ansNZ _ x :: l₁, l₂, acc => congrArg ((acc, [ρ.val x]) :: ·) (flGo_append l₁ l₂ [])
  | .empty _ :: l₁, l₂, acc => congrArg ((acc, []) :: ·) (flGo_append l₁ l₂ [])
  | .point _ _ v :: l₁, l₂, acc => congrArg ((acc, v.toList.map ρ.val) :: ·) (flGo_append l₁ l₂ [])

theorem openAfter_append : ∀ (l₁ l₂ : List Ev) (acc : List K),
    openAfter ρ acc (l₁ ++ l₂) = openAfter ρ (openAfter ρ acc l₁) l₂
  | [], _, _ => rfl
  | .sum x :: l₁, l₂, acc => openAfter_append l₁ l₂ (acc ++ [ρ.val x])
  | .read _ v :: l₁, l₂, acc => openAfter_append l₁ l₂ (acc ++ v.toList.map ρ.val)
  | .ans _ _ :: l₁, l₂, _ => openAfter_append l₁ l₂ []
  | .ansNZ _ _ :: l₁, l₂, _ => openAfter_append l₁ l₂ []
  | .empty _ :: l₁, l₂, _ => openAfter_append l₁ l₂ []
  | .point _ _ _ :: l₁, l₂, _ => openAfter_append l₁ l₂ []

/-- Behind calls that leave no message open the rounds are laid in a row. -/
theorem flEv_append (l₁ l₂ : List Ev) (h : openAfter ρ [] l₁ = []) :
    flEv ρ (l₁ ++ l₂) = flEv ρ l₁ ++ flEv ρ l₂ := by
  unfold flEv
  rw [flGo_append, h]

end

/-! ### further laws on "returns" -/
section
variable {α : Type}

theorem mustAs_ok (name : String) (b : Bool) (F : Fork) (c : Ctx) (r : (Unit × Fork) × Ctx) :
    (StateT.lift (mustAs name b) : SubM Unit) F c = .ok r ↔ b = true ∧ r = (((), F), c) := by
  rw [lift_ok]
  cases b
  · constructor
    · rintro ⟨a, c1, h, _⟩
      exact absurd h (by simp [mustAs, refuse, Blk.fail])
    · rintro ⟨h, _⟩
      exact absurd h (by simp)
  · constructor
    · rintro ⟨a, c1, h, rfl⟩
      have e : ((), c) = (a, c1) := Except.ok.inj h
      obtain ⟨_, rfl⟩ := Prod.mk.inj e
      exact ⟨rfl, rfl⟩
    · rintro ⟨_, rfl⟩
      exact ⟨(), c, rfl, rfl⟩

theorem slot_ok (F : Fork) (c : Ctx) (r : (ℕ × Fork) × Ctx) :
    SubM.slot F c = .ok r ↔ r = ((F.next, F), c) := by
  unfold SubM.slot
  rw [ask_ok]
  constructor
  · rintro ⟨a, h, rfl⟩
    rw [← Option.some.inj h]
  · rintro rfl
    exact ⟨_, rfl, rfl⟩

theorem owe_ok (what : String) (F : Fork) (c : Ctx) (r : (ℕ × Fork) × Ctx) :
    SubM.owe what F c = .ok r ↔ r = (F.owe what, c) := by
  unfold SubM.owe
  rw [take_ok]
  constructor
  · rintro ⟨y, h, rfl⟩
    rw [← Option.some.inj h]
  · rintro rfl
    exact ⟨_, rfl, rfl⟩

theorem shown_ok (j : ℕ) (F : Fork) (c : Ctx) (r : (OnBytes.E × Fork) × Ctx) :
    SubM.shown j F c = .ok r ↔ ∃ a, F.shown j = some a ∧ r = ((a, F), c) := ask_ok _ F c r

theorem publicPart_ok (a : Aff) (F : Fork) (c : Ctx) (r : (OnBytes.E × Fork) × Ctx) :
    SubM.publicPart a F c = .ok r ↔ ∃ x, F.publicPart a = some x ∧ r = ((x, F), c) := ask_ok _ F c r

theorem foldlM_nil_ok {σ : Type} (f : σ → α → SubM σ) (s : σ) (F : Fork) (c : Ctx)
    (r : (σ × Fork) × Ctx) : (([] : List α).foldlM f s) F c = .ok r ↔ r = ((s, F), c) :=
  pure_ok s F c r

theorem foldlM_cons_ok {σ : Type} (f : σ → α → SubM σ) (s : σ) (a : α) (l : List α) (F : Fork)
    (c : Ctx) (r : (σ × Fork) × Ctx) :
    ((a :: l).foldlM f s) F c = .ok r ↔
      ∃ s₁ F₁ c₁, f s a F c = .ok ((s₁, F₁), c₁) ∧ (l.foldlM f s₁) F₁ c₁ = .ok r := by
  rw [List.foldlM_cons]
  exact bind_ok _ _ F c r

/-! ### the routines on the channel -/

theorem liftEv_ok (b : Blk α) (e : α → Ev) (he : ∀ a c c', (e a).At c c' ↔ b c = .ok (a, c'))
    (F G : Fork) (c c' : Ctx) (x : α) :
    (StateT.lift b : SubM α) F c = .ok ((x, G), c') ↔ Evs [e x] c c' ∧ G = F := by
  rw [lift_ok, evs_one, he]
  constructor
  · rintro ⟨a, c1, h, e1⟩
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (x = a ∧ G = F) ∧ c' = c1 := by simpa [Prod.ext_iff] using e1
    exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨x, c', h, rfl⟩

theorem readSum_ok (F G : Fork) (c c' : Ctx) (x : OnBytes.E) :
    SubM.readSum F c = .ok ((x, G), c') ↔ Evs [.sum x] c c' ∧ G = F :=
  liftEv_ok trSum Ev.sum (fun _ _ _ => Iff.rfl) F G c c' x

theorem answer_ok (r : RoundName) (F G : Fork) (c c' : Ctx) (x : OnBytes.E) :
    SubM.answer r F c = .ok ((x, G), c') ↔ Evs [.ans r x] c c' ∧ G = F :=
  liftEv_ok (trAnswer r) (Ev.ans r) (fun _ _ _ => Iff.rfl) F G c c' x

theorem read_ok (n : ℕ) (F G : Fork) (c c' : Ctx) (v : Array OnBytes.E) :
    SubM.read n F c = .ok ((v, G), c') ↔ Evs [.read n v] c c' ∧ G = F :=
  liftEv_ok (trRead n) (Ev.read n) (fun _ _ _ => Iff.rfl) F G c c' v

theorem empty_ok (r : RoundName) (F G : Fork) (c c' : Ctx) :
    SubM.empty r F c = .ok (((), G), c') ↔ Evs [.empty r] c c' ∧ G = F :=
  liftEv_ok (trEmpty r) (fun _ => Ev.empty r) (fun _ _ _ => Iff.rfl) F G c c' ()

theorem point_ok (r : RoundName) (n : ℕ) (F G : Fork) (c c' : Ctx) (v : Array OnBytes.E) :
    SubM.point r n F c = .ok ((v, G), c') ↔ Evs [.point r n v] c c' ∧ G = F :=
  liftEv_ok (trPoint r n) (Ev.point r n) (fun _ _ _ => Iff.rfl) F G c c' v

end

end Fo
