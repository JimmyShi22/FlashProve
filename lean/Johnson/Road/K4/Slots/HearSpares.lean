-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/Slots/HearSpares.lean: K4's HEARING, FROM A LEDGER WITH ARRAYS OF THE RIGHT SIZES,
TURNS NEITHER THE MARK NOR THE SHOWN VALUE NOR THE FACTOR OF A SLOT THAT IT HAS NOT TAKEN ITSELF.
Where `hear` (OnBytes/Desc/First/K4/Hear.lean) at the plain engine returns, from a ledger F with
arrays of the right sizes to a ledger G: every slot below F.next, and every slot from G.next on, is
filled in G exactly if it is filled in F, and holds the same shown value and factor. So a slot that
an earlier block has taken and left free (the window of the lookup's leaves' sumcheck) is still free
behind the hearing, and so is every slot that nobody has taken yet. Definitions, statements and
proofs.

Why it is not `Later`. `OnBytes.PscRun.Later` says that what is filled stays filled. It does not say
that what is free stays free. `Fork.hide` (OnBytes/Model/Hide.lean) tests that the slot is there and
free; it does not look at F.next.

  `SameAt F G j`: slot j is filled in G exactly if in F; same shown value; same factor.
  `Fresh F G`: F.next ≤ G.next, and `SameAt F G j` at each j with j < F.next or G.next ≤ j.
    `Fresh.refl`, `Fresh.trans`.
  `run_same`, `fresh_run`: a run of values put under slots (off `hideRun_ok`).
  `walk_le`, `entries_zip_le`, `win_le`, `win_three`: a sumcheck's window (`Psc.walk`) has at most
    `hidingEntries` members: NO PREMISE on the weights or on the number of challenges.
  `Spares x`: a class: wherever x returns from a ledger with arrays of the right sizes, the ledger
    that it leaves has them too and is `Fresh`. Closed under `pure`, `bind`, `if`, a map. The tactic
    `spares` walks a do-block, as `grows` does (OnBytes/Desc/First/FlGrows.lean, whose pattern this
    file follows).
  WHAT IS NOT IN THE CLASS: `Fl.pscRow` (it lays a window that was taken earlier) and a bare
    `hideRun`. The three places of the hearing that call `pscRow` are treated whole, each off its
    own law: a product layer (`levelIn_heard`), the second token sumcheck (`hearTerms_calls`,
    `tscIn_heard`; `tsc_win` says where a token sumcheck's window lies), the batched sumcheck
    (`hearStack_tape`).
  **`hear_fresh`**: the statement on top.

Limits. ONE DIRECTION, FROM A RETURN. Only the hearing: the two runs of claims behind it lay the
windows of the row products' token sumcheck, of the lookup's leaves' sumcheck and of the merge, and
nothing is said of them here. Nothing on the slots from F.next on and below G.next (see
HearFills.lean). Nothing on the number G.next. Of a slot's coefficient in the one equation (LS), of
the number of slots and of the ledger's other fields nothing is said here. Nothing on soundness.

-/
import Johnson.Road.K4.Slots.HearFills
import OnBytes.Tie.Pv.Lay.Slots

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Slots

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own Heard HeardStack Env nEndT)
open OnBytes.PscRun (Sized Filled hideRun_ok)
open OnBytes.Psc (Weight hidingWalk hidingEntries)
open OnBytes.Tie.Pv.Lay (powers_length entries_three)
open OnBytes.Desc.First.Grow (some_triple bind_some)
open OnBytes.Desc.First.P1 (levelIn_heard tscIn_heard claimsIn_spec pscEnds_spec pscRow_spec
  endP_spec levelWs tscWs plainWs)

variable {α β γ : Type}

/-! ### The relation -/

/-- Slot j holds in G what it holds in F. -/
def SameAt (F G : Fork) (j : ℕ) : Prop :=
  (Filled G j ↔ Filled F j) ∧ G.vp.getD j zeroE = F.vp.getD j zeroE ∧
    G.mf.getD j zeroE = F.mf.getD j zeroE

theorem SameAt.refl (F : Fork) (j : ℕ) : SameAt F F j := ⟨Iff.rfl, rfl, rfl⟩

theorem SameAt.trans {F G H : Fork} {j : ℕ} (h1 : SameAt F G j) (h2 : SameAt G H j) :
    SameAt F H j :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

/-- F.next ≤ G.next; and from F to G nothing of the three has turned under a slot below F.next, or
from G.next on. -/
structure Fresh (F G : Fork) : Prop where
  next : F.next ≤ G.next
  same : ∀ j, j < F.next ∨ G.next ≤ j → SameAt F G j

theorem Fresh.refl (F : Fork) : Fresh F F := ⟨Nat.le_refl _, fun j _ => SameAt.refl F j⟩

theorem Fresh.trans {F G H : Fork} (h1 : Fresh F G) (h2 : Fresh G H) : Fresh F H := by
  have a := h1.next
  have b := h2.next
  exact ⟨Nat.le_trans a b, fun j hj =>
    (h1.same j (by omega)).trans (h2.same j (by omega))⟩

/-! ### A run of values -/

/-- From a ledger with arrays of the right sizes a run of values leaves what lies outside it. -/
theorem run_same {F G : Fork} {first : ℕ} {v : Array E} {k : E} (hF : Sized F)
    (h : F.hideRun first v k = some G) :
    Sized G ∧ G.next = F.next ∧ ∀ j, j < first ∨ first + v.size ≤ j → SameAt F G j := by
  obtain ⟨a, s, _, r⟩ := hideRun_ok F G first v k hF h
  exact ⟨s, a.next, fun j hj => ⟨(r j hj).2.2, (r j hj).1, (r j hj).2.1⟩⟩

/-- Slots are taken, up to m, and a run of values is put under some of them. -/
theorem fresh_run {F G : Fork} {m first : ℕ} {v : Array E} {k : E} (hF : Sized F)
    (h : ({ F with next := m } : Fork).hideRun first v k = some G) (h1 : F.next ≤ first)
    (h2 : first + v.size ≤ m) : Sized G ∧ Fresh F G := by
  obtain ⟨s, e, r⟩ := run_same (show Sized ({ F with next := m } : Fork) from hF) h
  have e' : G.next = m := e
  exact ⟨s, ⟨by omega, fun j hj => r j (by omega)⟩⟩

/-! ### How long a window is -/

/-- The hiding polynomial's linear form has at most as many members as the model counts. -/
theorem walk_le : ∀ l : List (Weight × E), (hidingWalk l).1.length ≤ hidingEntries (l.map (·.1))
  | [] => by simp [hidingWalk, hidingEntries]
  | [(w, g)] => by
    simp only [hidingWalk, powers_length, hidingEntries, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    omega
  | (w, g) :: q :: rest => by
    have ih := walk_le (q :: rest)
    have k : (hidingWalk ((w, g) :: q :: rest)).1.length =
        (w.d - 1) + (hidingWalk (q :: rest)).1.length := by
      simp only [hidingWalk, List.length_append, powers_length]
    have e : hidingEntries (((w, g) :: q :: rest).map (·.1)) =
        (w.d - 1) + hidingEntries ((q :: rest).map (·.1)) := by
      simp only [hidingEntries, List.map_cons, List.sum_cons]
      omega
    rw [k, e]
    omega

/-- Pairing the weights with challenges leaves no more of them. -/
theorem entries_zip_le : ∀ (l : List Weight) (r : List E),
    hidingEntries ((l.zip r).map (·.1)) ≤ hidingEntries l
  | [], _ => by simp [hidingEntries]
  | w :: l, [] => by
    simp only [hidingEntries, List.zip_nil_right, List.map_nil, List.sum_nil]
    omega
  | w :: l, g :: r => by
    have ih := entries_zip_le l r
    simp only [hidingEntries, List.zip_cons_cons, List.map_cons, List.sum_cons] at ih ⊢
    omega

/-- **A sumcheck's window has at most `hidingEntries` members.** -/
theorem win_le (p : Psc) : p.walk.1.length ≤ hidingEntries p.vars.toList := by
  unfold Psc.walk
  rw [zipT_eq]
  exact Nat.le_trans (walk_le _) (entries_zip_le _ _)

/-- Where the variables have three coefficients each, and then comes one with dy + 1, the window has
at most 1 + 2 * (their number) + dy members. -/
theorem win_three (p : Psc) (ws : List Weight) (dy : ℕ) (h3 : ∀ w ∈ ws, w.d = 3)
    (hv : p.vars.toList = ws ++ [Weight.atZero (dy + 1)]) :
    p.walk.1.length ≤ 1 + 2 * ws.length + dy := by
  have h := win_le p
  rw [hv, entries_three ws (Weight.atZero (dy + 1)) dy h3 rfl] at h
  exact h

/-! ### The class -/

/-- Wherever x returns from a ledger with arrays of the right sizes, the ledger that it leaves has
them too, and nothing has turned under a slot that x has not taken. -/
class Spares (x : Fl α) : Prop where
  fresh : ∀ {F : Fork} {t : Tape} {a : α} {G : Fork} {u : Tape}, x F t = some (a, G, u) →
    Sized F → Sized G ∧ Fresh F G

/-- A function that leaves the ledger as it is. -/
theorem Spares.of_same {x : Fl α}
    (h : ∀ (F : Fork) (t : Tape) (a : α) (G : Fork) (u : Tape), x F t = some (a, G, u) → F = G) :
    Spares x :=
  ⟨fun {F t a G u} e hF => by
    obtain rfl := h F t a G u e
    exact ⟨hF, Fresh.refl F⟩⟩

instance spares_pure (a : α) : Spares (pure a : Fl α) :=
  Spares.of_same fun _ _ _ _ _ e => (some_triple.mp e).2.1

/-- One function after another. -/
theorem Spares.bind {x : Fl α} {f : α → Fl β} (hx : Spares x) (hf : ∀ a, Spares (f a)) :
    Spares (x >>= f) :=
  ⟨fun e hF => by
    obtain ⟨a, G, u, h1, h2⟩ := bind_some.mp e
    obtain ⟨s1, f1⟩ := hx.fresh h1 hF
    obtain ⟨s2, f2⟩ := (hf a).fresh h2 s1
    exact ⟨s2, f1.trans f2⟩⟩

instance spares_bind (x : Fl α) (f : α → Fl β) [Spares x] [∀ a, Spares (f a)] :
    Spares (x >>= f) :=
  Spares.bind inferInstance inferInstance

instance spares_map (g : α → β) (x : Fl α) [Spares x] : Spares (g <$> x) := by
  rw [map_eq_pure_bind]
  infer_instance

instance spares_ite (p : Prop) [Decidable p] (x y : Fl α) [Spares x] [Spares y] :
    Spares (if p then x else y) := by
  split <;> infer_instance

/-- The function that always refuses. -/
instance spares_none : Spares (fun _ _ => none : Fl α) := ⟨fun e => by simp at e⟩

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
local macro "spares" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine Spares.bind ?_ ?_
    | intro _
    | split)

/-! ### The steps -/

instance spares_must (b : Bool) : Spares (Fl.must b) :=
  Spares.of_same fun _ _ _ _ _ e => (P1.must_some.mp e).2.1

instance spares_need (x : Option α) : Spares (Fl.need x) :=
  Spares.of_same fun _ _ _ _ _ e => (P1.need_some.mp e).2.1

instance spares_ask (f : Fork → Option α) : Spares (Fl.ask f) :=
  Spares.of_same fun _ _ _ _ _ e => (P1.ask_some.mp e).2.1

instance spares_onTape (g : Tape → Option (α × Tape)) : Spares (Fl.onTape g) :=
  Spares.of_same fun _ _ _ _ _ e => (P1.onTape_some.mp e).2

/-- Taking slots. -/
instance spares_takeSlots (n : ℕ) : Spares (Fl.takeSlots n) :=
  ⟨fun {F t a G u} e hF => by
    obtain ⟨_, rfl, _⟩ := P1.takeSlots_some.mp e
    exact ⟨hF, ⟨Nat.le_add_right _ _, fun j _ => SameAt.refl F j⟩⟩⟩

instance spares_read (n : ℕ) : Spares (Fl.read n) := by unfold Fl.read; infer_instance
instance spares_readSum : Spares Fl.readSum := by unfold Fl.readSum; infer_instance
instance spares_answer (r : RoundName) : Spares (Fl.answer r) := by
  unfold Fl.answer; infer_instance
instance spares_point (r : RoundName) (n : ℕ) : Spares (Fl.point r n) := by
  unfold Fl.point; infer_instance
instance spares_batch (n : ℕ) : Spares (Fl.batch n) := by unfold Fl.batch; infer_instance
instance spares_shown (j : ℕ) : Spares (Fl.shown j) := by unfold Fl.shown; infer_instance
instance spares_publicPart (a : Aff) : Spares (Fl.publicPart a) := by
  unfold Fl.publicPart; infer_instance

/-! ### Hidden values and the masked sumcheck, but for its claim -/

/-- A sending of n claimed values: under the n slots that it takes. -/
instance spares_claimsIn (n : ℕ) : Spares (Fl.claimsIn n) :=
  ⟨fun {F t j G u} h hF => by
    obtain ⟨_, v, hv, _, _, r⟩ := claimsIn_spec h
    exact fresh_run hF r (Nat.le_refl _) (by omega)⟩

instance spares_pscBeginAt (x : E) : Spares (Fl.pscBeginAt x) := by
  unfold Fl.pscBeginAt; spares
instance spares_pscBegin (C : Aff) : Spares (Fl.pscBegin C) := by unfold Fl.pscBegin; spares

instance spares_pscRound (p : Psc) (w : Weight) (draw : Tape → Option (E × Tape)) :
    Spares (Fl.pscRound p w draw) := by
  unfold Fl.pscRound; spares

instance spares_roundIn (form : RoundForm) (p : Psc) (z : E) (d : ℕ) :
    Spares (Fl.roundIn form p z d) := by
  unfold Fl.roundIn; spares

/-- The round in the further variable and the end values: under the last n slots that it takes. -/
instance spares_pscEnds (p : Psc) (d n : ℕ) : Spares (Fl.pscEnds p d n) :=
  ⟨fun {F t x G u} h hF => by
    obtain ⟨e, p'⟩ := x
    obtain ⟨_, _, _, v, _, hv, _, he, r⟩ := pscEnds_spec h
    exact fresh_run hF r (by omega) (by omega)⟩

/-- **A product layer**: its two end values and its own window lie under slots that it takes. -/
instance spares_levelIn (mu : ℕ) (rho : Array E) (C : Aff) (order : List ℕ) :
    Spares (Fl.levelIn mu rho C order) :=
  ⟨fun {F t L G u} h hF => by
    obtain ⟨hom, _, _, _, _, _, _, hvars, _, _, _, _, hfirst, _, hsL, _, _, _, v, G1, hv, r1, _,
      r2⟩ := levelIn_heard h
    have h3 : ∀ w ∈ levelWs mu rho order, w.d = 3 := fun w hw => by
      unfold levelWs at hw
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hw
      rfl
    have hl : (levelWs mu rho order).length = mu := by simp [levelWs, hom]
    have hw := win_three _ _ 2 h3 hvars
    rw [hl] at hw
    obtain ⟨s1, n1, q1⟩ :=
      run_same (show Sized ({ F with next := F.next + 1 + 2 * mu + 2 + 2 } : Fork) from hF) r1
    obtain ⟨s2, n2, q2⟩ := run_same s1 r2
    have n1' : G1.next = F.next + 1 + 2 * mu + 2 + 2 := n1
    refine ⟨s2, ⟨by omega, fun j hj => ?_⟩⟩
    have a : SameAt F G1 j := q1 j (by omega)
    have b : SameAt G1 G j := q2 j (by
      rw [Array.size_replicate, hfirst]
      omega)
    exact a.trans b⟩

/-- **A token sumcheck**, from a ledger with arrays of the right sizes: what it lays lies under
slots that it takes, AND SO DOES ITS WINDOW. Whether the window's slots are free is not said. -/
theorem tsc_win {P : Array E} {lt n dY : ℕ} {F G : Fork} {t u : Tape} {o : Tsc} (hF : Sized F)
    (h : Fl.tscIn P lt n dY F t = some (o, G, u)) :
    Sized G ∧ Fresh F G ∧ F.next ≤ o.p.first ∧ o.p.first + o.p.walk.1.length ≤ G.next := by
  obtain ⟨_, _, _, _, _, hvars, _, _, _, _, _, _, _, v, G0, r0, _, hfirst, hsEnd, hvn, r1⟩ :=
    tscIn_heard h
  have h3 : ∀ w ∈ tscWs (P.toList.take lt), w.d = 3 := fun w hw => by
    unfold tscWs at hw
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hw
    rfl
  have hl : (tscWs (P.toList.take lt)).length = (P.toList.take lt).length := by
    unfold tscWs
    rw [List.length_map]
  have hw := win_three _ _ dY h3 hvars
  rw [hl] at hw
  obtain ⟨s0, n0, q0⟩ := run_same (show Sized ({ F with next := F.next + 1 } : Fork) from hF) r0
  obtain ⟨s1, n1, q1⟩ := run_same (show Sized ({ G0 with
    next := G0.next + 1 + 2 * (P.toList.take lt).length + dY + n } : Fork) from s0) r1
  have n0' : G0.next = F.next + 1 := n0
  have n1' : G.next = G0.next + 1 + 2 * (P.toList.take lt).length + dY + n := n1
  refine ⟨s1, ⟨by omega, fun j hj => ?_⟩, by omega, by omega⟩
  have a : SameAt F G0 j := q0 j (by
    rcases hj with hj | hj
    · exact Or.inl hj
    · refine Or.inr ?_
      show F.next + 1 ≤ j
      omega)
  have b : SameAt G0 G j := q1 j (by omega)
  exact a.trans b

instance spares_tscIn (P : Array E) (lt n d : ℕ) : Spares (Fl.tscIn P lt n d) :=
  ⟨fun h hF => ⟨(tsc_win hF h).1, (tsc_win hF h).2.1⟩⟩

/-! ### The merge of the claims on the weights -/

theorem spares_wsForkRounds : ∀ (n : ℕ) (rm : Array E) (p : Psc), Spares (Fl.wsForkRounds n rm p)
  | 0, rm, p => by
    unfold Fl.wsForkRounds
    infer_instance
  | n + 1, rm, p => by
    unfold Fl.wsForkRounds
    refine Spares.bind inferInstance fun x => ?_
    obtain ⟨r, p'⟩ := x
    exact spares_wsForkRounds n _ p'

instance (n : ℕ) (rm : Array E) (p : Psc) : Spares (Fl.wsForkRounds n rm p) :=
  spares_wsForkRounds n rm p

instance spares_wsForkMerge (lk : ℕ) (sv : Array ℕ) : Spares (Fl.wsForkMerge lk sv) := by
  unfold Fl.wsForkMerge; spares

instance spares_flatForkEnd (lay : WsLay) (cl : Array WsClaim) (sv : Array ℕ) :
    Spares (flatForkEnd lay cl sv) := by
  unfold flatForkEnd; spares

/-! ### The engine's fields that the hearing's open stretches call -/

instance (x : Option α) : Spares (engFl.get x) := inferInstanceAs (Spares (Fl.need x))
instance (b : Bool) : Spares (engFl.must b) := inferInstanceAs (Spares (Fl.must b))
instance (n : String) (b : Bool) : Spares (engFl.mustAs n b) := inferInstanceAs (Spares (Fl.must b))
instance (n : String) (b : Bool) : Spares (engFl.check n b) := inferInstanceAs (Spares (Fl.must b))

instance (r : RoundName) (n : ℕ) : Spares (engFl.point r n) :=
  inferInstanceAs (Spares (if r == .batSigma then (fun _ _ => none) else Fl.point r n))

instance (n : ℕ) : Spares (engFl.claimsIn n) := inferInstanceAs (Spares (Fl.claimsIn n))
instance (n : ℕ) : Spares (engFl.batch n) := inferInstanceAs (Spares (Fl.batch n))

instance (mu : ℕ) (rho : Array E) (C : Aff) (order : List ℕ) :
    Spares (engFl.levelIn mu rho C order) := inferInstanceAs (Spares (Fl.levelIn mu rho C order))

instance (P : Array E) (lt n d : ℕ) : Spares (engFl.tscIn P lt n d) :=
  inferInstanceAs (Spares (Fl.tscIn P lt n d))

instance (lay : WsLay) (cl : Array WsClaim) (sv : Array ℕ) :
    Spares (engFl.wsForkEnd lay cl sv) := inferInstanceAs (Spares (flatForkEnd lay cl sv))

/-! ### The parts of the hearing -/

instance (P : Pub) (g : ℕ) (fo : Forest.Heard) : Spares (hearNorms engFl P g fo) := by
  unfold hearNorms; spares

/-- **The second token sumcheck with its claim**: the window that the claim lays was taken by the
token sumcheck just in front. -/
instance (P : Pub) (H : Heard) : Spares (hearTerms engFl P H) :=
  ⟨fun {F t H' G u} h hF => by
    obtain ⟨tT, G1, u1, row, p', c, _, r, _⟩ := hearTerms_calls h
    obtain ⟨s1, f1, w1, w2⟩ := tsc_win hF c
    obtain ⟨_, _, r2⟩ := pscRow_spec r
    obtain ⟨s2, n2, q2⟩ := run_same s1 r2
    have a := f1.next
    refine ⟨s2, ⟨by omega, fun j hj => (f1.same j (by omega)).trans (q2 j (by
      rw [Array.size_replicate]
      omega))⟩⟩⟩

/-- **The batched sumcheck**: its end values and its own window lie under slots that it takes. -/
instance (P : Pub) (v : Env) (H : Heard) (lamS NCLp : ℕ) :
    Spares (hearStack engFl P v H lamS NCLp) :=
  ⟨fun {F t K G u} h hF => by
    obtain ⟨x, mu0, eps, beta, T, rs, sentY, vals, w1, wY, wV, C, G1, ms, y, p, _, _, _, _, _, _,
      hy, hp, hms, _, _, _, hA, _, _, _, hv, r1, _, r2⟩ := hearStack_tape h
    have hfirst : p.first = F.next := by
      rw [hp]
      exact (endP_spec _ _ _).2.2.2.2.2.2
    have hvars : p.vars.toList = plainWs lamS ++ [Weight.atZero 3] := by
      rw [hp, (endP_spec _ _ _).1, List.map_append, hms, hy]
      try rfl
    have h3 : ∀ w ∈ plainWs lamS, w.d = 3 := fun w hw => by
      unfold plainWs at hw
      obtain rfl := List.eq_of_mem_replicate hw
      rfl
    have hl : (plainWs lamS).length = lamS := List.length_replicate
    have hw := win_three p _ 2 h3 hvars
    rw [hl] at hw
    obtain ⟨s1, n1, q1⟩ := run_same (show Sized ({ F with
      next := F.next + 1 + 2 * lamS + 2 + (2 + (1 + P.y.LamM) + NCLp) } : Fork) from hF) r1
    obtain ⟨s2, n2, q2⟩ := run_same s1 r2
    have n1' : G1.next = F.next + 1 + 2 * lamS + 2 + (2 + (1 + P.y.LamM) + NCLp) := n1
    refine ⟨s2, ⟨by omega, fun j hj => ?_⟩⟩
    have a : SameAt F G1 j := q1 j (by omega)
    have b : SameAt G1 G j := q2 j (by
      rw [Array.size_replicate, hfirst]
      omega)
    exact a.trans b⟩

instance (P : Pub) (H : Heard) (K : HeardStack) : Spares (hearGated engFl P H K) := by
  unfold hearGated; spares

instance (P : Pub) (hp : HPlan2) (g : ℕ) (fo : Forest.Heard) : Spares (hear engFl P hp g fo) := by
  unfold hear; spares

/-- **WHERE K4's HEARING RETURNS, from a ledger with arrays of the right sizes, NOTHING HAS TURNED
UNDER A SLOT BELOW THE LEDGER's NEXT IN FRONT, OR FROM ITS NEXT BEHIND ON.** -/
theorem hear_fresh {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork}
    {t u : Tape} (hF : Sized F) (h : hear engFl P hp g fo F t = some (o, G, u)) : Fresh F G := by
  have i : Spares (hear engFl P hp g fo) := inferInstance
  exact (i.fresh h hF).2

end OnBytes.Desc.First.K4.Slots

#print axioms OnBytes.Desc.First.K4.Slots.win_le
#print axioms OnBytes.Desc.First.K4.Slots.tsc_win
#print axioms OnBytes.Desc.First.K4.Slots.hear_fresh
