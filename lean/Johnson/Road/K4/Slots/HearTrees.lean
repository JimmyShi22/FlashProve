-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Slots/HearTrees.lean: K4's HEARING, FROM A LEDGER WITH ARRAYS OF THE RIGHT SIZES,
TURNS FOUR OF THE LEDGER's FIFTEEN FIELDS AND NO OTHER: the next free slot's number, and the three
arrays under the slots (what is shown, the factor, the mark). The arrays that the claims read
(trees), the number of slots, the one equation's coefficients and constant, the number of claims,
the batching element with its mark, the plan's number of claims, the marks of the weights handed
out, the door's mark AND THE LIST OF OWED CLAIMS are the ledger's in front. Definitions, statements
and proofs.

Why it is wanted. Later, Fresh and Spares (OnBytes/Tie/Pv/Psc/PscLater.lean,
Johnson/Road/K4/Slots/HearSpares.lean) speak of the slots alone; Core
(Johnson/Desc/First/K4/RunsCore.lean) is shown of the two runs of claims alone.

  `Kept F G`: FirstPass F G (OnBytes/Tie/Pv/Psc/PscLater.lean: G is F but for next, vp,
    mf, gotF, owed), and G.owed = F.owed.
  `Passes x`: a class: wherever x returns from a ledger with arrays of the right sizes, the ledger
    that it leaves has them too and is Kept. Closed under pure, bind, if, a map. The walk and the
    order of the instances are HearSpares.lean's; the three places of the hearing that lay a window
    are treated whole, off the same laws.
  `kept_run`, `kept_run0`: a run of values put under slots.
  **`hear_kept`**: the statement on top. **`hear_trees`**: G.trees = F.trees. `hear_rest`: the ten
    other fields, one by one.
No new argument: the hearing's chain of calls, walked once more with another relation.
**Limits.** ONE DIRECTION, FROM A RETURN, FROM A LEDGER WITH ARRAYS OF THE RIGHT SIZES (hF: a
premise). Only the hearing: of the two runs of claims behind it see Core. WHAT THE HEARING DOES
TURN: next, vp, mf, gotF: of these see Later, Fresh, Fills7. Nothing on soundness. K04_law, the law
of K4's block itself, IS NOT PROVED.


-/
import Johnson.Road.K4.Slots.HearFills
import OnBytes.Tie.Pv.Lay.Slots

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Slots

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own Heard HeardStack Env)
open OnBytes.PscRun (Sized Same FirstPass hideRun_ok)
open OnBytes.Psc (Weight)
open OnBytes.Desc.First.Grow (some_triple bind_some)
open OnBytes.Desc.First.P1 (levelIn_heard tscIn_heard claimsIn_spec pscEnds_spec pscRow_spec)

variable {α β γ : Type}

/-! ### The relation -/

/-- G is F but for the next free slot's number and what lies under the slots. -/
def Kept (F G : Fork) : Prop := FirstPass F G ∧ G.owed = F.owed

theorem Kept.refl (F : Fork) : Kept F F := ⟨FirstPass.refl F, rfl⟩

theorem Kept.trans {F G H : Fork} (h1 : Kept F G) (h2 : Kept G H) : Kept F H :=
  ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩

/-- A run of values put under slots. -/
theorem kept_run0 {F G : Fork} {first : ℕ} {v : Array E} {k : E} (hF : Sized F)
    (h : F.hideRun first v k = some G) : Sized G ∧ Kept F G := by
  obtain ⟨a, s, _, _⟩ := hideRun_ok F G first v k hF h
  refine ⟨s, a.firstPass, ?_⟩
  unfold Same at a
  rw [a]

/-- Slots are taken, up to m, and a run of values is put under some of them. -/
theorem kept_run {F G : Fork} {m first : ℕ} {v : Array E} {k : E} (hF : Sized F)
    (h : ({ F with next := m } : Fork).hideRun first v k = some G) : Sized G ∧ Kept F G := by
  obtain ⟨s, q⟩ := kept_run0 (show Sized ({ F with next := m } : Fork) from hF) h
  exact ⟨s, Kept.trans (⟨rfl, rfl⟩ : Kept F { F with next := m }) q⟩

/-! ### The class -/

/-- Wherever x returns from a ledger with arrays of the right sizes, the ledger that it leaves has
them too, and x has turned nothing but the next free slot's number and what lies under the slots. -/
class Passes (x : Fl α) : Prop where
  pass : ∀ {F : Fork} {t : Tape} {a : α} {G : Fork} {u : Tape}, x F t = some (a, G, u) →
    Sized F → Sized G ∧ Kept F G

/-- A function that leaves the ledger as it is. -/
theorem Passes.of_same {x : Fl α}
    (h : ∀ (F : Fork) (t : Tape) (a : α) (G : Fork) (u : Tape), x F t = some (a, G, u) → F = G) :
    Passes x :=
  ⟨fun {F t a G u} e hF => by
    obtain rfl := h F t a G u e
    exact ⟨hF, Kept.refl F⟩⟩

instance passes_pure (a : α) : Passes (pure a : Fl α) :=
  Passes.of_same fun _ _ _ _ _ e => (some_triple.mp e).2.1

/-- One function after another. -/
theorem Passes.bind {x : Fl α} {f : α → Fl β} (hx : Passes x) (hf : ∀ a, Passes (f a)) :
    Passes (x >>= f) :=
  ⟨fun e hF => by
    obtain ⟨a, G, u, h1, h2⟩ := bind_some.mp e
    obtain ⟨s1, f1⟩ := hx.pass h1 hF
    obtain ⟨s2, f2⟩ := (hf a).pass h2 s1
    exact ⟨s2, f1.trans f2⟩⟩

instance passes_bind (x : Fl α) (f : α → Fl β) [Passes x] [∀ a, Passes (f a)] :
    Passes (x >>= f) :=
  Passes.bind inferInstance inferInstance

instance passes_map (g : α → β) (x : Fl α) [Passes x] : Passes (g <$> x) := by
  rw [map_eq_pure_bind]
  infer_instance

instance passes_ite (p : Prop) [Decidable p] (x y : Fl α) [Passes x] [Passes y] :
    Passes (if p then x else y) := by
  split <;> infer_instance

/-- The function that always refuses. -/
instance passes_none : Passes (fun _ _ => none : Fl α) := ⟨fun e => by simp at e⟩

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
local macro "passes" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine Passes.bind ?_ ?_
    | intro _
    | split)

/-! ### The steps -/

instance passes_must (b : Bool) : Passes (Fl.must b) :=
  Passes.of_same fun _ _ _ _ _ e => (P1.must_some.mp e).2.1

instance passes_need (x : Option α) : Passes (Fl.need x) :=
  Passes.of_same fun _ _ _ _ _ e => (P1.need_some.mp e).2.1

instance passes_ask (f : Fork → Option α) : Passes (Fl.ask f) :=
  Passes.of_same fun _ _ _ _ _ e => (P1.ask_some.mp e).2.1

instance passes_onTape (g : Tape → Option (α × Tape)) : Passes (Fl.onTape g) :=
  Passes.of_same fun _ _ _ _ _ e => (P1.onTape_some.mp e).2

/-- Taking slots. -/
instance passes_takeSlots (n : ℕ) : Passes (Fl.takeSlots n) :=
  ⟨fun {F t a G u} e hF => by
    obtain ⟨_, rfl, _⟩ := P1.takeSlots_some.mp e
    exact ⟨hF, rfl, rfl⟩⟩

instance passes_read (n : ℕ) : Passes (Fl.read n) := by unfold Fl.read; infer_instance
instance passes_readSum : Passes Fl.readSum := by unfold Fl.readSum; infer_instance
instance passes_answer (r : RoundName) : Passes (Fl.answer r) := by
  unfold Fl.answer; infer_instance
instance passes_point (r : RoundName) (n : ℕ) : Passes (Fl.point r n) := by
  unfold Fl.point; infer_instance
instance passes_batch (n : ℕ) : Passes (Fl.batch n) := by unfold Fl.batch; infer_instance
instance passes_shown (j : ℕ) : Passes (Fl.shown j) := by unfold Fl.shown; infer_instance
instance passes_publicPart (a : Aff) : Passes (Fl.publicPart a) := by
  unfold Fl.publicPart; infer_instance

/-! ### Hidden values and the masked sumcheck, but for its claim -/

instance passes_claimsIn (n : ℕ) : Passes (Fl.claimsIn n) :=
  ⟨fun {F t j G u} h hF => by
    obtain ⟨_, v, hv, _, _, r⟩ := claimsIn_spec h
    exact kept_run hF r⟩

instance passes_pscBeginAt (x : E) : Passes (Fl.pscBeginAt x) := by
  unfold Fl.pscBeginAt; passes
instance passes_pscBegin (C : Aff) : Passes (Fl.pscBegin C) := by unfold Fl.pscBegin; passes

instance passes_pscRound (p : Psc) (w : Weight) (draw : Tape → Option (E × Tape)) :
    Passes (Fl.pscRound p w draw) := by
  unfold Fl.pscRound; passes

instance passes_roundIn (form : RoundForm) (p : Psc) (z : E) (d : ℕ) :
    Passes (Fl.roundIn form p z d) := by
  unfold Fl.roundIn; passes

instance passes_pscEnds (p : Psc) (d n : ℕ) : Passes (Fl.pscEnds p d n) :=
  ⟨fun {F t x G u} h hF => by
    obtain ⟨e, p'⟩ := x
    obtain ⟨_, _, _, v, _, hv, _, he, r⟩ := pscEnds_spec h
    exact kept_run hF r⟩

/-- A product layer. -/
instance passes_levelIn (mu : ℕ) (rho : Array E) (C : Aff) (order : List ℕ) :
    Passes (Fl.levelIn mu rho C order) :=
  ⟨fun {F t L G u} h hF => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, v, G1, hv, r1, _, r2⟩ :=
      levelIn_heard h
    obtain ⟨s1, q1⟩ := kept_run hF r1
    obtain ⟨s2, q2⟩ := kept_run0 s1 r2
    exact ⟨s2, q1.trans q2⟩⟩

/-- A token sumcheck. -/
instance passes_tscIn (P : Array E) (lt n d : ℕ) : Passes (Fl.tscIn P lt n d) :=
  ⟨fun {F t o G u} h hF => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, v, G0, r0, _, _, _, _, r1⟩ := tscIn_heard h
    obtain ⟨s0, q0⟩ := kept_run hF r0
    obtain ⟨s1, q1⟩ := kept_run s0 r1
    exact ⟨s1, q0.trans q1⟩⟩

/-! ### The merge of the claims on the weights -/

theorem passes_wsForkRounds : ∀ (n : ℕ) (rm : Array E) (p : Psc), Passes (Fl.wsForkRounds n rm p)
  | 0, rm, p => by
    unfold Fl.wsForkRounds
    infer_instance
  | n + 1, rm, p => by
    unfold Fl.wsForkRounds
    refine Passes.bind inferInstance fun x => ?_
    obtain ⟨r, p'⟩ := x
    exact passes_wsForkRounds n _ p'

instance (n : ℕ) (rm : Array E) (p : Psc) : Passes (Fl.wsForkRounds n rm p) :=
  passes_wsForkRounds n rm p

instance passes_wsForkMerge (lk : ℕ) (sv : Array ℕ) : Passes (Fl.wsForkMerge lk sv) := by
  unfold Fl.wsForkMerge; passes

instance passes_flatForkEnd (lay : WsLay) (cl : Array WsClaim) (sv : Array ℕ) :
    Passes (flatForkEnd lay cl sv) := by
  unfold flatForkEnd; passes

/-! ### The engine's fields that the hearing's open stretches call -/

instance (x : Option α) : Passes (engFl.get x) := inferInstanceAs (Passes (Fl.need x))
instance (b : Bool) : Passes (engFl.must b) := inferInstanceAs (Passes (Fl.must b))
instance (n : String) (b : Bool) : Passes (engFl.mustAs n b) := inferInstanceAs (Passes (Fl.must b))
instance (n : String) (b : Bool) : Passes (engFl.check n b) := inferInstanceAs (Passes (Fl.must b))

instance (r : RoundName) (n : ℕ) : Passes (engFl.point r n) :=
  inferInstanceAs (Passes (if r == .batSigma then (fun _ _ => none) else Fl.point r n))

instance (n : ℕ) : Passes (engFl.claimsIn n) := inferInstanceAs (Passes (Fl.claimsIn n))
instance (n : ℕ) : Passes (engFl.batch n) := inferInstanceAs (Passes (Fl.batch n))

instance (mu : ℕ) (rho : Array E) (C : Aff) (order : List ℕ) :
    Passes (engFl.levelIn mu rho C order) := inferInstanceAs (Passes (Fl.levelIn mu rho C order))

instance (P : Array E) (lt n d : ℕ) : Passes (engFl.tscIn P lt n d) :=
  inferInstanceAs (Passes (Fl.tscIn P lt n d))

instance (lay : WsLay) (cl : Array WsClaim) (sv : Array ℕ) :
    Passes (engFl.wsForkEnd lay cl sv) := inferInstanceAs (Passes (flatForkEnd lay cl sv))

/-! ### The parts of the hearing -/

instance (P : Pub) (g : ℕ) (fo : Forest.Heard) : Passes (hearNorms engFl P g fo) := by
  unfold hearNorms; passes

/-- The second token sumcheck with its claim. -/
instance (P : Pub) (H : Heard) : Passes (hearTerms engFl P H) :=
  ⟨fun {F t H' G u} h hF => by
    obtain ⟨tT, G1, u1, row, p', c, _, r, _⟩ := hearTerms_calls h
    obtain ⟨s1, q1⟩ := (inferInstance : Passes (Fl.tscIn _ _ _ _)).pass c hF
    obtain ⟨_, _, r2⟩ := pscRow_spec r
    obtain ⟨s2, q2⟩ := kept_run0 s1 r2
    exact ⟨s2, q1.trans q2⟩⟩

/-- The batched sumcheck. -/
instance (P : Pub) (v : Env) (H : Heard) (lamS NCLp : ℕ) :
    Passes (hearStack engFl P v H lamS NCLp) :=
  ⟨fun {F t K G u} h hF => by
    obtain ⟨x, mu0, eps, beta, T, rs, sentY, vals, w1, wY, wV, C, G1, ms, y, p, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, _, _, _, r1, _, r2⟩ := hearStack_tape h
    obtain ⟨s1, q1⟩ := kept_run hF r1
    obtain ⟨s2, q2⟩ := kept_run0 s1 r2
    exact ⟨s2, q1.trans q2⟩⟩

instance (P : Pub) (H : Heard) (K : HeardStack) : Passes (hearGated engFl P H K) := by
  unfold hearGated; passes

instance (P : Pub) (hp : HPlan2) (g : ℕ) (fo : Forest.Heard) : Passes (hear engFl P hp g fo) := by
  unfold hear; passes

variable {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork} {t u : Tape}

/-- **WHERE K4's HEARING RETURNS, from a ledger with arrays of the right sizes, IT HAS TURNED
NOTHING OF THE LEDGER BUT THE NEXT FREE SLOT's NUMBER AND WHAT LIES UNDER THE SLOTS.** -/
theorem hear_kept (hF : Sized F) (h : hear engFl P hp g fo F t = some (o, G, u)) : Kept F G := by
  have i : Passes (hear engFl P hp g fo) := inferInstance
  exact (i.pass h hF).2

/-- **Behind a return of the hearing from a ledger with arrays of the right sizes, the arrays that
the claims read are the ledger's in front.** -/
theorem hear_trees (hF : Sized F) (h : hear engFl P hp g fo F t = some (o, G, u)) :
    G.trees = F.trees := by
  have k := (hear_kept hF h).1
  unfold FirstPass at k
  rw [k]

/-- Behind such a return from such a ledger: the ten other fields that the hearing leaves. -/
theorem hear_rest (hF : Sized F) (h : hear engFl P hp g fo F t = some (o, G, u)) :
    G.ns = F.ns ∧ G.LS = F.LS ∧ G.c0 = F.c0 ∧ G.nClaim = F.nClaim ∧ G.theta = F.theta ∧
      G.thetaDrawnF = F.thetaDrawnF ∧ G.planClaimsF = F.planClaimsF ∧ G.kapMapF = F.kapMapF ∧
      G.doorShutF = F.doorShutF ∧ G.owed = F.owed := by
  obtain ⟨k, ko⟩ := hear_kept hF h
  unfold FirstPass at k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ko⟩ <;> rw [k]

end OnBytes.Desc.First.K4.Slots

#print axioms OnBytes.Desc.First.K4.Slots.kept_run0
#print axioms OnBytes.Desc.First.K4.Slots.kept_run
#print axioms OnBytes.Desc.First.K4.Slots.hear_kept
#print axioms OnBytes.Desc.First.K4.Slots.hear_trees
#print axioms OnBytes.Desc.First.K4.Slots.hear_rest
