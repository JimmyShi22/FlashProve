-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FlLooks.lean: THE PLAIN ENGINE's STEPS LEAVE THE LEDGER's ARRAYS' LOOKS
(Johnson/Desc/First/Link/Law/LooksAre.lean: kind, rows, columns, number of virtual rows). Wherever a
function of the type `Fl` (OnBytes/K/Kc) that is made of these steps returns, the ledger that it
leaves has the looks of the one that it was handed. Definitions, a class,
instances.

How. IT IS OnBytes/Desc/First/FlGrows.lean, INSTANCE FOR INSTANCE AND PROOF FOR PROOF, with "the
same
looks" in the place of "a later ledger" (made from that file's text by program; its monad's laws and
its two lemmas on what a step returns are called, not typed again). What differs: the three steps
that write the ledger: taking slots (the arrays are not touched) · a run of hidings
(`hideRun_core`, Johnson/Desc/First/K4/RunsCore.lean) · the adding of a claim (`lin_looks`, here:
the
weights' values alone turn: `pushEnt_frame`, OnBytes/Model/HideLaws.lean; NO PREMISE ON THE SIZES).
Main names: `SameLooks F G`; `push_looks`, `lin_looks`, `hideRun_looks`; the class `Stays x`; the
tactic `stays`; an instance for each step of FlGrows.lean.
Limits: one direction, from a return. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.LooksAre
import OnBytes.Desc.First.FlGrows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.FlL
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Desc.First.Grow (some_triple bind_some)
open OnBytes.Desc.First.K4 (hideRun_core)

variable {α β γ : Type}

/-- G has the looks of F. -/
def SameLooks (F G : Fork) : Prop := G.trees.map look = F.trees.map look

theorem SameLooks.refl (F : Fork) : SameLooks F F := rfl

theorem SameLooks.trans {F G H : Fork} (a : SameLooks F G) (b : SameLooks G H) : SameLooks F H :=
  Eq.trans b a

theorem sameLooks_frame {F G : Fork} (h : treesFrame G.trees = treesFrame F.trees) :
    SameLooks F G := by
  have e : ∀ tr : Array HTree, tr.map look = (treesFrame tr).map ofFrame := by
    intro tr
    unfold treesFrame
    rw [Array.map_map]
    congr 1
    funext X
    exact (look_frame X).symm
  unfold SameLooks
  rw [e, e, h]

theorem pushEnts_frame (w : E) : ∀ (l : List Ent) (tr tr' : Array HTree),
    l.foldlM (Fork.pushEnt w) tr = some tr' → treesFrame tr' = treesFrame tr
  | [], tr, tr', h => by
    obtain rfl : tr = tr' := Option.some.inj h
    rfl
  | x :: l, tr, tr', h => by
    rw [List.foldlM_cons] at h
    cases h1 : Fork.pushEnt w tr x with
    | none =>
      rw [h1] at h
      exact absurd h (by simp)
    | some t1 =>
      rw [h1] at h
      exact (pushEnts_frame w l t1 tr' h).trans (pushEnt_frame w tr t1 x h1)

/-- Adding w times a form to the one equation. -/
theorem push_looks {F G : Fork} {w : E} {a : Aff} (h : F.push w a = some G) : SameLooks F G := by
  unfold Fork.push at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · rename_i trees' LS' h1 h2
      have hG := Option.some.inj h
      subst hG
      rw [← Array.foldlM_toList] at h1
      exact sameLooks_frame (pushEnts_frame w _ _ _ h1)
    · simp at h

/-- The adding of a claim. -/
theorem lin_looks {F G : Fork} {f : Aff} (h : F.lin f = some G) : SameLooks F G := by
  unfold Fork.lin at h
  cases hk : F.kap with
  | none => simp [hk] at h
  | some x =>
    obtain ⟨k, F1⟩ := x
    rw [hk] at h
    have h2 : F1.push k f = some G := by simpa using h
    obtain ⟨_, hF1, _, _⟩ := Fork.kap_spec F F1 k hk
    have htr : F1.trees = F.trees := by rw [hF1]
    have e := push_looks h2
    unfold SameLooks at e ⊢
    rw [e, htr]

/-- A run of hidings. -/
theorem hideRun_looks {F G : Fork} {j : ℕ} {v : Array E} {c : E}
    (h : F.hideRun j v c = some G) : SameLooks F G := by
  unfold SameLooks
  rw [(hideRun_core h).trees]

/-! ### The class -/

/-- Wherever x returns, the ledger that it leaves has the looks of the one that it was handed. -/
class Stays (x : Fl α) : Prop where
  same : ∀ {F : Fork} {t : Tape} {a : α} {G : Fork} {u : Tape}, x F t = some (a, G, u) →
    SameLooks F G

/-- A function that leaves the ledger as it is. -/
theorem Stays.of_same {x : Fl α}
    (h : ∀ (F : Fork) (t : Tape) (a : α) (G : Fork) (u : Tape), x F t = some (a, G, u) → F = G) :
    Stays x :=
  ⟨fun {F t a G u} e => by
    obtain rfl := h F t a G u e
    exact SameLooks.refl F⟩

instance stays_pure (a : α) : Stays (pure a : Fl α) :=
  Stays.of_same fun _ _ _ _ _ e => (some_triple.mp e).2.1

/-- One function after another. -/
theorem Stays.bind {x : Fl α} {f : α → Fl β} (hx : Stays x) (hf : ∀ a, Stays (f a)) :
    Stays (x >>= f) :=
  ⟨fun e => by
    obtain ⟨a, G, u, h1, h2⟩ := bind_some.mp e
    exact (hx.same h1).trans ((hf a).same h2)⟩

instance stays_bind (x : Fl α) (f : α → Fl β) [Stays x] [∀ a, Stays (f a)] : Stays (x >>= f) :=
  Stays.bind inferInstance inferInstance

instance stays_map (g : α → β) (x : Fl α) [Stays x] : Stays (g <$> x) := by
  rw [map_eq_pure_bind]
  infer_instance

instance stays_ite (p : Prop) [Decidable p] (x y : Fl α) [Stays x] [Stays y] :
    Stays (if p then x else y) := by
  split <;> infer_instance

/-- The function that always refuses. -/
instance stays_none : Stays (fun _ _ => none : Fl α) := ⟨fun e => by simp at e⟩

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
macro "stays" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine Stays.bind ?_ ?_
    | intro _
    | split)

/-! ### Folds -/

theorem stays_foldlM {f : β → γ → Fl β} (hf : ∀ s a, Stays (f s a)) :
    ∀ (l : List γ) (s : β), Stays (l.foldlM f s)
  | [], s => by
    rw [List.foldlM_nil]
    infer_instance
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact Stays.bind (hf s a) fun s' => stays_foldlM hf l s'

theorem stays_mapM_list {f : α → Fl β} (hf : ∀ a, Stays (f a)) : ∀ l : List α, Stays (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    infer_instance
  | a :: l => by
    rw [List.mapM_cons]
    exact Stays.bind (hf a) fun _ => Stays.bind (stays_mapM_list hf l) fun _ => inferInstance

theorem stays_mapM_array {f : α → Fl β} (hf : ∀ a, Stays (f a)) (l : Array α) :
    Stays (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  haveI := stays_mapM_list hf l.toList
  infer_instance

/-! ### The steps -/

instance stays_must (b : Bool) : Stays (Fl.must b) :=
  Stays.of_same fun F t a G u e => by
    unfold Fl.must at e
    split at e
    · exact (some_triple.mp e).2.1
    · simp at e

instance stays_need (x : Option α) : Stays (Fl.need x) :=
  Stays.of_same fun F t a G u e => by
    unfold Fl.need at e
    cases x with
    | none => simp at e
    | some y => exact (some_triple.mp e).2.1

instance stays_ask (f : Fork → Option α) : Stays (Fl.ask f) :=
  Stays.of_same fun F t a G u e => by
    unfold Fl.ask at e
    cases h : f F with
    | none => simp [h] at e
    | some y =>
      rw [h] at e
      exact (some_triple.mp e).2.1

instance stays_onTape (g : Tape → Option (α × Tape)) : Stays (Fl.onTape g) :=
  Stays.of_same fun F t a G u e => by
    unfold Fl.onTape at e
    cases h : g t with
    | none => simp [h] at e
    | some y =>
      rw [h] at e
      exact (some_triple.mp e).2.1

/-- A step on the ledger that leaves the looks. -/
theorem Stays.change {f : Fork → Option Fork} (h : ∀ F G, f F = some G → SameLooks F G) :
    Stays (Fl.change f) :=
  ⟨fun {F t a G u} e => by
    unfold Fl.change at e
    cases hf : f F with
    | none => simp [hf] at e
    | some H =>
      rw [hf] at e
      obtain rfl := (some_triple.mp e).2.1
      exact h F H hf⟩

instance stays_takeSlots (n : Nat) : Stays (Fl.takeSlots n) :=
  ⟨fun {F t a G u} e => by
    obtain rfl := (some_triple.mp e).2.1
    exact SameLooks.refl F⟩

instance stays_hideRun (j : Nat) (v : Array E) (c : E) :
    Stays (Fl.change fun F => F.hideRun j v c) :=
  Stays.change fun _ _ h => hideRun_looks h

instance stays_lin (a : Aff) : Stays (Fl.change fun F => F.lin a) :=
  Stays.change fun _ _ h => lin_looks h

instance stays_read (n : Nat) : Stays (Fl.read n) := by unfold Fl.read; infer_instance
instance stays_readSum : Stays Fl.readSum := by unfold Fl.readSum; infer_instance
instance stays_answer (r : RoundName) : Stays (Fl.answer r) := by unfold Fl.answer; infer_instance
instance stays_point (r : RoundName) (n : Nat) : Stays (Fl.point r n) := by
  unfold Fl.point; infer_instance
instance stays_batch (n : Nat) : Stays (Fl.batch n) := by unfold Fl.batch; infer_instance
instance stays_empty (r : RoundName) : Stays (Fl.empty r) := by unfold Fl.empty; infer_instance
instance stays_shown (j : Nat) : Stays (Fl.shown j) := by unfold Fl.shown; infer_instance
instance stays_publicPart (a : Aff) : Stays (Fl.publicPart a) := by
  unfold Fl.publicPart; infer_instance

/-! ### Hidden values and the masked sumcheck -/

instance stays_claimsIn (n : Nat) : Stays (Fl.claimsIn n) := by unfold Fl.claimsIn; stays
instance stays_pscBeginAt (x : E) : Stays (Fl.pscBeginAt x) := by unfold Fl.pscBeginAt; stays
instance stays_pscBegin (C : Aff) : Stays (Fl.pscBegin C) := by unfold Fl.pscBegin; stays

instance stays_pscRound (p : Psc) (w : OnBytes.Psc.Weight) (draw : Tape → Option (E × Tape)) :
    Stays (Fl.pscRound p w draw) := by
  unfold Fl.pscRound; stays

instance stays_roundIn (form : RoundForm) (p : Psc) (z : E) (d : Nat) :
    Stays (Fl.roundIn form p z d) := by
  unfold Fl.roundIn; stays

instance stays_pscEnds (p : Psc) (d n : Nat) : Stays (Fl.pscEnds p d n) := by
  unfold Fl.pscEnds; stays

instance stays_pscRow (p : Psc) (S0 : E) (kept : Aff) : Stays (Fl.pscRow p S0 kept) := by
  unfold Fl.pscRow; stays

theorem stays_levelRounds (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (r : Array E) (p : Psc),
    Stays (Fl.levelRounds mu rho order r p)
  | [], r, p => by
    unfold Fl.levelRounds
    infer_instance
  | v :: order, r, p => by
    unfold Fl.levelRounds
    refine Stays.bind inferInstance fun _ => ?_
    refine Stays.bind inferInstance fun x => ?_
    obtain ⟨x, p'⟩ := x
    exact stays_levelRounds mu rho order _ p'

instance (mu : Nat) (rho : Array E) (order : List Nat) (r : Array E) (p : Psc) :
    Stays (Fl.levelRounds mu rho order r p) := stays_levelRounds mu rho order r p

instance stays_levelIn (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    Stays (Fl.levelIn mu rho C order) := by
  unfold Fl.levelIn; stays

theorem stays_tscLoop : ∀ (zs : List E) (r : Array E) (p : Psc), Stays (Fl.tscLoop zs r p)
  | [], r, p => by
    unfold Fl.tscLoop
    infer_instance
  | z :: zs, r, p => by
    unfold Fl.tscLoop
    refine Stays.bind inferInstance fun x => ?_
    obtain ⟨x, p'⟩ := x
    exact stays_tscLoop zs _ p'

instance (zs : List E) (r : Array E) (p : Psc) : Stays (Fl.tscLoop zs r p) := stays_tscLoop zs r p

instance stays_tscRounds (P : Array E) (lt : Nat) : Stays (Fl.tscRounds P lt) := by
  unfold Fl.tscRounds; stays

instance stays_tscIn (P : Array E) (lt n d : Nat) : Stays (Fl.tscIn P lt n d) := by
  unfold Fl.tscIn; stays

/-! ### The merge of the claims on the weights -/

theorem stays_wsForkRounds : ∀ (n : Nat) (rm : Array E) (p : Psc), Stays (Fl.wsForkRounds n rm p)
  | 0, rm, p => by
    unfold Fl.wsForkRounds
    infer_instance
  | n + 1, rm, p => by
    unfold Fl.wsForkRounds
    refine Stays.bind inferInstance fun x => ?_
    obtain ⟨r, p'⟩ := x
    exact stays_wsForkRounds n _ p'

instance (n : Nat) (rm : Array E) (p : Psc) : Stays (Fl.wsForkRounds n rm p) :=
  stays_wsForkRounds n rm p

instance stays_wsForkMerge (lk : Nat) (sv : Array Nat) : Stays (Fl.wsForkMerge lk sv) := by
  unfold Fl.wsForkMerge; stays

instance stays_flatForkEnd (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) :
    Stays (flatForkEnd lay cl sv) := by
  unfold flatForkEnd; stays

end VerifiableInference.Desc.LinkJoin.FlL
