-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/ZeroFl.lean: ITS FORM FIRST: ONE NEW CLASS (`StaysZ`), 35 INSTANCES OF THAT CLASS AND
NO OTHER, ONE LOCAL MACRO ("staysZ"): AS Johnson/Desc/First/Link/Law/FlLooks.lean HAS THEM FOR ITS
CLASS Stays. THE ROUTINES ON THE LEDGER THAT K4's HEARING AND THE MERGE CALL LEAVE THE ROWS' FIRST
COLUMNS. MADE BY PROGRAM FROM THE LIBRARY's Johnson/Desc/First/Link/Law/FlLooks.lean, WITH THE ROWS'
FIRST COLUMNS (`l0s`, Johnson/P1K8R/ZeroFrame.lean) IN THE PLACE OF THE ARRAYS' LOOKS AND
`KeepsZero` IN THE PLACE OF KeepsLooks: every declaration of that file that names the looks, or
leans on one that does, under a new name; the others are called where they lie. None of the
library's goals. No prover stands in it; nothing on completeness, soundness or hiding.

  `SameL0 F G`   G has the first columns of F
  `sameL0_frame`, `push_l0s`, `lin_l0s`, `hideRun_l0s`   the ground: whatever keeps treesFrame; the
      adding of a form, of a claim; a run of hidings
  `StaysZ x`   wherever x returns, the ledger that it leaves has the first columns of the one that
      it was handed; its instances walk the routines' texts
  `SameL0.refl`, `SameL0.trans`, `StaysZ.of_same`, `StaysZ.bind`, `StaysZ.change`   the plumbing
  `staysZ_foldlM`, `staysZ_mapM_list`, `staysZ_mapM_array`   folds
  `staysZ_levelRounds`, `staysZ_tscLoop`, `staysZ_wsForkRounds`   three loops, by induction
Limits. On what a routine leaves WHERE IT RETURNS: nothing on whether it returns. Nothing on any
reached state.

-/
import Johnson.P1K8R.ZeroShims
import Johnson.Desc.First.Link.Law.FlLooks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.FlL
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Desc.First.Grow (some_triple bind_some)
open OnBytes.Desc.First.K4 (hideRun_core)
open P1K8 (l0At AllZero l0s ZeroInv KeepsZero allZero_map allZero_trees allZero_frame l0s_of_frame
  l0s_of_sums l0s_rows_map l0s_rows_modify allZero_laid allZero_start fill_l0s allZero_fill
  allZero_rests kz_refl kz_trans kz_of_cases kz_same kz_none zeroInv_none kz_trees)

variable {α β γ : Type}

/-- G has the first columns of F. -/
def SameL0 (F G : Fork) : Prop := G.trees.map l0s = F.trees.map l0s

theorem SameL0.refl (F : Fork) : SameL0 F F := rfl

theorem SameL0.trans {F G H : Fork} (a : SameL0 F G) (b : SameL0 G H) : SameL0 F H :=
  Eq.trans b a

theorem sameL0_frame {F G : Fork} (h : treesFrame G.trees = treesFrame F.trees) :
    SameL0 F G := l0s_of_frame _ _ h

/-- Adding w times a form to the one equation. -/
theorem push_l0s {F G : Fork} {w : E} {a : Aff} (h : F.push w a = some G) : SameL0 F G := by
  unfold Fork.push at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · rename_i trees' LS' h1 h2
      have hG := Option.some.inj h
      subst hG
      rw [← Array.foldlM_toList] at h1
      exact sameL0_frame (pushEnts_frame w _ _ _ h1)
    · simp at h

/-- The adding of a claim. -/
theorem lin_l0s {F G : Fork} {f : Aff} (h : F.lin f = some G) : SameL0 F G := by
  unfold Fork.lin at h
  cases hk : F.kap with
  | none => simp [hk] at h
  | some x =>
    obtain ⟨k, F1⟩ := x
    rw [hk] at h
    have h2 : F1.push k f = some G := by simpa using h
    obtain ⟨_, hF1, _, _⟩ := Fork.kap_spec F F1 k hk
    have htr : F1.trees = F.trees := by rw [hF1]
    have e := push_l0s h2
    unfold SameL0 at e ⊢
    rw [e, htr]

/-- A run of hidings. -/
theorem hideRun_l0s {F G : Fork} {j : ℕ} {v : Array E} {c : E}
    (h : F.hideRun j v c = some G) : SameL0 F G := by
  unfold SameL0
  rw [(hideRun_core h).trees]

/-! ### The class -/

/-- Wherever x returns, the ledger that it leaves has the first columns of the one that it was
handed. -/
class StaysZ (x : Fl α) : Prop where
  same : ∀ {F : Fork} {t : Tape} {a : α} {G : Fork} {u : Tape}, x F t = some (a, G, u) →
    SameL0 F G

/-- A function that leaves the ledger as it is. -/
theorem StaysZ.of_same {x : Fl α}
    (h : ∀ (F : Fork) (t : Tape) (a : α) (G : Fork) (u : Tape), x F t = some (a, G, u) → F = G) :
    StaysZ x :=
  ⟨fun {F t a G u} e => by
    obtain rfl := h F t a G u e
    exact SameL0.refl F⟩

instance staysZ_pure (a : α) : StaysZ (pure a : Fl α) :=
  StaysZ.of_same fun _ _ _ _ _ e => (some_triple.mp e).2.1

/-- One function after another. -/
theorem StaysZ.bind {x : Fl α} {f : α → Fl β} (hx : StaysZ x) (hf : ∀ a, StaysZ (f a)) :
    StaysZ (x >>= f) :=
  ⟨fun e => by
    obtain ⟨a, G, u, h1, h2⟩ := bind_some.mp e
    exact (hx.same h1).trans ((hf a).same h2)⟩

instance staysZ_bind (x : Fl α) (f : α → Fl β) [StaysZ x] [∀ a, StaysZ (f a)] : StaysZ (x >>= f) :=
  StaysZ.bind inferInstance inferInstance

instance staysZ_map (g : α → β) (x : Fl α) [StaysZ x] : StaysZ (g <$> x) := by
  rw [map_eq_pure_bind]
  infer_instance

instance staysZ_ite (p : Prop) [Decidable p] (x y : Fl α) [StaysZ x] [StaysZ y] :
    StaysZ (if p then x else y) := by
  split <;> infer_instance

/-- The function that always refuses. -/
instance staysZ_none : StaysZ (fun _ _ => none : Fl α) := ⟨fun e => by simp at e⟩

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
local macro "staysZ" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine StaysZ.bind ?_ ?_
    | intro _
    | split)

/-! ### Folds -/

theorem staysZ_foldlM {f : β → γ → Fl β} (hf : ∀ s a, StaysZ (f s a)) :
    ∀ (l : List γ) (s : β), StaysZ (l.foldlM f s)
  | [], s => by
    rw [List.foldlM_nil]
    infer_instance
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact StaysZ.bind (hf s a) fun s' => staysZ_foldlM hf l s'

theorem staysZ_mapM_list {f : α → Fl β} (hf : ∀ a, StaysZ (f a)) : ∀ l : List α, StaysZ (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    infer_instance
  | a :: l => by
    rw [List.mapM_cons]
    exact StaysZ.bind (hf a) fun _ => StaysZ.bind (staysZ_mapM_list hf l) fun _ => inferInstance

theorem staysZ_mapM_array {f : α → Fl β} (hf : ∀ a, StaysZ (f a)) (l : Array α) :
    StaysZ (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  haveI := staysZ_mapM_list hf l.toList
  infer_instance

/-! ### The steps -/

instance staysZ_must (b : Bool) : StaysZ (Fl.must b) :=
  StaysZ.of_same fun F t a G u e => by
    unfold Fl.must at e
    split at e
    · exact (some_triple.mp e).2.1
    · simp at e

instance staysZ_need (x : Option α) : StaysZ (Fl.need x) :=
  StaysZ.of_same fun F t a G u e => by
    unfold Fl.need at e
    cases x with
    | none => simp at e
    | some y => exact (some_triple.mp e).2.1

instance staysZ_ask (f : Fork → Option α) : StaysZ (Fl.ask f) :=
  StaysZ.of_same fun F t a G u e => by
    unfold Fl.ask at e
    cases h : f F with
    | none => simp [h] at e
    | some y =>
      rw [h] at e
      exact (some_triple.mp e).2.1

instance staysZ_onTape (g : Tape → Option (α × Tape)) : StaysZ (Fl.onTape g) :=
  StaysZ.of_same fun F t a G u e => by
    unfold Fl.onTape at e
    cases h : g t with
    | none => simp [h] at e
    | some y =>
      rw [h] at e
      exact (some_triple.mp e).2.1

/-- A step on the ledger that leaves the first columns. -/
theorem StaysZ.change {f : Fork → Option Fork} (h : ∀ F G, f F = some G → SameL0 F G) :
    StaysZ (Fl.change f) :=
  ⟨fun {F t a G u} e => by
    unfold Fl.change at e
    cases hf : f F with
    | none => simp [hf] at e
    | some H =>
      rw [hf] at e
      obtain rfl := (some_triple.mp e).2.1
      exact h F H hf⟩

instance staysZ_takeSlots (n : Nat) : StaysZ (Fl.takeSlots n) :=
  ⟨fun {F t a G u} e => by
    obtain rfl := (some_triple.mp e).2.1
    exact SameL0.refl F⟩

instance staysZ_hideRun (j : Nat) (v : Array E) (c : E) :
    StaysZ (Fl.change fun F => F.hideRun j v c) :=
  StaysZ.change fun _ _ h => hideRun_l0s h

instance staysZ_lin (a : Aff) : StaysZ (Fl.change fun F => F.lin a) :=
  StaysZ.change fun _ _ h => lin_l0s h

instance staysZ_read (n : Nat) : StaysZ (Fl.read n) := by unfold Fl.read; infer_instance
instance staysZ_readSum : StaysZ Fl.readSum := by unfold Fl.readSum; infer_instance
instance staysZ_answer (r : RoundName) : StaysZ (Fl.answer r) := by unfold Fl.answer; infer_instance
instance staysZ_point (r : RoundName) (n : Nat) : StaysZ (Fl.point r n) := by
  unfold Fl.point; infer_instance
instance staysZ_batch (n : Nat) : StaysZ (Fl.batch n) := by unfold Fl.batch; infer_instance
instance staysZ_empty (r : RoundName) : StaysZ (Fl.empty r) := by unfold Fl.empty; infer_instance
instance staysZ_shown (j : Nat) : StaysZ (Fl.shown j) := by unfold Fl.shown; infer_instance
instance staysZ_publicPart (a : Aff) : StaysZ (Fl.publicPart a) := by
  unfold Fl.publicPart; infer_instance

/-! ### Hidden values and the masked sumcheck -/

instance staysZ_claimsIn (n : Nat) : StaysZ (Fl.claimsIn n) := by unfold Fl.claimsIn; staysZ
instance staysZ_pscBeginAt (x : E) : StaysZ (Fl.pscBeginAt x) := by unfold Fl.pscBeginAt; staysZ
instance staysZ_pscBegin (C : Aff) : StaysZ (Fl.pscBegin C) := by unfold Fl.pscBegin; staysZ

instance staysZ_pscRound (p : Psc) (w : OnBytes.Psc.Weight) (draw : Tape → Option (E × Tape)) :
    StaysZ (Fl.pscRound p w draw) := by
  unfold Fl.pscRound; staysZ

instance staysZ_roundIn (form : RoundForm) (p : Psc) (z : E) (d : Nat) :
    StaysZ (Fl.roundIn form p z d) := by
  unfold Fl.roundIn; staysZ

instance staysZ_pscEnds (p : Psc) (d n : Nat) : StaysZ (Fl.pscEnds p d n) := by
  unfold Fl.pscEnds; staysZ

instance staysZ_pscRow (p : Psc) (S0 : E) (kept : Aff) : StaysZ (Fl.pscRow p S0 kept) := by
  unfold Fl.pscRow; staysZ

theorem staysZ_levelRounds (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (r : Array E) (p :
    Psc),
    StaysZ (Fl.levelRounds mu rho order r p)
  | [], r, p => by
    unfold Fl.levelRounds
    infer_instance
  | v :: order, r, p => by
    unfold Fl.levelRounds
    refine StaysZ.bind inferInstance fun _ => ?_
    refine StaysZ.bind inferInstance fun x => ?_
    obtain ⟨x, p'⟩ := x
    exact staysZ_levelRounds mu rho order _ p'

instance (mu : Nat) (rho : Array E) (order : List Nat) (r : Array E) (p : Psc) :
    StaysZ (Fl.levelRounds mu rho order r p) := staysZ_levelRounds mu rho order r p

instance staysZ_levelIn (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    StaysZ (Fl.levelIn mu rho C order) := by
  unfold Fl.levelIn; staysZ

theorem staysZ_tscLoop : ∀ (zs : List E) (r : Array E) (p : Psc), StaysZ (Fl.tscLoop zs r p)
  | [], r, p => by
    unfold Fl.tscLoop
    infer_instance
  | z :: zs, r, p => by
    unfold Fl.tscLoop
    refine StaysZ.bind inferInstance fun x => ?_
    obtain ⟨x, p'⟩ := x
    exact staysZ_tscLoop zs _ p'

instance (zs : List E) (r : Array E) (p : Psc) : StaysZ (Fl.tscLoop zs r p) := staysZ_tscLoop zs r p

instance staysZ_tscRounds (P : Array E) (lt : Nat) : StaysZ (Fl.tscRounds P lt) := by
  unfold Fl.tscRounds; staysZ

instance staysZ_tscIn (P : Array E) (lt n d : Nat) : StaysZ (Fl.tscIn P lt n d) := by
  unfold Fl.tscIn; staysZ

/-! ### The merge of the claims on the weights -/

theorem staysZ_wsForkRounds : ∀ (n : Nat) (rm : Array E) (p : Psc), StaysZ (Fl.wsForkRounds n rm p)
  | 0, rm, p => by
    unfold Fl.wsForkRounds
    infer_instance
  | n + 1, rm, p => by
    unfold Fl.wsForkRounds
    refine StaysZ.bind inferInstance fun x => ?_
    obtain ⟨r, p'⟩ := x
    exact staysZ_wsForkRounds n _ p'

instance (n : Nat) (rm : Array E) (p : Psc) : StaysZ (Fl.wsForkRounds n rm p) :=
  staysZ_wsForkRounds n rm p

instance staysZ_wsForkMerge (lk : Nat) (sv : Array Nat) : StaysZ (Fl.wsForkMerge lk sv) := by
  unfold Fl.wsForkMerge; staysZ

instance staysZ_flatForkEnd (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) :
    StaysZ (flatForkEnd lay cl sv) := by
  unfold flatForkEnd; staysZ

end VerifiableInference.Desc.LinkJoin.FlL

#print axioms VerifiableInference.Desc.LinkJoin.FlL.SameL0.refl
#print axioms VerifiableInference.Desc.LinkJoin.FlL.SameL0.trans
#print axioms VerifiableInference.Desc.LinkJoin.FlL.sameL0_frame
#print axioms VerifiableInference.Desc.LinkJoin.FlL.push_l0s
#print axioms VerifiableInference.Desc.LinkJoin.FlL.lin_l0s
#print axioms VerifiableInference.Desc.LinkJoin.FlL.hideRun_l0s
#print axioms VerifiableInference.Desc.LinkJoin.FlL.StaysZ.of_same
#print axioms VerifiableInference.Desc.LinkJoin.FlL.StaysZ.bind
#print axioms VerifiableInference.Desc.LinkJoin.FlL.staysZ_foldlM
#print axioms VerifiableInference.Desc.LinkJoin.FlL.staysZ_mapM_list
#print axioms VerifiableInference.Desc.LinkJoin.FlL.staysZ_mapM_array
#print axioms VerifiableInference.Desc.LinkJoin.FlL.StaysZ.change
#print axioms VerifiableInference.Desc.LinkJoin.FlL.staysZ_levelRounds
#print axioms VerifiableInference.Desc.LinkJoin.FlL.staysZ_tscLoop
#print axioms VerifiableInference.Desc.LinkJoin.FlL.staysZ_wsForkRounds
