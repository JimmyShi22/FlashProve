-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FlSlots.lean: THE PLAIN FUNCTIONS ON A LEDGER AND A TAPE.
ONE OF FOURTEEN FILES THAT CARRY "THE OPEN LEDGER's TWO NUMBERS" (how many slots it has: ns; how
many coefficients its list LS has) ALONG THE FIRST CHAIN: `SlotsInv nsOf s`: where a ledger and a
link are open, the two numbers are the plan's nsOf at that link's number. Their top:
Johnson/LPFK9R/SlotsSeat.lean.
WHOSE: THE WALK COMES FROM FlLooks.lean, beside this file: that file's
theorems on the arrays' looks, CARRIED OVER BY PROGRAM to the two numbers, name by name (…looks… ↦
…slots…; else a letter S behind the name), and righted by hand where the ground fact is another.
That file is imported for what it holds that does not speak of looks.
Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.FlLooks
import Johnson.Desc.First.Link.Law.LooksAre
import Johnson.Desc.First.Link.Law.SlotsAre
import OnBytes.Desc.First.FlGrows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.FlS
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Desc.First.Grow (some_triple bind_some)
open OnBytes.Desc.First.K4 (hideRun_core)

variable {α β γ : Type}

/-- G has the two numbers of F. -/
def SameSlots (F G : Fork) : Prop := sl G = sl F

theorem SameSlots.refl (F : Fork) : SameSlots F F := rfl

theorem SameSlots.trans {F G H : Fork} (a : SameSlots F G) (b : SameSlots G H) : SameSlots F H :=
  Eq.trans b a

theorem pushSlots_size (w : E) (ns : ℕ) : ∀ (l : List (ℕ × E)) (a b : Array E),
    l.foldlM (Fork.pushSlot w ns) a = some b → b.size = a.size
  | [], a, b, h => by
    obtain rfl : a = b := Option.some.inj h
    rfl
  | x :: l, a, b, h => by
    rw [List.foldlM_cons] at h
    cases h1 : Fork.pushSlot w ns a x with
    | none =>
      rw [h1] at h
      exact absurd h (by simp)
    | some a1 =>
      rw [h1] at h
      have e1 : a1.size = a.size := by
        unfold Fork.pushSlot at h1
        split at h1
        · rw [← Option.some.inj h1]
          simp
        · cases h1
      exact (pushSlots_size w ns l a1 b h).trans e1

/-- Adding w times a form to the one equation. -/
theorem push_slots {F G : Fork} {w : E} {a : Aff} (h : F.push w a = some G) : SameSlots F G := by
  unfold Fork.push at h
  split at h
  · simp at h
  · dsimp only at h
    split at h
    · rename_i trees' LS' h1 h2
      have hG := Option.some.inj h
      subst hG
      rw [← Array.foldlM_toList] at h2
      show (F.ns, LS'.size) = (F.ns, F.LS.size)
      rw [pushSlots_size w F.ns _ _ _ h2]
    · simp at h

/-- The adding of a claim. -/
theorem lin_slots {F G : Fork} {f : Aff} (h : F.lin f = some G) : SameSlots F G := by
  unfold Fork.lin at h
  cases hk : F.kap with
  | none => simp [hk] at h
  | some x =>
    obtain ⟨k, F1⟩ := x
    rw [hk] at h
    have h2 : F1.push k f = some G := by simpa using h
    obtain ⟨_, hF1, _, _⟩ := Fork.kap_spec F F1 k hk
    have htr : sl F1 = sl F := by
      rw [hF1]
      rfl
    have e := push_slots h2
    unfold SameSlots at e ⊢
    rw [e, htr]

/-- A run of hidings. -/
theorem hideRun_slots {F G : Fork} {j : ℕ} {v : Array E} {c : E}
    (h : F.hideRun j v c = some G) : SameSlots F G := by
  exact sl_core (hideRun_core h)

/-! ### The class -/

/-- Wherever x returns, the ledger that it leaves has the two numbers of the one that it was handed.
-/
class StaysS (x : Fl α) : Prop where
  same : ∀ {F : Fork} {t : Tape} {a : α} {G : Fork} {u : Tape}, x F t = some (a, G, u) →
    SameSlots F G

/-- A function that leaves the ledger as it is. -/
theorem StaysS.of_same {x : Fl α}
    (h : ∀ (F : Fork) (t : Tape) (a : α) (G : Fork) (u : Tape), x F t = some (a, G, u) → F = G) :
    StaysS x :=
  ⟨fun {F t a G u} e => by
    obtain rfl := h F t a G u e
    exact SameSlots.refl F⟩

instance stays_pureS (a : α) : StaysS (pure a : Fl α) :=
  StaysS.of_same fun _ _ _ _ _ e => (some_triple.mp e).2.1

/-- One function after another. -/
theorem StaysS.bind {x : Fl α} {f : α → Fl β} (hx : StaysS x) (hf : ∀ a, StaysS (f a)) :
    StaysS (x >>= f) :=
  ⟨fun e => by
    obtain ⟨a, G, u, h1, h2⟩ := bind_some.mp e
    exact (hx.same h1).trans ((hf a).same h2)⟩

instance stays_bindS (x : Fl α) (f : α → Fl β) [StaysS x] [∀ a, StaysS (f a)] : StaysS (x >>= f) :=
  StaysS.bind inferInstance inferInstance

instance stays_mapS (g : α → β) (x : Fl α) [StaysS x] : StaysS (g <$> x) := by
  rw [map_eq_pure_bind]
  infer_instance

instance stays_iteS (p : Prop) [Decidable p] (x y : Fl α) [StaysS x] [StaysS y] :
    StaysS (if p then x else y) := by
  split <;> infer_instance

/-- The function that always refuses. -/
instance stays_noneS : StaysS (fun _ _ => none : Fl α) := ⟨fun e => by simp at e⟩

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
macro "staysS" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine StaysS.bind ?_ ?_
    | intro _
    | split)

/-! ### Folds -/

theorem stays_foldlMS {f : β → γ → Fl β} (hf : ∀ s a, StaysS (f s a)) :
    ∀ (l : List γ) (s : β), StaysS (l.foldlM f s)
  | [], s => by
    rw [List.foldlM_nil]
    infer_instance
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact StaysS.bind (hf s a) fun s' => stays_foldlMS hf l s'

theorem stays_mapM_listS {f : α → Fl β} (hf : ∀ a, StaysS (f a)) : ∀ l : List α, StaysS (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    infer_instance
  | a :: l => by
    rw [List.mapM_cons]
    exact StaysS.bind (hf a) fun _ => StaysS.bind (stays_mapM_listS hf l) fun _ => inferInstance

theorem stays_mapM_arrayS {f : α → Fl β} (hf : ∀ a, StaysS (f a)) (l : Array α) :
    StaysS (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  haveI := stays_mapM_listS hf l.toList
  infer_instance

/-! ### The steps -/

instance stays_mustS (b : Bool) : StaysS (Fl.must b) :=
  StaysS.of_same fun F t a G u e => by
    unfold Fl.must at e
    split at e
    · exact (some_triple.mp e).2.1
    · simp at e

instance stays_needS (x : Option α) : StaysS (Fl.need x) :=
  StaysS.of_same fun F t a G u e => by
    unfold Fl.need at e
    cases x with
    | none => simp at e
    | some y => exact (some_triple.mp e).2.1

instance stays_askS (f : Fork → Option α) : StaysS (Fl.ask f) :=
  StaysS.of_same fun F t a G u e => by
    unfold Fl.ask at e
    cases h : f F with
    | none => simp [h] at e
    | some y =>
      rw [h] at e
      exact (some_triple.mp e).2.1

instance stays_onTapeS (g : Tape → Option (α × Tape)) : StaysS (Fl.onTape g) :=
  StaysS.of_same fun F t a G u e => by
    unfold Fl.onTape at e
    cases h : g t with
    | none => simp [h] at e
    | some y =>
      rw [h] at e
      exact (some_triple.mp e).2.1

/-- A step on the ledger that leaves the two numbers. -/
theorem StaysS.change {f : Fork → Option Fork} (h : ∀ F G, f F = some G → SameSlots F G) :
    StaysS (Fl.change f) :=
  ⟨fun {F t a G u} e => by
    unfold Fl.change at e
    cases hf : f F with
    | none => simp [hf] at e
    | some H =>
      rw [hf] at e
      obtain rfl := (some_triple.mp e).2.1
      exact h F H hf⟩

instance stays_takeSlotsS (n : Nat) : StaysS (Fl.takeSlots n) :=
  ⟨fun {F t a G u} e => by
    obtain rfl := (some_triple.mp e).2.1
    exact SameSlots.refl F⟩

instance stays_hideRunS (j : Nat) (v : Array E) (c : E) :
    StaysS (Fl.change fun F => F.hideRun j v c) :=
  StaysS.change fun _ _ h => hideRun_slots h

instance stays_linS (a : Aff) : StaysS (Fl.change fun F => F.lin a) :=
  StaysS.change fun _ _ h => lin_slots h

instance stays_readS (n : Nat) : StaysS (Fl.read n) := by unfold Fl.read; infer_instance
instance stays_readSum : StaysS Fl.readSum := by unfold Fl.readSum; infer_instance
instance stays_answer (r : RoundName) : StaysS (Fl.answer r) := by unfold Fl.answer; infer_instance
instance stays_point (r : RoundName) (n : Nat) : StaysS (Fl.point r n) := by
  unfold Fl.point; infer_instance
instance stays_batch (n : Nat) : StaysS (Fl.batch n) := by unfold Fl.batch; infer_instance
instance stays_empty (r : RoundName) : StaysS (Fl.empty r) := by unfold Fl.empty; infer_instance
instance stays_shown (j : Nat) : StaysS (Fl.shown j) := by unfold Fl.shown; infer_instance
instance stays_publicPart (a : Aff) : StaysS (Fl.publicPart a) := by
  unfold Fl.publicPart; infer_instance

/-! ### Hidden values and the masked sumcheck -/

instance stays_claimsInS (n : Nat) : StaysS (Fl.claimsIn n) := by unfold Fl.claimsIn; staysS
instance stays_pscBeginAt (x : E) : StaysS (Fl.pscBeginAt x) := by unfold Fl.pscBeginAt; staysS
instance stays_pscBegin (C : Aff) : StaysS (Fl.pscBegin C) := by unfold Fl.pscBegin; staysS

instance stays_pscRoundS (p : Psc) (w : OnBytes.Psc.Weight) (draw : Tape → Option (E × Tape)) :
    StaysS (Fl.pscRound p w draw) := by
  unfold Fl.pscRound; staysS

instance stays_roundInS (form : RoundForm) (p : Psc) (z : E) (d : Nat) :
    StaysS (Fl.roundIn form p z d) := by
  unfold Fl.roundIn; staysS

instance stays_pscEndsS (p : Psc) (d n : Nat) : StaysS (Fl.pscEnds p d n) := by
  unfold Fl.pscEnds; staysS

instance stays_pscRowS (p : Psc) (S0 : E) (kept : Aff) : StaysS (Fl.pscRow p S0 kept) := by
  unfold Fl.pscRow; staysS

theorem stays_levelRoundsS (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (r : Array E) (p :
    Psc),
    StaysS (Fl.levelRounds mu rho order r p)
  | [], r, p => by
    unfold Fl.levelRounds
    infer_instance
  | v :: order, r, p => by
    unfold Fl.levelRounds
    refine StaysS.bind inferInstance fun _ => ?_
    refine StaysS.bind inferInstance fun x => ?_
    obtain ⟨x, p'⟩ := x
    exact stays_levelRoundsS mu rho order _ p'

instance (mu : Nat) (rho : Array E) (order : List Nat) (r : Array E) (p : Psc) :
    StaysS (Fl.levelRounds mu rho order r p) := stays_levelRoundsS mu rho order r p

instance stays_levelInS (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    StaysS (Fl.levelIn mu rho C order) := by
  unfold Fl.levelIn; staysS

theorem stays_tscLoopS : ∀ (zs : List E) (r : Array E) (p : Psc), StaysS (Fl.tscLoop zs r p)
  | [], r, p => by
    unfold Fl.tscLoop
    infer_instance
  | z :: zs, r, p => by
    unfold Fl.tscLoop
    refine StaysS.bind inferInstance fun x => ?_
    obtain ⟨x, p'⟩ := x
    exact stays_tscLoopS zs _ p'

instance (zs : List E) (r : Array E) (p : Psc) : StaysS (Fl.tscLoop zs r p) := stays_tscLoopS zs r p

instance stays_tscRoundsS (P : Array E) (lt : Nat) : StaysS (Fl.tscRounds P lt) := by
  unfold Fl.tscRounds; staysS

instance stays_tscInS (P : Array E) (lt n d : Nat) : StaysS (Fl.tscIn P lt n d) := by
  unfold Fl.tscIn; staysS

/-! ### The merge of the claims on the weights -/

theorem stays_wsForkRoundsS : ∀ (n : Nat) (rm : Array E) (p : Psc), StaysS (Fl.wsForkRounds n rm p)
  | 0, rm, p => by
    unfold Fl.wsForkRounds
    infer_instance
  | n + 1, rm, p => by
    unfold Fl.wsForkRounds
    refine StaysS.bind inferInstance fun x => ?_
    obtain ⟨r, p'⟩ := x
    exact stays_wsForkRoundsS n _ p'

instance (n : Nat) (rm : Array E) (p : Psc) : StaysS (Fl.wsForkRounds n rm p) :=
  stays_wsForkRoundsS n rm p

instance stays_wsForkMergeS (lk : Nat) (sv : Array Nat) : StaysS (Fl.wsForkMerge lk sv) := by
  unfold Fl.wsForkMerge; staysS

instance stays_flatForkEndS (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) :
    StaysS (flatForkEnd lay cl sv) := by
  unfold flatForkEnd; staysS

end VerifiableInference.Desc.LinkJoin.FlS

