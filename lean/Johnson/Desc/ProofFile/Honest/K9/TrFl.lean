-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/TrFl.lean: THE VERIFIER's SMALL STEPS ON THE LEDGER AND THE TAPE (`Fl`): each leaves the
reading `tr`. The class `StaysT`, its closure under bind, map, if, folds; the steps that read, hide values under slots, and run
a masked sumcheck. THE ADDING OF A CLAIM IS NOT AMONG THEM: it turns the reading.

One of nine files (Honest/K9/TrAre.lean, TrFl, TrWalk, TrK4, TrK5, TrK6, TrSeated, TrVia, TrLot) that say of the sub-protocols
which stand between a segment's opening and its batching: an accepting decision leaves the ledger's arrays, but for the mark
"the commitment is received" (`tr`), and what the batching's draw will test of the segment's book-keeping (`lnk`). They are the
nine files Honest/K9/TrAre.lean to TrLot.lean, carried over by program from the reading `tr` to the reading `tr`, name by name;
these in turn carry the library's own walk for the ledger's two numbers (Johnson/Desc/First/Link/Law/FlSlots.lean and the files
Slots*.lean beside it).

Limits. One direction: from an accepting decision. Nothing on the runs of claims unless it is said. This file proves no property
of a prover or a protocol.
-/
import Johnson.Desc.First.Link.Law.FlLooks
import Johnson.Desc.First.Link.Law.LooksAre
import Johnson.Desc.ProofFile.Honest.K9.TrAre
import OnBytes.Desc.First.FlGrows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.FlT
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Desc.First.Grow (some_triple bind_some)
open OnBytes.Desc.First.K4 (hideRun_core)

variable {α β γ : Type}

/-- G has the reading of F. -/
def SameTr (F G : Fork) : Prop := tr G = tr F

theorem SameTr.refl (F : Fork) : SameTr F F := rfl

theorem SameTr.trans {F G H : Fork} (a : SameTr F G) (b : SameTr G H) : SameTr F H :=
  Eq.trans b a

/-- A run of hidings. -/
theorem hideRun_tr {F G : Fork} {j : ℕ} {v : Array E} {c : E}
    (h : F.hideRun j v c = some G) : SameTr F G := by
  exact tr_core (hideRun_core h)

/-! ### The class -/

/-- Wherever x returns, the ledger that it leaves has the reading of the one that it was handed.
-/
class StaysT (x : Fl α) : Prop where
  same : ∀ {F : Fork} {t : Tape} {a : α} {G : Fork} {u : Tape}, x F t = some (a, G, u) →
    SameTr F G

/-- A function that leaves the ledger as it is. -/
theorem StaysT.of_same {x : Fl α}
    (h : ∀ (F : Fork) (t : Tape) (a : α) (G : Fork) (u : Tape), x F t = some (a, G, u) → F = G) :
    StaysT x :=
  ⟨fun {F t a G u} e => by
    obtain rfl := h F t a G u e
    exact SameTr.refl F⟩

instance stays_pureT (a : α) : StaysT (pure a : Fl α) :=
  StaysT.of_same fun _ _ _ _ _ e => (some_triple.mp e).2.1

/-- One function after another. -/
theorem StaysT.bind {x : Fl α} {f : α → Fl β} (hx : StaysT x) (hf : ∀ a, StaysT (f a)) :
    StaysT (x >>= f) :=
  ⟨fun e => by
    obtain ⟨a, G, u, h1, h2⟩ := bind_some.mp e
    exact (hx.same h1).trans ((hf a).same h2)⟩

instance stays_bindT (x : Fl α) (f : α → Fl β) [StaysT x] [∀ a, StaysT (f a)] : StaysT (x >>= f) :=
  StaysT.bind inferInstance inferInstance

instance stays_mapT (g : α → β) (x : Fl α) [StaysT x] : StaysT (g <$> x) := by
  rw [map_eq_pure_bind]
  infer_instance

instance stays_iteT (p : Prop) [Decidable p] (x y : Fl α) [StaysT x] [StaysT y] :
    StaysT (if p then x else y) := by
  split <;> infer_instance

/-- The function that always refuses. -/
instance stays_noneT : StaysT (fun _ _ => none : Fl α) := ⟨fun e => by simp at e⟩

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
macro "staysT" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine StaysT.bind ?_ ?_
    | intro _
    | split)

/-! ### Folds -/

theorem stays_foldlMT {f : β → γ → Fl β} (hf : ∀ s a, StaysT (f s a)) :
    ∀ (l : List γ) (s : β), StaysT (l.foldlM f s)
  | [], s => by
    rw [List.foldlM_nil]
    infer_instance
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact StaysT.bind (hf s a) fun s' => stays_foldlMT hf l s'

theorem stays_mapM_listT {f : α → Fl β} (hf : ∀ a, StaysT (f a)) : ∀ l : List α, StaysT (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    infer_instance
  | a :: l => by
    rw [List.mapM_cons]
    exact StaysT.bind (hf a) fun _ => StaysT.bind (stays_mapM_listT hf l) fun _ => inferInstance

theorem stays_mapM_arrayT {f : α → Fl β} (hf : ∀ a, StaysT (f a)) (l : Array α) :
    StaysT (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  haveI := stays_mapM_listT hf l.toList
  infer_instance

/-! ### The steps -/

instance stays_mustT (b : Bool) : StaysT (Fl.must b) :=
  StaysT.of_same fun F t a G u e => by
    unfold Fl.must at e
    split at e
    · exact (some_triple.mp e).2.1
    · simp at e

instance stays_needT (x : Option α) : StaysT (Fl.need x) :=
  StaysT.of_same fun F t a G u e => by
    unfold Fl.need at e
    cases x with
    | none => simp at e
    | some y => exact (some_triple.mp e).2.1

instance stays_askT (f : Fork → Option α) : StaysT (Fl.ask f) :=
  StaysT.of_same fun F t a G u e => by
    unfold Fl.ask at e
    cases h : f F with
    | none => simp [h] at e
    | some y =>
      rw [h] at e
      exact (some_triple.mp e).2.1

instance stays_onTapeT (g : Tape → Option (α × Tape)) : StaysT (Fl.onTape g) :=
  StaysT.of_same fun F t a G u e => by
    unfold Fl.onTape at e
    cases h : g t with
    | none => simp [h] at e
    | some y =>
      rw [h] at e
      exact (some_triple.mp e).2.1

/-- A step on the ledger that leaves the reading. -/
theorem StaysT.change {f : Fork → Option Fork} (h : ∀ F G, f F = some G → SameTr F G) :
    StaysT (Fl.change f) :=
  ⟨fun {F t a G u} e => by
    unfold Fl.change at e
    cases hf : f F with
    | none => simp [hf] at e
    | some H =>
      rw [hf] at e
      obtain rfl := (some_triple.mp e).2.1
      exact h F H hf⟩

instance stays_takeSlotsT (n : Nat) : StaysT (Fl.takeSlots n) :=
  ⟨fun {F t a G u} e => by
    obtain rfl := (some_triple.mp e).2.1
    exact SameTr.refl F⟩

instance stays_hideRunT (j : Nat) (v : Array E) (c : E) :
    StaysT (Fl.change fun F => F.hideRun j v c) :=
  StaysT.change fun _ _ h => hideRun_tr h

instance stays_readT (n : Nat) : StaysT (Fl.read n) := by unfold Fl.read; infer_instance
instance stays_readSum : StaysT Fl.readSum := by unfold Fl.readSum; infer_instance
instance stays_answer (r : RoundName) : StaysT (Fl.answer r) := by unfold Fl.answer; infer_instance
instance stays_point (r : RoundName) (n : Nat) : StaysT (Fl.point r n) := by
  unfold Fl.point; infer_instance
instance stays_batch (n : Nat) : StaysT (Fl.batch n) := by unfold Fl.batch; infer_instance
instance stays_empty (r : RoundName) : StaysT (Fl.empty r) := by unfold Fl.empty; infer_instance
instance stays_shown (j : Nat) : StaysT (Fl.shown j) := by unfold Fl.shown; infer_instance
instance stays_publicPart (a : Aff) : StaysT (Fl.publicPart a) := by
  unfold Fl.publicPart; infer_instance

/-! ### Hidden values and the masked sumcheck -/

instance stays_claimsInT (n : Nat) : StaysT (Fl.claimsIn n) := by unfold Fl.claimsIn; staysT
instance stays_pscBeginAt (x : E) : StaysT (Fl.pscBeginAt x) := by unfold Fl.pscBeginAt; staysT
instance stays_pscBegin (C : Aff) : StaysT (Fl.pscBegin C) := by unfold Fl.pscBegin; staysT

instance stays_pscRoundT (p : Psc) (w : OnBytes.Psc.Weight) (draw : Tape → Option (E × Tape)) :
    StaysT (Fl.pscRound p w draw) := by
  unfold Fl.pscRound; staysT

instance stays_roundInT (form : RoundForm) (p : Psc) (z : E) (d : Nat) :
    StaysT (Fl.roundIn form p z d) := by
  unfold Fl.roundIn; staysT

instance stays_pscEndsT (p : Psc) (d n : Nat) : StaysT (Fl.pscEnds p d n) := by
  unfold Fl.pscEnds; staysT

instance stays_pscRowT (p : Psc) (S0 : E) (kept : Aff) : StaysT (Fl.pscRow p S0 kept) := by
  unfold Fl.pscRow; staysT

theorem stays_levelRoundsT (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (r : Array E) (p :
    Psc),
    StaysT (Fl.levelRounds mu rho order r p)
  | [], r, p => by
    unfold Fl.levelRounds
    infer_instance
  | v :: order, r, p => by
    unfold Fl.levelRounds
    refine StaysT.bind inferInstance fun _ => ?_
    refine StaysT.bind inferInstance fun x => ?_
    obtain ⟨x, p'⟩ := x
    exact stays_levelRoundsT mu rho order _ p'

instance (mu : Nat) (rho : Array E) (order : List Nat) (r : Array E) (p : Psc) :
    StaysT (Fl.levelRounds mu rho order r p) := stays_levelRoundsT mu rho order r p

instance stays_levelInT (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    StaysT (Fl.levelIn mu rho C order) := by
  unfold Fl.levelIn; staysT

theorem stays_tscLoopT : ∀ (zs : List E) (r : Array E) (p : Psc), StaysT (Fl.tscLoop zs r p)
  | [], r, p => by
    unfold Fl.tscLoop
    infer_instance
  | z :: zs, r, p => by
    unfold Fl.tscLoop
    refine StaysT.bind inferInstance fun x => ?_
    obtain ⟨x, p'⟩ := x
    exact stays_tscLoopT zs _ p'

instance (zs : List E) (r : Array E) (p : Psc) : StaysT (Fl.tscLoop zs r p) := stays_tscLoopT zs r p

instance stays_tscRoundsT (P : Array E) (lt : Nat) : StaysT (Fl.tscRounds P lt) := by
  unfold Fl.tscRounds; staysT

instance stays_tscInT (P : Array E) (lt n d : Nat) : StaysT (Fl.tscIn P lt n d) := by
  unfold Fl.tscIn; staysT

/-! ### The merge of the claims on the weights -/

theorem stays_wsForkRoundsT : ∀ (n : Nat) (rm : Array E) (p : Psc), StaysT (Fl.wsForkRounds n rm p)
  | 0, rm, p => by
    unfold Fl.wsForkRounds
    infer_instance
  | n + 1, rm, p => by
    unfold Fl.wsForkRounds
    refine StaysT.bind inferInstance fun x => ?_
    obtain ⟨r, p'⟩ := x
    exact stays_wsForkRoundsT n _ p'

instance (n : Nat) (rm : Array E) (p : Psc) : StaysT (Fl.wsForkRounds n rm p) :=
  stays_wsForkRoundsT n rm p

instance stays_wsForkMergeT (lk : Nat) (sv : Array Nat) : StaysT (Fl.wsForkMerge lk sv) := by
  unfold Fl.wsForkMerge; staysT

instance stays_flatForkEndT (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) :
    StaysT (flatForkEnd lay cl sv) := by
  unfold flatForkEnd; staysT

end VerifiableInference.Desc.LinkJoin.FlT

#print axioms VerifiableInference.Desc.LinkJoin.FlT.SameTr.refl
#print axioms VerifiableInference.Desc.LinkJoin.FlT.SameTr.trans
#print axioms VerifiableInference.Desc.LinkJoin.FlT.hideRun_tr
#print axioms VerifiableInference.Desc.LinkJoin.FlT.StaysT.of_same
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_pureT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.StaysT.bind
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_bindT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_mapT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_iteT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_noneT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_foldlMT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_mapM_listT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_mapM_arrayT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_mustT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_needT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_askT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_onTapeT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.StaysT.change
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_takeSlotsT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_hideRunT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_readT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_readSum
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_answer
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_point
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_batch
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_empty
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_shown
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_publicPart
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_claimsInT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_pscBeginAt
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_pscBegin
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_pscRoundT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_roundInT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_pscEndsT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_pscRowT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_levelRoundsT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_levelInT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_tscLoopT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_tscRoundsT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_tscInT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_wsForkRoundsT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_wsForkMergeT
#print axioms VerifiableInference.Desc.LinkJoin.FlT.stays_flatForkEndT
