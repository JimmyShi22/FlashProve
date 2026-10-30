-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/CrFl.lean: THE VERIFIER's SMALL STEPS ON THE LEDGER AND THE TAPE (`Fl`): each leaves the
reading `cr`. The class `StaysC`, its closure under bind, map, if, folds; the steps that read, hide values under slots, and run
a masked sumcheck. THE ADDING OF A CLAIM IS NOT AMONG THEM: it turns the reading.

One of nine files (Honest/K9/CrAre.lean, CrFl, CrWalk, CrK4, CrK5, CrK6, CrSeated, CrVia, CrLot) that say of the sub-protocols
which stand between a segment's opening and its batching: an accepting decision leaves what the batching's draw will test of the
ledger (`cr`) and of the segment's book-keeping (`lnk`). The walk through each sub-protocol's text is the library's own walk for
the ledger's two numbers (Johnson/Desc/First/Link/Law/FlSlots.lean and the files Slots*.lean beside it), carried over by program
to the reading `cr`, name by name, and righted by hand where the ground fact is another.

Limits. One direction: from an accepting decision. Nothing on the runs of claims unless it is said. This file proves no property
of a prover or a protocol.
-/
import Johnson.Desc.First.Link.Law.FlLooks
import Johnson.Desc.First.Link.Law.LooksAre
import Johnson.Desc.ProofFile.Honest.K9.CrAre
import OnBytes.Desc.First.FlGrows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin.FlC
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Desc.First.Grow (some_triple bind_some)
open OnBytes.Desc.First.K4 (hideRun_core)

variable {α β γ : Type}

/-- G has the reading of F. -/
def SameCr (F G : Fork) : Prop := cr G = cr F

theorem SameCr.refl (F : Fork) : SameCr F F := rfl

theorem SameCr.trans {F G H : Fork} (a : SameCr F G) (b : SameCr G H) : SameCr F H :=
  Eq.trans b a

/-- A run of hidings. -/
theorem hideRun_cr {F G : Fork} {j : ℕ} {v : Array E} {c : E}
    (h : F.hideRun j v c = some G) : SameCr F G := by
  exact cr_core (hideRun_core h)

/-! ### The class -/

/-- Wherever x returns, the ledger that it leaves has the reading of the one that it was handed.
-/
class StaysC (x : Fl α) : Prop where
  same : ∀ {F : Fork} {t : Tape} {a : α} {G : Fork} {u : Tape}, x F t = some (a, G, u) →
    SameCr F G

/-- A function that leaves the ledger as it is. -/
theorem StaysC.of_same {x : Fl α}
    (h : ∀ (F : Fork) (t : Tape) (a : α) (G : Fork) (u : Tape), x F t = some (a, G, u) → F = G) :
    StaysC x :=
  ⟨fun {F t a G u} e => by
    obtain rfl := h F t a G u e
    exact SameCr.refl F⟩

instance stays_pureC (a : α) : StaysC (pure a : Fl α) :=
  StaysC.of_same fun _ _ _ _ _ e => (some_triple.mp e).2.1

/-- One function after another. -/
theorem StaysC.bind {x : Fl α} {f : α → Fl β} (hx : StaysC x) (hf : ∀ a, StaysC (f a)) :
    StaysC (x >>= f) :=
  ⟨fun e => by
    obtain ⟨a, G, u, h1, h2⟩ := bind_some.mp e
    exact (hx.same h1).trans ((hf a).same h2)⟩

instance stays_bindC (x : Fl α) (f : α → Fl β) [StaysC x] [∀ a, StaysC (f a)] : StaysC (x >>= f) :=
  StaysC.bind inferInstance inferInstance

instance stays_mapC (g : α → β) (x : Fl α) [StaysC x] : StaysC (g <$> x) := by
  rw [map_eq_pure_bind]
  infer_instance

instance stays_iteC (p : Prop) [Decidable p] (x y : Fl α) [StaysC x] [StaysC y] :
    StaysC (if p then x else y) := by
  split <;> infer_instance

/-- The function that always refuses. -/
instance stays_noneC : StaysC (fun _ _ => none : Fl α) := ⟨fun e => by simp at e⟩

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
macro "staysC" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine StaysC.bind ?_ ?_
    | intro _
    | split)

/-! ### Folds -/

theorem stays_foldlMC {f : β → γ → Fl β} (hf : ∀ s a, StaysC (f s a)) :
    ∀ (l : List γ) (s : β), StaysC (l.foldlM f s)
  | [], s => by
    rw [List.foldlM_nil]
    infer_instance
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact StaysC.bind (hf s a) fun s' => stays_foldlMC hf l s'

theorem stays_mapM_listC {f : α → Fl β} (hf : ∀ a, StaysC (f a)) : ∀ l : List α, StaysC (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    infer_instance
  | a :: l => by
    rw [List.mapM_cons]
    exact StaysC.bind (hf a) fun _ => StaysC.bind (stays_mapM_listC hf l) fun _ => inferInstance

theorem stays_mapM_arrayC {f : α → Fl β} (hf : ∀ a, StaysC (f a)) (l : Array α) :
    StaysC (l.mapM f) := by
  rw [Array.mapM_eq_mapM_toList]
  haveI := stays_mapM_listC hf l.toList
  infer_instance

/-! ### The steps -/

instance stays_mustC (b : Bool) : StaysC (Fl.must b) :=
  StaysC.of_same fun F t a G u e => by
    unfold Fl.must at e
    split at e
    · exact (some_triple.mp e).2.1
    · simp at e

instance stays_needC (x : Option α) : StaysC (Fl.need x) :=
  StaysC.of_same fun F t a G u e => by
    unfold Fl.need at e
    cases x with
    | none => simp at e
    | some y => exact (some_triple.mp e).2.1

instance stays_askC (f : Fork → Option α) : StaysC (Fl.ask f) :=
  StaysC.of_same fun F t a G u e => by
    unfold Fl.ask at e
    cases h : f F with
    | none => simp [h] at e
    | some y =>
      rw [h] at e
      exact (some_triple.mp e).2.1

instance stays_onTapeC (g : Tape → Option (α × Tape)) : StaysC (Fl.onTape g) :=
  StaysC.of_same fun F t a G u e => by
    unfold Fl.onTape at e
    cases h : g t with
    | none => simp [h] at e
    | some y =>
      rw [h] at e
      exact (some_triple.mp e).2.1

/-- A step on the ledger that leaves the reading. -/
theorem StaysC.change {f : Fork → Option Fork} (h : ∀ F G, f F = some G → SameCr F G) :
    StaysC (Fl.change f) :=
  ⟨fun {F t a G u} e => by
    unfold Fl.change at e
    cases hf : f F with
    | none => simp [hf] at e
    | some H =>
      rw [hf] at e
      obtain rfl := (some_triple.mp e).2.1
      exact h F H hf⟩

instance stays_takeSlotsC (n : Nat) : StaysC (Fl.takeSlots n) :=
  ⟨fun {F t a G u} e => by
    obtain rfl := (some_triple.mp e).2.1
    exact SameCr.refl F⟩

instance stays_hideRunC (j : Nat) (v : Array E) (c : E) :
    StaysC (Fl.change fun F => F.hideRun j v c) :=
  StaysC.change fun _ _ h => hideRun_cr h

instance stays_readC (n : Nat) : StaysC (Fl.read n) := by unfold Fl.read; infer_instance
instance stays_readSum : StaysC Fl.readSum := by unfold Fl.readSum; infer_instance
instance stays_answer (r : RoundName) : StaysC (Fl.answer r) := by unfold Fl.answer; infer_instance
instance stays_point (r : RoundName) (n : Nat) : StaysC (Fl.point r n) := by
  unfold Fl.point; infer_instance
instance stays_batch (n : Nat) : StaysC (Fl.batch n) := by unfold Fl.batch; infer_instance
instance stays_empty (r : RoundName) : StaysC (Fl.empty r) := by unfold Fl.empty; infer_instance
instance stays_shown (j : Nat) : StaysC (Fl.shown j) := by unfold Fl.shown; infer_instance
instance stays_publicPart (a : Aff) : StaysC (Fl.publicPart a) := by
  unfold Fl.publicPart; infer_instance

/-! ### Hidden values and the masked sumcheck -/

instance stays_claimsInC (n : Nat) : StaysC (Fl.claimsIn n) := by unfold Fl.claimsIn; staysC
instance stays_pscBeginAt (x : E) : StaysC (Fl.pscBeginAt x) := by unfold Fl.pscBeginAt; staysC
instance stays_pscBegin (C : Aff) : StaysC (Fl.pscBegin C) := by unfold Fl.pscBegin; staysC

instance stays_pscRoundC (p : Psc) (w : OnBytes.Psc.Weight) (draw : Tape → Option (E × Tape)) :
    StaysC (Fl.pscRound p w draw) := by
  unfold Fl.pscRound; staysC

instance stays_roundInC (form : RoundForm) (p : Psc) (z : E) (d : Nat) :
    StaysC (Fl.roundIn form p z d) := by
  unfold Fl.roundIn; staysC

instance stays_pscEndsC (p : Psc) (d n : Nat) : StaysC (Fl.pscEnds p d n) := by
  unfold Fl.pscEnds; staysC

instance stays_pscRowC (p : Psc) (S0 : E) (kept : Aff) : StaysC (Fl.pscRow p S0 kept) := by
  unfold Fl.pscRow; staysC

theorem stays_levelRoundsC (mu : Nat) (rho : Array E) : ∀ (order : List Nat) (r : Array E) (p :
    Psc),
    StaysC (Fl.levelRounds mu rho order r p)
  | [], r, p => by
    unfold Fl.levelRounds
    infer_instance
  | v :: order, r, p => by
    unfold Fl.levelRounds
    refine StaysC.bind inferInstance fun _ => ?_
    refine StaysC.bind inferInstance fun x => ?_
    obtain ⟨x, p'⟩ := x
    exact stays_levelRoundsC mu rho order _ p'

instance (mu : Nat) (rho : Array E) (order : List Nat) (r : Array E) (p : Psc) :
    StaysC (Fl.levelRounds mu rho order r p) := stays_levelRoundsC mu rho order r p

instance stays_levelInC (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    StaysC (Fl.levelIn mu rho C order) := by
  unfold Fl.levelIn; staysC

theorem stays_tscLoopC : ∀ (zs : List E) (r : Array E) (p : Psc), StaysC (Fl.tscLoop zs r p)
  | [], r, p => by
    unfold Fl.tscLoop
    infer_instance
  | z :: zs, r, p => by
    unfold Fl.tscLoop
    refine StaysC.bind inferInstance fun x => ?_
    obtain ⟨x, p'⟩ := x
    exact stays_tscLoopC zs _ p'

instance (zs : List E) (r : Array E) (p : Psc) : StaysC (Fl.tscLoop zs r p) := stays_tscLoopC zs r p

instance stays_tscRoundsC (P : Array E) (lt : Nat) : StaysC (Fl.tscRounds P lt) := by
  unfold Fl.tscRounds; staysC

instance stays_tscInC (P : Array E) (lt n d : Nat) : StaysC (Fl.tscIn P lt n d) := by
  unfold Fl.tscIn; staysC

/-! ### The merge of the claims on the weights -/

theorem stays_wsForkRoundsC : ∀ (n : Nat) (rm : Array E) (p : Psc), StaysC (Fl.wsForkRounds n rm p)
  | 0, rm, p => by
    unfold Fl.wsForkRounds
    infer_instance
  | n + 1, rm, p => by
    unfold Fl.wsForkRounds
    refine StaysC.bind inferInstance fun x => ?_
    obtain ⟨r, p'⟩ := x
    exact stays_wsForkRoundsC n _ p'

instance (n : Nat) (rm : Array E) (p : Psc) : StaysC (Fl.wsForkRounds n rm p) :=
  stays_wsForkRoundsC n rm p

instance stays_wsForkMergeC (lk : Nat) (sv : Array Nat) : StaysC (Fl.wsForkMerge lk sv) := by
  unfold Fl.wsForkMerge; staysC

instance stays_flatForkEndC (lay : WsLay) (cl : Array WsClaim) (sv : Array Nat) :
    StaysC (flatForkEnd lay cl sv) := by
  unfold flatForkEnd; staysC

end VerifiableInference.Desc.LinkJoin.FlC

#print axioms VerifiableInference.Desc.LinkJoin.FlC.SameCr.refl
#print axioms VerifiableInference.Desc.LinkJoin.FlC.SameCr.trans
#print axioms VerifiableInference.Desc.LinkJoin.FlC.hideRun_cr
#print axioms VerifiableInference.Desc.LinkJoin.FlC.StaysC.of_same
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_pureC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.StaysC.bind
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_bindC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_mapC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_iteC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_noneC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_foldlMC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_mapM_listC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_mapM_arrayC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_mustC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_needC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_askC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_onTapeC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.StaysC.change
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_takeSlotsC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_hideRunC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_readC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_readSum
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_answer
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_point
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_batch
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_empty
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_shown
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_publicPart
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_claimsInC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_pscBeginAt
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_pscBegin
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_pscRoundC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_roundInC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_pscEndsC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_pscRowC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_levelRoundsC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_levelInC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_tscLoopC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_tscRoundsC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_tscInC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_wsForkRoundsC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_wsForkMergeC
#print axioms VerifiableInference.Desc.LinkJoin.FlC.stays_flatForkEndC
