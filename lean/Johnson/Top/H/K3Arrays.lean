-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3Arrays.lean: at no real record has a yes of the block been
shown for this file. The kind "lookup" (K3): A YES LEAVES THE LEDGER's ARRAYS AS THEY WERE, WITH NO
PREMISE ON THE LEDGER's SIZES: the field Fork.trees is the same behind the hearing as in front; and
at the seat of the lookup on the digits a yes leaves what the lookup ON THE CALLS returned
(S.look?). Statements and proofs.

How. In all that the flat function of the lookup's messages calls (lkPad,
OnBytes/K/Kc/FlatHear.lean; the verbs of OnBytes/K/Kc/Flat.lean) the ledger is written by three
steps alone: takeSlots (the field next), Fork.hideRun (gotF, vp, mf) and Fork.owe (owed). The class
KeepsArrays says of a function in Fl that it leaves Fork.trees wherever it returns; it is walked
through the do-blocks verb by verb, after the pattern of the library's class Grows
(OnBytes/Desc/First/FlGrows.lean), whose two lemmas on what a step returns are called.

Main names:
  `KeepsArrays x`: the class. `hideRun_trees`: of Fork.hideRun.
  `lkPad_arrays`: lkPad calls pub lid F t = some (g, F', u) gives F'.trees = F.trees: NO PREMISE.
  `k3_decide_arrays`: of K3.block's decide, at any seat that keeps the ledger laid (SeatKeeps).
  `via_decide_arrays`: of Law.blockVia's decide, WHERE ITS TEST ON THE PLAN SAYS YES.
  `digits_put_look`: the digits' seat's put leaves S.look?.
  `via_digits_kept`: at the digits' seat: blockVia steps along "S.look? is as it was, and every
  array of the open ledger has the numbers of rows R and of columns K that it had".
  `via_digits_leaves_look`, `via_digits_leaves_shapes`: the two halves as Block.Leaves.

OBJECT: OnBytes.K.Kc.lkPad · K3.block (Johnson/Desc/First/Look/K3Lookup.lean) · K3.Law.blockVia
(Johnson/Desc/First/Look/Via/Via.lean) · K3.seatDigits (K3Seat.lean).
Used by LooksK3.lean (Johnson/Desc/First/Link/Law/), which calls lkPad_arrays alone.
LETTERS: general in seat, claim, piece, laid, before, p, guests.
Compiled with the whole library.






Limits. via_decide_arrays and what stands on it have the premise planOk = true. One direction: from
a yes. Of the runs of claims and of the steps without a round behind the block nothing is said. IT
SAYS MORE THAN Johnson/Top/H/K3Trees.lean, which has the same sentence under "the ledger in front
has its sizes", by another road (the library's record PadLeft). A TWIN, SAID: lookOf_putFork has the
statement of Came.look_putFork (Johnson/Desc/Kinds/Law/RowPins.lean), which is not imported here.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Desc.First.FlGrows
import Johnson.Top.H.K3KeySizes
import Johnson.Top.H.K3SeatFits
import Johnson.Top.H.K3Via.Blocks
import Johnson.Desc.Sound.FoldSteps
import Johnson.Desc.Sound.FoldHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Desc.First.Grow (some_triple bind_some)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (Seat seatCalls seatDigits)

/-! ## The class -/

section Keeps
variable {α β γ : Type}

/-- Wherever x returns, the ledger that it leaves has the arrays of the one that it was handed. -/
class KeepsArrays (x : Fl α) : Prop where
  same : ∀ {F : Fork} {t : Tape} {a : α} {G : Fork} {u : Tape},
    x F t = some (a, G, u) → G.trees = F.trees

theorem KeepsArrays.of_same {x : Fl α}
    (h : ∀ (F : Fork) (t : Tape) (a : α) (G : Fork) (u : Tape), x F t = some (a, G, u) → F = G) :
    KeepsArrays x :=
  ⟨fun {F t a G u} e => by
    obtain rfl := h F t a G u e
    rfl⟩

instance arrays_pure (a : α) : KeepsArrays (pure a : Fl α) :=
  KeepsArrays.of_same fun _ _ _ _ _ e => (some_triple.mp e).2.1

theorem KeepsArrays.bind {x : Fl α} {f : α → Fl β} (hx : KeepsArrays x)
    (hf : ∀ a, KeepsArrays (f a)) : KeepsArrays (x >>= f) :=
  ⟨fun e => by
    obtain ⟨a, G, u, h1, h2⟩ := bind_some.mp e
    exact ((hf a).same h2).trans (hx.same h1)⟩

instance arrays_bind (x : Fl α) (f : α → Fl β) [KeepsArrays x] [∀ a, KeepsArrays (f a)] :
    KeepsArrays (x >>= f) :=
  KeepsArrays.bind inferInstance inferInstance

instance arrays_ite (p : Prop) [Decidable p] (x y : Fl α) [KeepsArrays x] [KeepsArrays y] :
    KeepsArrays (if p then x else y) := by
  split <;> infer_instance

/-- Walks a do-block: bind by bind, into each `if` and each pattern. -/
local macro "arrays" : tactic =>
  `(tactic| repeat' first
    | infer_instance
    | refine KeepsArrays.bind ?_ ?_
    | intro _
    | split)

theorem arrays_foldlM {f : β → γ → Fl β} (hf : ∀ s a, KeepsArrays (f s a)) :
    ∀ (l : List γ) (s : β), KeepsArrays (l.foldlM f s)
  | [], s => by
    rw [List.foldlM_nil]
    infer_instance
  | a :: l, s => by
    rw [List.foldlM_cons]
    exact KeepsArrays.bind (hf s a) fun s' => arrays_foldlM hf l s'

instance arrays_fold (f : β → γ → Fl β) [∀ s a, KeepsArrays (f s a)] (l : List γ) (s : β) :
    KeepsArrays (l.foldlM f s) := arrays_foldlM (fun _ _ => inferInstance) l s

/-! ## The steps that leave the ledger -/

instance arrays_must (b : Bool) : KeepsArrays (Fl.must b) :=
  KeepsArrays.of_same fun F t a G u e => by
    unfold Fl.must at e
    split at e
    · exact (some_triple.mp e).2.1
    · simp at e

instance arrays_need (x : Option α) : KeepsArrays (Fl.need x) :=
  KeepsArrays.of_same fun F t a G u e => by
    unfold Fl.need at e
    cases x with
    | none => simp at e
    | some y => exact (some_triple.mp e).2.1

instance arrays_ask (f : Fork → Option α) : KeepsArrays (Fl.ask f) :=
  KeepsArrays.of_same fun F t a G u e => by
    unfold Fl.ask at e
    cases h : f F with
    | none => simp [h] at e
    | some y =>
      rw [h] at e
      exact (some_triple.mp e).2.1

instance arrays_onTape (g : Tape → Option (α × Tape)) : KeepsArrays (Fl.onTape g) :=
  KeepsArrays.of_same fun F t a G u e => by
    unfold Fl.onTape at e
    cases h : g t with
    | none => simp [h] at e
    | some y =>
      rw [h] at e
      exact (some_triple.mp e).2.1

/-! ## The three steps that write the ledger -/

theorem KeepsArrays.change {f : Fork → Option Fork} (h : ∀ F G, f F = some G → G.trees = F.trees) :
    KeepsArrays (Fl.change f) :=
  ⟨fun {F t a G u} e => by
    unfold Fl.change at e
    cases hf : f F with
    | none => simp [hf] at e
    | some H =>
      rw [hf] at e
      obtain rfl := (some_triple.mp e).2.1
      exact h F H hf⟩

theorem KeepsArrays.take {f : Fork → Option (α × Fork)}
    (h : ∀ F x, f F = some x → x.2.trees = F.trees) : KeepsArrays (Fl.take f) :=
  ⟨fun {F t a G u} e => by
    unfold Fl.take at e
    cases hf : f F with
    | none => simp [hf] at e
    | some x =>
      simp only [hf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨_, rfl, _⟩ := e
      exact h F x hf⟩

instance arrays_takeSlots (n : Nat) : KeepsArrays (Fl.takeSlots n) :=
  ⟨fun {F t a G u} e => by
    obtain rfl := (some_triple.mp e).2.1
    rfl⟩

theorem hide_trees {F G : Fork} {j : Nat} {y factor : E} (h : F.hide j y factor = some G) :
    G.trees = F.trees := by
  unfold Fork.hide at h
  split at h
  · obtain rfl := Option.some.inj h
    rfl
  · simp at h

theorem hideSteps_trees (factor : E) : ∀ (l : List E) (first : Nat) (F : Fork) (x : Nat × Fork),
    l.foldlM (Fork.hideStep factor) (first, F) = some x → x.2.trees = F.trees
  | [], first, F, x, h => by
    have hx : (first, F) = x := by simpa using h
    subst hx
    rfl
  | y :: l, first, F, x, h => by
    rw [List.foldlM_cons] at h
    cases hq : Fork.hideStep factor (first, F) y with
    | none => simp [hq] at h
    | some s =>
      rw [hq] at h
      have h2 : l.foldlM (Fork.hideStep factor) s = some x := by simpa using h
      simp only [Fork.hideStep] at hq
      cases hh : F.hide first y factor with
      | none => simp [hh] at hq
      | some H =>
        rw [hh] at hq
        obtain rfl : (first + 1, H) = s := by simpa using hq
        exact (hideSteps_trees factor l _ _ _ h2).trans (hide_trees hh)

theorem hideRun_trees {F G : Fork} {first : Nat} {v : Array E} {factor : E}
    (h : F.hideRun first v factor = some G) : G.trees = F.trees := by
  unfold Fork.hideRun at h
  split at h
  · rename_i x hx
    obtain rfl := Option.some.inj h
    rw [← Array.foldlM_toList] at hx
    exact hideSteps_trees factor _ _ _ _ hx
  · simp at h

instance arrays_hideRun (j : Nat) (v : Array E) (c : E) :
    KeepsArrays (Fl.change fun F => F.hideRun j v c) :=
  KeepsArrays.change fun _ _ h => hideRun_trees h

instance arrays_owe (w : String) : KeepsArrays (Fl.owe w) := by
  unfold Fl.owe
  exact KeepsArrays.take fun F x e => by
    obtain rfl := Option.some.inj e
    rfl

/-! ## The verbs of the lookup's messages -/

instance arrays_slot : KeepsArrays Fl.slot := by unfold Fl.slot; infer_instance
instance arrays_read (n : Nat) : KeepsArrays (Fl.read n) := by unfold Fl.read; infer_instance
instance arrays_readSum : KeepsArrays Fl.readSum := by unfold Fl.readSum; infer_instance
instance arrays_answer (r : RoundName) : KeepsArrays (Fl.answer r) := by
  unfold Fl.answer; infer_instance
instance arrays_point (r : RoundName) (n : Nat) : KeepsArrays (Fl.point r n) := by
  unfold Fl.point; infer_instance
instance arrays_empty (r : RoundName) : KeepsArrays (Fl.empty r) := by
  unfold Fl.empty; infer_instance
instance arrays_shown (j : Nat) : KeepsArrays (Fl.shown j) := by unfold Fl.shown; infer_instance
instance arrays_publicPart (a : Aff) : KeepsArrays (Fl.publicPart a) := by
  unfold Fl.publicPart; infer_instance

instance arrays_pscBeginAt (x : E) : KeepsArrays (Fl.pscBeginAt x) := by
  unfold Fl.pscBeginAt; arrays
instance arrays_pscBegin (C : Aff) : KeepsArrays (Fl.pscBegin C) := by unfold Fl.pscBegin; arrays

instance arrays_pscRound (p : Psc) (w : OnBytes.Psc.Weight) (draw : Tape → Option (E × Tape)) :
    KeepsArrays (Fl.pscRound p w draw) := by
  unfold Fl.pscRound; arrays

instance arrays_roundIn (form : RoundForm) (p : Psc) (z : E) (d : Nat) :
    KeepsArrays (Fl.roundIn form p z d) := by
  unfold Fl.roundIn; arrays

instance arrays_pscEnds (p : Psc) (d n : Nat) : KeepsArrays (Fl.pscEnds p d n) := by
  unfold Fl.pscEnds; arrays

instance arrays_pscRow (p : Psc) (S0 : E) (kept : Aff) : KeepsArrays (Fl.pscRow p S0 kept) := by
  unfold Fl.pscRow; arrays

theorem arrays_levelRounds (mu : Nat) (rho : Array E) :
    ∀ (order : List Nat) (r : Array E) (p : Psc), KeepsArrays (Fl.levelRounds mu rho order r p)
  | [], r, p => by
    unfold Fl.levelRounds
    infer_instance
  | v :: order, r, p => by
    unfold Fl.levelRounds
    refine KeepsArrays.bind inferInstance fun _ => ?_
    refine KeepsArrays.bind inferInstance fun x => ?_
    obtain ⟨x, p'⟩ := x
    exact arrays_levelRounds mu rho order _ p'

instance (mu : Nat) (rho : Array E) (order : List Nat) (r : Array E) (p : Psc) :
    KeepsArrays (Fl.levelRounds mu rho order r p) := arrays_levelRounds mu rho order r p

instance arrays_levelIn (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) :
    KeepsArrays (Fl.levelIn mu rho C order) := by
  unfold Fl.levelIn; arrays

instance arrays_roundsIn (form : RoundForm) (p : Psc) (zs : List (E × Nat)) :
    KeepsArrays (Fl.roundsIn form p zs) := by
  unfold Fl.roundsIn
  exact arrays_foldlM (fun s z => by arrays) zs _

instance arrays_lkDraws (h : Forest.Shape) : KeepsArrays (lkDraws h) := by
  unfold lkDraws
  arrays

instance arrays_lkTieStep (a : E) (s : Forest.TieStep) (j : Nat) :
    KeepsArrays (lkTieStep a s j) := by
  unfold lkTieStep
  arrays

instance arrays_lkTie (a : E) : KeepsArrays (lkTie a) := by
  unfold lkTie
  arrays

instance arrays_lkLevel (s : Forest.Descent) (mu : Nat) (order : List Nat) :
    KeepsArrays (lkLevel s mu order) := by
  unfold lkLevel
  arrays

/-- **The lookup's messages leave the ledger's arrays.** -/
instance arrays_lkPad (calls : Array Call) (pub : Array Nat) (lid : Nat) :
    KeepsArrays (lkPad calls pub lid) := by
  unfold lkPad
  arrays

theorem lkPad_arrays (calls : Array Call) (pub : Array Nat) (lid : ℕ) (F F' : Fork) (t u : Tape)
    (g : Forest.Heard) (h : lkPad calls pub lid F t = some (g, F', u)) : F'.trees = F.trees :=
  (arrays_lkPad calls pub lid).same h

end Keeps

/-! ## The block's decision, at any seat -/

section Seat
variable {T Cl : Type}

theorem k3_decide_arrays (seat : Seat T Cl) (hk : SeatKeeps seat) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest T Cl))
    (s s' : T) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hdec : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ F F', seat.fork s = some F ∧ seat.fork s' = some F' ∧ F'.trees = F.trees := by
  obtain ⟨F, F', g, t, hF, hn, hl, rfl⟩ :=
    decide_lkPad seat piece laid before p guests s s' rs cols hdec
  exact ⟨F, F', hF, hk s g F' (by rw [hF]; rfl) hn,
    lkPad_arrays p.calls p.pub p.lid F F' t [] g hl⟩

theorem via_decide_arrays (seat : Seat T Cl) (hk : SeatKeeps seat) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest T Cl))
    (hplan : (Desc.K3.Law.blockVia seat piece laid before p guests).planOk = true)
    (s s' : T) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hdec : (Desc.K3.Law.blockVia seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ F F', seat.fork s = some F ∧ seat.fork s' = some F' ∧ F'.trees = F.trees :=
  k3_decide_arrays seat hk piece laid before p guests s s' rs cols
    (Desc.K3.Law.blockVia_decide hplan hdec)

end Seat

/-! ## At the digits' seat: what the lookup on the calls returned, and the arrays' shapes -/

section AtS
variable {Cl : Type}

theorem lookOf_putFork (s : S) (G : Fork) : (s.putFork G).look? = s.look? := by
  cases hh : s.here with
  | between => simp [S.putFork, hh]
  | fin _ => simp [S.putFork, hh]
  | mem _ => simp [S.putFork, hh]
  | lay a => simp [S.putFork, S.look?, hh]
  | att a => simp [S.putFork, S.look?, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [S.putFork, hh, ho]
    | true => simp [S.putFork, S.look?, hh, ho]

theorem lookOf_putTl (s : S) (tl : HTailF2) : (s.putTl tl).look? = s.look? := by
  cases hh : s.here with
  | between => simp [S.putTl, hh]
  | fin _ => simp [S.putTl, hh]
  | mem _ => simp [S.putTl, hh]
  | lay a => simp [S.putTl, S.look?, hh]
  | att a => simp [S.putTl, S.look?, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [S.putTl, hh, ho]
    | true => simp [S.putTl, S.look?, hh, ho]

theorem lookOf_mark (s : S) (m : String) : (s.mark m).look? = s.look? := by
  unfold S.mark
  split <;> rfl

theorem digits_put_look (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    ((seatDigits claim).put s g G).look? = s.look? := by
  simp only [seatDigits]
  split
  · rw [lookOf_putFork, lookOf_putTl]
  · exact lookOf_mark s _

/-- The numbers of rows and of columns of the open ledger's arrays. -/
abbrev arrayShapes (s : S) : Option (Array (ℕ × ℕ)) :=
  s.fork?.map fun F => F.trees.map fun T => (T.R, T.K)

/-- **WHERE THE BLOCK ON THE DIGITS SAYS YES, WHAT THE LOOKUP ON THE CALLS RETURNED STANDS AS IT
WAS, AND EVERY ARRAY OF THE OPEN LEDGER HAS THE NUMBERS OF ROWS AND OF COLUMNS THAT IT HAD.** -/
theorem via_digits_kept (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (hplan : (Desc.K3.Law.blockVia (seatDigits claim) piece laid before p guests).planOk = true) :
    (Desc.K3.Law.blockVia (seatDigits claim) piece laid before p guests).Steps
      (fun s s' => s'.look? = s.look? ∧
        (s'.fork?.map fun F => F.trees.map fun T => (T.R, T.K)) =
          s.fork?.map fun F => F.trees.map fun T => (T.R, T.K)) := by
  intro s rs gs s' h
  obtain ⟨F, F', g, t, hF, hn, hl, rfl⟩ := decide_lkPad (seatDigits claim) piece laid before p
    guests s s' rs gs (Desc.K3.Law.blockVia_decide hplan h)
  have hF' : s.fork? = some F := hF
  have e1 : ((seatDigits claim).put s g F').fork? = some F' :=
    seatDigits_keeps claim s g F' (by rw [hF]; rfl) hn
  refine ⟨digits_put_look claim s g F', ?_⟩
  rw [e1, hF']
  show some (F'.trees.map fun T => (T.R, T.K)) = some (F.trees.map fun T => (T.R, T.K))
  rw [lkPad_arrays p.calls p.pub p.lid F F' t [] g hl]

theorem via_digits_leaves_look (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (hplan : (Desc.K3.Law.blockVia (seatDigits claim) piece laid before p guests).planOk = true) :
    (Desc.K3.Law.blockVia (seatDigits claim) piece laid before p guests).Leaves S.look? :=
  fun s rs gs s' h => (via_digits_kept claim piece laid before p guests hplan s rs gs s' h).1

theorem via_digits_leaves_shapes (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (hplan : (Desc.K3.Law.blockVia (seatDigits claim) piece laid before p guests).planOk = true) :
    (Desc.K3.Law.blockVia (seatDigits claim) piece laid before p guests).Leaves arrayShapes :=
  fun s rs gs s' h => (via_digits_kept claim piece laid before p guests hplan s rs gs s' h).2

end AtS

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.lkPad_arrays
#print axioms VerifiableInference.OnPublicFiles.k3_decide_arrays
#print axioms VerifiableInference.OnPublicFiles.via_decide_arrays
#print axioms VerifiableInference.OnPublicFiles.via_digits_kept
#print axioms VerifiableInference.OnPublicFiles.via_digits_leaves_look
#print axioms VerifiableInference.OnPublicFiles.via_digits_leaves_shapes
