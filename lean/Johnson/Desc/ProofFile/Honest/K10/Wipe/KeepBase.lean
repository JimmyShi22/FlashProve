-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/KeepBase.lean: the closing of a segment (K10): small general laws that the files
Wipe/KeepEach.lean, KeepK3.lean, KeepK4.lean, KeepK5.lean, KeepK6K7.lean and KeepK8K11.lean share. General in the
state's type σ and in a function w : σ → σ, but for the last two, which speak of the first chain's state and its
wiping. No kind of block is named. Theorems alone.

Words. wipeS sets to zero the targets of the rows that a state of the first chain holds (Honest/K10/WipeS.lean says
which). Two states are one under w where w s = w s'. A reader does not see w where it returns at w s what it returns
at s. A writer goes through w where it returns at w s the image under w of what it returns at s. Two outcomes are
alike where both refuse with the same word, or both return and the values are one under w (AlikeE, Wipe/Alike.lean). A
block does alike (Whole2 w) where its decide, each of its runs of claims and each of its runs behind the batching have
like outcomes at two states that are one under w; the claims of a run are then equal.

What is proved.
  blind2          a reader that does not see w returns one value at two states that are one under w
  put2, putE2, putO2   a writer that goes through w returns like values at two such states; putE2: a writer that may
                  refuse; putO2: one that may return nothing
  AlikeE.iteB     two branchings on equal Bools are alike where their arms are
  whole2_bare     a block that states no run does alike where its decide does
  whole2_same     a block does alike where it has the decide and the runs behind the batching of a block that does,
                  and its runs of claims are among that block's
  snd_comm        a run that goes through w still does when the value beside the state is dropped
  wCl_eq          two states that are one under w, each beside the same list of claims, are one under wCl w
  forM_same       a list of tests, run in a row, has one outcome at two functions that agree on the list
  alike_of_wiped, alikeCl_of_wiped   a state x with x = wipeS y is one with y under wipeS; the same beside a list of
                  claims

By what. Rewriting by the law on one state; cases on a Bool or an outcome; for forM_same, recursion on the list; for
the last two, that a second wiping changes nothing (Wipe/WipeLaws.lean: wipeS_idem).

Limits. Nothing is shown of any block here. putO2 and whole2_same have no user yet (Wipe/Wrap2.lean's whole_same2 says
what whole2_same says). No property of the protocol is claimed: nothing is said on its soundness, completeness,
binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Alike
import Johnson.Desc.ProofFile.Honest.K10.Wipe.WipeLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)

variable {σ Cl : Type} {w : σ → σ}

/-! ## 1 From one state to two -/

/-- A reader that does not see w returns one value at two states that are one under w. -/
theorem blind2 {α : Type} {f : σ → α} (h : ∀ s, f (w s) = f s) {s s' : σ} (hs : w s = w s') : f s = f s' := by
  rw [← h s, ← h s', hs]

/-- A writer that goes through w returns, at two states that are one under w, states that are one under w. -/
theorem put2 {α : Type} {f : σ → α → σ} (h : ∀ s x, f (w s) x = w (f s x)) {s s' : σ} (hs : w s = w s') (x : α) :
    w (f s x) = w (f s' x) := by
  rw [← h s x, ← h s' x, hs]

/-- The same for a writer that may refuse: its two outcomes are alike. -/
theorem putE2 {α : Type} {f : σ → α → Except String σ} (h : ∀ s x, f (w s) x = (f s x).map w) {s s' : σ}
    (hs : w s = w s') (x : α) : AlikeE w (f s x) (f s' x) := by
  have e : (f s x).map w = (f s' x).map w := by rw [← h s x, ← h s' x, hs]
  exact e

/-- The same for a writer that may return nothing: both return nothing, or states that are one under w. -/
theorem putO2 {α : Type} {f : σ → α → Option σ} (h : ∀ s x, f (w s) x = (f s x).map w) {s s' : σ}
    (hs : w s = w s') (x : α) : (f s x).map w = (f s' x).map w := by
  rw [← h s x, ← h s' x, hs]

/-! ## 2 Branchings -/

/-- Two branchings on equal Bools are alike where their arms are. -/
theorem AlikeE.iteB {α β : Type} {v : α → β} {c c' : Bool} {a a' b b' : Except String α} (hc : c = c')
    (h1 : AlikeE v a a') (h2 : AlikeE v b b') :
    AlikeE v (if c then a else b) (if c' then a' else b') := by
  subst hc
  cases c with
  | true => exact h1
  | false => exact h2

/-! ## 3 Blocks -/

/-- A block that states no run does alike where its decide does. -/
theorem whole2_bare {b : Block σ Cl} (hd : Decides2 w b) (hc : b.claims = []) (ha : b.after = []) : Whole2 w b := by
  refine ⟨hd, fun c h => ?_, fun c h => ?_⟩
  · rw [hc] at h
    cases h
  · rw [ha] at h
    cases h

/-- A block does alike where it has the decide and the runs behind the batching of a block that does, and its runs of
claims are among that block's. -/
theorem whole2_same {b c : Block σ Cl} (W : Whole2 w b) (e1 : c.decide = b.decide)
    (e2 : ∀ x ∈ c.claims, x ∈ b.claims) (e3 : c.after = b.after) : Whole2 w c := by
  refine ⟨fun s s' rs gs gs' hs hg => ?_, fun x hx => W.2.1 x (e2 x hx), fun x hx => W.2.2 x (e3 ▸ hx)⟩
  rw [e1]
  exact W.1 s s' rs gs gs' hs hg

/-! ## 4 Runs -/

/-- A run that goes through w still does when the value beside the state is dropped. -/
theorem snd_comm {α : Type} {x y : Except String (α × σ)} (h : x = y.map fun z => (z.1, w z.2)) :
    x.map (·.2) = (y.map (·.2)).map w := by
  subst h
  cases y with
  | error e => rfl
  | ok z => rfl

/-- A list of tests, run in a row, has one outcome at two functions that agree on the list. -/
theorem forM_same {α : Type} (f g : α → Except String Unit) :
    ∀ l : List α, (∀ a ∈ l, f a = g a) → l.forM f = l.forM g
  | [], _ => rfl
  | a :: l, h => by
    show (f a >>= fun _ => l.forM f) = (g a >>= fun _ => l.forM g)
    rw [h a (List.mem_cons.2 (Or.inl rfl)), forM_same f g l fun x hx => h x (List.mem_cons.2 (Or.inr hx))]

/-- Two states that are one under w, each beside the same list of claims, are one under wCl w. -/
theorem wCl_eq {c : List Cl} {x y : σ} (h : w x = w y) : wCl w (c, x) = wCl w (c, y) := by
  show (c, w x) = (c, w y)
  rw [h]

/-! ## 5 At the first chain's state -/

/-- A state x with x = wipeS y is one with y under the wiping. -/
theorem alike_of_wiped {x y : S} (h : x = wipeS y) : wipeS x = wipeS y := by
  rw [h, wipeS_idem]

/-- The same, each state beside the same list of claims. -/
theorem alikeCl_of_wiped {c : List Cl} {x y : S} (h : x = wipeS y) : wCl wipeS (c, x) = wCl wipeS (c, y) := by
  show (c, wipeS x) = (c, wipeS y)
  rw [h, wipeS_idem]

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.blind2
#print axioms ProofFile.Honest.K10.put2
#print axioms ProofFile.Honest.K10.putE2
#print axioms ProofFile.Honest.K10.putO2
#print axioms ProofFile.Honest.K10.AlikeE.iteB
#print axioms ProofFile.Honest.K10.whole2_bare
#print axioms ProofFile.Honest.K10.whole2_same
#print axioms ProofFile.Honest.K10.snd_comm
#print axioms ProofFile.Honest.K10.forM_same
#print axioms ProofFile.Honest.K10.wCl_eq
#print axioms ProofFile.Honest.K10.alike_of_wiped
#print axioms ProofFile.Honest.K10.alikeCl_of_wiped
