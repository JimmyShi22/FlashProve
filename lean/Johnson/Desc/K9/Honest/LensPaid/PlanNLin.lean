-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K9/Honest/LensPaid/PlanNLin.lean (kind K9): the three planners' number of linear claims, written at the
record of the smallness test that the plan returns. Each planner (`Layer.planG`, `Attention.plan`, `Head.planH2`) sets
nLin to its own claims plus `HTailF2.lins` of the record as `shape` first returns it; the record that stands in the plan
is a later one (behind the making of the list of arrays and the owner's entries). `lins` reads of the record the
lookup's numbers f9 and the number of matrices NM alone, and the later steps keep both. One definition; lemmas; two
local macros, which are the library's own (same file), typed again.

  `LKeep a b`      b has a's f9 and NM · `LKeep.lins`: so `lins` is one at both · `LKeep.trans`
  `addTreesF_lkeep`, `borderMeans_lkeep`, `ownerIs_lkeep`, `seamPlan_lkeep`, `ownerHeld_lkeep`   the plans' steps keep
                   the two: after the library's `addTreesF_zkeep` and its fellows
                   (OnBytes/Tie/Pv/Lookup/Ends/FoMadeTail.lean), line by line
  **`planG_nLin`**    hp.nLin = `claimsOf` + hp.tl.lins (`readsCount`)
  **`planA_nLin`**    P.nLin = `ownClaims` + P.seam.tl.lins (`tableReads`)
  **`planH2_nLin`**   hp.nLin = `claimsH` at hp.tl and `readsH`

Limits. What the makers write, and no more: that nLin is the number of claims that a run adds is a test of the run, no
statement here. Nothing ties a plan to a public part here. No property of the protocol is claimed: nothing is said on
its soundness, completeness, binding or hiding.
-/
import OnBytes.Tie.Pv.Lookup.Ends.FoMadeTail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Tie.Pv.Tail.Port
open Fo
open Fo.BatRows (bindE_ok ite_ok)

/-- b has a's record of the lookup's numbers and a's number of matrices. -/
def LKeep (a b : HTailF2) : Prop := b.f9 = a.f9 ∧ b.NM = a.NM

theorem LKeep.lins {a b : HTailF2} (h : LKeep a b) (n : ℕ) : b.lins n = a.lins n := by
  unfold HTailF2.lins HTailF2.linsF
  rw [h.1, h.2]

theorem LKeep.trans {a b c : HTailF2} (h : LKeep a b) (k : LKeep b c) : LKeep a c :=
  ⟨k.1.trans h.1, k.2.trans h.2⟩

set_option hygiene false in
/-- Closes a goal whose hypothesis e says that a routine which throws has returned. -/
local macro "dead" : tactic => `(tactic| first
  | (obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done)
  | (obtain ⟨_, _, e⟩ := bindE_ok e; obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done))

set_option hygiene false in
/-- Takes the branch of a test in which nothing is thrown. -/
local macro "alive" : tactic => `(tactic|
  (rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩; (· dead); obtain ⟨_, _, e⟩ := bindE_ok e))

/-! ### the plans' steps -/

theorem addTreesF_lkeep {tl tl' : HTailF2} {F F' : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', F', T')) :
    LKeep tl tl' := by
  obtain ⟨-, -, e⟩ := addTreesF_fits tl tl' F F' T T' nU aTX hb hbLine h
  rw [e]
  exact ⟨rfl, rfl⟩

theorem borderMeans_lkeep {tl tl' : HTailF2} {iF ownerNo index : Nat}
    (e : tl.borderMeans iF ownerNo index = .ok tl') : LKeep tl tl' := by
  unfold HTailF2.borderMeans at e
  split at e
  · cases e
  · split at e
    · cases e
    · cases e
      exact ⟨rfl, rfl⟩

theorem ownerIs_lkeep (tl : HTailF2) (no : Nat) : LKeep tl (tl.ownerIs no) := ⟨rfl, rfl⟩

theorem seamPlan_lkeep {s s' : Attention.Seam} {nU3 hb hbLine : Nat}
    (e : s.plan nU3 hb hbLine = .ok s') : LKeep s.tl s'.tl := by
  unfold Attention.Seam.plan at e
  dsimp only at e
  obtain ⟨⟨tl, Fp, T⟩, hr, e⟩ := bindE_ok e
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  cases e
  exact addTreesF_lkeep hr

theorem ownerHeld_lkeep {O : Head.Owner} {NGr : Nat} {tl tl' : HTailF2} {Fp : Fork} {Tp : Tail2}
    (e : Head.ownerHeld O NGr tl Fp Tp = .ok tl') : LKeep tl tl' := by
  unfold Head.ownerHeld at e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hB, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain rfl := pureE_ok e
    exact borderMeans_lkeep hB
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

/-! ### the three plans -/

/-- **A layers' plan's number of claims, at the record that the plan returns.** -/
theorem planG_nLin (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) :
    hp.nLin = Layer.claimsOf P.y P.rd g + hp.tl.lins (Layer.readsCount P.y P.rd g) := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have k2 : LKeep tl (tl1.ownerIs g) := (addTreesF_lkeep hA).trans (ownerIs_lkeep tl1 g)
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain rfl := pureE_ok hy
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    dsimp only
    rw [k2.lins]
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      have hy := pureE_ok ‹(pure _ : Except String HTailF2) = Except.ok _›
      have hB := ‹HTailF2.borderMeans _ _ _ _ = Except.ok _›
      dsimp only
      rw [hy, (k2.trans (borderMeans_lkeep hB)).lins]
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

open Attention in
/-- **An attention plan's number of claims, at the record that the plan returns.** -/
theorem planA_nLin (settings : Settings) (i : In) (cf : Cfg) (P : Plan)
    (e : plan settings i cf = .ok P) :
    P.nLin = ownClaims P.S P.fs (Counts.of P.S) + P.seam.tl.lins (tableReads P.S (Counts.of P.S)) := by
  unfold plan at e
  dsimp only at e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨⟨S, fs⟩, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨seam0, h0, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨seam, h1, e⟩ := bindE_ok e
  cases e
  dsimp only
  rw [(seamPlan_lkeep h1).lins]

/-- **The head's plan's number of claims, at the record that the plan returns.** -/
theorem planH2_nLin (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) :
    hp.nLin = Head.claimsH h L hp.tl (Head.readsH h L b) := by
  unfold Head.planH2 at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl, hS, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨⟨tl1, Fp, Tp⟩, hA, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hO, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    cases e
    dsimp only
    unfold Head.claimsH
    rw [((addTreesF_lkeep hA).trans (ownerHeld_lkeep hO)).lins]
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.LKeep
#print axioms ProofFile.Honest.K9.LKeep.lins
#print axioms ProofFile.Honest.K9.LKeep.trans
#print axioms ProofFile.Honest.K9.addTreesF_lkeep
#print axioms ProofFile.Honest.K9.borderMeans_lkeep
#print axioms ProofFile.Honest.K9.ownerIs_lkeep
#print axioms ProofFile.Honest.K9.seamPlan_lkeep
#print axioms ProofFile.Honest.K9.ownerHeld_lkeep
#print axioms ProofFile.Honest.K9.planG_nLin
#print axioms ProofFile.Honest.K9.planA_nLin
#print axioms ProofFile.Honest.K9.planH2_nLin
