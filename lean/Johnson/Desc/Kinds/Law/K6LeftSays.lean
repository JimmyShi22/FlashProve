-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6LeftSays.lean: WHAT THE PUBLIC SENTENCE "WHAT THE LOOKUP ON THE CALLS LEFT"
(Johnson/Desc/First/Look/K3LeftItem.lean: k3LeftItem; the table of joints' item left m) SAYS OF THE
VERIFIER's STATE AT WHICH IT HOLDS, FIELD BY FIELD, in the letters in which the calling
sub-protocol's lemmas ask it. A definition of type Prop, statements and proofs.

Why. That sentence stands in the table's promise in front of the calling sub-protocol. It says that
what was heard is the end values of a hearing of SOME rounds from SOME ledger in front, and that
the ledger in hand is the one behind that hearing. Several facts on the state in front of the
caller, which were booked as premises of their own, are consequences: the ledger's next free number
AS AN EQUATION; that the lookup's debts on the planes and on the join are unpaid; the number of the
calls' weights; that the form left for the join names no entry.

WHAT IT IS NOT. Implications from the sentence, which is a premise. Nothing on soundness. NOT HERE:
that the sumcheck over the leaves has a variable; the length of its walk (PadExact.len,
Johnson/Top/H/Keep/PadExact.lean, has it behind the lookup's own accept: the sentence does not hold
that structure).

  notFilled_of_leftQ   from its next free number on, a ledger of which LeftQ holds has no mark.
  push3_at         the second and the third of three entries that are pushed on an array.
  LeftSays h first n F' g   the fields.
  leftAt_says      K3LeftAt at LeftQ n gives them.
  left_says        MAIN: so does k3LeftItem p s, at p's shape, first slot and number of slots.

LETTERS. Under "there is" in the two tops' conclusions: F', g: pinned by the state's two readers;
h (left_says): pinned by p.shape = some h.

-/
import Johnson.Desc.First.Look.K3LeftItem
import Johnson.Desc.First.Look.K3Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model (Fork Forest.Shape Forest.Heard)
open OnBytes.PscRun (Sized)
open VerifiableInference.OnPublicFiles (LeftQ K3LeftAt k3LeftItem)
open VerifiableInference.Desc.First (S)

/-- From its next free number on, a ledger of which LeftQ holds has no mark. -/
theorem notFilled_of_leftQ {n : Nat} {F : Fork} (h : LeftQ n F) (j : Nat) (hj : F.next ≤ j) :
    ¬ OnBytes.PscRun.Filled F j := by
  obtain ⟨hS, _, hf⟩ := h
  unfold OnBytes.PscRun.Filled
  by_cases hlt : j < F.ns
  · have h1 := hf j hj hlt
    have hin : j < F.gotF.size := by
      rw [hS.2.2]
      exact hlt
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hin] at h1 ⊢
    simpa using h1
  · have hout : F.gotF.size ≤ j := by
      rw [hS.2.2]
      omega
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hout]
    simp

/-- The second and the third of three entries that are pushed. -/
theorem push3_at {α : Type} (A : Array α) (a b c : α) :
    (((A.push a).push b).push c)[A.size + 1]? = some b ∧
      (((A.push a).push b).push c)[A.size + 2]? = some c := by
  constructor
  · rw [Array.getElem?_push, if_neg (by simp only [Array.size_push]; omega), Array.getElem?_push,
      if_pos (by simp only [Array.size_push])]
  · rw [Array.getElem?_push, if_pos (by simp only [Array.size_push])]

/-- **What the sentence says of the ledger in hand F' and of what was heard g.** h: the lookup's
shape; first: its first slot; n: the ledger's number of slots. -/
structure LeftSays (h : Forest.Shape) (first n : Nat) (F' : Fork) (g : Forest.Heard) : Prop where
  /-- the next free number, as an equation -/
  next : F'.next = first + OnBytes.Model.Forest.elems h
  ns : F'.ns = n
  sized : Sized F'
  /-- from the next free number on no slot has a mark -/
  free : ∀ j, F'.next ≤ j → ¬ OnBytes.PscRun.Filled F' j
  /-- the debts on the planes and on the join are unpaid -/
  planes : K3.unpaid F' g.owedPlanes = true
  join : K3.unpaid F' g.owedJoin = true
  /-- one weight a call -/
  e : g.e.size = h.NC
  shape : g.shape = h
  zx : g.zx.size = h.dT
  zy : g.zy.size = h.rK
  zk : g.zk.size = h.NC
  zkLen : ∀ c, c < h.NC → (g.zk.getD c #[]).size = ((h.calls[c]?).map (·.n)).getD 0
  /-- the form left for the join names no entry, and every slot that it names is filled -/
  cEnd : g.cEnd.ents = #[]
  filled : _root_.Fo.FilledA F' g.cEnd
  /-- the sumcheck over the leaves was begun, its claim is not made, a challenge a variable -/
  started : g.leaves.started = true
  rowMade : g.leaves.rowMade = false
  rSize : g.leaves.r.size = g.leaves.vars.size
  /-- the slots of its hiding polynomial's coefficients have no mark, where they begin at or
  behind the lookup's first slot -/
  leaves : first ≤ g.leaves.first → ∀ j, g.leaves.first ≤ j →
    j < g.leaves.first + (1 + 2 * h.d + 5) → ¬ OnBytes.PscRun.Filled F' j

/-- **The sharp promise at LeftQ n gives the fields.** -/
theorem leftAt_says {St : Type} (fork : St → Option Fork) (heard : St → Option Forest.Heard)
    (h : Forest.Shape) (lm first n : Nat) (s : St)
    (hL : K3LeftAt fork heard h lm first (LeftQ n) s) :
    ∃ F' g, fork s = some F' ∧ heard s = some g ∧ LeftSays h first n F' g := by
  obtain ⟨F, F', g, rs, hQ, hnext, L, hg, hF⟩ := hL
  have P := L.padLeft
  have nf := notFilled_of_leftQ hQ
  refine ⟨F', g, hF, hg, ⟨by rw [P.next, hnext], by rw [P.rest.2.1, hQ.2.1], P.fit,
    fun j hj hf => ?_, ?_, ?_, ?_, L.shape, L.zx, L.zy, L.zkSize, L.zkLen, L.cEndEnts,
    L.cEndFilled, L.heardIs.lvFlags.1, L.heardIs.lvFlags.2.2, L.heardIs.lvSize,
    fun h0 j h1 h2 hf => ?_⟩⟩
  · rw [P.next] at hj
    exact nf j (by omega) ((P.beyond j hj).1 hf)
  · unfold K3.unpaid
    rw [P.owed, P.owedAt.2.1, (push3_at _ _ _ _).1]
    rfl
  · unfold K3.unpaid
    rw [P.owed, P.owedAt.2.2, (push3_at _ _ _ _).2]
    rfl
  · rw [L.eRaw]
    simp
  · exact nf j (by omega) ((P.leaves j h1 h2).1.1 hf)

/-- **THE SENTENCE "WHAT THE LOOKUP ON THE CALLS LEFT", FIELD BY FIELD.** -/
theorem left_says (p : First.Look.P) (s : S) (L : k3LeftItem p s) :
    ∃ h F' g, p.shape = some h ∧ s.fork? = some F' ∧ s.lookHeard? = some g ∧
      LeftSays h p.first p.ns F' g ∧ g.leaves.start.ents = #[] := by
  obtain ⟨⟨h, hs, hL⟩, hB⟩ := L
  obtain ⟨F', g, hF, hg, Y⟩ := leftAt_says _ _ h p.lm p.first p.ns s hL
  exact ⟨h, F', g, hs, hF, hg, Y, hB g hg⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.notFilled_of_leftQ
#print axioms VerifiableInference.Desc.Kinds.Head.Law.leftAt_says
#print axioms VerifiableInference.Desc.Kinds.Head.Law.left_says
