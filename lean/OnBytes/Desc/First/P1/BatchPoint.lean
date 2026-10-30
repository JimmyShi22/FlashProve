-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/P1/BatchPoint.lean: batchings and points. These are the two kinds of rounds of
the layers' own rounds (K4) in which nothing is summed. In a batching the verifier draws one element
x and uses its powers 1, x, x^2 and so on to make one claim of n claims. In a point it draws g
elements, at which a multilinear extension is read. Here the plain functions that hear such rounds
(OnBytes/K/Kc/Flat.lean) are taken apart where they return. The sets of bad drawn elements are in
BadSets.lean. Definitions, statements and proofs.

  `powers_size`, `powers_val`: Model.powers x n has n entries, and entry i reads as (the reading of
    x)^i.
  `putBack`: a tape with some elements laid back in front of what its first round still has to
    send.
  `recv_some`, `recvN_some`, `closeRows_some`, `closeN_some`: what the tape was.
  `batch_spec`, `point_spec`, `claimsIn_spec`: what the tape's first round was, what is returned,
    and what is done to the ledger.
  `batch_returns`, `point_returns`: on a tape of the form that the two statements name, the two
    functions do return.

What is not shown. The statements go from a return, but for the last two; nothing is said on when
`Fl.claimsIn` returns. No statement here joins a set of bad elements to a tape. Nothing on
soundness.
-/
import OnBytes.Desc.First.P1.FlSpec
import OnBytes.Desc.First.P1.BadSets
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open OnBytes OnBytes.Model OnBytes.K.Kc

variable {K : Type} [Field K] (ρ : Reading K)

/-! ### The array of powers -/

theorem powersLoop_size (x : E) : ∀ (n : Nat) (c : E) (a : Array E),
    (powersLoop x n c a).size = a.size + n
  | 0, _, _ => rfl
  | n + 1, c, a => by
    rw [powersLoop, powersLoop_size x n, Array.size_push]
    omega

theorem powersLoop_old (x : E) : ∀ (n : Nat) (c : E) (a : Array E) (j : Nat), j < a.size →
    (powersLoop x n c a).getD j zeroE = a.getD j zeroE
  | 0, _, _, _, _ => rfl
  | n + 1, c, a, j, h => by
    rw [powersLoop, powersLoop_old x n _ _ j (by rw [Array.size_push]; omega)]
    simp [Array.getD, Array.getElem_push, h, Nat.lt_succ_of_lt h]

theorem powersLoop_val (x : E) : ∀ (n : Nat) (c : E) (a : Array E) (i : Nat), i < n →
    ρ.val ((powersLoop x n c a).getD (a.size + i) zeroE) = ρ.val c * ρ.val x ^ i
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, c, a, 0, _ => by
    rw [powersLoop, Nat.add_zero, powersLoop_old x n _ _ a.size (by rw [Array.size_push]; omega)]
    simp [Array.getD]
  | n + 1, c, a, i + 1, h => by
    have e : a.size + (i + 1) = (a.push c).size + i := by rw [Array.size_push]; omega
    rw [powersLoop, e, powersLoop_val x n _ _ i (by omega), ρ.mul]
    ring

/-- Model.powers x n has n entries. -/
theorem powers_size (x : E) (n : Nat) : (Model.powers x n).size = n := by
  simp [powers, powersLoop_size]

/-- Entry i of Model.powers x n reads as (the reading of x)^i. -/
theorem powers_val (x : E) (n i : Nat) (h : i < n) :
    ρ.val ((Model.powers x n).getD i zeroE) = ρ.val x ^ i := by
  have := powersLoop_val ρ x n oneE (Array.emptyWithCapacity n) i h
  simpa [powers, ρ.one] using this

/-! ### What the tape was -/

/-- The tape u with the elements l laid back in front of what its first round still has to send. A
tape without a round stays as it is. -/
def putBack (l : List E) : Tape → Tape
  | [] => []
  | ⟨nm, z, w, s, d⟩ :: t => ⟨nm, z, w, l ++ s, d⟩ :: t

theorem putBack_cons (l : List E) (nm : Option String) (z w : Nat) (s d : List E) (t : Tape) :
    putBack l (⟨nm, z, w, s, d⟩ :: t) = ⟨nm, z, w, l ++ s, d⟩ :: t := rfl

theorem putBack_nil : ∀ u : Tape, putBack [] u = u
  | [] => rfl
  | ⟨_, _, _, _, _⟩ :: _ => rfl

theorem putBack_append (a b : List E) : ∀ u : Tape, putBack a (putBack b u) = putBack (a ++ b) u
  | [] => rfl
  | ⟨nm, z, w, s, d⟩ :: t => by
    rw [putBack_cons, putBack_cons, putBack_cons, List.append_assoc]

theorem putBack_ne_nil {l : List E} {u : Tape} (h : putBack l u ≠ []) : u ≠ [] := by
  intro hu
  subst hu
  exact h rfl

/-- One element is taken: it stood first in what the first round still had to send. -/
theorem recv_some {t u : Tape} {x : E} (h : recv t = some (x, u)) :
    t = putBack [x] u ∧ u ≠ [] := by
  unfold recv at h
  split at h
  · injection h with e0
    injection e0 with e1 e2
    subst e1 e2
    exact ⟨rfl, by simp⟩
  · cases h

theorem recvLoop_succ (n : Nat) (a : Array E) (t : Tape) :
    recvLoop (n + 1) a t =
      match recv t with
      | some (x, u) => recvLoop n (a.push x) u
      | none => none := rfl

theorem recvLoop_some : ∀ (n : Nat) (a v : Array E) (t u : Tape),
    recvLoop n a t = some (v, u) →
      ∃ l : List E, l.length = n ∧ v.toList = a.toList ++ l ∧ t = putBack l u
  | 0, a, v, t, u, h => by
    have h' : some (a, t) = some (v, u) := h
    injection h' with e0
    injection e0 with e1 e2
    subst e1 e2
    exact ⟨[], rfl, by simp, (putBack_nil _).symm⟩
  | n + 1, a, v, t, u, h => by
    rw [recvLoop_succ] at h
    cases hr : recv t with
    | none =>
      rw [hr] at h
      have h' : (none : Option (Array E × Tape)) = some (v, u) := h
      cases h'
    | some y =>
      obtain ⟨x, t1⟩ := y
      rw [hr] at h
      have h' : recvLoop n (a.push x) t1 = some (v, u) := h
      obtain ⟨l, hl, hv, ht⟩ := recvLoop_some n _ _ _ _ h'
      refine ⟨x :: l, by rw [List.length_cons, hl], by simp [hv], ?_⟩
      exact (recv_some hr).1.trans ((congrArg (putBack [x]) ht).trans (putBack_append [x] l u))

/-- n elements are taken: they stood first, in their order, in what the first round still had to
send; the rest of the tape is as it was. For n = 0 the tape may be without a round. -/
theorem recvN_some {n : Nat} {t u : Tape} {v : Array E} (h : recvN n t = some (v, u)) :
    v.size = n ∧ t = putBack v.toList u ∧ (n ≠ 0 → u ≠ []) := by
  unfold recvN at h
  obtain ⟨l, hl, hv, ht⟩ := recvLoop_some n _ _ _ _ h
  have hv' : v.toList = l := hv
  refine ⟨?_, ?_, ?_⟩
  · show v.toList.length = n
    rw [hv', hl]
  · rw [hv']
    exact ht
  · intro hn
    cases n with
    | zero => exact absurd rfl hn
    | succ m =>
      apply putBack_ne_nil (l := l)
      rw [← ht]
      intro ht0
      subst ht0
      have h' : (none : Option (Array E × Tape)) = some (v, u) := h
      cases h'

/-- The round that batches rows is closed: what it was. -/
theorem closeRows_some {rows : Nat} {t u : Tape} {x : E} (h : closeRows rows t = some (x, u)) :
    t = ⟨some Model.RoundName.batSigma.name, 0, rows, [], [x]⟩ :: u := by
  unfold closeRows at h
  split at h
  · split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨c1, c2⟩, c3⟩ := hc
      injection h with e0
      injection e0 with e1 e2
      subst c1 c2 c3 e1 e2
      rfl
    · cases h
  · cases h

/-- A round in which n elements are drawn is closed: what it was. -/
theorem closeN_some {name : String} {nz n : Nat} {t u : Tape} {d : List E}
    (h : closeN name nz n t = some (d, u)) :
    d.length = n ∧ ∃ w : Nat, t = ⟨some name, nz, w, [], d⟩ :: u := by
  unfold closeN at h
  split at h
  · split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      obtain ⟨⟨c1, c2⟩, c3⟩ := hc
      injection h with e0
      injection e0 with e1 e2
      subst c1 c2 e1 e2
      exact ⟨c3, _, rfl⟩
    · cases h
  · cases h

/-! ### The three functions -/

/-- **The round that batches rows.** The tape's first round has the batching's name, no element
drawn other than 0, the number of rows, nothing left to send and one drawn element x. The ledger
stays. What is returned is the powers of x. -/
theorem batch_spec {rows : Nat} {F G : Fork} {t u : Tape} {a : Array E}
    (h : Fl.batch rows F t = some (a, G, u)) :
    rows ≠ 0 ∧ F = G ∧ ∃ x : E,
      t = ⟨some Model.RoundName.batSigma.name, 0, rows, [], [x]⟩ :: u ∧
        a = Model.powers x rows := by
  unfold Fl.batch at h
  obtain ⟨h1, hF⟩ := onTape_some.mp h
  unfold Fl.batchOn at h1
  split at h1
  · rename_i hr
    cases hc : closeRows rows t with
    | none =>
      rw [hc] at h1
      exact absurd h1 (by simp)
    | some y =>
      obtain ⟨x, u'⟩ := y
      rw [hc, Option.map_some] at h1
      injection h1 with e0
      injection e0 with e1 e2
      have e2' : u' = u := e2
      subst e2'
      exact ⟨by simpa using hr, hF, x, closeRows_some hc, e1.symm⟩
  · cases h1

/-- On such a tape the function returns. -/
theorem batch_returns {rows : Nat} (hr : rows ≠ 0) (F : Fork) (x : E) (u : Tape) :
    Fl.batch rows F (⟨some Model.RoundName.batSigma.name, 0, rows, [], [x]⟩ :: u) =
      some (Model.powers x rows, F, u) := by
  simp [Fl.batch, Fl.onTape, Fl.batchOn, closeRows, hr]

/-- **The round in which a point is drawn.** The tape's first round has the name, no element drawn
other than 0, nothing left to send and n drawn elements. The ledger stays. What is returned is the
drawn elements in their order. -/
theorem point_spec {r : Model.RoundName} {n : Nat} {F G : Fork} {t u : Tape} {a : Array E}
    (h : Fl.point r n F t = some (a, G, u)) :
    F = G ∧ ∃ (w : Nat) (d : List E),
      t = ⟨some r.name, 0, w, [], d⟩ :: u ∧ d.length = n ∧ a = d.toArray := by
  unfold Fl.point at h
  obtain ⟨h1, hF⟩ := onTape_some.mp h
  unfold Fl.pointOn at h1
  cases hc : closeN r.name 0 n t with
  | none =>
    rw [hc] at h1
    exact absurd h1 (by simp)
  | some y =>
    obtain ⟨d, u'⟩ := y
    rw [hc, Option.map_some] at h1
    injection h1 with e0
    injection e0 with e1 e2
    have e2' : u' = u := e2
    subst e2'
    obtain ⟨hl, w, ht⟩ := closeN_some hc
    exact ⟨hF, w, d, ht, hl, e1.symm⟩

/-- On such a tape the function returns. -/
theorem point_returns (r : Model.RoundName) (F : Fork) (w : Nat) (d : List E) (u : Tape) :
    Fl.point r d.length F (⟨some r.name, 0, w, [], d⟩ :: u) = some (d.toArray, F, u) := by
  simp [Fl.point, Fl.onTape, Fl.pointOn, closeN]

/-- **n hidden values that are sent outside a sumcheck.** They stood first in what the tape's first
round still had to send. They are put under the next n slots with the factor 1. What is returned is
the first of these slots. -/
theorem claimsIn_spec {n j : Nat} {F G : Fork} {t u : Tape}
    (h : Fl.claimsIn n F t = some (j, G, u)) :
    j = F.next ∧ ∃ v : Array E, v.size = n ∧ t = putBack v.toList u ∧ (n ≠ 0 → u ≠ []) ∧
      ({ F with next := F.next + n } : Fork).hideRun F.next v oneE = some G := by
  unfold Fl.claimsIn at h
  obtain ⟨v, G1, u1, h1, k1⟩ := bind_some.mp h
  obtain ⟨hr, rfl⟩ := onTape_some.mp h1
  obtain ⟨_, G2, u2, h2, k2⟩ := bind_some.mp k1
  obtain ⟨_, rfl, rfl⟩ := must_some.mp h2
  obtain ⟨j', G3, u3, h3, k3⟩ := bind_some.mp k2
  obtain ⟨rfl, rfl, rfl⟩ := takeSlots_some.mp h3
  obtain ⟨_, G4, u4, h4, k4⟩ := bind_some.mp k3
  obtain ⟨hG, rfl⟩ := change_some.mp h4
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k4
  obtain ⟨hs, ht, hu⟩ := recvN_some hr
  exact ⟨rfl, v, hs, ht, hu, hG⟩

end OnBytes.Desc.First.P1
