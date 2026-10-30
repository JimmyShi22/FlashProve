-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ToySk.lean: what a chain's rounds declare, read from a closed
list. A round as `play` meets it (`Step`, Honest/Frame.lean) holds functions; what a plan declares
of it does not: its declared round, its oracle messages, whether a prover's side is defined at it,
its part's number: its skeleton. Two executable tests on a list of skeletons, and six lemmas: where
the tests pass, the six conditions hold of the rounds. No toy example and no sub-protocol occurs
here.

  1  `Sk`, `sk`, `skFits`, `inTimeFrom`   the skeleton; the two tests
  2  `sk_shaped`, `sk_noRoot`, `sk_part0`, `sk_stored`, `sk_own`, `sk_inTime`   the six conditions:
     they are the fields of `ChainServes` and the hypothesis `own₁` of `PlanServes`
     (Honest/Law/RunsFile.lean), written out

Limits.
  * The tests are made for small descriptions: every stored part is of the statement's item 0 and
    two words wide; no tree is taken over.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Oracle)

variable {W Y : Type}

/-! ## 1 The skeleton and the two tests -/

/-- What a plan declares of a round: its declared round, its oracle messages, whether a prover's
side is defined at it, its part's number. -/
abbrev Sk : Type := Fmt.DeclaredRound × List Oracle × Bool × Nat

def sk (u : Step W Y) : Sk := (u.decl, u.oracles, u.move.isSome, u.addr.part)

/-- A source is the chain's own. -/
def ownSrc : Fmt.TreeSource → Bool
  | .own _ => true
  | .taken _ _ => false

/-- Round by round: as many oracle messages as roots; a round without a prover's side declares no
root and is under the part 0; each stored part is of the item 0 and two words wide; no tree is taken
over. -/
def skFits (K : List Sk) : Bool :=
  K.all fun p => p.2.1.length == p.1.entry.roots &&
    (p.2.2.1 || (p.1.entry.roots == 0 && p.2.2.2 == 0)) &&
    p.1.stored.all (fun t => t.item == 0 && t.sh.W == 2) && p.1.opens.all fun o => ownSrc o.2

/-- One opening, against the oracle messages declared so far. -/
def openFits (os : List Oracle) (o : Fmt.Shape × Fmt.TreeSource) : Bool :=
  match o.2 with
  | .own n =>
    match os[n]? with
    | some c => c.words == o.1.W
    | none => false
  | .taken _ _ => true

/-- A tree of the chain's own that a round opens has been declared by that round at the latest, with
the width at which it is opened. `pre`: the oracle messages declared before the list. -/
def inTimeFrom (pre : List Oracle) : List Sk → Bool
  | [] => true
  | p :: K => p.1.opens.all (openFits (pre ++ p.2.1)) && inTimeFrom (pre ++ p.2.1) K

/-! ## 2 The six conditions -/

section
variable {l : List (Step W Y)}

theorem sk_all (hf : skFits (l.map sk) = true) : ∀ u ∈ l,
    u.oracles.length = u.decl.entry.roots ∧
    (u.move.isSome = true ∨ (u.decl.entry.roots = 0 ∧ u.addr.part = 0)) ∧
    (∀ t ∈ u.decl.stored, t.item = 0 ∧ t.sh.W = 2) ∧ ∀ o ∈ u.decl.opens, ownSrc o.2 = true := by
  intro u hu
  have h := List.all_eq_true.1 hf (sk u) (List.mem_map_of_mem hu)
  simp only [sk, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem sk_shaped (hf : skFits (l.map sk) = true) :
    ∀ u ∈ l, u.oracles.length = u.decl.entry.roots := fun u hu => (sk_all hf u hu).1

theorem sk_noRoot (hf : skFits (l.map sk) = true) :
    ∀ u ∈ l, u.move.isSome = false → u.decl.entry.roots = 0 := fun u hu hm =>
  (sk_all hf u hu).2.1.elim (fun h => by rw [hm] at h; cases h) fun h => h.1

theorem sk_part0 (hf : skFits (l.map sk) = true) :
    ∀ u ∈ l, u.move.isSome = false → u.addr.part = 0 := fun u hu hm =>
  (sk_all hf u hu).2.1.elim (fun h => by rw [hm] at h; cases h) fun h => h.2

theorem sk_stored (hf : skFits (l.map sk) = true) {stored : Nat → Nat → Option (List UInt64)}
    (hst : ∀ x, ∃ c, stored 0 x = some c ∧ c.length = 2) :
    ∀ u ∈ l, ∀ t ∈ u.decl.stored, ∀ x, x < 2 ^ t.sh.a →
      ∃ c, stored t.item x = some c ∧ c.length = t.sh.W := by
  intro u hu t ht x _
  obtain ⟨h1, h2⟩ := (sk_all hf u hu).2.2.1 t ht
  rw [h1, h2]
  exact hst x

theorem sk_own (hf : skFits (l.map sk) = true) :
    ∀ u ∈ l, ∀ o ∈ u.decl.opens, ∀ ch j, o.2 ≠ .taken ch j := by
  intro u hu o ho ch j h
  have h' := (sk_all hf u hu).2.2.2 o ho
  rw [h] at h'
  cases h'

end

theorem sk_inTime_from : ∀ (l : List (Step W Y)) (pre : List Oracle),
    inTimeFrom pre (l.map sk) = true → ∀ r s, l[r]? = some s → ∀ o ∈ s.decl.opens, ∀ n,
    o.2 = .own n →
    ∃ c, (pre ++ (l.take (r + 1)).flatMap (·.oracles))[n]? = some c ∧ c.words = o.1.W
  | [], _, _, r, s, hr, _, _, _, _ => by simp at hr
  | u :: t, pre, h, 0, s, hr, o, ho, n, hn => by
    have hs : u = s := by simpa using hr
    subst hs
    have h1 : u.decl.opens.all (openFits (pre ++ u.oracles)) = true :=
      (Bool.and_eq_true_iff.1 h).1
    have h2 := List.all_eq_true.1 h1 o ho
    unfold openFits at h2
    rw [hn] at h2
    have h3 : (match (pre ++ u.oracles)[n]? with
      | some c => c.words == o.1.W
      | none => false) = true := h2
    have e : (pre ++ ((u :: t).take (0 + 1)).flatMap (·.oracles)) = pre ++ u.oracles := by simp
    rw [e]
    cases hc : (pre ++ u.oracles)[n]? with
    | none =>
      rw [hc] at h3
      cases h3
    | some c =>
      rw [hc] at h3
      exact ⟨c, rfl, eq_of_beq h3⟩
  | u :: t, pre, h, r + 1, s, hr, o, ho, n, hn => by
    have hr' : t[r]? = some s := by simpa using hr
    have h2 : inTimeFrom (pre ++ u.oracles) (t.map sk) = true := (Bool.and_eq_true_iff.1 h).2
    obtain ⟨c, hc, hw⟩ := sk_inTime_from t (pre ++ u.oracles) h2 r s hr' o ho n hn
    refine ⟨c, ?_, hw⟩
    have e : (pre ++ ((u :: t).take (r + 1 + 1)).flatMap (·.oracles)) =
        pre ++ u.oracles ++ (t.take (r + 1)).flatMap (·.oracles) := by simp
    rw [e]
    exact hc

/-- The condition `InTime` (Honest/Law/RunsC.lean), written out. -/
theorem sk_inTime {l : List (Step W Y)} (h : inTimeFrom [] (l.map sk) = true) :
    ∀ r s, l[r]? = some s → ∀ o ∈ s.decl.opens, ∀ n, o.2 = .own n →
    ∃ c, ((l.take (r + 1)).flatMap (·.oracles))[n]? = some c ∧ c.words = o.1.W :=
  fun r s hr o ho n hn => sk_inTime_from l [] h r s hr o ho n hn

end ProofFile.Honest

#print axioms ProofFile.Honest.sk_all
#print axioms ProofFile.Honest.sk_shaped
#print axioms ProofFile.Honest.sk_noRoot
#print axioms ProofFile.Honest.sk_part0
#print axioms ProofFile.Honest.sk_stored
#print axioms ProofFile.Honest.sk_own
#print axioms ProofFile.Honest.sk_inTime_from
#print axioms ProofFile.Honest.sk_inTime
