-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/StBehind.lean: THE STATEMENT BEHIND A YES OF THE CLOSING, WRITTEN OUT:
the statement in front with the group's test begun and the fresh mask's message marked as spent:
nothing else. Definitions, statements and proofs.

Why. Whoever ties K10's block to a table of promises owes the whole promise BEHIND the block, and
that what rides past it still holds. Both ask what the closing's yes leaves of the statement. The
closing's text writes the statement in two places alone: the ground's `beginRunP` and
`spendAsMaskP`.
  `spent S id`: S with the message number id marked as spent as a mask.
  `fold_st`, `closing_st`, `closeFrame_st`: at a yes: the frame's mask is some id, the frame's group
    is there as G, and THE STATEMENT BEHIND IS `spent (begun S g G) id`.
  `spent_extends`, `behind_extends`, `behind_inOrder`: it extends the statement in front; it is in
    order if that is.
  `behind_size`, `behind_shape`, `behind_samples`, `behind_codes`: as many messages; each with its
    shape and its sample rows; the same table of codes. `behind_groups`, `behind_group_ne`: every
    other group as it was. `behind_group`: the frame's group: marked as in its test, without open
    rows.
Limits. On the statement alone: what the closing leaves of the other fields of the carried record is
Leaves.lean's. Nothing is said of a table's promise here. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.Inv
import Johnson.Desc.First.Close.Law.LayBegun
import Johnson.Desc.Means.Page
import Johnson.Desc.Means.Holds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Means

/-- S with the message number id marked as spent as a mask. -/
def spent (S : Statement) (id : Nat) : Statement :=
  { S with oracles := S.oracles.modify id fun x => { x with spentAsMask := true } }

/-- **The statement behind a yes of the fold.** -/
theorem fold_st {S S' : Statement} {F : FoldShape} {row : GroupRow} {m : Nat}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {out : SingleRows}
    (h : fold S F row m es rs = .ok (out, S')) : S' = spent S m := by
  unfold fold at h
  cases hD : foldD 0 (onSt S) F row (some m) es rs with
  | error e => rw [hD] at h; exact absurd h (by simp [Except.map])
  | ok y =>
    rw [hD] at h
    simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    unfold foldD at hD
    split at hD
    · rename_i eE eR rE rR
      obtain ⟨_, -, hD⟩ := ok_bind hD
      obtain ⟨_, -, hD⟩ := ok_bind hD
      obtain ⟨_, -, hD⟩ := ok_bind hD
      obtain ⟨p, k2, hD⟩ := ok_bind hD
      simp only [pure, Except.pure, Except.ok.injEq] at k2
      subst k2
      obtain ⟨_, -, hD⟩ := ok_bind hD
      obtain ⟨_, -, hD⟩ := ok_bind hD
      obtain ⟨d2, k5, hD⟩ := ok_bind hD
      have k5 := got_ok k5
      obtain ⟨z, -, hD⟩ := ok_bind hD
      split at hD
      · obtain ⟨_, -, hD⟩ := ok_bind hD
        obtain ⟨w, -, hD⟩ := ok_bind hD
        simp only [pure, Except.pure, Except.ok.injEq] at hD
        subst hD
        unfold Ground.spendAsMaskP at k5
        split at k5
        · obtain rfl := Option.some.inj k5
          rfl
        · cases k5
      · exact absurd hD (by simp)
    · exact absurd hD (by simp)

/-- **The statement behind a yes of the closing.** -/
theorem closing_st {P : Plan} {S S' : Statement} {g : Nat} {mask : Option Nat}
    {rs : List Fmt.RoundView} {out : SingleRows} (h : closing P S g mask rs = .ok (out, S')) :
    ∃ G id, mask = some id ∧ S.groups[g]? = some G ∧ S' = spent (begun S g G) id := by
  unfold closing at h
  split at h
  · obtain ⟨m, k0, h⟩ := ok_bind h
    obtain ⟨p, k1, h⟩ := ok_bind h
    obtain ⟨_, -, h⟩ := ok_bind h
    obtain ⟨G, x, a1, -, -, a4⟩ := bat_inv (row := p.1) (lay := p.2.1) (S1 := p.2.2) k1
    refine ⟨G, m, got_ok k0, a1, ?_⟩
    rw [fold_st h, a4]
  · exact absurd h (by simp)

/-- **The statement behind a yes of the frame's closing.** -/
theorem closeFrame_st {owed : Option Nat} {f : ReqFrame} {S : Statement} {es : List Fmt.Entry}
    {rs : List Fmt.RoundView} {x : ReqFrame × Statement} (h : closeFrame owed f S es rs = .ok x) :
    ∃ G id, f.mask = some id ∧ S.groups[f.group]? = some G ∧
      x.2 = spent (begun S f.group G) id := by
  unfold closeFrame at h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨L, -, h⟩ := ok_bind h
  obtain ⟨Gf, -, h⟩ := ok_bind h
  obtain ⟨_, -, h⟩ := ok_bind h
  obtain ⟨y, kc, h⟩ := ok_bind h
  obtain ⟨G, id, e1, e2, e3⟩ := closing_st (out := y.1) (S' := y.2) kc
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨G, id, e1, e2, e3⟩

section
variable (S : Statement) (g : Nat) (G : Group) (id : Nat)

theorem behind_inOrder (hI : InOrder S) (hG : S.groups[g]? = some G) :
    InOrder (spent (begun S g G) id) :=
  (hI.begun g G hG).onOracle id _ (fun _ => rfl) fun _ => rfl

theorem spent_extends (T : Statement) : Extends T (spent T id) :=
  Extends.of_shapes rfl fun o => by
    show ((T.oracles.modify id _)[o]?).map _ = _
    rw [Array.getElem?_modify]
    split
    · cases T.oracles[o]? <;> rfl
    · rfl

theorem behind_extends : Extends S (spent (begun S g G) id) :=
  (extends_begun S g G).trans (spent_extends id _)

theorem behind_groups : (spent (begun S g G) id).groups = (begun S g G).groups := rfl

/-- The same table of codes. -/
theorem behind_codes : (spent (begun S g G) id).codes = S.codes := (behind_extends S g G id).codes

/-- Each message with its shape. -/
theorem behind_shape (o : Nat) :
    ((spent (begun S g G) id).oracles[o]?).map (fun x : Oracle => x.shape) =
      (S.oracles[o]?).map fun x : Oracle => x.shape := by
  show (((closeLedgers S G.members.toList).oracles.modify id _)[o]?).map _ = _
  exact (map_modify (fun x : Oracle => x.shape) _ id o
    (fun x : Oracle => { x with spentAsMask := true }) fun _ => rfl).trans
    (closeLedgers_shape _ S o)

/-- Each message with its sample rows. -/
theorem behind_samples (o : Nat) :
    ((spent (begun S g G) id).oracles[o]?).map (fun x : Oracle => x.sampleRows) =
      (S.oracles[o]?).map fun x : Oracle => x.sampleRows := by
  show (((closeLedgers S G.members.toList).oracles.modify id _)[o]?).map _ = _
  exact (map_modify (fun x : Oracle => x.sampleRows) _ id o
    (fun x : Oracle => { x with spentAsMask := true }) fun _ => rfl).trans
    (closeLedgers_sampleRows _ S o)

/-- As many messages. -/
theorem behind_size : (spent (begun S g G) id).oracles.size = S.oracles.size := by
  have h1 := (behind_extends S g G id).size
  by_contra c
  have c' : S.oracles.size < (spent (begun S g G) id).oracles.size := by omega
  have e := behind_shape S g G id S.oracles.size
  rw [Array.getElem?_eq_getElem c', Array.getElem?_eq_none (Nat.le_refl _)] at e
  cases e

/-- Every other group as it was. -/
theorem behind_group_ne (g' : Nat) (hne : g' ≠ g) :
    (spent (begun S g G) id).groups[g']? = S.groups[g']? := by
  show (begun S g G).groups[g']? = _
  rw [begun_groups, Array.getElem?_modify, if_neg fun c => hne c.symm]

theorem behind_group (hG : S.groups[g]? = some G) :
    (spent (begun S g G) id).groups[g]? = some { G with inRun := true, rows := #[] } :=
  OnBytes.LayLaw.begun_group S g G hG

end

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.closeFrame_st
#print axioms VerifiableInference.Desc.First.Close.behind_inOrder
#print axioms VerifiableInference.Desc.First.Close.behind_extends
#print axioms VerifiableInference.Desc.First.Close.behind_group
#print axioms VerifiableInference.Desc.First.Close.behind_size
#print axioms VerifiableInference.Desc.First.Close.behind_samples
#print axioms VerifiableInference.Desc.First.Close.behind_group_ne
