-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/G4/WfJoin.lean: the three calls that stand in Wf.rowsVerify (OnBytes/Iop/Wf.lean) between
the sending of the lookups' oracle message and the lookups: a new group is made, the message joins
it, and the statement is read. What they leave is written out.

`withNewGroupOfMessage c o code maskCode`: the context c with one group more, whose one member is the message o,
and with that group's number noted at the message. `join_val`: where five facts on c's statement
hold (`JoinFacts`), the three calls, run from c, go on from `withNewGroupOfMessage` with the new group's number and
its statement.

Main definitions: withNewGroupOfMessage, JoinFacts.
Main theorems: join_val.
Not claimed. What the sending of the message (sendVerify) leaves.


-/
import OnBytes.G4.WfNext

set_option autoImplicit false

namespace OnBytes.G4

open Blk OnBytes.Params

/-- The context with one group more, whose one member is the message o. -/
def withNewGroupOfMessage (c : Ctx) (o code maskCode : Nat) : Ctx :=
  { c with st := { c.st with
      groups := c.st.groups.push
          { code := code, maskCode := maskCode, members := #[o], kept := #[false] }
      oracles := c.st.oracles.modify o fun y => { y with groups := y.groups ++ [c.st.groups.size] }
          } }

/-- What the making of the group and the joining test. y: the message. -/
structure JoinFacts (c : Ctx) (o code maskCode : Nat) (y : Oracle) : Prop where
  message : c.st.oracles[o]? = some y
  sampled : y.sampled = true
  codes : ∃ a z, c.st.codes.base[code]? = some a ∧ c.st.codes.mask[maskCode]? = some z ∧ z.logN ≤
      a.logN
  main : (y.shape.mainRows == 0 || y.shape.code == code) = true
  mask : (y.shape.maskRows == 0 || y.shape.maskCode == maskCode) = true

/-- A context with other groups. -/
abbrev withGroups (c : Ctx) (g : Array Group) : Ctx := { c with st := { c.st with groups := g } }

/-- A group without a member. -/
abbrev emptyGroup (code maskCode : Nat) : Group := { code := code, maskCode := maskCode }

/-- A group with one member. -/
abbrev oneGroup (o code maskCode : Nat) : Group :=
  { code := code, maskCode := maskCode, members := #[o], kept := #[false] }

theorem modify_pushed (g : Array Group) (G : Group) (F : Group → Group) :
    (g.push G).modify g.size F = g.push (F G) := by
  apply Array.ext_getElem?
  intro i
  simp only [Array.getElem?_modify, Array.getElem?_push]
  by_cases hi : i = g.size
  · subst hi
    simp
  · have hi' : g.size ≠ i := fun e => hi e.symm
    simp [hi, hi']

/-- The new group, the joining and the reading of the statement, written out. -/
theorem join_val {α : Type} (c : Ctx) (o code maskCode : Nat) (y : Oracle)
    (h : JoinFacts c o code maskCode y) (f : Nat → Statement → Blk α) :
    ((Blk.newGroup code maskCode) >>= fun g => (Blk.join g o) >>= fun _ =>
      Blk.statement >>= fun st => f g st) c =
      f c.st.groups.size (withNewGroupOfMessage c o code maskCode).st (withNewGroupOfMessage c o code maskCode) := by
  obtain ⟨a, z, ha, hz, hle⟩ := h.codes
  have h1 : (Blk.newGroup code maskCode) c =
      .ok (c.st.groups.size, withGroups c (c.st.groups.push (emptyGroup code maskCode))) := by
    unfold Blk.newGroup
    rw [bind_ok (show Blk.statement c = .ok (c.st, c) from rfl), ha, bind_ok (get_ok _ _), hz,
      bind_ok (get_ok _ _), bind_ok (must_ok (by simp [hle]) _)]
    rfl
  rw [bind_ok h1]
  have hsize : o < c.st.oracles.size := (Array.getElem?_eq_some_iff.1 h.message).1
  have h2 : (Blk.join c.st.groups.size o)
      (withGroups c (c.st.groups.push (emptyGroup code maskCode))) =
      .ok ((), withNewGroupOfMessage c o code maskCode) := by
    unfold Blk.join
    have hg : (Blk.group c.st.groups.size)
        (withGroups c (c.st.groups.push (emptyGroup code maskCode))) =
        .ok (emptyGroup code maskCode,
          withGroups c (c.st.groups.push (emptyGroup code maskCode))) := by
      show (Blk.get ((c.st.groups.push (emptyGroup code maskCode))[c.st.groups.size]?)) _ = _
      simp [get_ok]
    have ho : (Blk.oracle o) (withGroups c (c.st.groups.push (emptyGroup code maskCode))) =
        .ok (y, withGroups c (c.st.groups.push (emptyGroup code maskCode))) := by
      show (Blk.get (c.st.oracles[o]?)) _ = _
      rw [h.message]
      rfl
    rw [bind_ok hg, bind_ok ho, bind_ok (must_ok (by simp [h.sampled]) _), bind_ok
        (must_ok h.main _),
      bind_ok (must_ok h.mask _), bind_ok (must_ok (by simp) _), bind_ok (must_ok (by simp) _)]
    have hon1 : (Blk.onGroup c.st.groups.size fun G => { G with
          members := G.members.insertIdxIfInBounds
            (((emptyGroup code maskCode).members.filter (· < o)).size) o
          kept := G.kept.insertIdxIfInBounds
            (((emptyGroup code maskCode).members.filter (· < o)).size) false })
        (withGroups c (c.st.groups.push (emptyGroup code maskCode))) =
        .ok ((), withGroups c (c.st.groups.push (oneGroup o code maskCode))) := by
      unfold Blk.onGroup
      rw [if_pos (by simp)]
      simp only [modify_pushed]
      have e1 : (#[] : Array Nat).insertIdxIfInBounds
          (Array.filter (fun x => decide (x < o)) (#[] : Array Nat)).size o = #[o] := by
        simp [Array.insertIdxIfInBounds]
      have e2 : (#[] : Array Bool).insertIdxIfInBounds
          (Array.filter (fun x => decide (x < o)) (#[] : Array Nat)).size false = #[false] := by
        simp [Array.insertIdxIfInBounds]
      simp only [e1, e2]
    refine (bind_ok hon1).trans ?_
    unfold Blk.onOracle
    rw [if_pos hsize]
    rfl
  rw [bind_ok h2]
  rfl

end OnBytes.G4
