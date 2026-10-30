-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/PlanSeatsAllAt.lean: what the maker of all three chains' seats (`planSeatsAll`) and the
test on the seats' roles (`rolesFit`, both Johnson/P5T/PlanSeats.lean) read of the public part of
the IOP as written in Lean. It goes on from Johnson/P5T/PlanSeatsAt.lean. Definitions and statements
with their proofs.

  `chainSeatsBy`, `chainSeats_at`: a later chain's seats: of the declared rounds their entries'
    roots alone are read.
  `planSeatsAllAt pr S es`, `planSeatsAll_at`: **the tie**: `planSeatsAll Z D` is that function at
    `Z.made.proof`, `Z.first.shape` and the three chains' declared rounds' entries.
  `rolesFitAt S ps`, `rolesFit_at`: the test on the roles reads `Z.first.shape` alone; by the make.

Limits. As in Johnson/P5T/PlanSeatsAt.lean. Nothing on soundness.
-/
import Johnson.P5T.PlanSeatsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open Johnson.G

/-- `chainSeats`' own text, at a letter for the roots in front of a round. -/
def chainSeatsBy (rb : Nat → Nat) (chain base : Nat) (c : ChainSends) : List PSeat :=
  c.sends.zipIdx.flatMap fun s =>
    match OnBytes.layTrees c.codes s.1.sent.toArray with
    | none => []
    | some lay =>
      (List.range s.1.sent.length).map fun i =>
        { label := s!"chain {chain}, {s.1.label}", send := 1000 * chain + s.2, seg := none,
          idx := i, j := base + rb (s.1.entry - 1) + lay.tree.getD i 0, t := lay.part.getD i 0,
          shape := (s.1.sent.getD i default).shape, role := .other }

theorem chainSeats_at (chain base : Nat) (c : ChainSends) (dl : List Fmt.DeclaredRound) :
    chainSeats chain base c dl = chainSeatsBy (rootsIn (dl.map (·.entry))) chain base c := by
  unfold chainSeats chainSeatsBy
  simp only [rootsBefore_entries]
  rfl

/-- `planSeatsAll`' own text, at the proof file's three lists of sendings, the shape of the
request's own rounds, and the three chains' entries. -/
def planSeatsAllAt (pr : ChainSends × ChainSends × ChainSends) (S : OnBytes.Params.ReqShape)
    (es : List Fmt.Entry × List Fmt.Entry × List Fmt.Entry) : List PSeat :=
  planSeatsAt pr.1 S es.1 ++ chainSeatsBy (rootsIn es.2.1) 1 (rootsIn es.1 es.1.length) pr.2.1 ++
    chainSeatsBy (rootsIn es.2.2) 2 (rootsIn es.1 es.1.length + rootsIn es.2.1 es.2.1.length)
      pr.2.2

/-- **The tie, for all three chains' seats.** -/
theorem planSeatsAll_at (Z : ProofFile.Pub)
    (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) :
    planSeatsAll Z D = planSeatsAllAt Z.made.proof Z.first.shape
      (D.1.map (·.entry), D.2.1.map (·.entry), D.2.2.map (·.entry)) := by
  unfold planSeatsAll planSeatsAllAt
  simp only [planSeats_at, chainSeats_at, rootsBefore_entries, List.length_map]

/-- `rolesFit`' own text, at the shape of the request's own rounds. -/
def rolesFitAt (S : OnBytes.Params.ReqShape) (ps : List PSeat) : List String :=
  let groups := (OnBytes.reqGroups S).toList
  ps.filterMap fun p =>
    match p.seg, p.role with
    | some (l, _), .own k =>
      if (((S.link[l]?).bind (·.messages[k]?)).map (·.shape)) == some p.shape then none
      else some s!"{p.label}, message {p.idx}: own {k}: another shape"
    | some _, .kept l₀ k =>
      if (((S.link[l₀]?).bind (·.messages[k]?)).map fun m =>
          (m.shape.code, m.shape.mainRows, m.shape.mainDeg)) ==
          some (p.shape.code, p.shape.mainRows, p.shape.mainDeg) then none
      else some s!"{p.label}, message {p.idx}: kept ({l₀}, {k}): other main rows"
    | some (l, _), .carried =>
      if (groups.getD l default).target.shape == p.shape then none
      else some s!"{p.label}, message {p.idx}: carried: another shape"
    | some _, .mask => if p.shape.answers == 0 && p.shape.mainRows == 0 then none
      else some s!"{p.label}, message {p.idx}: the mask has a sample or main rows"
    | some _, .atStart i => if ((S.atStart[i]?).map (·.shape)) == some p.shape then none
      else some s!"{p.label}, message {p.idx}: atStart {i}: another shape"
    | some _, .other => some s!"{p.label}, message {p.idx}: no role"
    | none, _ => none

theorem rolesFit_at (Z : ProofFile.Pub) (ps : List PSeat) :
    rolesFit Z ps = rolesFitAt Z.first.shape ps := rfl

end P5T

#print axioms P5T.chainSeats_at
#print axioms P5T.planSeatsAll_at
#print axioms P5T.rolesFit_at
