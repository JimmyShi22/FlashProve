-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/G/PlannedAtG.lean: the program's planner over a monad, at the identity monad and any
hash h, is the planner's text with the digest as an argument, at the digest that h gives on the
three public files.

"The program" is the Lean program verify-on-bytes. OnBytes/ChecksWithHashAsArgument/M/Model/Verify.lean has the
program's planner (Model.Verify.planned) written once more over a monad in which the hash is asked.
It hashes at one place: the digest of the three public files. OnBytes/Tie/ChainsAtCfg.lean has the
planner's text with that digest as an argument (plannedAt), and says how its value hangs on the
digest (plannedAt_at).

Main definition: digestG h pol KL layout: the digest that h gives on the three public files.
Main theorems.
  plannedG_at: the planner over a monad, at the identity monad and h, is plannedAt at digestG h.
    No premise.
  digestG_port: at the program's hash digestG is the program's digest.
  plannedG_of_planned: where the program's planner returns p, the planner at h returns p with
    digestG h as its digest and the seven chains put at it; the public part and the links are p's.
    Asked: digestG h has 32 bytes; each of p's seven strings of parameter bytes has fewer than 2^64
    bytes (the conditions of plannedAt_at). For four of the seven (the two shared and the two second
    chains) no theorem gives the bound; the lengths do not hang on the digest
    (Tie.size_bytes_chainsAtCfg_any).
  plannedG_back: the way back, under the like conditions at the value of the planner at h.

Not claimed. That h's answers have 32 bytes. Nothing on what the stages behind the planner do with
the digest. Nothing on soundness. The program does not import this file.


-/
import OnBytes.Tie.ChainsAtCfg
import OnBytes.ChecksWithHashAsArgument.M.Model.Verify

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK.G

open OnBytes.TwoPort OnBytes.Model OnBytes.Model.Verify
open OnBytes.Tie (plannedAt plannedAt_at chainsAtCfg planned_eq)

/-- The digest that h gives on the three public files. -/
def digestG (h : M.HashM Id) (pol KL : ByteArray) (layout : Option ByteArray) : ByteArray :=
  M.Model.Verify.configuration (m := Id) h pol (layout.getD .empty) KL

/-- At the program's hash it is the program's digest. -/
theorem digestG_port (pol KL : ByteArray) (layout : Option ByteArray) :
    digestG formatHashFastForm pol KL layout = configuration pol (layout.getD .empty) KL := rfl

/-- **The planner over a monad, at h, is the planner's text at h's digest.** -/
theorem plannedG_at (h : M.HashM Id) (pol KL : ByteArray) (layout : Option ByteArray) :
    (M.Model.Verify.planned (m := Id) h pol KL layout).run =
      plannedAt pol KL layout (digestG h pol KL layout) := by
  unfold M.Model.Verify.planned plannedAt digestG
  generalize M.Model.Verify.configuration (m := Id) h pol (layout.getD .empty) KL = c
  cases publicOf pol KL layout with
  | error e => rfl
  | ok X =>
    show (ExceptT.run (do
        let chains ← (chainsOf X layout c : ExceptT String Id Chains)
        pure { X := X, cfg := c, chains := chains, built := ← builtOf X chains } :
          ExceptT String Id Planned)) =
      (do
        let chains ← chainsOf X layout c
        pure { X := X, cfg := c, chains := chains, built := ← builtOf X chains } :
          Except String Planned)
    cases chainsOf X layout c with
    | error e => rfl
    | ok chains =>
      show (ExceptT.run (do
          pure { X := X, cfg := c, chains := chains, built := ← builtOf X chains } :
            ExceptT String Id Planned)) =
        (do
          pure { X := X, cfg := c, chains := chains, built := ← builtOf X chains } :
            Except String Planned)
      cases builtOf X chains <;> rfl

/-- **Where the program's planner returns p, the planner at h returns p put at h's digest.** -/
theorem plannedG_of_planned (h : M.HashM Id) {pol KL : ByteArray} {layout : Option ByteArray}
    {p : Planned} (hd : (digestG h pol KL layout).size = 32)
    (hb : ∀ n : ChainName, (p.chains.bytes n).size < 2 ^ 64)
    (hp : planned pol KL layout = .ok p) :
    (M.Model.Verify.planned (m := Id) h pol KL layout).run =
      .ok { p with cfg := digestG h pol KL layout
                   chains := chainsAtCfg p.chains (digestG h pol KL layout) } := by
  rw [plannedG_at]
  rw [planned_eq] at hp
  exact plannedAt_at (Params.configurationDigest_size _) hd hb hp

/-- The way back: where the planner at h returns q, the program's planner returns q put at the
program's digest. -/
theorem plannedG_back (h : M.HashM Id) {pol KL : ByteArray} {layout : Option ByteArray}
    {q : Planned} (hd : (digestG h pol KL layout).size = 32)
    (hb : ∀ n : ChainName, (q.chains.bytes n).size < 2 ^ 64)
    (hq : (M.Model.Verify.planned (m := Id) h pol KL layout).run = .ok q) :
    planned pol KL layout =
      .ok { q with
        cfg := configuration pol (layout.getD .empty) KL
        chains := chainsAtCfg q.chains (configuration pol (layout.getD .empty) KL) } := by
  rw [plannedG_at] at hq
  rw [planned_eq]
  exact plannedAt_at hd (Params.configurationDigest_size _) hb hq

end OnBytes.TieK.G

#print axioms OnBytes.TieK.G.plannedG_at
#print axioms OnBytes.TieK.G.plannedG_of_planned
#print axioms OnBytes.TieK.G.plannedG_back
