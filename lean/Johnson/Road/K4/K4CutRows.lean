-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4CutRows.lean: K4's sub-protocol's row in the table of a chain's sub-protocols.

Words. The code's `Block` is a sub-protocol at one place. `PlanWritten.cutOf`
(Johnson/Desc/Ok/PlanWritten/CutTest.lean) makes of a list of them a table, a row each: name · place
· number of rounds · length of the list `oracles` · the rounds that tell a tree · `before`. (It is
not the table of steps `Z.cuts`, which `First.cutOf` makes of a plan's entries.)

What it says.
  `rounds_len`      how many rounds K4's table has: 31 + muV + 2 lt + lamS + muH + muH2 + lk, and
                    two more at the first group. By counting the text; no premise.
  `k4Block_told`    K4 tells no tree.
  `k4Block_claims`, `k4Block_after`: its lists of claims are named "front" and "back"; its one run
                    behind the batching "free-slot".
  `k4_row_alone`    the row of a `Block` that is a member of K4's lot seated alone (`IM.LaidAlone`):
                    the seat's name · the seat's place · that number, twice · no told round · the
                    member's `before`.

Limits. Equations on plain data. Which name the seat gives, and what the numbers are at any public
files, is not said here. Nothing on soundness.
-/
import Johnson.Road.K4.K4BlockPlan
import Johnson.Desc.Ok.PlanWritten.CutTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (entries entryOf Par rounds layerRds masked pointRd batchRd)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (toldRounds)
open ProofFile (Cl)

/-- **How many rounds K4's table has.** -/
theorem rounds_len (P : Layer.Pub) (hp : Layer.HPlan2) (g : ℕ) :
    (rounds P hp g).length =
      31 + P.rd.muV + 2 * P.y.h.lt + hp.lamS + P.rd.muH + P.rd.muH2 + P.wsLay.lk +
        (if g == 0 then 2 else 0) := by
  unfold OnBytes.Desc.First.K4.rounds
  by_cases hg : (g == 0) = true
  · simp [hg, layerRds, masked]
    omega
  · simp [hg, layerRds, masked]
    omega

/-- K4's entries are as many as its table's rows. -/
theorem entries_len (P : Layer.Pub) (hp : Layer.HPlan2) (g : ℕ) :
    (entries P hp g).length = (rounds P hp g).length := by
  unfold OnBytes.Desc.First.K4.entries
  rw [List.length_map]

theorem k4Block_rounds (x : Bool × Par) :
    (ProofFile.k4Block x).rounds = (entries x.2.P x.2.hp x.2.g).map fun e => { entry := e } := rfl

theorem k4Block_oracles (x : Bool × Par) :
    (ProofFile.k4Block x).oracles = (entries x.2.P x.2.hp x.2.g).map fun _ => [] := rfl

theorem k4Block_before (x : Bool × Par) : (ProofFile.k4Block x).before = x.2.before := rfl

theorem k4Block_name (x : Bool × Par) : (ProofFile.k4Block x).name = x.2.name := rfl

/-- The names of K4's lists of claims. -/
theorem k4Block_claims (x : Bool × Par) :
    (ProofFile.k4Block x).claims.map (·.1) = ["front", "back"] := rfl

/-- The name of K4's one run behind the batching. -/
theorem k4Block_after (x : Bool × Par) : (ProofFile.k4Block x).after.map (·.1) = ["free-slot"] := rfl

/-- Of a list of empty lists none is kept as «tells a tree». -/
theorem told_aux {α : Type} : ∀ (es : List α) (n : ℕ),
    (((es.map fun _ => ([] : List VerifiableInference.Desc.Oracle)).zipIdx n).filter
      fun x => !x.1.isEmpty) = []
  | [], _ => rfl
  | _ :: es, n => by
    simpa [List.zipIdx_cons] using told_aux es (n + 1)

/-- **K4 tells no tree.** -/
theorem k4Block_told (x : Bool × Par) : toldRounds (ProofFile.k4Block x) = [] := by
  unfold VerifiableInference.PlanWritten.toldRounds
  rw [k4Block_oracles, told_aux]
  rfl

/-- `toldRounds` reads the list `oracles` alone. -/
theorem told_congr {T C T' C' : Type} {b : Block T C} {b' : Block T' C'}
    (ho : b.oracles = b'.oracles) : toldRounds b = toldRounds b' := by
  unfold VerifiableInference.PlanWritten.toldRounds
  rw [ho]

/-- **The row of a member of K4's lot, seated alone.** -/
theorem k4_row_alone {same : S → S → Bool} {b : Block S Cl} {x : Bool × Par} {name : String}
    {a : VerifiableInference.Desc.Place} (la : IM.LaidAlone same b (ProofFile.k4Block x) name a) :
    VerifiableInference.PlanWritten.cutOf [b] =
      [(name, a, (rounds x.2.P x.2.hp x.2.g).length, (rounds x.2.P x.2.hp x.2.g).length, [],
        x.2.before)] := by
  unfold VerifiableInference.PlanWritten.cutOf
  simp only [List.map_cons, List.map_nil]
  rw [IM.alone_name la, IM.alone_place la, IM.alone_rounds la, IM.alone_oracles la,
    IM.alone_before la, told_congr (IM.alone_oracles la), k4Block_told, k4Block_rounds,
    k4Block_oracles, k4Block_before, List.length_map, List.length_map, entries_len]

#print axioms OnBytes.Road.K4.rounds_len
#print axioms OnBytes.Road.K4.entries_len
#print axioms OnBytes.Road.K4.k4Block_rounds
#print axioms OnBytes.Road.K4.k4Block_oracles
#print axioms OnBytes.Road.K4.k4Block_before
#print axioms OnBytes.Road.K4.k4Block_name
#print axioms OnBytes.Road.K4.k4Block_claims
#print axioms OnBytes.Road.K4.k4Block_after
#print axioms OnBytes.Road.K4.told_aux
#print axioms OnBytes.Road.K4.k4Block_told
#print axioms OnBytes.Road.K4.told_congr
#print axioms OnBytes.Road.K4.k4_row_alone

end OnBytes.Road.K4
