-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/ReadAgainFold.lean: THE SMALLNESS TEST: THE VERIFIER's SECOND COMPUTATION OF
THE COLUMN WEIGHTS OF THE READS' ROW (`readWeightsAgain`, OnBytes/Model/Tail.lean: five loops, one
inside the other, over a running state) WRITTEN AS FIVE FOLDS OVER LISTS, EACH STEP A NAMED
FUNCTION: the same words, entry for entry. That a loop whose body always goes on is a fold is the
library's (`Fo.forIn_foldl`, OnBytes/Tie/Pv/Lookup/Ends/FoCoef.lean). A lemma on the verifier's own
text; none of the library's goals.

  `id_bind`   · `ite_yield` two rewriting lemmas on a loop's body: a step behind a step; a body that
                   is an "if"
  `jStep`   · `sgStep` · `fnStep` · `unStep` · `muStep` the five steps: a row of cells of a segment
                   · a segment · a table · a vector of reads · a matrix
  **`readAgain_fold`**   tl.readWeightsAgain F = ‹the fold of muStep over the matrices, from 0, 0
                   and the array of zeros›, its array
Limits. Nothing on values here.
Nothing is claimed on completeness, soundness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoCoef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2

theorem id_bind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl

theorem ite_yield {β : Type} (c : Prop) [Decidable c] (A B : β) :
    (if c then (pure (ForInStep.yield A) : Id (ForInStep β)) else pure (ForInStep.yield B)) =
      pure (ForInStep.yield (if c then A else B)) := by
  split <;> rfl

/-- One row of cells of a segment: its low digit's column and its high digit's. -/
def jStep (mz base : Nat) (kr : E) (phi : Array E) (w : Array E) (j : Nat) : Array E :=
  (w.modify (base + j) fun x => addE x (mulE kr (phi.getD j zeroE))).modify (mz + (base + j))
    fun x => addE x (scaleNat (mulE kr (phi.getD j zeroE)) (2 ^ t2D0))

/-- One segment; the factor goes on by a step. -/
def sgStep (mz before : Nat) (byStep : E) (Fn : HFun) (s : MProd E (Array E)) (sg : Nat) :
    MProd E (Array E) :=
  ⟨mulE s.fst byStep,
    (List.range Fn.len).foldl (jStep mz (before + sg * Fn.len) s.fst Fn.phi) s.snd⟩

/-- One table, if it lies on matrix mu and vector un. -/
def fnStep (tl : HTailF2) (F : Fork) (mu un before : Nat) (s : MProd Nat (Array E)) (Fn : HFun) :
    MProd Nat (Array E) :=
  if (Fn.mat == mu && Fn.tree == un) = true then
    ⟨s.fst + (tl.mats.getD mu {}).m / Fn.len,
      ((List.range ((tl.mats.getD mu {}).m / Fn.len)).foldl
        (sgStep tl.mz before (powE F.theta (pow2Again tl.tau)) Fn)
        ⟨powE F.theta (F.planClaimsF + tl.firstAgain tl.NM + s.fst * pow2Again tl.tau),
          s.snd⟩).snd⟩
  else ⟨s.fst, s.snd⟩

/-- One vector of reads. -/
def unStep (tl : HTailF2) (F : Fork) (mu before : Nat) (s : MProd Nat (Array E)) (un : Nat) :
    MProd Nat (Array E) :=
  let r := tl.funs.toList.foldl (fnStep tl F mu un before) ⟨s.fst, s.snd⟩
  ⟨r.fst, r.snd⟩

/-- One matrix. -/
def muStep (tl : HTailF2) (F : Fork) (s : MProd Nat (MProd Nat (Array E))) (mu : Nat) :
    MProd Nat (MProd Nat (Array E)) :=
  let r := [0, 2].foldl (unStep tl F mu s.fst) ⟨s.snd.fst, s.snd.snd⟩
  ⟨s.fst + (tl.mats.getD mu {}).m, r.fst, r.snd⟩

/-- **The five loops as five folds.** -/
theorem readAgain_fold (tl : HTailF2) (F : Fork) :
    tl.readWeightsAgain F =
      ((List.range tl.NM).foldl (muStep tl F)
        ⟨0, 0, Array.replicate (2 * tl.mz) zeroE⟩).snd.snd := by
  unfold HTailF2.readWeightsAgain
  simp only [Id.run, ← Array.forIn_toList, id_bind, ite_yield, Fo.forIn_foldl]
  rfl

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.id_bind
#print axioms VerifiableInference.Desc.First.K8.Honest.ite_yield
#print axioms VerifiableInference.Desc.First.K8.Honest.readAgain_fold
