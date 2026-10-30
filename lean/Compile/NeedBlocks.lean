-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/NeedBlocks.lean: token programs that go on in the same way after two related answers (words
of this library: lean/GLOSSARY.md).

Generic in the oracles and in the relation. ag is a relation on the answers to each query of each
oracle. (Token programs: `Step`, Rom/Defer.lean; their erased form and its store: `erase`,
Compile/Star.lean.) What it is for: in the step to one hash function of Rom/OverOneN.lean only
marked hash blocks of an answer are queried (`Need`: which hash blocks of the answer to a query are
marked); that the marked hash blocks are those that a program needs is the condition
`FactorsBy (Agree m need)` there (`Agree`: two answers agree on the marked hash blocks).

  `OComp.FactorsBy ag c`
                         (Rom/OverOneN.lean) At every query of the oracle algorithm c, two answers
                         that are related by ag lead to the same program. `facBy_ask_bind`: one
                         query, and what follows it.
  `SFac ag c`            The same for a program c with tokens; at a marked query (`Step.marked`,
                         Rom/Defer.lean) two related answers have the same part for the store, and
                         the program goes on in the same way with their visible parts.
  `SFac.bind`            Sequences.
  `SFac.erase`           If `SFac ag c`, the erased program has `FactorsBy ag`, on every store.

Use. For the compiled scheme: the relation `agree nb` on typed answers is in
Compile/Batch/NeedTable.lean, the lemmas for its programs, one by one, in
Compile/Batch/NeedBlocks.lean.

Limits: nothing on any scheme.
-/
import Compile.EraseKit
import Iop.WireOf
import Rom.OverOneN
import Compile.Ser
import Compile.Spec
import Mathlib.Logic.Equiv.Fin.Basic

open Rom Iop

namespace Compile
namespace Need

/-! ## Part 1 -/

section Generic
variable {S : OSpec} {sp : Split S} {α β : Type} {ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop}

-- the predicate of Rom/OverOneN.lean: at every query, two answers that are related by ag lead to
-- the same program
local notation "FacBy" => OComp.FactorsBy

/-- one query, and what follows it -/
theorem facBy_ask_bind {o : S.ι} {q : S.Dom o} {g : S.Rng o → OComp S β}
    (he : ∀ r r', ag o q r r' → g r = g r') (hg : ∀ r, FacBy ag (g r)) :
    FacBy ag ((OComp.ask o q).bind g) := ⟨he, hg⟩

variable (ag)

/-- `FactorsBy` for a token program: after a marked query the program goes on with the
visible part of the answer, and the store takes the tail. -/
inductive SFac : Step S sp α → Prop
  | pure (a : α) : SFac (.pure a)
  | sample (m : ℕ) {k : Fin (m + 1) → Step S sp α} (h : ∀ r, SFac (k r)) : SFac (.sample m k)
  | plain (o : S.ι) (q : S.Dom o) {k : S.Rng o → Step S sp α}
      (he : ∀ r r', ag o q r r' → k r = k r') (h : ∀ r, SFac (k r)) : SFac (.plain o q k)
  | fresh (ℓ : ℕ) {k : Tok → Step S sp α} (h : ∀ t, SFac (k t)) : SFac (.fresh ℓ k)
  | marked (o : S.ι) (t : Tok) (us : List Tok) (pt : Bits → List Bits → S.Dom o)
      (inj : ∀ vs, Function.Injective fun v => pt v vs) {k : sp.Vis o → Tok → Step S sp α}
      (he : ∀ v ws r r', ag o (pt v ws) r r' →
        (sp.split o r).2 = (sp.split o r').2 ∧ k (sp.split o r).1 = k (sp.split o r').1)
      (h : ∀ v t', SFac (k v t')) : SFac (.marked o t us pt inj k)
  | reveal (ts : List Tok) {k : List Bits → Step S sp α} (h : ∀ w, SFac (k w)) : SFac (.reveal ts k)

variable {ag}

theorem SFac.bind {c : Step S sp α} {g : α → Step S sp β}
    (hc : SFac ag c) (hg : ∀ a, SFac ag (g a)) : SFac ag (c.bind g) := by
  induction hc with
  | pure a => exact hg a
  | sample m _ ih => exact .sample m ih
  | plain o q he _ ih => exact .plain o q (fun r r' h => congrArg (fun x => Step.bind x g) (he r r' h)) ih
  | fresh ℓ _ ih => exact .fresh ℓ ih
  | marked o t us pt inj he _ ih =>
    exact .marked o t us pt inj
      (fun v ws r r' h =>
        ⟨(he v ws r r' h).1,
          funext fun t' => congrArg (fun x => Step.bind (x t') g) (he v ws r r' h).2⟩) ih
  | reveal ts _ ih => exact .reveal ts ih

theorem SFac.erase {c : Step S sp α} (hc : SFac ag c) : ∀ vs, FacBy ag (erase c vs) := by
  induction hc with
  | pure a => exact fun _ => trivial
  | sample m _ ih => exact fun vs r => ih r vs
  | plain o q he _ ih =>
    exact fun vs =>
      ⟨fun r r' h => congrArg (fun x => Compile.erase x vs) (he r r' h), fun r => ih r vs⟩
  | fresh ℓ _ ih => exact fun vs r => ih _ _
  | marked o t us pt inj he _ ih =>
    refine fun vs => ⟨fun r r' h => ?_, fun r => ih _ _ _⟩
    obtain ⟨h1, h2⟩ := he _ _ r r' h
    show Compile.erase _ _ = Compile.erase _ _
    rw [h1, h2]
  | reveal ts _ ih => exact fun vs => ih _ vs

end Generic

end Need
end Compile
