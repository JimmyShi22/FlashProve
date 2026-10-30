-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/CarriedSecond.lean (kind K10): THE SECOND CONJUNCT OF `CarriedAt`
(Leads.lean, beside this file: "what stands behind the closing"), FROM TWO PLAIN SENTENCES. A
statement and its proof.

What the conjunct says, unfolded (`Sig.over`, Cb/Ld/LdSig.lean): there are a seed z and a witness v
of
the messages that are carried past the batching (those with kp) such that (i) each such message's
own word, as x lays it, decodes with the sample that x lays to v's message, and (ii) the joint A₀'s
relaxed relation holds, at what x lays for it, of these messages and v's further part. THE SEED IS
IDLE. NO WITNESS OF THE TABLE OF JOINTS IS READ: it is a sentence on the typed statement and its
oracles alone.

What is said. `carried_second_of_decs`: the conjunct, IN THE VERY FORM in which
carriedAt_of takes it (its h2), from: z₀ (any seed) · u with hdec (every message with kp decodes, at
x's sample and word, to u's) · v₂ with hA (A₀'s relaxed relation of u and v₂).

Limits. hdec AND hA ARE PREMISES. hdec cannot come from the law's own end ("every word decodes"
stands there BEHIND CarriedAt); it is to come from what the closing's row opens behind. A₀ IS A
LETTER HERE: whether it is free where the law is spent, or fixed by who composes, is not said.
General in the group, the caller's letters and x. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.Leads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold Iop IOR KObj OnBytes.Flat
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H

variable {S : Sig GE} (R : RowsK S) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) R.G.C.J)
  (Z : Evader GE (R.G.Row B)) (fx : Fin ((R.Sh.fold Sb sl Z).n + 1) × GE) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep Sb sl Z).kp).Msg × Wp)) (bC bZ : ℕ)
  (w₀ : S.Wit × Wp) (w₁ : LdBrW R.G (R.sizeB keep Sb sl Z).kp Wp)

/-- **CarriedAt's SECOND CONJUNCT.** -/
theorem carried_second_of_decs (L : List (BatFoldCaller GE))
    (x : ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).X ×
      ((kBatFoldRide L).src (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).E.Str)
    (z₀ : Z.D) (u : (S.sub (R.sizeB keep Sb sl Z).kp).Msg)
    (hdec : ∀ i : {o // (R.sizeB keep Sb sl Z).kp o}, S.decs x.1.2 x.2.1.2 i.1 = some (u i))
    (v₂ : Wp) (hA : A₀.relR (x.1.1.2, x.2.1.1) (u, v₂)) :
    ∃ (z : Z.D) (v : (S.sub (R.sizeB keep Sb sl Z).kp).Wit × Wp),
      ((S.sub (R.sizeB keep Sb sl Z).kp).over A₀).relR
        ((batX (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) x.1 z).2,
          ((ldBrG R.G (R.sizeB keep Sb sl Z).kp E₀).map x.2.1).2) v :=
  ⟨z₀, (fun i => (u i, fun _ => 0), v₂), fun i => hdec i, hA⟩

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.carried_second_of_decs
