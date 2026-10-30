-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/ChiTyped.lean: THE TYPED CHALLENGES OF A ROUND THAT DRAWS ONE ELEMENT AND
NOTHING ELSE: EACH SHOWS AS `chiAt` (Johnson/Desc/K8/Honest/FallCount.lean) OF ONE FIELD ELEMENT,
AND NO TWO SHOW THE SAME. Statements and proofs, on the format's draws alone: no block, no state of
the chain, no prover. Lemmas; none of the library's goals.

A round's typed challenges: Run.Ch f e k, with the untyped view Run.drawnOf (Run/PlanDraws.lean). e:
the round's entry in the plan; k: its kind.
  `OneElem e k`   the round's list of draws is one element and a matrix of no entries
  `oneElem_of`   so it is at an entry that states one element, none of them "not 0", no position and
      no matrix entry, at a kind that is neither "seeds" nor "sealed"; `oneElem_bat`: the batching
      round's entry (Johnson/Desc/First/Batch/Kind.lean) is such an entry, whatever work it states:
      THE TEST OF WORK IS NO DRAW
  `elOf`   the field element that a typed challenge gives
  **`shows_chi`**   the untyped view of a typed challenge v of such a round is `chiAt (elOf v)`: one
      element in reduced words, no position, no matrix entry, no digest
  **`elOf_one`**   at most one typed challenge gives one element
Limits. Typed challenges alone: nothing on written verifier messages, on the sampler or on the test
of work.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallCount
import OnBytes.Slice.Draws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Slice Run

/-- The round's list of draws is one element and a matrix of no entries. -/
def OneElem (e : Fmt.Entry) (k : Fmt.Kind) : Prop := Fmt.dsOf e k = [.elem, .trits 0]

theorem oneElem_of (e : Fmt.Entry) (k : Fmt.Kind) (h1 : e.drawE = 1) (h2 : e.drawNZ = 0)
    (h3 : e.poss = 0) (h4 : e.trits = 0) (h5 : k ≠ .seeds) (h6 : k ≠ .sealed) : OneElem e k := by
  unfold OneElem Fmt.dsOf Fmt.dsElems
  rw [h1, h2, h3, h4, if_neg h5, if_neg h6]
  rfl

theorem oneElem_bat (p : K9.Where) (k : Fmt.Kind) (h5 : k ≠ .seeds) (h6 : k ≠ .sealed) :
    OneElem (K9.entry p) k :=
  oneElem_of _ k rfl rfl rfl rfl h5 h6

/-- The field element that a typed challenge gives: the first of its elements. -/
def elOf (e : Fmt.Entry) (k : Fmt.Kind) (v : Ch .two e k) : Cb.Gl.E :=
  (elemsV (Fmt.dsOf e k) v).headD 0

theorem ofE_toE (u : Fmt.Ext3) (h : Fmt.Fld.two.okE u = true) : Slice.ofE (toE u) = u :=
  toE_inj _ _ (by simp only [Fmt.Fld.okE, Slice.ofE, ok_ofF, Bool.and_self]) h (toE_ofE _)

theorem collect_one : ∀ (ds : List Fmt.Draw), ds = [.elem, .trits 0] → ∀ v : Vals .two ds,
    Fmt.collect (outAll .two ds v) = chiAt ((elemsV ds v).headD 0) := by
  intro ds h v
  subst h
  show (⟨[toU3 v.1], [], List.ofFn (fun j : Fin 0 => trit (v.2.1 j)) ++ [], none⟩ : Fmt.Drawn) =
    ⟨[Slice.ofE (toE (toU3 v.1))], [], [], none⟩
  rw [ofE_toE _ (okE_toU3 v.1)]
  simp

/-- **What a typed challenge of such a round shows.** -/
theorem shows_chi (e : Fmt.Entry) (k : Fmt.Kind) (h : OneElem e k) (v : Ch .two e k) :
    drawnOf .two e k v = chiAt (elOf e k v) :=
  collect_one _ h v

theorem elems_inj : ∀ (ds : List Fmt.Draw), ds = [.elem, .trits 0] → ∀ v v' : Vals .two ds,
    (elemsV ds v).headD 0 = (elemsV ds v').headD 0 → v = v' := by
  intro ds h v v' hv
  subst h
  have h1 : v.1 = v'.1 := evE_inj hv
  exact Prod.ext h1 (Prod.ext (funext fun j => j.elim0) rfl)

/-- **At most one typed challenge gives one element.** -/
theorem elOf_one (e : Fmt.Entry) (k : Fmt.Kind) (h : OneElem e k) (x : Cb.Gl.E) :
    Prob.cnt (fun v : Ch .two e k => elOf e k v = x) ≤ 1 :=
  Prob.cnt_le_one fun a b ha hb => elems_inj _ h a b (ha.trans hb.symm)

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.oneElem_bat
#print axioms VerifiableInference.Desc.First.K8.Honest.shows_chi
#print axioms VerifiableInference.Desc.First.K8.Honest.elOf_one
