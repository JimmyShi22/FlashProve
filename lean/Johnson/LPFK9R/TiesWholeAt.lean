-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK9R/TiesWholeAt.lean: THE THREE STRUCTURES OF TIES OF THE
LINK's LAW (`LayersTies`, `AttTies`, `HeadTies`: Johnson/Desc/First/Link/Law/PayLayers.lean,
PayAttention.lean, PayHead.lean), EACH WHOLE, AT A SEATED LINK OF ITS SORT: all 21 fields, with
every parameter named off the seat's own letters. The assembly of K4Ties, K6Ties, K8Ties,
MergeTie and GuestsTie (this folder's) and of Johnson/H2K5R/K5Tie.lean. (In the Lean names
a «block» is a sub-protocol.)

What is said.
  `kinds_at`: the kinds of a sort's hearing sub-protocols at the numbers that the ties name: closed
    facts on `kindsBeforeBatching`: so no premise on them is left. `layers_ties_at`: **at a seated link of the
    sort «layers»: there are the link Lk, the parameters p with `k4ParAt Z B.G₀ l = some p` and the
    built entry X with `LayersTies Lk p (ProofFile.k8NU B.G₀ X)`.** `att_ties_at`: **of the sort
    «attention»: `AttTies Lk (parCOf A) (ProofFile.k8NU B.G₀ X)`, A the plan of that link's group.**
    `head_ties_at`: **of the sort «head»: `HeadTies Lk B.G₀.W.hS iU3 (B.G₀.built.size - 1) 4 (parOf
    …) (ProofFile.k8NU B.G₀ X)`**, where iU3 is the third of the tail's tables' arrays.

Limits. The seat's four premises (the base returns; the parts' base; the chain; the link's sort)
stand; at the head's link that the tail names a third table's array. THE TIES ARE NOT THE TAKES:
`LayersTake`, `AttTake`, `HeadTake` ask more (the lookups' runs' share; what is fixed; «full»):
nothing of that is here. Nothing on soundness.

-/
import Johnson.LPFK9R.K4Ties
import Johnson.H2K5R.K5Tie
import Johnson.LPFK9R.K6Ties
import Johnson.LPFK9R.K8Ties
import Johnson.LPFK9R.MergeTie
import Johnson.LPFK9R.GuestsTie
import Johnson.Desc.First.Link.Law.PayLayers
import Johnson.Desc.First.Link.Law.PayAttention
import Johnson.Desc.First.Link.Law.PayHead

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.LinkJoin (LayersTies AttTies HeadTies)
open VerifiableInference.Desc.First.Att (P.parCOf)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workAtW)
open ProofFile (Cl)

/-- The kinds at the numbers that the ties name. -/
theorem kinds_at (first : Bool) :
    (kindsBeforeBatching .layers first)[2]? = some KindName.K4 ∧
    (kindsBeforeBatching .layers first)[4]? = some KindName.K8 ∧
    (kindsBeforeBatching .attention first)[2]? = some KindName.K5 ∧
    (kindsBeforeBatching .attention first)[4]? = some KindName.K8 ∧
    (kindsBeforeBatching .head first)[3]? = some KindName.K6 ∧
    (kindsBeforeBatching .head first)[5]? = some KindName.K8 ∧
    (kindsBeforeBatching .head first)[8]? = some KindName.K11 := by
  cases first <;> simp [kindsBeforeBatching, VerifiableInference.Desc.First.kindOfModelPart]

variable {o : ProofFile.SecondHashFunctionArgument}

/-- **LayersTies, WHOLE, AT A SEATED LINK.** -/
theorem layers_ties_at {Z : ProofFile.Pub} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B)
    (hb : (ProofFile.partsAt (ProofFile.pureSeat o Z) B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) B).road = .ok c) (l : ℕ)
    (hl : (ProofFile.subsOf Z)[l]? = some ModelPart.layers) :
    ∃ Lk p X, c.links[l]? = some Lk ∧ k4ParAt Z B.G₀ l = some p ∧
      B.G₀.built.toList[l]? = some X ∧ LayersTies Lk p (ProofFile.k8NU B.G₀ X) := by
  obtain ⟨h2, h4, _⟩ := kinds_at (l == 0)
  obtain ⟨Lk, e, p, hp, tF, tB, tFr⟩ := k4_ties hB hb hc l .layers hl h2
  obtain ⟨Lk8, e8, X, hX, tE, tL, tT⟩ := k8_ties hB hb hc l .layers hl 4 h4 (by omega)
  obtain ⟨LkG, eG, tG⟩ := guests_ties_16 hB hb hc l .layers hl (by decide)
  obtain rfl : Lk = Lk8 := Option.some.inj (e.symm.trans e8)
  obtain rfl : Lk = LkG := Option.some.inj (e.symm.trans eG)
  exact ⟨Lk, p, X, e, hp, hX, ⟨tF, tB, tG, tE, tL, tFr, tT⟩⟩

/-- **AttTies, WHOLE, AT A SEATED LINK.** -/
theorem att_ties_at {Z : ProofFile.Pub} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B)
    (hb : (ProofFile.partsAt (ProofFile.pureSeat o Z) B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) B).road = .ok c) (l : ℕ)
    (hl : (ProofFile.subsOf Z)[l]? = some ModelPart.attention) :
    ∃ Lk Xl A X, c.links[l]? = some Lk ∧ B.G₀.built[l]? = some Xl ∧ Xl.kind = 1 ∧
      B.G₀.W.A[Xl.g]? = some A ∧ B.G₀.built.toList[l]? = some X ∧
      AttTies Lk (P.parCOf A) (ProofFile.k8NU B.G₀ X) := by
  obtain ⟨_, _, h2, h4, _⟩ := kinds_at (l == 0)
  obtain ⟨Lk, Xl, A, e, hXl, hk, hA, t1, t2, t3⟩ := H2K5.k5_ties hB hb hc l .attention hl h2
  obtain ⟨Lk8, e8, X, hX, tE, tL, tT⟩ := k8_ties hB hb hc l .attention hl 4 h4 (by omega)
  obtain ⟨LkG, eG, tG⟩ := guests_ties_16 hB hb hc l .attention hl (by decide)
  obtain rfl : Lk = Lk8 := Option.some.inj (e.symm.trans e8)
  obtain rfl : Lk = LkG := Option.some.inj (e.symm.trans eG)
  exact ⟨Lk, Xl, A, X, e, hXl, hk, hA, hX, ⟨t1, t2, t3, tG, tE, tL, tT⟩⟩

/-- **HeadTies, WHOLE, AT A SEATED LINK.** -/
theorem head_ties_at {Z : ProofFile.Pub} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B)
    (hb : (ProofFile.partsAt (ProofFile.pureSeat o Z) B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) B).road = .ok c) (l : ℕ)
    (hl : (ProofFile.subsOf Z)[l]? = some ModelPart.head)
    (iU3 : ℕ) (hU : B.G₀.W.H.tl.ix.U.getD 2 none = some iU3) :
    ∃ Lk X, c.links[l]? = some Lk ∧ B.G₀.built.toList[l]? = some X ∧
      HeadTies Lk B.G₀.W.hS iU3 (B.G₀.built.size - 1) 4 (parOf B.G₀.W.hS (workAtW B.G₀.W))
        (ProofFile.k8NU B.G₀ X) := by
  obtain ⟨_, _, _, _, h3, h5, h8⟩ := kinds_at (l == 0)
  obtain ⟨Lk, e, t6, tJ⟩ := k6_ties hB hb hc l .head hl h3 iU3 hU
  obtain ⟨Lk8, e8, X, hX, tE, tL, tT⟩ := k8_ties hB hb hc l .head hl 5 h5 (by omega)
  obtain ⟨LkG, eG, tG⟩ := guests_ties_27 hB hb hc l hl
  obtain ⟨LkM, eM, tM⟩ := merge_tie hB hb hc l .head hl h8
  obtain rfl : Lk = Lk8 := Option.some.inj (e.symm.trans e8)
  obtain rfl : Lk = LkG := Option.some.inj (e.symm.trans eG)
  obtain rfl : Lk = LkM := Option.some.inj (e.symm.trans eM)
  exact ⟨Lk, X, e, hX, ⟨t6, tJ, tG, tE, tM, tL, tT⟩⟩

end LPFK9

#print axioms LPFK9.kinds_at
#print axioms LPFK9.layers_ties_at
#print axioms LPFK9.att_ties_at
#print axioms LPFK9.head_ties_at
