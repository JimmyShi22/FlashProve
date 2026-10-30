-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/RwFill.lean: FOR THE ITEM "totalB": WHAT `RwFront` (Honest/K9/TotalFront.lean) SAYS,
AT A STATE THAT IS REACHED IN FRONT OF A BATCHING, UNDER ONE PUBLIC PREMISE. Statements and proofs over the sealed
library's laws; no goal is stated.
  `rowsFit_of_fit`   from what the library's three laws end in (a ledger G, the tables funs and the smallness test's
      state tl are there, and at every structure that reads as tl: G.planClaimsF + top8 … ≤ rows): `K9L.rowsFit rows
      pi8 (fixed9 (phiAll u ψ) s)`: the blanked structure reads as the state's, and the snapshot's ledger is the state's
  **`rwFill_lay`**, **`rwFill_att`**, **`rwFill_head`**   in the goals' scope, at the opening of the description,
      UNDER `K9Asks.RowsAsked Z` (Johnson/Desc/First/Link/Law/K9RowsAskLaw.lean: at each of the 25 segments the public
      test "the rows fit" says yes of the segment that stands in Z.p.built.links: A PUBLIC PREMISE; NOTHING HERE PAYS
      IT), at every state s that is reached at the border in front of the segment's batching, and p what `IM.k9At`
      names there: `K9L.rowsFit p.rows pi8 (fixed9 (phiAll u ψ) s)`, at every u and ψ. The library's
      `rows_fit_layers`, `rows_fit_att`, `rows_fit_head`, called
No member. `rowsFit_of_fit` is called by the other three; these by Honest/K9/RwFrontAt.lean.
WHAT IS NOT CLAIMED. `RowsAsked` at any public parameters. "Reached" at any state. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K9.TotalFront
import Johnson.Desc.First.Link.Law.K9RowsAskLaw
import Johnson.Desc.First.Link.Law.PayLayers

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.LinkJoin (pi8 rowsRead)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- From the form in which the library's three laws end. -/
theorem rowsFit_of_fit {β : Type} (u : HTailF2) (ψ : S → β) (s : S) (rows : ℕ) (G : Fork) (funs : Array HFun)
    (tl : HTailF2) (hG : s.fork? = some G) (hf : s.funs? = some funs) (ht : s.tl? = some tl)
    (H : ∀ tl', rowsRead tl' = rowsRead tl → G.planClaimsF + top8 tl' funs ≤ rows) :
    K9L.rowsFit rows pi8 (fixed9 (phiAll u ψ) s) := by
  intro v tlb funs' hv hq
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hv
  have e : pi8 (phiAll u ψ s) = (s.tl?.map (TailClaims.Law.blank u), s.funs?) := rfl
  have hq' : pi8 (phiAll u ψ s) = (some tlb, some funs') := hq
  rw [e, ht, hf] at hq'
  obtain rfl : TailClaims.Law.blank u tl = tlb := Option.some.inj (congrArg Prod.fst hq')
  obtain rfl : funs = funs' := Option.some.inj (congrArg Prod.snd hq')
  have eF : a.F = G := Option.some.inj ((Desc.K9.get_fork s a ha).symm.trans hG)
  show a.F.planClaimsF + top8 (TailClaims.Law.blank u tl) funs ≤ rows
  rw [eF]
  exact H _ rfl

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {β : Type}

theorem rwFill_lay (hE : K9Asks.RowsAsked Z) (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (28 * g + 9) (z, s)) (p : Desc.K9.Where) (kp : IM.k9At Z (2 * g) = some p)
    (u : HTailF2) (ψ : S → β) : K9L.rowsFit p.rows pi8 (fixed9 (phiAll u ψ) s) := by
  obtain ⟨G, funs, tl, p', a1, a2, a3, a4, H⟩ := K9Asks.rows_fit_layers hE hS hR O hg h
  obtain rfl : p' = p := Option.some.inj (a4.symm.trans kp)
  exact rowsFit_of_fit u ψ s _ G funs tl a1 a2 a3 H

theorem rwFill_att (hE : K9Asks.RowsAsked Z) (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (z, s)) (p : Desc.K9.Where)
    (kp : IM.k9At Z (2 * g + 1) = some p) (u : HTailF2) (ψ : S → β) :
    K9L.rowsFit p.rows pi8 (fixed9 (phiAll u ψ) s) := by
  obtain ⟨G, funs, tl, p', a1, a2, a3, a4, H⟩ := K9Asks.rows_fit_att hE hS hR O hg h
  obtain rfl : p' = p := Option.some.inj (a4.symm.trans kp)
  exact rowsFit_of_fit u ψ s _ G funs tl a1 a2 a3 H

theorem rwFill_head (hE : K9Asks.RowsAsked Z) (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (z, s)) (p : Desc.K9.Where) (kp : IM.k9At Z 24 = some p) (u : HTailF2)
    (ψ : S → β) : K9L.rowsFit p.rows pi8 (fixed9 (phiAll u ψ) s) := by
  obtain ⟨G, funs, tl, p', a1, a2, a3, a4, H⟩ := K9Asks.rows_fit_head hE hS hR O h
  obtain rfl : p' = p := Option.some.inj (a4.symm.trans kp)
  exact rowsFit_of_fit u ψ s _ G funs tl a1 a2 a3 H

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.rowsFit_of_fit
#print axioms ProofFile.Honest.K9.rwFill_lay
#print axioms ProofFile.Honest.K9.rwFill_att
#print axioms ProofFile.Honest.K9.rwFill_head
