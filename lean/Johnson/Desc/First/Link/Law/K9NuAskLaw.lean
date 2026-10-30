-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/K9NuAskLaw.lean: THE LAW OF THE TEST `nuPosB`
(Johnson/Desc/First/Link/K9NuAsk.lean): ITS YES IS THE PREMISE h0 OF `ents_of_static`
(EntsAtBatch.lean) AND OF ALL THAT CALLS IT, IN ITS OWN LETTERS, AT nU := `ProofFile.k8NU G₀ Xl`, AT THE
BLANK LETTERS' BUILT SEGMENT. Statements and proofs.

  `nuB_is`: the tie of the second text: ProofFile.k8NU G X = nuB G.W X (by rfl).
  `nuPosB_iff`: the test's yes, written out: an "if and only if".
  `zip_kind`: an entry of the built segments with their routines exchanged has the kind and the
    group of the entry that it stems from (beside `zip_at`, which has the structure,
    the ledger and the names).
  `NuAsked Z`: at each l < 25 a segment stands in Z.p.built.links and the test says yes of it.
  `h0_of_asked`: **NuAsked Z; an opening; l < 25; Xl the blank letters' built segment l ⊢ 0 <
    (ProofFile.k8NU Bs.G₀ Xl).getD 2 0.**
  `entsFirst_asked`, `entsSecond_asked`: so the two attention clauses (EntsAtt.lean) at that nU,
    without h0.
Limits. `NuAsked Z` IS A PREMISE: no running text asks the test. No soundness statement.

-/
import Johnson.Desc.First.Link.K9NuAsk
import Johnson.Desc.First.Link.Law.EntsAtt
import Johnson.Desc.ProofFile.Lot.K8
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.IMR.OwnSeat
import Johnson.IMR.LinkSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K9Asks
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P (ParC Heard)
open VerifiableInference.Desc.LinkJoin (EntsAt entsFirst_of_plain entsSecond_of_plain StaticOk)
open H2K5.Door (plainThereB)
open K5Law
open ProofFile (Cl)

theorem nuB_is (G : ProofFile.Ground) (X : LinkH) : ProofFile.k8NU G X = nuB G.W X := rfl

theorem nuPosB_iff (W : Verify.Public) (X : LinkH) :
    nuPosB W X = true ↔ 0 < (nuB W X).getD 2 0 := by
  unfold nuPosB
  exact decide_eq_true_iff

/-- An entry of the built segments with their routines exchanged: its kind and its group. -/
theorem zip_kind {bs ls : Array LinkH} {j : ℕ} {Y : LinkH}
    (h : (bs.zipWith (fun b l => { b with run := l.run }) ls)[j]? = some Y) :
    ∃ b, bs[j]? = some b ∧ Y.kind = b.kind ∧ Y.g = b.g := by
  rw [Array.getElem?_zipWith] at h
  cases hb : bs[j]? with
  | none =>
    rw [hb] at h
    cases h
  | some b =>
    rw [hb] at h
    cases hx : ls[j]? with
    | none =>
      rw [hx] at h
      cases h
    | some y =>
      rw [hx] at h
      obtain rfl := Option.some.inj h
      exact ⟨b, rfl, rfl, rfl⟩

/-- The lengths hang on the segment's kind and group alone. -/
theorem nuB_congr (W : Verify.Public) {X Y : LinkH} (hk : Y.kind = X.kind) (hg : Y.g = X.g) :
    nuB W Y = nuB W X := by
  unfold nuB
  rw [hk, hg]

/-- At each segment's number a segment stands, and the test says yes of it. -/
def NuAsked (Z : ProofFile.Pub) : Prop :=
  ∀ l < 25, ∃ X, Z.p.built.links[l]? = some X ∧ nuPosB Z.p.X X = true

variable {P : VerifierAndGoals.PublicFiles} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **h0, IN ITS SPENDERS' OWN LETTERS.** -/
theorem h0_of_asked (hE : NuAsked Z) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) :
    0 < (ProofFile.k8NU Bs.G₀ Xl).getD 2 0 := by
  obtain ⟨links, e⟩ := _root_.Meaning.K2.blank_built O.blank
  rw [e] at e3
  obtain ⟨b, hb, hk, hg⟩ := zip_kind e3
  obtain ⟨X, y1, y2⟩ := hE l hl
  obtain rfl : b = X := Option.some.inj (hb.symm.trans y1)
  rw [nuB_is, ProofFile.Law.blankBy_W O.blank, nuB_congr Z.p.X hk hg]
  exact (nuPosB_iff Z.p.X b).1 y2

variable {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α)
  (rd : α → Option (Forest.Heard × Heard)) (cA : ParC)

/-- The clause entsFirst at the seat's own lengths, without h0. -/
theorem entsFirst_asked (hE : NuAsked Z)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {s : S}
    (hp : plainThereB cA.iU3 cA.nW s = true)
    (hrd : ∀ g h, rd (φ s) = some (g, h) → s.heard5? = some h)
    (hs : ∀ tlb v, (π (fixed9 φ s).1).1 = some tlb → (fixed9 φ s).2 = some v → StaticOk tlb v.F)
    (hU : ∀ tlb, (π (fixed9 φ s).1).1 = some tlb → tlb.ix.U.getD 2 none = some cA.iU3) :
    ∀ l', fsFirst rd cA (fixed9 φ s) = some l' →
      EntsAt π (ProofFile.k8NU Bs.G₀ Xl) (fixed9 φ s) l' :=
  entsFirst_of_plain π φ rd cA hp hrd hs hU (h0_of_asked hE O hl e3)

/-- The clause entsSecond at the seat's own lengths, without h0. -/
theorem entsSecond_asked (hE : NuAsked Z)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {s : S}
    (hp : plainThereB cA.iU3 cA.nW s = true)
    (hrd : ∀ g h, rd (φ s) = some (g, h) → s.heard5? = some h)
    (hs : ∀ tlb v, (π (fixed9 φ s).1).1 = some tlb → (fixed9 φ s).2 = some v → StaticOk tlb v.F)
    (hU : ∀ tlb, (π (fixed9 φ s).1).1 = some tlb → tlb.ix.U.getD 2 none = some cA.iU3) :
    ∀ l', fsSecond rd cA (fixed9 φ s) = some l' →
      EntsAt π (ProofFile.k8NU Bs.G₀ Xl) (fixed9 φ s) l' :=
  entsSecond_of_plain π φ rd cA hp hrd hs hU (h0_of_asked hE O hl e3)

end VerifiableInference.Desc.K9Asks

#print axioms VerifiableInference.Desc.K9Asks.nuB_is
#print axioms VerifiableInference.Desc.K9Asks.nuPosB_iff
#print axioms VerifiableInference.Desc.K9Asks.zip_kind
#print axioms VerifiableInference.Desc.K9Asks.nuB_congr
#print axioms VerifiableInference.Desc.K9Asks.h0_of_asked
#print axioms VerifiableInference.Desc.K9Asks.entsFirst_asked
#print axioms VerifiableInference.Desc.K9Asks.entsSecond_asked
