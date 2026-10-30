-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FrontBackAt.lean: THE CLAUSES front AND back OF `OkLayers` (OkOne.lean),
TO THE LETTER, AT EVERY STATE REACHED IN FRONT OF A LAYERS' LINK's BATCHING WHOSE LEDGER IS OPEN AND
HAS ITS SIZES. Theorems: joins of other files' lemmas.
How. `k4_heard_at_front` (K4AtFront.lean) has K4's hearing's own equation with the sizes and
`PadNames` in front of it, the state's own as its return, and a later ledger. `hs_back`, `hs_front`,
`hear_fills` (Johnson/Road/K4/Slots/HearFills.lean) say of such a return which slots the runs' forms
name.
  `front_tokv`: the forms of "front" do not read the tokens' values: the seat hears at `{ P with
    tokv := .. }`, the clause reads at P. `k4Back_of_heard`, `k4Front_of_heard`: the clauses' bodies
    at a hearing's return and any ledger U in which what the hearing filled is filled. That the row
    products have four end values an instance comes from the return itself (`hear_parts`,
    `covers_nums`).
  `okBack_at`, `okFront_at`: **the two clauses at `fixed9 (phiAll u ψ) s'`, s' reached at 28 g +
    9.**
PREMISES. The scope (hS, hR, `IM.Open`); hp: every sub-protocol of the first chain passes its test
on the plan; "reached"; hB: the ledger at the state is open and has its sizes; for front: hP, hgp:
the clause's parameters are the seat's.
Limits. hp, hB, hP, hgp are shown of nothing here. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.K4AtFront
import Johnson.Road.K4.Slots.RunsThereNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.PscRun (Sized Filled)
open OnBytes.K.Kc (Tape)
open OnBytes.Desc.First.K4 (hearFl front hear_parts)
open OnBytes.Desc.First.K4.Slots (hs_front hs_back hear_fills covers_nums named_filled of_slot)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.K4Values (backForms frontForms frontWins winOf)
open VerifiableInference.Desc.PhiAll
open Johnson.Desc.First.Walk.Tied (Reach)
open _root_.Fo.Tp (PadNames)

/-- The forms of "front" do not read the tokens' values. -/
theorem front_tokv (rows : Bool) (P : Pub) (tk : _) (g : ℕ) (o : Own) (a b : Aff) :
    front rows { P with tokv := tk } g o a b = front rows P g o a b := rfl

/-- **THE BODY OF back, AT A HEARING's RETURN.** -/
theorem k4Back_of_heard {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own}
    {F G U : Fork} {t u : Tape} (hF : Sized F) (hh : hearFl P hp g fo F t = some (o, G, u))
    (hU : ∀ j, Filled G j → Filled U j) :
    ∀ f ∈ backForms o, ∀ x ∈ f.slots.toList,
      K4Values.InWin (winOf o.wo.toWsMerged.p) x.1 ∨ Filled U x.1 :=
  hs_back hF hh hU

/-- **THE BODY OF front, AT A HEARING's RETURN.** -/
theorem k4Front_of_heard {P : Pub} {tk : _} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own}
    {F G U : Fork} {t u : Tape} (hF : Sized F)
    (hh : hearFl { P with tokv := tk } hp g fo F t = some (o, G, u))
    (hU : ∀ j, Filled G j → Filled U j) (N : PadNames o.H.fo F) :
    (∀ i, i < 4 * P.y.NI → Filled U (o.H.tV.sEnd + i)) ∧
      ∀ rows l, frontForms rows P g o U = some l → ∀ f ∈ l, ∀ x ∈ f.slots.toList,
        (∃ w ∈ frontWins o, K4Values.InWin w x.1) ∨ Filled U x.1 := by
  obtain ⟨hc, -⟩ := hear_parts hh
  have e4 := (covers_nums hc).2.2.1
  have hL := OnBytes.Desc.First.K4.hearFl_later hh
  have hk : ∀ j, Filled F j → Filled U j := fun j hj => hU j (hL.keep j hj).1
  refine ⟨fun i hi => hU _ ((hear_fills hF hh).tVEnd i (by rw [e4]; exact hi)), ?_⟩
  intro rows l hl
  unfold frontForms at hl
  obtain ⟨sh, -, hl⟩ := Option.bind_eq_some_iff.1 hl
  obtain ⟨pq, hpp, hl⟩ := Option.bind_eq_some_iff.1 hl
  exact hs_front hF hh hU (fun _ f hf => named_filled hk (N.rows f hf))
    (hk _ (of_slot N.sBit.2).2) (named_filled hk N.start) sh hpp
    ((front_tokv rows P tk g o _ _).trans hl)

variable {β : Type} {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **THE CLAUSE back.** -/
theorem okBack_at (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {g : ℕ} (hg : g < 12) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s'))
    (hB : ∃ G', s'.fork? = some G' ∧ Sized G') (u : HTailF2) (ψ : S → β) :
    ∀ o v, (fixed9 (phiAll u ψ) s').1.own = some o → (fixed9 (phiAll u ψ) s').2 = some v →
      Sized v.F ∧ ∀ f ∈ backForms o, ∀ x ∈ f.slots.toList,
        K4Values.InWin (winOf o.wo.toWsMerged.p) x.1 ∨ Filled v.F x.1 := by
  obtain ⟨x, tokv, fo, F₄, o₀, G, F', t, w, -, -, -, -, hh, hz, -, -, ho, hF', hl, hz'⟩ :=
    k4_heard_at_front hS hR O hp hg h hB
  intro o v e1 e2
  obtain rfl : o₀ = o := Option.some.inj (ho.symm.trans e1)
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 e2
  have eF : (pubOf b).F = F' := Option.some.inj ((K9.get_fork s' b hb).symm.trans hF')
  rw [eF]
  exact ⟨hz', k4Back_of_heard hz hh fun j hj => (hl.keep j hj).1⟩

/-- **THE CLAUSE front.** -/
theorem okFront_at (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {g : ℕ} (hg : g < 12) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s'))
    (hB : ∃ G', s'.fork? = some G' ∧ Sized G') (u : HTailF2) (ψ : S → β)
    (p : OnBytes.Desc.First.K4.Par) (hP : p.P = Bs.G₀.W.layers) (hgp : p.g = g) :
    ∀ o v, (fixed9 (phiAll u ψ) s').1.own = some o → (fixed9 (phiAll u ψ) s').2 = some v →
      Sized v.F ∧ (∀ i, i < 4 * p.P.y.NI → Filled v.F (o.H.tV.sEnd + i)) ∧
      ∀ l, frontForms (!p.k3Runs) p.P p.g o v.F = some l → ∀ f ∈ l, ∀ x ∈ f.slots.toList,
        (∃ w ∈ frontWins o, K4Values.InWin w x.1) ∨ Filled v.F x.1 := by
  obtain ⟨x, tokv, fo, F₄, o₀, G, F', t, w, -, a2, a3, -, hh, hz, hN, hofo, ho, hF', hl, hz'⟩ :=
    k4_heard_at_front hS hR O hp hg h hB
  intro o v e1 e2
  obtain rfl : o₀ = o := Option.some.inj (ho.symm.trans e1)
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 e2
  have eF : (pubOf b).F = F' := Option.some.inj ((K9.get_fork s' b hb).symm.trans hF')
  rw [eF, hP, ← a3, hgp, ← a2]
  obtain ⟨k1, k2⟩ := k4Front_of_heard hz hh (fun j hj => (hl.keep j hj).1) (hofo ▸ hN)
  exact ⟨hz', k1, k2 _⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.front_tokv
#print axioms VerifiableInference.Desc.LinkJoin.k4Back_of_heard
#print axioms VerifiableInference.Desc.LinkJoin.k4Front_of_heard
#print axioms VerifiableInference.Desc.LinkJoin.okBack_at
#print axioms VerifiableInference.Desc.LinkJoin.okFront_at
