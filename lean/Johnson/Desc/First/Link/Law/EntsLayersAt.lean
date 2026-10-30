-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/EntsLayersAt.lean: THE TWO CLAUSES "entsFront" AND "entsBack" OF WHAT IS
FIXED IN FRONT OF A LAYERS' SEGMENT's BATCHING, AT EVERY STATE REACHED THERE. In the goals' scope.
Statements and proofs: a join.

What is joined: the root lemma `k4_heard_at_front` (K4AtFront.lean: at a state reached at
28 g + 9 whose ledger is open and has its sizes: what the state holds as the segment's own is a
return of K4's hearing, at the seat's parameters with the request's tokens laid in, and the lookup's
`PadNames` stands of what that hearing was handed); `entsFront_of`, `entsBack_of`
  (EntsLayers.lean); `k4_hK` (Johnson/Meaning/PlanesTieK8Plan.lean: the plan's
  length of the third vector is at most the width that the hearing stored) at `IM.k4_of`'s last
  conjunct (the public list of plans is `plansG`'s return); `hear_iU3`
  (Johnson/Meaning/ReadsK4.lean: the plan's structure names o.v.iU3 for the third vector);
  `IM.ground_tails` and the planned reading `posRead`.

  `layers_root`: the root lemma's end with hK and the plan's word on iU3 laid beside.
  `hU_layers`: **the fixed structure names o.v.iU3 for the third vector.**
  `entsFront_at`, `entsBack_at`: **the two clauses at fixed9 (phiAll u ψ) x.1.2, in the letters of
    `OkLayersLeft`.**
  `own_layout`: **what the fixed part holds as the segment's own has the plan's layout**
    (`env_of_hear`): the premise ho of `lenFront_le` and `hlen_layers2`.
PREMISES THAT STAY: the scope; hp (every sub-protocol of the first chain passes its test on the
plan); "reached"; hB (the ledger at the state is open and has its sizes: the promise's); hs (the
static clause at what is fixed); h0 (the third vector is planned with at least one entry).
Limits. These are shown of no state here. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.EntsLayers
import Johnson.Desc.First.Link.Law.K4AtFront
import Johnson.Desc.First.Link.Law.PosAtBatch
import Johnson.Desc.First.Link.Law.PayLayers
import Johnson.Meaning.PlanesTieK8Plan
import Johnson.Meaning.ReadsK4
import Johnson.IMR.K8Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own HPlan2)
open OnBytes.Model.Stages (LinkH)
open OnBytes.PscRun (Sized)
open OnBytes.Desc.First.K4 (hearFl)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K4Values (frontForms backForms)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.PhiAll
open Johnson.Desc.First.Walk.Tied (RchAt Reach rchAt_raw)
open _root_.Fo.Tp (PadNames)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The root lemma's end, with hK and the plan's word on iU3. -/
theorem layers_root (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {g : ℕ} (hg : g < 12) {Q' : Type} {start : Q' → S}
    {z : Q'} {s' : S} (h : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s'))
    (hB : ∃ G', s'.fork? = some G' ∧ Sized G') :
    ∃ (Ph : Layer.Pub) (hpl : HPlan2) (fo : Forest.Heard) (F₄ G : Fork)
      (t u : OnBytes.K.Kc.Tape) (o : Own),
      Ph.y = Bs.G₀.W.layers.y ∧ Bs.G₀.W.G[g]? = some hpl ∧
      hearFl Ph hpl g fo F₄ t = some (o, G, u) ∧ PadNames o.H.fo F₄ ∧ s'.own? = some o ∧
      hpl.nU.getD 2 0 ≤ o.v.K3 ∧ hpl.tl.ix.U.getD 2 none = some o.v.iU3 := by
  obtain ⟨x, tokv, fo, F₄, o, G, F', t, u, _, xg, xP, xG, hh, _, N, efo, ho, _⟩ :=
    k4_heard_at_front hS hR O hp hg h hB
  obtain ⟨_, _, x', _, _, _, _, _, _, xP', _, _, hG⟩ := IM.k4_of hS hR O g hg
  rw [xP'] at hG
  rw [xg] at hh
  refine ⟨{ x.2.P with tokv := tokv }, x.2.hp, fo, F₄, G, t, u, o, ?_, xG, hh, ?_, ho,
    _root_.Meaning.Reads.k4_hK hh hG xG, (_root_.Meaning.Reads.hear_iU3 hh).1⟩
  · show x.2.P.y = _
    rw [xP]
  · rw [efo]
    exact N

/-- **hU AT THE LAYERS.** -/
theorem hU_layers (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {hpl : HPlan2} (hG : Bs.G₀.W.G[g]? = some hpl) {i : ℕ}
    (hi : hpl.tl.ix.U.getD 2 none = some i) {Str : Type} (x : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (28 * g + 9) x)
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) :
    ∀ tlb, (π (fixed9 φ x.1.2).1).1 = some tlb → tlb.ix.U.getD 2 none = some i := by
  obtain ⟨hp', _, Xl, _, hG', _, hX, ht, _⟩ := (IM.ground_tails hS hR O.pub O.blank).1 g hg
  obtain rfl : hpl = hp' := Option.some.inj (hG.symm.trans hG')
  have hx : ((2 * g, 4, 2) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨2 * g, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g = 24), if_neg (by omega : ¬ 2 * g = 24)]⟩
  have e : 14 * (2 * g) + 4 + 3 + 2 = 28 * g + 9 := by omega
  have h' : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (14 * (2 * g) + 4 + 3 + 2) x := by
    rw [e]
    exact h
  have hr := of_readTl (planned_batch_rch planned_pos hS hR O hx hX x h')
  intro tlb e1
  have e1' : x.1.2.tl?.map (blank u) = some tlb := (congrArg Prod.fst (hπ x.1.2)).symm.trans e1
  obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.1 e1'
  have eq : posRead (blank u tl) = posRead Xl.tl := (posRead_blank u tl).trans (hr tl htl)
  have eU : (blank u tl).ix.U = Xl.tl.ix.U := congrArg (·.2.2) eq
  rw [eU, ht]
  exact hi

variable {β : Type}

/-- **THE CLAUSE entsFront AT 28 g + 9.** -/
theorem entsFront_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {g : ℕ} (hg : g < 12) {Str : Type}
    (x : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (28 * g + 9) x)
    (hB : ∃ G', x.1.2.fork? = some G' ∧ Sized G') (u : HTailF2) (ψ : S → β) {nU : Array ℕ}
    (h0 : 0 < nU.getD 2 0)
    (hs : ∀ tlb v, (pi8 (fixed9 (phiAll u ψ) x.1.2).1).1 = some tlb →
      (fixed9 (phiAll u ψ) x.1.2).2 = some v → StaticOk tlb v.F)
    (p4 : OnBytes.Desc.First.K4.Par) :
    ∀ o v, (fixed9 (phiAll u ψ) x.1.2).1.own = some o → (fixed9 (phiAll u ψ) x.1.2).2 = some v →
      ∀ l, frontForms (!p4.k3Runs) p4.P p4.g o v.F = some l →
        EntsAt pi8 nU (fixed9 (phiAll u ψ) x.1.2) l := by
  obtain ⟨Ph, hpl, fo, F₄, G, t, t', o₀, _, hG, hh, N, ho, hK, hi⟩ :=
    layers_root hS hR O hp hg (z := x.1.1) (s' := x.1.2) (rchAt_raw h) hB
  intro o v e _
  obtain rfl : o₀ = o := Option.some.inj (ho.symm.trans e)
  exact entsFront_of pi8 hh hK N hs
    (hU_layers hS hR O hg hG hi x h pi8 (phiAll u ψ) u (fun _ => rfl)) h0

/-- **THE CLAUSE entsBack AT 28 g + 9.** -/
theorem entsBack_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {g : ℕ} (hg : g < 12) {Str : Type}
    (x : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) (28 * g + 9) x)
    (hB : ∃ G', x.1.2.fork? = some G' ∧ Sized G') (u : HTailF2) (ψ : S → β) {nU : Array ℕ}
    (h0 : 0 < nU.getD 2 0)
    (hs : ∀ tlb v, (pi8 (fixed9 (phiAll u ψ) x.1.2).1).1 = some tlb →
      (fixed9 (phiAll u ψ) x.1.2).2 = some v → StaticOk tlb v.F) :
    ∀ o, (fixed9 (phiAll u ψ) x.1.2).1.own = some o →
      EntsAt pi8 nU (fixed9 (phiAll u ψ) x.1.2) (backForms o) := by
  obtain ⟨Ph, hpl, fo, F₄, G, t, t', o₀, _, hG, hh, N, ho, hK, hi⟩ :=
    layers_root hS hR O hp hg (z := x.1.1) (s' := x.1.2) (rchAt_raw h) hB
  intro o e
  obtain rfl : o₀ = o := Option.some.inj (ho.symm.trans e)
  exact entsBack_of pi8 hh hK N hs
    (hU_layers hS hR O hg hG hi x h pi8 (phiAll u ψ) u (fun _ => rfl)) h0

/-- **WHAT THE FIXED PART HOLDS AS THE SEGMENT's OWN HAS THE PLAN's LAYOUT.** -/
theorem own_layout (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {g : ℕ} (hg : g < 12) {Q' : Type} {start : Q' → S}
    {z : Q'} {s' : S} (h : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s'))
    (hB : ∃ G', s'.fork? = some G' ∧ Sized G') (u : HTailF2) (ψ : S → β) :
    ∀ o, (fixed9 (phiAll u ψ) s').1.own = some o → o.v.y = Bs.G₀.W.layers.y := by
  obtain ⟨Ph, hpl, fo, F₄, G, t, t', o₀, hy, _, hh, _, ho, _⟩ :=
    layers_root hS hR O hp hg h hB
  intro o e
  obtain rfl : o₀ = o := Option.some.inj (ho.symm.trans e)
  rw [(OnBytes.Road.K4.env_of_hear hh).1, hy]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.layers_root
#print axioms VerifiableInference.Desc.LinkJoin.hU_layers
#print axioms VerifiableInference.Desc.LinkJoin.entsFront_at
#print axioms VerifiableInference.Desc.LinkJoin.entsBack_at
#print axioms VerifiableInference.Desc.LinkJoin.own_layout
