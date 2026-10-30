-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/K9LensAskLaw.lean: THE LAW OF THE TEST `lensFitB`
(Johnson/Desc/First/Link/K9LensAsk.lean): ITS YES, WITH NAMED BOUNDS ON EACH RUN's OWN NUMBER OF
CLAIMS, GIVES "THE RUNS' CLAIMS ARE AT MOST THE PLAN's NUMBER" (the field hlen of `EqTake`,
ExpsAt.lean, and of `NumbersOk`, SortNumbers.lean) AT WHAT IS FIXED AT EVERY STATE REACHED IN FRONT
OF EVERY ONE OF THE 25 BATCHINGS; AND `NumbersOk`'s CLAUSE "the stated functions are there". In the
goals' scope. Statements and proofs.

  `lensFitB_iff`: the test's yes, written out: an "if and only if".
  `len8_le`: K8's share at what is fixed at a state: at most 4 + (NM + the reads off the skeleton),
    at the built segment's numbers.
  `LensAsked Z`: at each l < 25 a segment stands in Z.p.built.links and the test says yes of it.
  `hlen_layers`, `hlen_att`, `hlen_head`: **LensAsked Z; the scope; reached in front of the
    batching; the segment has its sort's order; the bounds ⊢ ∀ v, q.2 = some v → lenRuns q (rlOf L
    tm ‹the sort's len›) ≤ v.F.planClaimsF**, q := fixed9 (phiAll u ψ) s'.
  `funs_layers`, `funs_att`, `funs_head`: **((pi8 q.1).2).isSome = true there**: no premise but the
scope and "reached". THE BOUNDS, EACH A PREMISE: the lookups' entries: l3 o q at most Forest.lins of
the plan's shape at "objects" (the calls': y.fo, a.fs, HLy.fs; the digits': the built segment's
tl.f9), at most 3 at "planes", at most 1 at the attention's "join"; the sort's own runs: lenFront at
most frontB; the attention's two together at most attOwnB; the head's three at most 29, 4 and 2, its
join at most 1.
Limits. `LensAsked Z` AND ALL THE BOUNDS ARE PREMISES. No soundness statement.

-/
import Johnson.Desc.First.Link.K9LensAsk
import Johnson.Desc.First.Link.Law.LensAtFront
import Johnson.Desc.First.Link.Law.K9RowsAskLaw
import Johnson.Desc.First.Link.Law.OkAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K9Asks
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Tie.Pv.Tail.Port (readsList)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf layShapes attShapes nScores)
open Cb.Pv.Tail (Tab)
open VerifiableInference.Desc (Block Chain FileDescription Link Claim)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att.P (ParC)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.K4Run (lenFront)
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.Kinds.Head.Law (tabsOfPlan Seen fsK6 fsJoin)
open Johnson.Desc.First.Walk.Tied (Reach)
open K5Law

variable {β : Type}

theorem lensFitB_iff (W : Verify.Public) (l : ℕ) (X : LinkH) :
    lensFitB W l X = true ↔ ∃ a ps n, ownLenB W l = some a ∧ pairsAt W l = some ps ∧
      claimsAt W l = some n ∧
      a + (4 + (X.tl.NM + readsB X.tl.NM X.tl.mats ps)) + Forest.lins X.tl.f9 ≤ n := by
  unfold lensFitB
  constructor
  · intro h
    split at h
    · rename_i a ps n e1 e2 e3
      exact ⟨a, ps, n, e1, e2, e3, of_decide_eq_true h⟩
    · exact nomatch h
  · rintro ⟨a, ps, n, e1, e2, e3, h⟩
    rw [e1, e2, e3]
    exact decide_eq_true h

/-- K8's share at what is fixed at a state. -/
theorem len8_le (u : HTailF2) (ψ : S → β) (s : S) (tlP : HTailF2) (sh : List Tab)
    (hf : ∀ funs, s.funs? = some funs → ∀ tl : HTailF2,
      (readsList tl funs).length = readsLenOf tl.NM tl.mats sh)
    (ht : ∀ tl, s.tl? = some tl → rowsRead tl = rowsRead tlP) :
    len8 pi8 (fixed9 (phiAll u ψ) s) ≤ 4 + (tlP.NM + readsLenOf tlP.NM tlP.mats sh) := by
  unfold len8
  show (match ((s.tl?.map (blank u), s.funs?) : Option HTailF2 × Option (Array HFun)) with
    | (some tlb, some funs) => 4 + (tlb.NM + (readsList tlb funs).length)
    | _ => 0) ≤ _
  cases h1 : s.tl? with
  | none => exact Nat.zero_le _
  | some tl =>
    cases h2 : s.funs? with
    | none => exact Nat.zero_le _
    | some funs =>
      show 4 + ((blank u tl).NM + (readsList (blank u tl) funs).length) ≤ _
      rw [hf funs h2 (blank u tl)]
      have e := ht tl h1
      have e1 : (blank u tl).NM = tlP.NM := congrArg (·.1) e
      have e2 : (blank u tl).mats = tlP.mats := congrArg (·.2.1) e
      rw [e1, e2]

/-- The snapshot's ledger is the state's. -/
theorem snap_is {α : Type} (φ : S → α) {s : S} {v : Pub9} (h : (fixed9 φ s).2 = some v) :
    s.fork? = some v.F := by
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 (show (atS.get? s).map pubOf = some v from h)
  exact K9.get_fork s p hp

/-- At each segment's number a segment stands, and the test says yes of it. -/
def LensAsked (Z : ProofFile.Pub) : Prop :=
  ∀ l < 25, ∃ X, Z.p.built.links[l]? = some X ∧ lensFitB Z.p.X l X = true

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The test's yes at the blank letters' own segment and public parameters. -/
theorem lens_at (hE : LensAsked Z)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) :
    ∃ a ps n, ownLenB Bs.G₀.W l = some a ∧ pairsAt Bs.G₀.W l = some ps ∧
      claimsAt Bs.G₀.W l = some n ∧
      a + (4 + (Xl.tl.NM + readsB Xl.tl.NM Xl.tl.mats ps)) + Forest.lins Xl.tl.f9 ≤ n := by
  obtain ⟨X, x1, x2⟩ := built_tl O.blank e3
  obtain ⟨X', y1, y2⟩ := hE l hl
  obtain rfl : X = X' := Option.some.inj (x1.symm.trans y1)
  rw [← ProofFile.Law.blankBy_W O.blank] at y2
  rw [x2]
  exact (lensFitB_iff _ l X).1 y2

/-- **hlen AT THE LAYERS' SEGMENTS.** -/
theorem hlen_layers (hE : LensAsked Z) (hS : VerifierAndGoals.InScope Pb = true)
    (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s' : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (28 * g + 9) (z, s'))
    {l' : ℕ} {L : Link S Claim} (hL : SegAt l' .layers L) (p4 : OnBytes.Desc.First.K4.Par)
    (tm : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (u : HTailF2) (ψ : S → β)
    (hC : l3 (1, "objects") (fixed9 (phiAll u ψ) s') ≤ Forest.lins Bs.G₀.W.layers.y.fo)
    (hD : ∀ Xl, Bs.G₀.built[2 * g]? = some Xl →
      l3 (6, "objects") (fixed9 (phiAll u ψ) s') ≤ Forest.lins Xl.tl.f9)
    (hF : lenFront p4 (·.own) (fixed9 (phiAll u ψ) s') ≤ frontB Bs.G₀.W.layers.y g) :
    ∀ v, (fixed9 (phiAll u ψ) s').2 = some v →
      lenRuns (fixed9 (phiAll u ψ) s') (rlOf L tm (lenL p4 l3)) ≤ v.F.planClaimsF := by
  intro v hv
  obtain ⟨funs, f1, f2⟩ := reads_length_at_batch hS hR O hg h
  obtain ⟨G, funs', Xl, n, tl, a1, _, a3, hX, hn, _⟩ := rowsNumber_layers hS hR O hg h
  have e9 : 28 * g + 9 = 14 * (2 * g) + 9 := by omega
  obtain ⟨G', n', g1, g2, g3⟩ := planClaims_at_batch hS hR O (l := 2 * g) (by omega) (e9 ▸ h)
  obtain rfl : G' = v.F := Option.some.inj (g1.symm.trans (snap_is _ hv))
  have hx : ((2 * g, 4, 2) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨2 * g, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g = 24), if_neg (by omega : ¬ 2 * g = 24)]⟩
  have hr := planned_at_batch planned_rows hS hR O hx hX (z, s') (by
    show Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g) + 4 + 3 + 2) (z, s')
    have e : 14 * (2 * g) + 4 + 3 + 2 = 28 * g + 9 := by omega
    rw [e]
    exact h)
  have K8 := len8_le u ψ s' Xl.tl (layShapes Bs.G₀.W.layers g)
    (fun fs hfs => by
      obtain rfl : funs = fs := Option.some.inj (f1.symm.trans hfs)
      exact f2) (of_readTl hr)
  obtain ⟨a, ps, m, b1, b2, b3, b4⟩ := lens_at hE O (l := 2 * g) (by omega) hX
  have n24 : 2 * g ≠ 24 := by omega
  have ev : 2 * g % 2 = 0 := by omega
  have dv : 2 * g / 2 = g := by omega
  unfold ownLenB at b1
  unfold pairsAt at b2
  unfold claimsAt at b3
  rw [if_neg n24, if_pos ev, dv] at b1 b2 b3
  obtain rfl := Option.some.inj b1
  rw [layPairs_is b2, readsB_is] at b4
  have hm : n' = m := by
    unfold planClaimsAt at g2
    rw [if_pos ev, dv] at g2
    exact Option.some.inj (g2.symm.trans b3)
  have T := lens_layers hL p4 tm l3 (fixed9 (phiAll u ψ) s')
  have hD' := hD Xl hX
  omega

/-- **hlen AT THE ATTENTION SEGMENTS.** -/
theorem hlen_att (hE : LensAsked Z) (hS : VerifierAndGoals.InScope Pb = true)
    (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {z : ProofFile.InstPub} {s' : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g + 1) + 9) (z, s'))
    {l' : ℕ} {L : Link S Claim} (hL : SegAt l' .attention L)
    (rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)) (cA : ParC)
    (tm : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (u : HTailF2) (ψ : S → β)
    (hC : ∀ a, Bs.G₀.W.A[g]? = some a →
      l3 (1, "objects") (fixed9 (phiAll u ψ) s') ≤ Forest.lins a.fs)
    (hD : ∀ Xl, Bs.G₀.built[2 * g + 1]? = some Xl →
      l3 (6, "objects") (fixed9 (phiAll u ψ) s') ≤ Forest.lins Xl.tl.f9)
    (hJ : l3 (2, "join") (fixed9 (phiAll u ψ) s') ≤ 1)
    (hP : l3 (1, "planes") (fixed9 (phiAll u ψ) s') ≤ 3)
    (hF : ∀ a, Bs.G₀.W.A[g]? = some a →
      lenStill (fsFirst rd cA) (fixed9 (phiAll u ψ) s') +
        lenStill (fsSecond rd cA) (fixed9 (phiAll u ψ) s') ≤ attOwnB a.S) :
    ∀ v, (fixed9 (phiAll u ψ) s').2 = some v →
      lenRuns (fixed9 (phiAll u ψ) s') (rlOf L tm (lenA rd cA l3)) ≤ v.F.planClaimsF := by
  intro v hv
  obtain ⟨a, funs, ha, f1, f2⟩ := reads_length_att hS hR O hg h
  obtain ⟨G, funs', Xl, a', tl, a1, _, a3, hX, ha', _⟩ := rowsNumber_att hS hR O hg h
  obtain ⟨G', n', g1, g2, g3⟩ := planClaims_at_batch hS hR O (l := 2 * g + 1) (by omega) h
  obtain rfl : G' = v.F := Option.some.inj (g1.symm.trans (snap_is _ hv))
  have hx : ((2 * g + 1, 4, 2) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨2 * g + 1, List.mem_range.2 (by omega), by
      rw [if_neg (by omega : ¬ 2 * g + 1 = 24), if_neg (by omega : ¬ 2 * g + 1 = 24)]⟩
  have hr := planned_at_batch planned_rows hS hR O hx hX (z, s') h
  have K8 := len8_le u ψ s' Xl.tl (attShapes a.S (nScores a.S))
    (fun fs hfs => by
      obtain rfl : funs = fs := Option.some.inj (f1.symm.trans hfs)
      exact f2) (of_readTl hr)
  obtain ⟨b, ps, m, b1, b2, b3, b4⟩ := lens_at hE O (l := 2 * g + 1) (by omega) hX
  have n24 : 2 * g + 1 ≠ 24 := by omega
  have od : ¬ (2 * g + 1) % 2 = 0 := by omega
  have dv : (2 * g + 1) / 2 = g := by omega
  unfold ownLenB at b1
  unfold pairsAt at b2
  unfold claimsAt at b3
  rw [if_neg n24, if_neg od, dv, ha] at b1 b2 b3
  obtain rfl := Option.some.inj b1
  obtain rfl := Option.some.inj b2
  obtain rfl := Option.some.inj b3
  have b5 : Forest.lins a.fs + attOwnB a.S + 1 + 3 +
      (4 + (Xl.tl.NM + readsB Xl.tl.NM Xl.tl.mats (attPairs a.S))) + Forest.lins Xl.tl.f9 ≤
      a.nLin := b4
  rw [attPairs_is, readsB_is] at b5
  have hm : n' = a.nLin := by
    unfold planClaimsAt at g2
    rw [if_neg od, dv, ha] at g2
    exact (Option.some.inj g2).symm
  have T := lens_att hL rd cA tm l3 (fixed9 (phiAll u ψ) s')
  have hC' := hC a ha
  have hD' := hD Xl hX
  have hF' := hF a ha
  omega

/-- **hlen AT THE HEAD.** -/
theorem hlen_head (hE : LensAsked Z) (hS : VerifierAndGoals.InScope Pb = true)
    (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    {z : ProofFile.InstPub} {s' : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) 347 (z, s'))
    {l' : ℕ} {L : Link S Claim} (hL : SegAt l' .head L)
    (hh : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p6 : Kinds.Head.Par) (kap : Phi β → Option Seen)
    (tm : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)) (l3 : ℕ × String → Q β → ℕ)
    (u : HTailF2) (ψ : S → β)
    (hC : l3 (2, "objects") (fixed9 (phiAll u ψ) s') ≤ Forest.lins Bs.G₀.W.HLy.fs)
    (hD : ∀ Xl, Bs.G₀.built[24]? = some Xl →
      l3 (7, "objects") (fixed9 (phiAll u ψ) s') ≤ Forest.lins Xl.tl.f9)
    (hP : l3 (2, "planes") (fixed9 (phiAll u ψ) s') ≤ 3)
    (hN : lenStill (fsK6 hh iU3 p6 kap "norm") (fixed9 (phiAll u ψ) s') ≤ 29)
    (hPo : lenStill (fsK6 hh iU3 p6 kap "policy") (fixed9 (phiAll u ψ) s') ≤ 4)
    (hLo : lenStill (fsK6 hh iU3 p6 kap "logits") (fixed9 (phiAll u ψ) s') ≤ 2)
    (hJ : lenStill (fsJoin hh iU3 p6 kap) (fixed9 (phiAll u ψ) s') ≤ 1) :
    ∀ v, (fixed9 (phiAll u ψ) s').2 = some v →
      lenRuns (fixed9 (phiAll u ψ) s') (rlOf L tm (lenH hh iU3 p6 kap l3)) ≤
        v.F.planClaimsF := by
  intro v hv
  obtain ⟨funs, t0, f1, f0, f2⟩ := reads_length_head hS hR O h
  obtain ⟨G, funs', Xl, t0', tl, a1, _, a3, hX, _, _⟩ := rowsNumber_head hS hR O h
  obtain ⟨G', g1, g3⟩ := planClaims_at_head hS hR O h
  obtain rfl : G' = v.F := Option.some.inj (g1.symm.trans (snap_is _ hv))
  have hx : ((24, 5, 3) : ℕ × ℕ × ℕ) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨24, List.mem_range.2 (by omega), rfl⟩
  have hr := planned_at_batch planned_rows hS hR O hx hX (z, s') h
  have K8 := len8_le u ψ s' Xl.tl (shapesOf t0.funs)
    (fun fs hfs => by
      obtain rfl : funs = fs := Option.some.inj (f1.symm.trans hfs)
      exact f2) (of_readTl hr)
  obtain ⟨b, ps, m, b1, b2, b3, b4⟩ := lens_at hE O (l := 24) (by omega) hX
  unfold ownLenB at b1
  unfold pairsAt at b2
  unfold claimsAt at b3
  rw [if_pos rfl] at b1 b2 b3
  obtain rfl := Option.some.inj b1
  obtain rfl := Option.some.inj b3
  obtain ⟨t1, h1, rfl⟩ := headPairs_is b2
  obtain rfl : t0 = t1 := Option.some.inj (f0.symm.trans h1)
  rw [readsB_is] at b4
  have T := lens_head hL hh iU3 p6 kap tm l3 (fixed9 (phiAll u ψ) s')
  have hD' := hD Xl hX
  omega

/-! ## "The stated functions are there" -/

theorem funs_layers (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {Q' : Type} {start : Q' → S} {z : Q'} {s' : S}
    (h : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s')) (u : HTailF2) (ψ : S → β) :
    ((pi8 (fixed9 (phiAll u ψ) s').1).2).isSome = true := by
  obtain ⟨funs, f1, _⟩ := reads_length_at_batch hS hR O hg h
  show (s'.funs?).isSome = true
  rw [f1]
  rfl

theorem funs_att (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12)
    {Q' : Type} {start : Q' → S} {z : Q'} {s' : S}
    (h : Reach 0 c.blocksInOrder start (14 * (2 * g + 1) + 9) (z, s')) (u : HTailF2) (ψ : S → β) :
    ((pi8 (fixed9 (phiAll u ψ) s').1).2).isSome = true := by
  obtain ⟨_, funs, _, f1, _⟩ := reads_length_att hS hR O hg h
  show (s'.funs?).isSome = true
  rw [f1]
  rfl

theorem funs_head (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    {Q' : Type} {start : Q' → S} {z : Q'} {s' : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, s')) (u : HTailF2) (ψ : S → β) :
    ((pi8 (fixed9 (phiAll u ψ) s').1).2).isSome = true := by
  obtain ⟨funs, _, f1, _⟩ := reads_length_head hS hR O h
  show (s'.funs?).isSome = true
  rw [f1]
  rfl

end VerifiableInference.Desc.K9Asks

#print axioms VerifiableInference.Desc.K9Asks.lensFitB_iff
#print axioms VerifiableInference.Desc.K9Asks.len8_le
#print axioms VerifiableInference.Desc.K9Asks.snap_is
#print axioms VerifiableInference.Desc.K9Asks.lens_at
#print axioms VerifiableInference.Desc.K9Asks.hlen_layers
#print axioms VerifiableInference.Desc.K9Asks.hlen_att
#print axioms VerifiableInference.Desc.K9Asks.hlen_head
#print axioms VerifiableInference.Desc.K9Asks.funs_layers
#print axioms VerifiableInference.Desc.K9Asks.funs_att
#print axioms VerifiableInference.Desc.K9Asks.funs_head
