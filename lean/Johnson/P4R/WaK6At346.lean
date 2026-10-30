-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P4R/WaK6At346.lean: THE STRUCTURE WaK6 (Johnson/Desc/Kinds/Law/WtJointAt.lean: what
the joining of the merge's sentence with the output head's asks of the verifier's state in front of
the merge) AT EVERY STATE THAT IS REACHED AT PLACE 346 OF THE IOP AS WRITTEN IN LEAN, in the goals'
scope, where the description's test on the plan passes. A WALK BACK over five sub-protocols, 346 to
341.

WHICH "REACHED". Reach 0 (c.blocksInOrder.map below) start: by the steps of the WRAPPED sub-protocols
(Johnson/Top/H0/Walk/Reach.lean): what the pieces' acceptances hand on. Not the wider family
Reach 0 c.blocksInOrder start. Why: WaK6 asks that the rounds of the head's own accept are canonical; here
that is taken from the wrapper (canonical_of_below). Whether the wider family gives it too is not
settled: reading the head's own decision and its seat's dress, the author found no test on the
words there; no counterexample is typed.

What is proved.
  peel            one step back: the state in front, the sub-protocol at that place, canonical
                  rounds, and the sub-protocol's own accept.
  KeptW.next      KeptW hands on "stands in a head's segment, and its ledger has its sizes".
  yes_341         an accept at place 341 is an accept of the head's own bare sub-protocol.
  kept_342, kept_343, kept_344   KeptW over the second sending with the quiet step that lays the
                  tables; over the approximate range proof; over the third sending.
  digits_345      over the lookup on the digits with its quiet step: KeptW, and WaK6's two clauses
                  on the covered positions and on the claim.
  **waK6_at_346** the structure, at the public numbers Bs.G₀.W and the plan's size of the
                  vocabulary.

Existential quantifiers. peel: s, B: by the walk (B by the list at k); rs, gs: SOME rounds and
columns at which the step accepts: no law may speak of "the" rounds. KeptW.next: o': by the state's
field here.
Not proved here. THAT ANY STATE IS REACHED AT 346. That the plan's test passes (hOk). At the second,
non-standard hash alone (secondHashFunction), as the seats' theorems that are called. Only in the goals' scope,
at the full size. Nothing on soundness.

-/
import Johnson.IMR.FlatScope
import Johnson.IMR.K1Scope
import Johnson.IMR.K8Seat
import Johnson.IMR.K3Seat
import Johnson.IMR.K6Seat
import Johnson.IMR.PlanAt
import Johnson.P4R.FreeAt341N
import Johnson.Top.H0.Walk.Reach
import Johnson.Goal.Meaning.PlanShapes
import Johnson.Desc.Reads.RowAtLot
import Johnson.Desc.Kinds.Law.DigitsKeptAtDecide
import Johnson.Desc.Kinds.Law.Wa7Meets
import Johnson.Desc.Kinds.Law.HeadPlanesFive
import Johnson.Desc.Kinds.Law.K6RecordPaid
import Johnson.Desc.Kinds.Law.KeepsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P4

open VerifiableInference.Desc (Block Chain Link FileDescription)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (WaK6)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open OnBytes.PscRun (Sized)
open ProofFile (Cl)
open Inst.Model (ScalesAndPolicy)

/-- **One step back, at the wrapped list.** -/
theorem peel {C XP : Type} {bs : List (Block S C)} {start : XP → S} {k : ℕ} {z : XP} {t : S}
    (h : Reach 0 (bs.map below) start (k + 1) (z, t)) :
    ∃ (s : S) (B : Block S C) (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))),
      Reach 0 (bs.map below) start k (z, s) ∧ bs[k]? = some B ∧ Canonical rs ∧
      B.decide s rs gs = .ok t := by
  obtain ⟨s, b, hr, hb, hy⟩ := reach_last h
  rw [List.getElem?_map] at hb
  obtain ⟨B, hB, rfl⟩ := Option.map_eq_some_iff.1 hb
  obtain ⟨rs, gs, hd⟩ := step_yes hy
  obtain ⟨hc, hd'⟩ := canonical_of_below B s t rs gs hd
  exact ⟨s, B, rs, gs, hr, hB, hc, hd'⟩

/-- KeptW hands on the head's segment and the ledger's sizes. -/
theorem _root_.VerifiableInference.Desc.Kinds.Head.Law.KeptW.next {s t : S} (k : KeptW s t)
    {o : HeadOwn} (ho : s.here = .head o) (hz : Sized o.F) :
    ∃ o', t.here = .head o' ∧ Sized o'.F := by
  obtain ⟨p, p', hp, hp', -, -, -, -, -, -, hL⟩ := k
  obtain rfl : o = p := VerifiableInference.Desc.First.Here.head.inj (ho.symm.trans hp)
  exact ⟨p', hp', hL.sized hz⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **Place 341: the head's own sub-protocol.** -/
theorem yes_341 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b0 : Block S Cl} {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} (hB : c.blocksInOrder[341]? = some b0)
    (hd : b0.decide s rs gs = .ok t) :
    (blockAt Bs.G₀.W.hS (readsOf Bs.G₀.W) (workOf Bs.G₀.W) 24).decide s rs gs = .ok t := by
  obtain ⟨Lk, b, b', ms, h1, h2, -, hb', hla, -⟩ := IM.k6_of hS hR O
  obtain rfl : b = b0 := Option.some.inj ((IM.k6_at_341 hS hR O h1 h2).1.symm.trans hB)
  exact seated_decide hb' ((IM.k6_yes hla s t rs gs).1 hd).1

/-- **Place 342: the second sending, then the quiet step that lays the head's tables.** -/
theorem kept_342 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b0 : Block S Cl} {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} (hB : c.blocksInOrder[342]? = some b0)
    (hd : b0.decide s rs gs = .ok t) {a : HeadOwn} (ha : s.here = .head a) : KeptW s t := by
  obtain ⟨Lk, b, Xl, pd, reads, digits, h1, h2, hX, -, hla⟩ :=
    IM.k1_reads_of hS hR O 24 (by decide)
  have h3 := IM.hear_at_flat h1 h2
  rw [IM.flatIx_scope hS hR O (by decide) _] at h3
  obtain rfl : b = b0 := Option.some.inj (h3.symm.trans hB)
  have hd2 : (IM.k1Reads Z Bs.G₀ 24 Xl (IM.k1Ix 24 false + 1) reads).decide s rs gs = .ok t :=
    ((IM.yes_alone hla (by decide) s t rs gs).1 hd).1
  obtain ⟨-, l, hl, hk, -⟩ := IM.ground_named hS hR O.pub O.blank
  obtain rfl : l = Xl := Option.some.inj (hl.symm.trans hX)
  have hp : (if l.kind == 0 || l.kind == 1 then 4 else 5) = 5 := by
    rw [hk]
    rfl
  have hq : IM.k1Quiet Bs.G₀ 24 l = VerifiableInference.Desc.K8.ReadsQuiet.head
      ⟨⟨1, some 24, 5, .K1⟩, Bs.G₀.W.hS, Bs.G₀.W.HLy, Bs.G₀.W.H⟩ := by
    unfold IM.k1Quiet
    simp only [hp]
    exact VerifiableInference.Reads.AtSeat.quiet_is Bs.G₀ 24 l _ _ _ hk (g := l.g) (by
      rw [List.getElem?_map, Array.getElem?_toList, hl]
      show some (l.kind, l.g) = some (2, l.g)
      rw [hk])
  unfold IM.k1Reads at hd2
  rw [hq] at hd2
  exact keptW_reads_laid ha hd2

/-- **Place 343: the approximate range proof.** -/
theorem kept_343 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b0 : Block S Cl} {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} (hB : c.blocksInOrder[343]? = some b0)
    (hd : b0.decide s rs gs = .ok t) {a : HeadOwn} (ha : s.here = .head a) : KeptW s t := by
  obtain ⟨Lk, b, Xl, h1, h2, -, hla, -⟩ := IM.k8_of_head hS hR O
  have h3 := IM.hear_at_flat h1 h2
  rw [IM.flatIx_scope hS hR O (by decide) _] at h3
  obtain rfl : b = b0 := Option.some.inj (h3.symm.trans hB)
  exact keptW_range _ ha ((IM.k8_yes hla s t rs gs).1 hd).1

/-- **Place 344: the third sending.** -/
theorem kept_344 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b0 : Block S Cl} {s t : S}
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} (hB : c.blocksInOrder[344]? = some b0)
    (hd : b0.decide s rs gs = .ok t) {a : HeadOwn} (ha : s.here = .head a) : KeptW s t := by
  obtain ⟨Lk, b, Xl, pr, reads, digits, h1, h2, -, -, hla⟩ :=
    IM.k1_digits_of hS hR O 24 (by decide)
  have h3 := IM.hear_at_flat h1 h2
  rw [IM.flatIx_scope hS hR O (by decide) _] at h3
  obtain rfl : b = b0 := Option.some.inj (h3.symm.trans hB)
  have hd2 : (VerifiableInference.Desc.K1.laterAt Bs.G₀.first (VerifiableInference.Desc.K1.gpOf Z)
      24 (IM.k1Ix 24 true + 1) 2 digits : Block S Unit).decide s rs gs = .ok t :=
    ((IM.yes_alone hla (by decide) s t rs gs).1 hd).1
  exact keptW_sending ha hd2

/-- **Place 345: the lookup on the digits, then its quiet step.** -/
theorem digits_345 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {b0 : Block S Cl} {s t : S} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (hB : c.blocksInOrder[345]? = some b0) (hd : b0.decide s rs gs = .ok t) {a : HeadOwn}
    (ha : s.here = .head a) (hz : Sized a.F) :
    KeptW s t ∧ ∃ (cov : OnBytes.Model.Head.Covered) (tb : OnBytes.Model.Head.Tables),
      t.covered Bs.G₀.W.T Bs.G₀.W.P.h.V = .ok cov ∧
      ∀ o' x claim', t.here = .head o' → o'.x = some x → o'.claim = some claim' →
        VerifiableInference.Desc.First.Look.weightsClaim (runAt Bs.G₀.W cov x tb)
          Bs.G₀.W.layers.wsLay = .ok claim' := by
  obtain ⟨Lk, b, b', h1, h2, hb', hla⟩ := IM.k3_of hS hR O 24 (by decide) true
  have h3 := IM.hear_at_flat h1 h2
  rw [IM.flatIx_scope hS hR O (by decide) _] at h3
  obtain rfl : b = b0 := Option.some.inj (h3.symm.trans hB)
  obtain ⟨e4, eN, -⟩ := Meaning.scope_plans hS hR O.public
  have hH : VerifiableInference.Desc.K3.isHead Bs.G₀.W 24 = true := by
    unfold VerifiableInference.Desc.K3.isHead
    rw [e4, eN]
    rfl
  have hpc : (IM.k3Place 24 true).piece = VerifiableInference.Desc.K3.pieceAt Bs.G₀.W 24 true := by
    unfold VerifiableInference.Desc.K3.pieceAt
    rw [hH]
    rfl
  exact digits_at_head _ _ _ _ _ _ b' hb' (IM.plan_alone O hOk h1 h2 hla) 24 rfl hpc hH s t rs gs
    ((IM.k3_yes hla s t rs gs).1 hd).1 ha hz

/-- **WaK6 AT EVERY STATE REACHED AT 346.** -/
theorem waK6_at_346 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {XP : Type} {start : XP → S} {z : XP} {sF : S}
    (h : Reach 0 (c.blocksInOrder.map below) start 346 (z, sF)) :
    WaK6 Bs.G₀.W Bs.G₀.W.P.h.V sF := by
  obtain ⟨s345, B5, r5, g5, h345, hB5, -, d5⟩ := peel h
  obtain ⟨s344, B4, r4, g4, h344, hB4, -, d4⟩ := peel h345
  obtain ⟨s343, B3, r3, g3, h343, hB3, -, d3⟩ := peel h344
  obtain ⟨s342, B2, r2, g2, h342, hB2, -, d2⟩ := peel h343
  obtain ⟨s341, B1, r1, g1, h341, hB1, hc1, d1⟩ := peel h342
  have c1 := yes_341 hS hR O hB1 d1
  have c2 : WellLaid ((seatAt Bs.G₀.W.hS (readsOf Bs.G₀.W)).ledger s341) :=
    wellLaid_341 hS hR O (plan_at O hOk 340) (reach_raw h341) _ _
  obtain ⟨a, F1, X0, Q, -, hop, -, e⟩ := Came.decide_record _ _ _ _ c1
  have ho2 : s342.here = .head { a with F := F1, x := some X0, squaresP := some Q } := by rw [e]
  have eL : (seatAt Bs.G₀.W.hS (readsOf Bs.G₀.W)).ledger s342 = F1 := by
    rw [e]
    show (S.fork? _).getD {} = F1
    simp [S.fork?, hop]
  have hz2 : Sized ({ a with F := F1, x := some X0, squaresP := some Q } : HeadOwn).F := by
    have hL := blockAt_later _ _ _ _ s341 s342 r1 g1 c1
    rw [eL] at hL
    exact hL.sized (sized_of_wellLaid c2)
  have k2 := kept_342 hS hR O hB2 d2 ho2
  obtain ⟨o3, ho3, hz3⟩ := k2.next ho2 hz2
  have k3 := kept_343 hS hR O hB3 d3 ho3
  obtain ⟨o4, ho4, hz4⟩ := k3.next ho3 hz3
  have k4 := kept_344 hS hR O hB4 d4 ho4
  obtain ⟨o5, ho5, hz5⟩ := k4.next ho4 hz4
  obtain ⟨k5, cov, tb, c5, c6⟩ := digits_345 hS hR O hOk hB5 d5 ho5 hz5
  exact InScope.waK6_of_six hS hR O.public tb c1 c2 hc1 (((k2.trans k3).trans k4).trans k5).fo c5
    c6

end

end P4

#print axioms P4.peel
#print axioms P4.yes_341
#print axioms P4.kept_342
#print axioms P4.kept_343
#print axioms P4.kept_344
#print axioms P4.digits_345
#print axioms P4.waK6_at_346
