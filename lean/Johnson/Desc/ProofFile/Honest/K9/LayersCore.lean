-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/LayersCore.lean: A FEED-FORWARD SEGMENT's SEVEN RUNS OF CLAIMS KEEP THE LEDGER's
CORE. Statements and proofs ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated.

After part 1's `layers_lists` (Johnson/Desc/K8/Honest/FallLayersLists.lean), under its premises on the runs and the
order (not those on the draw: the state in front is any that stands in a feed-forward segment) and by the same walk
over the seven runs. That lemma carries part 1's `SameSums` (seven fields of the ledger); K9's adding asks three
more (chi's mark, the claims' marks, the door): the sealed lemmas on the runs give them too (`K4.Core`,
`Law.OnlySide`), so here they are carried.
  `side_of_core`    the layers' own `Core` gives the smallness test's `OnlySide`
  **`layers_side`**   one yes of the segment's function of claims from a state that stands in a feed-forward segment:
      the state behind stands there too, and its ledger is the ledger in front but for the side (`OnlySide`: the
      arrays, the number of slots, the sums, the count, chi and its mark, the plan's number, the claims' marks, the
      door)
  `layers_keeps`    so `LedgerCore` (Honest/K9/LedgerOf.lean) between K9's parts of the two states
Called by Honest/K9/YesAtSeat.lean's `yes_at_seat` and `yes_of_family` alone: no member. (`step_ok` in the proof is
part 1's: Honest/K9/GatherFold.lean, which has a lemma of that name, is not imported here.)
WHAT IS NOT CLAIMED. The walk's premises. That the function of claims returns. Attention and the head. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K9.LedgerOf
import Johnson.Desc.K8.Honest.FallLayersLists

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open VerifiableInference.Desc.First.K8.Honest
open OnBytes.Desc.First.K4 (frontAtC backAtC frontOf formsFrontWith formsFrontWith_some
  formsBack_some formsFrontWith_core formsBack_core claimOf Wrote)

theorem side_of_core {F G : Fork} (h : OnBytes.Desc.First.K4.Core F G) : OnlySide F G :=
  ⟨h.trees, h.ns, h.LS, h.c0, h.nClaim, h.theta, h.thetaDrawnF, h.planClaimsF, h.kapMapF, h.doorShutF⟩

/-- **The seven runs leave the ledger but for the side.** -/
theorem layers_side (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (ties : LinkJoin.LayersTies L p4 nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run VerifiableInference.Desc.K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run VerifiableInference.Desc.K9.objectsDigits)
    (hord : L.order = VerifiableInference.Desc.First.orderOf .layers) (t e : S) (b₀ : LayOwn)
    (h0 : t.here = .lay b₀) (cls : List Claim)
    (hg : claimsInBy L.each L.hear L.order t = .ok (cls, e)) :
    ∃ b₁ : LayOwn, e.here = .lay b₁ ∧ OnlySide b₀.F b₁.F := by
  rw [hord, claimsInBy_eq] at hg
  have ho7 : VerifiableInference.Desc.First.orderOf .layers = [(1, "objects"), (1, "guests"), (2, "front"),
      (6, "objects"), (6, "guests"), (4, "K8.equations"), (2, "back")] := rfl
  rw [ho7] at hg
  simp only [runAll] at hg
  obtain ⟨z1, g1, hg⟩ := bind_ok hg
  obtain ⟨z2, g2, hg⟩ := bind_ok hg
  obtain ⟨z3, g3, hg⟩ := bind_ok hg
  obtain ⟨z4, g4, hg⟩ := bind_ok hg
  obtain ⟨z5, g5, hg⟩ := bind_ok hg
  obtain ⟨z6, g6, hg⟩ := bind_ok hg
  obtain ⟨z7, g7, hg⟩ := bind_ok hg
  have hz7 : z7 = (cls, e) := Except.ok.inj hg
  -- 1: the lookup on the calls: "objects"
  obtain ⟨r1, c1, e1, at1, y1, rfl⟩ := step_ok g1
  obtain ⟨F1, gC, f1, k1, rfl, rfl⟩ := objectsBy_ok _ _ _ _ _ (tC r1 at1 _ _ _ _ y1)
  obtain rfl : b₀.F = F1 := Option.some.inj ((lay_fork t _ h0).symm.trans f1)
  have h1 := lay_putFork t _ (b₀.F.paid gC.owedObjects) h0
  -- 2: "guests"
  obtain ⟨r2, c2, e2, at2, y2, rfl⟩ := step_ok g2
  have i2 := Except.ok.inj (ties.tGuests 1 (by simp) r2 at2 _ _ _ _ y2)
  obtain rfl : [] = c2 := congrArg Prod.fst i2
  obtain rfl : _ = e2 := congrArg Prod.snd i2
  -- 3: "front"
  obtain ⟨r3, c3, e3, at3, y3, rfl⟩ := step_ok g3
  obtain ⟨q3, l3, u3⟩ := ties.tFront r3 at3
  obtain ⟨A3, o, fs3, G3, ho3, hf3, rfl, w3⟩ := frontAtC l3 (u3 _ _ _ _ y3)
  obtain ⟨w3a, h3⟩ := wrote_here w3
  obtain rfl : _ = A3 := Here.lay.inj (h1.symm.trans w3a)
  rw [frontOf_eq] at hf3
  have s3 : OnlySide b₀.F G3 :=
    (side_of_core (OnBytes.Desc.First.K4.paid_core b₀.F _)).trans (side_of_core (formsFrontWith_core hf3))
  -- 4: the lookup on the digits: "objects"
  obtain ⟨r4, c4, e4, at4, y4, rfl⟩ := step_ok g4
  obtain ⟨F4, gD, f4, k4, rfl, rfl⟩ := objectsBy_ok _ _ _ _ _ (tD r4 at4 _ _ _ _ y4)
  obtain rfl : G3 = F4 := Option.some.inj ((lay_fork _ _ h3).symm.trans f4)
  have h4 := lay_putFork _ _ (G3.paid gD.owedObjects) h3
  -- 5: "guests"
  obtain ⟨r5, c5, e5, at5, y5, rfl⟩ := step_ok g5
  have i5 := Except.ok.inj (ties.tGuests 6 (by simp) r5 at5 _ _ _ _ y5)
  obtain rfl : [] = c5 := congrArg Prod.fst i5
  obtain rfl : _ = e5 := congrArg Prod.snd i5
  -- 6: "K8.equations"
  obtain ⟨r6, c6, e6, at6, y6, rfl⟩ := step_ok g6
  obtain ⟨F6, tl6, fu6, tl', F6', f6, t6, n6, q6, rfl⟩ :=
    K9L.k8Run_ok _ _ _ _ (ties.tEq r6 at6 _ _ _ _ y6)
  obtain rfl : _ = F6 := Option.some.inj ((lay_fork _ _ h4).symm.trans f6)
  have h6 := lay_putFork _ _ F6' (lay_putTl _ _ tl' h4)
  have s6 : OnlySide b₀.F F6' :=
    (s3.trans (side_of_core (OnBytes.Desc.First.K4.paid_core G3 _))).trans (eq_side q6)
  -- 7: "back"
  obtain ⟨r7, c7, e7, at7, y7, rfl⟩ := step_ok g7
  obtain ⟨q7, l7, u7⟩ := ties.tBack r7 at7
  obtain ⟨A7, o7, fs7, G7, ho7', hf7, rfl, w7⟩ := backAtC l7 (u7 _ _ _ _ y7)
  obtain ⟨w7a, h7⟩ := wrote_here w7
  obtain rfl : _ = A7 := Here.lay.inj (h6.symm.trans w7a)
  have s7 : OnlySide b₀.F G7 := s6.trans (side_of_core (formsBack_core hf7))
  have he : e7 = e := congrArg Prod.snd hz7
  subst he
  exact ⟨_, h7, s7⟩

/-- **`LedgerCore` between K9's parts of the two states.** -/
theorem layers_keeps (L : Link S Claim) (p4 : OnBytes.Desc.First.K4.Par) (nU : Array Nat)
    (ties : LinkJoin.LayersTies L p4 nU)
    (tC : ∀ run, LinkJoin.At L (1, "objects") run → LinkJoin.Under run VerifiableInference.Desc.K9.objectsCalls)
    (tD : ∀ run, LinkJoin.At L (6, "objects") run → LinkJoin.Under run VerifiableInference.Desc.K9.objectsDigits)
    (hord : L.order = VerifiableInference.Desc.First.orderOf .layers) (t e : S) (b₀ : LayOwn)
    (h0 : t.here = .lay b₀) (cls : List Claim)
    (hg : claimsInBy L.each L.hear L.order t = .ok (cls, e)) (a a' : VerifiableInference.Desc.K9.Part)
    (ha : VerifiableInference.Desc.K9.atS.get? t = some a)
    (ha' : VerifiableInference.Desc.K9.atS.get? e = some a') : LedgerCore a a' := by
  obtain ⟨b₁, h1, sd⟩ := layers_side L p4 nU ties tC tD hord t e b₀ h0 cls hg
  have e0 : a.F = b₀.F := Option.some.inj ((VerifiableInference.Desc.K9.get_fork t a ha).symm.trans (lay_fork t b₀ h0))
  have e1 : a'.F = b₁.F :=
    Option.some.inj ((VerifiableInference.Desc.K9.get_fork e a' ha').symm.trans (lay_fork e b₁ h1))
  rw [← e0, ← e1] at sd
  exact ⟨sd.theta, sd.LS, sd.ns, sd.plan, sd.nClaim, sd.door, sd.drawn, sd.kapMap, by rw [sd.trees]⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.layers_side
#print axioms ProofFile.Honest.K9.layers_keeps
#print axioms ProofFile.Honest.K9.side_of_core
