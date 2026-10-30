-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/YesAll.lean: THE SEATED BATCHING BLOCK's YES, BROUGHT TO NAMED PREMISES, AT EACH OF
THE 25 SEGMENTS. Statements and proofs ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated. NO
PREMISE IS PAID AT A STATE OF A RUN HERE, K9's own (`drawReady`; the equation is open) among them.

`SeatedFree c Z l k Lk p w` (Honest/K9/AtSeatAll.lean) holds at each l < 25 wherever the proof file's description can
be opened in the goals' scope (`free_at_seat_all`; that the three premises of such an opening can be met together is
shown by no known theorem). Its fields `alone`, `order`, `each`, `keeps` are spent here.
  **`yes_seated`**   of a segment of which `SeatedFree` holds: the description's own batching block (number 14 l + k +
      2 of the chain's flat list) SAYS YES AT x where: K9's lens answers at s · `drawReady` · the equation is open ·
      and ONE FAMILY J i cs u for the segment's runs (`seated_yes_family`, Honest/K9/YesAtSeat.lean): J holds at (0,
      [], the state behind the draw); at each entry of the order THE RUN THAT STANDS IN THE DESCRIPTION's LIST
      returns, passes K9's test behind it and hands J on; and J at the order's length says: at most the plan's number
      of claims, each of which fits the arrays behind the draw · no mark of failure · the reply as it was. THE
      LEDGER's CORE AND THE LENS BEHIND THE GATHERER ARE PAID (`SeatedFree.keeps`: part 1's `core_layers`, `core_att`,
      `core_head`). Handed on: `BatBehind`, no mark of failure and the reply as it was behind, and J at the end
  **`step_seated`**   the same at the block's STEP, at the round in which nothing is sent and the words tr are drawn,
      whatever the sealed digest, the columns and the first tree's number: the same state; no column is taken
At a feed-forward segment `yes_of_family` and `step_of_family` (Honest/K9/YesAtSeat.lean, StepYes.lean) say the like,
under one premise more (the state stands in such a segment), over the walk of Honest/K9/LayersCore.lean: these
three files stand without part 1's three on the core (Johnson/Desc/K8/Honest/SameCore.lean, CoreRuns.lean,
CoreGathers.lean), which lie beneath Honest/K9/AtSeatAll.lean and so beneath this file. THE RUNS IN THESE CLAUSES ARE
THOSE IN THE DESCRIPTION's LIST, WRAPPED BY ITS MAKERS: what Honest/K9/YesAtSeat.lean's head says of that holds here.
  **`step_at_each`**   AT EACH OF THE 25 SEGMENTS, UNDER ONE NAME: `free_at_seat_all` and `step_seated`, joined
In each, the last clause is handed the gatherer's own yes as well. No member: `SeatedFree` is shown at no written
description. `yes_seated` is called by `step_seated`; that by `step_at_each` and by Honest/K9/ThrYes.lean's
`bat_accepted`.
WHAT IS NOT CLAIMED. Any of the premises at any state: above all the runs' clauses: J IS ONE FAMILY: who lays which
clause into it, and who carries it through the other kinds' runs, is not settled here. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.AtSeatAll
import Johnson.Desc.ProofFile.Honest.K9.StepYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim Link Chain claimsInBy)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (atS Where drawAlone)
open VerifiableInference.Desc.K9H (claimFits)

/-- **The yes at a segment of which `SeatedFree` holds.** -/
theorem yes_seated {c : Chain S Claim} {Z : ProofFile.Pub} {l k : ℕ} {Lk : Link S Claim} {p : Where}
    {w : VerifiableInference.Desc.K9.SegSort × ℕ × VerifiableInference.Desc.K9.TWhere}
    (Sd : SeatedFree c Z l k Lk p w) (s : S) (x : E) (a : VerifiableInference.Desc.K9.Part)
    (ha : atS.get? s = some a) (hr : drawReady a = true) (hdoor : a.F.doorShutF = false)
    (J : ℕ → List Claim → S → Prop)
    (start : ∀ t₁, (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁ → J 0 [] t₁)
    (step : ∀ j o, Lk.order[j]? = some o → ∀ cs u, J j cs u → ∃ run z, claimsRunOf Lk.hear o = some run ∧
      run cs.length u = .ok z ∧ Lk.each o z.1 z.2 = .ok () ∧ J (j + 1) (cs ++ z.1) z.2)
    (fin : ∀ t₁ a₁ cs u, (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁ →
      atS.get? t₁ = some a₁ → claimsInBy Lk.each Lk.hear Lk.order t₁ = .ok (cs, u) → J Lk.order.length cs u →
        cs.length ≤ a.F.planClaimsF ∧
        cs.all (claimFits a₁.F.trees a₁.F.ns) = true ∧ u.failed = none ∧ u.out.reply = s.out.reply) :
    ∃ y G t, (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).decide s [⟨[], drawnOne x⟩] [] = .ok t ∧
      BatBehind p (claimsInBy Lk.each Lk.hear Lk.order) s x y G t ∧ t.failed = none ∧
      t.out.reply = s.out.reply ∧ J Lk.order.length y.2.2 y.1 := by
  obtain ⟨pl, hk, hb⟩ := Sd.alone
  refine seated_yes_family hb hk s x a ha hr hdoor J start step ?_
  intro t₁ a₁ cs u ht h1 hz hJ
  obtain ⟨q4, q5, q6, q7⟩ := fin t₁ a₁ cs u ht h1 hz hJ
  obtain ⟨a', q2, q3⟩ := Sd.keeps t₁ u cs a₁ hz h1
  exact ⟨a', q2, q3, q4, q5, q6, q7⟩

/-- **The same at the step.** -/
theorem step_seated {c : Chain S Claim} {Z : ProofFile.Pub} {l k : ℕ} {Lk : Link S Claim} {p : Where}
    {w : VerifiableInference.Desc.K9.SegSort × ℕ × VerifiableInference.Desc.K9.TWhere}
    (Sd : SeatedFree c Z l k Lk p w) (s : S) (tr : UInt64 × UInt64 × UInt64)
    (a : VerifiableInference.Desc.K9.Part)
    (ha : atS.get? s = some a) (hr : drawReady a = true) (hdoor : a.F.doorShutF = false)
    (J : ℕ → List Claim → S → Prop)
    (start : ∀ t₁, (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = .ok t₁ →
      J 0 [] t₁)
    (step : ∀ j o, Lk.order[j]? = some o → ∀ cs u, J j cs u → ∃ run z, claimsRunOf Lk.hear o = some run ∧
      run cs.length u = .ok z ∧ Lk.each o z.1 z.2 = .ok () ∧ J (j + 1) (cs ++ z.1) z.2)
    (fin : ∀ t₁ a₁ cs u,
      (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = .ok t₁ →
      atS.get? t₁ = some a₁ → claimsInBy Lk.each Lk.hear Lk.order t₁ = .ok (cs, u) → J Lk.order.length cs u →
        cs.length ≤ a.F.planClaimsF ∧
        cs.all (claimFits a₁.F.trees a₁.F.ns) = true ∧ u.failed = none ∧ u.out.reply = s.out.reply) :
    ∃ y G t, (∀ (ft : ℕ) (dg : Option ByteArray) (cols : List VerifiableInference.Desc.OpenedColumn),
      (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).step ft s [⟨[], ⟨[tr], [], [], dg⟩⟩] cols = .ok (t, 0)) ∧
      BatBehind p (claimsInBy Lk.each Lk.hear Lk.order) s (E.ofTriple tr) y G t ∧ t.failed = none ∧
      t.out.reply = s.out.reply ∧ J Lk.order.length y.2.2 y.1 := by
  obtain ⟨y, G, t, hd, hB, hf, ho, hJ⟩ := yes_seated Sd s (E.ofTriple tr) a ha hr hdoor J start step fin
  obtain ⟨pl, _, hb⟩ := Sd.alone
  exact ⟨y, G, t, fun ft dg cols => seated_step_yes hb ft s t tr dg cols hd, hB, hf, ho, hJ⟩

/-- **AT EACH OF THE 25 SEGMENTS, UNDER ONE NAME**: wherever the description can be opened in the goals' scope:
`free_at_seat_all` (Honest/K9/AtSeatAll.lean) and `step_seated`, joined. -/
theorem step_at_each {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : VerifiableInference.Desc.FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Block S Claim)} {c : Chain S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25) :
    ∃ Lk p w, SeatedFree c Z l (if l = 24 then 9 else 7) Lk p w ∧
      ∀ (s : S) (tr : UInt64 × UInt64 × UInt64) (a : VerifiableInference.Desc.K9.Part),
        atS.get? s = some a → drawReady a = true → a.F.doorShutF = false → ∀ J : ℕ → List Claim → S → Prop,
        (∀ t₁, (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = .ok t₁ → J 0 [] t₁) →
        (∀ j o, Lk.order[j]? = some o → ∀ cs u, J j cs u → ∃ run z, claimsRunOf Lk.hear o = some run ∧
          run cs.length u = .ok z ∧ Lk.each o z.1 z.2 = .ok () ∧ J (j + 1) (cs ++ z.1) z.2) →
        (∀ t₁ a₁ cs u, (drawAlone (Cl := Claim) atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = .ok t₁ →
          atS.get? t₁ = some a₁ → claimsInBy Lk.each Lk.hear Lk.order t₁ = .ok (cs, u) → J Lk.order.length cs u →
            cs.length ≤ a.F.planClaimsF ∧ cs.all (claimFits a₁.F.trees a₁.F.ns) = true ∧ u.failed = none ∧
              u.out.reply = s.out.reply) →
        ∃ y G t, (∀ (ft : ℕ) (dg : Option ByteArray) (cols : List VerifiableInference.Desc.OpenedColumn),
          (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).step ft s [⟨[], ⟨[tr], [], [], dg⟩⟩] cols = .ok (t, 0)) ∧
          BatBehind p (claimsInBy Lk.each Lk.hear Lk.order) s (E.ofTriple tr) y G t ∧ t.failed = none ∧
          t.out.reply = s.out.reply ∧ J Lk.order.length y.2.2 y.1 := by
  obtain ⟨Lk, p, w, Sd⟩ := free_at_seat_all hS hR O l hl
  exact ⟨Lk, p, w, Sd, fun s tr a ha hr hdoor J start step fin =>
    step_seated Sd s tr a ha hr hdoor J start step fin⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.step_at_each
#print axioms ProofFile.Honest.K9.yes_seated
#print axioms ProofFile.Honest.K9.step_seated
