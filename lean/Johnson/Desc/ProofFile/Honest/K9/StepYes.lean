-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/StepYes.lean: FROM THE SEATED BATCHING BLOCK's DECISION TO ITS STEP: THE YES. Lemmas
ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated.

A chain goes on by a block's step (`Block.step`, Johnson/Desc/Block.lean). Honest/K9/YesAtSeat.lean says when the
seated block's DECISION says yes, at the round that `drawnOne` gives and no column. Honest/K9/AtStep.lean goes from a
yes of the step to a yes of the decision. Here the other way.
  `bat_fits`        the step's test on the rounds' shape says yes at K9's one round wherever nothing is sent and one
      element is drawn, whatever its words and the sealed digest
  **`seated_step_yes`**   the decision of a block that seats K9's batching alone says yes at the element of words tr:
      THEN ITS STEP SAYS YES at the round in which nothing is sent and tr is drawn, with whatever sealed digest,
      columns and first tree's number; it returns the same state and takes no column
  **`step_of_family`**   `yes_of_family` (Honest/K9/YesAtSeat.lean) AT THE STEP: wherever the description can be
      opened in the goals' scope (that its three premises can be met together is shown by no known
      theorem), at each feed-forward segment: under that theorem's premises at the element of words tr, the STEP of the
      description's own block at number 14 l + 9 says yes at that round
Neither the step nor the decision reads the entry's proof of work. `seated_step_yes` is called at a member in
Honest/K9/YesToy.lean (`stepYesC`); `step_of_family` has no member.
WHAT IS NOT CLAIMED. That the decision says yes; any premise of `step_of_family`. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.YesAtSeat
import Johnson.Desc.Sound.RunIsDecide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First

/-- The test on the rounds' shape, at K9's one round. -/
theorem bat_fits (p : Desc.K9.Where) (tr : UInt64 × UInt64 × UInt64) (dg : Option ByteArray) :
    roundsFit [{ entry := Desc.K9.entry p }] [⟨[], ⟨[tr], [], [], dg⟩⟩] = true := by
  have hi : (({ entry := Desc.K9.entry p } : Fmt.DeclaredRound).items.filter (· != .root)) = [] := by
    simp only [Fmt.DeclaredRound.items, Fmt.Entry.cut, Desc.K9.entry]; decide
  have hk : ∃ k, Fmt.kindOf "BAT-sigma" = some k ∧ k ≠ .seeds := ⟨_, rfl, by decide⟩
  obtain ⟨k, hk1, hk2⟩ := hk
  have hz : drawsMarkedNonzeroHaveNonzeroWords { entry := Desc.K9.entry p } ⟨[], ⟨[tr], [], [], dg⟩⟩ = true := by
    unfold drawsMarkedNonzeroHaveNonzeroWords
    show ((Fmt.kindOf "BAT-sigma").any fun k =>
      ((Fmt.dsElems (Desc.K9.entry p) k).zip [tr]).all fun x => x.1 != .elemNZ || x.2 != (0, 0, 0)) = true
    rw [hk1]
    show (((Fmt.dsElems (Desc.K9.entry p) k).zip [tr]).all fun x => x.1 != .elemNZ || x.2 != (0, 0, 0)) = true
    unfold Fmt.dsElems
    rw [if_neg hk2]
    rfl
  unfold roundsFit
  rw [hi, hz]
  rfl

/-- **From the decision's yes to the step's.** -/
theorem seated_step_yes {same : S → S → Bool} {b : Block S Claim} {p : Desc.K9.Where}
    {g : S → Except String (List Claim × S)} {name : String} {a : Place}
    (hb : IM.LaidAlone same b (Desc.K9.batch Desc.K9.atS p g) name a) (ft : ℕ) (s t : S)
    (tr : UInt64 × UInt64 × UInt64) (dg : Option ByteArray) (cols : List Desc.OpenedColumn)
    (h : b.decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = .ok t) :
    b.step ft s [⟨[], ⟨[tr], [], [], dg⟩⟩] cols = .ok (t, 0) := by
  have hr : b.rounds = [{ entry := Desc.K9.entry p }] := IM.alone_rounds hb
  refine (Sound.step_ok_iff ft b s t _ cols 0).2 ⟨?_, ?_, ?_, ?_⟩
  · rw [hr]
    exact bat_fits p tr dg
  · rw [hr]
    rfl
  · rw [hr]
    rfl
  · have hg : Sound.groupsAt ft b [⟨[], ⟨[tr], [], [], dg⟩⟩] (cols.take 0) = [] := by
      unfold Sound.groupsAt
      rw [hr]
      rfl
    rw [hg]
    exact h

/-- **`yes_of_family` (Honest/K9/YesAtSeat.lean), AT THE STEP.** -/
theorem step_of_family {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)}
    {c : Chain S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25)
    (hsub : IM.subAt l = .layers) :
    ∃ (Lk : Link S Claim) (p : Desc.K9.Where), c.links[l]? = some Lk ∧ IM.k9At Z l = some p ∧
      c.blocksInOrder[14 * l + 9]? = some (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) ∧
      Lk.order = VerifiableInference.Desc.First.orderOf .layers ∧
      Lk.each = Desc.K9.eachAtS .layers ∧
      ∀ (s : S) (a₀ : LayOwn) (tr : UInt64 × UInt64 × UInt64) (a : Desc.K9.Part)
        (J : ℕ → List Claim → S → Prop), s.here = .lay a₀ →
        Desc.K9.atS.get? s = some a → drawReady a = true → a.F.doorShutF = false →
        (∀ t₁, (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = .ok t₁ →
          J 0 [] t₁) →
        (∀ j o, Lk.order[j]? = some o → ∀ cs u, J j cs u → ∃ run z, claimsRunOf Lk.hear o = some run ∧
          run cs.length u = .ok z ∧ Lk.each o z.1 z.2 = .ok () ∧ J (j + 1) (cs ++ z.1) z.2) →
        (∀ t₁ a₁ cs u,
          (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne (E.ofTriple tr)⟩] [] = .ok t₁ →
          Desc.K9.atS.get? t₁ = some a₁ → claimsInBy Lk.each Lk.hear Lk.order t₁ = .ok (cs, u) → J 7 cs u →
            cs.length ≤ a.F.planClaimsF ∧
            cs.all (Desc.K9H.claimFits a₁.F.trees a₁.F.ns) = true ∧ u.failed = none ∧
            u.out.reply = s.out.reply) →
        ∃ y G t, (∀ (ft : ℕ) (dg : Option ByteArray) (cols : List Desc.OpenedColumn),
          (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)).step ft s [⟨[], ⟨[tr], [], [], dg⟩⟩] cols = .ok (t, 0)) ∧
          BatBehind p (claimsInBy Lk.each Lk.hear Lk.order) s (E.ofTriple tr) y G t ∧ t.failed = none ∧
          t.out.reply = s.out.reply ∧ J 7 y.2.2 y.1 := by
  obtain ⟨Lk, p, e1, e2, f9, hord, heach, hyes⟩ := yes_of_family hS hR O l hl hsub
  obtain ⟨Lk', p', w', T, e1', e2', -, -, -, -, hb, -⟩ := (IM.k9_of hS hR O).2 l hl
  obtain rfl : Lk = Lk' := Option.some.inj (e1.symm.trans e1')
  obtain rfl : p = p' := Option.some.inj (e2.symm.trans e2')
  refine ⟨Lk, p, e1, e2, f9, hord, heach, fun s a₀ tr a J hs ha hr hdoor start step fin => ?_⟩
  obtain ⟨y, G, t, hd, hB, hf, ho, hJ⟩ := hyes s a₀ (E.ofTriple tr) a J hs ha hr hdoor start step fin
  exact ⟨y, G, t, fun ft dg cols =>
    seated_step_yes (hb (claimsInBy Lk.each Lk.hear Lk.order)) ft s t tr dg cols hd, hB, hf, ho, hJ⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.step_of_family
#print axioms ProofFile.Honest.K9.bat_fits
#print axioms ProofFile.Honest.K9.seated_step_yes
