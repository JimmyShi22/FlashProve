-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/PlanClaimsAtBatch.lean: THE LEDGER's NUMBER OF PLANNED CLAIMS
(`Fork.planClaimsF`) AT EVERY
STATE THAT IS REACHED IN FRONT OF A BATCHING IS THE PLAN's: it is laid by the sub-protocol that
stands
just in front of the batching, at all 25 segments: at a layers' or an attention segment by the step
without a round behind the lookup on the digits (`K3.quietDigits`,
Johnson/Desc/First/Look/K3Whole.lean:
`{ F with planClaimsF := claims }`), at the head by the merge (`{ F with planClaimsF := P.nLin }`).
ONE
STEP BACK EACH: no walk. In the goals' scope. One definition, statements and proofs.

  `planClaimsAt X l`: off the public parameters: at an even l the layers' plan's nLin (X.G[l / 2]),
at
    an odd l the attention's (X.A[l / 2]).
  `quietAt_claims`: a yes of the step that `K3.quietAt X l true` gives, at l < 24, where X has two
    segments a group and 12 groups.
  `quietAt_some`: that step is there, where the plan has the groups' numbers.
  `theStated_ends`: K3's sub-protocol at an address ends in the step without a round that stands
    there: whatever holds behind every yes of that step holds behind every yes of the decision.
  `planClaims_at_batch`: **l < 24: reached at 14 l + 9 ⊢ ∃ G n, s.fork? = some G ∧ planClaimsAt
    Bs.G₀.W l = some n ∧ G.planClaimsF = n.**
  `planClaims_at_head`: **reached at 347 ⊢ ∃ G, s.fork? = some G ∧ G.planClaimsF = Bs.G₀.W.H.nLin.**
Limits. Nothing on the other numbers that "the rows fit" reads. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.StretchBack
import Johnson.Desc.First.Link.Law.FunsStay
import Johnson.Top.H0.MergeLaw.Says

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (Reach stepYes_decide)
open OnBytes.Road.K4 (reach_pred)

/-- The plan's number of claims at segment l < 24. -/
def planClaimsAt (X : Verify.Public) (l : ℕ) : Option ℕ :=
  if l % 2 = 0 then (X.G[l / 2]?).map (·.nLin) else (X.A[l / 2]?).map (·.nLin)

/-- The ledger is there, with n planned claims. -/
def ClaimsAre (n : Option ℕ) (t : S) : Prop :=
  ∃ G m, t.fork? = some G ∧ n = some m ∧ G.planClaimsF = m

theorem quietDigits_claims {used claims : ℕ} {s t : S} (h : K3.quietDigits used claims s = .ok t) :
    ∃ G, t.fork? = some G ∧ G.planClaimsF = claims := by
  unfold K3.quietDigits at h
  obtain ⟨F, hF, h⟩ := K9L.ok_bind h
  obtain ⟨G, hG, h⟩ := K9L.ok_bind h
  obtain rfl := Except.ok.inj h
  have hG' := named_some hG
  unfold First.Look.slotsTaken at hG'
  split at hG'
  · obtain rfl := Option.some.inj hG'
    exact ⟨_, fork_putFork s F (named_some hF) _, rfl⟩
  · exact nomatch hG'

theorem quietAt_claims {X : Verify.Public} (hp4 : X.p4 = true) (hN : X.NGr = 12) {l : ℕ}
    (hl : l < 24) {f : S → Except String S} (hf : K3.quietAt X l true = some f) {s t : S}
    (h : f s = .ok t) : ClaimsAre (planClaimsAt X l) t := by
  have hh : K3.isHead X l = false := by
    unfold K3.isHead
    rw [hp4, hN]
    simp
    omega
  unfold K3.quietAt at hf
  rw [hh, hp4] at hf
  simp only [if_true, Bool.false_eq_true, if_false] at hf
  unfold ClaimsAre planClaimsAt
  by_cases he : l % 2 = 0
  · rw [if_pos he]
    rw [if_pos (by simpa using he)] at hf
    obtain ⟨hp, e1, rfl⟩ := Option.map_eq_some_iff.1 hf
    obtain ⟨G, g1, g2⟩ := quietDigits_claims h
    exact ⟨G, hp.nLin, g1, by rw [e1]; rfl, g2⟩
  · rw [if_neg he]
    rw [if_neg (by simpa using he)] at hf
    obtain ⟨a, e1, rfl⟩ := Option.map_eq_some_iff.1 hf
    obtain ⟨G, g1, g2⟩ := quietDigits_claims h
    exact ⟨G, a.nLin, g1, by rw [e1]; rfl, g2⟩

/-- The step is there, where the plan has the groups' numbers. -/
theorem quietAt_some {X : Verify.Public} (hp4 : X.p4 = true) (hN : X.NGr = 12) {l : ℕ}
    (hl : l < 24) (hG : ∀ g < 12, ∃ hp, X.G[g]? = some hp) (hA : ∀ g < 12, ∃ a, X.A[g]? = some a) :
    ∃ f, K3.quietAt X l true = some f := by
  have hh : K3.isHead X l = false := by
    unfold K3.isHead
    rw [hp4, hN]
    simp
    omega
  unfold K3.quietAt
  rw [hh, hp4]
  simp only [if_true, Bool.false_eq_true, if_false]
  by_cases he : l % 2 = 0
  · rw [if_pos (by simpa using he)]
    obtain ⟨hp, e⟩ := hG (l / 2) (by omega)
    rw [e]
    exact ⟨_, rfl⟩
  · rw [if_neg (by simpa using he)]
    obtain ⟨a, e⟩ := hA (l / 2) (by omega)
    rw [e]
    exact ⟨_, rfl⟩

/-- K3's sub-protocol at an address ends in the step without a round that stands there. -/
theorem theStated_ends {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) {f : S → Except String S}
    (hf : (a.link.bind fun i => K3.quietAt X i (a.piece == K3.pieceAt X i true)) = some f)
    (Q : S → Prop) (hQ : ∀ s t, f s = .ok t → Q t) :
    ∀ s rs gs s', b.decide s rs gs = .ok s' → Q s' := by
  have W : ∀ b₀ : Block S Cl, K3.theWhole claim true X codes shape a = some b₀ →
      ∀ s rs gs s', b₀.decide s rs gs = .ok s' → Q s' := by
    intro b₀ h0 s rs gs s' hd
    unfold K3.theWhole at h0
    obtain ⟨b₁, _, rfl⟩ := Option.map_eq_some_iff.1 h0
    rw [hf] at hd
    obtain ⟨m, _, h2⟩ := Keeps.ebind_ok hd
    exact hQ m s' h2
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · cases h
    exact W _ h0
  · split at h
    · cases h
      exact W _ h0
    · split at h
      · cases h
        exact W _ h0
      · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
        exact fun s rs gs s' hd => W b₀ h0 s rs gs s' hd

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **IN FRONT OF THE BATCHING OF A LAYERS' OR AN ATTENTION SEGMENT.** -/
theorem planClaims_at_batch (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {l : ℕ} (hl : l < 24) {z : Q}
    {s' : S} (h : Reach 0 c.blocksInOrder start (14 * l + 9) (z, s')) :
    ∃ G n, s'.fork? = some G ∧ planClaimsAt Bs.G₀.W l = some n ∧ G.planClaimsF = n := by
  obtain ⟨hp4, hN, -, hA⟩ := Meaning.scope_plans hS hR (IM.ground_publicK O.pub O.blank)
  have n24 : l ≠ 24 := by omega
  have i3 : IM.k3Ix l true = 6 := by
    show (if true = true then 6 else 1) + (if l = 24 then 1 else 0) = 6
    simp [n24]
  obtain ⟨z', s, s'', b₀, e, _, hb, hy⟩ := reach_pred (k := 14 * l + 8) h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  obtain ⟨Lk, b, b', e1, e2, e3, e4⟩ := IM.k3_of hS hR O l (by omega) true
  have hfl : c.blocksInOrder[14 * l + 8]? = some b := by
    have := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by omega) _, i3] at this
    exact this
  obtain rfl : b = b₀ := Option.some.inj (hfl.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have hd' := ((IM.yes_alone e4 (fun k => nomatch k) s _ rs gs).1 hd).1
  have hh : K3.isHead Bs.G₀.W l = false := by
    unfold K3.isHead
    rw [hp4, hN]
    simp
    omega
  have hpc : ((IM.k3Place l true).piece == K3.pieceAt Bs.G₀.W l true) = true := by
    show (IM.k3Ix l true + 1 == K3.pieceAt Bs.G₀.W l true) = true
    unfold K3.pieceAt
    rw [hh, i3]
    rfl
  obtain ⟨f, hq⟩ := quietAt_some hp4 hN hl
    (fun g hg => by
      obtain ⟨_, _, x, _, _, _, _, _, _, _, e, _⟩ := IM.k4_of hS hR O g hg
      exact ⟨_, e⟩)
    (fun g hg => by
      obtain ⟨a, e, _⟩ := hA g hg
      exact ⟨a, e⟩)
  exact theStated_ends _ _ _ _ _ _ e3 (f := f)
    (by
      show K3.quietAt Bs.G₀.W l ((IM.k3Place l true).piece == K3.pieceAt Bs.G₀.W l true) = some f
      rw [hpc]
      exact hq)
    (ClaimsAre (planClaimsAt Bs.G₀.W l)) (fun _ _ k => quietAt_claims hp4 hN hl hq k)
    s rs gs _ hd'

/-- **IN FRONT OF THE HEAD's BATCHING.** -/
theorem planClaims_at_head (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, s')) :
    ∃ G, s'.fork? = some G ∧ G.planClaimsF = Bs.G₀.W.H.nLin := by
  obtain ⟨z', s, s'', b₀, e, _, hb, hy⟩ := reach_pred (k := 346) h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  obtain ⟨Lk, b, e1, e2, e4, _⟩ := IM.k11_of hS hR O
  have hfl : c.blocksInOrder[346]? = some b := by
    have := IM.hear_at_flat e1 e2
    rw [IM.flatIx_scope hS hR O (by omega) 8] at this
    exact this
  obtain rfl : b = b₀ := Option.some.inj (hfl.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have hd' : Johnson.Desc.First.ForkMerge.headMergeDecide (K11.parOf Z Bs.G₀) s rs = .ok s' :=
    ((IM.k11_yes e4 _ _ _ _).1 hd).1
  unfold Johnson.Desc.First.ForkMerge.headMergeDecide at hd'
  split at hd'
  · rename_i a ha
    obtain ⟨_, ho, hd'⟩ := K9L.ok_bind hd'
    obtain ⟨_, _, hd'⟩ := K9L.ok_bind hd'
    obtain ⟨t, _, hd'⟩ := K9L.ok_bind hd'
    obtain ⟨claim, _, hd'⟩ := K9L.ok_bind hd'
    obtain ⟨x, _, hd'⟩ := K9L.ok_bind hd'
    obtain ⟨⟨wo, G, t'⟩, _, hd'⟩ := K9L.ok_bind hd'
    dsimp only at hd'
    obtain ⟨_, _, hd'⟩ := K9L.ok_bind hd'
    obtain ⟨_, _, hd'⟩ := K9L.ok_bind hd'
    have hop : a.opened = true := by
      cases e : a.opened with
      | true => rfl
      | false =>
        rw [e] at ho
        exact nomatch ho
    obtain rfl := Except.ok.inj hd'
    exact ⟨{ G with planClaimsF := (K11.parOf Z Bs.G₀).nLin }, by simp [S.fork?, hop], rfl⟩
  · exact nomatch hd'

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.quietDigits_claims
#print axioms VerifiableInference.Desc.LinkJoin.quietAt_claims
#print axioms VerifiableInference.Desc.LinkJoin.quietAt_some
#print axioms VerifiableInference.Desc.LinkJoin.theStated_ends
#print axioms VerifiableInference.Desc.LinkJoin.planClaims_at_batch
#print axioms VerifiableInference.Desc.LinkJoin.planClaims_at_head
