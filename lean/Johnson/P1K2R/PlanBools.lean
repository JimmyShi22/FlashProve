-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/PlanBools.lean: code switching (K2): THE CLOSED PREMISES OF ITS SHARES OF e₁ THAT
READ THE PLANNER's OWN OUTPUT (the built links · the attention's and the layers' plans · the
head's link's letters), EACH HEAP AS ONE Bool WITH CODE, AND «the Bool accepts ⟹ the structure» AS
A THEOREM: so that they can be evaluated at a stored example, with negative tests. No written
value reaches these parts of the planner's output (by report), so Lean's kernel has
nothing closed to reduce. NO BLOCK IMPORTS THIS FILE.
  linkPlanB Z nsOf d3 l        LinkPlan's five (Johnson/P1K2R/MadeFirst.lean), at the letters that
                               they read of the public data: nsOf · d3. IT REJECTS WHERE THE LINK
                               IS NOT BUILT, where its sort is the head's, or where its plan is
                               lacking: so an accept is not idle
  linkPlan_of_B                an accept gives LinkPlan Z l D, where D.nsOf | D.d3 are these
                               letters
  k5PlanB Z d5 lay₀ l          K5Plan's ha · hW · c1 · c2 · hμ, and hμc, at d5
  k5Plan_of_B                  an accept, with hOwn, gives ∃ q μ, K5Plan Z l D N lay₀ q μ ∧ hμc
  letters_of_blank             what the head's link's letters (ProofFile.pureLetters G₀ l) hold of the
                               plan, where G₀ is the ground that is made for a request of zeros
                               (ProofFile.blankBy: the opening IM.Open has it): the built
                               link's list of arrays and planned ledger · the head's plan. By
                               blank_built (Johnson/IMR/OwnSeat.lean: THE GROUND's BUILT
                               LINKS ARE THE PLAN's BUT FOR THEIR ROUTINES: so «G₀.built =
                               Z.p.built.links» CANNOT HOLD and is asked nowhere) and
                               ProofFile.Law.blankBy_W
  headPlanB Z nsOf d3          HeadPlan's two (Johnson/P1K2R/MadeHear.lean), off the plan's own
                               built link 24 and head's plan
  headPlan_of_B                an accept gives HeadPlan G₀ D at that ground
  hFp_of_blank                 NO TEST IS WANTED FOR hFp (Johnson/P1K2R/MadeSentHear.lean): a
                               theorem at that ground
LIMITS. Definitions and what an accept says. THE Bools ARE EVALUATED NOWHERE HERE. verify() asks
none of them. No soundness is claimed.
-/
import Johnson.P1K2R.MaskFirstWritten
import Johnson.P1K2R.MadeSentHear
import Johnson.IMR.OwnSeat
import Johnson.Desc.ProofFile.Law.MakerPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (ModelPart Numbers PubData)
open VerifiableInference.Desc.First.Look (K3Data)
open VerifiableInference.Desc.First.K2 (madeLookB)
open Johnson.Desc.First.Walk (startFork)
open Johnson.Desc.First.Walk.Seat (pubOf)
open H2K5.Door (K5Data)
open IM (subW)

/-- LinkPlan's five, with code. -/
def linkPlanB (Z : ProofFile.Pub) (nsOf : Nat → Option Nat) (d3 : K3Data) (l : Nat) : Bool :=
  decide ((ProofFile.subsOf Z)[l]? = some (subW l)) &&
    match Z.p.built.links[l]? with
    | none => false
    | some X =>
      if X.kind = 1 then
        match Z.p.X.A[X.g]? with
        | none => false
        | some p =>
          decide (nsOf l = some p.ns) &&
            madeLookB d3 l 2 (pubOf X).arrayOf (pubOf X).Fp.next p.ns && p.seam.tl.heard.isNone
      else if X.kind = 0 then
        match Z.p.X.G[X.g]? with
        | none => false
        | some hp =>
          decide (nsOf l = some hp.ns) &&
            madeLookB d3 l 2 (pubOf X).arrayOf (pubOf X).Fp.next hp.ns && hp.tl.heard.isNone
      else false

theorem linkPlan_of_B {Z : ProofFile.Pub} {D : PubData} {l : Nat}
    (h : linkPlanB Z D.nsOf D.d3 l = true) : LinkPlan Z l D := by
  unfold linkPlanB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  split at h2
  · cases h2
  · rename_i X hX
    split at h2
    · rename_i hk
      split at h2
      · cases h2
      · rename_i p hp
        simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at h2
        obtain ⟨⟨a, b⟩, c⟩ := h2
        refine ⟨of_decide_eq_true h1, ?_, ?_, ?_, ?_⟩
        · intro X' p' hX' _ hp'
          obtain rfl : X = X' := Option.some.inj (hX.symm.trans hX')
          obtain rfl : p = p' := Option.some.inj (hp.symm.trans hp')
          exact a
        · intro X' _ hX' hk' _
          obtain rfl : X = X' := Option.some.inj (hX.symm.trans hX')
          omega
        · intro X' p' hX' _ hp'
          obtain rfl : X = X' := Option.some.inj (hX.symm.trans hX')
          obtain rfl : p = p' := Option.some.inj (hp.symm.trans hp')
          exact ⟨b, c⟩
        · intro X' _ hX' hk' _
          obtain rfl : X = X' := Option.some.inj (hX.symm.trans hX')
          omega
    · rename_i hk
      split at h2
      · rename_i hk0
        split at h2
        · cases h2
        · rename_i p hp
          simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at h2
          obtain ⟨⟨a, b⟩, c⟩ := h2
          refine ⟨of_decide_eq_true h1, ?_, ?_, ?_, ?_⟩
          · intro X' _ hX' hk' _
            obtain rfl : X = X' := Option.some.inj (hX.symm.trans hX')
            omega
          · intro X' p' hX' _ hp'
            obtain rfl : X = X' := Option.some.inj (hX.symm.trans hX')
            obtain rfl : p = p' := Option.some.inj (hp.symm.trans hp')
            exact a
          · intro X' _ hX' hk' _
            obtain rfl : X = X' := Option.some.inj (hX.symm.trans hX')
            omega
          · intro X' p' hX' _ hp'
            obtain rfl : X = X' := Option.some.inj (hX.symm.trans hX')
            obtain rfl : p = p' := Option.some.inj (hp.symm.trans hp')
            exact ⟨b, c⟩
      · cases h2

/-- K5Plan's ha · hW · c1 · c2 · hμ, and hμc, with code. -/
def k5PlanB (Z : ProofFile.Pub) (d5 : K5Data) (lay₀ : Params.ReqLayout) (l : Nat) : Bool :=
  d5.isAtt l && maskFirstB d5.shape l &&
    match d5.W.A[l / 2]?, Z.p.built.links[l]? with
    | some q, some X =>
      r2B lay₀ d5.shape l (pubOf X).arrayOf q.iU3 q.nW &&
        match Z.p.X.A[X.g]? with
        | some p =>
          ((startFork (pubOf X) p.ns).trees[q.iU3]?).any fun T => T.R == 1 && T.K == q.nW
        | none => false
    | _, _ => false

theorem k5Plan_of_B {Z : ProofFile.Pub} {D : PubData} {N : Numbers} {lay₀ : Params.ReqLayout} {l : Nat}
    (h : k5PlanB Z D.d5 lay₀ l = true) (hOwn : D.d5.ownOf l = N.sent l 0) :
    ∃ q μ, K5Plan Z l D N lay₀ q μ ∧
      μ < (((D.d5.shape.link[l]?.map (·.messages)).getD []).filter
        fun y => y.moment == 0).length := by
  unfold k5PlanB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨ha, hm⟩, h3⟩ := h
  obtain ⟨μ, hμ, hμc⟩ := mask_first_of hm
  split at h3
  · rename_i q X hq hX
    rw [Bool.and_eq_true] at h3
    obtain ⟨c2, h4⟩ := h3
    split at h4
    · rename_i p hp
      refine ⟨q, μ, ⟨ha, hq, ?_, ?_, hμ, hOwn⟩, hμc⟩
      · intro X' p' hX' _ hp'
        obtain rfl : X = X' := Option.some.inj (hX.symm.trans hX')
        obtain rfl : p = p' := Option.some.inj (hp.symm.trans hp')
        exact h4
      · intro X' hX'
        obtain rfl : X = X' := Option.some.inj (hX.symm.trans hX')
        exact c2
    · cases h4
  · cases h3

/-- What the head's link's letters hold of the plan: where the ground is the one that is made for a
request of zeros. -/
theorem letters_of_blank {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy mk Z = some G₀) {l : Nat} {HP : VerifiableInference.Desc.First.K2.HeadPar}
    (h : pureLetters G₀ l = some HP) :
    ∃ b, Z.p.built.links[l]? = some b ∧ HP.X.arrayOf = b.arrayOf ∧ HP.X.Fp = b.Fp ∧
      HP.hp = Z.p.X.H := by
  obtain ⟨links, e⟩ := Meaning.K2.blank_built hG
  have hW := ProofFile.Law.blankBy_W hG
  unfold pureLetters at h
  obtain ⟨X, hX, rfl⟩ := Option.map_eq_some_iff.1 h
  rw [e, Array.getElem?_zipWith] at hX
  cases hb : Z.p.built.links[l]? with
  | none => rw [hb] at hX; cases hX
  | some b =>
    rw [hb] at hX
    cases hl : links[l]? with
    | none => rw [hl] at hX; cases hX
    | some x =>
      rw [hl] at hX
      obtain rfl := Option.some.inj hX
      exact ⟨b, rfl, rfl, rfl, by show G₀.W.H = _; rw [hW]⟩

/-- HeadPlan's two, with code, off the plan's own built link and head's plan. -/
def headPlanB (Z : ProofFile.Pub) (nsOf : Nat → Option Nat) (d3 : K3Data) : Bool :=
  match Z.p.built.links[24]? with
  | some b => decide (nsOf 24 = some Z.p.X.H.ns) && madeLookB d3 24 3 b.arrayOf 0 Z.p.X.H.ns
  | none => false

theorem headPlan_of_B {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy mk Z = some G₀) {D : PubData} (h : headPlanB Z D.nsOf D.d3 = true) :
    HeadPlan G₀ D := by
  unfold headPlanB at h
  split at h
  · rename_i b hb
    rw [Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨?_, ?_⟩
    · intro HP h'
      obtain ⟨b', hb', _, _, e⟩ := letters_of_blank hG h'
      rw [e]
      exact h.1
    · intro HP h'
      obtain ⟨b', hb', ea, _, e⟩ := letters_of_blank hG h'
      obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
      rw [ea, e]
      exact h.2
  · cases h

theorem hFp_of_blank {mk : ProofFile.LinksBy} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy mk Z = some G₀) :
    ∀ HP, pureLetters G₀ 24 = some HP →
      ∃ X, Z.p.built.links[24]? = some X ∧ X.Fp.trees = HP.X.Fp.trees := by
  intro HP h
  obtain ⟨b, hb, _, e, _⟩ := letters_of_blank hG h
  exact ⟨b, hb, by rw [e]⟩

end P1K2

#print axioms P1K2.linkPlan_of_B
#print axioms P1K2.k5Plan_of_B
#print axioms P1K2.letters_of_blank
#print axioms P1K2.headPlan_of_B
#print axioms P1K2.hFp_of_blank
