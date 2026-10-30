-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/FallFormLay.lean: K9's FALL ON THE FREE SLOTS, AT THE TWELVE FEED-FORWARD SEGMENTS, IN
THE FORM OF THE FRAME's PREMISE hF9 (see Honest/K9/FallFormAny.lean). THAT PREMISE's TEXT AT l := 2 g IS THE END, AND IT
IS EXCHANGED, NOT PAID: for hPW (the gate's condition gives ONE SENTENCE ON THE STATE in front of the batching,
`BatFrontLay`, A DEFINITION OF THIS FILE, and "reached by the wrapped blocks") and hq. `BatFrontLay` IS SHOWN AT NO
STATE OF A RUN. The twin of `k9_fallDebt_form_att` (Honest/K9/FallFormAtt.lean). One definition; statements and proofs;
no goal is stated.
  `BatFrontLay p4 n s`   A DEFINITION: at every a₀ with s.here = .lay a₀: `LiveLayers p4 s a₀ n`
      (Honest/K9/GoodLayLive.lean). At a state that stands elsewhere it holds for nothing: THAT COSTS NOTHING HERE ALONE
      BECAUSE "here" IS PAID INSIDE THE THEOREM, from "reached"
  `sub_even_lay`   the even segments below the head's are feed-forward segments, by evaluation: `sub_even` of
      Honest/K9/TotalLay.lean under another name, so that that file and what lies beneath it need not lie beneath this
  `lay_at_front`   a state reached at 14 (2 g) + 9 stands in a feed-forward segment, and its part holds K4's own (a₀.own
      = some o): by the smallness test's `list_at_layers` (Johnson/P1K8R/ListAtLayers.lean) and the six cases of
      `S.own?`
  **`k9_fallDebt_form_lay`**   under the head · hB : the base is the head's own (a public equation, which the caller of
      that file's bound has) · cut · hPW: at the batching of 2 g, at K4's parameters p4 (`LPFK9.k4ParAt`) and the
      tests' numbers u: PW b fr s' gives `BatFrontLay p4 u.2.2.filled s'` and "reached" · hq. HOW: `k9_fallDebt_form_at`
      at I := "l = 2 g for a g < 12" · the walk's premises by `free_at_seat` (Honest/K9/AtSeat.lean), `sub_even_lay` ·
      `lay_at_front` · `goodW_layers_live`
WHERE IT WOULD BE TRUE FOR NOTHING, and what is said of hq, of qF and of notGood: as in Honest/K9/FallFormAny.lean's
head.
WHAT IS NOT CLAIMED. hPW at any gate's condition. `BatFrontLay` at any state, in this file: `liveLayers_of_clauses`
leads to it from nine premises; all nine are paid at the states that the frame's field hands, from the silence of three
families of marks, in Honest/K9/BatFrontHandedMarks.lean: at no run. The head's segment. `k9_fallDebt_form_lay` is
called by Honest/K9/FallFormLayWith.lean alone; `BatFrontLay` stands in BatFrontHanded.lean too. At the full size and
the format's second hash function alone. Nothing on any property.
GROUND: beneath this file, beside the sealed library (laws.11), lie 505 files, this one among them: reading copies, all
but ours.
-/
import Johnson.Desc.ProofFile.Honest.K9.FallFormAny
import Johnson.Desc.ProofFile.Honest.K9.GoodLayLive
import Johnson.Desc.ProofFile.Honest.K9.AtSeat
import Johnson.P1K8R.ListAtLayers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Maker (RDT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest (Odds Fall FallDebt KindFits repsAt fallSeat)
open Iop
open scoped ENNReal

/-- The even segments below the head's are feed-forward segments. (`sub_even` of Honest/K9/TotalLay.lean, typed once
more, so that that file and what lies beneath it need not lie beneath this one.) -/
theorem sub_even_lay : ∀ g < 12, IM.subAt (2 * g) = .layers := by decide

/-- **What is asked of the state in front of a feed-forward segment's batching**: where it stands in such a segment, it
is "live" (Honest/K9/GoodLayLive.lean) there. -/
def BatFrontLay (p4 : OnBytes.Desc.First.K4.Par) (n : ℕ) (s : S) : Prop :=
  ∀ a₀, s.here = .lay a₀ → LiveLayers p4 s a₀ n

/-- A state reached in front of a feed-forward segment's batching stands in such a segment, and its part holds K4's own
(a₀.own = some o). -/
theorem lay_at_front {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {g : ℕ} (hg : g < 12) {Q' : Type}
    {start : Q' → S} {z : Q'} {s' : S} (hr : Reach 0 c.blocksInOrder start (14 * (2 * g) + 9) (z, s')) :
    ∃ a₀ o, s'.here = .lay a₀ ∧ a₀.own = some o := by
  have hr' : Reach 0 c.blocksInOrder start (28 * g + 9) (z, s') := by
    rw [show 28 * g + 9 = 14 * (2 * g) + 9 by omega]
    exact hr
  obtain ⟨-, -, o, -, -, eo, -⟩ := P1K8.list_at_layers P pp lay F Z Bs base c A B hS hR O Q' start g hg z s' hr'
  unfold S.own? at eo
  cases hh : s'.here with
  | lay a => rw [hh] at eo; exact ⟨a, o, rfl, eo⟩
  | between => rw [hh] at eo; exact nomatch eo
  | att a => rw [hh] at eo; exact nomatch eo
  | head a => rw [hh] at eo; exact nomatch eo
  | fin a => rw [hh] at eo; exact nomatch eo
  | mem a => rw [hh] at eo; exact nomatch eo

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **THE FRAME's PREMISE ON K9's FALL, AT THE TWELVE FEED-FORWARD SEGMENTS, EXCHANGED**: its end is that premise's text
at l := 2 g, with fs for the list of falls and PW b for the gate's condition. -/
theorem k9_fallDebt_form_lay (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (fs : List (Fall S)) (notGood : ℕ → Odds) {pre₁ : List (Block S ProofFile.Cl)} {e₁ : Block S ProofFile.Cl}
    (cut : cF.blocksInOrder = pre₁ ++ [e₁]) (PW : Block S ProofFile.Cl → List Fmt.Drawn → S → Prop)
    (qF : Block S ProofFile.Cl → Fall S → ℝ≥0∞)
    (hPW : ∀ g, g < 12 → ∀ b, cF.blocksInOrder[14 * (2 * g) + 9]? = some b → ∀ p4 u,
      LPFK9.k4ParAt Zp Bs.G₀ (2 * g) = some p4 → Desc.K9.testsWhere Zp.p.X (2 * g) 0 = some u →
      ∀ fr s', PW b fr s' → BatFrontLay p4 u.2.2.filled s' ∧
        ∃ z, Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) (14 * (2 * g) + 9) (z, s'))
    (hq : ∀ g, g < 12 → ∀ b p u, IM.k9At Zp (2 * g) = some p →
      Desc.K9.testsWhere Zp.p.X (2 * g) 0 = some u →
      kapSl 128 ^ 3 * ((u.2.2.filled * (u.2.1 - 1) : ℕ) : ℝ≥0∞) / ((sizeOfE : ℕ) : ℝ≥0∞) ≤
        qF b (quietFall p u.2.2.filled (u.2.1 - 1) (notGood (2 * g)))) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B → (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ g p u, g < 12 → IM.k9At Zp (2 * g) = some p →
      Desc.K9.testsWhere Zp.p.X (2 * g) 0 = some u →
      quietFall p u.2.2.filled (u.2.1 - 1) (notGood (2 * g)) ∈ repsAt cF.blocksInOrder fs b →
      ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt (_root_.Run.ckP .two) (quietFall p u.2.2.filled (u.2.1 - 1) (notGood (2 * g))) 0 b
        (b' :: B ++ [e₁]) dsb [] (PW b)
        (qF b (quietFall p u.2.2.filled (u.2.1 - 1) (notGood (2 * g)))) := by
  intro A b b' B e hs hn g p u hg hp hu hmem dsb hk
  refine k9_fallDebt_form_at h fs notGood cut PW qF (fun l => ∃ g, g < 12 ∧ l = 2 * g) ?_ ?_
    A b b' B e hs hn (2 * g) p u (by omega) ⟨g, hg, rfl⟩ hp hu hmem dsb hk
  · rintro l hl ⟨g', hg', rfl⟩ b₁ hb₁ Lk p₁ w Sd fr s' q
    have n24 : ¬ 2 * g' = 24 := by omega
    rw [if_neg n24] at hb₁ Sd ⊢
    obtain ⟨Bs', base, O⟩ := h.laid.opened
    obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
    obtain ⟨Lk', p', p4, X, w', e1, e2, e3, -, e5, -, -, walk, -⟩ :=
      free_at_seat h.scope h.reads O (2 * g') hl (sub_even_lay g' hg')
    obtain rfl : Lk = Lk' := Option.some.inj (Sd.link.symm.trans e1)
    obtain rfl : w = w' := Option.some.inj (Sd.tested.symm.trans e5)
    obtain ⟨hfront, z, hrr⟩ := hPW g' hg' b₁ hb₁ p4 w e3 e5 fr s' q
    obtain ⟨a₀, -, ha₀, -⟩ :=
      lay_at_front h.scope h.reads O hg' (Johnson.Desc.First.Walk.Tied.reach_raw hrr)
    exact ⟨goodW_layers_live Lk p4 _ p₁ s' a₀ (walk s' a₀ ha₀) _ (hfront a₀ ha₀), z, hrr⟩
  · rintro l - ⟨g', hg', rfl⟩ b₁ p₁ u₁ hp₁ hu₁
    exact hq g' hg' b₁ p₁ u₁ hp₁ hu₁

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.sub_even_lay
#print axioms ProofFile.Honest.K9.BatFrontLay
#print axioms ProofFile.Honest.K9.lay_at_front
#print axioms ProofFile.Honest.K9.k9_fallDebt_form_lay
