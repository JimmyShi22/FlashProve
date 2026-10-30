-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/FallsAtLists.lean: THE SMALLNESS TEST's TWO FALLS IN THE HONEST SIDE's FRAME: THE
FRAME's AUTHORS' BOUND ON THE CHANCE THAT A RUN MEETS A FALL, AT THEIR OWN LISTS OF FALLS AND MARKS,
WITH OUR MEMBER's TWO FIELDS LAID IN; AND WHAT IS LEFT OF THE FALLS' BOUNDS, BY OWNER. A CHECK THAT
THE FORMS MEET. Lemmas; NONE OF THE LIBRARY's GOALS. A joining. Nothing on completeness, soundness
or hiding.

  `full_cases`   by the texts of fallsFull (Johnson/Desc/ProofFile/Honest/Law/FallsFull.lean),
      fallsHead, linkFalls (FallsHead.lean)
  **`falls_five_at_member`**   falls_five (Johnson/Desc/ProofFile/Honest/Law/CoverHeadFive.lean);
      `firstAsks_own` (Johnson/P1K8R/CountedAtOwn.lean), of whose record the fields hF and hP' are
      spent; part1_sub, k3_sub, k5_sub, k6_sub (MarksHeadSub.lean); fallsFull_seats
      (FallsFull.lean); hq0_head (MarksHead.lean); kit_two (KitTwo.lean)
  **`falls_five_by_owner`**   the two
Kin. `falls_at_member` (Johnson/P1K8R/FallsAtMember.lean): the like call of falls_head_fit at an
elder member, at free lists: twenty named hypotheses. The frame's authors' fallsHead_seats
(Johnson/Desc/ProofFile/Honest/Law/FallsHeadAt.lean) splits the list in its proof as `full_cases`
does; their front_at, share_at, quiet_at (the same file) go the other way: at a member's number, a
record of the list.
Limits. BOUNDS UNDER FIFTEEN AND SIXTEEN NAMED HYPOTHESES, NONE PROVED HERE OF ANYTHING: h, hB
(`falls_five` stands at every ground; hB binds ours to the opened one); hG, hXc, which fix letters;
hRd, hn, hf₂, hf₃, cut, which `falls_five` asks; hseat, hM, hPM: three of its five fields, handed
through: the marks' authors' matter; hFr (or hF9 and hF4), hqF, hPr: what our member asks for the
two others. hF9, hF4 ARE OTHER AUTHORS' MATTER: the bounds for at most 25 and at most twelve
records, each where it is counted, under our member's condition on the state and the letter Pr:
whatever condition of their own these authors need beyond ours must be laid into Pr, AND hPr THEN
OWES IT AT THE STATE HANDED. hPr asks the caller's own letter Pr at the state handed. A SUM OF
LETTERS: kapL, kapH, notGood, r0, qF, p₂, p₃ are open, and PM, Pr too: NO NUMBER FOLLOWS, and
nothing says that the right side is below 1. All that is assumed of the other two chains sits in hf₂
and hf₃; their prices p₂, p₃ stay letters. At strings of hash blocks alone. The head h is a
hypothesis; the full size alone. It proves no property of a prover or a protocol.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.CountedAtOwn
import Johnson.Desc.ProofFile.Honest.Law.CoverHeadFive
import Johnson.Desc.ProofFile.Honest.Law.MarksHeadSub
import Johnson.Desc.ProofFile.Honest.Law.KitTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Slice
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (RDT uLT drawnT WholeD chainsOf)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open ProofFile.Honest.K3.Good (markK3 markOut)
open Johnson.Desc.First.Walk.Tied (Reach RchAt reach_raw reach_fold)
open ProofFile.Honest (Odds FallDebt KindFits Fall Mark MarkDebt FirstAsks firstAsks_cut fellBy silentQ
  fitMarks drawsFit walk groupOf localFall ChainAt Local fallSeat markSeat cut_first repsAt
  priceAt hin_reps hp₁_sum hp₂_sum places_nodup ChainProgress Mid marksQuiet Prover Ready at₁
  letter_starts letter_tree file_head hz_head Sides ProverCoinCounts Coins ready fallAt drawsAt gates₁ gates₂
  gates₃ kit_two falls_five fallsFull fallsFull_seats marksHead qMHead hq0_head part1_sub k3_sub
  k5_sub k6_sub fallsHead linkFalls)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open ProofFile.Honest.K8 (k8ShareFall k8Second)
open Iop
open scoped ENNReal

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat} {W₀ Rc Tr X₁ : Type}

/-- **A record of the frame's authors' list `fallsFull`
(Johnson/Desc/ProofFile/Honest/Law/FallsFull.lean) at the opened ground is one of the smallness
test's fifty (`K8Fall`, Johnson/P1K8R/CountedAtOwn.lean), or the batching's authors' fall of the
free slots at a segment, or the feed-forward layers' own rounds' authors' fall at a group.** By the
list's text. -/
theorem full_cases {notGood : Nat → Odds} {r0 : Nat → Nat} {g : Fall S}
    (hg : g ∈ fallsFull Z Bs.G₀ notGood r0) :
    K8Fall Z Bs g ∨
      (∃ l p u, l < 25 ∧ IM.k9At Z l = some p ∧ Desc.K9.testsWhere Z.p.X l 0 = some u ∧
        g = ProofFile.Honest.K9.quietFall p u.2.2.filled (u.2.1 - 1) (notGood l)) ∨
      ∃ gk hp, gk < 12 ∧ Bs.G₀.W.G[gk]? = some hp ∧
        g = ProofFile.Honest.K4.k4Fall ⟨Bs.G₀.W.layers, hp, gk, 2 * gk, 3, r0 gk, 2 * gk⟩ := by
  unfold fallsFull fallsHead at hg
  rcases List.mem_append.1 hg with hg | hg
  · obtain ⟨l, hl, hg⟩ := List.mem_flatMap.1 hg
    have hl' : l < 25 := List.mem_range.1 hl
    unfold linkFalls at hg
    rcases List.mem_append.1 hg with hg | hg
    · rcases List.mem_append.1 hg with hg | hg
      · exact Or.inl ⟨l, hl', Or.inl (List.mem_singleton.1 hg)⟩
      · split at hg
        next p u hp hu =>
          exact Or.inr (Or.inl ⟨l, p, u, hl', hp, hu, List.mem_singleton.1 hg⟩)
        next => simp at hg
    · split at hg
      next Xl hX =>
        exact Or.inl ⟨l, hl', Or.inr ⟨Xl, by rw [Array.getElem?_toList]; exact hX,
          List.mem_singleton.1 hg⟩⟩
      next => simp at hg
  · obtain ⟨gk, hgk, hg⟩ := List.mem_filterMap.1 hg
    obtain ⟨hp, hhp, rfl⟩ := Option.map_eq_some_iff.1 hg
    exact Or.inr (Or.inr ⟨gk, hp, List.mem_range.1 hgk, hhp, rfl⟩)

set_option maxHeartbeats 4000000 in
/-- **A CHECK OF FIT BY LEAN, AND NO MORE: THE FRAME's AUTHORS' `falls_five`
(Johnson/Desc/ProofFile/Honest/Law/CoverHeadFive.lean) CALLED WITH TWO OF ITS FIVE FIELDS, hF AND
hP', OUT OF OUR MEMBER `firstAsks_own` (Johnson/P1K8R/CountedAtOwn.lean), AT THE LISTS AND NUMBERS
THAT `falls_five` BINDS**: the falls `fallsFull`, the marks `marksHead`, the marks' numbers
`qMHead`. Their bound on the chance that a run meets a fall, at strings of hash blocks. Our member's
premises hmk, hsub, hsubK, hsubA are their part1_sub, k3_sub, k6_sub, k5_sub (MarksHeadSub.lean);
hfs their fallsFull_seats (FallsFull.lean); hq0 their hq0_head (MarksHead.lean); the kit's condition
their kit_two (KitTwo.lean). kapL, kapH: the two letters of `qMHead`, the lookups' authors' and the
output head's own rounds' authors'. -/
theorem falls_five_at_member {Pz : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Np : H2U.Places4} {x₀ : Look.Place} (h : P5J.AtMgA OnBytes.secondHashFunction Pz D r Z Np c x₀)
    (hB : ProofFile.baseOf Z (ProofFile.pureSeat OnBytes.secondHashFunction Z) = .ok Bs)
    {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) {Bk : ProverCoinCounts} {Ky X₀ : Type}
    (G : Sides (P5J.F0T OnBytes.secondHashFunction Z Np c) Bk W₀ Rc Ky Tr X₀ X₁)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X₁) (k : Coins Bk) (p₂ p₃ : Nat → ℝ≥0∞)
    (kapL kapH : ℝ≥0∞) (notGood : Nat → Odds) (r0 : Nat → Nat)
    {pre₁ : List (Block S Claim)} {e₁ : Block S Claim} (x : ProofFile.Inst)
    (Xc : List Fmt.Drawn → ChainAt S Claim (Local W₀ Rc ProofFile.Inst Tr) X₁)
    (PM : Block S Claim → List Fmt.Drawn → Prop)
    (Pr : Block S Claim → List Fmt.Drawn → S → Prop) (qF : Block S Claim → Fall S → ℝ≥0∞)
    (w₀ : W₀) (rc : Rc)
    (R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X₁)
    (hG : G.falls₁ = fallsFull Z Bs.G₀ notGood r0)
    (hXc : Xc = fun _ => at₁ (P5J.F0T OnBytes.secondHashFunction Z Np c) (G.prover H) w₀ rc x R)
    (hRd : ready (P5J.F0T OnBytes.secondHashFunction Z Np c) Bk (G.prover H) w₀ rc x k = .ok R)
    (hn : ∀ g ∈ (G.prover H).first, g.place.kind ≠ KindName.frame)
    (hf₂ : G.falls₂ = []) (hf₃ : G.falls₃ = []) (cut : c.blocksInOrder = pre₁ ++ [e₁])
    (hseat : ∀ mk ∈ marksHead Z Bs.G₀, markSeat mk.place = true)
    (hM : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (marksHead Z Bs.G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb (PM b) (qMHead kapL kapH b mk))
    (hPM : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ fr, 0 ≤ fr.length → (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy c.blocksInOrder G.falls₁ (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (marksHead Z Bs.G₀ ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr → PM b fr)
    (hFr : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ g ∈ repsAt c.blocksInOrder G.falls₁ b, ¬ K8Fall Z Bs g → ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      FallDebt (_root_.Run.ckP .two) g 0 b (b' :: B ++ [e₁]) dsb []
        (PWith Z c Bs Pr b) (qF b g))
    (hqF : ∀ b g, g.share.val ≤ qF b g)
    (hPr : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ fr a z s', 0 ≤ fr.length →
      (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy c.blocksInOrder G.falls₁ (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (marksHead Z Bs.G₀ ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr →
      (Xc (fr.take 0)).start = some a →
      walk (Xc (fr.take 0)).lay
        ((Xc (fr.take 0)).steps.take (0 + (A.flatMap (·.rounds)).length)) (fr.drop 0) a =
        .ok z →
      z.ver = some s' →
      (b.rounds ≠ [] → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) A.length (x.pub, s')) →
      Pr b fr s') :
    Iop.prRho {ρ : Iop.Rho (chainsOf (_root_.Run.ckP .two) D tF tJ t3).sh |
        (fallAt G H w₀ rc x k (drawsAt (_root_.Run.ckP .two) D tF tJ t3 ρ)).isSome = true} ≤
      ((gates₁ D G H w₀ rc x R (marksHead Z Bs.G₀ ++ fitMarks pre₁)
        (priceAt pre₁ (marksHead Z Bs.G₀) (qMHead kapL kapH) (repsAt c.blocksInOrder G.falls₁) qF)
        pre₁).map (·.p)).sum +
        (((gates₂ D G H w₀ rc x R (fitMarks (P5J.F0T OnBytes.secondHashFunction Z Np c).shared.blocksInOrder) p₂).map
            (·.p)).sum +
          ((gates₃ D G H w₀ rc x R (fitMarks (P5J.F0T OnBytes.secondHashFunction Z Np c).second.blocksInOrder) p₃).map
            (·.p)).sum) := by
  subst hXc
  have hfs : ∀ f ∈ G.falls₁, (fallSeat P5J.At.links) f.place = true := by
    rw [hG]
    exact fallsFull_seats h Bs.G₀
  have St := firstAsks_own h hB G.falls₁ (marksHead Z Bs.G₀) x _ PM (qMHead kapL kapH) Pr qF
    (G.prover H) w₀ rc R rfl (part1_sub Z Bs.G₀) (k3_sub Z Bs.G₀) (k6_sub Z Bs.G₀)
    (k5_sub Z Bs.G₀) cut hfs hseat (hq0_head kapL kapH pre₁) hM hPM hFr hqF hPr
  exact falls_five (_root_.Run.ckP .two) kit_two tF tJ t3 h Bs.G₀ kapL kapH notGood r0 G H w₀ rc x
    k R p₂ p₃ pre₁ e₁ cut hG hRd hn hf₂ hf₃ _ rfl PM (PWith Z c Bs Pr) qF hseat hM hPM St.hF St.hP'

set_option maxHeartbeats 4000000 in
/-- **THE SAME BOUND WITH WHAT IS LEFT OF THE FALLS' BOUNDS TOLD BY OWNER**: hFr is gone; in its
stead hF9: the bound for the fall of the free slots, where it is counted; hF4: the bound for the
feed-forward layers' own rounds' fall, where it is counted: by `full_cases` the list has no other
record beside the smallness test's fifty. -/
theorem falls_five_by_owner {Pz : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Np : H2U.Places4} {x₀ : Look.Place} (h : P5J.AtMgA OnBytes.secondHashFunction Pz D r Z Np c x₀)
    (hB : ProofFile.baseOf Z (ProofFile.pureSeat OnBytes.secondHashFunction Z) = .ok Bs)
    {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3) {Bk : ProverCoinCounts} {Ky X₀ : Type}
    (G : Sides (P5J.F0T OnBytes.secondHashFunction Z Np c) Bk W₀ Rc Ky Tr X₀ X₁)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X₁) (k : Coins Bk) (p₂ p₃ : Nat → ℝ≥0∞)
    (kapL kapH : ℝ≥0∞) (notGood : Nat → Odds) (r0 : Nat → Nat)
    {pre₁ : List (Block S Claim)} {e₁ : Block S Claim} (x : ProofFile.Inst)
    (Xc : List Fmt.Drawn → ChainAt S Claim (Local W₀ Rc ProofFile.Inst Tr) X₁)
    (PM : Block S Claim → List Fmt.Drawn → Prop)
    (Pr : Block S Claim → List Fmt.Drawn → S → Prop) (qF : Block S Claim → Fall S → ℝ≥0∞)
    (w₀ : W₀) (rc : Rc)
    (R : Ready W₀ Rc ProofFile.Inst Ky Tr X₀ X₁)
    (hG : G.falls₁ = fallsFull Z Bs.G₀ notGood r0)
    (hXc : Xc = fun _ => at₁ (P5J.F0T OnBytes.secondHashFunction Z Np c) (G.prover H) w₀ rc x R)
    (hRd : ready (P5J.F0T OnBytes.secondHashFunction Z Np c) Bk (G.prover H) w₀ rc x k = .ok R)
    (hn : ∀ g ∈ (G.prover H).first, g.place.kind ≠ KindName.frame)
    (hf₂ : G.falls₂ = []) (hf₃ : G.falls₃ = []) (cut : c.blocksInOrder = pre₁ ++ [e₁])
    (hseat : ∀ mk ∈ marksHead Z Bs.G₀, markSeat mk.place = true)
    (hM : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (marksHead Z Bs.G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb (PM b) (qMHead kapL kapH b mk))
    (hPM : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ fr, 0 ≤ fr.length → (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy c.blocksInOrder G.falls₁ (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (marksHead Z Bs.G₀ ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr → PM b fr)
    (hF9 : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ l p u, l < 25 → IM.k9At Z l = some p → Desc.K9.testsWhere Z.p.X l 0 = some u →
      ProofFile.Honest.K9.quietFall p u.2.2.filled (u.2.1 - 1) (notGood l) ∈
        repsAt c.blocksInOrder G.falls₁ b →
      ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt (_root_.Run.ckP .two)
        (ProofFile.Honest.K9.quietFall p u.2.2.filled (u.2.1 - 1) (notGood l)) 0 b
        (b' :: B ++ [e₁]) dsb [] (PWith Z c Bs Pr b)
        (qF b (ProofFile.Honest.K9.quietFall p u.2.2.filled (u.2.1 - 1) (notGood l))))
    (hF4 : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ gk hp, gk < 12 → Bs.G₀.W.G[gk]? = some hp →
      ProofFile.Honest.K4.k4Fall ⟨Bs.G₀.W.layers, hp, gk, 2 * gk, 3, r0 gk, 2 * gk⟩ ∈
        repsAt c.blocksInOrder G.falls₁ b →
      ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt (_root_.Run.ckP .two)
        (ProofFile.Honest.K4.k4Fall ⟨Bs.G₀.W.layers, hp, gk, 2 * gk, 3, r0 gk, 2 * gk⟩) 0 b
        (b' :: B ++ [e₁]) dsb [] (PWith Z c Bs Pr b)
        (qF b (ProofFile.Honest.K4.k4Fall ⟨Bs.G₀.W.layers, hp, gk, 2 * gk, 3, r0 gk, 2 * gk⟩)))
    (hqF : ∀ b g, g.share.val ≤ qF b g)
    (hPr : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ fr a z s', 0 ≤ fr.length →
      (fr.drop 0).length = 0 + (A.flatMap (·.rounds)).length →
      fellBy c.blocksInOrder G.falls₁ (Xc (fr.take 0)) (0 + (A.flatMap (·.rounds)).length)
        (fr.drop 0) = false →
      silentQ (marksHead Z Bs.G₀ ++ fitMarks pre₁) 0 pre₁ (0 + A.length) fr →
      (Xc (fr.take 0)).start = some a →
      walk (Xc (fr.take 0)).lay
        ((Xc (fr.take 0)).steps.take (0 + (A.flatMap (·.rounds)).length)) (fr.drop 0) a =
        .ok z →
      z.ver = some s' →
      (b.rounds ≠ [] → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) A.length (x.pub, s')) →
      Pr b fr s') :
    Iop.prRho {ρ : Iop.Rho (chainsOf (_root_.Run.ckP .two) D tF tJ t3).sh |
        (fallAt G H w₀ rc x k (drawsAt (_root_.Run.ckP .two) D tF tJ t3 ρ)).isSome = true} ≤
      ((gates₁ D G H w₀ rc x R (marksHead Z Bs.G₀ ++ fitMarks pre₁)
        (priceAt pre₁ (marksHead Z Bs.G₀) (qMHead kapL kapH) (repsAt c.blocksInOrder G.falls₁) qF)
        pre₁).map (·.p)).sum +
        (((gates₂ D G H w₀ rc x R (fitMarks (P5J.F0T OnBytes.secondHashFunction Z Np c).shared.blocksInOrder) p₂).map
            (·.p)).sum +
          ((gates₃ D G H w₀ rc x R (fitMarks (P5J.F0T OnBytes.secondHashFunction Z Np c).second.blocksInOrder) p₃).map
            (·.p)).sum) := by
  refine falls_five_at_member h hB tF tJ t3 G H k p₂ p₃ kapL kapH notGood r0 x Xc PM Pr qF w₀ rc R
    hG hXc hRd hn hf₂ hf₃ cut hseat hM hPM ?_ hqF hPr
  intro A b b' B e hs hn' g hg hnk dsb hk
  have hmem : g ∈ fallsFull Z Bs.G₀ notGood r0 := by
    rw [← hG]
    exact (List.mem_filter.1 hg).1
  rcases full_cases hmem with h8 | ⟨l, p, u, hl, hp, hu, rfl⟩ | ⟨gk, hp, hgk, hhp, rfl⟩
  · exact absurd h8 hnk
  · exact hF9 A b b' B e hs hn' l p u hl hp hu hg dsb hk
  · exact hF4 A b b' B e hs hn' gk hp hgk hhp hg dsb hk

end

end P1K8

#print axioms P1K8.full_cases
#print axioms P1K8.falls_five_at_member
#print axioms P1K8.falls_five_by_owner
