-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/MergeLiveHanded.lean: AT THE STATE THAT THE FRAME's FIELD HANDS IN FRONT OF THE OUTPUT
HEAD's SEGMENT's BATCHING (the member number 347) THE MERGE's CONDITION `MergeLive`
(Johnson/Desc/K11/Live/RunStatement.lean) HOLDS AT THE WRITTEN NUMBERS 18 AND 3531, WHERE THE LISTED MARKS HAVE BEEN
SILENT. A joining of the smallness test's lemmas on K11; one statement with its proof; no definition; no goal is
stated.
  **`mergeLive_handed`** under the head · hB · the smallness test's marks (`P1K8.part1Marks Zp Bs.G₀`) and the fit's marks among
      the marks asked · the walk's premises at A.length = 347: there are a' and xh with s'.here = .head a', a'.x = some
      xh and `MergeLive 18 3531 xh.sV s'`. HOW: the member number 346 in its seated form: `headMergeAtFull` ·
      its own step leads into s': `P1K8.mid_handed` at 346 · in front of it the state holds the head's own part and what
      the head heard: by "reached": `backToHeadRaw` and `sv_at_yes` (the lines of `svBelowRaw`) · the merge's
      mark is the last of the list (`part1Marks_eq`), stands at the member's place (`merge_place`) and is
      silent (`mark_silent`) · the rounds' drawn values fit (`fit_at_silent`) · so no later draw reads 0
      (`headMergeMarkSilent` · `headMergeLaterFit` · `laterDrawsNoDigest`) · `mergeLiveBehindRaw` · the member leaves
      what the head heard: `five_decide_frontLater` at 346
WHAT IS NOT CLAIMED. That any walk returns. ARGUED, STATED IN NO THEOREM:
AT A FILLING WITH NO SIDE OF THE CLOSING (K10), AS `widerFillAt` (`k10_ten`, Honest/K10/AtFill.lean), NO STEP
IS TAKEN BEHIND NUMBER 12; THE PREMISES HERE STAND AT 347: AT SUCH A FILLING THE THEOREM SPEAKS OF NOTHING. At the
shipped filling (onlineFilling), which has the closings, nothing here shows the premises met. Nor that the marks are
silent at any run; how often the merge's mark speaks. NO MEMBER. Where a listed challenge reads 0 the theorem says
nothing: that is the mark's share. IT STANDS OVER MANY FILES THAT ARE NO PART OF THE SEALED LIBRARY (laws.11): OF THE
LEMMAS CALLED HERE: that house's Johnson/P1K8R/ (`mid_handed` · `fold_window_end` · `fit_at_silent` · `part1Marks_eq`
· `merge_place`), Johnson/Desc/K11/Front/ and Live/ (`backToHeadRaw` · `mergeLiveBehindRaw` · `MergeLive` itself)
and Honest/K11/Mark/ (the mark and its three lemmas); the frame's house's Honest/Law/ (`mark_silent`); and all that
these import, of several houses. Of these Honest/K11/Mark/Join.lean · AtStep.lean with their statements' files lie
in no list or lot that we know of. Under set_option maxHeartbeats 1000000. Called by Honest/K9/GoodHeadHanded.lean
alone. At the full size and the format's second hash function alone, as h. Nothing on any property.
-/
import Johnson.P1K8R.ClausesAtFrame
import Johnson.P1K8R.Part1Marks
import Johnson.Desc.K11.Front.LiveBehind
import Johnson.Desc.K11.Exchange.AtFull
import Johnson.Desc.ProofFile.Honest.K11.Mark.AtStep
import Johnson.Desc.Kinds.Law.K6FiveFront
import Johnson.P1K2R.SitsDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest (Lay Mid Step walk Mark markOf marksQuiet mark_silent drawsFit)
open Johnson.Desc.First.ForkMerge (headClaimMergeKind)
open Johnson.Desc.First.ForkMerge.Live (MergeLive laterDraws)
open Johnson.Desc.First.ForkMerge.Front (backToHeadRaw mergeLiveBehindRaw)
open ProofFile.Honest.K11 (headMergeMark headMergeMarkSilent headMergeLaterFit laterDrawsNoDigest)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {W Y : Type}

set_option maxHeartbeats 1000000 in
/-- **AT THE STATE THAT THE FRAME's FIELD HANDS IN FRONT OF THE HEAD's SEGMENT's BATCHING THE MERGE's CONDITION HOLDS AT
THE WRITTEN NUMBERS**, where the listed marks are silent; and the state still holds what the head heard. -/
theorem mergeLive_handed (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (ms : List Mark)
    (hsub1 : ∀ mk ∈ P1K8.part1Marks Zp Bs.G₀, mk ∈ ms)
    {A t : List (Block S ProofFile.Cl)} {b : Block S ProofFile.Cl} (hall : cF.blocksInOrder = A ++ b :: t)
    (hfit : ∀ d ∈ A, (⟨d.place,
      fun _ own => if drawsFit d.rounds own then none else some "its rounds cannot draw these",
      ⟨0, 1⟩⟩ : Mark) ∈ ms)
    (hA : A.length = 347) (hpos : 0 < b.rounds.length)
    (L : Lay) (hft : L.firstTree = 0) {a₀ z : ProofFile.Honest.ChainProgress S ProofFile.Cl W Y} {zp : ProofFile.InstPub} {s' : S}
    {m₀ : Option (Mid W Y)} {ss : List (Step W Y)} {fr : List Fmt.Drawn}
    (hm : m₀.isSome = true)
    (ha : ProofFile.Honest.ChainProgress.start L cF.blocksInOrder m₀ (some (ProofFile.startS Zp zp)) [] = .ok a₀)
    (hn : fr.length = (A.flatMap (·.rounds)).length) (hq : marksQuiet ms A [] fr = true)
    (hz : walk L ss fr a₀ = .ok z) (hv : z.ver = some s') :
    ∃ (a' : HeadOwn) (xh : OnBytes.Model.Head.Heard),
      s'.here = .head a' ∧ a'.x = some xh ∧ MergeLive 18 3531 xh.sV s' := by
  obtain ⟨Bs₁, Lk, name, hB₁, -, -, -, -, f346, -⟩ :=
    Johnson.Desc.First.ForkMerge.Exchange.headMergeAtFull Z D r Zp Np cF x h
  obtain rfl : Bs = Bs₁ := Except.ok.inj (hB.symm.trans hB₁)
  obtain ⟨Bs₂, base, O⟩ := h.laid.opened
  obtain rfl : Bs = Bs₂ := Except.ok.inj (hB.symm.trans O.made)
  have inA : ∀ {i : ℕ} {d : Block S ProofFile.Cl}, i < 347 → cF.blocksInOrder[i]? = some d → d ∈ A := by
    intro i d hi hd
    rw [hall, List.getElem?_append_left (by omega)] at hd
    exact List.mem_of_getElem? hd
  -- the merge's member's own step leads into s'
  obtain ⟨tj, tk, Rt, dt, q₂, q₃, e₂, e₃, -, g, -, hsil, hrj, -, hf⟩ :=
    P1K8.mid_handed cF.blocksInOrder (ProofFile.startS Zp) zp (n := 346) f346 ms hall hfit (by omega) hpos L hft hm ha hn hq hz hv
  rw [hA] at hf
  obtain rfl : s' = tk := P1K8.fold_window_end hf
  have d := ((Sound.step_ok_iff 0 _ tj s' Rt dt dt.length).1 g).2.2.2
  -- in front of it the state holds the head's own part and what the head heard: by "reached"
  obtain ⟨s₀, s₁, rv, gs, hd₀, hW, hk⟩ := backToHeadRaw Z D r Zp Np cF x Bs zp tj h hB hrj
  obtain ⟨o₁, xh, ho₁, hx₁, -⟩ := Kinds.Head.Law.sv_at_yes _ _ _ _ s₀ s₁ rv gs hW hd₀
  obtain ⟨p, a, hp, hta, ex, -⟩ := hk
  obtain rfl : o₁ = p := Here.head.inj (ho₁.symm.trans hp)
  have hax : a.x = some xh := ex.trans hx₁
  -- the merge's mark is silent; the rounds' drawn values fit
  have hmk : headMergeMark (_root_.K11.parOf Zp Bs.G₀) ∈ ms := hsub1 _ (by
    rw [P1K8.part1Marks_eq]
    exact List.mem_append_right _ (List.mem_singleton.2 rfl))
  have hs : (headMergeMark (_root_.K11.parOf Zp Bs.G₀)).test
      ([] ++ fr.take ((cF.blocksInOrder.take 346).flatMap (·.rounds)).length) (Rt.map (·.drawn)) = none :=
    mark_silent hmk (by
      rw [P1K8.merge_place h.scope h.reads O]
      show (markOf ms IM.k11Place ([] ++ fr.take ((cF.blocksInOrder.take 346).flatMap (·.rounds)).length)
        (Rt.map (·.drawn))).isSome = false
      rw [show markOf ms IM.k11Place ([] ++ fr.take ((cF.blocksInOrder.take 346).flatMap (·.rounds)).length)
        (Rt.map (·.drawn)) = none from hsil]
      rfl)
  have hdf : drawsFit (headClaimMergeKind (_root_.K11.parOf Zp Bs.G₀)).rounds (Rt.map (·.drawn)) = true :=
    P1K8.fit_at_silent _ (hfit _ (inA (by omega) f346)) hsil
  have hne : ∀ e ∈ laterDraws (Rt.map noDigest), Reading.gl.val e ≠ 0 := by
    rw [laterDrawsNoDigest Rt]
    exact headMergeMarkSilent _ _ Rt hs (headMergeLaterFit _ Rt hdf)
  have hML := mergeLiveBehindRaw Z D r Zp Np cF x Bs zp tj s' a xh name IM.k11Place (Rt.map noDigest) _ h hB hrj d
    hta hax hne
  -- the member leaves what the head heard
  have hFL := Kinds.Head.Law.Five.five_decide_frontLater h.scope h.reads O (P1K2.flat_planOk O h.laid.planOk)
    (i := 346) (by omega) (by omega) f346 tj _ _ s' d
  obtain ⟨a', wo, c, hsa, -⟩ := id hML
  have e6 : LinkJoin.frontSix s' = LinkJoin.frontSix tj := hFL.1
  unfold LinkJoin.frontSix at e6
  simp only [hsa, hta] at e6
  have ex' : a'.x = a.x := congrArg Prod.fst (Option.some.inj (congrArg Prod.fst e6))
  exact ⟨a', xh, hsa, ex'.trans hax, hML⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.mergeLive_handed
