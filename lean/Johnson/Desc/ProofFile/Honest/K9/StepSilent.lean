-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/StepSilent.lean: THE SUB-PROTOCOL WITHOUT A ROUND BEHIND A SEGMENT's BATCHING ACCEPTS ONLY WHERE THE FIRST CHAIN's FALLS AT ITS
PLACE ARE SILENT. At each of the 25 segments, under the library's hypothesis `AtMgA`: if the block at 14 l + `IM.nAt l` + 3 steps from s,
then the list `fallsHead` (Honest/Law/FallsHead.lean) says nothing at that number at s. It is the premise htst of `owesS_firstThread`
(Honest/Thread/FirstThreadOwes.lean), to the letter, at the first thread's own list of falls.

Why. Two records of the list stand at that place: this kind's "a slot that must be free is not" and the smallness test's share (seven of
that test's own conditions). Both are conditions that the block's own run asks: where one speaks, the run refuses.

  `share_silent_at_link`   at a link with the library's `K8At`: a yes of `Link.runBehind` from sB ⊢ `K8.k8Share p.nU sB = none`: the run's last
                           part is the smallness test's three tests in a row (`sits_tests`), whose yes says that the seven are silent
                           (`K8.share_of_tests`); the runs in front leave what the seven read (`K8.share_lsTail`; the record and the ledger)
  `share_silent`           that at each of the 25 segments, at an opening in the goals' scope
  `falls_at_behind`        which records of `fallsHead` stand at the place behind the batching of segment l: these two, at l
  **`step_silent`**         the theorem, at `fallsHead Zp Bs.G₀ …`, the five stated numbers variables
  **`step_silent_first`**   the premise htst of `owesS_firstThread`, at `firstFalls A n` and the head at a return

Limits. It says nothing on what the two records cost in measure, nor that the block steps at any state. This file proves no property of a
prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.EqFormFits
import Johnson.Desc.ProofFile.Honest.K9.XkAtHead
import Johnson.Desc.ProofFile.Honest.K8.TestsSplitIff
import Johnson.Desc.ProofFile.Honest.K8.ShareLaid
import Johnson.Desc.ProofFile.Honest.Law.FallsHead
import Johnson.Desc.ProofFile.Honest.Law.FallSilent
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open Inst.Model
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Claim claimsInBy afterIn)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open Johnson.AtFull.Shape (LeavesLedger)
open ProofFile (Cl)
open IM
open TocK8 (K8At afterIn_of_behind k08_scope ixOf preOf postOf midOf)
open ProofFile.Honest.K8 (k8Share share_at share_lsTail share_of_tests)

/-- At a link with the library's `K8At`: where the step behind the batching accepts, the smallness test's share is silent in front. -/
theorem share_silent_at_link {Lk : Link S Cl} {p : VerifiableInference.Desc.First.K8.ParW} {i : ℕ}
    {pre post mid : List (ℕ × String)} (K : K8At Lk p i pre post mid)
    (hF : ∀ o ∈ mid, LeavesLedger Lk.hear o) (sB sE : S) (h2 : Lk.runBehind sB = .ok sE) :
    k8Share p.nU sB = none := by
  have ha := afterIn_of_behind h2
  rw [K.after] at ha
  obtain ⟨rL', s₁, hlL, hrL, ha'⟩ := afterIn_cons ha
  obtain ⟨s₂, -, hkeep, ha''⟩ :=
    afterIn_keeps (fun s : S => (k8Field s, s.fork?)) mid [(i, "K8.tests")] s₁ sE
      (fun o ho run hl e e₁ hr =>
        Prod.ext (K.hmid o ho run hl e e₁ hr) (hF o ho run hl e e₁ hr)) ha'
  obtain ⟨rT', s₃, hlT, hrT, -⟩ := afterIn_cons ha''
  obtain ⟨rL, mL, uL⟩ := K.hL rL' hlL
  obtain ⟨rT, mT, uT⟩ := K.hT rT' hlT
  obtain ⟨q₂, Fc, hq₂, ht, -⟩ := (sits_tests p rT mT s₂ _).1 (uT _ _ hrT)
  obtain ⟨d1, d2, -⟩ := partOf_some.1 hq₂
  obtain ⟨k1, k2⟩ := Prod.mk.inj hkeep
  have k1' : s₂.tl? = s₁.tl? := congrArg Prod.fst k1
  obtain ⟨f1, f2, -⟩ := share_of_tests ht
  rw [← share_lsTail p.nU p rL mL sB s₁ (uL _ _ hrL), share_at p.nU (k1'.symm.trans d1) (k2.symm.trans d2), f1, f2]
  rfl

/-- At each of the 25 segments, in the goals' scope, at an opening. -/
theorem share_silent {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25) (Lk : Link S Cl)
    (hLk : c.links[l]? = some Lk) {Xl : OnBytes.Model.Stages.LinkH} (hX : Bs.G₀.built[l]? = some Xl) (sB sE : S)
    (h2 : Lk.runBehind sB = .ok sE) : k8Share (ProofFile.k8ParW Z Bs.G₀ Xl l).nU sB = none := by
  obtain ⟨Lk', Xl', e, eX, K, -⟩ := k08_scope hS hR O l hl
  obtain rfl : Lk' = Lk := Option.some.inj (e.symm.trans hLk)
  obtain rfl : Xl' = Xl := Option.some.inj (eX.symm.trans hX)
  have hLL : ∀ o ∈ midOf (subAt l), LeavesLedger Lk'.hear o := by
    intro o ho run hlk e₀ e₁ hr
    by_cases h24 : l = 24
    · subst h24
      exact nomatch ho
    · by_cases he : l % 2 = 0
      · have ej : 2 * (l / 2) = l := by omega
        have hs : subAt l = .layers := by
          rw [← ej]
          exact subAt_layers (l / 2) (by omega)
        rw [hs] at ho
        obtain rfl := List.mem_singleton.1 ho
        obtain ⟨L4, b4, x, e4, hb4, -, la4, -⟩ := k4_of hS hR O (l / 2) (by omega)
        rw [ej] at e4
        obtain rfl : Lk' = L4 := Option.some.inj (e.symm.trans e4)
        rw [show ((2, "free-slot") : ℕ × String).1 = 2 from rfl, hb4] at hlk
        obtain ⟨r', hl', -, hy⟩ := after_yes la4 hlk
        exact (freeSlot_field (p := { x.2 with k3Runs := true }) hl' ((hy e₀ e₁).1 hr).1).2
      · have ej : 2 * (l / 2) + 1 = l := by omega
        have hs : subAt l = .attention := by
          rw [← ej]
          exact subAt_attention (l / 2)
        rw [hs] at ho
        exact nomatch ho
  exact share_silent_at_link K hLL sB sE h2

/-- **Which records of the list stand at the place behind a batching.** a: a place of the kind "frame" in segment l. -/
theorem falls_at_behind {Zp : ProofFile.Pub} {G₀ : ProofFile.Ground} {cols tau : ℕ → ℕ} {share notGood : ℕ → Odds} {r0 : ℕ → ℕ}
    {f : Fall S} (hf : f ∈ fallsHead Zp G₀ cols tau share notGood r0) {a : Place} (hk : a.kind = KindName.frame) {l : ℕ}
    (hlink : a.link = some l) (hp : f.place = a) :
    (∃ p u, IM.k9At Zp l = some p ∧ VerifiableInference.Desc.K9.testsWhere Zp.p.X l 0 = some u ∧
        f = quietFall p u.2.2.filled (u.2.1 - 1) (notGood l)) ∨
      ∃ Xl, G₀.built[l]? = some Xl ∧ f = K8.k8ShareFall l (oAt l) (ProofFile.k8ParW Zp G₀ Xl l).nU (share l) := by
  unfold fallsHead at hf
  rcases List.mem_append.1 hf with hf | hf
  · obtain ⟨l', -, hf⟩ := List.mem_flatMap.1 hf
    unfold linkFalls at hf
    rcases List.mem_append.1 hf with hf | hf
    · rcases List.mem_append.1 hf with hf | hf
      · obtain rfl := List.mem_singleton.1 hf
        have e : KindName.K9 = KindName.frame := (congrArg Place.kind hp).trans hk
        exact absurd e (by decide)
      · cases h9 : IM.k9At Zp l' with
        | none => rw [h9] at hf; exact absurd hf (List.not_mem_nil)
        | some p =>
          cases hu : VerifiableInference.Desc.K9.testsWhere Zp.p.X l' 0 with
          | none => rw [h9, hu] at hf; exact absurd hf (List.not_mem_nil)
          | some u =>
            rw [h9, hu] at hf
            obtain rfl := List.mem_singleton.1 hf
            obtain ⟨-, e2, -⟩ := IM.k9Where_fields h9
            have e : some p.link = some l := (congrArg Place.link hp).trans hlink
            obtain rfl : l' = l := by
              have := Option.some.inj e
              omega
            exact Or.inl ⟨p, u, h9, hu, rfl⟩
    · cases hX : G₀.built[l']? with
      | none => rw [hX] at hf; exact absurd hf (List.not_mem_nil)
      | some Xl =>
        rw [hX] at hf
        obtain rfl := List.mem_singleton.1 hf
        have e : some l' = some l := (congrArg Place.link hp).trans hlink
        obtain rfl : l' = l := Option.some.inj e
        exact Or.inr ⟨Xl, hX, rfl⟩
  · obtain ⟨g, -, hg⟩ := List.mem_filterMap.1 hf
    obtain ⟨hpl, -, rfl⟩ := Option.map_eq_some_iff.1 hg
    have e : KindName.K4 = KindName.frame := (congrArg Place.kind hp).trans hk
    exact absurd e (by decide)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The step behind the batching accepts only where the list of falls is silent at its number.** -/
theorem step_silent (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (cols tau : ℕ → ℕ) (share notGood : ℕ → Odds)
    (r0 : ℕ → ℕ) {l : ℕ} (hl : l < 25) {blk : Block S ProofFile.Cl} (hblk : cF.blocksInOrder[14 * l + IM.nAt l + 3]? = some blk)
    {s s' : S} {rs : List Fmt.RoundView} {cols' : List VerifiableInference.Desc.OpenedColumn} {n : ℕ}
    (hstep : blk.step 0 s rs cols' = .ok (s', n)) :
    fallsBy (fallsHead Zp Bs.G₀ cols tau share notGood r0) cF.blocksInOrder (14 * l + IM.nAt l + 3) s [] = none := by
  obtain ⟨Lk, p, w, Qc, bE, bS, Sd, -⟩ := seats_at_head h hl
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  obtain ⟨b, hb, hp, hdec⟩ := Sd.behind
  obtain rfl : b = blk := Option.some.inj (hb.symm.trans hblk)
  obtain ⟨rs', gs', hd⟩ := Johnson.Desc.First.Walk.Tied.stepYes_decide (IM.yes_stepYes ⟨rs, cols', n, hstep⟩)
  have hrun : Lk.runBehind s = .ok s' := (hdec s rs' gs').symm.trans hd
  obtain ⟨-, e2, -⟩ := IM.k9Where_fields Sd.numbers
  unfold fallsBy
  rw [hblk]
  refine (fallOf_silent_iff _ _ _ _).2 fun f hf hpl => ?_
  rcases falls_at_behind hf (a := b.place) (l := l) (by rw [hp]; rfl) (by rw [hp]; show some p.link = some l; rw [e2]) hpl
    with ⟨p', u, h9, hu, rfl⟩ | ⟨Xl, hX, rfl⟩
  · obtain rfl : w = u := Option.some.inj (Sd.tested.symm.trans hu)
    show freeSlotShare w.2.2.filled s = none
    cases hq : freeSlotShare w.2.2.filled s with
    | none => rfl
    | some m => exact absurd hrun (Sd.refuses s (by rw [hq]; rfl) s')
  · exact share_silent h.scope h.reads O l hl Lk Sd.link hX s s' hrun

open ProofFile.Honest.FirstThread in
/-- **The premise htst of `owesS_firstThread`.** -/
theorem step_silent_first {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : HeadAtReturn files A) (nums : FallNumbers) :
    ∀ l, l < 25 → ∀ blk, h.firstChain.blocksInOrder[14 * l + IM.nAt l + 3]? = some blk →
      ∀ s rs cols s' n, blk.step 0 s rs cols = .ok (s', n) →
        fallsAfterBatching (firstFalls A nums) h.firstChain l s = none := by
  intro l hl blk hblk s rs cols s' n hstep
  obtain ⟨Bs, base, O⟩ := h.head.laid.opened
  have e := step_silent h.head O.made nums.columns nums.tau nums.share nums.notGood nums.roundsBefore hl hblk hstep
  unfold fallsAfterBatching firstFalls
  rw [seatGround_of_base O.made]
  exact e

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.share_silent_at_link
#print axioms ProofFile.Honest.K9.share_silent
#print axioms ProofFile.Honest.K9.falls_at_behind
#print axioms ProofFile.Honest.K9.step_silent
#print axioms ProofFile.Honest.K9.step_silent_first
