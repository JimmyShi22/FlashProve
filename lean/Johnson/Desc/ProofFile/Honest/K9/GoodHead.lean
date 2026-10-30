-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/GoodHead.lean: "GOOD" (`goodW`, Honest/K9/GateArms.lean) IN FRONT OF THE BATCHING OF
THE HEAD's SEGMENT, UNDER THE LIBRARY's HEAD AND K9's SEAT: K11's CLAUSE JOINED; what is still owed gathered in ONE
NAMED STRUCTURE. Statements and proofs ON THE VERIFIER's TEXT; no prover is in this file, and no goal is stated. No
probability is in this file. `goodW_of_inv` wants ONE predicate I on states for the whole order (eleven runs). Here I
:= K11's clause ∧ J: K11's clause is its house's `MergeLive lk first sv` (Johnson/Desc/K11/Live/RunStatement.lean); J
stands inside the structure.
  `mergeLive_congr`   `MergeLive` reads of a state the head's own three (`headOf`, Honest/K9/KeepsPaid.lean) alone
  `draw_headOf`   K9's draw leaves these three
  `HeadLive L p lk first sv n s`   **WHAT IS STILL OWED, AS ONE STRUCTURE**: a predicate J on states with: it holds
      behind K9's draw from s; every run of the order hands it on; every slot below n that is neither sv, nor in K11's
      window [first, first + 2 lk + 2), nor the merge's slot first + 2 lk + 2, is live in some run's claims; K6's
      three runs and "join" make claims that are plain at every slot; and the eight runs that are neither idle nor the
      merge's name the merge's slot in no claim (each clause may spend K11's `MergeLive` too)
  **`goodW_head`**   from the head, `SeatedFree` at 24, `MergeLive lk first sv s` AT THE STATE IN FRONT OF THE
      BATCHING and `HeadLive`: `goodW p ‹the segment's gatherer› s n`, AT EVERY n
WHAT IS PAID HERE: start and hand for K11's clause, at the draw and at all eleven runs, whosever (by
`fieldRun_head_at`, Honest/K9/KeepsAtHead.lean, at `rests_headOf`): so no kind need carry K11's clause · the merge's
slot (K11's `mergeLiveSlot`) · live at sv and on K11's window (`mergeRunLiveStart`, `mergeRunLive`) · plain at seven
of the eleven runs: the merge's (`mergeRunPlain`), "K8.equations", both "objects", "planes" (by
Honest/K9/GoodAttSeat.lean's `equations_plain`, `objects_plain`, `planes_plain`), the two idle ones · unnamed at the
merge's own run (`mergeRunUnnamed`) and the two idle ones. The ties between the description's runs and the kinds'
texts are the library's: `HeadTies`, `at_objects_is`, `at_planes_is`.
WHAT IS NOT CLAIMED. `MergeLive` at any state (had from its mark's silence, under premises). `HeadLive` AT
ANY STATE: IT MAY BE UNMEETABLE: it is shown met at no state. J IS ONE FOR K6's, THE LOOKUPS' AND K8's CLAUSES: each is
to be handed on by ALL ELEVEN runs, whosever: who carries whose, and the cut to fixed readings, as
Honest/K9/GoodAttLook.lean has it at attention: Honest/K9/GoodHeadLook.lean and GoodHeadWrap.lean, not here. `MergeLive`
asks that its challenges read other than 0: where one is 0 this theorem says nothing. `HeadLive`'s fourth clause asks
"plain" at every slot: more than `goodW_of_inv` takes. That the windows cover the slots below the public number (n is
free: no law here says that the seat's number at 24 is the head's plan's), or that lk, first, sv are the plan's. u and
kk are letters; u is read by nothing in the conclusion. No member. `HeadLive` is named by Honest/K9/GoodHeadLook.lean
and GoodHeadWrap.lean; `goodW_head` is called by GoodHeadWrap.lean alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.GoodAttSeat
import Johnson.Desc.K11.Live.Run

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open Johnson.Desc.First.ForkMerge.Live (MergeLive mergeRunLive mergeRunLiveStart mergeRunPlain mergeRunUnnamed
  mergeLiveSlot)

/-- K11's clause reads of a state the head's own three alone. -/
theorem mergeLive_congr {lk first sv : ℕ} {u u' : S} (e : headOf u' = headOf u) (h : MergeLive lk first sv u) :
    MergeLive lk first sv u' := by
  obtain ⟨a, wo, c, ha, hw, rest⟩ := h
  unfold headOf at e
  rw [ha] at e
  cases hu : u'.here with
  | head a' =>
    rw [hu] at e
    have e3 : a'.wo = a.wo := congrArg (fun x => x.2.2) (Option.some.inj e)
    exact ⟨a', wo, c, hu, e3.trans hw, rest⟩
  | _ =>
    rw [hu] at e
    exact nomatch e

/-- K9's draw leaves the head's own three. -/
theorem draw_headOf (p : Desc.K9.Where) (s t₁ : S) (x : E)
    (h : (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne x⟩] [] = .ok t₁) :
    headOf t₁ = headOf s := by
  obtain ⟨a, ha⟩ := draw_open p s t₁ x h
  rw [draw_is p s t₁ x a ha h, set_headOf]

/-- **What is still owed in front of the head's segment's batching.** -/
structure HeadLive (L : Link S ProofFile.Cl) (p : Desc.K9.Where) (lk first sv n : ℕ) (s : S) : Prop where
  owed : ∃ J : S → Prop,
    (∀ y t₁, (Desc.K9.drawAlone (Cl := Claim) Desc.K9.atS p).decide s [⟨[], drawnOne y⟩] [] = .ok t₁ → J t₁) ∧
    (∀ o ∈ L.order, ∀ run, At L o run → ∀ m t z, MergeLive lk first sv t → J t → run m t = .ok z → J z.2) ∧
    (∀ j < n, j ≠ sv → (j < first ∨ first + 2 * lk + 2 < j) → ∃ o ∈ L.order, ∀ run, At L o run →
      ∀ m t z, MergeLive lk first sv t → J t → run m t = .ok z → Desc.K9H.liveAt z.1 j = true) ∧
    (∀ o ∈ [(3, "norm"), (3, "join"), (3, "policy"), (3, "logits")], ∀ run, At L o run →
      ∀ m t z, MergeLive lk first sv t → J t → run m t = .ok z → ∀ j, Desc.K9H.plainAt z.1 j = true) ∧
    ∀ o ∈ [(2, "objects"), (3, "norm"), (3, "join"), (3, "policy"), (2, "planes"), (7, "objects"),
        (5, "K8.equations"), (3, "logits")], ∀ run, At L o run →
      ∀ m t z, MergeLive lk first sv t → J t → run m t = .ok z →
        Desc.K9H.unnamedAt z.1 (first + 2 * lk + 2) = true

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **"Good" in front of the head's segment's batching, under the head and K9's seat.** -/
theorem goodW_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {kk : ℕ} {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {w : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp 24 kk Lk p w)
    (u : HTailF2) {lk first sv : ℕ} (s : S) (n : ℕ) (hI : MergeLive lk first sv s)
    (hJ : HeadLive Lk p lk first sv n s) : goodW p (claimsInBy Lk.each Lk.hear Lk.order) s n := by
  have hm : 24 < 25 := by omega
  obtain ⟨hlk, seg, drawB, kp⟩ := tied_of_seated h hm Sd
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hs : IM.subAt 24 = .head := rfl
  obtain ⟨X, _, Wh⟩ := LPFK9.headOwesC_24 h O hs Lk p hlk seg drawB kp
  have T := (Wh (fun _ => False) (((First.Look.placeAt (P5J.At.X Zp) 24 false).map (·.lm)).getD 0) 0 0 0
    (fun _ _ _ => 0) u u (fun _ hq => hq.elim) (fun _ hq => hq.elim) fun pl e => by rw [e]; rfl).ties
  have ord : Lk.order = First.orderOf .head := by
    rw [← hs]
    exact seg.order
  obtain ⟨J, Js, Jh, Jl, Jp, Ju⟩ := hJ.owed
  have idle : ∀ i ∈ [2, 7], ∀ run, At Lk (i, "guests") run → ∀ m t z, run m t = .ok z → z.1 = [] := by
    intro i hi run hr m t z hz
    have e := T.tGuests i hi run hr m t z.1 z.2 hz
    exact (Prod.mk.inj (Except.ok.inj e)).1.symm
  refine goodW_of_inv p Lk.each Lk.hear Lk.order s n (some (first + 2 * lk + 2))
    (fun e => MergeLive lk first sv e ∧ J e) ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun y t₁ ht => ⟨mergeLive_congr (draw_headOf p s t₁ y ht) hI, Js y t₁ ht⟩
  · exact fun o ho run hr m t z hIt hz =>
      ⟨mergeLive_congr (fieldRun_head_at h O hs Lk p hlk seg drawB kp u rests_headOf o ho run hr m t z.1 z.2 hz)
        hIt.1, Jh o ho run hr m t z hIt.1 hIt.2 hz⟩
  · exact fun e he => mergeLiveSlot lk first sv e he.1
  · intro j hj hne
    have hne' : j ≠ first + 2 * lk + 2 := fun e => hne (congrArg some e.symm)
    by_cases h1 : j = sv
    · refine ⟨(8, "the merge"), by rw [ord]; decide, fun run hr m t z hIt hz => ?_⟩
      rw [h1]
      exact mergeRunLiveStart lk first sv m t z hIt.1 (T.tMerge run hr m t z.1 z.2 hz)
    · by_cases h2 : j < first ∨ first + 2 * lk + 2 < j
      · obtain ⟨o, ho, H⟩ := Jl j hj h1 h2
        exact ⟨o, ho, fun run hr m t z hIt hz => H run hr m t z hIt.1 hIt.2 hz⟩
      · refine ⟨(8, "the merge"), by rw [ord]; decide, fun run hr m t z hIt hz => ?_⟩
        exact mergeRunLive lk first sv m t z hIt.1 (T.tMerge run hr m t z.1 z.2 hz) j (by omega) (by omega)
  · intro j _ _ o ho
    rw [ord] at ho
    revert o
    refine (order_head fun o => ∀ run, claimsRunOf Lk.hear o = some run → ∀ m t z,
      (MergeLive lk first sv t ∧ J t) → run m t = .ok z → Desc.K9H.plainAt z.1 j = true).2
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro run hr m t z _ hz
      have e := OnPublicFiles.at_objects_is h.scope h.reads O hm false Sd.link (run := run) hr
      rw [e] at hz
      exact objects_plain _ (fun _ => rfl) hz j
    · intro run hr m t z _ hz
      rw [idle 2 (by simp) run hr m t z hz]
      rfl
    · exact fun run hr m t z hIt hz => Jp _ (by simp) run hr m t z hIt.1 hIt.2 hz j
    · exact fun run hr m t z hIt hz => Jp _ (by simp) run hr m t z hIt.1 hIt.2 hz j
    · exact fun run hr m t z hIt hz => Jp _ (by simp) run hr m t z hIt.1 hIt.2 hz j
    · intro run hr m t z _ hz
      obtain ⟨rd, hrd⟩ := OnPublicFiles.readers_of_at_planes h.scope h.reads O hm Sd.link (run := run) hr
      obtain ⟨pl, _, e⟩ := OnPublicFiles.at_planes_is h.scope h.reads O hm Sd.link hrd (run := run) hr
      rw [e] at hz
      exact planes_plain _ (fun _ => rfl) _ _ hz j
    · intro run hr m t z _ hz
      have e := OnPublicFiles.at_objects_is h.scope h.reads O hm true Sd.link (run := run) hr
      rw [e] at hz
      exact objects_plain _ (fun _ => rfl) hz j
    · intro run hr m t z _ hz
      rw [idle 7 (by simp) run hr m t z hz]
      rfl
    · exact fun run hr m t z _ hz => equations_plain (T.tEq run hr m t z.1 z.2 hz) j
    · exact fun run hr m t z hIt hz => Jp _ (by simp) run hr m t z hIt.1 hIt.2 hz j
    · exact fun run hr m t z _ hz => mergeRunPlain m t z (T.tMerge run hr m t z.1 z.2 hz) j
  · intro j _ hmj o ho
    obtain rfl : first + 2 * lk + 2 = j := Option.some.inj hmj
    rw [ord] at ho
    revert o
    refine (order_head fun o => ∀ run, claimsRunOf Lk.hear o = some run → ∀ m t z,
      (MergeLive lk first sv t ∧ J t) → run m t = .ok z →
        Desc.K9H.unnamedAt z.1 (first + 2 * lk + 2) = true).2
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun run hr m t z hIt hz => Ju _ (by simp) run hr m t z hIt.1 hIt.2 hz
    · intro run hr m t z _ hz
      rw [idle 2 (by simp) run hr m t z hz]
      rfl
    · exact fun run hr m t z hIt hz => Ju _ (by simp) run hr m t z hIt.1 hIt.2 hz
    · exact fun run hr m t z hIt hz => Ju _ (by simp) run hr m t z hIt.1 hIt.2 hz
    · exact fun run hr m t z hIt hz => Ju _ (by simp) run hr m t z hIt.1 hIt.2 hz
    · exact fun run hr m t z hIt hz => Ju _ (by simp) run hr m t z hIt.1 hIt.2 hz
    · exact fun run hr m t z hIt hz => Ju _ (by simp) run hr m t z hIt.1 hIt.2 hz
    · intro run hr m t z _ hz
      rw [idle 7 (by simp) run hr m t z hz]
      rfl
    · exact fun run hr m t z hIt hz => Ju _ (by simp) run hr m t z hIt.1 hIt.2 hz
    · exact fun run hr m t z hIt hz => Ju _ (by simp) run hr m t z hIt.1 hIt.2 hz
    · exact fun run hr m t z hIt hz =>
        mergeRunUnnamed lk first sv m t z hIt.1 (T.tMerge run hr m t z.1 z.2 hz)

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.mergeLive_congr
#print axioms ProofFile.Honest.K9.draw_headOf
#print axioms ProofFile.Honest.K9.goodW_head
