-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/BatchStays.lean: THE PREMISE `stays` OF `PileWalk`
(Johnson/Desc/K13/Honest/PileInduction.lean) AT THE FIRST CHAIN OF THE PROOF FILE's IOP AS WRITTEN
IN LEAN: SHOWN AT THE BATCHING, AT EVERY SITE, UNDER THE LIBRARY's ONE HYPOTHESIS AT THE FULL SIZE;
SO, UNDER THAT HYPOTHESIS, THE WHOLE PREMISE hfive HOLDS. Statements with their proofs: calls.

THE ARGUMENT. A reader that K9 writes beside, and that each run of the segment's order keeps, is
left by the batching; each run keeps a reader that rests under the library's four writings.
ALL THAT IS CALLED IS THE LIBRARY's: `K9.batch_keeps` (Johnson/Desc/First/Batch/Law/Keeps.lean),
`TailClaims.Law.claimsInBy_keeps` (Johnson/Desc/First/TailClaims/K8SitsFront.lean), `run_layers`,
`run_head`, `runRests_of_rel` (Johnson/Desc/First/Link/Law/RunRel.lean), `relRests_of_field`
(LinkAtSort.lean), `take_of_layersOwesC`, `take_of_headOwesC` (LinkRestAtSort4C.lean),
`LPFK9.layersOwesC_whole` (Johnson/LPFK9R/LayersOwesWhole.lean), `LPFK9.headOwesC_24`
(LPFK9R/OwesAtLetters.lean), `rests_rest9`, `ReadsRest9.alike` (Rest9.lean). The ties to the chain's
own numbers: `LPFK9.k09_sits` (LPFK9R/Sits.lean: the segment; its two orders; the library's
`DrawMoves` of its batching; K9's numbers), `K1.hlk_atAll`
(Johnson/Desc/K1/Law/LinksQuietAtAll.lean), `IM.k9_of`, `IM.frame_of`, `IM.yes_alone`.
Main names. Under h : `P5J.AtMgA`:
  `fieldRests_of_reads`: a reader with the library's `ReadsRest9` has its `FieldRests`. No premise.
  `batch_keeps_of_runs`: from "each run of the segment's order keeps f" and `K9.Beside f` to the
    decision of number 14 m + `IM.nAt` m + 2.
  `batch_keeps_lay`, `batch_keeps_head24`: **the batching of a layers' segment, and of the head's,
    leaves every f with `K9.Beside f` and `FieldRests f`.**
  `stays_batch_head`: **so at every site of `sitesAt cF Zp` every decision of number c − 5 leaves
    what the site's reader reads.** At every state.
  `hfive_at_head`: **THE PREMISE hfive, WHOLE, at any start**: with `hfive_of_one_head`
    (BehindStays.lean of this folder).

What is not claimed. That h holds at any public files. Nothing at an attention's segment. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.BehindStays
import Johnson.LPFK9R.Sits
import Johnson.LPFK9R.LayersOwesWhole
import Johnson.LPFK9R.OwesAtLetters
import Johnson.Desc.First.Link.Law.LinkRestAtSort4C
import Johnson.Desc.First.Link.Law.RunRel
import Johnson.Desc.First.Link.Law.LinkAtSort
import Johnson.Desc.First.Link.Law.KeepsAny
import Johnson.Desc.First.TailClaims.K8SitsFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K13

open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.First.Close (leftHead)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.K13.Honest (PileSite FoldReaches)
open Johnson.Desc.First.Walk (leftLay)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-- A reader with the library's `ReadsRest9` rests under the library's four writings. -/
theorem fieldRests_of_reads {γ : Type} {f : S → γ} (hf : ∀ L₀ F₀ t₀, ReadsRest9 L₀ F₀ t₀ f) :
    FieldRests f where
  tl s tl := ReadsRest9.alike { check := s.check } {} {} (hf _ _ _) ((rests_rest9 _ _ _).tl s tl)
  fork s G := ReadsRest9.alike { check := s.check } {} {} (hf _ _ _) ((rests_rest9 _ _ _).fork s G)
  wrote e a G e₁ hw :=
    ReadsRest9.alike { check := e.check } {} {} (hf _ _ _) ((rests_rest9 _ _ _).wrote e a G e₁ hw)
  head s a G ha :=
    ReadsRest9.alike { check := s.check } {} {} (hf _ _ _) ((rests_rest9 _ _ _).head s a G ha)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- From "each run of the segment's order keeps f" to the batching's decision, by its number. -/
theorem batch_keeps_of_runs (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {γ : Type} {f : S → γ}
    (hB : Desc.K9.Beside f) (m : ℕ) (hm : m < 25)
    (hrun : ∀ Lk, cF.links[m]? = some Lk → ∀ o ∈ Lk.order, ∀ run, At Lk o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → f e₁ = f e)
    (blk : Block S ProofFile.Cl) (hb : cF.blocksInOrder[14 * m + IM.nAt m + 2]? = some blk) (s t : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (hd : blk.decide s rs gs = .ok t) :
    f t = f s := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, fs, hfs, hall⟩ := IM.frame_of h.scope h.reads O
  obtain ⟨Lk, _, _, _, _, e1, hn, _⟩ := hall m hm
  have hn' : Lk.hear.length = IM.nAt m := hn
  obtain ⟨Lk9, p, _, _, e9, _, _, _, _, _, hal, i9, _⟩ := (IM.k9_of h.scope h.reads O).2 m hm
  obtain rfl : Lk = Lk9 := Option.some.inj (e1.symm.trans e9)
  rw [hn'] at i9
  obtain rfl := Option.some.inj (i9.symm.trans hb)
  have y := ((IM.yes_alone (hal _) (by unfold IM.a9Of; intro q; cases q) s t rs gs).1 hd).1
  exact Desc.K9.batch_keeps hB p _
    (fun t' y' hy => TailClaims.Law.claimsInBy_keeps f Lk.order t' y' (hrun Lk e1) hy) y

/-- **THE BATCHING OF A LAYERS' SEGMENT, BY NUMBER.** -/
theorem batch_keeps_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {γ : Type} {f : S → γ}
    (hB : Desc.K9.Beside f) (hR : FieldRests f) (m : ℕ) (hm : m < 25)
    (hs : IM.subAt m = .layers) (blk : Block S ProofFile.Cl)
    (hb : cF.blocksInOrder[14 * m + IM.nAt m + 2]? = some blk) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : blk.decide s rs gs = .ok t) : f t = f s := by
  refine batch_keeps_of_runs h hB m hm ?_ blk hb s t rs gs hd
  intro Lk e1
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk', p, Q, kp, -, St⟩ := LPFK9.k09_sits h.scope h.reads O m hm
  obtain rfl : Lk' = Lk := Option.some.inj (St.link.symm.trans e1)
  have hlk : h.𝔇.lk m = some Lk' := (VerifiableInference.Desc.K1.hlk_atAll h m hm).trans e1
  have seg : SegAt m (IM.subAt m) Lk' := ⟨St.order, St.orderAfter, St.hear⟩
  obtain ⟨p4, X, -, -, Wh⟩ := LPFK9.layersOwesC_whole h O m hm hs Lk' p hlk seg St.draw kp
  have OW := Wh (fun _ => False) 0 0 0 0 (fun _ _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) {} {}
    fun _ hq => hq.elim
  exact (run_layers (runRests_of_rel (relRests_of_field hR)) OW.seg (take_of_layersOwesC OW)
    fun o ho run hh n e c e₁ hx => by
      obtain ⟨G, rfl⟩ := OW.k3p o ho run hh n e c e₁ hx
      exact hR.fork e G).1

/-- **THE BATCHING OF THE HEAD's SEGMENT, BY NUMBER.** -/
theorem batch_keeps_head24 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {γ : Type} {f : S → γ}
    (hB : Desc.K9.Beside f) (hR : FieldRests f) (blk : Block S ProofFile.Cl)
    (hb : cF.blocksInOrder[14 * 24 + IM.nAt 24 + 2]? = some blk) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : blk.decide s rs gs = .ok t) : f t = f s := by
  refine batch_keeps_of_runs h hB 24 (by decide) ?_ blk hb s t rs gs hd
  intro Lk e1
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk', p, Q, kp, -, St⟩ := LPFK9.k09_sits h.scope h.reads O 24 (by decide)
  obtain rfl : Lk' = Lk := Option.some.inj (St.link.symm.trans e1)
  have hlk : h.𝔇.lk 24 = some Lk' :=
    (VerifiableInference.Desc.K1.hlk_atAll h 24 (by decide)).trans e1
  have seg : SegAt 24 (IM.subAt 24) Lk' := ⟨St.order, St.orderAfter, St.hear⟩
  obtain ⟨X, -, Wh⟩ := LPFK9.headOwesC_24 h O rfl Lk' p hlk seg St.draw kp
  have OW := Wh (fun _ => False) (((placeAt (P5J.At.X Zp) 24 false).map (·.lm)).getD 0) 0 0 0
    (fun _ _ _ => 0) {} {} (fun _ hq => hq.elim) (fun _ hq => hq.elim) fun pl e => by rw [e]; rfl
  exact (run_head (runRests_of_rel (relRests_of_field hR)) OW.seg (take_of_headOwesC OW)
    fun o ho run hh n e c e₁ hx => by
      obtain ⟨G, rfl⟩ := OW.k3p o ho run hh n e c e₁ hx
      exact hR.fork e G).1

/-- **`stays` AT THE NUMBER c − 5 OF EVERY SITE.** -/
theorem stays_batch_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (σ : PileSite)
    (hσ : σ ∈ sitesAt cF Zp) (k : ℕ) (hk : k + 5 = σ.c) (blk : Block S ProofFile.Cl)
    (hb : cF.blocksInOrder[k]? = some blk) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hd : blk.decide s rs gs = .ok t) :
    σ.left t = σ.left s := by
  rcases mem_sitesAt.1 hσ with ⟨g, hg, rfl⟩ | rfl
  · have a1 : k + 5 = 28 * g + 14 := hk
    have hn : IM.nAt (2 * g) = 7 := by
      unfold IM.nAt
      rw [if_neg (by omega)]
    have e : k = 14 * (2 * g) + IM.nAt (2 * g) + 2 := by omega
    rw [e] at hb
    have hs : IM.subAt (2 * g) = .layers := by
      unfold IM.subAt
      rw [if_neg (by omega), if_pos (by omega)]
    exact batch_keeps_lay h beside_leftLay (fieldRests_of_reads readsRest9_leftLay) (2 * g)
      (by omega) hs blk hb s t rs gs hd
  · have a1 : k + 5 = 352 := hk
    have hn : IM.nAt 24 = 9 := rfl
    have e : k = 14 * 24 + IM.nAt 24 + 2 := by omega
    rw [e] at hb
    exact batch_keeps_head24 h beside_leftHead (fieldRests_of_reads readsRest9_leftHead) blk hb s t
      rs gs hd

/-- **SO, UNDER h, THE PREMISE hfive HOLDS**: at any start. -/
theorem hfive_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Xi : Type} (start : Xi → S) :
    ∀ σ ∈ sitesAt cF Zp, ∀ k blk, σ.c ≤ k + 5 → k < σ.c → cF.blocksInOrder[k]? = some blk →
      ∀ x rs cols s cl, FoldReaches cF.blocksInOrder start k x rs cols s cl →
      ∀ R gs t, blk.decide s R gs = .ok t → σ.left t = σ.left s :=
  hfive_of_one_head h start fun σ hσ k blk hk hb _ _ _ s _ _ R gs t hd =>
    stays_batch_head h σ hσ k hk blk hb s t R gs hd

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.fieldRests_of_reads
#print axioms ProofFile.Honest.K13.batch_keeps_of_runs
#print axioms ProofFile.Honest.K13.batch_keeps_lay
#print axioms ProofFile.Honest.K13.batch_keeps_head24
#print axioms ProofFile.Honest.K13.stays_batch_head
#print axioms ProofFile.Honest.K13.hfive_at_head
