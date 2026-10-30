-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Behind/Promise.lean: the proofs of `RunsPassOfTests` and `PromiseBehindMerge`
(Johnson/Desc/K11/Behind/PromiseStatement.lean), to the letter, and one definition for the second
(`stringFree`). Lemmas; none of the library's goals.

How. The first: the lines of `runsPass_at_merge` (Johnson/Top/H0/MergeLaw/RunsPassAtMerge.lean)
behind its first two. The second: the library's second tie of the merge in general letters
(`merge_t2`, Johnson/Top/H0/MergeLaw/TieOneTwo.lean: general in the meaning) at the composed meaning
with its three sentences on oracle strings laid "true" (`stringFree`, here), at a frame without a
tree and the strings that hold nothing, the same in front and behind. Its premises as the library
pays them in `merge_t2_all` (SecondTieAt.lean), `merge_t2_full` (SecondTieFull.lean) and
`k11_law_atMg` (Johnson/K11R/LawAtMg.lean): "in order" rides · the public tests behind
(`merge_pubHeld_full`) from the eight that ride (`keep_at_merge_head`, at the first lemma), the row
(`MergeFront.hasRow`) and the merge's own run (`merge_makes_formsIn`) · what the items say
(`merge_hPP_all`) · "held" (`merge_hHeld_full`) · the closed facts on the two places. The promise at
that meaning is taken apart and put together by unfolding.

Limits. Those of the statements. Nothing on any property.
-/
import Johnson.Desc.K11.Behind.PromiseStatement
import Johnson.K11R.KindAtFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Desc.First.ForkMerge.Behind
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Link Claim Wit)
open VerifiableInference.Reads.Pass (Fwd)
open VerifiableInference.Desc.K9 (readersAt)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S HeadOwn Here Pub Meaning onAt samplesHeld pubHeld ledgerB
  freeAboveB pubRowM pubSets flatPlacesOf)
open VerifiableInference.Desc.First.Look (lookOutC)
open VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc.Kinds.Head.Law (Alike)
open VerifiableInference.Desc.Sound.MgAt (mergeAt behindAt k11_hp k11_hp' k11_hq k11_hst k11_hlk)
open P5J (AtMgA mgAtAll)

/-- **The eighteen, from the two tests.** -/
theorem runsPassOfTests : RunsPassOfTests := by
  intro Xi P Tok rows cols nR X D Pm l iU3 lm a b rs hlk H hy hled hout hsp hlen
  have L : NineLate (readersAt D.lk X (VerifiableInference.OnPublicFiles.headLink X) 24) Pm a :=
    nine_late hlk H D.pubD.d3 Pm hout hlen
  have V : FiveFwd (readersAt D.lk X (VerifiableInference.OnPublicFiles.headLink X) 24) a b :=
    five_fwd hlk H Pm hy hled hsp.join3
  have pl : Fwd (readersAt D.lk X (VerifiableInference.OnPublicFiles.headLink X) 24) 2 "planes" a b :=
    fwd_planes hlk H.planes2 D.pubD.d3 Pm hy hled hout hlen hsp.planes2
  obtain ⟨F0, hF0, hS⟩ := sized_of_ledgerB hled
  obtain ⟨x, x', hx, hx', rfl, hG, -, -, -⟩ := merge_forks Pm hy hF0
  have al : Alike a b := merge_alike Pm hy fun y hy' => by
    rw [hx] at hy'
    obtain rfl := Here.head.inj hy'
    exact hS
  have hrow : x'.F.trees.map (·.R) = x.F.trees.map (·.R) := by
    rw [merge_trees Pm hy hx hx' hS]
  exact
    { fwd_objects2 := V.fwd_objects2
      late_objects2 := L.late_objects2
      fwd_guests2 := V.fwd_guests2
      late_guests2 := L.late_guests2
      fwd_planes2 := pl
      late_planes2 := L.late_planes2
      fwd_join3 := V.fwd_join3
      late_join3 := L.late_join3
      fwd_norm3 := fwd_own hlk (by decide) H.norm3 al hF0 hG hrow hsp.norm3
      late_norm3 := L.late_norm3
      fwd_policy3 := fwd_own hlk (by decide) H.policy3 al hF0 hG hrow hsp.policy3
      late_policy3 := L.late_policy3
      fwd_logits3 := fwd_own hlk (by decide) H.logits3 al hF0 hG hrow hsp.logits3
      late_logits3 := L.late_logits3
      fwd_objects7 := V.fwd_objects7
      late_objects7 := L.late_objects7
      fwd_guests7 := V.fwd_guests7
      late_guests7 := L.late_guests7 }

/-- A meaning with its three sentences on oracle strings laid "true". -/
def stringFree {P W : Type} (Mg : Meaning P W) : Meaning P W :=
  { Mg with
    noColl := fun _ _ _ _ => True
    shown := fun _ _ _ => True
    decodes := fun _ _ => True }

set_option maxRecDepth 100000 in
/-- **The four behind the decision's yes.** -/
theorem promiseBehindMerge : PromiseBehindMerge := by
  intro Z D r Zp Np cF x h Bs Lk xM R ni z s s' rs hmade hLk hy F hsp hlen hf hx hHeld hPP
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hmade)
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some Bs'.G₀ := (IM.base_made O.made).2.2.1
  have tn := LT28.K11Tests.numsB_head_of_public h.scope h.reads h.laid.pub h.pubOne
    (Nat.pow_right_injective (le_refl 2) (h.cols13.trans (by decide +kernel)))
  have tc := LT28.K11Tests.nclB_head_of_public h.scope h.reads h.laid.pub h.pubOne
  obtain ⟨c1, c2, c3, c4, c5⟩ := IM.xk_parts hx
  unfold P1K2.EQ at c5
  rw [Bool.and_eq_true] at c5
  obtain ⟨cIn, cPub⟩ := c5
  -- the public tests in front
  have hall := List.all_eq_true.1 (by unfold pubHeld at cPub; exact cPub)
  obtain ⟨_, _, _, k4, k5, _⟩ := k11_six h.𝔇 mgBase rfl rfl
  have e1 : ledgerB s = true := hall _ (List.mem_append_left _ k4)
  have e2 : ((h.𝔇.pubD.nsOf 24).any fun n => freeAboveB n s) = true :=
    hall _ (List.mem_append_left _ k5)
  have e2' : freeAboveB (K11.parOf Zp Bs'.G₀).nMsg s = true := by
    have : h.𝔇.pubD.nsOf 24 = some (K11.parOf Zp Bs'.G₀).nMsg := (nums_of_test hG tn).1
    rw [this] at e2
    exact e2
  have hH : VerifiableInference.OnPublicFiles.headLink (P5J.At.X Zp) = 24 := by
    obtain ⟨p4, ng, -⟩ := Meaning.scope_plans h.scope h.reads h.pubOne
    unfold VerifiableInference.OnPublicFiles.headLink
    rw [p4, ng]
    rfl
  have hout : lookOutC h.𝔇.pubD.d3 24 false s = true := by
    have h1 : (mgAll h.𝔇 mgBase).pub (.lookOut 24 3) (z, s) = true :=
      hall (Pub.lookOut 24 3)
        (k11_hIn h.𝔇 mgBase rfl (Pub.lookOut 24 3) (List.mem_append_right _ (by simp [keep24])))
    rw [mgAll_pub, VerifiableInference.Desc.First.pubAll_lookOut h.𝔇.pubD mgBase.pub 24 3 false
      (sorts_at_head hH).1] at h1
    exact h1
  obtain ⟨Lk', iU3, lm, hLk', -, -, HR⟩ := runsAre_at_link24 h.scope h.reads O
  obtain rfl : Lk' = Lk := Option.some.inj (hLk'.symm.trans hLk)
  have hlk24 : h.𝔇.lk 24 = some Lk' := (ToldDesc.linkAt_of_open O 24).trans hLk
  have HR' : RunsAre Lk' (P5J.At.X Zp) iU3 lm := by
    have e := HR
    rw [O.W] at e
    exact e
  have hruns := runsPassOfTests _ _ _ _ _ _ _ h.𝔇 (K11.parOf Zp Bs'.G₀) Lk' iU3 lm s s' rs hlk24 HR'
    hy e1 hout hsp hlen
  have hkeep := keep_at_merge_head h.𝔇 mgBase rfl hH (K11.parOf Zp Bs'.G₀) z hy e1 e2' hruns
  have hfr : frontR (K11.parOf Zp Bs'.G₀) s = true := frontR_of_tests _ e1 e2'
  have hRow : Johnson.Desc.First.Walk.Law.hasRow h.𝔇.d1.lay (h.𝔇.d1.ncl 24) h.𝔇.d1.lin s' =
      true := by
    have hlay : h.𝔇.d1.lay = (K11.parOf Zp Bs'.G₀).lay := hlay_at hG
    have hncl : h.𝔇.d1.ncl 24 = 1 := ncl_of_test tc
    rw [hlay, hncl]
    exact F.hasRow hy (K11.pendAll_paid h Bs' O)
  have hMade := merge_makes_formsIn (K11.parOf Zp Bs'.G₀) hy hfr (freeAbove_of_tests e1 e2')
    (h.𝔇.N.group 24) xM R F.mask
  obtain ⟨l, name, rr, hlk, hst, hr⟩ := ToldDesc.merge_at_linkAt h.scope h.reads O
  obtain ⟨htr, hms⟩ := K11.htr_hms_at h.toAtMg
  have hmk : ∀ p ∈ (pubRowM (mgAtAll h).more linksFull mergeAt).makes,
      p ∉ (pubSets (mgAtAll h).more linksFull (flatPlacesOf linksFull true))[346]?.getD [] →
      (mgAtAll h).pubP p (z, s') := by
    intro p hp
    have e : (mgAtAll h).more = moreAll := (mgAll_more_base h.𝔇).trans mgMore_is
    rw [e, K11.makes346] at hp
    cases hp
  -- the promise in front, at the meaning without the three sentences on strings
  have ha : onQ (Fr := ⟨0, [], id, 0⟩) h.𝔇.N (stringFree (mgAtAll h)) linksFull
      (flatPlacesOf linksFull true) (fun t => (z, t)) 346 (s, (fun _ => (0, []), fun _ => [])) := by
    refine ⟨trivial, Or.inr ⟨?_, hHeld, fun _ _ => ⟨trivial, trivial⟩, hPP⟩⟩
    show (_ && _ && _ && _ && _ && _) = true
    simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, cIn⟩, cPub⟩, c4⟩
  have hb := merge_t2 (Fr := ⟨0, [], id, 0⟩) h.𝔇.N (stringFree (mgAtAll h)) linksFull
    (flatPlacesOf linksFull true) 346 (K11.parOf Zp Bs'.G₀) mergeAt behindAt k11_hp k11_hp' k11_hq
    k11_hst k11_hlk htr hms z (s, (fun _ => (0, []), fun _ => []))
    (s', (fun _ => (0, []), fun _ => [])) ha ⟨rs, hy⟩ (fun _ => trivial)
    (mgAll_inOrder_rides h.𝔇 z s s')
    (merge_pubHeld_full h.𝔇 mgBase rfl rfl (K11.parOf Zp Bs'.G₀) mergeAt k11_hp z hy hkeep hRow l
      name rr hlk hst hr hMade)
    (merge_hPP_all h.𝔇 mgBase _ _ (K11.parOf Zp Bs'.G₀) z ⟨rs, hy⟩ (fun _ h' => h')
      (fun q hq _ m e => k11_noLeft_front h.𝔇 mgBase rfl m (e ▸ hq)) hmk)
    (merge_hHeld_full h.𝔇 mgBase (K11.parOf Zp Bs'.G₀) h.𝔇.N z
      (s, ((fun _ => (0, []), fun _ => []) : (Frame.mk 0 [] id 0).E.Str))
      (s', (fun _ => (0, []), fun _ => [])) ⟨rs, hy⟩)
    (fun _ _ _ => ⟨trivial, trivial⟩)
  have hf' : s'.failed = none := by
    rw [(yes_keeps (K11.parOf Zp Bs'.G₀) hy).2.2.1]
    exact hf
  have hb' : onAt h.𝔇.N (stringFree (mgAtAll h)) linksFull (flatPlacesOf linksFull true)[347]?
      (IM.openAt linksFull psFull 347) (P1K2.pubAt (stringFree (mgAtAll h)) linksFull psFull 347)
      (z, s') (strsOf ⟨0, [], id, 0⟩ (fun _ => (0, []), fun _ => [])) := hb
  have hxk : IM.XK h.𝔇.N linksFull psFull
      (P1K2.EQ (stringFree (mgAtAll h)) linksFull psFull z) 347 s' = true := P1K2.xk_of_on hb' hf'
  refine ⟨hf', hxk, ?_⟩
  rcases hb'.2 with hm | ⟨_, hS, _, hP⟩
  · exact absurd hf' hm
  · exact ⟨hS, hP⟩

end Johnson.Desc.First.ForkMerge.Behind

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms Johnson.Desc.First.ForkMerge.Behind.runsPassOfTests
#print axioms Johnson.Desc.First.ForkMerge.Behind.promiseBehindMerge
#print axioms Johnson.Desc.First.ForkMerge.Behind.stringFree
