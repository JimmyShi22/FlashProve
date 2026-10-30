-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/GuardNLaw.lean: WHAT KIND K5's GUARD GIVES: at a return of Verify.publicOf a
yes of the plain text k5GuardN (Att/GuardN.lean), with a yes of the block's own test on the plan,
gives K5Public (Att/K05LawOne.lean): all thirteen public premises of the kind's law in one
statement, at the stored plan's own letters.

Main names:
  TWIN BY TWIN: `nValsN_eq`, `heldN_eq` (= k5Held) · `usualN_eq` (= usualB) · `expOkN_gives` (ExpOK)
    · `callsFitN_gives` (CallsFit) · `numsN_gives` (numsB) · `posN_eq` (= posOk) · `unitsN_eq` (=
    unitsOk) · `planOkN_gives` (planOkAll).
  THEOREMS, NO TESTS: `attFits_of_calls` ("att": fits, from CallsFit) · `nc_of_made`, `four_of_plan`
    ("att": four, from "att": shape, "fs", shapeHid's return and the plan's law) · "plan" and "own":
    public_plan (Att/GuardPublic.lean).
  `guardList_gives`: all seven tests of guardListN say yes ⊢ "att": masksIn · planOk (with CallsFit)
    · held, at the plan a.
  "att": shape and planes · "fs" · "mats" · "planes": theorems: guard_theorems (Att/GuardPlan.lean).
  `guard_gives`: **PlanIs W, k5GuardN W l g = true, planOk p = true and claimsOkAtO a = true, at p
    := parO W l a before, and the three facts on the stretch ds as one premise: there are the place
    x and the planner's return A0, a is A0 but for the field plFor of seam.tl, and K5Public holds**
    at tl := a.seam.tl (what the carried record holds), the dry run's letters a's own, kc := 128.
    `guard_gives_written`: at ds := written p the three are theorems.
  `attLinks_mem`: a member of the guard's walk has W.p4 and l = 2 g + 1.
  `asks_give`, `asksFiles_give`: from a yes of every named test of k5AsksN | k5AsksFilesN.
  `walk_gives`, `asksDesc_give`: what the walk's test (Att/GuardWalkN.lean) gives: every block that
    bears the kind K5 in a description stands at a link that the guard has tested, and each such
    link has its block.
So K05_law_one at K5's seated block asks of the public side only what the block's own planOk and the
guard say, at a public record with PlanIs. The guard tests held at the block's numbers with before
:= [] (parN); guard_gives is stated at any before (parO): the kind's rounds, and so held, read no
"before".
Limits. AT A LETTER W WITHOUT PlanIs THE GUARD's YES GIVES NEITHER "plan" NOR "own". asksFiles_give
and asksDesc_give speak of publicOf's own return. That a description's data at the kind's stretch
meet h3 is not shown here. No value of the guard is stated. EVALUATED IS NOT PROVED.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.GuardWalkN
import Johnson.Desc.First.Att.K05PublicB
import Johnson.Desc.First.Att.GuardPlan
import Johnson.Desc.First.Att.GuardFilesN
import Johnson.Road.FormsKeysShape
import Johnson.Desc.First.Look.LookKindAgrees

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Road.L5 (dimOf callsOf)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open VerifiableInference.Desc.First.Look (Sent AttOK attFitsB lookAt)

/-! ## "held" -/

theorem nValsN_eq : ∀ l : List Fmt.Draw, nValsN l = nVals l
  | [] => rfl
  | .elem :: ds => by show _ * nValsN ds = _ * nVals ds; rw [nValsN_eq ds]
  | .elemNZ :: ds => by show _ * nValsN ds = _ * nVals ds; rw [nValsN_eq ds]
  | .pos k :: ds => by show _ * nValsN ds = _ * nVals ds; rw [nValsN_eq ds]
  | .trits n :: ds => by show _ * nValsN ds = _ * nVals ds; rw [nValsN_eq ds]
  | .sealed :: ds => by show _ * nValsN ds = _ * nVals ds; rw [nValsN_eq ds]

theorem heldN_eq (k : ℕ) (p : Par) :
    heldN k p = k5Held k (zOf p.own) ((rounds p).map fun r => (r.entry, kindFmt r.entry)) := by
  unfold heldN k5Held rowOkN rowOk pickN pick
  simp only [nValsN_eq]
  rfl

/-! ## "mats", "att": fits -/

theorem aN_rows (h : Forest.Shape) (c : Fin 4) :
    (OnBytes.Road.Rows.callsOf h).a c = aN h c.val := by
  show (h.calls.getD c.val default).n = _
  unfold aN
  rw [Array.getD_eq_getD_getElem?]
  cases h.calls[c.val]? <;> rfl

/-- **"att": fits is a theorem**: the library's condition at call 2 follows from CallsFit. -/
theorem attFits_of_calls {S : Attention.Shape} {fs : Forest.Shape}
    (h : OnBytes.Road.L5.CallsFit S fs) : attFitsB S fs = true := by
  obtain ⟨u, le, _, _, ten, _, ⟨_, _, lw, _, _⟩, _, _, last⟩ := h
  have e2 : (OnBytes.Road.Rows.callsOf fs).a 2 = aN fs 2 := aN_rows fs 2
  have u2 : (dimOf S).nb * 2 ^ (dimOf S).lW + (dimOf S).nb * 2 ^ (dimOf S).lX ≤ 2 ^ aN fs 2 := u 2
  have le2 : fs.dT ≤ aN fs 2 := le 2
  have l2 : aN fs 2 - fs.dT ≤ fs.rK := (last 2).2
  have lw' : (dimOf S).lW ≤ fs.dT := lw
  have ten' : 10 ≤ fs.dT := ten
  unfold attFitsB
  refine decide_eq_true ⟨e2.symm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e2]; exact le2
  · show (OnBytes.Road.Rows.callsOf fs).a 2 - fs.dT ≤ fs.rK
    rw [e2]; exact l2
  · rw [e2]; exact lw'.trans le2
  · rw [e2]
    have hm : (dimOf S).nb * 2 ^ (dimOf S).lW ≤ 2 ^ (aN fs 2 - (dimOf S).lW) * 2 ^ (dimOf S).lW := by
      rw [← pow_add, Nat.sub_add_cancel (lw'.trans le2)]
      exact le_trans (Nat.le_add_right _ _) u2
    exact Nat.le_of_mul_le_mul_right hm (Nat.two_pow_pos _)
  · show 1 ≤ fs.dT + fs.rK
    omega

/-- Where the lookup's own parameters make the place's shape, that shape counts its own calls. -/
theorem nc_of_made {set : Params.Setting} {x : VerifiableInference.Desc.First.Look.Place}
    (h1 : (VerifiableInference.Desc.First.Look.P.ofPlace set false x).shape = some x.fs) :
    x.fs.NC = x.fs.calls.size := by
  obtain ⟨h0, e, _, e1⟩ := VerifiableInference.Desc.First.Look.P.shape_made h1
  obtain ⟨c1, c2⟩ := OnBytes.Road.shape_calls e
  rw [e1]
  show h0.NC = h0.calls.size
  rw [c1, c2]

/-- **"att": four is a theorem**: from "att": shape, "fs", shapeHid's return and the plan's law. -/
theorem four_of_plan {set : Params.Setting} {x : VerifiableInference.Desc.First.Look.Place}
    (h1 : (VerifiableInference.Desc.First.Look.P.ofPlace set false x).shape = some x.fs) {lid : ℕ}
    {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape} (hfs : x.fs = fs)
    (hid : Attention.shapeHid lid cf = Except.ok (S, fs)) (PL : K5Law.PlanLaw cf S fs) :
    x.fs.NC = 4 := by
  rw [nc_of_made h1, hfs, OnBytes.Road.L5.calls_of_hid hid, Array.size_map, ← Array.length_toList,
    PL.place.calls]
  rfl

/-! ## "planOk" -/

theorem usualN_eq (cf : Attention.Cfg) : usualN cf = OnBytes.Road.L5.usualB cf := rfl

theorem expOkN_gives {sh u0 : ℕ} (e : expOkN sh u0 = true) : ExpOK sh u0 := by
  unfold expOkN at e
  simp only [Bool.and_eq_true, decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := e
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem all4 {q : ℕ → Prop} [DecidablePred q]
    (h : (List.range 4).all (fun c => Decidable.decide (q c)) = true) : ∀ c : Fin 4, q c.val := by
  intro c
  have := List.all_eq_true.1 h c.val (List.mem_range.2 c.isLt)
  exact of_decide_eq_true this

theorem callsFitN_gives {S : Attention.Shape} {fs : Forest.Shape} (e : callsFitN S fs = true) :
    OnBytes.Road.L5.CallsFit S fs := by
  unfold callsFitN at e
  simp only [Bool.and_eq_true, decide_eq_true_eq] at e
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := e
  have a1 := all4 h1
  have a2 := all4 h2
  have a4 := all4 h4
  have a13 := all4 h13
  have a14 : ∀ c : Fin 4, fs.iota.getD c.val 0 = aN fs c.val - fs.dT ∧ aN fs c.val - fs.dT ≤ fs.rK := by
    intro c
    have := List.all_eq_true.1 h14 c.val (List.mem_range.2 c.isLt)
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using this
  refine ⟨fun c => ?_, fun c => a2 c, h3, fun c => ?_, h5, expOkN_gives h6, ⟨h7, h8, h9, h10, h11⟩,
    h12, fun c => ?_, fun c => a14 c⟩
  · have := a1 c
    fin_cases c <;> exact this
  · have := a4 c
    fin_cases c <;> exact Nat.dvd_of_mod_eq_zero this
  · have := a13 c
    fin_cases c <;> exact this

theorem numsN_gives {S : Attention.Shape} (e : numsN S = true) : OnBytes.Road.L5.numsB S = true := by
  unfold numsN at e
  simp only [Bool.and_eq_true, beq_iff_eq] at e
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := e
  unfold OnBytes.Road.L5.numsB
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, ?_⟩
  rw [h12]
  rfl

theorem posN_eq (g : Geo) : posN g = K5Law.posOk g := rfl

theorem unitsN_eq (S : Attention.Shape) (fs : Forest.Shape) : unitsN S fs = unitsOk S fs := rfl

theorem planOkN_gives {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape}
    (h1 : usualN cf = true) (h2 : callsFitN S fs = true) (h3 : numsN S = true)
    (h4 : posN (geoOf S) = true) (h5 : unitsN S fs = true) : planOkAll cf S fs = true := by
  unfold planOkAll K5Law.planOkLaw
  rw [← usualN_eq, h1, numsN_gives h3, ← posN_eq, h4, ← unitsN_eq, h5,
    decide_eq_true (callsFitN_gives h2)]
  rfl

/-! ## What the guard gives -/

/-- **All seven tests of the list say yes**: "att": masksIn, "planOk" and "held". -/
theorem guardList_gives {a : Attention.Plan} {x : VerifiableInference.Desc.First.Look.Place}
    {p : Par} (h : (guardListN a x p).all (·.2) = true) :
    x.F.next + FoNums.nMasks x.fs ≤ x.ns ∧ planOkAll a.S.cf a.S a.fs = true ∧
      OnBytes.Road.L5.CallsFit a.S a.fs ∧
      k5Held 128 (zOf p.own) ((rounds p).map fun r => (r.entry, kindFmt r.entry)) = true := by
  unfold guardListN at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h5, h7, h8, h9, h10, h11, h14⟩ := h
  refine ⟨h5, planOkN_gives h7 h8 h9 h10 h11, callsFitN_gives h8, ?_⟩
  rw [← heldN_eq]
  exact h14

/-- **What the guard gives where the stored plans are the planner's and the proof covers
attention**, at link 2 g + 1, with the block's own test on the plan and the three facts on the
stretch: K5Public, all thirteen, at the stored plan a's own letters; A0: what the planner returns at
a's settings, input and configuration. -/
theorem guard_gives {W : Verify.Public} (hP : PlanIs W) (h4 : W.p4 = true) (g : ℕ)
    (before : List (ℕ × ℕ)) (D : Sent) (rad : OracleShape → Nat) {a : Attention.Plan}
    (ha : W.A[g]? = some a) (hG : k5GuardN W (2 * g + 1) g = true)
    (hb : planOk (parO W (2 * g + 1) a before) = true) (hc : claimsOkAtO a = true) (ds : List RDT)
    (h3 : (∀ d ∈ ds, Plain (toRD d)) ∧
      ds.map (·.entry) = (rounds (parO W (2 * g + 1) a before)).map (·.entry) ∧
      ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind) :
    ∃ x A0, lookAt W (2 * g + 1) false = some x ∧
      (∃ pf, a = { A0 with seam := { A0.seam with tl := { A0.seam.tl with plFor := pf } } }) ∧
      K5Public x a.seam.tl D rad (Params.settingOf W.P.frame) a.settings a.inp a.S.cf A0
        (parO W (2 * g + 1) a before) ds 128 a.iU3 a.nW (plannedK a) (padOfO a.fs) a.fs.dT := by
  obtain ⟨A0, pf, hA, e⟩ := hP g a ha
  unfold k5GuardN k5ListN at hG
  rw [ha] at hG
  cases hx : lookAt W (2 * g + 1) false with
  | none => rw [hx] at hG; cases hG
  | some x =>
    rw [hx] at hG
    dsimp only at hG
    obtain ⟨t1, t2, t3, t4, t5⟩ := guard_theorems hP h4 ha hx (Params.settingOf W.P.frame)
    obtain ⟨g5, g3, gc, g6⟩ := guardList_gives hG
    have hid0 := (OnBytes.Road.L5.plan_shape hA).1
    have eS : a.S = A0.S := by rw [e]
    have eF : a.fs = A0.fs := by rw [e]
    have eO : a.own = A0.own := by rw [e]
    have hid : Attention.shapeHid a.settings.lidb a.S.cf = Except.ok (a.S, a.fs) := by
      rw [eS, eF]
      rw [eS] at hid0
      exact hid0
    have g1 : AttOK (Params.settingOf W.P.frame) x a.S a.seam.tl D rad :=
      ⟨t1, four_of_plan t1 t3 hid (plan_all hid g3).law, t2,
        by rw [t3]; exact attFits_of_calls gc, g5⟩
    have hown : (parO W (2 * g + 1) a before).own = A0.own := eO
    have g3' : planOkAll a.S.cf A0.S A0.fs = true := by rw [← eS, ← eF]; exact g3
    have t5' : Look.planesOk x.fs (parCOf a).geo.lmb = true := t5
    refine ⟨x, A0, rfl, ⟨pf, e⟩, hA, eS ▸ g1, t3.trans eF, g3', hown,
      pair_of_planOk x a.seam.tl D rad hA g3' hown hb, eS ▸ t4, ?_, ?_, h3.1, h3.2.1, h3.2.2, g6,
      by rw [e]; rfl⟩
    · rw [← eS]
      exact claims_of_atO t3 t5' hc
    · have : (parCOf A0).geo.lmb = (parCOf a).geo.lmb := by rw [e]; rfl
      rw [this]
      exact t5'

/-- **At the kind's own written rounds** the three facts on the stretch are theorems. -/
theorem guard_gives_written {W : Verify.Public} (hP : PlanIs W) (h4 : W.p4 = true) (g : ℕ)
    (before : List (ℕ × ℕ)) (D : Sent) (rad : OracleShape → Nat) {a : Attention.Plan}
    (ha : W.A[g]? = some a) (hG : k5GuardN W (2 * g + 1) g = true)
    (hb : planOk (parO W (2 * g + 1) a before) = true) (hc : claimsOkAtO a = true) :
    ∃ x A0, lookAt W (2 * g + 1) false = some x ∧
      (∃ pf, a = { A0 with seam := { A0.seam with tl := { A0.seam.tl with plFor := pf } } }) ∧
      K5Public x a.seam.tl D rad (Params.settingOf W.P.frame) a.settings a.inp a.S.cf A0
        (parO W (2 * g + 1) a before) (written (parO W (2 * g + 1) a before)) 128 a.iU3 a.nW
        (plannedK a) (padOfO a.fs) a.fs.dT :=
  guard_gives hP h4 g before D rad ha hG hb hc _ ⟨seam_plain _, seam_entries _, seam_kinds _⟩

/-- A member of the walk: the proof covers attention, and the link is 2 g + 1. -/
theorem attLinks_mem {W : Verify.Public} {y : ℕ × ℕ} (hy : y ∈ attLinksN W) :
    W.p4 = true ∧ y.1 = 2 * y.2 + 1 ∧ y.2 < W.NGr := by
  unfold attLinksN at hy
  split at hy
  · rename_i h4
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
    exact ⟨h4, rfl, List.mem_range.1 hg⟩
  · cases hy

/-- A yes of every named test of k5AsksN is the guard's yes at every attention segment. -/
theorem asks_give (W : Verify.Public) (h : ∀ t ∈ k5AsksN W, t.2 = true) :
    ∀ y ∈ attLinksN W, k5GuardN W y.1 y.2 = true := by
  intro y hy
  unfold k5GuardN
  refine List.all_eq_true.2 fun t ht => ?_
  exact h (s!"link {y.1}: {t.1}", t.2)
    (List.mem_flatMap.2 ⟨y, hy, List.mem_map.2 ⟨t, ht, rfl⟩⟩)

/-- **Off the three public files**: a yes of every named test gives the public record and the
guard's
yes at every attention segment of it. -/
theorem asksFiles_give (pol lay KL : ByteArray) (h : ∀ t ∈ k5AsksFilesN pol lay KL, t.2 = true) :
    ∃ W, Model.Verify.publicOf pol KL (some lay) = .ok W ∧
      ∀ y ∈ attLinksN W, k5GuardN W y.1 y.2 = true := by
  unfold k5AsksFilesN at h
  cases hW : Model.Verify.publicOf pol KL (some lay) with
  | error e =>
    rw [hW] at h
    exact absurd (h _ (List.mem_singleton.2 rfl)) (by simp)
  | ok W =>
    rw [hW] at h
    exact ⟨W, rfl, asks_give W h⟩

/-! ## The walk -/

/-- **What the walk's test gives**: every block of kind K5 in the first chain stands at a place of
the
walk; every place of the walk has its block; the two other chains have no such block. -/
theorem walk_gives {Xi : Type} (W : Verify.Public) (F : VerifiableInference.Desc.FileDescription Xi)
    (h : k5WalkN W F = true) :
    (∀ b ∈ F.first.blocksInOrder, b.place.kind = .K5 →
      ∃ y ∈ attLinksN W, b.place = ⟨1, some y.1, 3, .K5⟩) ∧
    (∀ y ∈ attLinksN W, ∃ b ∈ F.first.blocksInOrder, b.place = ⟨1, some y.1, 3, .K5⟩) ∧
    (∀ b ∈ F.shared.blocksInOrder, b.place.kind ≠ .K5) ∧ ∀ b ∈ F.second.blocksInOrder, b.place.kind ≠ .K5 := by
  unfold k5WalkN k5WalkPlacesN at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun b hb hk => ?_, fun y hy => ?_, fun b hb => h2 _ (List.mem_map_of_mem hb),
    fun b hb => h3 _ (List.mem_map_of_mem hb)⟩
  · have hm : b.place ∈ (F.first.blocksInOrder.map (·.place)).filter fun q => q.kind == .K5 :=
      List.mem_filter.2 ⟨List.mem_map_of_mem hb, by rw [hk]; rfl⟩
    rw [h1] at hm
    obtain ⟨y, hy, e⟩ := List.mem_map.1 hm
    exact ⟨y, hy, e.symm⟩
  · have hm : (⟨1, some y.1, 3, .K5⟩ : VerifiableInference.Desc.Place) ∈ k5PlacesN W :=
      List.mem_map.2 ⟨y, hy, rfl⟩
    rw [← h1] at hm
    obtain ⟨b, hb, e⟩ := List.mem_map.1 (List.mem_filter.1 hm).1
    exact ⟨b, hb, e⟩

/-- **From a yes of every named test of k5AsksDescN**: the public record, the guard's yes at every
attention segment, and the walk's test. -/
theorem asksDesc_give {Xi : Type} (pol lay KL : ByteArray)
    (F : VerifiableInference.Desc.FileDescription Xi) (h : ∀ t ∈ k5AsksDescN pol lay KL F, t.2 = true) :
    ∃ W, Model.Verify.publicOf pol KL (some lay) = .ok W ∧
      (∀ y ∈ attLinksN W, k5GuardN W y.1 y.2 = true) ∧ k5WalkN W F = true := by
  unfold k5AsksDescN at h
  obtain ⟨W, hW, hg⟩ := asksFiles_give pol lay KL fun t ht => h t (List.mem_append_left _ ht)
  have hw := h _ (List.mem_append_right _ (List.mem_singleton.2 rfl))
  rw [hW] at hw
  exact ⟨W, hW, hg, hw⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.walk_gives
#print axioms VerifiableInference.Desc.First.Att.P.asksDesc_give
#print axioms VerifiableInference.Desc.First.Att.P.attFits_of_calls
#print axioms VerifiableInference.Desc.First.Att.P.nc_of_made
#print axioms VerifiableInference.Desc.First.Att.P.four_of_plan
#print axioms VerifiableInference.Desc.First.Att.P.asksFiles_give
#print axioms VerifiableInference.Desc.First.Att.P.guardList_gives
#print axioms VerifiableInference.Desc.First.Att.P.guard_gives
#print axioms VerifiableInference.Desc.First.Att.P.guard_gives_written
#print axioms VerifiableInference.Desc.First.Att.P.attLinks_mem
#print axioms VerifiableInference.Desc.First.Att.P.asks_give
#print axioms VerifiableInference.Desc.First.Att.P.heldN_eq
#print axioms VerifiableInference.Desc.First.Att.P.callsFitN_gives
#print axioms VerifiableInference.Desc.First.Att.P.numsN_gives
#print axioms VerifiableInference.Desc.First.Att.P.unitsN_eq
#print axioms VerifiableInference.Desc.First.Att.P.planOkN_gives
#print axioms VerifiableInference.Desc.First.Att.P.nValsN_eq
#print axioms VerifiableInference.Desc.First.Att.P.aN_rows
#print axioms VerifiableInference.Desc.First.Att.P.usualN_eq
#print axioms VerifiableInference.Desc.First.Att.P.expOkN_gives
#print axioms VerifiableInference.Desc.First.Att.P.all4
#print axioms VerifiableInference.Desc.First.Att.P.posN_eq
