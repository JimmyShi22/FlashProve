-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/LiveSecond.lean: CONDITIONAL: an attention segment's own rounds: every
slot from the two value products' scalars on, and the accumulator's, is named by a form of the run
"second" with a coefficient that does not read 0, where the test on the drawn elements says yes.
Statements with their proofs ON THE VERIFIER'S OWN DATA: no prover is in this file.

Main names:
  RecOk, recOk_of_sum, RecOk.own   what the hearing lays into what was heard of a sumcheck: the
                  claimed sum, the variables, as many challenges as variables; so the hiding
                  polynomial has as many weights as the plan counts slots of the sumcheck's own
  sumLive_r, sumLive_eps   what the test on a sumcheck's drawn elements gives
  rec_own_live, rec_start_live   the row's coefficient, at such a structure
  LiveFits, liveFitsB, liveFits_of_B, liveFits_of   the public premise on the plan's numbers; its
                  test with code; it follows from the library's GeoFits
                  (Johnson/Desc/First/Att/K05PtsSlots.lean) where each unit has all pairs' pieces
                  and the plan counts as many units as the place has
  Heard5          what the statements on both runs take of a hearing, gathered once
  heard5_of       it holds where the hearing returns
  k5_next         the ledger's next slot behind the hearing is the plan's: the two statements' slots
                  are just those that the hearing takes
  k5_live_second  **the statement**

k5_live_second is CONDITIONAL. The premises, and who is meant to show each:
  hh, hz: the hearing returns from a ledger whose arrays have their length; li, hp: the rows are the
    verifier's, the points are made of them; h2: the run returns: whoever has the block's yes.
  gf: the place's numbers are the plan's (LiveFits: it has a test with code, liveFitsB); hg, hzk:
    the structure is made of the shape and of the lookup's key points: public.
  hL: the test on the drawn elements (heardLive, Johnson/Desc/K5/Honest/Law/Live.lean) says yes:
    whoever counts the drawn elements at which it says no.
The slots' numbers are the plan's (numbers_of_plan, Johnson/Desc/First/Att/K05Numbers.lean).
Limits. It speaks of the forms that the run gathers, not of claims in a state's list. One direction:
nothing says that a slot is dead where the test says no.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.LiveForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading Aff Fork)
open VerifiableInference.Desc.Part (MaskedSum.Heard)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends hidingAt ownSlots)
open VerifiableInference.Desc.First.Att.P (Geo UnitG geoOf Heard Left Pts St hear pointsOf LeftIs
  GeoFits formOf sum products keyStage batched sum_spec batch_spec hear_ran ownOf own3 ownKey kB kE
  kV kM kVD kX kF kD kH numsOf numsPlan numbers_of_plan Nums At take_at sum_at batch_at close_at
  takes_at units_at)
open VerifiableInference.Desc.First.Att.P.Runs (In JoinsP firstRun secondRun)
open K5Law (PointsAre points_are oldOf second_any)

/-! ## 1 What was heard of a sumcheck -/

/-- **What the hearing lays into what was heard of a sumcheck.** -/
structure RecOk (C : Aff) (vs : List Var) (e : Ends) (hh : MaskedSum.Heard) : Prop where
  start : hh.start = C
  vars : hh.vars = vs ++ [.point zeroE (e.dY + 1)]
  len : hh.r.length = hh.vars.length

theorem recOk_of_sum {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard} {s s' : St}
    (h : sum C (.sum vs e) s = some (hh, s')) : RecOk C vs e hh := by
  obtain ⟨F, rs, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  obtain ⟨_, _, G1, f, a1, _⟩ := sum_spec h
  obtain ⟨_, T, R, _, hR, e1, _⟩ := VerifiableInference.Desc.Part.MaskedSum.hear_spec a1
  obtain ⟨_, _, _, _, _, _, _, hv, _⟩ := VerifiableInference.Desc.Part.MaskedSum.readAll_spec hR
  subst e1
  refine ⟨rfl, rfl, ?_⟩
  show (R.rounds.map (·.2)).length = (vs ++ [Var.point zeroE (e.dY + 1)]).length
  rw [List.length_map, hv.length.2]

/-- The hiding polynomial has as many weights as the plan counts slots of the sumcheck's own. -/
theorem RecOk.own {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard}
    (R : RecOk C vs e hh) (hd : ∀ v ∈ vs, 1 ≤ v.d) :
    (hidingAt (hh.vars.zip hh.r)).1.length = ownOf vs e := by
  have hm : (hh.vars.zip hh.r).map (·.1) = hh.vars :=
    List.map_fst_zip (Nat.le_of_eq R.len.symm)
  rw [VerifiableInference.Desc.Kinds.Head.Law.hidingAt_length _ ?_ ?_, hm, R.vars]
  · rfl
  · intro e0
    have h0 := congrArg List.length hm
    rw [e0, R.vars] at h0
    simp at h0
  · intro p hp
    have hv : p.1 ∈ vs ++ [Var.point zeroE (e.dY + 1)] := R.vars ▸ (List.of_mem_zip hp).1
    rcases List.mem_append.1 hv with hv | hv
    · exact hd _ hv
    · rw [List.mem_singleton.1 hv]
      exact Nat.le_add_left 1 e.dY

theorem sumLive_r {b : Bool} {hh : MaskedSum.Heard} (h : sumLive b hh = true) :
    ∀ r ∈ hh.r, Reading.gl.val r ≠ 0 := by
  unfold sumLive at h
  rw [Bool.and_eq_true] at h
  exact fun r hr => nzE_val (List.all_eq_true.1 h.1 r hr)

theorem sumLive_eps {hh : MaskedSum.Heard} (h : sumLive true hh = true) :
    Reading.gl.val hh.eps ≠ 0 := by
  unfold sumLive at h
  rw [Bool.and_eq_true] at h
  exact nzE_val (by simpa using h.2)

/-- A slot of the sumcheck's own, by the plan's count. -/
theorem rec_own_live {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard} {b : Bool}
    (R : RecOk C vs e hh) (hd : ∀ v ∈ vs, 1 ≤ v.d) (hl : sumLive b hh = true) (S0 : E) {j : ℕ}
    (h1 : hh.first ≤ j) (h2 : j < hh.first + ownOf vs e) (hs : slotCo Reading.gl C j = 0) :
    slotCo Reading.gl (formOf hh S0 {}) j ≠ 0 :=
  row_own_live Reading.gl hh S0 (sumLive_r hl) h1 (by rw [R.own hd]; exact h2)
    (by rw [R.start]; exact hs)

/-- A slot that the claimed sum names. -/
theorem rec_start_live {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard}
    (R : RecOk C vs e hh) (hl : sumLive true hh = true) (S0 : E) {j : ℕ} (h1 : j < hh.first)
    (hs : slotCo Reading.gl C j ≠ 0) : slotCo Reading.gl (formOf hh S0 {}) j ≠ 0 :=
  row_start_live Reading.gl hh S0 (sumLive_r hl) (sumLive_eps hl) h1 (by rw [R.start]; exact hs)

theorem plain4_d (n : ℕ) : ∀ v ∈ List.replicate n (Var.plain 4), 1 ≤ v.d := fun v hv => by
  rw [List.eq_of_mem_replicate hv]
  exact Nat.le_of_ble_eq_true rfl

theorem keyVars_d (x : OnBytes.Params.AttentionRounds) : ∀ v ∈ (List.replicate x.lt 3 ++
    List.replicate x.lgk (x.lt + 3) ++ List.replicate x.lt (x.lt + 2)).map Var.plain, 1 ≤ v.d := by
  intro v hv
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hv
  show 1 ≤ d
  rcases List.mem_append.1 hd with hd | hd
  · rcases List.mem_append.1 hd with hd | hd
    · rw [List.eq_of_mem_replicate hd]
      omega
    · rw [List.eq_of_mem_replicate hd]
      omega
  · rw [List.eq_of_mem_replicate hd]
    omega

/-! ## 2 What both statements take of the plan and of a hearing -/

/-- **PUBLIC: the place's numbers and the plan's structure of rounds agree**, as far as the two
statements read them: three numbers; and, unit by unit, a softmax-table unit's sumcheck has two end
values for each of the unit's pieces. -/
structure LiveFits (g : Geo) (x : OnBytes.Params.AttentionRounds) : Prop where
  lt : g.lt = x.lt
  NP : g.NP = x.pairs
  Lam : g.Lam = x.Lam
  pieces : List.Forall₂ (fun (u : ℕ × ℕ) (ug : UnitG) => u.2 = ug.pcs.length) x.score g.scores

/-- The same as a test that a program can run. -/
def liveFitsB (g : Geo) (x : OnBytes.Params.AttentionRounds) : Bool :=
  g.lt == x.lt && g.NP == x.pairs && g.Lam == x.Lam && x.score.length == g.scores.length &&
    (x.score.zip g.scores).all fun z => z.1.2 == z.2.pcs.length

theorem liveFits_of_B {g : Geo} {x : OnBytes.Params.AttentionRounds} (h : liveFitsB g x = true) :
    LiveFits g x := by
  unfold liveFitsB at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, List.forall₂_iff_zip.2 ⟨h.1.2, fun hab => h.2 _ hab⟩⟩

/-- It follows from the library's structure on the same numbers where each unit has as many pieces
as the place has pairs (hpc) and the plan counts as many units as the place has (hn). -/
theorem liveFits_of {g : Geo} {x : OnBytes.Params.AttentionRounds} (gf : GeoFits g x)
    (hpc : ∀ u ∈ g.scores, u.pcs.length = x.pairs) (hn : x.score.length = g.scores.length) :
    LiveFits g x :=
  ⟨gf.lt, gf.NP, gf.Lam, List.forall₂_iff_zip.2 ⟨hn, fun hab =>
    (gf.score _ (List.of_mem_zip hab).1).trans (hpc _ (List.of_mem_zip hab).2).symm⟩⟩

/-- **What the hearing lays into its structure**: the plan's numbers, and what was heard of each
sumcheck. -/
structure Heard5 (x : OnBytes.Params.AttentionRounds) (k : ℕ) (h : Heard) : Prop where
  nums : numsOf h = numsPlan x k
  units : List.Forall₂ (fun (u : ℕ × ℕ) (o : ℕ × MaskedSum.Heard) =>
    RecOk (.slot (o.1 + 6)) (List.replicate u.1 (.plain 4)) ⟨2, 2 * u.2⟩ o.2) x.score
    h.scores.toList
  rE : RecOk (.slot (h.five + 1)) (List.replicate x.e (.plain 4)) ⟨2, 2 * x.pairs⟩ h.division
  rM : RecOk (.slot h.values) (List.replicate x.valueM (.plain 4)) ⟨2, 2 * x.pairs⟩ h.below
  rVD : RecOk (.slot (h.values + 1)) (List.replicate x.valueD (.plain 4)) ⟨2, 2 * x.pairs⟩ h.on
  rF : RecOk (batched x.pairs h.om h.maxima 1 0) (List.replicate x.attained (.plain 4))
    ⟨2, 2 * x.pairs⟩ h.atIndex
  rD : RecOk (batched x.pairs h.om' h.atIndex.sEnd 2 1)
    ((List.replicate x.lt 3 ++ List.replicate x.lgk (x.lt + 3) ++
      List.replicate x.lt (x.lt + 2)).map .plain) ⟨x.lt + 1, x.Lam + x.pairs * x.lt⟩ h.key
  rH : RecOk (.ofConst zeroE) (List.replicate x.bits (.plain 4)) ⟨2, 2 * x.pairs⟩ h.cells
  om' : h.om'.size = x.pairs

theorem units_rec : ∀ (us : List (ℕ × ℕ)) (os : List (ℕ × MaskedSum.Heard)) (s s' : St),
    VerifiableInference.Desc.First.Att.P.UnitsRan us os s s' →
    List.Forall₂ (fun (u : ℕ × ℕ) (o : ℕ × MaskedSum.Heard) =>
      RecOk (.slot (o.1 + 6)) (List.replicate u.1 (.plain 4)) ⟨2, 2 * u.2⟩ o.2) us os
  | [], [], _, _, _ => .nil
  | _ :: us, _ :: os, _, s', ⟨s2, ⟨_, _, h2⟩, h3⟩ =>
    .cons (recOk_of_sum h2) (units_rec us os s2 s' h3)
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim

/-- It holds where the hearing returns from a ledger whose arrays have their length. -/
theorem heard5_of {x : OnBytes.Params.AttentionRounds} {F : Fork} {rs : List Fmt.RoundView} {h : Heard}
    {s' : St} (hh : hear x (F, rs, 0) = some (h, s')) (hz : OnBytes.Model.Road.Sized F) :
    Heard5 x F.next h := by
  obtain ⟨sa, sb, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, ⟨F12, rs12, l12⟩,
    ⟨F13, rs13, l13⟩, s14, s15, pt, ha, hb, h1, h2, h3, h4, h5, h6, h7, h8, h9, _, h10, h11, h12,
    h13, h14, h15, h16⟩ := (hear_ran hh).ran
  refine ⟨(numbers_of_plan hh hz).1, units_rec _ _ _ _ hb, recOk_of_sum h4, recOk_of_sum h7,
    recOk_of_sum h8, recOk_of_sum h12, recOk_of_sum h14, recOk_of_sum h16, ?_⟩
  obtain ⟨_, _, r, y, _, _, _, e⟩ := batch_spec h13
  rw [e, List.size_toArray, VerifiableInference.Desc.Part.MaskedSum.powersFrom_length]

/-- **The ledger's next slot behind the hearing is the plan's**: so the slots of which the two
statements speak are just those that the hearing takes. -/
theorem k5_next {x : OnBytes.Params.AttentionRounds} {F : Fork} {rs : List Fmt.RoundView} {h : Heard}
    {s' : St} (hh : hear x (F, rs, 0) = some (h, s')) (hz : OnBytes.Model.Road.Sized F) :
    s'.1.next = k5End x F.next := by
  obtain ⟨sa, sb, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, pt, ha, hb, h1,
    h2, h3, h4, h5, h6, h7, h8, h9, _, h10, h11, h12, h13, h14, h15, h16⟩ := (hear_ran hh).ran
  have a0 : At (F, rs, 0) F.next :=
    ⟨hz, rfl, [], VerifiableInference.Desc.First.Att.P.open_zero _⟩
  obtain ⟨_, aa⟩ := takes_at _ _ _ _ _ ha a0
  obtain ⟨_, ab⟩ := units_at _ _ _ _ _ hb aa
  obtain ⟨_, a1⟩ := take_at h1 ab
  obtain ⟨_, a2⟩ := take_at h2 a1
  obtain ⟨_, a3⟩ := take_at h3 a2
  obtain ⟨_, _, a4⟩ := sum_at h4 a3
  have a5 := batch_at h5 a4
  obtain ⟨_, a6⟩ := take_at h6 a5
  obtain ⟨_, _, a7⟩ := sum_at h7 a6
  obtain ⟨_, _, a8⟩ := sum_at h8 a7
  have a9 := close_at h9 a8
  obtain ⟨_, a10⟩ := take_at h10 a9
  have a11 := batch_at h11 a10
  obtain ⟨_, _, a12⟩ := sum_at h12 a11
  have a13 := batch_at h13 a12
  obtain ⟨_, _, a14⟩ := sum_at h14 a13
  have a15 := batch_at h15 a14
  obtain ⟨_, _, a16⟩ := sum_at h16 a15
  exact a16.2.1

/-- An entry of an array all of whose entries pass the test. -/
theorem all_getD {a : Array E} (h : a.all nzE = true) {b : ℕ} (hb : b < a.size) :
    Reading.gl.val (a.getD b zeroE) ≠ 0 := by
  have h1 : nzE a[b] = true := Array.all_eq_true.1 h b hb
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hb]
  exact nzE_val h1

/-! ## 3 The run "second" -/

section Main
variable {x : OnBytes.Params.AttentionRounds} {F G F' : Fork} {rs rest : List Fmt.RoundView} {lead : ℕ}
  {h : Heard} {i : In} {zk : Array (Array E)} {l : Left} {K : ℕ} {l₂ : List Aff}

/-- **The accumulator's slot, and every slot from the two value products' scalars on, is named with
a coefficient that does not read 0 by a form of the run "second"**, CONDITIONAL on the premises
that the head lists. -/
theorem k5_live_second (S : OnBytes.Attention.Shape) (gL : OnBytes.Model.Forest.Heard)
    (hh : hear x (F, rs, 0) = some (h, G, rest, lead)) (hz : OnBytes.Model.Road.Sized F)
    (li : LeftIs i.g zk h F' l) (hp : pointsOf i.g zk h l = some i.p) (gf : LiveFits i.g x)
    (hg : i.g = geoOf S) (hzk : i.zk = gL.zk) (h2 : secondRun i K = some l₂)
    (hL : heardLive h = true) :
    ∀ j, j = kB x F.next ∨ (kV x F.next ≤ j ∧ j < k5End x F.next) →
      ∃ f ∈ l₂, slotCo Reading.gl f j ≠ 0 := by
  have PA := points_are hp
  obtain ⟨_, _, ⟨SM, eM⟩, ⟨SV, eV⟩, ⟨SF, eF⟩, ⟨SK, eK⟩, ⟨SH, eH⟩⟩ := li.forms
  have Q := heard5_of hh hz
  rw [second_any S gL i K l₂ hg hzk h2]
  unfold heardLive at hL
  simp only [Bool.and_eq_true] at hL
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, lM⟩, lV⟩, lF⟩, lD⟩, lH⟩, lO⟩ := hL
  obtain ⟨H, hH⟩ : ∃ H, H = oldOf S gL i := ⟨_, rfl⟩
  rw [← hH]
  obtain ⟨k, hk⟩ : ∃ k, k = F.next := ⟨_, rfl⟩
  rw [← hk] at Q ⊢
  -- the place's numbers are the plan's
  have hNP : H.S.NP = x.pairs := by
    have e := gf.NP
    rw [hg] at e
    rw [hH]
    exact e
  have hlt : H.S.cf.lt = x.lt := by
    have e := gf.lt
    rw [hg] at e
    rw [hH]
    exact e
  have hLam : H.S.Lam = x.Lam := by
    have e := gf.Lam
    rw [hg] at e
    rw [hH]
    exact e
  -- the numbers that the structure holds
  have n5 : H.d.s5 = kB x k := by
    rw [hH]
    exact PA.s5.trans (congrArg Nums.five Q.nums)
  have nV : h.values = kV x k := congrArg Nums.values Q.nums
  have nCl : H.d.sCl = kV x k := by
    rw [hH]
    exact PA.sCl.trans nV
  have nX : h.maxima = kX x k := congrArg Nums.maxima Q.nums
  have nM6 : H.x.sM6 = kX x k := by
    rw [hH]
    exact PA.sM6.trans nX
  have fM : h.below.first = kM x k := congrArg Nums.fM Q.nums
  have fV : h.on.first = kVD x k := congrArg Nums.fVD Q.nums
  have fF : h.atIndex.first = kF x k := congrArg Nums.fF Q.nums
  have fD : h.key.first = kD x k := congrArg Nums.fD Q.nums
  have fH : h.cells.first = kH x k := congrArg Nums.fH Q.nums
  have gF : h.atIndex.sEnd = kF x k + own3 x.attained := congrArg Nums.eF Q.nums
  have sM : H.d.vpm.sEnd = kM x k + own3 x.valueM := by
    rw [hH]
    show i.p.d.vpm.ends = _
    rw [PA.vpm]
    exact congrArg Nums.eM Q.nums
  have sV : H.d.vpd.sEnd = kVD x k + own3 x.valueD := by
    rw [hH]
    show i.p.d.vpd.ends = _
    rw [PA.vpd]
    exact congrArg Nums.eVD Q.nums
  have sF : H.x.scF.sEnd = kF x k + own3 x.attained := by
    rw [hH]
    show i.p.x.scF.ends = _
    rw [PA.scF]
    exact gF
  have sD : H.x.scd.sEnd = kD x k + ownKey x := by
    rw [hH]
    show i.p.x.scd.ends = _
    rw [PA.scd]
    exact congrArg Nums.eD Q.nums
  have sH : H.x.scH.sEnd = kH x k + own3 x.bits := by
    rw [hH]
    show i.p.x.scH.ends = _
    rw [PA.scH]
    exact congrArg Nums.eH Q.nums
  -- the rows
  have wM : H.d.vpm.rowU = formOf h.below SM {} := by
    rw [hH]
    show i.p.d.vpm.row = _
    rw [PA.vpm]
    exact eM
  have wV : H.d.vpd.rowU = formOf h.on SV {} := by
    rw [hH]
    show i.p.d.vpd.row = _
    rw [PA.vpd]
    exact eV
  have wF : H.x.scF.rowU = formOf h.atIndex SF {} := by
    rw [hH]
    show i.p.x.scF.row = _
    rw [PA.scF]
    exact eF
  have wD : H.x.scd.rowU = formOf h.key SK {} := by
    rw [hH]
    show i.p.x.scd.row = _
    rw [PA.scd]
    exact eK
  have wH : H.x.scH.rowU = formOf h.cells SH {} := by
    rw [hH]
    show i.p.x.scH.row = _
    rw [PA.scH]
    exact eH
  -- the plan's numbers, one behind the other
  have a1 : kE x k = kB x k + 5 + x.lt + 2 := rfl
  have a2 : kV x k = kE x k + own3 x.e + 2 * x.pairs := rfl
  have a3 : kM x k = kV x k + 2 := rfl
  have a4 : kVD x k = kM x k + own3 x.valueM + 2 * x.pairs := rfl
  have a5 : kX x k = kVD x k + own3 x.valueD + 2 * x.pairs := rfl
  have a6 : kF x k = kX x k + x.pairs := rfl
  have a7 : kD x k = kF x k + own3 x.attained + 2 * x.pairs := rfl
  have a8 : kH x k = kD x k + ownKey x + (x.Lam + x.pairs * x.lt) := rfl
  have a9 : k5End x k = kH x k + own3 x.bits + 2 * x.pairs := rfl
  have in6 : ∀ f ∈ Fo.claim6T H K, f ∈ Fo.claim6T H K ++ (Fo.claim7T H K ++ Fo.claim8T H K) :=
    fun f hf => List.mem_append_left _ hf
  have in7 : ∀ f ∈ Fo.claim7T H K, f ∈ Fo.claim6T H K ++ (Fo.claim7T H K ++ Fo.claim8T H K) :=
    fun f hf => List.mem_append_right _ (List.mem_append_left _ hf)
  have in8 : ∀ f ∈ Fo.claim8T H K, f ∈ Fo.claim6T H K ++ (Fo.claim7T H K ++ Fo.claim8T H K) :=
    fun f hf => List.mem_append_right _ (List.mem_append_right _ hf)
  have ho : H.d.s5 + 2 < H.d.sCl := by omega
  have via6 : ∀ j, (j = H.d.sCl ∨ j = H.d.sCl + 1 ∨ j = H.d.s5 ∨
      (∃ e < 2 * H.S.NP, j = H.d.vpm.sEnd + e) ∨ ∃ e < 2 * H.S.NP, j = H.d.vpd.sEnd + e) →
      ∃ f ∈ Fo.claim6T H K ++ (Fo.claim7T H K ++ Fo.claim8T H K),
        slotCo Reading.gl f j ≠ 0 := fun j hj => by
    obtain ⟨f, hf, hl⟩ := live6 Reading.gl H K ho hj
    exact ⟨f, in6 f hf, hl⟩
  have via7 : ∀ j, ((∃ b < H.S.NP, j = H.x.sM6 + b) ∨
      (∃ b < H.S.NP, j = H.x.scF.sEnd + 2 * b) ∨ (∃ lam < H.S.Lam, j = H.x.scd.sEnd + lam) ∨
      ∃ b < H.S.NP, ∃ k < H.S.cf.lt, j = H.x.scd.sEnd + (H.S.Lam + b * H.S.cf.lt + k)) →
      ∃ f ∈ Fo.claim6T H K ++ (Fo.claim7T H K ++ Fo.claim8T H K),
        slotCo Reading.gl f j ≠ 0 := fun j hj => by
    obtain ⟨f, hf, hl⟩ := live7 Reading.gl H K hj
    exact ⟨f, in7 f hf, hl⟩
  intro j hj
  rcases hj with rfl | ⟨j1, j2⟩
  · exact via6 _ (.inr (.inr (.inl n5.symm)))
  by_cases c1 : j < kM x k
  · -- the two value products' scalars
    by_cases c : j = kV x k
    · exact via6 j (.inl (by omega))
    · exact via6 j (.inr (.inl (by omega)))
  by_cases c2 : j < kM x k + own3 x.valueM
  · refine ⟨_, in6 _ (row6m H K), ?_⟩
    rw [wM]
    exact rec_own_live Q.rM (plain4_d _) lM SM (by omega) (by rw [fM]; exact c2)
      (by rw [slotCo_slot, if_neg (by omega)])
  by_cases c3 : j < kVD x k
  · exact via6 j (.inr (.inr (.inr (.inl ⟨j - H.d.vpm.sEnd, by omega, by omega⟩))))
  by_cases c4 : j < kVD x k + own3 x.valueD
  · refine ⟨_, in6 _ (row6d H K), ?_⟩
    rw [wV]
    exact rec_own_live Q.rVD (plain4_d _) lV SV (by omega) (by rw [fV]; exact c4)
      (by rw [slotCo_slot, if_neg (by omega)])
  by_cases c5 : j < kX x k
  · exact via6 j (.inr (.inr (.inr (.inr ⟨j - H.d.vpd.sEnd, by omega, by omega⟩))))
  by_cases c6 : j < kF x k
  · exact via7 j (.inl ⟨j - H.x.sM6, by omega, by omega⟩)
  by_cases c7 : j < kF x k + own3 x.attained
  · refine ⟨_, in7 _ (row7f H K), ?_⟩
    rw [wF]
    exact rec_own_live Q.rF (plain4_d _) lF SF (by omega) (by rw [fF]; exact c7)
      (slotCo_batched_off _ _ _ _ _ _ _ fun b hb => by omega)
  by_cases c8 : j < kD x k
  · -- the end values of the score at the index: the first by their own forms, the second by the
    -- row of the key at the index
    obtain ⟨b, hb, hc⟩ := SD.pair_cases (e := j - (kF x k + own3 x.attained)) (n := x.pairs)
      (by omega)
    rcases hc with hc | hc
    · exact via7 j (.inr (.inl ⟨b, by omega, by omega⟩))
    · refine ⟨_, in7 _ (row7d H K), ?_⟩
      rw [wD]
      have ej : j = h.atIndex.sEnd + (2 * b + 1) := by omega
      refine rec_start_live Q.rD lD SK (by omega) ?_
      rw [ej, slotCo_batched_at Reading.gl h.om' h.atIndex.sEnd 2 1 (by omega) hb]
      exact all_getD lO (by rw [Q.om']; exact hb)
  by_cases c9 : j < kD x k + ownKey x
  · refine ⟨_, in7 _ (row7d H K), ?_⟩
    rw [wD]
    exact rec_own_live Q.rD (keyVars_d x) lD SK (by omega) (by rw [fD]; exact c9)
      (slotCo_batched_off _ _ _ _ _ _ _ fun b hb => by omega)
  by_cases c10 : j < kH x k
  · -- the end values of the key at the index
    by_cases c : j < kD x k + ownKey x + x.Lam
    · exact via7 j (.inr (.inr (.inl ⟨j - H.x.scd.sEnd, by omega, by omega⟩)))
    · obtain ⟨e, he⟩ : ∃ e, e = j - (kD x k + ownKey x + x.Lam) := ⟨_, rfl⟩
      have he' : e < x.pairs * x.lt := by omega
      have hpos : 0 < x.lt := by
        rcases Nat.eq_zero_or_pos x.lt with h0 | h0
        · rw [h0, Nat.mul_zero] at he'
          omega
        · exact h0
      have hd := Nat.div_add_mod' e x.lt
      refine via7 j (.inr (.inr (.inr ⟨e / x.lt, ?_, e % x.lt, ?_, ?_⟩)))
      · rw [hNP]
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact he')
      · rw [hlt]
        exact Nat.mod_lt _ hpos
      · rw [hlt, hLam, sD]
        omega
  by_cases c11 : j < kH x k + own3 x.bits
  · refine ⟨_, in8 _ (row8 H K), ?_⟩
    rw [wH]
    exact rec_own_live Q.rH (plain4_d _) lH SH (by omega) (by rw [fH]; exact c11)
      (slotCo_ofConst _ _ _)
  · obtain ⟨f, hf, hl⟩ := live8 Reading.gl H K (e := j - H.x.scH.sEnd) (by omega)
    refine ⟨f, in8 f hf, ?_⟩
    rw [show j = H.x.scH.sEnd + (j - H.x.scH.sEnd) by omega]
    exact hl

end Main

end H2K5.Honest

#print axioms H2K5.Honest.recOk_of_sum
#print axioms H2K5.Honest.RecOk.own
#print axioms H2K5.Honest.sumLive_r
#print axioms H2K5.Honest.sumLive_eps
#print axioms H2K5.Honest.rec_own_live
#print axioms H2K5.Honest.rec_start_live
#print axioms H2K5.Honest.plain4_d
#print axioms H2K5.Honest.keyVars_d
#print axioms H2K5.Honest.liveFits_of_B
#print axioms H2K5.Honest.liveFits_of
#print axioms H2K5.Honest.units_rec
#print axioms H2K5.Honest.heard5_of
#print axioms H2K5.Honest.k5_next
#print axioms H2K5.Honest.all_getD
#print axioms H2K5.Honest.k5_live_second
