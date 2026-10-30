-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MsgsPlaces.lean: THE
FIRST CLAUSE OF THE FENCE (K2.Fence, Johnson/Top/H0/Tw/K2C/SendsOn.lean), PAID AT THE CODE
SWITCHES IN FRONT OF THE BLOCKS BEHIND THE LAST LINK; AND SO Johnson/IMR/MsgsCut.lean's
msgs_at_cut_but's
PREMISE hM, PAID IN THE GOALS' SCOPE, UNDER K2Told ALONE.

What it is about. A code switch's decision does not read what its block tells: what it sends is read
off the verifier's state's frame. Here: at the states that the fold hands to the 24 switches in
front (the links 1 to 23; the head's link), what the frame says IS what the lot's numbers say is
sent, of which the block's told oracle messages are made.
AT EVERY Z AND G (no scope):
  prep_facts, nums_facts: what P1K2.prepOf and numsAt give, off their texts
      (Johnson/Desc/ProofFile/Lot/K2OfPlan.lean): the sizes' request and codes are the letters'
      first chain's; the frames are Plan.framesOf; n.sent is the l-th frame's list; layTrees lays
      it.
  firstFront_notices: what the front of a later link's switch announces, off firstFront's text.
  fence1_at_link, fence1_at_head, **fence1_at: prepOf Z G = some Pp · numsAt Pp (some l) = some n ·
      t.check.frame.link = l · t.check.frame.shape = G.first.shape · t.check.frame.groups =
      reqGroups G.first.shape · st ≠ .finish ⇒ Fence1 (IM.k2P Z a nm st n) n.sent t.** By
      notices_sent (Johnson/Top/H0/K2Hands/NoticesSent.lean).
      reqFrom_length, reqGroups_size.
  marked_of_rounds · joined_lot_adds · hear_K2 · k2Is_adds (a lot's block of the kind K2, by
      K2Seat.lean's K2Is, under the fence's first clause) · batch_poss, closeOf_poss.
IN SCOPE (InScope P · readFiles P = .ok pp · an opening at OnBytes.secondHashFunction):
  head_link_at: at the cut 339 the walk's frame stands at link
      24.
  adds_at_marked: **j < 353 · c.blocksInOrder[j]? = some b · b.planOk = true · b declares a round that draws
      positions · the fold's returns r₀ at the cut j and r₁ at j + 1, from ProofFile.startS Z p at ft = 0
      ⇒ r₁.1.st.oracles.size = r₀.1.st.oracles.size + toldMsgs b.** By cases on
      flat_cases (Johnson/IMR/FlatCases.lean): eight of the ten forms draw no position or stand
        behind;
      "first" and "hear": marked_kind (Johnson/IMR/NoPosSeat.lean) makes the lot's block K2's; the
        state's
      frame: laid_at, h1_check (FrontPin.lean) and open_recAll
      (Johnson/IMR/ListsEnds.lean).
TRULY SAID OF THE SEARCH. firstFront_notices and fence1_at_link were typed BEFORE
FrontPin.lean was read. Fellows: front_link (K2Hands/TiedAt.lean: the like at
K2.frontAt) and K2.link_notices and FrontPin.lean's front_pin_link (the front's target and other
announcements as terms of the plan's shape): these tie the state's front to the SHAPE; fence1_at
ties it to the LOT's n.sent; firstFront_notices opens firstFront's text a third time. head_link_at
repeats the first lines of front_pin_head's proof, which hands that equation out under no name.
step_of_cuts and front_len stand in RootsWhole.lean, which this file
imports.
PREMISE: K2Told (MsgsSwitch.lean): not shown here: K2C/ToldTenants.lean's told_tenants.
OBJECT · USER · LETTERS. Object: c := F.first, F := ProofFile.onlineDescription OnBytes.secondHashFunction's value, in scope.
User: Johnson/IMR/MsgsScope.lean; whoever needs the fence's first clause. Letters: none.



Compiled with the whole library.

Limits. The finish's switch ("F:1", behind the last link) is not here. The fence's other two clauses
are not here. No member. Nothing on soundness.
-/
import Johnson.IMR.MsgsSwitch
import Johnson.IMR.NoPosSeat
import Johnson.IMR.RootsWhole
import Johnson.IMR.FlatCases
import Johnson.IMR.FrontPin
import Johnson.IMR.ListsEnds
import Johnson.Top.H0.K2Hands.NoticesSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First hiding Col
open ProofFile (Cl)

/-! ## 1 What the lot's numbers are made of -/

theorem prep_facts {Z : ProofFile.Pub} {G : ProofFile.Ground} {Pp : P1K2.Prep}
    (h : P1K2.prepOf Z G = some Pp) :
    Pp.z.request = G.first.shape ∧ Pp.z.codes = G.first.codes ∧
      Pp.frames = Plan.framesOf Pp.z (Verify.subproofsWith G.W G.first.shape.link) := by
  unfold P1K2.prepOf P1K2.prepareAt at h
  simp only [bind, Option.bind, pure] at h
  split at h
  · cases h
  · rename_i ht
    split at h
    · cases h
    · cases h
      unfold P1K2.tied at ht
      simp only [Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_eq] at ht
      exact ⟨ht.1.1.1.1, ht.1.1.1.2, rfl⟩

theorem nums_facts {Pp : P1K2.Prep} {l : Nat} {n : P1K2.Nums}
    (h : P1K2.numsAt Pp (some l) = some n) :
    l ≠ 0 ∧ ∃ f lay, Pp.frames[l]? = some f ∧ layTrees Pp.z.codes f.sent.toArray = some lay ∧
      n.sent = f.sent.toArray ∧ n.codes = Pp.z.codes ∧ n.grp = l := by
  unfold P1K2.numsAt at h
  dsimp only [Option.getD_some] at h
  split at h
  · cases h
  · rename_i h0
    obtain ⟨-, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨f, hf, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨lay, hl, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨read, -, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact ⟨by simpa using h0, f, lay, hf, hl, rfl, rfl, rfl⟩

/-! ## 2 The fence's first clause at a link -/

/-- What the front of a later link's switch announces, off the text of firstFront. -/
theorem firstFront_notices {T : Statement} {f : ReqFrame} {x : _root_.Tw.K2.Front}
    (h : _root_.Tw.K2.firstFront T f = .ok x) :
    f.link ≠ 0 ∧ (f.shape.link[f.link]?).isSome = true ∧ ∃ g, f.groups[f.link]? = some g ∧
      _root_.Tw.K2.switchNotices x.T x.others = _root_.Tw.K2.switchNotices g.target
        (ReqFrame.notices (f.atMoment 0) ++ #[foldMaskNotice (f.foldShape f.link {})]) := by
  unfold _root_.Tw.K2.firstFront at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i h0
      split at h
      · rename_i L G hL hG
        dsimp only at h
        split at h
        · cases h
        · cases h
          exact ⟨by simpa using h0, by rw [hL]; rfl, G, hG, rfl⟩
      · cases h
      · cases h

/-- **At a state whose walk's frame has the plan's shape and groups and stands at link l: whatever
front a link's code switch at the lot's numbers for link l takes off it announces just what the
lot's numbers say is sent.** By notices_sent (NoticesSent.lean). -/
theorem fence1_at_link {Z : ProofFile.Pub} {G : ProofFile.Ground} {Pp : P1K2.Prep} {l : Nat} {n : P1K2.Nums}
    (hP : P1K2.prepOf Z G = some Pp) (hn : P1K2.numsAt Pp (some l) = some n) {t : S}
    (hl : t.check.frame.link = l) (hs : t.check.frame.shape = G.first.shape)
    (hg : t.check.frame.groups = reqGroups G.first.shape) (a : Place) (nm : String) :
    Fence1 (IM.k2P Z a nm .link n) n.sent t := by
  intro x hx
  obtain ⟨e1, -, e3⟩ := prep_facts hP
  obtain ⟨-, f', lay, hf', -, es, -, -⟩ := nums_facts hn
  rcases hx with ⟨-, hx⟩ | ⟨hst, -⟩ | ⟨hst, -⟩
  · obtain ⟨h0, hL, g, hG, e⟩ := firstFront_notices hx
    obtain ⟨nF, hF, eN⟩ := K2Hands.notices_sent Pp.z (Verify.subproofsWith G.W G.first.shape.link)
      t.check.frame (hs.trans e1.symm) (by rw [hg, e1]) (Nat.pos_of_ne_zero h0)
      (by
        obtain ⟨L, hL'⟩ := Option.isSome_iff_exists.1 hL
        rw [e1.trans hs.symm]
        exact Nat.le_of_lt (List.getElem?_eq_some_iff.1 hL').1) g hG
    rw [← e3, hl, hf'] at hF
    obtain rfl := Option.some.inj hF
    rw [e, es, ← eN]
  · cases hst
  · cases hst

/-! ## 3 The same at the head's link -/

theorem reqFrom_length (sh : Params.ReqShape) : ∀ (count l : Nat) (alive : List ReqAlive),
    (reqGroupsFrom sh count l alive).length = count
  | 0, _, _ => rfl
  | count + 1, l, alive => by
    rw [reqGroupsFrom, List.length_cons, reqFrom_length sh count]

theorem reqGroups_size (sh : Params.ReqShape) : (reqGroups sh).size = sh.link.length + 1 := by
  rw [reqGroups_eq]
  simp [reqFrom_length]

/-- The switch at the head's link: at a state whose walk's frame has the plan's shape and groups and
stands at link l. -/
theorem fence1_at_head {Z : ProofFile.Pub} {G : ProofFile.Ground} {Pp : P1K2.Prep} {l : Nat} {n : P1K2.Nums}
    (hP : P1K2.prepOf Z G = some Pp) (hn : P1K2.numsAt Pp (some l) = some n) {t : S}
    (hl : t.check.frame.link = l)
    (hs : t.check.frame.shape = G.first.shape)
    (hg : t.check.frame.groups = reqGroups G.first.shape) (a : Place) (nm : String) :
    Fence1 (IM.k2P Z a nm .head n) n.sent t := by
  intro x hx
  obtain ⟨e1, -, e3⟩ := prep_facts hP
  obtain ⟨h0, f', lay, hf', -, es, -, -⟩ := nums_facts hn
  rcases hx with ⟨hst, -⟩ | ⟨-, a', g, -, hG, rfl⟩ | ⟨hst, -⟩
  · cases hst
  · obtain ⟨nF, hF, eN⟩ := K2Hands.notices_sent Pp.z (Verify.subproofsWith G.W G.first.shape.link)
      t.check.frame (hs.trans e1.symm) (by rw [hg, e1]) (by rw [hl]; exact Nat.pos_of_ne_zero h0)
      (by
        have k := (Array.getElem?_eq_some_iff.1 hG).1
        rw [hg, reqGroups_size, ← e1] at k
        omega) g hG
    rw [← e3, hl, hf'] at hF
    obtain rfl := Option.some.inj hF
    show _root_.Tw.K2.switchNotices g.target (ReqFrame.notices (t.check.frame.atMoment 0) ++
      #[foldMaskNotice (t.check.frame.foldShape t.check.frame.link {})]) = _
    rw [es, ← eN]
  · cases hst

/-- Both. -/
theorem fence1_at {Z : ProofFile.Pub} {G : ProofFile.Ground} {Pp : P1K2.Prep} {l : Nat} {n : P1K2.Nums}
    (hP : P1K2.prepOf Z G = some Pp) (hn : P1K2.numsAt Pp (some l) = some n) {t : S}
    (hl : t.check.frame.link = l) (hs : t.check.frame.shape = G.first.shape)
    (hg : t.check.frame.groups = reqGroups G.first.shape) (a : Place) (nm : String) (st : K2.At)
    (hst : st ≠ K2.At.finish) : Fence1 (IM.k2P Z a nm st n) n.sent t := by
  cases st with
  | link => exact fence1_at_link hP hn hl hs hg a nm
  | head => exact fence1_at_head hP hn hl hs hg a nm
  | finish => exact absurd rfl hst

/-! ## 4 At the fold's own two states -/

theorem marked_of_rounds {x y : Block S Cl} (e : x.rounds = y.rounds)
    (h : Marked drawsPos x) : Marked drawsPos y := by
  obtain ⟨r, hr, k⟩ := h
  exact ⟨r, e ▸ hr, k⟩

/-- IM.Joined over any block x of a lot: where a yes of x adds what x tells, a yes of the
joined block's step adds what it tells. -/
theorem joined_lot_adds {Z : ProofFile.Pub} {l : Nat} {b : Block S Cl} {x : Block S Unit} {a : Place}
    (hj : IM.Joined Z l b x.retype a) {ft : Nat} {s t : S} {n : Nat} {rs : List Fmt.RoundView}
    {cols : List OpenedColumn}
    (hx : ∀ rs' gs m, x.decide s rs' gs = .ok m →
      m.st.oracles.size = s.st.oracles.size + toldMsgs x)
    (hy : b.step ft s rs cols = .ok (t, n)) :
    t.st.oracles.size = s.st.oracles.size + toldMsgs b := by
  obtain ⟨fs, f, m, hfs, hf, hm, -, ho, -, -⟩ := hj.step hy
  obtain ⟨rs', gs', hd⟩ := ChainEnd.step_decide ft _ s m rs cols n hm
  have e1 := hx rs' gs' m hd
  have e2 : t.st.oracles.size = m.st.oracles.size :=
    (Meaning.K2.framesOf_three rcM_three hfs f (List.mem_of_getElem? hf)).2.1 m t ho
  have e3 : toldMsgs b = toldMsgs x := by
    obtain ⟨fs', f', -, -, e⟩ := hj
    rw [e]
    show ((x.oracles ++ []).flatten.map
      fun o : VerifiableInference.Desc.Oracle => o.tenants.length).sum = _
    rw [List.append_nil]
    rfl
  rw [e2, e1, e3]

/-- Behind the first entry of a link a code switch stands at the head's link alone, second. -/
theorem hear_K2 {l i : Nat} (hi : 1 ≤ i)
    (hk : (kindsBeforeBatching (IM.subAt l) (l == 0))[i]? = some KindName.K2) : l = 24 ∧ i = 1 := by
  have hlt := (List.getElem?_eq_some_iff.1 hk).1
  unfold IM.subAt at hk hlt
  generalize (l == 0) = z at hk hlt
  split at hk
  · rename_i h24
    refine ⟨h24, ?_⟩
    rw [if_pos h24] at hlt
    cases z <;>
      · have h9 : i < 9 := hlt
        interval_cases i <;> first | rfl | (exfalso; revert hk; decide)
  · rename_i h24
    rw [if_neg h24] at hlt
    exfalso
    split at hk
    · rename_i h2
      rw [if_pos h2] at hlt
      cases z <;>
        · have h7 : i < 7 := hlt
          interval_cases i <;> (revert hk; decide)
    · rename_i h2
      rw [if_neg h2] at hlt
      cases z <;>
        · have h7 : i < 7 := hlt
          interval_cases i <;> (revert hk; decide)

/-- What a lot's block of the kind K2 adds, under the fence's first clause at each word "stands". -/
theorem k2Is_adds (hT : K2Told) {Z : ProofFile.Pub} {G : ProofFile.Ground} {x : Block S Unit} {l : Nat}
    (his : IM.K2Is Z G x.place x.name x) (hp : x.planOk = true) (hl : x.place.link = some l)
    {s : S}
    (hF : ∀ Pp n, P1K2.prepOf Z G = some Pp → P1K2.numsAt Pp (some l) = some n →
      ∀ st, st ≠ K2.At.finish → Fence1 (IM.k2P Z x.place x.name st n) n.sent s) :
    ∀ rs gs m, x.decide s rs gs = .ok m →
      m.st.oracles.size = s.st.oracles.size + toldMsgs x := by
  intro rs gs m h
  obtain ⟨Pp, n, hP, hn, arms⟩ := his.live hp
  rw [hl] at hn
  obtain ⟨-, f', lay, -, hlay, es, ec, -⟩ := nums_facts hn
  have hlay' : layTrees n.codes n.sent = some lay := by rw [ec, es]; exact hlay
  rcases arms with ⟨h0, -⟩ | ⟨l', HP, -, -, ex⟩ | ⟨l', -, ex⟩
  · rw [hl] at h0
    cases h0
  · rw [ex] at h ⊢
    exact headLot_adds hT (hF Pp n hP hn .head (by decide)) rfl hlay' h
  · rw [ex] at h ⊢
    exact k2_adds_of_fence hT (hF Pp n hP hn .link (by decide)) rfl hlay' h

/-! ## 5 In the goals' scope: hM, paid -/

theorem batch_poss (p : K9.Where) (g : S → Except String (List Claim × S)) :
    ∀ r ∈ (K9.batch K9.atS p g : Block S Cl).rounds, r.entry.poss = 0 := fun r hr =>
  beq_iff_eq.1 (List.all_eq_true.1
    (show ((K9.batch K9.atS p g : Block S Cl).rounds.all fun r => r.entry.poss == 0) = true from
      rfl) r hr)

theorem closeOf_poss (p : K9.Where) (Q : Close.Par) {x : Block S Unit}
    (hx : x ∈ (K9.closeOf p Q : List (Block S Unit))) : ∀ r ∈ x.rounds, r.entry.poss = 0 := by
  unfold K9.closeOf at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · intro r hr
    cases hr
  · intro r hr
    have hr' : r ∈ (Close.entries Q).map (fun e => ({ entry := e } : Fmt.DeclaredRound)) := hr
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hr'
    unfold Close.entries at he
    simp only [List.mem_cons, List.mem_replicate] at he
    rcases he with rfl | rfl | ⟨-, rfl⟩ <;> rfl
  · intro r hr
    cases hr

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The walk's frame at the cut in front of the head's link's switch. -/
theorem head_link_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R R₀ : List Fmt.RoundView} {C C₀ : List OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    t₀.check.frame.link = 24 := by
  obtain ⟨Lk, b0, eL, e0, hj, -⟩ := IM.k7_sits hS hR O
  have i0 : c.blocksInOrder[338]? = some b0 := by
    have k := IM.hear_at_flat eL e0
    rwa [IM.flatIx_scope hS hR O (by decide) 0] at k
  obtain ⟨tm, Rm, Cm, fm⟩ := Meaning.K2.fold_back (k := 338) f₀
  obtain ⟨rs0, gs0, d0⟩ := Meaning.K2.fold_next i0 fm f₀
  rw [Meaning.K2.h1_check (IM.k7_sits_yes hS hR O hj d0).1]
  exact (Meaning.K2.laid_at hS hR O (l := 24) (by decide) fm).2

/-- **msgs_at_cut_but's hM, IN SCOPE**: a block in front of the blocks behind the last link that
declares a round which draws positions: between the fold's two cuts the number of oracle messages
grows by what the block tells. -/
theorem adds_at_marked (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hT : K2Told)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List OpenedColumn} {j : Nat} {b : Block S Cl} (hj : j < 353)
    (hb : c.blocksInOrder[j]? = some b) (hp : b.planOk = true) (hm : Marked drawsPos b)
    {r₀ r₁ : S × List Fmt.RoundView × List OpenedColumn}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take j) (ProofFile.startS Z p) R C = .ok r₀)
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (j + 1)) (ProofFile.startS Z p) R C = .ok r₁) :
    r₁.1.st.oracles.size = r₀.1.st.oracles.size + toldMsgs b := by
  obtain ⟨n, hstep⟩ := step_of_cuts hb f₀ f₁
  obtain ⟨t₀, R₀, C₀⟩ := r₀
  obtain ⟨ls, -, -, -, eF⟩ := IM.blank_ground (IM.base_made O.made).2.2.1
  have hfl := front_len hS hR O
  have none_marked : ∀ {x : Block S Cl}, x.rounds = [] → Marked drawsPos x → False :=
    fun h0 ⟨r, hr, _⟩ => by rw [h0] at hr; cases hr
  have noPos : ∀ {x : Block S Cl}, (∀ r ∈ x.rounds, r.entry.poss = 0) → Marked drawsPos x →
      False := fun h0 ⟨r, hr, k⟩ => k (h0 r hr)
  have hcase := IM.flat_cases hS hR O j b hb
  cases hcase with
  | front b hr hd => exact (none_marked hr hm).elim
  | laid l hl b hr hd => exact (none_marked hr hm).elim
  | behind l hl Lk b e1 hr hd => exact (none_marked hr hm).elim
  | cleared l hl fs f b hfs hf hr hd => exact (none_marked hr hm).elim
  | batch l hl Lk q e1 hq hal =>
    exact (noPos (by rw [IM.alone_rounds (hal _)]; exact batch_poss q _) hm).elim
  | close l hl q Q i k b x hq hQ hk ex hla =>
    exact (noPos (by
      rw [IM.alone_rounds hla]
      exact closeOf_poss q Q (List.mem_of_getElem? ex)) hm).elim
  | back i k b b' name hk lot hp' hla => omega
  | last lot hla => omega
  | first l hl k b b' hk lot hp' hjn =>
    obtain ⟨L, hL, hb'⟩ := lot
    obtain ⟨fs, f, -, -, ep⟩ := hjn.planOk
    have hpb : b'.planOk = true := by
      rw [ep, Bool.and_eq_true] at hp
      exact hp.1
    have hk2 : b'.place.kind = KindName.K2 :=
      (marked_kind Z Bs.G₀ hL hb' hpb (marked_of_rounds hjn.rounds hm)).resolve_right
        (by rw [hp']; simp)
    obtain ⟨x, hx, rfl⟩ := IM.lot_K2 hL hb' hk2
    have hpl : x.place = { chain := 1, link := some l, piece := 1, kind := k } := hp'
    have hlk := (Meaning.K2.laid_at hS hR O hl f₀).2
    have Rr := Meaning.K2.open_recAll hS hR O (by omega) (by omega) f₀
    refine joined_lot_adds hjn (k2Is_adds hT (IM.k2_mem hx) (IM.retype_planOk x hpb).1
      (by rw [hpl]) fun Pp n hP hn st hst => ?_) hstep
    exact fence1_at hP hn hlk (by rw [eF]; exact Rr.walk.shape)
      (by rw [eF]; exact Rr.walk.groups) _ _ st hst
  | hear l hl i hi k b b' name hk lot hp' hla =>
    obtain ⟨L, hL, hb'⟩ := lot
    have hpb : b'.planOk = true := by rw [← IM.alone_planOk hla]; exact hp
    have hk2 : b'.place.kind = KindName.K2 :=
      (marked_kind Z Bs.G₀ hL hb' hpb (marked_of_rounds (IM.alone_rounds hla) hm)).resolve_right
        (by rw [hp']; simp)
    have ek : k = KindName.K2 := by rw [hp'] at hk2; exact hk2
    subst ek
    obtain ⟨rfl, rfl⟩ := hear_K2 hi hk
    obtain ⟨x, hx, rfl⟩ := IM.lot_K2 hL hb' hk2
    have hpl : x.place = { chain := 1, link := some 24, piece := 1 + 1, kind := .K2 } := hp'
    have hlk := head_link_at hS hR O f₀
    have Rr := Meaning.K2.open_recAll hS hR O (by decide) (by omega) f₀
    obtain ⟨rs', gs', hd⟩ := ChainEnd.step_decide 0 _ _ _ _ _ n hstep
    refine alone_adds hla (k2Is_adds hT (IM.k2_mem hx) (IM.retype_planOk x hpb).1
      (by rw [hpl]) (fun Pp n hP hn st hst => ?_) rs' gs' _) hd
    exact fence1_at hP hn hlk (by rw [eF]; exact Rr.walk.shape)
      (by rw [eF]; exact Rr.walk.groups) _ _ st hst

end

#print axioms fence1_at_link
#print axioms fence1_at_head
#print axioms k2Is_adds
#print axioms adds_at_marked

end Meaning.Carry
