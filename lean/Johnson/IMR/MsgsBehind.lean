-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/MsgsBehind.lean:
behind the last link: the five last blocks of the first chain's flat list (353 the
finish's code
switch · 354 the proximity test · 355 K13's batching · 356 W's commitment · 357 the seal): across
each, at the fold's own two states, the number of oracle messages grows by what the block tells, the
book has a place for each message, the count of roots grows by what the rounds declare. So the three
counts hold at every cut of the flat list, to the chain's end (counts_at_cut), in the goals' scope,
from the fold's return alone, under K1Told and K2Told. And the fence's first clause at the fold's
own states, by name, at all 25 code switches.

bookAt_whole stands in BookAtWhole.lean; this file does not stand over the table of joints
(Johnson/Desc/First/Borders.lean).
The tops, in scope (InScope P · readFiles P = .ok pp · an opening at OnBytes.secondHashFunction; ft = 0; from
ProofFile.startS Z p):
  counts_at_cut: **K1Told · K2Told · k ≤ 358 · every block of c.blocksInOrder.take k passes its test on the
      plan · the fold's return r ⇒ r.1.st.oracles.size = ((c.blocksInOrder.take k).map toldMsgs).sum ∧
      r.1.book.place.size = r.1.st.oracles.size ∧ r.1.roots = rootsOf (declOf (c.blocksInOrder.take k)).**
  
  fence1_link (the cut 14 l + 2, l < 25) · fence1_head (339) · fence1_finish (353: at the state
      behind the quiet step finishFrontQ): **Fence1 (IM.k2P Z a nm st n) n.sent ‹the fold's
      state›**, n the lot's numbers at that link.

  behind_step: the five as one step. adds_at_353 … adds_at_357: each. The
      roots' clauses at 353 and 354 are calls of Johnson/IMR/RootsWhole.lean's
        roots_behind_step, 354's
      ground is its finish_yes, and flat_len stands there.
At every o: roots_trees_at_cut: as many roots as trees at every cut of the whole list (over
open_front, chainBy_back, partsAt_baseAll, thePure_all,
at the sentence orderedP: the text of pureZ_flat (Johnson/IMR/KeepsSeat.lean) at an opening's own letters).
At every Z and G, or general:
  K12, the plan's side: deal_flatten (H2U.testOracles5's dealing, laid in a row again, is a first
      stretch of the list) · sent_two_tenants · sum_two · told_atFinish: **at a place that the maker
      lays, under the block's test on the plan, ownMask = false: toldMsgs (atFinish p) = 2 *
      (p.nums.stages.length - 1).** The state's side: atFinish_msgs
      (Johnson/Desc/K12/Law/MsgsAcross.lean); k12_out3's field "step"
      gives the places; atFinish_roots the roots. "The mask has come": Johnson/IMR/RootsWhole.lean's
          finish_yes.
  K2's finish: nums_facts_none · atMoment_end (behind the last link no message of a link is due) ·
      fence1_at_finish (by NoticesSent.lean's notices_sent; its premises are what finishFrontQ_fr,
      K2C/FinFront.lean, hands out) · finishLot_adds · finishLot_has (StillKeeps.lean's yes_has).
  K13 (its laws: below Johnson/Desc/K13/Law/): atM3_adds (atM3_book) · atM4_adds (atM4_seated,
      sendAtS_two; K1Told at W's place's numbers). bare_adds · back_zero_at.
deal_flatten, sum_two: general sentences on lists, typed here with no search of Lean's core or
Mathlib.
Premises: K1Told · K2Told: see Johnson/IMR/MsgsScope.lean's head.
Object · user · letters. Object: c := F.first, F := ProofFile.onlineDescription OnBytes.secondHashFunction's value, in scope;
not verify(). User: Johnson/IMR/BookAtWhole.lean; Johnson/IMR/N0AtCut.lean; whoever needs the
fence's first clause or
a count at a cut. Letters: none.
FinFront.lean (Johnson/Top/H0/Tw/K2C/), on which fence1_at_finish rests, states frame facts: its
head claims no soundness.
Compiled with the whole library.
Limits. In scope alone; ft = 0. No member: that a fold returns is shown of no proof. Book-keeping.
Nothing on soundness.
-/
import Johnson.IMR.MsgsScope
import Johnson.IMR.RootsWhole
import Johnson.Top.H0.Tw.K2C.FinFront
import Johnson.Desc.K12.Law.MsgsAcross
import Johnson.IMR.BookPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First hiding Col
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts atFinish)
open Johnson.G.OfPlan (rootsOf)
open ProofFile (Cl)

/-! ## 1 What the proximity test at the first chain's finish tells -/

/-- The dealing of a list of trees to the rounds, by each round's number of roots
(H2U.testOracles5's fold): laid in a row again it is a first stretch of the list. -/
theorem deal_flatten : ∀ (l : List Fmt.DeclaredRound)
    (acc : List (List VerifiableInference.Desc.Oracle)) (os : List VerifiableInference.Desc.Oracle),
    ((l.foldl (fun (a : List (List VerifiableInference.Desc.Oracle) ×
        List VerifiableInference.Desc.Oracle) r =>
      (a.2.take r.entry.roots :: a.1, a.2.drop r.entry.roots)) (acc, os)).1.reverse).flatten =
      acc.reverse.flatten ++ os.take (rootsOf l)
  | [], acc, os => by
    show acc.reverse.flatten = acc.reverse.flatten ++ os.take 0
    simp
  | r :: l, acc, os => by
    rw [List.foldl_cons, deal_flatten l]
    have e : rootsOf (r :: l) = r.entry.roots + rootsOf l := by
      unfold rootsOf
      rw [List.map_cons, List.sum_cons]
    rw [e, List.take_add, List.reverse_cons, List.flatten_append, List.append_assoc]
    simp

/-- Where the test does not send its own first mask every tree that it sends has two tenants. -/
theorem sent_two_tenants (N : H2U.TestNums) (g : Nat) (ho : N.ownMask = false) :
    ∀ o ∈ N.sentOracles g, o.tenants.length = 2 := by
  intro o h
  unfold H2U.TestNums.sentOracles at h
  rw [ho] at h
  simp only [List.nil_append, List.mem_map] at h
  obtain ⟨s, -, rfl⟩ := h
  rfl

theorem sum_two {l : List VerifiableInference.Desc.Oracle} (h : ∀ o ∈ l, o.tenants.length = 2) :
    (l.map fun o => o.tenants.length).sum = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, h a List.mem_cons_self,
      ih fun o ho => h o (List.mem_cons_of_mem _ ho), List.length_cons]
    omega

/-- **THE PLAN's SIDE AT K12**: at a place that the maker lays, under the block's test on the plan,
where the test does not send its own first mask: the block tells two oracle messages a switch. -/
theorem told_atFinish (place : Place) (x : H2U.PlaceNums)
    (hp : (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt place x) : Block T12 Unit).planOk = true)
    (ho : (H2U.proximityTestParametersAt place x).nums.ownMask = false) :
    toldMsgs (atFinish (H2U.proximityTestParametersAt place x)) = 2 * ((H2U.proximityTestParametersAt place x).nums.stages.length - 1) := by
  have e1 : (atFinish (H2U.proximityTestParametersAt place x)).oracles = (H2U.proximityTestParametersAt place x).oracles :=
    VerifiableInference.Desc.K12.k12_oracles guardedProximityTestParts _ hp
  have hr := VerifiableInference.Desc.K12.k12_rounds (Cl := Unit) guardedProximityTestParts _ hp
  have hd := VerifiableInference.Desc.K12.Coin.declared_of_plan _ hp ho
  have en := H2K.Made.nums_of_planOk place x hp
  -- the place's oracles are the dealing
  have e2 : ∃ g, (H2U.proximityTestParametersAt place x).oracles.flatten =
      ((H2U.proximityTestParametersAt place x).nums.sentOracles g).take
        (rootsOf (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt place x) : Block T12 Unit).rounds) := by
    rw [en] at hr ⊢
    generalize (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt place x) : Block T12 Unit).rounds = R at hr
    have hp' := hp
    unfold H2U.proximityTestParametersAt at hp' ⊢
    split
    · rename_i hc
      rw [if_pos hc] at hp'
      simp [proximityTestKind, H2U.noP12] at hp'
    · rename_i hc
      split
      · rename_i os hos
        refine ⟨x.firstGroup, ?_⟩
        unfold H2U.testOracles5 at hos
        rw [hr] at hos
        obtain rfl := Option.some.inj hos
        have k := deal_flatten R [] (x.nums.sentOracles x.firstGroup)
        simpa using k
      · rename_i hos
        rw [if_neg hc, hos] at hp'
        simp [proximityTestKind, H2U.noP12] at hp'
  obtain ⟨g, e2⟩ := e2
  unfold toldMsgs
  rw [e1, e2, sum_two fun o h => sent_two_tenants _ g ho o (List.mem_of_mem_take h)]
  have hlen : ((H2U.proximityTestParametersAt place x).nums.sentOracles g).length =
      (H2U.proximityTestParametersAt place x).nums.stages.length - 1 := by
    unfold H2U.TestNums.sentOracles
    rw [ho]
    simp
  rw [List.length_take, hlen]
  omega

/-! ## 2 The finish's code switch -/

theorem nums_facts_none {Pp : P1K2.Prep} {n : P1K2.Nums} (h : P1K2.numsAt Pp none = some n) :
    Pp.z.request.link.length ≠ 0 ∧ ∃ f lay, Pp.frames[Pp.z.request.link.length]? = some f ∧
      layTrees Pp.z.codes f.sent.toArray = some lay ∧ n.sent = f.sent.toArray ∧
      n.codes = Pp.z.codes := by
  unfold P1K2.numsAt at h
  dsimp only [Option.getD_none] at h
  split at h
  · cases h
  · rename_i h0
    obtain ⟨-, -, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨f, hf, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨lay, hl, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨read, -, h⟩ := Option.bind_eq_some_iff.1 h
    cases h
    exact ⟨by simpa using h0, f, lay, hf, hl, rfl, rfl⟩

/-- Behind the last link no message of a link is due. -/
theorem atMoment_end {f : ReqFrame} (h : f.link = f.shape.link.length) (m : Nat) :
    f.atMoment m = [] := by
  unfold ReqFrame.atMoment
  rw [h, List.getElem?_eq_none (Nat.le_refl _)]
  rfl

/-- **The fence's first clause at the finish's switch**: at a state that stands at the finish, whose
own copy of the frame has the plan's shape and groups, stands behind the last link, and whose noted
group is the frame's at that number. -/
theorem fence1_at_finish {Z : ProofFile.Pub} {G : ProofFile.Ground} {Pp : P1K2.Prep} {n : P1K2.Nums}
    (hP : P1K2.prepOf Z G = some Pp) (hn : P1K2.numsAt Pp none = some n) {t : S} {a₀ : FinOwn}
    {g : ReqGroup} (hb : t.here = .fin a₀) (hG : a₀.G = some g)
    (hg : a₀.fr.groups[a₀.fr.link]? = some g) (hl : a₀.fr.link = a₀.fr.shape.link.length)
    (hs : a₀.fr.shape = G.first.shape) (hgr : a₀.fr.groups = reqGroups G.first.shape) (a : Place)
    (nm : String) : Fence1 (IM.k2P Z a nm .finish n) n.sent t := by
  intro x hx
  obtain ⟨e1, -, e3⟩ := prep_facts hP
  obtain ⟨h0, f', lay, hf', -, es, -⟩ := nums_facts_none hn
  have el : a₀.fr.link = Pp.z.request.link.length := by rw [hl, hs, e1]
  rcases hx with ⟨hst, -⟩ | ⟨hst, -⟩ | ⟨-, a', g', ha, hG', rfl⟩
  · cases hst
  · cases hst
  · obtain rfl : a₀ = a' := Here.fin.inj (hb.symm.trans ha)
    obtain rfl : g = g' := Option.some.inj (hG.symm.trans hG')
    obtain ⟨nF, hF, eN⟩ := K2Hands.notices_sent Pp.z (Verify.subproofsWith G.W G.first.shape.link)
      a₀.fr (hs.trans e1.symm) (by rw [hgr, e1]) (by rw [el]; exact Nat.pos_of_ne_zero h0)
      (by rw [el]) g hg
    rw [← e3, el, hf'] at hF
    obtain rfl := Option.some.inj hF
    rw [atMoment_end hl] at eN
    show _root_.Tw.K2.switchNotices g.target #[foldMaskNotice (a₀.fr.foldShape a₀.fr.link {})] = _
    rw [es, ← eN]
    rfl

/-- **The lot's block at the finish** (a quiet step in front, the switch, a quiet step behind): a
yes adds what it tells, where the fence's first clause holds BEHIND THE QUIET STEP IN FRONT. -/
theorem finishLot_adds (hT : K2Told) {p : K2.P2} {nm : String} {a : Place}
    {sent : Array OracleNotice} {codes : Codes} {lay : TreeLay} {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hF : ∀ m, K2.finishFrontQ s = .ok m → Fence1 p sent m)
    (hs : p.sent = P1K2.oraclesAt p.grp codes sent) (hl : layTrees codes sent = some lay)
    (h : (IM.under nm a (K2.finishPlace p : Block S Unit)).decide s rs gs = .ok s') :
    s'.st.oracles.size = s.st.oracles.size +
      toldMsgs (IM.under nm a (K2.finishPlace p : Block S Unit)) := by
  obtain ⟨m₂, h12, h3⟩ := Keeps.ebind_ok h
  obtain ⟨m₁, h1, h2⟩ := Keeps.ebind_ok h12
  have e0 : m₁.st.oracles.size = s.st.oracles.size := K2.finishFrontQ_size h1
  have e1 := k2_adds_of_fence hT (hF m₁ h1) hs hl h2
  have e2 : s'.st.oracles.size = m₂.st.oracles.size := K2.finishBehindQ_size h3
  have e3 : toldMsgs (IM.under nm a (K2.finishPlace p : Block S Unit)) =
      toldMsgs (K2.codeSwitchKind p : Block S Unit) := by
    show toldMsgs (((roundlessBlock (p.name ++ ": front") p.place.chain p.place.link p.place.piece
      K2.finishFrontQ : Block S Unit).andThen p.name (K2.codeSwitchKind p)).andThen p.name
      (roundlessBlock (p.name ++ ": behind") p.place.chain p.place.link p.place.piece
        K2.finishBehindQ)) = _
    rw [toldMsgs_andThen, toldMsgs_andThen]
    show 0 + _ + 0 = _
    omega
  rw [e2, e1, e0, e3]

/-- Behind the lot's block at the finish the book has a place for each oracle message. -/
theorem finishLot_has {p : K2.P2} {nm : String} {a : Place} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (IM.under nm a (K2.finishPlace p : Block S Unit)).decide s rs gs = .ok s') :
    s'.book.place.size = s'.st.oracles.size := by
  obtain ⟨m₂, h12, h3⟩ := Keeps.ebind_ok h
  obtain ⟨m₁, -, h2⟩ := Keeps.ebind_ok h12
  have e1 : m₂.book.place.size = m₂.st.oracles.size := K2.yes_has h2
  have e2 : s'.st.oracles.size = m₂.st.oracles.size := K2.finishBehindQ_size h3
  rw [(K2.finishBehindQ_book h3).1, e2]
  exact e1

/-! ## 3 The three behind the proximity test -/

theorem atM3_adds {P : K13.Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K13.atM3 (Cl := Unit) P).decide s rs gs = .ok s') :
    s'.st.oracles.size = s.st.oracles.size + toldMsgs (K13.atM3 (Cl := Unit) P) := by
  have e : toldMsgs (K13.atM3 (Cl := Unit) P) = 0 := told_zero fun l hl => by
    have hl' : l ∈ ([] ++ List.replicate (2 + P.lin.kCol) []) ++
        ([] : List (List VerifiableInference.Desc.Oracle)) := hl
    simp only [List.nil_append, List.append_nil] at hl'
    exact (List.mem_replicate.1 hl').2
  rw [e, Nat.add_zero]
  exact (K13.Law.atM3_book h).2

theorem atM4_adds (h1 : K1Told) {P : K13.Where} {P' : K1.Par}
    (hp : (K13.atM4 (Cl := Unit) P (K1.sendAtS P')).planOk = true) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K13.atM4 (Cl := Unit) P (K1.sendAtS P')).decide s rs gs = .ok s') :
    s'.st.oracles.size = s.st.oracles.size +
      toldMsgs (K13.atM4 (Cl := Unit) P (K1.sendAtS P')) := by
  obtain ⟨s₁, a1, a2⟩ := Keeps.ebind_ok h
  obtain ⟨r₁, r₂, e⟩ := K13.Law.sendAtS_two P' a1
  have h3 : (K13.atM4 (Cl := Unit) P (K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s' := by
    show ((K1.sendAtS P' : Block S Unit).decide s [r₁, r₂] _).bind (fun m =>
      (K13.rowsB (Cl := Unit) K13.atS P).decide m [] _) = .ok s'
    rw [← e, a1]
    exact a2
  have hp' : ((K1.sendAtS P' : Block S Unit).planOk &&
      (K13.rowsB (Cl := Unit) K13.atS P).planOk) = true := hp
  rw [Bool.and_eq_true] at hp'
  have et : toldMsgs (K13.atM4 (Cl := Unit) P (K1.sendAtS P')) = P'.sent.size := by
    show toldMsgs ((K1.sendAtS P' : Block S Unit).andThen _ (K13.rowsB K13.atS P)) = _
    rw [toldMsgs_andThen]
    show ((K1.oracles P').flatten.map fun o => o.tenants.length).sum + 0 = _
    rw [Nat.add_zero]
    exact h1 P' hp'.1
  rw [et]
  exact (K13.Law.atM4_seated h3).msgs

/-! ## 4 In the goals' scope: the five blocks behind the last link -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- Chain.blocksInOrder's "bare" of a block that the seat lays alone over a lot's block x. -/
theorem bare_adds {same : S → S → Bool} {b : Block S Cl} {x : Block S Unit} {name : String}
    {a : Place} (h : IM.LaidAlone same b x.retype name a) {ft : Nat} {s t : S} {n : Nat}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    (hx : ∀ rs' gs, x.decide s rs' gs = .ok t →
      t.st.oracles.size = s.st.oracles.size + toldMsgs x)
    (hy : b.asBare.step ft s rs cols = .ok (t, n)) :
    t.st.oracles.size = s.st.oracles.size + toldMsgs b.asBare := by
  obtain ⟨rs', gs', hd⟩ := ChainEnd.step_decide ft _ s t rs cols n hy
  exact alone_adds h (hx rs' gs') hd

/-- The first block behind the links, with its place. -/
theorem back_zero_at (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∃ k0 x name, c.back[0]? = some k0 ∧ x ∈ P1K2.pureTable (fun _ _ => some none) Z Bs.G₀ ∧
      x.place.link = none ∧
      IM.LaidAlone ProofFile.sameReply k0 x.retype name
        { chain := 1, link := none, piece := 0 + 1, kind := .K2 } := by
  obtain ⟨-, -, -, hall⟩ := IM.base_made O.made
  obtain ⟨sv, hsv, -, hat⟩ := IM.chain_back_any hall (IM.makers_K9 Z Bs.G₀) O.places O.chain
  obtain rfl : sv = true := hsv.2 (IM.base_has_K13 O)
  obtain ⟨b, e, sp, -, L, hL, b', hb', -, ep, h⟩ := hat 0 .K2 rfl (by decide)
  obtain ⟨x, hx, rfl⟩ := IM.lot_K2 hL hb' (by rw [ep])
  have epx : x.place = { chain := 1, link := none, piece := 0 + 1, kind := .K2 } := ep
  exact ⟨b, x, _, e, hx, by rw [epx], h⟩

/-- **353: the finish's code switch.** -/
theorem adds_at_353 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hT : K2Told)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List OpenedColumn} {b : Block S Cl}
    (hb : c.blocksInOrder[353]? = some b) (hp : b.planOk = true) {r₀ r₁ : S × List Fmt.RoundView × List OpenedColumn}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok r₀)
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (353 + 1)) (ProofFile.startS Z p) R C = .ok r₁) :
    r₁.1.st.oracles.size = r₀.1.st.oracles.size + toldMsgs b ∧
      r₁.1.book.place.size = r₁.1.st.oracles.size ∧
      r₁.1.roots = r₀.1.roots + rootsOf b.rounds := by
  obtain ⟨n, hstep⟩ := step_of_cuts hb f₀ f₁
  obtain ⟨ls, -, -, -, eF⟩ := IM.blank_ground (IM.base_made O.made).2.2.1
  obtain ⟨k0, x, name, e0, hx, hln, hla⟩ := back_zero_at O
  obtain rfl := Option.some.inj (((IM.back_numbers hS hR O).1 0 k0 e0).symm.trans hb)
  have hpb : (x.retype : Block S Cl).planOk = true := by
    have a1 : (k0.planOk && k0.hasNoClaimsAndNothingAfter) = true := hp
    rw [Bool.and_eq_true] at a1
    rw [← IM.alone_planOk hla]
    exact a1.1
  have Rr := Meaning.K2.open_recAll hS hR O (by decide) (by rw [front_len hS hR O]) f₀
  obtain ⟨rs₁, gs₁, hd⟩ := ChainEnd.step_decide 0 _ _ _ _ _ n hstep
  have hdx : x.decide r₀.1 rs₁ gs₁ = .ok r₁.1 := (IM.alone_underR hla).2 _ _ _ _ hd
  refine ⟨bare_adds hla (fun rs' gs h => ?_) hstep, ?_, ?_⟩
  rotate_left
  · obtain ⟨Pp, nn, -, -, arms⟩ := (IM.k2_mem hx).live (IM.retype_planOk x hpb).1
    rcases arms with ⟨-, ex⟩ | ⟨l', HP, el, -, -⟩ | ⟨l', el, -⟩
    · rw [ex] at hdx
      exact finishLot_has hdx
    · rw [hln] at el
      cases el
    · rw [hln] at el
      cases el
  · exact roots_behind_step hS hR O (by decide) (by decide) hb hp f₀ f₁
  obtain ⟨Pp, nn, hP, hn, arms⟩ := (IM.k2_mem hx).live (IM.retype_planOk x hpb).1
  rw [hln] at hn
  obtain ⟨-, f', ly, -, hlay, es, ec⟩ := nums_facts_none hn
  have hlay' : layTrees nn.codes nn.sent = some ly := by rw [ec, es]; exact hlay
  rcases arms with ⟨-, ex⟩ | ⟨l', HP, el, -, -⟩ | ⟨l', el, -⟩
  · rw [ex] at h ⊢
    refine finishLot_adds hT (fun m hm => ?_) rfl hlay' h
    obtain ⟨a, g, ha, hG, hg, hl, hs, -, hgr, -⟩ := K2.finishFrontQ_fr hm
    exact fence1_at_finish hP hn ha hG hg hl (by rw [hs, eF]; exact Rr.walk.shape)
      (by rw [hgr, eF]; exact Rr.walk.groups) _ _
  · rw [hln] at el
    cases el
  · rw [hln] at el
    cases el

/-- **354: the proximity test at the first chain's finish.** -/
theorem adds_at_354 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {ft : Nat} {s : S} {R : List Fmt.RoundView} {C : List OpenedColumn} {b : Block S Cl}
    (hb : c.blocksInOrder[354]? = some b) (hp : b.planOk = true) {r₀ r₁ : S × List Fmt.RoundView × List OpenedColumn}
    (f₀ : foldBlocks ft (c.blocksInOrder.take 354) s R C = .ok r₀)
    (f₁ : foldBlocks ft (c.blocksInOrder.take (354 + 1)) s R C = .ok r₁) :
    r₁.1.st.oracles.size = r₀.1.st.oracles.size + toldMsgs b ∧
      r₁.1.book.place.size = r₁.1.st.oracles.size ∧
      r₁.1.roots = r₀.1.roots + rootsOf b.rounds := by
  obtain ⟨hpk, ho, ⟨Ps, ep⟩, hm, ⟨rs, gs, y1⟩, -, eo⟩ := finish_yes hS hR O hb hp f₀ f₁
  refine ⟨?_, ?_, roots_behind_step hS hR O (by decide) (by decide) hb hp f₀ f₁⟩
  · have et : toldMsgs b = toldMsgs (atFinish (H2U.p12OfMade Z.made)) := by
      unfold toldMsgs
      rw [eo]
    rw [et, H2K.Out.atFinish_msgs _ hpk _ _ _ _ hm y1]
    have hp' := hpk
    have ho' := ho
    rw [ep] at hp' ho' ⊢
    rw [told_atFinish _ _ hp' ho']
  · obtain ⟨o, tE, -, -, -, hd, e⟩ := VerifiableInference.Desc.K12.Seat.atFinish_ok _ _ _ _ _ y1
    have k3 := (H2K.Out.k12_out3 _ (H2K.JointK.early_of_planOk _ hpk)
      (H2K.JointK.answers_of_planOk _ hpk) _ tE _ _ hd).step
    rw [e]
    exact k3.symm

/-- **355, 356, 357: K13's batching, W's commitment, the seal.** Each: the number of oracle messages
grows by what the block tells; the book has a place for each message behind, if it had in front;
the count of roots grows by what the rounds declare. -/
theorem adds_at_355 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : Nat} {s : S}
    {R : List Fmt.RoundView} {C : List OpenedColumn} {b : Block S Cl} (hb : c.blocksInOrder[355]? = some b)
    {r₀ r₁ : S × List Fmt.RoundView × List OpenedColumn}
    (f₀ : foldBlocks ft (c.blocksInOrder.take 355) s R C = .ok r₀)
    (f₁ : foldBlocks ft (c.blocksInOrder.take (355 + 1)) s R C = .ok r₁) :
    r₁.1.st.oracles.size = r₀.1.st.oracles.size + toldMsgs b ∧
      (r₀.1.book.place.size = r₀.1.st.oracles.size →
        r₁.1.book.place.size = r₁.1.st.oracles.size) ∧
      r₁.1.roots = r₀.1.roots + rootsOf b.rounds := by
  obtain ⟨n, hstep⟩ := step_of_cuts hb f₀ f₁
  obtain ⟨-, -, ⟨k2, k2', e2, -, eb2, hl2⟩, -⟩ := IM.back_of O
  obtain rfl := Option.some.inj (((IM.back_numbers hS hR O).1 2 k2 e2).symm.trans hb)
  subst eb2
  obtain ⟨rs', gs', hd⟩ := ChainEnd.step_decide ft _ _ _ _ _ n hstep
  have hd' : (K13.atM3 (Cl := Unit) (K13.whereOf Z)).decide r₀.1 rs' gs' = .ok r₁.1 :=
    (IM.alone_underR hl2).2 _ _ _ _ hd
  have hbk := K13.Law.atM3_book hd'
  refine ⟨alone_adds hl2 (fun _ => atM3_adds hd') hd, fun h => by rw [hbk.1, hbk.2]; exact h, ?_⟩
  show r₁.1.roots = r₀.1.roots + rootsOf k2.rounds
  rw [IM.alone_rounds hl2]
  exact K13.Law.atM3_roots hd'

theorem adds_at_356 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (h1 : K1Told) {ft : Nat} {s : S}
    {R : List Fmt.RoundView} {C : List OpenedColumn} {b : Block S Cl} (hb : c.blocksInOrder[356]? = some b)
    (hp : b.planOk = true) {r₀ r₁ : S × List Fmt.RoundView × List OpenedColumn}
    (f₀ : foldBlocks ft (c.blocksInOrder.take 356) s R C = .ok r₀)
    (f₁ : foldBlocks ft (c.blocksInOrder.take (356 + 1)) s R C = .ok r₁) :
    r₁.1.st.oracles.size = r₀.1.st.oracles.size + toldMsgs b ∧
      r₁.1.book.place.size = r₁.1.st.oracles.size ∧
      r₁.1.roots = r₀.1.roots + rootsOf b.rounds := by
  obtain ⟨n, hstep⟩ := step_of_cuts hb f₀ f₁
  obtain ⟨-, -, -, ⟨k3, k3', w, e3, -, hw, eb3, hl3⟩⟩ := IM.back_of O
  obtain rfl := Option.some.inj (((IM.back_numbers hS hR O).1 3 k3 e3).symm.trans hb)
  subst eb3
  obtain ⟨P', rfl⟩ : ∃ P' : K1.Par, w = K1.sendAtS P' := by
    obtain ⟨msg, -, e⟩ := (K13.Law.wAt_is _ _ _ w).1 hw
    exact ⟨_, e⟩
  obtain ⟨rs', gs', hd⟩ := ChainEnd.step_decide ft _ _ _ _ _ n hstep
  have hd' : (K13.atM4 (Cl := Unit) (K13.whereOf Z) (K1.sendAtS P')).decide r₀.1 rs' gs' =
      .ok r₁.1 := (IM.alone_underR hl3).2 _ _ _ _ hd
  have hpx : (K13.atM4 (Cl := Unit) (K13.whereOf Z) (K1.sendAtS P')).planOk = true := by
    have a1 : (k3.planOk && k3.hasNoClaimsAndNothingAfter) = true := hp
    rw [Bool.and_eq_true] at a1
    exact (IM.retype_planOk _ (by rw [← IM.alone_planOk hl3]; exact a1.1)).1
  have em := atM4_adds h1 hpx hd'
  refine ⟨alone_adds hl3 (fun _ => em) hd, ?_, ?_⟩
  · obtain ⟨s₁, a1, a2⟩ := Keeps.ebind_ok hd'
    obtain ⟨q₁, q₂, e⟩ := K13.Law.sendAtS_two P' a1
    have h3 : (K13.atM4 (Cl := Unit) (K13.whereOf Z) (K1.sendAtS P')).decide r₀.1 [q₁, q₂] gs' =
        .ok r₁.1 := by
      show ((K1.sendAtS P' : Block S Unit).decide r₀.1 [q₁, q₂] _).bind (fun m =>
        (K13.rowsB (Cl := Unit) K13.atS (K13.whereOf Z)).decide m [] _) = .ok r₁.1
      rw [← e, a1]
      exact a2
    have Sd := K13.Law.atM4_seated h3
    rw [Sd.seated.count, ← Sd.seated.step, Sd.msgs]
  · show r₁.1.roots = r₀.1.roots + rootsOf k3.rounds
    rw [IM.alone_rounds hl3]
    exact K13.Law.atM4_roots hd'

theorem adds_at_357 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {ft : Nat} {s : S}
    {R : List Fmt.RoundView} {C : List OpenedColumn} {b : Block S Cl} (hb : c.blocksInOrder[357]? = some b)
    {r₀ r₁ : S × List Fmt.RoundView × List OpenedColumn}
    (f₀ : foldBlocks ft (c.blocksInOrder.take 357) s R C = .ok r₀)
    (f₁ : foldBlocks ft (c.blocksInOrder.take (357 + 1)) s R C = .ok r₁) :
    r₁.1 = r₀.1 ∧ toldMsgs b = 0 ∧ rootsOf b.rounds = 0 := by
  obtain ⟨n, hstep⟩ := step_of_cuts hb f₀ f₁
  obtain ⟨kL, -, ebL, hlL⟩ := IM.seal_seated O
  obtain rfl := Option.some.inj ((IM.back_numbers hS hR O).2.symm.trans hb)
  subst ebL
  obtain ⟨rs', gs', hd⟩ := ChainEnd.step_decide ft _ _ _ _ _ n hstep
  have hd' := (IM.alone_underR hlL).2 _ _ _ _ hd
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨_, -, e⟩ := Keeps.emap_ok hd'
    exact e.symm
  · show toldMsgs c.last = 0
    unfold toldMsgs
    rw [IM.alone_oracles hlL]
    rfl
  · show rootsOf c.last.rounds = 0
    rw [IM.alone_rounds hlL]
    rfl

/-- **THE FIVE, AS ONE STEP.** -/
theorem behind_step (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (h1 : K1Told) (hT : K2Told)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List OpenedColumn} {j : Nat} {b : Block S Cl}
    (h353 : 353 ≤ j) (h358 : j < 358) (hb : c.blocksInOrder[j]? = some b) (hp : b.planOk = true)
    {r₀ r₁ : S × List Fmt.RoundView × List OpenedColumn}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take j) (ProofFile.startS Z p) R C = .ok r₀)
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (j + 1)) (ProofFile.startS Z p) R C = .ok r₁) :
    r₁.1.st.oracles.size = r₀.1.st.oracles.size + toldMsgs b ∧
      (r₀.1.book.place.size = r₀.1.st.oracles.size →
        r₁.1.book.place.size = r₁.1.st.oracles.size) ∧
      r₁.1.roots = r₀.1.roots + rootsOf b.rounds := by
  obtain rfl | rfl | rfl | rfl | rfl : j = 353 ∨ j = 354 ∨ j = 355 ∨ j = 356 ∨ j = 357 := by omega
  · obtain ⟨a1, a2, a3⟩ := adds_at_353 hS hR O hT hb hp f₀ f₁
    exact ⟨a1, fun _ => a2, a3⟩
  · obtain ⟨a1, a2, a3⟩ := adds_at_354 hS hR O hb hp f₀ f₁
    exact ⟨a1, fun _ => a2, a3⟩
  · exact adds_at_355 hS hR O hb f₀ f₁
  · obtain ⟨a1, a2, a3⟩ := adds_at_356 hS hR O h1 hb hp f₀ f₁
    exact ⟨a1, fun _ => a2, a3⟩
  · obtain ⟨a1, a2, a3⟩ := adds_at_357 hS hR O hb f₀ f₁
    rw [a1, a2, a3]
    exact ⟨rfl, id, rfl⟩

/-- **THE THREE COUNTS AT EVERY CUT OF THE FIRST CHAIN's FLAT LIST, TO ITS END, IN SCOPE.** -/
theorem counts_at_cut (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (h1 : K1Told) (hT : K2Told)
    (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List OpenedColumn) :
    ∀ (k : Nat), k ≤ 358 → (∀ b ∈ c.blocksInOrder.take k, b.planOk = true) →
      ∀ r : S × List Fmt.RoundView × List OpenedColumn,
        foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok r →
        r.1.st.oracles.size = ((c.blocksInOrder.take k).map toldMsgs).sum ∧
          r.1.book.place.size = r.1.st.oracles.size ∧
          r.1.roots = rootsOf (H2K.First.declOf (c.blocksInOrder.take k)) := by
  intro k
  induction k with
  | zero =>
    intro _ hp r h
    have hk : 0 ≤ (Meaning.K2.frontOf c).length := Nat.zero_le _
    have e1 := roots_at_cut_paid O 0 hk hp 0 _ R C r h
    rw [(Meaning.K2.start_empty O.pub p).2, Nat.zero_add] at e1
    exact ⟨msgs_at_cut_scope hS hR O h1 hT (Nat.zero_le _) hp p R C r h,
      Meaning.K2.open_has O hk h, e1⟩
  | succ k ih =>
    intro hk hp r h
    by_cases hf : k + 1 ≤ 353
    · have hk' : k + 1 ≤ (Meaning.K2.frontOf c).length := by rw [front_len hS hR O]; exact hf
      have e1 := roots_at_cut_paid O (k + 1) hk' hp 0 _ R C r h
      rw [(Meaning.K2.start_empty O.pub p).2, Nat.zero_add] at e1
      exact ⟨msgs_at_cut_scope hS hR O h1 hT hf hp p R C r h, Meaning.K2.open_has O hk' h, e1⟩
    · obtain ⟨b, hb⟩ : ∃ b, c.blocksInOrder[k]? = some b :=
        ⟨_, List.getElem?_eq_getElem (by rw [flat_len hS hR O]; omega)⟩
      have e : c.blocksInOrder.take (k + 1) = c.blocksInOrder.take k ++ [b] := by
        rw [List.take_add_one, hb]
        rfl
      obtain ⟨t, rs, cs⟩ := r
      obtain ⟨t₀, r₀, c₀, f₀⟩ := Meaning.K2.fold_back h
      obtain ⟨i1, i2, i3⟩ := ih (by omega)
        (fun x hx => hp x (by rw [e]; exact List.mem_append_left _ hx)) _ f₀
      obtain ⟨a1, a2, a3⟩ := behind_step hS hR O h1 hT (by omega) (by omega) hb
        (hp b (by rw [e]; exact List.mem_append_right _ List.mem_cons_self)) f₀ h
      refine ⟨?_, a2 i2, ?_⟩
      · rw [a1, i1, e, List.map_append, List.sum_append]
        simp
      · rw [a3, i3, e]
        show _ = rootsOf ((c.blocksInOrder.take k ++ [b]).flatMap (·.rounds))
        rw [List.flatMap_append, H2K.First.rootsOf_append]
        simp [H2K.First.declOf]

/-- As many roots as trees, at every cut of the whole flat list: the walk over the whole first chain
(the text of KeepsSeat.lean's pureZ_flat, at the sentence orderedP), at an opening's own letters. -/
theorem roots_trees_at_cut {o : ProofFile.SecondHashFunctionArgument} {pol KL : ByteArray}
    (O : IM.Open o pol lay KL F Z Bs base c A B) (k : Nat)
    (hp : ∀ b ∈ c.blocksInOrder.take k, b.planOk = true) (ft : Nat) (p : ProofFile.InstPub) (R : List Fmt.RoundView)
    (C : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok r) :
    r.1.roots = r.1.book.trees.size := by
  have H : Meaning.K2.BookLaw Meaning.K2.orderedP :=
    ⟨Meaning.K2.recv_ordered, fun A B r hs k => K2.ordered_same 0 A B r hs k,
      Meaning.K2.k12_ordered⟩
  have H' := Meaning.K2.seatKeeps_sentence H
  have hall := Meaning.K2.all_of_made (IM.base_made O.made).2.2.2
  have h0 := Meaning.K2.pub_firstTree (o := o) (pol := pol) (lay := lay) (KL := KL) O.pub
  have K₀ : Meaning.K2.LotsKeep _ (ProofFile.pureSeat o Z).lots Bs.G₀ :=
    Meaning.K2.thePure_keeps H' Z trivial h0 Bs.G₀ fun _ _ _ => trivial
  have Ka : Meaning.K2.LotsAll _ (ProofFile.pureSeat o Z).lots Bs.G₀ :=
    Meaning.K2.thePure_all H' (Meaning.K2.seatBack_sentence H) Z trivial h0 Bs.G₀
      fun _ _ _ => trivial
  have K : ∀ b ∈ c.blocksInOrder, b.planOk = true → Keeps.Decides (Meaning.K2.PR Meaning.K2.orderedP) b := by
    intro b hb hpb
    rw [Meaning.K2.flat_eq (Meaning.K2.chainBy_noFront O.chain)] at hb
    rcases List.mem_append.1 hb with q | q
    · exact (Meaning.K2.open_front H' O trivial fun _ _ _ => trivial).2 b q
    · exact Meaning.K2.chainBy_back H'.trans O.chain
        (Meaning.K2.partsAt_baseAll H'.refl Ka hall O.places) (Meaning.K2.partsAt_frames K₀ hall) b
        q hpb
  have k1 := Keeps.foldBlocks_keeps _ H'.refl H'.trans ft _
    (fun b hb => K b (List.mem_of_mem_take hb) (hp b hb)) _ R C r h
  refine (k1 ?_).1
  show Meaning.K2.orderedP (ProofFile.startS Z p).book (ProofFile.startS Z p).roots
  rw [(Meaning.K2.start_empty O.pub p).1, (Meaning.K2.start_empty O.pub p).2]
  exact Meaning.K2.empty_ordered

/-! ## 5 The fence's first clause at the fold's own states, by name -/

/-- **AT THE CUT IN FRONT OF LINK l's FIRST ENTRY** (14 l + 2). -/
theorem fence1_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    {Pp : P1K2.Prep} {n : P1K2.Nums} (hP : P1K2.prepOf Z Bs.G₀ = some Pp)
    (hn : P1K2.numsAt Pp (some l) = some n) (a : Place) (nm : String) (st : K2.At)
    (hst : st ≠ K2.At.finish) : Fence1 (IM.k2P Z a nm st n) n.sent t₀ := by
  have Rr := Meaning.K2.open_recAll hS hR O (by omega) (by rw [front_len hS hR O]; omega) f₀
  exact fence1_at hP hn (Meaning.K2.laid_at hS hR O hl f₀).2 (by rw [O.first]; exact Rr.walk.shape)
    (by rw [O.first]; exact Rr.walk.groups) a nm st hst

/-- **AT THE CUT IN FRONT OF THE HEAD's LINK's SWITCH** (339). -/
theorem fence1_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    {Pp : P1K2.Prep} {n : P1K2.Nums} (hP : P1K2.prepOf Z Bs.G₀ = some Pp)
    (hn : P1K2.numsAt Pp (some 24) = some n) (a : Place) (nm : String) (st : K2.At)
    (hst : st ≠ K2.At.finish) : Fence1 (IM.k2P Z a nm st n) n.sent t₀ := by
  have Rr := Meaning.K2.open_recAll hS hR O (by decide) (by rw [front_len hS hR O]; decide) f₀
  exact fence1_at hP hn (head_link_at hS hR O f₀) (by rw [O.first]; exact Rr.walk.shape)
    (by rw [O.first]; exact Rr.walk.groups) a nm st hst

/-- **AT THE FINISH** (the cut 353): at the state behind the quiet step in front of the switch. -/
theorem fence1_finish (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    {Pp : P1K2.Prep} {n : P1K2.Nums} (hP : P1K2.prepOf Z Bs.G₀ = some Pp)
    (hn : P1K2.numsAt Pp none = some n) (a : Place) (nm : String) {m : S}
    (hm : K2.finishFrontQ t₀ = .ok m) : Fence1 (IM.k2P Z a nm .finish n) n.sent m := by
  have Rr := Meaning.K2.open_recAll hS hR O (by decide) (by rw [front_len hS hR O]) f₀
  obtain ⟨a', g, ha, hG, hg, hl, hs, -, hgr, -⟩ := K2.finishFrontQ_fr hm
  exact fence1_at_finish hP hn ha hG hg hl (by rw [hs, O.first]; exact Rr.walk.shape)
    (by rw [hgr, O.first]; exact Rr.walk.groups) a nm

end

#print axioms told_atFinish
#print axioms fence1_at_finish
#print axioms finishLot_adds
#print axioms atM4_adds
#print axioms adds_at_353
#print axioms adds_at_354
#print axioms adds_at_355
#print axioms adds_at_356
#print axioms adds_at_357
#print axioms behind_step
#print axioms counts_at_cut
#print axioms roots_trees_at_cut
#print axioms fence1_link
#print axioms fence1_head
#print axioms fence1_finish

end Meaning.Carry
