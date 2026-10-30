-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/HstReached.lean: code switching (K2): THE STATE's SIDE OF WHAT IS OWED ON THE
TABLE's NUMBERS, AT REACHED STATES (Johnson/P1K2R/HstInScope.lean), WITH EVERY PREMISE ON A STATE
ASKED AT «REACHED» STATES ALONE: over Johnson/P1K2R/FoldSideR.lean in the place of
FoldSide.lean. The count and the shapes at the switch's own number are asked OF THE STATE s ITSELF;
the count at the switch before, and the shapes in front of the last closing at the kept old
numbers, of every state that Reach has at that one earlier number from the same public part z.
  sw_link · sw_head · sw_finish  THE FIRST TWO CLAUSES ALONE (SwState · what the switch announces is
               n.sent): they ask nothing at any cut, and neither hcs nor (but at the finish) hsh
  SwLinkCutsR · SwHeadCutsR · SwFinishCutsR  what foldSideR_one | _link · _head · _fin ask, each as
               one Lean structure, at z and s
  linkCutsR_of_cuts · headCutsR_of_cuts · finishCutsR_of_cuts  HstInScope.lean's …Cuts at z give
               them at every s reached from z: so whatever pays those pays these
  hst_link_reached · hst_head_reached · hst_finish_reached  the three arms; the ends are
               hst_link | hst_head | hst_finish's to the letter
  d_link_reached · d_head_reached · d_finish_reached  d_link | d_head | d_finish (DebtsAt.lean) with
               hst gone: hFk: where the fence Fk holds, the state is reached from a z, and the
               …CutsR hold at z and that state
WHY. A law along the switches can pay «each message has the listed shape» at the state in front of
switch j out of what it has shown at the switches before j; it cannot pay it at every return of the
fold. SwLinkCutsR asks two counts (in front of the switches into groups m and m + 1), where
SwLinkCuts asks 23.
THE OTHER PREMISES STAY: in scope, the files read, the opening O · hF · hpl · hcs · hsh · in d_…:
the six closed premises.
LIMITS. Joins: every step is a call. No premise is shown met at a real value: no example. The second
and third clause say nothing at a state of which the switch's text makes no front. No probability;
no soundness is claimed.
-/
import Johnson.P1K2R.HstInScope
import Johnson.P1K2R.FoldSideR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription Place)
open VerifiableInference.Desc.First (S ModelPart Numbers blockPlaces possAt)
open VerifiableInference.Desc.First.K2 (SwState frontAt frameAt finishFrontQ frontOf_iff LinkDebts
  SwitchDebts sentFitB)
open VerifiableInference.Desc.First.K2Hands (csW MW frontB2)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit keptTyped_at one_answer_of_test)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Johnson.G (fxAt)
open IM (XK linksW placesW k2P)
open _root_.Tw.K2 (firstFront switchNotices)
open ProofFile (Cl)

/-- **What foldSideR_one | foldSideR_link ask**, at the switch into group m + 1, of the state s in
front of it and of the states reached earlier from the same public part z. -/
structure SwLinkCutsR (Z : ProofFile.Pub) (c : Chain S Cl) (z : ProofFile.InstPub) (m : ℕ) (s : S) : Prop where
  before : 1 ≤ m → ∀ t, Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * m + 2) (z, t) →
    t.st.oracles.size = VerifiableInference.Desc.First.K2.n0At m
  count : s.st.oracles.size = VerifiableInference.Desc.First.K2.n0At (m + 1)
  shapes : ∀ o, o < s.st.oracles.size → (s.st.oracles[o]?).map (·.shape) = MW[o]?
  olds : ∀ t, Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * m + 12) (z, t) →
    ∀ o ∈ VerifiableInference.Desc.First.K2.oldsAt (m + 1),
      (t.st.oracles[o]?).map (·.shape) = MW[o]?

/-- **What foldSideR_head asks.** -/
structure SwHeadCutsR (Z : ProofFile.Pub) (c : Chain S Cl) (z : ProofFile.InstPub) (s : S) : Prop where
  before : ∀ t, Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 324 (z, t) →
    t.st.oracles.size = VerifiableInference.Desc.First.K2.n0At 23
  count : s.st.oracles.size = VerifiableInference.Desc.First.K2.n0At 24
  shapes : ∀ o, o < s.st.oracles.size → (s.st.oracles[o]?).map (·.shape) = MW[o]?
  olds : ∀ t, Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 334 (z, t) →
    ∀ o ∈ VerifiableInference.Desc.First.K2.oldsAt 24, (t.st.oracles[o]?).map (·.shape) = MW[o]?

/-- **What foldSideR_fin asks**: of the state in front of the finish's switch alone. -/
structure SwFinishCutsR (s : S) : Prop where
  count : s.st.oracles.size = VerifiableInference.Desc.First.K2.n0At 25
  shapes : ∀ o, o < s.st.oracles.size → (s.st.oracles[o]?).map (·.shape) = MW[o]?

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-! ## The …Cuts at z give the …CutsR at every state reached from z -/

theorem linkCutsR_of_cuts {m : ℕ} (h23 : m < 23) (K : SwLinkCuts Z c z m) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s)) :
    SwLinkCutsR Z c z m s := by
  obtain ⟨-, R, C, f⟩ := (reach_raw hr).fold
  refine ⟨fun h1 t ht => ?_, K.counts (m + 1) (by omega) (by omega) _ _ _ _ _ f,
    K.shapes _ _ _ _ _ f, fun t ht => ?_⟩
  · obtain ⟨-, R', C', f'⟩ := (reach_raw ht).fold
    exact K.counts m h1 (by omega) _ _ _ _ _ f'
  · obtain ⟨-, R', C', f'⟩ := (reach_raw ht).fold
    exact K.olds _ _ _ _ _ f'

theorem headCutsR_of_cuts (K : SwHeadCuts Z c z) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) : SwHeadCutsR Z c z s := by
  obtain ⟨-, R, C, f⟩ := (reach_raw hr).fold
  refine ⟨fun t ht => ?_, K.count24 _ _ _ _ _ f, K.shapes _ _ _ _ _ f, fun t ht => ?_⟩
  · obtain ⟨-, R', C', f'⟩ := (reach_raw ht).fold
    exact K.count23 _ _ _ _ _ f'
  · obtain ⟨-, R', C', f'⟩ := (reach_raw ht).fold
    exact K.olds _ _ _ _ _ f'

theorem finishCutsR_of_cuts (K : SwFinishCuts Z c z) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s)) : SwFinishCutsR s := by
  obtain ⟨-, R, C, f⟩ := (reach_raw hr).fold
  exact ⟨K.count _ _ _ _ _ f, K.shapes _ _ _ _ _ f⟩

/-! ## The first two clauses alone -/

/-- **AT THE SWITCH INTO GROUP m + 1, m < 23: THE SIX FACTS AND THE NOTICES.** -/
theorem sw_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    {m : ℕ} (h23 : m < 23) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s)) :
    SwState Z.first.shape (m + 1) n.codes s ∧
      ∀ x, firstFront s.st s.check.frame = .ok x → switchNotices x.T x.others = n.sent := by
  obtain ⟨hG, hA⟩ := both_at_open O hF hpl (by rw [Meaning.Carry.front_len hS hR O]; omega) hr
  have Q := Meaning.K2.swState_link_reach hS hR O (l := m + 1) (by omega) hr hG hA
  rw [← codes_at O hP hn] at Q
  exact ⟨Q, fun x hx => Meaning.Carry.fence1_at_link hP hn Q.link (by rw [Q.shape, O.first])
    (by rw [Q.groups, Q.shape, O.first]) default "" x (Or.inl ⟨rfl, hx⟩)⟩

/-- **AT THE OUTPUT HEAD's SWITCH.** -/
theorem sw_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (a : Place) (nm : String) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some 24) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) :
    SwState Z.first.shape 24 n.codes s ∧
      ∀ x, frontAt (k2P Z a nm .head n) s = some x → switchNotices x.T x.others = n.sent := by
  obtain ⟨hG, hA⟩ := both_at_open O hF hpl (by rw [Meaning.Carry.front_len hS hR O]; omega) hr
  have Q := Meaning.K2.swState_head_reach hS hR O hr hG hA
  rw [← codes_at O hP hn] at Q
  exact ⟨Q, fun x hx => Meaning.Carry.fence1_at_head hP hn Q.link (by rw [Q.shape, O.first])
    (by rw [Q.groups, Q.shape, O.first]) a nm x (frontOf_iff.2 hx)⟩

/-- **AT THE FINISH's SWITCH.** h25: the public part's shape has 25 links. -/
theorem sw_finish (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (h25 : Z.first.shape.link.length = 25) (a : Place) (nm : String)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp none = some n)
    {s t : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : finishFrontQ s = .ok t) :
    SwState Z.first.shape 25 n.codes s ∧
      ∀ x, frontAt (k2P Z a nm .finish n) t = some x → switchNotices x.T x.others = n.sent := by
  have hlen : 353 ≤ (Meaning.K2.frontOf c).length := by rw [Meaning.Carry.front_len hS hR O]
  obtain ⟨hG, hA⟩ := both_at_open O hF hpl hlen hr
  have Q := Meaning.K2.swState_finish_reach hS hR O hr hlen h25 he hG hA
  rw [← codes_at O hP hn] at Q
  refine ⟨Q, fun x hx => ?_⟩
  obtain ⟨a₀, g, ha, hg, hgr, hl, hs, -, hfg, -⟩ :=
    VerifiableInference.Desc.First.K2.finishFrontQ_fr he
  exact Meaning.Carry.fence1_at_finish hP hn ha hg hgr hl (by rw [hs, Q.shape, O.first])
    (by rw [hfg, Q.groups, Q.shape, O.first]) a nm x (frontOf_iff.2 hx)

/-! ## The three arms -/

/-- **AT THE SWITCH INTO GROUP m + 1, m < 23.** -/
theorem hst_link_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW)
    (hsh : Z.first.shape = VerifiableInference.Desc.First.K2Hands.shW) {m : ℕ} (h23 : m < 23)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp)
    (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (K : SwLinkCutsR Z c z m s) :
    SwState Z.first.shape (m + 1) n.codes s ∧
      (∀ x, firstFront s.st s.check.frame = .ok x → switchNotices x.T x.others = n.sent) ∧
      ∀ x W, firstFront s.st s.check.frame = .ok x → frameAt x = some W → ∀ κ ∈ W.kept,
        ∃ xo : OnBytes.Oracle, x.st.oracles[κ.old]? = some xo ∧ xo.shape.answers = 1 := by
  obtain ⟨Q, N⟩ := sw_link hS hR O hF hpl h23 hP hn hr
  refine ⟨Q, N, fun x W hx hW => ?_⟩
  have hfx : frontAt (k2P Z default "" .link n) s = some x := frontOf_iff.1 (Or.inl ⟨rfl, hx⟩)
  obtain ⟨r, hrw⟩ := swRow_at (i := m) (by omega)
  obtain ⟨W₀, hW₀, hB⟩ : ∃ W₀, frameAt (fxAt r) = some W₀ ∧
      frontB2 (fxAt r) W₀ (m + 1) 0 (VerifiableInference.Desc.First.K2.n0At (m + 1))
        (VerifiableInference.Desc.First.K2.oldsAt (m + 1)) x = true := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · obtain ⟨W₀, a, b, -⟩ := foldSideR_one hS hR O hF hpl hcs hsh hr K.count K.shapes K.olds rfl
        hfx hrw
      exact ⟨W₀, a, b⟩
    · obtain ⟨W₀, a, b, -⟩ := foldSideR_link hS hR O hF hpl hcs hsh hm h23 hr (K.before hm)
        K.count K.shapes K.olds rfl hfx hrw
      exact ⟨W₀, a, b⟩
  exact one_answer_of_test hB (keptTyped_at hrw) (closed_at hrw hW₀).2 hW

/-- **AT THE OUTPUT HEAD's SWITCH, INTO GROUP 24.** -/
theorem hst_head_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW)
    (hsh : Z.first.shape = VerifiableInference.Desc.First.K2Hands.shW) (a : Place) (nm : String)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some 24) = some n)
    {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    (K : SwHeadCutsR Z c z s) :
    SwState Z.first.shape 24 n.codes s ∧
      (∀ x, frontAt (k2P Z a nm .head n) s = some x → switchNotices x.T x.others = n.sent) ∧
      ∀ x W, frontAt (k2P Z a nm .head n) s = some x → frameAt x = some W → ∀ κ ∈ W.kept,
        ∃ xo : OnBytes.Oracle, x.st.oracles[κ.old]? = some xo ∧ xo.shape.answers = 1 := by
  obtain ⟨Q, N⟩ := sw_head hS hR O hF hpl a nm hP hn hr
  refine ⟨Q, N, fun x W hx hW => ?_⟩
  obtain ⟨r, hrw⟩ := swRow_at (i := 23) (by omega)
  obtain ⟨W₀, hW₀, hB, -⟩ := foldSideR_head hS hR O hF hpl hcs hsh hr K.before K.count K.shapes
    K.olds rfl hx hrw
  exact one_answer_of_test hB (keptTyped_at hrw) (closed_at hrw hW₀).2 hW

/-- **AT THE FINISH's SWITCH, INTO GROUP 25.** -/
theorem hst_finish_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW)
    (hsh : Z.first.shape = VerifiableInference.Desc.First.K2Hands.shW) (a : Place) (nm : String)
    {Pp : Prep} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp none = some n)
    {s t : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : finishFrontQ s = .ok t) (K : SwFinishCutsR s) :
    SwState Z.first.shape 25 n.codes s ∧
      (∀ x, frontAt (k2P Z a nm .finish n) t = some x → switchNotices x.T x.others = n.sent) ∧
      ∀ x W, frontAt (k2P Z a nm .finish n) t = some x → frameAt x = some W → ∀ κ ∈ W.kept,
        ∃ xo : OnBytes.Oracle, x.st.oracles[κ.old]? = some xo ∧ xo.shape.answers = 1 := by
  obtain ⟨Q, N⟩ := sw_finish hS hR O hF hpl (by rw [hsh]; exact shW_links) a nm hP hn hr he
  refine ⟨Q, N, fun x W hx hW => ?_⟩
  obtain ⟨r, hrw⟩ := swRow_at (i := 24) (by omega)
  obtain ⟨W₀, hW₀, hB, -⟩ := foldSideR_fin hS hR O hF hpl hcs hsh hr K.count K.shapes he rfl hx
    hrw
  exact one_answer_of_test hB (keptTyped_at hrw) (closed_at hrw hW₀).2 hW

/-! ## The spender's three -/

section
variable {St Cl' : Type} {N₀ : Numbers} {links : List ModelPart} {bs : List (Block St Cl')}
  {Fk : Nat → S → Prop} {E : Nat → S → Bool}

theorem d_link_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW)
    (hsh : Z.first.shape = VerifiableInference.Desc.First.K2Hands.shW) {m : ℕ} (h23 : m < 23)
    (hFk : ∀ s, Fk (14 * (m + 1) + 2) s → ∃ z, SwLinkCutsR Z c z m s ∧
      Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (hps : blockPlaces bs = placesW) (hnd : placesW.Nodup) {b : Block St Cl'}
    (hbk : bs[14 * (m + 1) + 2]? = some b) (hok : reqShapeOk Z.first.shape = true)
    (hlenC : (N₀.keptOf (m + 1 - 1)).length =
      ((reqGroups Z.first.shape).getD (m + 1) {}).target.kept.size)
    (hcl : ∀ Pp n, prepOf Z Bs.G₀ = some Pp → numsAt Pp (some (m + 1)) = some n →
      b.oracles.flatten = oraclesAt n.grp n.codes n.sent ∧
      sentFitB (N₀.atBlocks Z.first.shape links bs) (m + 1) placesW[14 * (m + 1) + 2]? n.codes
        n.sent = true ∧
      possAt bs links.length (m + 1) = n.positions) :
    ∀ Pp n (s : S) x W lay', prepOf Z Bs.G₀ = some Pp → numsAt Pp (some (m + 1)) = some n →
      Fk (14 * (m + 1) + 2) s →
      XK (N₀.atBlocks Z.first.shape links bs) linksW placesW E (14 * (m + 1) + 2) s = true →
      firstFront s.st s.check.frame = .ok x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay' →
      LinkDebts (N₀.atBlocks Z.first.shape links bs) (m + 1) placesW[14 * (m + 1) + 2]?
        placesW[14 * (m + 1) + 3]? s n.positions x W lay' :=
  d_link (Nat.succ_ne_zero m) hps hnd hbk hok hlenC hcl fun _ _ s hP hn hf _ => by
    obtain ⟨z, K, hr⟩ := hFk s hf
    exact hst_link_reached hS hR O hF hpl hcs hsh h23 hP hn hr K

theorem d_head_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW)
    (hsh : Z.first.shape = VerifiableInference.Desc.First.K2Hands.shW)
    (hFk : ∀ s, Fk 339 s → ∃ z, SwHeadCutsR Z c z s ∧
      Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s))
    (hps : blockPlaces bs = placesW) (hnd : placesW.Nodup) {b : Block St Cl'}
    (hbk : bs[339]? = some b) (hok : reqShapeOk Z.first.shape = true)
    (hlenC : (N₀.keptOf (24 - 1)).length =
      ((reqGroups Z.first.shape).getD 24 {}).target.kept.size)
    (hcl : ∀ Pp n, prepOf Z Bs.G₀ = some Pp → numsAt Pp (some 24) = some n →
      b.oracles.flatten = oraclesAt n.grp n.codes n.sent ∧
      sentFitB (N₀.atBlocks Z.first.shape links bs) 24 placesW[339]? n.codes n.sent = true ∧
      possAt bs links.length 24 = n.positions) :
    ∀ nm Pp n (s : S) x W lay', prepOf Z Bs.G₀ = some Pp → numsAt Pp (some 24) = some n →
      Fk 339 s → XK (N₀.atBlocks Z.first.shape links bs) linksW placesW E 339 s = true →
      frontAt (k2P Z { chain := 1, link := some 24, piece := 2, kind := .K2 } nm .head n) s =
        some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay' →
      SwitchDebts (N₀.atBlocks Z.first.shape links bs) 24 placesW[339]? placesW[339 + 1]?
        s.book.trees.size n.positions (1 + x.T.kept.size + x.own.length) x W lay' :=
  d_head hps hnd hbk hok hlenC hcl fun nm _ _ s hP hn hf _ => by
    obtain ⟨z, K, hr⟩ := hFk s hf
    exact hst_head_reached hS hR O hF hpl hcs hsh _ nm hP hn hr K

theorem d_finish_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW)
    (hsh : Z.first.shape = VerifiableInference.Desc.First.K2Hands.shW)
    (hFk : ∀ s, Fk 353 s → ∃ z, SwFinishCutsR s ∧
      Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (hps : blockPlaces bs = placesW) (hnd : placesW.Nodup) {b : Block St Cl'}
    (hbk : bs[353]? = some b) (hok : reqShapeOk Z.first.shape = true)
    (hlenC : (N₀.keptOf (25 - 1)).length =
      ((reqGroups Z.first.shape).getD 25 {}).target.kept.size)
    (hcl : ∀ Pp n, prepOf Z Bs.G₀ = some Pp → numsAt Pp none = some n →
      b.oracles.flatten = oraclesAt n.grp n.codes n.sent ∧
      sentFitB (N₀.atBlocks Z.first.shape links bs) 25 placesW[353]? n.codes n.sent = true ∧
      possAt bs links.length 25 = n.positions) :
    ∀ nm Pp n (s t : S) x W lay', prepOf Z Bs.G₀ = some Pp → numsAt Pp none = some n →
      Fk 353 s → XK (N₀.atBlocks Z.first.shape links bs) linksW placesW E 353 s = true →
      finishFrontQ s = .ok t →
      frontAt (k2P Z IM.k2PlaceF nm .finish n) t = some x → frameAt x = some W →
      OnBytes.layTrees x.st.codes (switchNotices x.T x.others) = some lay' →
      SwitchDebts (N₀.atBlocks Z.first.shape links bs) 25 placesW[353]? placesW[353 + 1]?
        s.book.trees.size n.positions (1 + x.T.kept.size) x W lay' :=
  d_finish hps hnd hbk hok hlenC hcl fun nm _ _ s t hP hn hf _ he => by
    obtain ⟨z, K, hr⟩ := hFk s hf
    exact hst_finish_reached hS hR O hF hpl hcs hsh _ nm hP hn hr he K

end

end

end P1K2

#print axioms P1K2.linkCutsR_of_cuts
#print axioms P1K2.headCutsR_of_cuts
#print axioms P1K2.finishCutsR_of_cuts
#print axioms P1K2.sw_link
#print axioms P1K2.sw_head
#print axioms P1K2.sw_finish
#print axioms P1K2.hst_link_reached
#print axioms P1K2.hst_head_reached
#print axioms P1K2.hst_finish_reached
#print axioms P1K2.d_link_reached
#print axioms P1K2.d_head_reached
#print axioms P1K2.d_finish_reached
