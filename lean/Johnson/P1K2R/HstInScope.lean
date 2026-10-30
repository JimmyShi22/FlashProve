-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/HstInScope.lean: code switching (K2): THE STATE's SIDE OF WHAT IS OWED ON THE
TABLE's NUMBERS, AT REACHED STATES, IN SCOPE: the premise hst of d_link | d_head | d_finish
(Johnson/P1K2R/DebtsAt.lean), paid at every state that Reach has at the switch's own number
(14 (m + 1) + 2 · 339 · 353) over the first chain's sub-protocols of the IOP as written in Lean for
the proof file. A join: every step is a call of another file's theorem.
  MsgCountAt · MsgShapesAt · OldShapesAt  short names for what foldSide_* asks at one written
               cut, at one public part p of an instance
  SwLinkCuts · SwHeadCuts · SwFinishCuts  what foldSide_one | _link · _head · _fin ask at written
               cuts, each as one Lean structure, at one p
  numsAt_codes · codes_at  the codes in the numbers of a switch are the public part's first chain's
  swRow_at     the written table of the 25 switches has an entry at each i < 25
  shW_links    the written shape of the request has 25 links (by Lean's kernel)
  mw_length    the written list of the messages' shapes has 199 entries
  noMark_of_fold · noMark_of_reach  where the fold over the first k ≥ 2 sub-protocols returns, or a
               state is reached at k ≥ 2, the first state bears no mark
  hst_link     at the switch into group m + 1, m < 23
  hst_head     at the output head's switch, into group 24
  hst_finish   at the finish's switch, into group 25
  d_link_scope · d_head_scope · d_finish_scope  d_link | d_head | d_finish with hst gone: so Lean
               itself holds the three arms to the spender's letters
EACH ARM ENDS IN THREE CLAUSES: SwState (six facts on the state in front of the switch) · what the
switch announces is n.sent · at each entry of the frame's list of kept places the front's statement
has an oracle message whose shape counts one answer. The third clause alone spends the …Cuts, hcs
and hsh (but for «25 links» at the finish, which comes from hsh).
CALLED. swState_link_reach | _head_reach | _finish_reach (SwStateAt.lean) · both_at_open ·
closed_at · foldSide_one | _link | _head | _fin (FoldSide.lean) · keptTyped_at ·
one_answer_of_test (K2Caller/OneAnswer.lean) · frontOf_iff (Tw/K2C/DebtsState.lean) ·
finishFrontQ_fr · reach_raw. From Johnson/IMR/: prep_facts · fence1_at_link | _head
(MsgsPlaces.lean) · fence1_at_finish (MsgsBehind.lean) · front_len · Open.first · start_real ·
fold_cut · pub_start. ProofFile's startP_is.
THE PREMISES THAT STAY, BY NAME. In scope, the files read, the opening O · hF: onlineDescription returns F ·
hpl: F.planOk · hcs hsh: the public part's codes and shape are the written ones · K: the …Cuts AT
THE REACHED STATE's OWN PUBLIC PART z: the count of oracle messages at a written cut is the closed
number · at the switch's cut each message has the listed shape · the like in front of the last
closing, at the kept old numbers. In the three d_…_scope: d_…'s six closed premises, and hFk: where
the fence Fk holds, the state is reached from a public part z at which the …Cuts hold.
WHY AT ONE z. The payer of the shapes (FoldSidePaid.lean's Owed)
stands at one p and holds «the first state bears no mark», which fails at some p (the empty
request). At a z from which a state is reached at a switch's number it holds: noMark_of_reach.
LIMITS. A join. The …Cuts speak of every return of the fold from z: more than «reached». No premise
is shown met at a real value here. The second and third clause say nothing at a state of which the
switch's text makes no front. No probability; no soundness is claimed.
-/
import Johnson.P1K2R.DebtsAt
import Johnson.P1K2R.SwStateAt
import Johnson.P1K2R.FoldSide
import Johnson.IMR.MsgsPlaces
import Johnson.IMR.MsgsBehind
import Johnson.Top.H0.K2Caller.OneAnswer
import Johnson.Desc.K1.Law.FirstMakeFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription Place foldBlocks)
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

/-- At every return of the fold over the chain's first k sub-protocols, from the first state at the
instance's public part p, the statement holds n oracle messages. -/
def MsgCountAt (Z : ProofFile.Pub) (c : Chain S Cl) (p : ProofFile.InstPub) (k n : ℕ) : Prop :=
  ∀ (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (t : S) (R' : List Fmt.RoundView)
    (C' : List VerifiableInference.Desc.OpenedColumn),
    foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (t, R', C') → t.st.oracles.size = n

/-- At every such return each oracle message has the shape that the written list has at its
number. -/
def MsgShapesAt (Z : ProofFile.Pub) (c : Chain S Cl) (p : ProofFile.InstPub) (k : ℕ) : Prop :=
  ∀ (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (t : S) (R' : List Fmt.RoundView)
    (C' : List VerifiableInference.Desc.OpenedColumn),
    foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (t, R', C') →
    ∀ o, o < t.st.oracles.size → (t.st.oracles[o]?).map (·.shape) = MW[o]?

/-- The like at the numbers of the old messages that the switch into group g keeps. -/
def OldShapesAt (Z : ProofFile.Pub) (c : Chain S Cl) (p : ProofFile.InstPub) (k g : ℕ) : Prop :=
  ∀ (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (t : S) (R' : List Fmt.RoundView)
    (C' : List VerifiableInference.Desc.OpenedColumn),
    foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (t, R', C') →
    ∀ o ∈ VerifiableInference.Desc.First.K2.oldsAt g, (t.st.oracles[o]?).map (·.shape) = MW[o]?

/-- **What foldSide_one | foldSide_link ask at written cuts**, at the switch into group m + 1, at
one public part p of an instance. counts is asked at the 23 links' cuts, as foldSide_link asks it;
two of them are spent (in front of the switches into groups m and m + 1). -/
structure SwLinkCuts (Z : ProofFile.Pub) (c : Chain S Cl) (p : ProofFile.InstPub) (m : ℕ) : Prop where
  counts : ∀ g, 1 ≤ g → g ≤ 23 →
    MsgCountAt Z c p (14 * g + 2) (VerifiableInference.Desc.First.K2.n0At g)
  shapes : MsgShapesAt Z c p (14 * (m + 1) + 2)
  olds : OldShapesAt Z c p (14 * m + 12) (m + 1)

/-- **What foldSide_head asks at written cuts.** -/
structure SwHeadCuts (Z : ProofFile.Pub) (c : Chain S Cl) (p : ProofFile.InstPub) : Prop where
  count23 : MsgCountAt Z c p 324 (VerifiableInference.Desc.First.K2.n0At 23)
  count24 : MsgCountAt Z c p 339 (VerifiableInference.Desc.First.K2.n0At 24)
  shapes : MsgShapesAt Z c p 339
  olds : OldShapesAt Z c p 334 24

/-- **What foldSide_fin asks at written cuts.** -/
structure SwFinishCuts (Z : ProofFile.Pub) (c : Chain S Cl) (p : ProofFile.InstPub) : Prop where
  count : MsgCountAt Z c p 353 (VerifiableInference.Desc.First.K2.n0At 25)
  shapes : MsgShapesAt Z c p 353

/-- The codes in the numbers of a switch are the sizes' own; at a link and at the finish. -/
theorem numsAt_codes {Pp : Prep} {link : Option Nat} {n : Nums} (h : numsAt Pp link = some n) :
    n.codes = Pp.z.codes := by
  unfold numsAt at h
  dsimp only at h
  split at h
  · cases h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨_, _, f, _, lay, _, rd, _, rfl⟩ := h
    rfl

/-- The written list of the oracle messages' shapes has 199 entries: more than the 185 messages that
stand in front of the last switch, so MsgShapesAt never asks «some = none» there. -/
theorem mw_length : MW.length = 199 := by
  rw [VerifiableInference.Desc.First.K2Hands.MW_eq]
  rfl

/-- The written table of the 25 switches has an entry at each i < 25. -/
theorem swRow_at {i : ℕ} (hi : i < 25) : ∃ r : SwRow, tableFullLit[i]? = some r :=
  ⟨_, List.getElem?_eq_getElem (show i < tableFullLit.length from hi)⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- They are the public part's first chain's codes. -/
theorem codes_at (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Pp : Prep}
    {link : Option Nat} {n : Nums} (hP : prepOf Z Bs.G₀ = some Pp)
    (hn : numsAt Pp link = some n) : n.codes = Z.first.codes := by
  rw [numsAt_codes hn, (Meaning.Carry.prep_facts hP).2.1, O.first]

/-- **Where the fold over the first k ≥ 2 sub-protocols returns, the first state bears no mark.**
By start_real (Johnson/IMR/ListsEnds.lean): the request has passed the test at the start. -/
theorem noMark_of_fold (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} (h2 : 2 ≤ k)
    {p : ProofFile.InstPub} {R R' : List Fmt.RoundView} {C C' : List VerifiableInference.Desc.OpenedColumn} {t : S}
    (f : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (t, R', C')) :
    (ProofFile.startS Z p).failed = none := by
  obtain ⟨d, rfl⟩ : ∃ d, k = 2 + d := ⟨k - 2, by omega⟩
  obtain ⟨t₀, R₀, C₀, f₀⟩ := Meaning.K2.fold_cut d f
  have hq := Meaning.K2.start_real hS hR O f₀
  have e0 := ProofFile.Law.startP_is (Meaning.K2.pub_start O.pub)
  unfold ProofFile.startS
  dsimp only
  rw [if_pos hq]
  show Z.s₀.failed = none
  rw [e0]
  rfl

/-- The same from a state reached at k ≥ 2. -/
theorem noMark_of_reach (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} (h2 : 2 ≤ k)
    {z : ProofFile.InstPub} {s : S} (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (z, s)) :
    (ProofFile.startS Z z).failed = none := by
  obtain ⟨-, rs, cols, f⟩ := (reach_raw hr).fold
  exact noMark_of_fold hS hR O h2 f

/-- **AT THE SWITCH INTO GROUP m + 1, m < 23.** -/
theorem hst_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW)
    (hsh : Z.first.shape = VerifiableInference.Desc.First.K2Hands.shW) {m : ℕ} (h23 : m < 23)
    {z : ProofFile.InstPub} (K : SwLinkCuts Z c z m) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some (m + 1)) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s)) :
    SwState Z.first.shape (m + 1) n.codes s ∧
      (∀ x, firstFront s.st s.check.frame = .ok x → switchNotices x.T x.others = n.sent) ∧
      ∀ x W, firstFront s.st s.check.frame = .ok x → frameAt x = some W → ∀ κ ∈ W.kept,
        ∃ xo : OnBytes.Oracle, x.st.oracles[κ.old]? = some xo ∧ xo.shape.answers = 1 := by
  obtain ⟨hG, hA⟩ := both_at_open O hF hpl (by rw [Meaning.Carry.front_len hS hR O]; omega) hr
  have Q := Meaning.K2.swState_link_reach hS hR O (l := m + 1) (by omega) hr hG hA
  rw [← codes_at O hP hn] at Q
  refine ⟨Q, fun x hx => ?_, fun x W hx hW => ?_⟩
  · exact Meaning.Carry.fence1_at_link hP hn Q.link (by rw [Q.shape, O.first])
      (by rw [Q.groups, Q.shape, O.first]) default "" x (Or.inl ⟨rfl, hx⟩)
  · have hfx : frontAt (k2P Z default "" .link n) s = some x :=
      frontOf_iff.1 (Or.inl ⟨rfl, hx⟩)
    obtain ⟨r, hrw⟩ := swRow_at (i := m) (by omega)
    obtain ⟨W₀, hW₀, hB⟩ : ∃ W₀, frameAt (fxAt r) = some W₀ ∧
        frontB2 (fxAt r) W₀ (m + 1) 0 (VerifiableInference.Desc.First.K2.n0At (m + 1))
          (VerifiableInference.Desc.First.K2.oldsAt (m + 1)) x = true := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · obtain ⟨W₀, a, b, -⟩ := foldSide_one hS hR O hF hpl hcs hsh hr
          (K.counts 1 (by omega) (by omega)) K.shapes K.olds rfl hfx hrw
        exact ⟨W₀, a, b⟩
      · obtain ⟨W₀, a, b, -⟩ := foldSide_link hS hR O hF hpl hm h23 hcs hsh hr
          K.counts K.shapes K.olds rfl hfx hrw
        exact ⟨W₀, a, b⟩
    exact one_answer_of_test hB (keptTyped_at hrw) (closed_at hrw hW₀).2 hW

/-- **AT THE OUTPUT HEAD's SWITCH, INTO GROUP 24.** -/
theorem hst_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW)
    (hsh : Z.first.shape = VerifiableInference.Desc.First.K2Hands.shW)
    {z : ProofFile.InstPub} (K : SwHeadCuts Z c z) (a : Place) (nm : String) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp (some 24) = some n) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (z, s)) :
    SwState Z.first.shape 24 n.codes s ∧
      (∀ x, frontAt (k2P Z a nm .head n) s = some x → switchNotices x.T x.others = n.sent) ∧
      ∀ x W, frontAt (k2P Z a nm .head n) s = some x → frameAt x = some W → ∀ κ ∈ W.kept,
        ∃ xo : OnBytes.Oracle, x.st.oracles[κ.old]? = some xo ∧ xo.shape.answers = 1 := by
  obtain ⟨hG, hA⟩ := both_at_open O hF hpl (by rw [Meaning.Carry.front_len hS hR O]; omega) hr
  have Q := Meaning.K2.swState_head_reach hS hR O hr hG hA
  rw [← codes_at O hP hn] at Q
  refine ⟨Q, fun x hx => ?_, fun x W hx hW => ?_⟩
  · exact Meaning.Carry.fence1_at_head hP hn Q.link (by rw [Q.shape, O.first])
      (by rw [Q.groups, Q.shape, O.first]) a nm x (frontOf_iff.2 hx)
  · obtain ⟨r, hrw⟩ := swRow_at (i := 23) (by omega)
    obtain ⟨W₀, hW₀, hB, -⟩ := foldSide_head hS hR O hF hpl hcs hsh hr K.count23 K.count24
      K.shapes K.olds rfl hx hrw
    exact one_answer_of_test hB (keptTyped_at hrw) (closed_at hrw hW₀).2 hW

/-- The written shape of the request has 25 links. -/
theorem shW_links : VerifiableInference.Desc.First.K2Hands.shW.link.length = 25 := by
  decide +kernel

/-- **AT THE FINISH's SWITCH, INTO GROUP 25.** s: the state in front of the switch. t: the state
behind the quiet step in front of the switch, whose accept is a premise. -/
theorem hst_finish (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW)
    (hsh : Z.first.shape = VerifiableInference.Desc.First.K2Hands.shW)
    {z : ProofFile.InstPub} (K : SwFinishCuts Z c z) (a : Place) (nm : String) {Pp : Prep} {n : Nums}
    (hP : prepOf Z Bs.G₀ = some Pp) (hn : numsAt Pp none = some n) {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (z, s))
    (he : finishFrontQ s = .ok t) :
    SwState Z.first.shape 25 n.codes s ∧
      (∀ x, frontAt (k2P Z a nm .finish n) t = some x → switchNotices x.T x.others = n.sent) ∧
      ∀ x W, frontAt (k2P Z a nm .finish n) t = some x → frameAt x = some W → ∀ κ ∈ W.kept,
        ∃ xo : OnBytes.Oracle, x.st.oracles[κ.old]? = some xo ∧ xo.shape.answers = 1 := by
  have hlen : 353 ≤ (Meaning.K2.frontOf c).length := by rw [Meaning.Carry.front_len hS hR O]
  obtain ⟨hG, hA⟩ := both_at_open O hF hpl hlen hr
  have Q := Meaning.K2.swState_finish_reach hS hR O hr hlen (by rw [hsh]; exact shW_links) he hG
    hA
  rw [← codes_at O hP hn] at Q
  refine ⟨Q, fun x hx => ?_, fun x W hx hW => ?_⟩
  · obtain ⟨a₀, g, ha, hg, hgr, hl, hs, -, hfg, -⟩ :=
      VerifiableInference.Desc.First.K2.finishFrontQ_fr he
    exact Meaning.Carry.fence1_at_finish hP hn ha hg hgr hl (by rw [hs, Q.shape, O.first])
      (by rw [hfg, Q.groups, Q.shape, O.first]) a nm x (frontOf_iff.2 hx)
  · obtain ⟨r, hrw⟩ := swRow_at (i := 24) (by omega)
    obtain ⟨W₀, hW₀, hB, -⟩ := foldSide_fin hS hR O hF hpl hcs hsh hr K.count K.shapes he rfl hx
      hrw
    exact one_answer_of_test hB (keptTyped_at hrw) (closed_at hrw hW₀).2 hW

/-! ## d_link | d_head | d_finish with hst gone: Lean holds the three arms to the spender's letters
-/

section
variable {St Cl' : Type} {N₀ : Numbers} {links : List ModelPart} {bs : List (Block St Cl')}
  {Fk : Nat → S → Prop} {E : Nat → S → Bool}

theorem d_link_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW)
    (hsh : Z.first.shape = VerifiableInference.Desc.First.K2Hands.shW) {m : ℕ} (h23 : m < 23)
    (hFk : ∀ s, Fk (14 * (m + 1) + 2) s → ∃ z, SwLinkCuts Z c z m ∧
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
    exact hst_link hS hR O hF hpl hcs hsh h23 K hP hn hr

theorem d_head_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW)
    (hsh : Z.first.shape = VerifiableInference.Desc.First.K2Hands.shW)
    (hFk : ∀ s, Fk 339 s → ∃ z, SwHeadCuts Z c z ∧
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
    exact hst_head hS hR O hF hpl hcs hsh K _ nm hP hn hr

theorem d_finish_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW)
    (hsh : Z.first.shape = VerifiableInference.Desc.First.K2Hands.shW)
    (hFk : ∀ s, Fk 353 s → ∃ z, SwFinishCuts Z c z ∧
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
    exact hst_finish hS hR O hF hpl hcs hsh K _ nm hP hn hr he

end

end

end P1K2

#print axioms P1K2.numsAt_codes
#print axioms P1K2.mw_length
#print axioms P1K2.swRow_at
#print axioms P1K2.codes_at
#print axioms P1K2.shW_links
#print axioms P1K2.noMark_of_fold
#print axioms P1K2.noMark_of_reach
#print axioms P1K2.hst_link
#print axioms P1K2.hst_head
#print axioms P1K2.hst_finish
#print axioms P1K2.d_link_scope
#print axioms P1K2.d_head_scope
#print axioms P1K2.d_finish_scope
