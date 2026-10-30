-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/FreshAtClosing.lean: in front of the closing of each of the 25 segments of the proof file's first chain, the message
that the frame names as the fold's fresh mask is neither sampled nor spent as a mask. Under the library's head
(`P5J.AtMg`, at the older hash), at the states that the chain's own blocks reach from its own start.

  `answered_reached`   at every border up to 353: every sampled message's shape counts an answer
  `calm_folds`         between two cuts of one fold, up to 353: the relation `Calm` (FreshFlags.lean)
  `unspent_of_calm`    a law on two statements: from `Calm A B`, the marks of the groups below l in A, l + 1 groups in B, no
                      mark on group l in B: a message of B whose number is not below A's count of messages is not spent
  `unspent_fold`       the three cases (the first segment, the segments 1 to 23, the last) at a fold
  **`fresh_at_closing`**   the two flags, at the border 14 l + `IM.nAt l` + 5
  `fresh_of_begin`      the same from the yes of the four clauses in front of the beginning of the proximity test

How. Not sampled: the flag is laid by the admitting of a sample alone, which asks that the shape counts an answer; the
mask's shape counts none (premise ha). Not spent: the frame names the mask by a number that is not below the count of
messages in front of the segment's first sub-protocol (`mask_named`, `mask_head_named`, Johnson/IMR/); from there to the
closing no group gains the mark "its proximity test has begun", since the groups below l bear it already (`marked_at`,
Johnson/AtFull/Shape/MarksReached.lean), the statement has l + 1 groups (FreshSize.lean) and group l bears none (premise
hrun); and a message is spent only by a closing, which lays that mark.

Limits. ha (the mask's shape counts no answer) and hrun (no proximity test has begun on group l) are premises. Whether the
head can be had at any files is not shown here. The full size and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.FreshFlags
import Johnson.Desc.ProofFile.Honest.K10.Pay.FreshSize
import Johnson.Desc.ProofFile.Honest.K10.Xch.Says
import Johnson.AtFull.Shape.MarksReached
import Johnson.IMR.MaskNamed
import Johnson.IMR.MaskHeadNamed
import Johnson.IMR.WalkGivesAt
import Johnson.IMR.OpenWalk
import Johnson.IMR.FinPin
import Johnson.IMR.GroupHead
import Johnson.IMR.AtReach
import Johnson.Desc.AtSeats.StatementSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn foldBlocks)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open P5J (AtMg TS)

/-! ## 1 At an opening of the proof file's description -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)} {c : Chain TS ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The chain's own start has no message. -/
theorem answered_start (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (p : ProofFile.InstPub) : Answered (ProofFile.startS Z p).st := by
  intro o x hx
  rw [(Meaning.K2.startS_facts O.pub p).2.1] at hx
  simp at hx

/-- At every cut up to 353: every sampled message's shape counts an answer. -/
theorem answered_fold (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : Nat} (hk : k ≤ 353)
    {p : ProofFile.InstPub} {R R' : List Fmt.RoundView} {C C' : List OpenedColumn} {t : TS}
    (f : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (t, R', C')) : Answered t.st := by
  have w : AnsweredStays (ProofFile.startS Z p).st t.st :=
    Meaning.K2.open_fold (Meaning.K2.seatKeeps_mild stMild_answered) O trivial
      (fun _ _ _ => trivial) (by rw [Meaning.K2.front_len hS hR O]; exact hk) f
  exact w (answered_start O p)

/-- Between two cuts of one fold, up to 353. -/
theorem calm_folds (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {j k : Nat} (hjk : j ≤ k)
    (hk : k ≤ 353) {p : ProofFile.InstPub} {R R₁ R₂ : List Fmt.RoundView} {C C₁ C₂ : List OpenedColumn} {t₁ t₂ : TS}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take j) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    Calm t₁.st t₂.st :=
  Meaning.K2.open_between (Meaning.K2.seatKeeps_mild stMild_calm) O trivial
    (fun _ _ _ => trivial) hjk (by rw [Meaning.K2.front_len hS hR O]; exact hk) f₁ f₂

end

/-- **From "no group has gained the mark" to "not spent".** -/
theorem unspent_of_calm {A B : Statement} (hc : Calm A B) {l M : Nat}
    (hA : ∀ g, g < l → MarkedAt A g) (hsz : B.groups.size = l + 1)
    (hrun : ∀ G, B.groups[l]? = some G → G.inRun = false) (hM : A.oracles.size ≤ M)
    {x : OnBytes.Oracle} (hx : B.oracles[M]? = some x) : x.spentAsMask = false := by
  have hb : ∀ g, MarkedAt B g → MarkedAt A g := by
    rintro g ⟨G, h1, h2⟩
    have hg : g < B.groups.size := (Array.getElem?_eq_some_iff.1 h1).1
    by_cases c : g < l
    · exact hA g c
    · obtain rfl : g = l := by omega
      rw [hrun G h1] at h2
      cases h2
  cases hs : x.spentAsMask with
  | false => rfl
  | true =>
    obtain ⟨y, hy, -⟩ := hc.2 hb M x hx hs
    have := (Array.getElem?_eq_some_iff.1 hy).1
    omega

theorem markedAt_of {g : Nat} {T : Statement} (h : Johnson.AtFull.Shape.Marked g T) :
    MarkedAt T g := by
  unfold Johnson.AtFull.Shape.Marked Johnson.AtFull.Shape.markAt at h
  obtain ⟨G, h1, h2⟩ := Option.map_eq_some_iff.1 h
  exact ⟨G, h1, h2⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)} {c : Chain TS ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Not spent, at a fold that ends in front of a closing.** -/
theorem unspent_fold (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {p : ProofFile.InstPub} {R r : List Fmt.RoundView} {C q : List OpenedColumn} {t : TS}
    (g : foldBlocks 0 (c.blocksInOrder.take (14 * l + IM.nAt l + 5)) (ProofFile.startS Z p) R C = .ok (t, r, q))
    (hrun : ∀ G, t.st.groups[l]? = some G → G.inRun = false) {mk : Nat} {x : OnBytes.Oracle}
    (hm : (VerifiableInference.Desc.K9.recOf t).frame.mask = some mk)
    (hx : t.st.oracles[mk]? = some x) : x.spentAsMask = false := by
  have hn : IM.nAt l = if l = 24 then 9 else 7 := rfl
  rcases Nat.lt_or_ge l 24 with h24 | h24
  · rw [hn, if_neg (by omega : ¬ l = 24)] at g
    have g9 : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + 9)) (ProofFile.startS Z p) R C = .ok (t, r, q) := by
      rw [show 14 * l + 3 + 9 = 14 * l + 7 + 5 by omega]
      exact g
    have hsz := Meaning.K2.count_in_link hS hR O h24 9 (Nat.le_refl 9) t r q g9
    rcases Nat.eq_zero_or_pos l with rfl | h1
    · obtain ⟨t₀, R₀, C₀, f₀⟩ := Meaning.K2.fold_cut_le (Nat.zero_le (14 * 0 + 3 + 9)) g9
      have e0 : t₀ = ProofFile.startS Z p := by
        rw [List.take_zero] at f₀
        unfold foldBlocks at f₀
        exact (congrArg Prod.fst (Except.ok.inj f₀)).symm
      refine unspent_of_calm (calm_folds hS hR O (Nat.zero_le _) (by omega) f₀ g9)
        (fun g hg => absurd hg (Nat.not_lt_zero g)) hsz hrun ?_ hx
      rw [e0, (Meaning.K2.startS_facts O.pub p).2.1]
      exact Nat.zero_le _
    · obtain ⟨t₀, R₀, C₀, L, f₀, hL, -, hmask⟩ :=
        Meaning.K2.mask_named hS hR O h1 h24 (Nat.le_refl 9) g9
      rw [frame_of_open hL, hmask] at hm
      obtain rfl := Option.some.inj hm
      refine unspent_of_calm (calm_folds hS hR O (by omega) (by omega) f₀ g9)
        (fun g hg => markedAt_of (Johnson.AtFull.Shape.marked_at hS hR O (by omega) (by omega)
          (by rw [Meaning.K2.front_len hS hR O]; omega) f₀)) hsz hrun (by omega) hx
  · obtain rfl : l = 24 := by omega
    rw [hn, if_pos rfl] at g
    have g10 : foldBlocks 0 (c.blocksInOrder.take (340 + 10)) (ProofFile.startS Z p) R C = .ok (t, r, q) := g
    have hsz := Meaning.K2.count_in_head hS hR O 10 (Nat.le_refl 10) t r q g
    obtain ⟨t₀, R₀, C₀, L, f₀, hL, -, hmask⟩ :=
      Meaning.K2.mask_head_named hS hR O (Nat.le_refl 10) g10
    rw [frame_of_open hL, hmask] at hm
    obtain rfl := Option.some.inj hm
    refine unspent_of_calm (calm_folds hS hR O (by omega) (by omega) f₀ g10)
      (fun g hg => markedAt_of (Johnson.AtFull.Shape.marked_at hS hR O (by omega) (by omega)
        (by rw [Meaning.K2.front_len hS hR O]; omega) f₀)) hsz hrun (by omega) hx

end

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl}

/-- At every border up to 353: every sampled message's shape counts an answer. -/
theorem answered_reached (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {b : Nat} (hb : b ≤ 353)
    {z : ProofFile.InstPub} {s : TS} (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b (z, s)) : Answered s.st := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, rs, cols, f⟩ := hr.fold
  exact answered_fold h.scope h.reads O hb f

/-- **IN FRONT OF A CLOSING THE FRESH MASK's MESSAGE IS NEITHER SAMPLED NOR SPENT.** -/
theorem fresh_at_closing (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l : Nat} (hl : l < 25)
    {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s))
    (hrun : ∀ G, s.st.groups[l]? = some G → G.inRun = false) {mk : Nat} {x : OnBytes.Oracle}
    (hm : (VerifiableInference.Desc.K9.recOf s).frame.mask = some mk)
    (hx : s.st.oracles[mk]? = some x) (ha : x.shape.answers = 0) :
    x.sampled = false ∧ x.spentAsMask = false := by
  have hn : IM.nAt l ≤ 9 := by
    unfold IM.nAt
    split <;> omega
  refine ⟨?_, ?_⟩
  · cases hs : x.sampled with
    | false => rfl
    | true =>
      have := answered_reached h (by omega) hr mk x hx hs
      omega
  · obtain ⟨Bs, base, O⟩ := h.laid.opened
    obtain ⟨-, rs, cols, f⟩ := hr.fold
    exact unspent_fold h.scope h.reads O hl f hrun hm hx

/-- The same, from the yes of the four clauses in front of the beginning of the proximity test at
the group that the record's frame names. -/
theorem fresh_of_begin (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {l : Nat} (hl : l < 25)
    {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s))
    (hb : VerifiableInference.Desc.Ground.ok (VerifiableInference.Desc.Ground.beginRunL
      (VerifiableInference.Desc.K9.recOf s).st (VerifiableInference.Desc.K9.recOf s).frame.group) =
        true)
    {mk : Nat} {x : OnBytes.Oracle}
    (hm : (VerifiableInference.Desc.K9.recOf s).frame.mask = some mk)
    (hx : s.st.oracles[mk]? = some x) (ha : x.shape.answers = 0) :
    x.sampled = false ∧ x.spentAsMask = false := by
  refine fresh_at_closing h hl hr (fun G hG => ?_) hm hx ha
  have hg : (VerifiableInference.Desc.K9.recOf s).frame.group = l := by
    obtain ⟨-, rs, cols, hfd⟩ := hr.fold
    have hn : IM.nAt l = if l = 24 then 9 else 7 := rfl
    have b1 : 14 * l + 3 + (if l = 24 then 1 else 0) ≤ 14 * l + IM.nAt l + 5 := by
      rw [hn]
      split <;> omega
    have b2 : 14 * l + IM.nAt l + 5 ≤ 14 * l + 14 + (if l = 24 then 2 else 0) := by
      rw [hn]
      split <;> omega
    obtain ⟨Bs, base, O⟩ := h.laid.opened
    obtain ⟨L, hL, -, hg⟩ := _root_.Meaning.K2.group_all h.scope h.reads O hl b1 b2 hfd
    rw [frame_of_open hL]
    exact hg
  rw [hg] at hb
  have hG2 : (VerifiableInference.Desc.K9.recOf s).st.groups[l]? = some G := hG
  simp only [VerifiableInference.Desc.Ground.ok, VerifiableInference.Desc.Ground.beginRunL,
    List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true] at hb
  obtain ⟨-, h2, -⟩ := hb
  rw [hG2] at h2
  simpa [VerifiableInference.Desc.Ground.has] using h2

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.answered_start
#print axioms ProofFile.Honest.K10.answered_fold
#print axioms ProofFile.Honest.K10.calm_folds
#print axioms ProofFile.Honest.K10.unspent_of_calm
#print axioms ProofFile.Honest.K10.markedAt_of
#print axioms ProofFile.Honest.K10.unspent_fold
#print axioms ProofFile.Honest.K10.answered_reached
#print axioms ProofFile.Honest.K10.fresh_at_closing
#print axioms ProofFile.Honest.K10.fresh_of_begin
