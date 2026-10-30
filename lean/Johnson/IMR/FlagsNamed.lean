-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FlagsNamed.lean: THE MEMBERS OF A LINK's GROUP WITH THE FIRST NUMBER NAMED: what
flags_at (Johnson/IMR/FlagsAt.lean) and members_head (Johnson/IMR/HeadMembers.lean) say with "there
is a number n₀":
HERE n₀ IS THE STATE's COUNT OF ORACLE MESSAGES AT THE CUT IN FRONT OF THE LINK's CODE SWITCH, of
the same fold: at the proof file's seat, in the goals' scope, from the fold's return alone.
Theorems, proved.


Compiled with the whole library.
  flags_named   1 ≤ l < 24, the cuts 14 l + 8 + n, n ≤ 4 (n = 4: in front of the closing): with t₀,
    t₃, t₅ the states of the same fold at the cuts 14 l + 2, 14 l + 5, 14 l + 7 (in front of the
    switch and of the two later sendings): G.members = #[t₀'s count] ++ keptBefore ++ own;
    keptBefore and own AS RANGES off these three counts, their lengths in the public shape's
    words. Calls: entry_at, front_words, walk_c, At.members, atMoment_of.
  size_at_table   at EVERY cut k of the first chain: the state's count of oracle messages is the
    table's N.msgsAt placesW[k]?, at N := N₀.withTold placesW (toldOf c.blocksInOrder), under the tests on
    the plan: the third clause of bookAt at book_reached_planOk (Johnson/IMR/BookPaidR.lean).
  walk_head_named   THE WALK OF THE HEAD's LINK WITH ITS FIRST NUMBER NAMED: walk_head's OWN PROOF
    (Johnson/IMR/HeadMembers.lean), LINE FOR LINE, WITH THE STATEMENT STRENGTHENED: the witness was
      that term
    already. walk_head FOLLOWS FROM IT IN ONE LINE (the example behind it); its file is not
    turned.
  members_head_named   the cuts 340 + n, n ≤ 10 (n = 10: in front of the closing): members_head with
    n₀ := the count at the cut 339.
THE FIRST NUMBER, CLOSED: Meaning.Carry.n0_at_link_paid | n0_at_head_paid
(Johnson/IMR/ToldPaid.lean): it is
K2.n0At l | K2.n0At 24, where the chain's sub-protocols have the written cut: called by whoever
wants it, at the folds that these theorems hand out.
sh := Z.first.shape.

OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: kind K10's files. LETTERS: N₀.

What is not claimed. The counts at 14 l + 5 and 14 l + 7 as closed numbers. keptBefore and own as
ranges at the head's link. Anything at link 0 (members_at, Johnson/IMR/FrameEntry.lean: no number
stands in
front there). That a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.HeadMembers
import Johnson.IMR.OwnSize
import Johnson.IMR.BookPaidR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE MEMBERS, keptBefore AND own, OFF THREE COUNTS OF THE SAME FOLD: 1 ≤ l < 24.** -/
theorem flags_named (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h1 : 1 ≤ l)
    (h24 : l < 24) {p : ProofFile.InstPub} {R : List Fmt.RoundView}
    {C : List VerifiableInference.Desc.OpenedColumn} {n : Nat} (hn : n ≤ 4) {t : S} {r : List Fmt.RoundView}
    {q : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (14 * l + 8 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ (t₀ t₃ t₅ : S) (R₀ R₃ R₅ : List Fmt.RoundView) (C₀ C₃ C₅ : List VerifiableInference.Desc.OpenedColumn)
      (L : LinkCtx) (G : Group),
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀) ∧
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 5)) (ProofFile.startS Z p) R C = .ok (t₃, R₃, C₃) ∧
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 7)) (ProofFile.startS Z p) R C = .ok (t₅, R₅, C₅) ∧
      t.link? = some L ∧ L.link = l ∧ t.st.groups[l]? = some G ∧
      G.members = #[t₀.st.oracles.size] ++ L.check.frame.keptBefore ++ L.check.frame.own ∧
      L.check.frame.keptBefore = (Array.range (K2.targetAt Z.first.shape l).kept.size).map
        (· + (t₀.st.oracles.size + 1)) ∧
      L.check.frame.own =
        (Array.range (msgsAt Z.first.shape l 0)).map
            (· + (t₀.st.oracles.size + (1 + (K2.targetAt Z.first.shape l).kept.size))) ++
          (Array.range (msgsAt Z.first.shape l 1)).map (· + t₃.st.oracles.size) ++
          (Array.range (msgsAt Z.first.shape l 2)).map (· + t₅.st.oracles.size) := by
  obtain ⟨t₅, R₅, C₅, f₅⟩ := fold_cut (k := 14 * l + 7) (n + 1)
    (by rw [show 14 * l + 7 + (n + 1) = 14 * l + 8 + n by omega]; exact g)
  obtain ⟨t₃, R₃, C₃, f₃⟩ := fold_cut (k := 14 * l + 5) 2 f₅
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 14 * l + 3) 2 f₃
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * l + 2) f₁
  obtain ⟨x, f, hx, a1, a2, mo, lk, hg, -, sh, kb, ow⟩ := entry_at hS hR O h1 h24 f₀ f₁
  obtain ⟨eT, eo, es⟩ := front_words hS hR O h24 f₀ hx
  obtain ⟨L, G, hL, e2, e1, hG, em, -, -, -⟩ :=
    (walk_c hS hR O h24 f₁ f₃ f₅ hg a1 a2 n hn t r q g).members
  have s1 : f.shape = Z.first.shape := sh.trans es
  refine ⟨t₀, t₃, t₅, R₀, R₃, R₅, C₀, C₃, C₅, L, G, f₀, f₃, f₅, hL, e2, hG, em, ?_, ?_⟩
  · rw [e1]
    show f.keptBefore = _
    rw [kb, eT]
  · rw [e1]
    show f.own ++ (Array.range (f.atMoment f.moment).length).map (· + t₃.st.oracles.size) ++
        (Array.range ((laterF f t₃.st.oracles.size).atMoment
          (laterF f t₃.st.oracles.size).moment).length).map (· + t₅.st.oracles.size) = _
    have m2 : (laterF f t₃.st.oracles.size).moment = 2 := by
      show f.moment + 1 = 2
      rw [mo]
    unfold msgsAt
    rw [m2, mo, atMoment_of s1 lk, atMoment_of (f := laterF f t₃.st.oracles.size) s1 lk, ow, eT,
      eo]

/-- **THE STATE's COUNT OF ORACLE MESSAGES AT A CUT IS THE TABLE's.** -/
theorem size_at_table (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hF : F.planOk = true)
    (N₀ : Numbers) {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn}
    {k : Nat} (hk : k ≤ c.blocksInOrder.length)
    {x : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (f : foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok x) :
    x.1.st.oracles.size =
      (N₀.withTold IM.placesW (Meaning.Carry.toldOf c.blocksInOrder)).msgsAt IM.placesW[k]? := by
  have hr := Johnson.Desc.First.Walk.Tied.reach_of_fold k hk x.1 R x.2.1 C x.2.2 f
  have hb := IM.book_reached_planOk hS hR O N₀ hF p k x.1 hr
  unfold bookAt at hb
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  exact hb.2

/-- **THE WALK OF THE HEAD's LINK, ITS FIRST NUMBER NAMED.** -/
theorem walk_head_named (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {n : Nat} (hn : n ≤ 10) {t : S}
    {r : List Fmt.RoundView} {q : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (340 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ (t₀ : S) (r0 : List Fmt.RoundView) (q0 : List VerifiableInference.Desc.OpenedColumn) (n₄ n₆ : Nat)
      (f : ReqFrame), foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₀, r0, q0) ∧
      At 24 #[t₀.st.oracles.size] (headFl (flagsHead Z.first.shape) f n₄ n) (headF f n₄ n₆ n) t ∧
      f.moment = 1 ∧ f.link = 24 ∧ f.group = 24 ∧ f.shape = Z.first.shape := by
  have cut : ∀ k ≤ n + 1, ∃ t' r' q',
      foldBlocks 0 (c.blocksInOrder.take (339 + k)) (ProofFile.startS Z p) R C = .ok (t', r', q') := by
    intro k hk
    exact fold_cut (k := 339 + k) (n + 1 - k)
      (by rw [show 339 + k + (n + 1 - k) = 340 + n by omega]; exact g)
  have same : ∀ {k : Nat} {a b : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn},
      foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok a →
      foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok b → a.1 = b.1 :=
    fun h1 h2 => congrArg Prod.fst (Except.ok.inj (h1.symm.trans h2))
  obtain ⟨t₀, r0, q0, g0⟩ := cut 0 (by omega)
  obtain ⟨t₁, r1, q1, g1⟩ := cut 1 (by omega)
  obtain ⟨f, a1, b1, mo, lk, gp, sh⟩ := at_head_entry hS hR O g0 g1
  -- n = 0
  by_cases h0 : n = 0
  · subst h0
    obtain rfl : t₁ = t := same g1 g
    exact ⟨t₀, r0, q0, 0, 0, f, g0, a1, mo, lk, gp, sh⟩
  obtain ⟨t₂, r2, q2, g2⟩ := cut 2 (by omega)
  have k2 := step_quiet24 hS hR O (j := 2) (by omega) g1 g2
  by_cases h1 : n = 1
  · subst h1
    obtain rfl : t₂ = t := same g2 g
    exact ⟨t₀, r0, q0, 0, 0, f, g0, at_quiet k2 a1, mo, lk, gp, sh⟩
  obtain ⟨t₃, r3, q3, g3⟩ := cut 3 (by omega)
  have k3 := step_quiet24 hS hR O (j := 3) (by omega) g2 g3
  have a3 := at_quiet k3 (at_quiet k2 a1)
  have b3 := below_quiet k3 (below_quiet k2 b1)
  by_cases h2 : n = 2
  · subst h2
    obtain rfl : t₃ = t := same g3 g
    exact ⟨t₀, r0, q0, 0, 0, f, g0, a3, mo, lk, gp, sh⟩
  obtain ⟨t₄, r4, q4, g4⟩ := cut 4 (by omega)
  obtain ⟨a4, b4⟩ := step_at24 hS hR O (j := 4) (Or.inl rfl) g3 g4 gp a3 b3
  by_cases h3 : n = 3
  · subst h3
    obtain rfl : t₄ = t := same g4 g
    exact ⟨t₀, r0, q0, t₃.st.oracles.size, 0, f, g0, a4, mo, lk, gp, sh⟩
  obtain ⟨t₅, r5, q5, g5⟩ := cut 5 (by omega)
  have k5 := step_quiet24 hS hR O (j := 5) (by omega) g4 g5
  by_cases h4 : n = 4
  · subst h4
    obtain rfl : t₅ = t := same g5 g
    exact ⟨t₀, r0, q0, t₃.st.oracles.size, 0, f, g0, at_quiet k5 a4, mo, lk, gp, sh⟩
  obtain ⟨t₆, r6, q6, g6⟩ := cut 6 (by omega)
  obtain ⟨a6, -⟩ := step_at24 hS hR O (j := 6) (Or.inr rfl) g5 g6
    (f := laterF f t₃.st.oracles.size) gp (at_quiet k5 a4) (below_quiet k5 b4)
  -- from here on the frame and the flags stay
  have fin : ∀ {t' : S}, At 24 #[t₀.st.oracles.size]
      (flagsHead Z.first.shape ++ K1.flagsAt f ++ K1.flagsAt (laterF f t₃.st.oracles.size))
      (laterF (laterF f t₃.st.oracles.size) t₅.st.oracles.size) t' → t' = t →
      ∃ (t₀ : S) (r0 : List Fmt.RoundView) (q0 : List VerifiableInference.Desc.OpenedColumn) (n₄ n₆ : Nat)
        (f : ReqFrame), foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₀, r0, q0) ∧
        At 24 #[t₀.st.oracles.size] (headFl (flagsHead Z.first.shape) f n₄ n) (headF f n₄ n₆ n)
          t ∧
        f.moment = 1 ∧ f.link = 24 ∧ f.group = 24 ∧ f.shape = Z.first.shape := by
    intro t' H e
    subst e
    refine ⟨t₀, r0, q0, t₃.st.oracles.size, t₅.st.oracles.size, f, g0, ?_, mo, lk, gp, sh⟩
    unfold headFl headF
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    exact H
  by_cases h5 : n = 5
  · subst h5
    exact fin a6 (same g6 g)
  obtain ⟨t₇, r7, q7, g7⟩ := cut 7 (by omega)
  have a7 := at_quiet (step_quiet24 hS hR O (j := 7) (by omega) g6 g7) a6
  by_cases h6 : n = 6
  · subst h6
    exact fin a7 (same g7 g)
  obtain ⟨t₈, r8, q8, g8⟩ := cut 8 (by omega)
  have a8 := at_quiet (step_quiet24 hS hR O (j := 8) (by omega) g7 g8) a7
  by_cases h7 : n = 7
  · subst h7
    exact fin a8 (same g8 g)
  -- the batching, what runs behind it, the one equation
  obtain ⟨Lk, eL, hlen, hA⟩ := hear_flat24 hS hR O
  have hy : ∀ b₁, Lk.hear[1]? = some b₁ → ∃ s rs gs t, b₁.decide s rs gs = .ok t := by
    intro b₁ e1
    obtain ⟨b₁', e1', i1⟩ := hA 1 (by omega)
    obtain rfl : b₁ = b₁' := Option.some.inj (e1.symm.trans e1')
    obtain ⟨rs0, gs0, d0⟩ := fold_next i1 g0 g1
    exact ⟨_, _, _, _, d0⟩
  have hruns := hear_runs24 fr_refl fr_trans (fun _ _ => fr_of_quiet) hS hR O eL hy
  have step : ∀ k ≤ 2, ∀ s rs' qs' s' rs'' qs'',
      foldBlocks 0 (c.blocksInOrder.take (347 + k)) (ProofFile.startS Z p) R C = .ok (s, rs', qs') →
      foldBlocks 0 (c.blocksInOrder.take (347 + k + 1)) (ProofFile.startS Z p) R C = .ok (s', rs'', qs'') →
      Fr s s' := by
    intro k hk s rs' qs' s' rs'' qs'' u u'
    obtain ⟨b, ib⟩ : ∃ b, c.blocksInOrder[347 + k]? = some b := by
      cases hb : c.blocksInOrder[347 + k]? with
      | some b => exact ⟨b, rfl⟩
      | none =>
        exfalso
        have hl : c.blocksInOrder.length ≤ 347 + k := List.getElem?_eq_none_iff.1 hb
        obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
        obtain ⟨Lk', -, -, -, bC, eL', hlen', -, -, -, -, -, -, -, -, -, -, -, iC, -⟩ :=
          hfr 24 (by omega)
        rw [if_pos rfl] at hlen'
        rw [hlen'] at iC
        have := (List.getElem?_eq_some_iff.1 iC).1
        omega
    obtain ⟨rs, gs, d⟩ := fold_next ib u u'
    exact rest_front_of_runs fr_refl fr_trans
      (fun p _ hcl s rs gs t h => ⟨(batch_calm p fun a y k => (hcl a y k).1).1 s rs gs t h,
        batch_gby _ p (fun a y k => (hcl a y k).2) s rs gs t h⟩)
      (fun p s rs gs t h => ⟨oneEquation_calm (Cl := Unit) p s rs gs t h,
        oneEquation_gby _ (C := Unit) p s rs gs t h⟩)
      hS hR O (by omega : 24 < 25) eL hruns hk
      (by rw [hlen, show 14 * 24 + 9 + 2 + k = 347 + k by omega]; exact ib) s rs gs s' d
  obtain ⟨t₉, r9, q9, g9⟩ := cut 9 (by omega)
  have a9 := at_fr (step 0 (by omega) t₈ r8 q8 t₉ r9 q9 g8 g9) a8
  by_cases h8 : n = 8
  · subst h8
    exact fin a9 (same g9 g)
  obtain ⟨ta, ra, qa, ga⟩ := cut 10 (by omega)
  have aa := at_fr (step 1 (by omega) t₉ r9 q9 ta ra qa g9 ga) a9
  by_cases h9 : n = 9
  · subst h9
    exact fin aa (same ga g)
  obtain rfl : n = 10 := by omega
  exact fin (at_fr (step 2 (by omega) ta ra qa t r q ga g) aa) rfl

/-- walk_head's own sentence (Johnson/IMR/HeadMembers.lean) follows. -/
example (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {n : Nat} (hn : n ≤ 10) {t : S}
    {r : List Fmt.RoundView} {q : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (340 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ (n₀ n₄ n₆ : Nat) (f : ReqFrame),
      At 24 #[n₀] (headFl (flagsHead Z.first.shape) f n₄ n) (headF f n₄ n₆ n) t ∧
      f.moment = 1 ∧ f.link = 24 ∧ f.group = 24 ∧ f.shape = Z.first.shape :=
  let ⟨t₀, _, _, n₄, n₆, f, _, H⟩ := walk_head_named hS hR O hn g
  ⟨t₀.st.oracles.size, n₄, n₆, f, H⟩

/-- **AT EVERY CUT 340 + n, n ≤ 10: THE GROUP's MEMBERS BEHIND THE COUNT AT THE CUT 339.** -/
theorem members_head_named (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {n : Nat} (hn : n ≤ 10) {t : S}
    {r : List Fmt.RoundView} {q : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (340 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ (t₀ : S) (R₀ : List Fmt.RoundView) (C₀ : List VerifiableInference.Desc.OpenedColumn) (L : LinkCtx)
      (G : Group), foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀) ∧
      t.link? = some L ∧ L.link = 24 ∧ L.check.frame.group = 24 ∧ t.st.groups[24]? = some G ∧
      G.members = #[t₀.st.oracles.size] ++ L.check.frame.keptBefore ++ L.check.frame.own ∧
      G.kept.size = G.members.size ∧ G.members.toList.Nodup := by
  obtain ⟨t₀, R₀, C₀, n₄, n₆, f, f₀, H, -, -, gp, -⟩ := walk_head_named hS hR O hn g
  obtain ⟨L, G, hL, e2, e1, hG, em, -, es, hnd⟩ := H.members
  refine ⟨t₀, R₀, C₀, L, G, f₀, hL, e2, ?_, hG, em, es, hnd⟩
  rw [e1]
  unfold headF
  split
  · exact gp
  · split <;> exact gp

end

#print axioms flags_named
#print axioms size_at_table
#print axioms walk_head_named
#print axioms members_head_named

end Meaning.K2
