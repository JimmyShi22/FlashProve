-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/HeadMembers.lean: Johnson/IMR/FrameEntry.lean's members_at AND
Johnson/IMR/FlagsAt.lean's flags_at AT THE HEAD's LINK: at every cut 340 + n, n ≤ 10 (from behind
"H:2" to
in front of the closing): at the proof file's seat, in the goals' scope, from the fold's return
alone.
  headF, headFl: the frame and the flags by the cut's number.
  walk_head: THE WALK: there are a frame f (moment 1, link 24, group 24, the public shape) and
    numbers n₀, n₄, n₆ with: At 24 #[n₀] (Johnson/IMR/FrameAt.lean) with the frame f at n ≤ 2;
      laterF f n₄ at
    n = 3, 4; laterF (laterF f n₄) n₆ at 5 ≤ n ≤ 10; the flags grown alike. THE STATEMENT SAYS ONLY
    THAT SUCH NUMBERS ARE: in the proof they are the numbers of messages at the cuts 339, 342 and
    344; who wants them so takes Johnson/IMR/FrameAll.lean's frames.
  members_head: a link L is open, L.link = 24, L.check.frame.group = 24, and the statement's group
    number 24 has G.members = #[n₀] ++ L.check.frame.keptBefore ++ L.check.frame.own; a flag a
    member; no number twice. (n = 3: in front of kind K8's draw, the cut 343; n = 9: in front of
    the one equation, 349; n = 10: in front of the closing, 350.)
  flags_head: at 5 ≤ n ≤ 10: G.kept.toList = false :: the target's "kept again" ++ "life > 0" of
    the link's messages of moment 0 ++ of moment 1 ++ of moment 2, in the public shape's words.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USERS: kind K8's and K10's files.
The premises are laws' premises: that a fold returns is shown of no proof here. No soundness.
-/
import Johnson.IMR.FinKept

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

/-- The frame and the flags at the cut 340 + n of the head's link. -/
def headF (f : ReqFrame) (n₄ n₆ n : Nat) : ReqFrame :=
  if n ≤ 2 then f else if n ≤ 4 then laterF f n₄ else laterF (laterF f n₄) n₆

def headFl (fl : List Bool) (f : ReqFrame) (n₄ n : Nat) : List Bool :=
  if n ≤ 2 then fl else if n ≤ 4 then fl ++ K1.flagsAt f
  else fl ++ K1.flagsAt f ++ K1.flagsAt (laterF f n₄)

/-- **THE WALK OF THE HEAD's LINK, FROM BEHIND "H:2" TO IN FRONT OF ITS CLOSING.** Of the three
numbers the statement says only that they are. -/
theorem walk_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {n : Nat} (hn : n ≤ 10) {t : S}
    {r : List Fmt.RoundView} {q : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (340 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ (n₀ n₄ n₆ : Nat) (f : ReqFrame),
      At 24 #[n₀] (headFl (flagsHead Z.first.shape) f n₄ n) (headF f n₄ n₆ n) t ∧
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
    exact ⟨_, 0, 0, f, a1, mo, lk, gp, sh⟩
  obtain ⟨t₂, r2, q2, g2⟩ := cut 2 (by omega)
  have k2 := step_quiet24 hS hR O (j := 2) (by omega) g1 g2
  by_cases h1 : n = 1
  · subst h1
    obtain rfl : t₂ = t := same g2 g
    exact ⟨_, 0, 0, f, at_quiet k2 a1, mo, lk, gp, sh⟩
  obtain ⟨t₃, r3, q3, g3⟩ := cut 3 (by omega)
  have k3 := step_quiet24 hS hR O (j := 3) (by omega) g2 g3
  have a3 := at_quiet k3 (at_quiet k2 a1)
  have b3 := below_quiet k3 (below_quiet k2 b1)
  by_cases h2 : n = 2
  · subst h2
    obtain rfl : t₃ = t := same g3 g
    exact ⟨_, 0, 0, f, a3, mo, lk, gp, sh⟩
  obtain ⟨t₄, r4, q4, g4⟩ := cut 4 (by omega)
  obtain ⟨a4, b4⟩ := step_at24 hS hR O (j := 4) (Or.inl rfl) g3 g4 gp a3 b3
  by_cases h3 : n = 3
  · subst h3
    obtain rfl : t₄ = t := same g4 g
    exact ⟨_, t₃.st.oracles.size, 0, f, a4, mo, lk, gp, sh⟩
  obtain ⟨t₅, r5, q5, g5⟩ := cut 5 (by omega)
  have k5 := step_quiet24 hS hR O (j := 5) (by omega) g4 g5
  by_cases h4 : n = 4
  · subst h4
    obtain rfl : t₅ = t := same g5 g
    exact ⟨_, t₃.st.oracles.size, 0, f, at_quiet k5 a4, mo, lk, gp, sh⟩
  obtain ⟨t₆, r6, q6, g6⟩ := cut 6 (by omega)
  obtain ⟨a6, -⟩ := step_at24 hS hR O (j := 6) (Or.inr rfl) g5 g6
    (f := laterF f t₃.st.oracles.size) gp (at_quiet k5 a4) (below_quiet k5 b4)
  -- from here on the frame and the flags stay
  have fin : ∀ {t' : S}, At 24 #[t₀.st.oracles.size]
      (flagsHead Z.first.shape ++ K1.flagsAt f ++ K1.flagsAt (laterF f t₃.st.oracles.size))
      (laterF (laterF f t₃.st.oracles.size) t₅.st.oracles.size) t' → t' = t →
      ∃ (n₀ n₄ n₆ : Nat) (f : ReqFrame),
        At 24 #[n₀] (headFl (flagsHead Z.first.shape) f n₄ n) (headF f n₄ n₆ n) t ∧
        f.moment = 1 ∧ f.link = 24 ∧ f.group = 24 ∧ f.shape = Z.first.shape := by
    intro t' H e
    subst e
    refine ⟨t₀.st.oracles.size, t₃.st.oracles.size, t₅.st.oracles.size, f, ?_, mo, lk, gp, sh⟩
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

/-- **AT EVERY CUT 340 + n, n ≤ 10: THE GROUP's MEMBERS ARE THE FRAME's TWO LISTS BEHIND ONE
NUMBER.** -/
theorem members_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {n : Nat} (hn : n ≤ 10) {t : S}
    {r : List Fmt.RoundView} {q : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (340 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ (L : LinkCtx) (G : Group) (n₀ : Nat), t.link? = some L ∧ L.link = 24 ∧
      L.check.frame.group = 24 ∧ t.st.groups[24]? = some G ∧
      G.members = #[n₀] ++ L.check.frame.keptBefore ++ L.check.frame.own ∧
      G.kept.size = G.members.size ∧ G.members.toList.Nodup := by
  obtain ⟨n₀, n₄, n₆, f, H, -, -, gp, -⟩ := walk_head hS hR O hn g
  obtain ⟨L, G, hL, e2, e1, hG, em, -, es, hnd⟩ := H.members
  refine ⟨L, G, n₀, hL, e2, ?_, hG, em, es, hnd⟩
  rw [e1]
  unfold headF
  split
  · exact gp
  · split <;> exact gp

/-- **THE GROUP's FLAGS IN THE SHAPE's WORDS, AT THE CUTS 340 + n, 5 ≤ n ≤ 10** (n = 10: in front of
the closing). -/
theorem flags_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {n : Nat} (h5 : 5 ≤ n)
    (hn : n ≤ 10) {t : S} {r : List Fmt.RoundView} {q : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (340 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ G : Group, t.st.groups[24]? = some G ∧
      G.kept.toList = false :: (K2.targetAt Z.first.shape 24).kept.toList.map (·.keptAgain) ++
        (((K2.frameAtLink Z.first.shape 24).atMoment 0).map fun m => decide (0 < m.life)) ++
        (((K2.frameAtLink Z.first.shape 24).atMoment 1).map fun m => decide (0 < m.life)) ++
        (((K2.frameAtLink Z.first.shape 24).atMoment 2).map fun m => decide (0 < m.life)) := by
  obtain ⟨n₀, n₄, n₆, f, H, mo, lk, -, sh⟩ := walk_head hS hR O hn g
  obtain ⟨G, hG, -, ek, -, -⟩ := H.group
  refine ⟨G, hG, ?_⟩
  have k1 : K1.flagsAt f =
      ((K2.frameAtLink Z.first.shape 24).atMoment 1).map fun m => decide (0 < m.life) := by
    unfold K1.flagsAt
    rw [mo, atMoment_of sh lk]
  have k2 : K1.flagsAt (laterF f n₄) =
      ((K2.frameAtLink Z.first.shape 24).atMoment 2).map fun m => decide (0 < m.life) := by
    unfold K1.flagsAt
    have m2 : (laterF f n₄).moment = 2 := by
      show f.moment + 1 = 2
      rw [mo]
    rw [m2, atMoment_of (f := laterF f n₄) sh lk]
  rw [ek]
  unfold headFl
  rw [if_neg (by omega), if_neg (by omega), k1, k2]
  rfl

end

#print axioms walk_head
#print axioms members_head
#print axioms flags_head

end Meaning.K2
