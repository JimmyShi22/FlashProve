-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/FreshSize.lean: how many groups the statement has inside a segment of the proof file's first chain: at every cut
from behind the segment's first sub-protocol up to its closing it has one group more than the segment's number.

  `count_in_link`   segment l < 24, the cuts 14 l + 3 + n, n ≤ 9: l + 1 groups
  `count_in_head`   the last segment, the cuts 340 + n, n ≤ 10: 25 groups

How. The library has the count in front of each segment (`count_at`, Johnson/IMR/GroupCount.lean) and shows inside the
proofs of `link_one` (same file) and `head_one` (Johnson/IMR/FinCount.lean) that no sub-protocol behind a segment's first
changes it. These two proofs ask a fold up to the next segment. Here their steps are taken from a fold that ends inside the
segment. The two lemmas stand in the namespace of these files.

Limits. From a fold's return alone; that a fold returns is not shown here.
-/
import Johnson.IMR.FinCount
import Johnson.IMR.GroupCount
import Johnson.IMR.EndFive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Inside segment l < 24 the statement has l + 1 groups.** -/
theorem count_in_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} :
    ∀ n ≤ 9, ∀ (t : S) (r : List Fmt.RoundView) (q : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      t.st.groups.size = l + 1 := by
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, f, bL, bB, bC, eL, hlen, -⟩ := hfr l (by omega)
  rw [if_neg (by omega : ¬ l = 24)] at hlen
  intro n
  induction n with
  | zero =>
    intro _ t r q g
    obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * l + 2) g
    rw [first_one hS hR O h24 f₀ g, count_at hS hR O l (by omega) t₀ R₀ C₀ f₀]
  | succ n ih =>
    intro hn t' r' q' g'
    obtain ⟨t, r, q, g⟩ := fold_back (k := 14 * l + 3 + n) g'
    obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 14 * l + 3) n g
    obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * l + 2) f₁
    have hy : ∀ b₀, Lk.hear[0]? = some b₀ → ∃ s rs gs t, b₀.decide s rs gs = .ok t := by
      intro b₀ e0
      have i0 : c.blocksInOrder[14 * l + 2]? = some b₀ := by
        have q := IM.hear_at_flat eL e0
        rwa [(IM.flatIx_scope hS hR O (by omega : l ≤ 24) 0).trans
          (by omega : 14 * l + 0 + 2 = 14 * l + 2)] at q
      obtain ⟨rs0, gs0, d0⟩ := fold_next i0 f₀ f₁
      exact ⟨_, _, _, _, d0⟩
    have hlenF : 14 * l + 3 + n < c.blocksInOrder.length := by
      rw [flat_358 hS O]
      omega
    obtain ⟨b, ib⟩ : ∃ b, c.blocksInOrder[14 * l + 3 + n]? = some b :=
      ⟨_, List.getElem?_eq_getElem hlenF⟩
    obtain ⟨rs, gs, d⟩ := fold_next ib g g'
    have w : Sz t t' := by
      by_cases h5 : n ≤ 5
      · obtain ⟨b', e⟩ : ∃ b', Lk.hear[n + 1]? = some b' :=
          ⟨_, List.getElem?_eq_getElem (by omega : n + 1 < Lk.hear.length)⟩
        have ib' : c.blocksInOrder[14 * l + 3 + n]? = some b' := by
          have k := IM.hear_at_flat eL e
          rwa [(IM.flatIx_scope hS hR O (by omega : l ≤ 24) (n + 1)).trans
            (by omega : 14 * l + (n + 1) + 2 = 14 * l + 3 + n)] at k
        obtain rfl := Option.some.inj (ib.symm.trans ib')
        exact hear_by sz_trans (fun _ _ => sz_of_quiet) (fun _ _ _ _ _ _ _ _ => sz_commit)
          hS hR O h24 (by omega) (by omega) eL e t rs gs t' d
      · have ib' : c.blocksInOrder[14 * l + 9 + (n - 6)]? = some b := by
          rw [show 14 * l + 9 + (n - 6) = 14 * l + 3 + n by omega]
          exact ib
        exact rest_by sz_refl sz_trans (fun _ _ => sz_of_quiet) (fun p _ hcl => batch_sz p hcl)
          closeOf_sz hS hR O h24 eL hy (by omega) ib' t rs gs t' d
    have w' : t'.st.groups.size = t.st.groups.size := w
    rw [w', ih (by omega) t r q g]

/-- **Inside the last segment the statement has 25 groups.** -/
theorem count_in_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} :
    ∀ n ≤ 10, ∀ (t : S) (r : List Fmt.RoundView) (q : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (338 + (2 + n))) (ProofFile.startS Z p) R C = .ok (t, r, q) →
      t.st.groups.size = 25 := by
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, f, bL, bB, bC, eL, hlen, -⟩ := hfr 24 (by omega)
  rw [if_pos rfl] at hlen
  have hearAt : ∀ j < 9, ∃ b, Lk.hear[j]? = some b ∧ c.blocksInOrder[338 + j]? = some b := by
    intro j hj
    obtain ⟨b, e⟩ : ∃ b, Lk.hear[j]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by omega : j < Lk.hear.length)⟩
    refine ⟨b, e, ?_⟩
    have q := IM.hear_at_flat eL e
    rwa [(IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) j).trans
      (by omega : 14 * 24 + j + 2 = 338 + j)] at q
  intro n
  induction n with
  | zero =>
    intro _ t₁ R₁ C₁ f₁
    obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 338 + 1) f₁
    obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 338) f₀
    obtain ⟨Lk0, b0, eL0, e0, hj, -⟩ := IM.k7_sits hS hR O
    obtain rfl : Lk = Lk0 := Option.some.inj (eL.symm.trans eL0)
    obtain ⟨b0', e0', i0⟩ := hearAt 0 (by omega)
    obtain rfl : b0 = b0' := Option.some.inj (e0.symm.trans e0')
    obtain ⟨rs0, gs0, d0⟩ := fold_next i0 fm f₀
    obtain ⟨x, a, hx, ha, -, es, ec⟩ := h1_front (IM.k7_sits_yes hS hR O hj d0).1
    have s0 : t₀.st.groups.size = tm.st.groups.size + 1 := by
      rw [es, (K2.firstFront_st hx).1]
      simp [K2.withFresh]
    obtain ⟨L0, G0, S0, g, fa⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 hx
    have hfx : K2.frontAt headQ t₀ = some (K2.headFrontOf t₀ a G0.target) := by
      unfold K2.frontAt
      rw [show headQ.stands = .head from rfl, ha, ec, fa.group]
      rfl
    have s1 : t₁.st.groups.size = t₀.st.groups.size := (head_gains hS hR O f₀ f₁ rfl hfx).1.1
    rw [s1, s0, count_at hS hR O 24 (by omega) tm Rm Cm fm]
  | succ n ih =>
    intro hn t' r' q' g'
    obtain ⟨t, r, q, g⟩ := fold_back (k := 338 + (2 + n)) g'
    obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 338 + 2) n
      (by rw [show 338 + 2 + n = 338 + (2 + n) by omega]; exact g)
    obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 338 + 1) f₁
    obtain ⟨b1, e1, i1⟩ := hearAt 1 (by omega)
    obtain ⟨rs1, gs1, d1⟩ := fold_next i1 f₀ f₁
    have hy : ∀ b₁, Lk.hear[1]? = some b₁ → ∃ s rs gs t, b₁.decide s rs gs = .ok t := by
      intro b₁ e
      obtain rfl : b1 = b₁ := Option.some.inj (e1.symm.trans e)
      exact ⟨_, _, _, _, d1⟩
    have hruns := hear_runs24 sz_refl sz_trans (fun _ _ => sz_of_quiet) hS hR O eL hy
    have w : Sz t t' := by
      by_cases h8 : 2 + n ≤ 8
      · obtain ⟨b, e, ib⟩ := hearAt (2 + n) (by omega)
        obtain ⟨rs, gs, d⟩ := fold_next ib g g'
        exact hear_by24 sz_trans (fun _ _ => sz_of_quiet) (fun _ _ _ _ _ _ _ _ => sz_commit)
          hS hR O (by omega) h8 eL e t rs gs t' d
      · obtain ⟨b, ib⟩ : ∃ b, c.blocksInOrder[338 + (2 + n)]? = some b :=
          ⟨_, List.getElem?_eq_getElem (by
            rw [flat_358 hS O]
            omega)⟩
        obtain ⟨rs, gs, d⟩ := fold_next ib g g'
        exact rest_of_runs sz_refl sz_trans (fun p _ hcl => batch_sz p hcl) closeOf_sz hS hR O
          (by omega : 24 < 25) eL hruns (n := 2 + n - 9) (by omega)
          (by rw [hlen, show 14 * 24 + 9 + 2 + (2 + n - 9) = 338 + (2 + n) by omega]; exact ib)
          t rs gs t' d
    have w' : t'.st.groups.size = t.st.groups.size := w
    rw [w', ih (by omega) t r q g]

end Meaning.K2

#print axioms Meaning.K2.count_in_link
#print axioms Meaning.K2.count_in_head
