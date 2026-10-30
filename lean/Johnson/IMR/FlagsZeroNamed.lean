-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FlagsZeroNamed.lean: flags_named (Johnson/IMR/FlagsNamed.lean) AT LINK 0: at the cuts
8 + n, n ≤ 4 (n = 4: in front of the closing): THE GROUP's MEMBERS ARE THE FRAME's LIST own: THREE
RANGES: the first from 0, the others behind the state's counts of oracle messages at the cuts 5 and
7 of the same fold (in front of the two later sendings); AND THE GROUP's FLAGS "kept" IN THE PUBLIC
SHAPE's WORDS: at the proof file's seat, in the goals' scope, from the fold's return alone. One
theorem, proved: calls.


Compiled with the whole library.
  flags_zero_named   no code switch stands in front of link 0: so no number stands in front of the
    two lists, keptBefore is empty, and the flags lack flags_at's first entry and the target's part.
HOW. entry_at_zero (Johnson/IMR/FrameEntry.lean): behind link 0's first sub-protocol. walk_c
(Johnson/IMR/FrameAt.lean): it runs at every l < 24. At.members. The start's frame in the public
shape's
words: laid_is_start, open_recAll, K2.atMoment_pub; the first state has no message: start_msgs
(Johnson/IMR/KeptJoin.lean).
sh := Z.first.shape.

OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: kind K10's files. LETTERS: none.

What is not claimed. The counts at 5 and 7 as closed numbers (in the table's words: size_at_table).
Anything on the group's field inRun. That a fold returns is shown of no proof here. No soundness.

-/
import Johnson.IMR.FlagsNamed
import Johnson.IMR.KeptJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE MEMBERS AND THE FLAGS AT LINK 0.** -/
theorem flags_zero_named (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {n : Nat} (hn : n ≤ 4) {t : S}
    {r : List Fmt.RoundView} {q : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (8 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ (t₃ t₅ : S) (R₃ R₅ : List Fmt.RoundView) (C₃ C₅ : List VerifiableInference.Desc.OpenedColumn)
      (L : LinkCtx) (G : Group),
      foldBlocks 0 (c.blocksInOrder.take 5) (ProofFile.startS Z p) R C = .ok (t₃, R₃, C₃) ∧
      foldBlocks 0 (c.blocksInOrder.take 7) (ProofFile.startS Z p) R C = .ok (t₅, R₅, C₅) ∧
      t.link? = some L ∧ L.link = 0 ∧ t.st.groups[0]? = some G ∧
      G.members = L.check.frame.own ∧ L.check.frame.keptBefore = #[] ∧
      L.check.frame.own =
        (Array.range (msgsAt Z.first.shape 0 0)).map (· + 0) ++
          (Array.range (msgsAt Z.first.shape 0 1)).map (· + t₃.st.oracles.size) ++
          (Array.range (msgsAt Z.first.shape 0 2)).map (· + t₅.st.oracles.size) ∧
      G.kept.toList =
        (((K2.frameAtLink Z.first.shape 0).atMoment 0).map fun m => decide (0 < m.life)) ++
        (((K2.frameAtLink Z.first.shape 0).atMoment 1).map fun m => decide (0 < m.life)) ++
        (((K2.frameAtLink Z.first.shape 0).atMoment 2).map fun m => decide (0 < m.life)) := by
  have g' : foldBlocks 0 (c.blocksInOrder.take (14 * 0 + 8 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q) := by
    rw [show 14 * 0 + 8 + n = 8 + n by omega]
    exact g
  obtain ⟨t₅, R₅, C₅, f₅⟩ := fold_cut (k := 14 * 0 + 7) (n + 1)
    (by rw [show 14 * 0 + 7 + (n + 1) = 8 + n by omega]; exact g)
  obtain ⟨t₃, R₃, C₃, f₃⟩ := fold_cut (k := 14 * 0 + 5) 2 f₅
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 14 * 0 + 3) 2 f₃
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * 0 + 2) f₁
  obtain ⟨f, a1, a2, mo, lk, hg, -, sh, kb, ow⟩ := entry_at_zero hS hR O f₁
  obtain ⟨-, hk⟩ := laid_at hS hR O (by omega : 0 < 25) f₀
  have Rr : RecAll Z.first.codes Z.first.shape t₀ := open_recAll hS hR O (by omega)
    (by have k := draw_in_front hS hR O (l := 0) (i := 0) (by omega) (by decide); omega) f₀
  obtain rfl : t₀ = ProofFile.startS Z p := laid_is_start hS hR O f₀
  have s1 : f.shape = Z.first.shape := sh.trans Rr.walk.shape
  have ea : (ProofFile.startS Z p).check.frame.atMoment 0 =
      (K2.frameAtLink Z.first.shape 0).atMoment 0 := K2.atMoment_pub Rr.walk hk 0
  have e0 : (ProofFile.startS Z p).st.oracles.size = 0 := by
    rw [start_msgs O.pub p]
    rfl
  obtain ⟨L, G, hL, e2, e1, hG, em, ek, -, -⟩ :=
    (walk_c hS hR O (by omega : 0 < 24) f₁ f₃ f₅ hg a1 a2 n hn t r q g').members
  have m2 : (laterF f t₃.st.oracles.size).moment = 2 := by
    show f.moment + 1 = 2
    rw [mo]
  have ekb : L.check.frame.keptBefore = #[] := by
    rw [e1]
    exact kb
  refine ⟨t₃, t₅, R₃, R₅, C₃, C₅, L, G, f₃, f₅, hL, e2, hG, ?_, ekb, ?_, ?_⟩
  · rw [em, ekb, Array.empty_append, Array.empty_append]
  · rw [e1]
    show f.own ++ (Array.range (f.atMoment f.moment).length).map (· + t₃.st.oracles.size) ++
        (Array.range ((laterF f t₃.st.oracles.size).atMoment
          (laterF f t₃.st.oracles.size).moment).length).map (· + t₅.st.oracles.size) = _
    unfold msgsAt
    rw [m2, mo, atMoment_of s1 lk, atMoment_of (f := laterF f t₃.st.oracles.size) s1 lk, ow, ea,
      e0]
  · have k1 : K1.flagsAt f =
        ((K2.frameAtLink Z.first.shape 0).atMoment 1).map fun m => decide (0 < m.life) := by
      unfold K1.flagsAt
      rw [mo, atMoment_of s1 lk]
    have k2 : K1.flagsAt (laterF f t₃.st.oracles.size) =
        ((K2.frameAtLink Z.first.shape 0).atMoment 2).map fun m => decide (0 < m.life) := by
      unfold K1.flagsAt
      rw [m2, atMoment_of (f := laterF f t₃.st.oracles.size) s1 lk]
    rw [ek, k1, k2, ea]

end

#print axioms flags_zero_named

end Meaning.K2
