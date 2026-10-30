-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FlagsHeadNamed.lean: flags_named (Johnson/IMR/FlagsNamed.lean) AT THE HEAD's LINK: at
the
cuts 340 + n, 5 ≤ n ≤ 10 (n = 10: in front of the closing): THE GROUP's MEMBERS, AND keptBefore AND
own AS RANGES, OFF THE STATE's COUNTS OF ORACLE MESSAGES AT THREE CUTS OF THE SAME FOLD: 339 (in
front of "H:2", the code switch), 342 and 344 (in front of the two later sendings): at the proof
file's seat, in the goals' scope, from the fold's return alone. One theorem, proved: calls.


Compiled with the whole library.
  flags_head_named   flags_named's sentence, letter for letter, at l := 24, with the cuts 339, 342,
    344 in the place of 14 l + 2, 14 l + 5, 14 l + 7.
HOW. members_head_named: the members. entry_head_frame (Johnson/IMR/FrameAll.lean): the frame behind
"H:2",
its two lists as ranges off the count at 339, in the words of the frame's own group's target.
frame_walk_head (the same file): the open link's frame at 340 + k is seqF f n₃ n₅ k, n₃ and n₅ the
counts at 342 and 344. One link is open at t: so the two contexts are one. The words are turned to
the public shape's as at_head_entry's own proof (Johnson/IMR/FinKept.lean) turns them:
front_pin_head,
K2.atMoment_pub, atMoment_of.
sh := Z.first.shape.

OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USER: kind K10's files. LETTERS: none.

What is not claimed. The counts at 342 and 344 as closed numbers (the first: n0_at_head_paid,
Johnson/IMR/ToldPaid.lean; all three in the table's words: size_at_table). Anything at n < 5: in
front of the
second later sending "own" is shorter. That a fold returns is shown of no proof here. No soundness.

-/
import Johnson.IMR.FlagsNamed

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

/-- **THE MEMBERS, keptBefore AND own, OFF THREE COUNTS OF THE SAME FOLD: THE HEAD's LINK.** -/
theorem flags_head_named (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub}
    {R : List Fmt.RoundView} {C : List VerifiableInference.Desc.OpenedColumn} {n : Nat} (h5 : 5 ≤ n)
    (hn : n ≤ 10) {t : S} {r : List Fmt.RoundView} {q : List VerifiableInference.Desc.OpenedColumn}
    (g : foldBlocks 0 (c.blocksInOrder.take (340 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∃ (t₀ t₃ t₅ : S) (R₀ R₃ R₅ : List Fmt.RoundView) (C₀ C₃ C₅ : List VerifiableInference.Desc.OpenedColumn)
      (L : LinkCtx) (G : Group),
      foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀) ∧
      foldBlocks 0 (c.blocksInOrder.take 342) (ProofFile.startS Z p) R C = .ok (t₃, R₃, C₃) ∧
      foldBlocks 0 (c.blocksInOrder.take 344) (ProofFile.startS Z p) R C = .ok (t₅, R₅, C₅) ∧
      t.link? = some L ∧ L.link = 24 ∧ t.st.groups[24]? = some G ∧
      G.members = #[t₀.st.oracles.size] ++ L.check.frame.keptBefore ++ L.check.frame.own ∧
      L.check.frame.keptBefore = (Array.range (K2.targetAt Z.first.shape 24).kept.size).map
        (· + (t₀.st.oracles.size + 1)) ∧
      L.check.frame.own =
        (Array.range (msgsAt Z.first.shape 24 0)).map
            (· + (t₀.st.oracles.size + (1 + (K2.targetAt Z.first.shape 24).kept.size))) ++
          (Array.range (msgsAt Z.first.shape 24 1)).map (· + t₃.st.oracles.size) ++
          (Array.range (msgsAt Z.first.shape 24 2)).map (· + t₅.st.oracles.size) := by
  obtain ⟨t₅, R₅, C₅, f₅⟩ := fold_cut (k := 344) (n - 4)
    (by rw [show 344 + (n - 4) = 340 + n by omega]; exact g)
  obtain ⟨t₃, R₃, C₃, f₃⟩ := fold_cut (k := 342) 2 f₅
  obtain ⟨t₂, R₂, C₂, f₂⟩ := fold_cut (k := 340) 2 f₃
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 339) f₂
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 338) f₀
  -- the members
  obtain ⟨t₀', R₀', C₀', L, G, f₀', hL, e2, -, hG, em, -, -⟩ := members_head_named hS hR O hn g
  obtain rfl : t₀ = t₀' := congrArg Prod.fst (Except.ok.inj (f₀.symm.trans f₀'))
  -- the frame behind "H:2", and at t
  obtain ⟨Gr, f, hGr, hk, HO, mo, lk, -, -, sh, kb, ow⟩ := entry_head_frame hS hR O f₀ f₂
  obtain ⟨L', hL', eF, -⟩ := (frame_walk_head hS hR O (n₃ := t₃.st.oracles.size)
    (n₅ := t₅.st.oracles.size)
    (fun _ _ _ h => congrArg (fun x : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn =>
      x.1.st.oracles.size) (Except.ok.inj (h.symm.trans f₃)))
    (fun _ _ _ h => congrArg (fun x : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn =>
      x.1.st.oracles.size) (Except.ok.inj (h.symm.trans f₅))) f₂ HO).1 n hn t r q g
  obtain rfl : L' = L := Option.some.inj (hL'.symm.trans hL)
  have eS : seqF f t₃.st.oracles.size t₅.st.oracles.size n =
      laterF (laterF f t₃.st.oracles.size) t₅.st.oracles.size := by
    unfold seqF
    rw [if_neg (by omega), if_neg (by omega)]
  rw [eS] at eF
  -- the words of the public shape
  obtain ⟨Lk, b0, eL, e0, hj, -⟩ := IM.k7_sits hS hR O
  have i0 : c.blocksInOrder[338]? = some b0 := by
    have k := IM.hear_at_flat eL e0
    rwa [(IM.flatIx_scope hS hR O (by decide : 24 ≤ 24) 0).trans (by omega : _ = 338)] at k
  obtain ⟨rs0, gs0, d0⟩ := fold_next i0 fm f₀
  obtain ⟨x, a, hx, ha, -, -, -⟩ := h1_front (IM.k7_sits_yes hS hR O hj d0).1
  have hfx : K2.frontAt headQ t₀ = some (K2.headFrontOf t₀ a Gr.target) := by
    unfold K2.frontAt
    rw [show headQ.stands = .head from rfl, ha, hk, hGr]
    rfl
  have Rr : RecAll Z.first.codes Z.first.shape t₀ := open_recAll hS hR O (by decide)
    (by have k := draw_in_front hS hR O (l := 24) (i := 1) (by decide) (by decide); omega) f₀
  obtain ⟨-, -, eT, -⟩ := front_pin_head hS hR O f₀ rfl hfx
  have eT' : Gr.target = K2.targetAt Z.first.shape 24 := eT
  have s1 : f.shape = Z.first.shape := sh.trans Rr.walk.shape
  refine ⟨t₀, t₃, t₅, R₀, R₃, R₅, C₀, C₃, C₅, L', G, f₀, f₃, f₅, hL, e2, hG, em, ?_, ?_⟩
  · rw [eF]
    show f.keptBefore = _
    rw [kb, eT']
  · rw [eF]
    show f.own ++ (Array.range (f.atMoment f.moment).length).map (· + t₃.st.oracles.size) ++
        (Array.range ((laterF f t₃.st.oracles.size).atMoment
          (laterF f t₃.st.oracles.size).moment).length).map (· + t₅.st.oracles.size) = _
    have m2 : (laterF f t₃.st.oracles.size).moment = 2 := by
      show f.moment + 1 = 2
      rw [mo]
    unfold msgsAt
    rw [m2, mo, atMoment_of s1 lk, atMoment_of (f := laterF f t₃.st.oracles.size) s1 lk, ow, eT',
      K2.atMoment_pub Rr.walk hk 0]

end

#print axioms flags_head_named

end Meaning.K2
