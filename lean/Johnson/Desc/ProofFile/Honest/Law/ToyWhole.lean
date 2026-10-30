-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ToyWhole.lean: theorems about the toy example of
Honest/Law/ToyRow.lean and about two sides of Honest/FrameToy.lean: a whole list's run in one
condition (`WholeAt`): from a condition before, where no part stops: the book gives the list its
coins, the list is played, the columns that the sub-protocol reads are available, the sub-protocol's
own step accepts, and a condition holds after it. That condition is proved at the four sides of
the example and at the two of Honest/FrameToy.lean. The theorems are about these files' own made-up
objects alone. None is one of the library's goals.

It names no field of `Good` (Honest/Side.lean): Honest/Law/ToyGood.lean derives that structure's two
fields on a whole list's run from it.

Limits.
  * A toy example.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ToyExact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Toy
open VerifiableInference.Desc (Place Block FileDescription OpenedColumn itemOf roundsFit drawsMarkedNonzeroHaveNonzeroWords need)
open VerifiableInference.Desc.BlockToy (St look send₃ ask tree tree₃ drawT sendS openA sendR orc)
open OnBytes.Slice (toF toE ofF ofE)
open Prob

/-! ## 1 A whole list's run in one condition -/

/-- **A whole list's run in one condition**: from A, where no part stops: the book gives the list
its coins, the list is played, the columns that the sub-protocol reads are available, the
sub-protocol's own step accepts, and B holds after it, at the state with the columns read laid in
(`Mid.took`), as in `Good.plays`. At a side without a fall the fields `plays` and `acc` of `Good`
both follow from it. -/
def WholeAt {S Cl V W X Pb : Type} (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (Bk : ProverCoinCounts)
    (chain firstTree : Nat) (A B : Coins Bk → S → Mid W X → Env → Prop) : Prop :=
  ∀ k s m E ds, A k s m E → drawsFit σ.block.rounds ds = true →
    σ.stopAt φ m.st.input m.loc ds = none →
    ∃ (c : RowCoins σ.half.parts) (y : List Played × Mid W X) (cols : List OpenedColumn) (s' : S) (n : Nat),
      lendRow Bk (Bk.rowsOf chain) (k.look chain) σ.block.place σ.half.parts 0 = .ok c ∧
      play (σ.half.steps σ.block (φ.sees m.st.input) c) ds [] m = .ok y ∧
      fillCols (readsOf chain firstTree (E.add y.1).stored (E.add y.1).tree σ.block.rounds ds) [] =
        .ok cols ∧
      σ.block.step firstTree s (roundsOf y.1) cols = .ok (s', n) ∧
      B k s' (y.2.took cols) (E.add y.1)

theorem look_whole (Bk : ProverCoinCounts) (hL : LendsLook Bk) :
    WholeAt .shared zSide Bk 1 0 noTree lookSent := by
  intro k s m E ds hA hd _
  have hd' : drawsFit [{ entry := sendS }, { entry := openA, opens := [(tree, .own 0)] }] ds =
    true := hd
  obtain ⟨R₀, R₁, rfl, h₀, h₁⟩ := drawsFit_two hd'
  obtain ⟨x, hx⟩ := one_of_length (poss_of_drawFit h₁)
  obtain ⟨el, ps, tr, dg⟩ := R₁
  have hx' : ps = [x] := hx
  subst hx'
  obtain ⟨st, tre, sent⟩ := E
  have hs : sent = 0 := hA
  subst hs
  obtain ⟨c₀, e₀, cu, hc, ht, hu⟩ := hL k
  obtain ⟨m', hy, hm'⟩ := play_look c₀ e₀ cu m R₀ ⟨el, [x], tr, dg⟩
  refine ⟨_, _, [(0, x % 2 ^ 3, [ofF (toF (m.st.input.w₀.a (x % 2 ^ 3)) + c₀.f ⟨0, by decide⟩ +
      c₀.f ⟨1, by decide⟩ + c₀.f ⟨1, by decide⟩)])],
    { s with total := s.total + (ofF (toF (m.st.input.w₀.a (x % 2 ^ 3)) + c₀.f ⟨0, by decide⟩ +
      c₀.f ⟨1, by decide⟩ + c₀.f ⟨1, by decide⟩)).toNat }, 1, hc, hy,
    by with_unfolding_all rfl, ?_, ?_⟩
  · exact VerifiableInference.Desc.Block.step_ok.2
      ⟨(roundsFit_cons (by with_unfolding_all rfl) h₀).trans
          ((roundsFit_cons (by with_unfolding_all rfl) h₁).trans (by with_unfolding_all rfl)),
        by with_unfolding_all rfl,
        by with_unfolding_all rfl, by with_unfolding_all rfl⟩
  · unfold lookSent hasTree
    refine ⟨rfl, _, rfl, rfl, fun p _ => ?_⟩
    show toF (m.st.input.w₀.a p) + c₀.f ⟨0, by decide⟩ + c₀.f ⟨1, by decide⟩ +
        c₀.f ⟨1, by decide⟩ =
      toF (m'.st.input.w₀.a p) + coinAt k 1 zO 0 + coinAt k 1 zO 1 + coinAt k 1 zO 1
    rw [ht, hu, hm']

theorem send_whole : WholeAt .own ySide₂ By 2 Fy.lastChainFirstTreeNumber noTree sendSent := by
  intro k s m E ds hA hd _
  have hd' : drawsFit [{ entry := { name := "CS", msg := 32, roots := 1 } }] ds = true := hd
  obtain ⟨R, rfl, h₀⟩ := drawsFit_one hd'
  obtain ⟨st, tre, sent⟩ := E
  have hs : sent = 0 := hA
  subst hs
  obtain ⟨c₀, hc, hv⟩ := lend_send k
  obtain ⟨m', hy, hm'⟩ := play_sendRow c₀ m R
  refine ⟨_, _, [], s, 0, hc, hy, by with_unfolding_all rfl, ?_, ?_⟩
  · exact VerifiableInference.Desc.Block.step_ok.2
      ⟨(roundsFit_cons (by with_unfolding_all rfl) h₀).trans (by with_unfolding_all rfl),
        by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩
  · unfold sendSent hasTree
    refine ⟨rfl, _, rfl, rfl, fun p _ => ?_⟩
    show toF (m.st.input.trace.b p) + c₀.f ⟨0, by decide⟩ =
      toF (m'.st.input.trace.b p) + coinAt k 2 sSend 0
    rw [hv, hm']

theorem carry_whole : WholeAt .own ySide₄ By 2 Fy.lastChainFirstTreeNumber anyAt anyAt := by
  intro k s m E ds _ hd _
  have hd' : drawsFit [{ entry := { name := "CS", msg := 24 } }] ds = true := hd
  obtain ⟨R, rfl, h₀⟩ := drawsFit_one hd'
  obtain ⟨c, ca, hc⟩ := lend_carry k
  obtain ⟨m', hy⟩ := play_cS m c ca R
  refine ⟨_, _, [], s, 0, hc, hy, by with_unfolding_all rfl, ?_, trivial⟩
  exact VerifiableInference.Desc.Block.step_ok.2
    ⟨(roundsFit_cons (by with_unfolding_all rfl) h₀).trans (by with_unfolding_all rfl),
      by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩

/-- Before `BlockToy.ask`: the verifier's running total is odd. -/
def oddAt {Bk : ProverCoinCounts} {W : Type} : Coins Bk → St → Mid W Nat → Env → Prop :=
  fun _ s _ _ => s.total % 2 = 1

theorem zSide₂_whole : WholeAt .own zSide₂ Bz 2 Fz.lastChainFirstTreeNumber oddAt anyAt := by
  intro k s m E ds hA hd _
  have hd' : drawsFit [{ entry := { name := "CS", msg := 24 } }] ds = true := hd
  obtain ⟨R, rfl, h₀⟩ := drawsFit_one hd'
  have hodd : (s.total % 2 == 1) = true := beq_iff_eq.2 hA
  obtain ⟨c, ca, hc⟩ := lend_zCarry k
  obtain ⟨m', hy⟩ := play_cS m c ca R
  refine ⟨_, _, [], s, 0, hc, hy, by with_unfolding_all rfl, ?_, trivial⟩
  refine VerifiableInference.Desc.Block.step_ok.2
    ⟨(roundsFit_cons (by with_unfolding_all rfl) h₀).trans (by with_unfolding_all rfl),
      by with_unfolding_all rfl, ?_, by with_unfolding_all rfl⟩
  show ((need "ask.odd" (s.total % 2 == 1)).bind fun _ => _) = Except.ok s
  rw [hodd]
  rfl

theorem tell_whole : WholeAt .own ySide₃ By 2 Fy.lastChainFirstTreeNumber sendSent sendSent := by
  intro k s m E ds hA hd _
  have hd' : drawsFit [{ entry := drawT, opens := [(tree₃, .own 0)] },
      { entry := { name := "CS", msg := 24 } }] ds = true := hd
  obtain ⟨R₀, R₁, rfl, h₀, h₁⟩ := drawsFit_two hd'
  obtain ⟨x, hx⟩ := one_of_length (poss_of_drawFit h₀)
  obtain ⟨el, ps, tr, dg⟩ := R₀
  have hx' : ps = [x] := hx
  subst hx'
  obtain ⟨st, tre, sent⟩ := E
  obtain ⟨hs, T, hT, hw, hsym⟩ := hA
  have hs' : sent = 1 := hs
  subst hs'
  obtain ⟨lg, w, sym⟩ := T
  have hw' : w = 1 := hw
  subst hw'
  have hsym' : sym = fun p _ => toF (m.st.input.trace.b p) + coinAt k 2 sSend 0 :=
    funext fun p => funext fun i => hsym p i
  subst hsym'
  have hT' : tre (.own 0) = some (pSend,
      ⟨lg, 1, fun p _ => toF (m.st.input.trace.b p) + coinAt k 2 sSend 0⟩) := hT
  obtain ⟨c₀, cv, hc, hv⟩ := lend_tell k
  obtain ⟨m', hy, hm'⟩ := play_tell c₀ cv m ⟨el, [x], tr, dg⟩ R₁
  rw [hv] at hy
  refine ⟨_, _, [(tree₃.tree - Fy.lastChainFirstTreeNumber, x % 2 ^ 2,
    [ofF (toF (m.st.input.trace.b (x % 2 ^ 2)) + coinAt k 2 sSend 0)])], s, 1, hc, hy, ?_, ?_, ?_⟩
  · refine (congrArg (fun q => fillCols q [])
      (reads_tell st tre _ Fy.lastChainFirstTreeNumber el x tr dg R₁)).trans ?_
    show fillCols [⟨tree₃.tree - Fy.lastChainFirstTreeNumber, x % 2 ^ 2, none, some (2, 0),
      (tre (.own 0)).map (·.1), (tre (.own 0)).map (·.2.col (x % 2 ^ 2)), 1⟩] [] = _
    rw [hT']
    rfl
  · exact VerifiableInference.Desc.Block.step_ok.2
      ⟨(roundsFit_cons (by with_unfolding_all rfl) h₀).trans
          ((roundsFit_cons (by with_unfolding_all rfl) h₁).trans (by with_unfolding_all rfl)),
        by with_unfolding_all rfl,
        tell_decide s _ _ _ _, by with_unfolding_all rfl⟩
  · unfold sendSent hasTree
    exact ⟨rfl, _, hT', rfl, fun p _ =>
      congrArg (fun w : L => toF (w.trace.b p) + coinAt k 2 sSend 0) hm'.symm⟩

end ProofFile.Honest.Toy

#print axioms ProofFile.Honest.Toy.look_whole
#print axioms ProofFile.Honest.Toy.send_whole
#print axioms ProofFile.Honest.Toy.carry_whole
#print axioms ProofFile.Honest.Toy.zSide₂_whole
#print axioms ProofFile.Honest.Toy.tell_whole
#print axioms ProofFile.Honest.Toy.WholeAt
#print axioms ProofFile.Honest.Toy.oddAt
