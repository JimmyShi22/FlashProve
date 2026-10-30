-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ToyFallWhole.lean: theorems about the toy example of
Honest/Law/ToyFall.lean: a whole list's run in one condition (`WholeAt`, Honest/Law/ToyWhole.lean)
at the seven sides whose sub-protocol accepts from the condition before it; at the eighth, "weigh",
whose sub-protocol can reject there: that the list is played at all coins, that the condition after
it holds wherever the sub-protocol accepts, that it accepts where the weight is not 1, and that it
rejects where the weight is 1. The theorems are about these files' own made-up objects alone. None
is one of the library's goals.

  1  `vNum`, `vAt`, `vSent`, `vWord`, `vLate`   the conditions before and after
  2  `vlend_…`, `vplay_…`   what the book gives each list, and what is played
  3  `v…_whole`, `weigh_keeps`, `vW_plays`, `vW_yes`, `weigh_refuses`   side by side

It names no field of `Good` (Honest/Side.lean) and no fall: Honest/Law/ToyFallGood.lean puts these
into that structure.

Limits.
  * A toy example.
  * Among the hypotheses that the prose above does not name: `drawsFit` (`drawFit` round by round,
    and as many challenges as rounds): `vW_plays`, `vW_yes`.
  * No part of the example reads what it is handed as `Seen`, so none reads the field `opened`: what
    the hypotheses here ask of that field is met for free. Of a prover with a part that reads the
    columns nothing is shown here.
  * No condition here (`vAt`, `vSent`, `vLate`) reads the field either: each theorem holds at every
    value of it, `none` too, and `Mid.took` changes nothing that a condition reads.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ToyFallLaws
import Johnson.Desc.ProofFile.Honest.Law.ToyWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Toy
open VerifiableInference.Desc (Place Block FileDescription OpenedColumn itemOf roundsFit drawsMarkedNonzeroHaveNonzeroWords need)
open VerifiableInference.Desc.BlockToy (St tree₃ drawD orc)
open OnBytes.Slice (toF toE ofF ofE)
open Prob

/-! ## 1 The conditions before and after -/

/-- The number that the verifier's state takes at "own a", from a run's coins and the index. -/
def vNum (k : Coins Bv) (m : Mid L Nat) : Nat :=
  (ofF (toF m.st.input.w₀.ans + coinAt k 2 vaA 0 + coinAt k 2 vaA 1)).toNat

/-- After "own a", up to "spend": no tree yet; the state's total is the first owner's word, from
this run's coins, as a number. -/
def vAt : Coins Bv → St → Mid L Nat → Env → Prop := fun k s m E =>
  E.sent = 0 ∧ s.total = vNum k m

/-- After "spend": one tree; its word at p is the index's plus a plus b, from this run's coins; the
state's total as before. -/
def vSent : Coins Bv → St → Mid L Nat → Env → Prop := fun k s m E =>
  (E.sent = 1 ∧ hasTree E 0 vpS fun p =>
    toF (m.st.input.w₀.a p) + coinAt k 2 vaA 1 + coinAt k 2 vaB 1) ∧ s.total = vNum k m

/-- The word of "late", from a run's coins and the index. -/
def vWordF (k : Coins Bv) (m : Mid L Nat) : Cb.Gl.F :=
  toF (m.st.input.w₀.a 1) + coinAt k 2 vaL 0 + coinAt k 2 vaA 0

/-- The number that the verifier's state takes at "late". -/
def vWord (k : Coins Bv) (m : Mid L Nat) : Nat := (ofF (vWordF k m)).toNat

/-- After "late": the state's third number is the word of "late", from this run's coins, as a
number; and the last round that the prover's run has seen shows that word. -/
def vLate : Coins Bv → St → Mid L Nat → Env → Prop := fun k s m _ =>
  s.claimed = vWord k m ∧ m.seen.getLast?.map (·.vals) = some [.e (ofF (vWordF k m), 0, 0)]

/-! ## 2 What the book gives, and what is played -/

theorem vlend_A (k : Coins Bv) : ∃ c : Cs ⟨2, 0⟩,
    lendRow Bv (Bv.rowsOf 2) (k.look 2) vSideA.block.place vSideA.half.parts 0 =
      .ok ((c, (), ()), ()) ∧
    c.f ⟨0, by decide⟩ = coinAt k 2 vaA 0 ∧ c.f ⟨1, by decide⟩ = coinAt k 2 vaA 1 :=
  ⟨_, rfl, rfl, rfl⟩

theorem vlend_B (k : Coins Bv) : ∃ c : Cs ⟨2, 0⟩,
    lendRow Bv (Bv.rowsOf 2) (k.look 2) vSideB.block.place vSideB.half.parts 0 =
      .ok ((c, (), ()), ()) := ⟨_, rfl⟩

theorem vlend_S (k : Coins Bv) : ∃ (e : Cs ⟨0, 0⟩) (ca cb : Cs ⟨1, 0⟩),
    lendRow Bv (Bv.rowsOf 2) (k.look 2) vSideS.block.place vSideS.half.parts 0 =
      .ok ((e, (ca, cb, ()), ()), ()) ∧
    ca.f ⟨0, by decide⟩ = coinAt k 2 vaA 1 ∧ cb.f ⟨0, by decide⟩ = coinAt k 2 vaB 1 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

theorem vlend_D (k : Coins Bv) : ∃ e : Cs ⟨0, 0⟩,
    lendRow Bv (Bv.rowsOf 2) (k.look 2) vSideD.block.place vSideD.half.parts 0 =
      .ok ((e, (), ()), ()) := ⟨_, rfl⟩

theorem vlend_M (k : Coins Bv) : ∃ c : Cs ⟨1, 0⟩,
    lendRow Bv (Bv.rowsOf 2) (k.look 2) vSideM.block.place vSideM.half.parts 0 =
      .ok ((c, (), ()), ()) := ⟨_, rfl⟩

theorem vlend_W (k : Coins Bv) : ∃ c : Cs ⟨1, 0⟩,
    lendRow Bv (Bv.rowsOf 2) (k.look 2) vSideW.block.place vSideW.half.parts 0 =
      .ok ((c, (), ()), ()) := ⟨_, rfl⟩

theorem vlend_L (k : Coins Bv) : ∃ (c ct : Cs ⟨1, 0⟩),
    lendRow Bv (Bv.rowsOf 2) (k.look 2) vSideL.block.place vSideL.half.parts 0 =
      .ok ((c, (), (ct, ())), ()) ∧
    c.f ⟨0, by decide⟩ = coinAt k 2 vaL 0 ∧ ct.f ⟨0, by decide⟩ = coinAt k 2 vaA 0 :=
  ⟨_, _, rfl, rfl, rfl⟩

theorem vlend_E (k : Coins Bv) : ∃ (e : Cs ⟨0, 0⟩) (ct cr : Cs ⟨1, 0⟩),
    lendRow Bv (Bv.rowsOf 2) (k.look 2) vSideE.block.place vSideE.half.parts 0 =
      .ok ((e, (), (ct, cr, ())), ()) ∧
    ct.f ⟨0, by decide⟩ = coinAt k 2 vaA 0 ∧ cr.f ⟨0, by decide⟩ = coinAt k 2 vaL 0 :=
  ⟨_, _, _, rfl, rfl, rfl⟩

/-- A list of one part that says one element y and has no stop, played: the round as played, and the
input is as it was. -/
def saidOne (n : String) (a : Place) (y : Cb.Gl.F) (R : Fmt.Drawn) : List Played :=
  [⟨n, a, 0, true, [.e (ofF y, ofF (toF 0), ofF (toF 0))], [], R⟩]

theorem vplay_A (c : Cs ⟨2, 0⟩) (m : Mid L Nat) (R : Fmt.Drawn) : ∃ m' : Mid L Nat,
    play (vSideA.half.steps vSideA.block (Face.own.sees m.st.input) ((c, (), ()), ())) [R] [] m =
      .ok (saidOne "own a" vpA
        (toF m.st.input.w₀.ans + c.f ⟨0, by decide⟩ + c.f ⟨1, by decide⟩) R, m') ∧
    m'.st.input = m.st.input :=
  ⟨_, by with_unfolding_all rfl, by with_unfolding_all rfl⟩

theorem vplay_B (c : Cs ⟨2, 0⟩) (m : Mid L Nat) (R : Fmt.Drawn) : ∃ m' : Mid L Nat,
    play (vSideB.half.steps vSideB.block (Face.own.sees m.st.input) ((c, (), ()), ())) [R] [] m =
      .ok (saidOne "own b" vpB
        (toF (m.st.input.w₀.a 0) + c.f ⟨0, by decide⟩ + c.f ⟨1, by decide⟩) R, m') ∧
    m'.st.input = m.st.input :=
  ⟨_, by with_unfolding_all rfl, by with_unfolding_all rfl⟩

theorem vplay_D (e : Cs ⟨0, 0⟩) (m : Mid L Nat) (R : Fmt.Drawn) : ∃ m' : Mid L Nat,
    play (vSideD.half.steps vSideD.block (Face.own.sees m.st.input) ((e, (), ()), ())) [R] [] m =
      .ok ([⟨"draw", vpD, 0, true, [], [], R⟩], m') ∧ m'.st.input = m.st.input :=
  ⟨_, by with_unfolding_all rfl, by with_unfolding_all rfl⟩

theorem vplay_M (c : Cs ⟨1, 0⟩) (m : Mid L Nat) (R : Fmt.Drawn) : ∃ m' : Mid L Nat,
    play (vSideM.half.steps vSideM.block (Face.own.sees m.st.input) ((c, (), ()), ())) [R] [] m =
      .ok (saidOne "mid" vpM (toF m.st.input.w₀.ans + c.f ⟨0, by decide⟩) R, m') ∧
    m'.st.input = m.st.input :=
  ⟨_, by with_unfolding_all rfl, by with_unfolding_all rfl⟩

theorem vplay_W (c : Cs ⟨1, 0⟩) (m : Mid L Nat) (R : Fmt.Drawn) : ∃ m' : Mid L Nat,
    play (vSideW.half.steps vSideW.block (Face.own.sees m.st.input) ((c, (), ()), ())) [R] [] m =
      .ok (saidOne "weigh" vpW (toF (m.st.input.w₀.a 2) + c.f ⟨0, by decide⟩) R, m') ∧
    m'.st.input = m.st.input :=
  ⟨_, by with_unfolding_all rfl, by with_unfolding_all rfl⟩

theorem vplay_L (c ct : Cs ⟨1, 0⟩) (m : Mid L Nat) (R : Fmt.Drawn) : ∃ m' : Mid L Nat,
    play (vSideL.half.steps vSideL.block (Face.own.sees m.st.input) ((c, (), (ct, ())), ())) [R] []
        m =
      .ok (saidOne "late" vpL
        (toF (m.st.input.w₀.a 1) + c.f ⟨0, by decide⟩ + ct.f ⟨0, by decide⟩) R, m') ∧
    m'.st.input = m.st.input ∧
    m'.seen = m.seen ++ [⟨[.e (ofF (toF (m.st.input.w₀.a 1) + c.f ⟨0, by decide⟩ +
      ct.f ⟨0, by decide⟩), ofF (toF 0), ofF (toF 0))], R⟩] :=
  ⟨_, by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩

theorem vplay_E (e : Cs ⟨0, 0⟩) (ct cr : Cs ⟨1, 0⟩) (m : Mid L Nat) (R : Fmt.Drawn) :
    ∃ m' : Mid L Nat,
    play (vSideE.half.steps vSideE.block (Face.own.sees m.st.input) ((e, (), (ct, cr, ())), ()))
        [R] [] m =
      .ok (saidOne "echo" vpE
        (toF (m.st.input.w₀.a 1) + cr.f ⟨0, by decide⟩ + ct.f ⟨0, by decide⟩) R, m') :=
  ⟨_, by with_unfolding_all rfl⟩

/-- The spender's list, played, where its stop returns `none`. -/
theorem vplay_S (e : Cs ⟨0, 0⟩) (ca cb : Cs ⟨1, 0⟩) (m : Mid L Nat) {R : Fmt.Drawn}
    (hR : R ≠ dE 13) : ∃ m' : Mid L Nat,
    play (vSideS.half.steps vSideS.block (Face.own.sees m.st.input) ((e, (ca, cb, ()), ()), ()))
        [R] [] m =
      .ok ([⟨"spend", vpS, 0, true, [], [some ⟨2, 1, fun p _ => toF (m.st.input.w₀.a p) +
        ca.f ⟨0, by decide⟩ + cb.f ⟨0, by decide⟩⟩], R⟩], m') ∧ m'.st.input = m.st.input := by
  have h := play_one_go (s := sS m (ca.f ⟨0, by decide⟩) (cb.f ⟨0, by decide⟩)) (d := R) (m := m)
    (z := ⟨[], [⟨2, 1, fun p _ => toF (m.st.input.w₀.a p) + ca.f ⟨0, by decide⟩ +
      cb.f ⟨0, by decide⟩⟩]⟩)
    (stop_front m.loc (fun _ => rfl) (fun _ => rfl)) (stop_last_none (bad_else m.loc hR) rfl)
    rfl (by with_unfolding_all rfl) (by with_unfolding_all rfl)
  exact ⟨_, h, rfl⟩

/-! ## 3 A whole list's run in one condition, side by side -/

theorem vNum_on {k : Coins Bv} {m m' : Mid L Nat} (hm : m'.st.input = m.st.input) :
    vNum k m' = vNum k m := by
  unfold vNum
  rw [hm]

/-- `vSent` is carried over rounds that send no table, leave the state's total and the input. -/
theorem vSent_on {k : Coins Bv} {s s' : St} {m m' : Mid L Nat} {E : Env} {ps : List Played}
    (h : vSent k s m E) (ht : tablesOf ps = []) (hs : s'.total = s.total)
    (hm : m'.st.input = m.st.input) : vSent k s' m' (E.add ps) := by
  obtain ⟨⟨h1, T, hT, hw, hsym⟩, h2⟩ := h
  obtain ⟨st, tre, sent⟩ := E
  have h1' : sent = 1 := h1
  subst h1'
  unfold vSent hasTree
  refine ⟨⟨?_, T, hT, hw, fun p i => ?_⟩, ?_⟩
  · show 1 + (tablesOf ps).length = 1
    rw [ht]
    rfl
  · rw [hm]
    exact hsym p i
  · rw [hs, vNum_on hm]
    exact h2

theorem vA_whole : WholeAt .own vSideA Bv 2 Fv.lastChainFirstTreeNumber noTree vAt := by
  intro k s m E ds hA hd _
  have hd' : drawsFit [sayR] ds = true := hd
  obtain ⟨R, rfl, h₀⟩ := drawsFit_one hd'
  obtain ⟨c, hc, ht, ha⟩ := vlend_A k
  obtain ⟨m', hy, hm'⟩ := vplay_A c m R
  refine ⟨_, _, [], { s with total := (ofF (toF m.st.input.w₀.ans + c.f ⟨0, by decide⟩ +
    c.f ⟨1, by decide⟩)).toNat }, 0, hc, hy, by with_unfolding_all rfl, ?_, ?_⟩
  · exact VerifiableInference.Desc.Block.step_ok.2
      ⟨(roundsFit_cons (by with_unfolding_all rfl) h₀).trans (by with_unfolding_all rfl),
        by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩
  · unfold vAt
    refine ⟨hA, ?_⟩
    show (ofF (toF m.st.input.w₀.ans + c.f ⟨0, by decide⟩ + c.f ⟨1, by decide⟩)).toNat = vNum k m'
    rw [vNum_on hm', ht, ha]
    rfl

theorem vB_whole : WholeAt .own vSideB Bv 2 Fv.lastChainFirstTreeNumber vAt vAt := by
  intro k s m E ds hA hd _
  have hd' : drawsFit [sayR] ds = true := hd
  obtain ⟨R, rfl, h₀⟩ := drawsFit_one hd'
  obtain ⟨c, hc⟩ := vlend_B k
  obtain ⟨m', hy, hm'⟩ := vplay_B c m R
  refine ⟨_, _, [], s, 0, hc, hy, by with_unfolding_all rfl, ?_, ?_⟩
  · exact VerifiableInference.Desc.Block.step_ok.2
      ⟨(roundsFit_cons (by with_unfolding_all rfl) h₀).trans (by with_unfolding_all rfl),
        by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩
  · unfold vAt
    exact ⟨hA.1, hA.2.trans (vNum_on (m' := Mid.took m' []) hm').symm⟩

theorem stop_13 (w : L) (loc : List Fmt.Drawn) : vSideS.stopAt .own w loc [dE 13] = some .bad := rfl

theorem vS_whole : WholeAt .own vSideS Bv 2 Fv.lastChainFirstTreeNumber vAt vSent := by
  intro k s m E ds hA hd hs
  have hd' : drawsFit [{ entry := { name := "CS", msg := 32, roots := 1, drawE := 1 } }] ds =
    true := hd
  obtain ⟨R, rfl, h₀⟩ := drawsFit_one hd'
  have hR : R ≠ dE 13 := by
    intro h
    subst h
    rw [stop_13] at hs
    cases hs
  obtain ⟨st, tre, sent⟩ := E
  have h1 : sent = 0 := hA.1
  subst h1
  obtain ⟨e, ca, cb, hc, ha, hb⟩ := vlend_S k
  obtain ⟨m', hy, hm'⟩ := vplay_S e ca cb m hR
  refine ⟨_, _, [], s, 0, hc, hy, by with_unfolding_all rfl, ?_, ?_⟩
  · exact VerifiableInference.Desc.Block.step_ok.2
      ⟨(roundsFit_cons (by with_unfolding_all rfl) h₀).trans (by with_unfolding_all rfl),
        by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩
  · unfold vSent hasTree
    refine ⟨⟨rfl, _, rfl, rfl, fun p _ => ?_⟩, ?_⟩
    · show toF (m.st.input.w₀.a p) + ca.f ⟨0, by decide⟩ + cb.f ⟨0, by decide⟩ =
        toF (m'.st.input.w₀.a p) + coinAt k 2 vaA 1 + coinAt k 2 vaB 1
      rw [ha, hb, hm']
    · exact hA.2.trans (vNum_on (m' := Mid.took m' []) hm').symm

theorem vD_whole : WholeAt .own vSideD Bv 2 Fv.lastChainFirstTreeNumber vSent vSent := by
  intro k s m E ds hA hd _
  have hd' : drawsFit [{ entry := drawD }] ds = true := hd
  obtain ⟨R, rfl, h₀⟩ := drawsFit_one hd'
  obtain ⟨e, hc⟩ := vlend_D k
  obtain ⟨m', hy, hm'⟩ := vplay_D e m R
  refine ⟨_, _, [], { s with claimed := (VerifiableInference.Desc.BlockToy.drawn
    ((roundsOf [⟨"draw", vpD, 0, true, [], [], R⟩]).map
      VerifiableInference.Desc.noDigest)).headD 0 }, 0, hc, hy, by with_unfolding_all rfl, ?_,
    vSent_on hA rfl rfl hm'⟩
  exact VerifiableInference.Desc.Block.step_ok.2
    ⟨(roundsFit_cons (by with_unfolding_all rfl) h₀).trans (by with_unfolding_all rfl),
      by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩

/-- What the round of "mid" reads, where the chain has sent one tree before it. -/
theorem reads_M (st : Nat → Nat → Option (List UInt64))
    (tre : Fmt.TreeSource → Option (Place × Table)) (ps : List Played) (ft : Nat)
    (el : List Fmt.Ext) (x : Nat) (tr : List Int) (dg : Option ByteArray) :
    readsOf 2 ft (Env.add ⟨st, tre, 1⟩ ps).stored (Env.add ⟨st, tre, 1⟩ ps).tree vbM.rounds
        [⟨el, [x], tr, dg⟩] =
      [⟨tree₃.tree - ft, x % 2 ^ 2, none, some (2, 0), (tre (.own 0)).map (·.1),
        (tre (.own 0)).map (·.2.col (x % 2 ^ 2)), 1⟩] := rfl

theorem vM_whole : WholeAt .own vSideM Bv 2 Fv.lastChainFirstTreeNumber vSent vSent := by
  intro k s m E ds hA hd _
  have hd' : drawsFit [{ entry := { name := "CS", msg := 24, poss := 1, logN := 3 }
                         opens := [(tree₃, .own 0)] }] ds = true := hd
  obtain ⟨R, rfl, h₀⟩ := drawsFit_one hd'
  obtain ⟨x, hx⟩ := one_of_length (poss_of_drawFit h₀)
  obtain ⟨el, ps, tr, dg⟩ := R
  have hx' : ps = [x] := hx
  subst hx'
  obtain ⟨c, hc⟩ := vlend_M k
  obtain ⟨m', hy, hm'⟩ := vplay_M c m ⟨el, [x], tr, dg⟩
  have hB := vSent_on (s' := s) (ps := saidOne "mid" vpM
    (toF m.st.input.w₀.ans + c.f ⟨0, by decide⟩) ⟨el, [x], tr, dg⟩) hA rfl rfl hm'
  obtain ⟨⟨h1, T, hT, hw, -⟩, -⟩ := hA
  obtain ⟨st, tre, sent⟩ := E
  have h1' : sent = 1 := h1
  subst h1'
  obtain ⟨lg, w, sym⟩ := T
  have hw' : w = 1 := hw
  subst hw'
  have hT' : tre (.own 0) = some (vpS, ⟨lg, 1, sym⟩) := hT
  refine ⟨_, _, [(tree₃.tree - Fv.lastChainFirstTreeNumber, x % 2 ^ 2, [ofF (sym (x % 2 ^ 2) ⟨0, by decide⟩)])],
    s, 1, hc, hy, ?_, ?_, hB⟩
  · refine (congrArg (fun q => fillCols q [])
      (reads_M st tre _ Fv.lastChainFirstTreeNumber el x tr dg)).trans ?_
    show fillCols [⟨tree₃.tree - Fv.lastChainFirstTreeNumber, x % 2 ^ 2, none, some (2, 0),
      (tre (.own 0)).map (·.1), (tre (.own 0)).map (·.2.col (x % 2 ^ 2)), 1⟩] [] = _
    rw [hT']
    rfl
  · exact VerifiableInference.Desc.Block.step_ok.2
      ⟨(roundsFit_cons (by with_unfolding_all rfl) h₀).trans (by with_unfolding_all rfl),
        by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩

/-! ### The sub-protocol with a round that can reject -/

/-- Where "weigh" accepts it leaves the state as it was, and the weight is not 1. -/
theorem weigh_keeps {s s' : St} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : vbW.decide s rs gs = .ok s') : s' = s ∧ weighOk s = true := by
  have h' : ((need "weigh.one-element" (firstWord rs).isSome).bind fun _ =>
      (need "weigh.a-weight-is-1" (weighOk s)).map fun _ => s) = .ok s' := h
  cases h1 : (firstWord rs).isSome with
  | false =>
    rw [h1] at h'
    cases h'
  | true =>
    rw [h1] at h'
    cases h2 : weighOk s with
    | false =>
      rw [h2] at h'
      cases h'
    | true =>
      rw [h2] at h'
      exact ⟨(Except.ok.inj h').symm, rfl⟩

/-- **`plays` at the side of "weigh", at all coins, fall or not**: the list is played; and wherever
the sub-protocol's own step accepts, `vSent` holds after it, at `y.2.took cols`. The text of the
field `plays` of `Good`, at the side without its fall. -/
theorem vW_plays : ∀ k s m E ds, vSent k s m E → drawsFit vSideW.block.rounds ds = true →
    vSideW.stopAt .own m.st.input m.loc ds = none →
    ∃ (c : RowCoins vSideW.half.parts) (y : List Played × Mid L Nat) (cols : List OpenedColumn),
      lendRow Bv (Bv.rowsOf 2) (k.look 2) vSideW.block.place vSideW.half.parts 0 = .ok c ∧
      play (vSideW.half.steps vSideW.block (Face.own.sees m.st.input) c) ds [] m = .ok y ∧
      fillCols (readsOf 2 Fv.lastChainFirstTreeNumber (E.add y.1).stored (E.add y.1).tree vSideW.block.rounds
        ds) [] = .ok cols ∧
      ∀ s' n, vSideW.block.step Fv.lastChainFirstTreeNumber s (roundsOf y.1) cols = .ok (s', n) →
        vSent k s' (y.2.took cols) (E.add y.1) := by
  intro k s m E ds hA hd _
  have hd' : drawsFit [sayR] ds = true := hd
  obtain ⟨R, rfl, -⟩ := drawsFit_one hd'
  obtain ⟨c, hc⟩ := vlend_W k
  obtain ⟨m', hy, hm'⟩ := vplay_W c m R
  refine ⟨_, _, [], hc, hy, by with_unfolding_all rfl, fun s' n hst => ?_⟩
  obtain ⟨hs, -⟩ := weigh_keeps (VerifiableInference.Desc.Block.step_ok.1 hst).2.2.1
  exact vSent_on hA rfl (congrArg St.total hs) hm'

/-- **Where the weight is not 1 the own step of "weigh" accepts** whatever the list has played. -/
theorem vW_yes : ∀ (k : Coins Bv) (s : St) (m : Mid L Nat) (E : Env) (ds : List Fmt.Drawn),
    drawsFit vSideW.block.rounds ds = true → weighOk s = true →
    ∀ (c : RowCoins vSideW.half.parts) (y : List Played × Mid L Nat) (cols : List OpenedColumn),
      lendRow Bv (Bv.rowsOf 2) (k.look 2) vSideW.block.place vSideW.half.parts 0 = .ok c →
      play (vSideW.half.steps vSideW.block (Face.own.sees m.st.input) c) ds [] m = .ok y →
      fillCols (readsOf 2 Fv.lastChainFirstTreeNumber (E.add y.1).stored (E.add y.1).tree vSideW.block.rounds
        ds) [] = .ok cols →
      ∃ s' n, vSideW.block.step Fv.lastChainFirstTreeNumber s (roundsOf y.1) cols = .ok (s', n) := by
  intro k s m E ds hd hw c' y' cols' h1 h2 h3
  have hd' : drawsFit [sayR] ds = true := hd
  obtain ⟨R, rfl, h₀⟩ := drawsFit_one hd'
  obtain ⟨c, hc⟩ := vlend_W k
  have ec := Except.ok.inj (hc.symm.trans h1)
  subst ec
  obtain ⟨m', hy, -⟩ := vplay_W c m R
  have ey := Except.ok.inj (hy.symm.trans h2)
  subst ey
  have ek : ([] : List OpenedColumn) = cols' := Except.ok.inj h3
  subst ek
  refine ⟨s, 0, VerifiableInference.Desc.Block.step_ok.2
    ⟨(roundsFit_cons (by with_unfolding_all rfl) h₀).trans (by with_unfolding_all rfl),
      by with_unfolding_all rfl, ?_, by with_unfolding_all rfl⟩⟩
  show ((need "weigh.one-element" true).bind fun _ =>
    (need "weigh.a-weight-is-1" (weighOk s)).map fun _ => s) = .ok s
  rw [hw]
  rfl

/-- At a state whose weight is 1 the sub-protocol's own step rejects whatever is produced. (The
field `acc` of `Good` is false of the side without its fall: said here without a theorem.) -/
theorem weigh_refuses {s : St} (h : weighOk s = false) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    ¬ ∃ s' n, vbW.step Fv.lastChainFirstTreeNumber s rs cols = .ok (s', n) := by
  rintro ⟨s', n, hst⟩
  have h2 := (weigh_keeps (VerifiableInference.Desc.Block.step_ok.1 hst).2.2.1).2
  rw [h] at h2
  cases h2

theorem vWordF_on {k : Coins Bv} {m m' : Mid L Nat} (hm : m'.st.input = m.st.input) :
    vWordF k m' = vWordF k m := by
  unfold vWordF
  rw [hm]

theorem vL_whole : WholeAt .own vSideL Bv 2 Fv.lastChainFirstTreeNumber anyAt vLate := by
  intro k s m E ds _ hd _
  have hd' : drawsFit [sayR] ds = true := hd
  obtain ⟨R, rfl, h₀⟩ := drawsFit_one hd'
  obtain ⟨c, ct, hc, h1, h2⟩ := vlend_L k
  obtain ⟨m', hy, hm', hseen⟩ := vplay_L c ct m R
  have hW : toF (m.st.input.w₀.a 1) + c.f ⟨0, by decide⟩ + ct.f ⟨0, by decide⟩ = vWordF k m' := by
    rw [vWordF_on hm', h1, h2]
    rfl
  refine ⟨_, _, [], { s with claimed := (ofF (toF (m.st.input.w₀.a 1) + c.f ⟨0, by decide⟩ +
    ct.f ⟨0, by decide⟩)).toNat }, 0, hc, hy, by with_unfolding_all rfl, ?_, ?_⟩
  · exact VerifiableInference.Desc.Block.step_ok.2
      ⟨(roundsFit_cons (by with_unfolding_all rfl) h₀).trans (by with_unfolding_all rfl),
        by with_unfolding_all rfl, by with_unfolding_all rfl, by with_unfolding_all rfl⟩
  · unfold vLate
    refine ⟨?_, ?_⟩
    · show (ofF (toF (m.st.input.w₀.a 1) + c.f ⟨0, by decide⟩ + ct.f ⟨0, by decide⟩)).toNat =
        vWord k m'
      rw [hW]
      rfl
    · show m'.seen.getLast?.map (·.vals) = some [.e (ofF (vWordF k m'), 0, 0)]
      rw [hseen, List.getLast?_concat, hW, ofF_toF_zero]
      rfl

/-- The condition before is used: the test of "echo" on a value passes because the state's third
number is the word of "late" from this run's coins, and the echo says that word from the blocks that
it carries. -/
theorem vE_whole : WholeAt .own vSideE Bv 2 Fv.lastChainFirstTreeNumber vLate anyAt := by
  intro k s m E ds hA hd _
  have hd' : drawsFit [sayR] ds = true := hd
  obtain ⟨R, rfl, h₀⟩ := drawsFit_one hd'
  obtain ⟨e, ct, cr, hc, h1, h2⟩ := vlend_E k
  obtain ⟨m', hy⟩ := vplay_E e ct cr m R
  have hA' : s.claimed = vWord k m := hA.1
  have hw : ((ofF (toF (m.st.input.w₀.a 1) + cr.f ⟨0, by decide⟩ +
      ct.f ⟨0, by decide⟩)).toNat == s.claimed) = true := by
    rw [hA', h1, h2]
    exact beq_self_eq_true _
  refine ⟨_, _, [], s, 0, hc, hy, by with_unfolding_all rfl, ?_, trivial⟩
  refine VerifiableInference.Desc.Block.step_ok.2
    ⟨(roundsFit_cons (by with_unfolding_all rfl) h₀).trans (by with_unfolding_all rfl),
      by with_unfolding_all rfl, ?_, by with_unfolding_all rfl⟩
  show ((need "echo.the-word" ((ofF (toF (m.st.input.w₀.a 1) + cr.f ⟨0, by decide⟩ +
    ct.f ⟨0, by decide⟩)).toNat == s.claimed)).map fun _ => s) = .ok s
  rw [hw]
  rfl

end ProofFile.Honest.Toy

#print axioms ProofFile.Honest.Toy.vlend_A
#print axioms ProofFile.Honest.Toy.vlend_B
#print axioms ProofFile.Honest.Toy.vlend_S
#print axioms ProofFile.Honest.Toy.vlend_D
#print axioms ProofFile.Honest.Toy.vlend_M
#print axioms ProofFile.Honest.Toy.vlend_W
#print axioms ProofFile.Honest.Toy.vlend_L
#print axioms ProofFile.Honest.Toy.vlend_E
#print axioms ProofFile.Honest.Toy.vplay_A
#print axioms ProofFile.Honest.Toy.vplay_B
#print axioms ProofFile.Honest.Toy.vplay_D
#print axioms ProofFile.Honest.Toy.vplay_M
#print axioms ProofFile.Honest.Toy.vplay_W
#print axioms ProofFile.Honest.Toy.vplay_L
#print axioms ProofFile.Honest.Toy.vplay_E
#print axioms ProofFile.Honest.Toy.vplay_S
#print axioms ProofFile.Honest.Toy.vNum_on
#print axioms ProofFile.Honest.Toy.vSent_on
#print axioms ProofFile.Honest.Toy.vA_whole
#print axioms ProofFile.Honest.Toy.vB_whole
#print axioms ProofFile.Honest.Toy.stop_13
#print axioms ProofFile.Honest.Toy.vS_whole
#print axioms ProofFile.Honest.Toy.vD_whole
#print axioms ProofFile.Honest.Toy.reads_M
#print axioms ProofFile.Honest.Toy.vM_whole
#print axioms ProofFile.Honest.Toy.weigh_keeps
#print axioms ProofFile.Honest.Toy.vW_plays
#print axioms ProofFile.Honest.Toy.vW_yes
#print axioms ProofFile.Honest.Toy.weigh_refuses
#print axioms ProofFile.Honest.Toy.vWordF_on
#print axioms ProofFile.Honest.Toy.vL_whole
#print axioms ProofFile.Honest.Toy.vE_whole
#print axioms ProofFile.Honest.Toy.vNum
#print axioms ProofFile.Honest.Toy.vAt
#print axioms ProofFile.Honest.Toy.vSent
#print axioms ProofFile.Honest.Toy.vWordF
#print axioms ProofFile.Honest.Toy.vWord
#print axioms ProofFile.Honest.Toy.vLate
#print axioms ProofFile.Honest.Toy.saidOne
