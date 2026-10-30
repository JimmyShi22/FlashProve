-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/FoldSide.lean (over two
  files, BothInScope.lean and Johnson/P1HeadR/FrontInScope.lean, and the law files
  K2Hands/FrontsFullTied.lean, Johnson/Top/H0/K2Caller/FrontSide.lean, KeptTypedFull.lean and
  Johnson/G/SwitchFrontTests.lean): THE FOLD's SIDE OF THE CODE SWITCH's FIRST AND FOURTH TIE, IN
  SCOPE, AT ALL 25 SWITCHES: what the ties' premise hT1 (Johnson/Top/H0/K2Caller/TieOneR.lean,
  TieFourR.lean) asks at a state that is reached in front of the switch.

Main names (namespace `P1K2`).
  `foldSide_one` (group 1) · `foldSide_link` (groups 2 to 23) · `foldSide_head` (24) ·
    `foldSide_fin` (25): at a state s that `Reach` has at the switch's own number over the chain's
    sub-protocols (each beneath `below`), at the front fx that the text makes of what the way in
    lets in of s, at the written entry r of the place: there is the written front's frame W₀, and:
    the test `frontB2` accepts at the place's closed numbers · the typed list of new members is
    tied to the notices · the invariant on stored sample rows holds at the front's statement · the
    test `storedB` accepts · the state's and the front's statements hold the same oracle messages.
  `both_at_open`: both invariants on the stored sample rows at the opening's own chain.
    `chain_of_desc`: the IOP as written in Lean for the proof file has one first chain.
    `closed_at`: the closed side at a written entry.
THE PREMISES THAT STAY, BY NAME: in scope, the files read, the opening O, `ProofFile.onlineDescription` returns
  F, F.planOk · hcs, hsh: the public part's codes and shape are the written ones · Hn, Hn2: the
  count of oracle messages at a written cut is the closed number (in `foldSide_link` asked at the
  23 links' cuts, of which it spends two; in the other three at the cuts that are spent) · He: at
  the switch's cut each message has the listed shape · He0: the like in front of the last closing,
  at the kept old numbers (not at the finish) · at the finish: the quiet step in front of the
  switch accepts.
Limits. A join; no premise is shown met here; who pays which stands in a text
  of this project that is not in this repository. Nothing on soundness or on hiding.

-/
import Johnson.P1HeadR.FrontInScope
import Johnson.P1K2R.BothInScope
import Johnson.Top.H0.K2Caller.FrontSide
import Johnson.Top.H0.K2Caller.KeptTypedFull
import Johnson.Top.H0.K2Hands.FrontsFullTied
import Johnson.G.SwitchFrontTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes OnBytes.Model OnBytes.Slice Johnson.Pack Johnson.Top.H
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.Desc.First.K2Hands (frontB2 placeFrame Tied csW MW tied_at)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit frontSide_of keptTyped_at)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Johnson.G (fxAt storedB keptShapeB keptShape_full kept_len front_tests_full)
open Meaning.K2
open _root_.Tw.K2 (switchNotices)
open ProofFile (Cl)

/-- The IOP as written in Lean for the proof file has one first chain. -/
theorem chain_of_desc {o : ProofFile.SecondHashFunctionArgument} {links : ProofFile.LinksBy} {Z : ProofFile.Pub}
    {A A' : ProofFile.SharedSeat} {B B' : ProofFile.SecondSeat} {c c' : Chain S Cl}
    (e : ProofFile.fileDescBy o links Z A B (fun s => s) (ProofFile.startS Z) c =
      ProofFile.fileDescBy o links Z A' B' (fun s => s) (ProofFile.startS Z) c') : c = c' := by
  have h : HEq (ProofFile.fileDescBy o links Z A B (fun s => s) (ProofFile.startS Z) c).first
      (ProofFile.fileDescBy o links Z A' B' (fun s => s) (ProofFile.startS Z) c').first := by rw [e]
  exact eq_of_heq h

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Both invariants on the stored sample rows, at the opening's own chain.** -/
theorem both_at_open (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true) {k : ℕ}
    (hk : k ≤ (frontOf c).length) {z : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) k (z, s)) :
    K2.SampleGoodS s.st ∧ K2.AnsweredStored s.st := by
  obtain ⟨Z', c', A', B', hZ, hE, -, hall⟩ := both_in_scope hF hpl
  obtain rfl : Z = Z' := Except.ok.inj (O.pub.symm.trans hZ)
  obtain rfl : c = c' := chain_of_desc (O.desc.symm.trans hE)
  exact hall k hk z s hr

/-- The closed side at a written entry, for `frontSide_of`. -/
theorem closed_at {i : ℕ} {r : SwRow} {W₀ : SwitchFrame} (h : tableFullLit[i]? = some r)
    (hW : K2.frameAt (fxAt r) = some W₀) :
    W₀.kept.length = r.kept.length ∧ keptShapeB r = true := by
  obtain ⟨W, hW', -, -, -, hk, -, -⟩ := front_tests_full (List.mem_of_getElem? h)
  obtain rfl : W = W₀ := Option.some.inj (hW'.symm.trans hW)
  exact ⟨kept_len hk, List.all_eq_true.1 keptShape_full r (List.mem_of_getElem? h)⟩

/-- **THE FOLD's SIDE OF THE FIRST AND THE FOURTH TIE, IN SCOPE, AT THE SWITCH INTO GROUP l + 1,
1 ≤ l < 23.** -/
theorem foldSide_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true) {l : ℕ}
    (h1 : 1 ≤ l) (h23 : l < 23) (hcs : Z.first.codes = csW) (hsh : Z.first.shape = K2Hands.shW)
    {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (l + 1) + 2) (p, s))
    (Hn : ∀ g, 1 ≤ g → g ≤ 23 → ∀ (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (t : S)
        (R' : List
        Fmt.RoundView)
      (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (14 * g + 2)) (ProofFile.startS Z p) R C = .ok (t, R', C') →
          t.st.oracles.size = K2.n0At g)
    (He : ∀ (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (t : S) (R' : List Fmt.RoundView)
      (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t, R', C') →
      ∀ o, o < t.st.oracles.size → (t.st.oracles[o]?).map (·.shape) = MW[o]?)
    (He0 : ∀ (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (t : S) (R' : List Fmt.RoundView)
      (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 12)) (ProofFile.startS Z p) R C = .ok (t, R', C') →
      ∀ o ∈ K2.oldsAt (l + 1), (t.st.oracles[o]?).map (·.shape) = MW[o]?)
    {q : K2.P2} (hq : q.stands = .link) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q s = some fx) {r : SwRow} (hrw : tableFullLit[l]? = some r) :
    ∃ W₀, K2.frameAt (fxAt r) = some W₀ ∧
      (frontB2 (fxAt r) W₀ (l + 1) 0 (K2.n0At (l + 1)) (K2.oldsAt (l + 1)) fx = true ∧
        Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
        storedB r (placeFrame W₀ (K2.n0At (l + 1)) (K2.oldsAt (l + 1))) fx = true ∧
        s.st.oracles = fx.st.oracles) := by
  obtain ⟨-, R, C, f₂⟩ := (reach_raw hr).fold
  have f₂' : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (s, [], []) :=
    f₂
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_cut (k := 14 * l + 2) 14
    (show foldBlocks 0 (c.blocksInOrder.take (14 * l + 2 + 14)) (ProofFile.startS Z p) R C = .ok (s, [], []) from
      (by rw [show 14 * l + 2 + 14 = 14 * (l + 1) + 2 by ring]; exact f₂'))
  obtain ⟨s₃, R₃, C₃, g3⟩ := fold_cut (k := 14 * l + 12) 4
    (show foldBlocks 0 (c.blocksInOrder.take (14 * l + 12 + 4)) (ProofFile.startS Z p) R C = .ok (s, [], []) from
      (by rw [show 14 * l + 12 + 4 = 14 * (l + 1) + 2 by ring]; exact f₂'))
  obtain ⟨W₀, hW, hB⟩ := front_link_in_scope hS hR O h1 h23 hcs hsh f₀ (Hn l h1 (by omega) _ _ _ _ _
      f₀) g3 f₂'
    (Hn (l + 1) (by omega) (by omega) _ _ _ _ _ f₂') (He _ _ _ _ _ f₂') (He0 _ _ _ _ _ g3) hq h hrw
  obtain ⟨-, -, a3, a4, -⟩ := front_pin_link hS hR O (l := l + 1) (by omega) (by omega) f₂' hq h
  obtain ⟨hG, hA⟩ := both_at_open O hF hpl (by rw [front_len hS hR O]; omega) hr
  obtain ⟨k1, k2⟩ := closed_at hrw hW
  refine ⟨W₀, hW, frontSide_of h hB hG hA (Or.inl ⟨(by rw [hq]; exact fun e => (by cases e)), rfl⟩)
      k1
      k2
    (keptTyped_at hrw) (K2Hands.sentW (l + 1)) ?_ (tied_at (by omega) hrw)⟩
  rw [a3, a4, hsh]
  unfold K2Hands.sentW
  rw [if_neg (by omega)]

/-- **THE SAME AT THE SWITCH INTO GROUP 1.** -/
theorem foldSide_one (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW) (hsh : Z.first.shape = K2Hands.shW) {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 16 (p, s))
    (Hn : ∀ (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (t : S) (R' : List Fmt.RoundView)
      (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take 16) (ProofFile.startS Z p) R C = .ok (t, R', C') → t.st.oracles.size =
          K2.n0At 1)
    (He : ∀ (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (t : S) (R' : List Fmt.RoundView)
      (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take 16) (ProofFile.startS Z p) R C = .ok (t, R', C') → ∀ o, o <
          t.st.oracles.size → (t.st.oracles[o]?).map (·.shape) = MW[o]?)
    (He0 : ∀ (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (t : S) (R' : List Fmt.RoundView)
      (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take 12) (ProofFile.startS Z p) R C = .ok (t, R', C') →
      ∀ o ∈ K2.oldsAt 1, (t.st.oracles[o]?).map (·.shape) = MW[o]?)
    {q : K2.P2} (hq : q.stands = .link) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q s = some fx) {r : SwRow} (hrw : tableFullLit[0]? = some r) :
    ∃ W₀, K2.frameAt (fxAt r) = some W₀ ∧
      (frontB2 (fxAt r) W₀ 1 0 (K2.n0At 1) (K2.oldsAt 1) fx = true ∧
        Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
        storedB r (placeFrame W₀ (K2.n0At 1) (K2.oldsAt 1)) fx = true ∧
        s.st.oracles = fx.st.oracles) := by
  obtain ⟨-, R, C, f₂⟩ := (reach_raw hr).fold
  have f₂' : foldBlocks 0 (c.blocksInOrder.take 16) (ProofFile.startS Z p) R C = .ok (s, [], []) := f₂
  obtain ⟨s₃, R₃, C₃, g3⟩ := fold_cut (k := 12) 4 f₂'
  obtain ⟨W₀, hW, hB⟩ := front_one_in_scope hS hR O hcs hsh g3 f₂' (Hn _ _ _ _ _ f₂')
    (He _ _ _ _ _ f₂') (He0 _ _ _ _ _ g3) hq h hrw
  obtain ⟨-, -, a3, a4, -⟩ := front_pin_link hS hR O (l := 1) (by omega) (by omega) f₂' hq h
  obtain ⟨hG, hA⟩ := both_at_open O hF hpl (by rw [front_len hS hR O]; omega) hr
  obtain ⟨k1, k2⟩ := closed_at hrw hW
  refine ⟨W₀, hW, frontSide_of h hB hG hA (Or.inl ⟨(by rw [hq]; exact fun e => (by cases e)), rfl⟩)
    k1 k2 (keptTyped_at hrw) (K2Hands.sentW 1) ?_ (tied_at (by omega) hrw)⟩
  rw [a3, a4, hsh]
  unfold K2Hands.sentW
  rw [if_neg (by omega)]

/-- **THE SAME AT THE OUTPUT HEAD's SWITCH, INTO GROUP 24.** -/
theorem foldSide_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW) (hsh : Z.first.shape = K2Hands.shW) {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 339 (p, s))
    (Hn : ∀ (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (t : S) (R' : List Fmt.RoundView)
      (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take 324) (ProofFile.startS Z p) R C = .ok (t, R', C') → t.st.oracles.size =
          K2.n0At 23)
    (Hn2 : ∀ (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (t : S) (R' : List Fmt.RoundView)
      (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t, R', C') → t.st.oracles.size =
          K2.n0At 24)
    (He : ∀ (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (t : S) (R' : List Fmt.RoundView)
      (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t, R', C') → ∀ o, o <
          t.st.oracles.size → (t.st.oracles[o]?).map (·.shape) = MW[o]?)
    (He0 : ∀ (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (t : S) (R' : List Fmt.RoundView)
      (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take 334) (ProofFile.startS Z p) R C = .ok (t, R', C') →
      ∀ o ∈ K2.oldsAt 24, (t.st.oracles[o]?).map (·.shape) = MW[o]?)
    {q : K2.P2} (hq : q.stands = .head) {fx : _root_.Tw.K2.Front}
    (h : K2.frontAt q s = some fx) {r : SwRow} (hrw : tableFullLit[23]? = some r) :
    ∃ W₀, K2.frameAt (fxAt r) = some W₀ ∧
      (frontB2 (fxAt r) W₀ 24 0 (K2.n0At 24) (K2.oldsAt 24) fx = true ∧
        Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
        storedB r (placeFrame W₀ (K2.n0At 24) (K2.oldsAt 24)) fx = true ∧
        s.st.oracles = fx.st.oracles) := by
  obtain ⟨-, R, C, f₂⟩ := (reach_raw hr).fold
  have f₀ : foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (s, [], []) := f₂
  obtain ⟨t₃, R₃, C₃, f₃⟩ := fold_cut (k := 324) 15 f₀
  obtain ⟨s₃, R₄, C₄, g3⟩ := fold_cut (k := 334) 5 f₀
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_cut (k := 338) 1 f₀
  obtain ⟨W₀, hW, hB⟩ := front_head_in_scope hS hR O hcs hsh f₃ (Hn _ _ _ _ _ f₃) g3 fm f₀
    (Hn2 _ _ _ _ _ f₀) (He _ _ _ _ _ f₀) (He0 _ _ _ _ _ g3) hq h hrw
  obtain ⟨-, -, a3, a4, -⟩ := front_pin_head hS hR O f₀ hq h
  obtain ⟨hG, hA⟩ := both_at_open O hF hpl (by rw [front_len hS hR O]; omega) hr
  obtain ⟨k1, k2⟩ := closed_at hrw hW
  refine ⟨W₀, hW, frontSide_of h hB hG hA (Or.inl ⟨(by rw [hq]; exact fun e => (by cases e)), rfl⟩)
    k1 k2 (keptTyped_at hrw) (K2Hands.sentW 24) ?_ (tied_at (by omega) hrw)⟩
  rw [a3, a4, hsh]
  unfold K2Hands.sentW
  rw [if_neg (by omega)]

/-- **THE SAME AT THE FINISH, INTO GROUP 25.** t: the state behind the quiet step in front of the
switch, whose acceptance is a premise. -/
theorem foldSide_fin (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol lay P.KL = .ok F) (hpl : F.planOk = true)
    (hcs : Z.first.codes = csW) (hsh : Z.first.shape = K2Hands.shW) {p : ProofFile.InstPub} {s t : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) 353 (p, s))
    (Hn2 : ∀ (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (u : S) (R' : List Fmt.RoundView)
      (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (u, R', C') → u.st.oracles.size =
          K2.n0At 25)
    (He : ∀ (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (u : S) (R' : List Fmt.RoundView)
      (C' : List VerifiableInference.Desc.OpenedColumn),
      foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (u, R', C') →
      ∀ o, o < u.st.oracles.size → (u.st.oracles[o]?).map (·.shape) = MW[o]?)
    (hQ : K2.finishFrontQ s = .ok t) {q : K2.P2} (hq : q.stands = .finish)
    {fx : _root_.Tw.K2.Front} (h : K2.frontAt q t = some fx) {r : SwRow}
    (hrw : tableFullLit[24]? = some r) :
    ∃ W₀, K2.frameAt (fxAt r) = some W₀ ∧
      (frontB2 (fxAt r) W₀ 25 0 (K2.n0At 25) (K2.oldsAt 25) fx = true ∧
        Tied r.l (switchNotices fx.T fx.others) ∧ K2.SampleGoodS fx.st ∧
        storedB r (placeFrame W₀ (K2.n0At 25) (K2.oldsAt 25)) fx = true ∧
        s.st.oracles = fx.st.oracles) := by
  obtain ⟨-, R, C, f⟩ := (reach_raw hr).fold
  have f₂ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (s, [], []) := f
  obtain ⟨s₃, R₃, C₃, g3⟩ := fold_cut (k := 350) 3 f₂
  obtain ⟨W₀, hW, hB⟩ := front_fin_in_scope hS hR O hcs hsh g3 f₂ (Hn2 _ _ _ _ _ f₂)
    (He _ _ _ _ _ f₂) hQ hq h hrw
  obtain ⟨-, -, a3, a4, -⟩ := front_pin_fin hS hR O f₂ hQ hq h
  obtain ⟨hG, hA⟩ := both_at_open O hF hpl (by rw [front_len hS hR O]) hr
  obtain ⟨k1, k2⟩ := closed_at hrw hW
  refine ⟨W₀, hW, frontSide_of h hB hG hA (Or.inr ⟨hq, hQ⟩) k1 k2 (keptTyped_at hrw)
    (K2Hands.sentW 25) ?_ (tied_at (by omega) hrw)⟩
  rw [a3, a4, hsh]
  unfold K2Hands.sentW
  rw [if_pos rfl]

end

#print axioms chain_of_desc
#print axioms both_at_open
#print axioms closed_at
#print axioms foldSide_link
#print axioms foldSide_one
#print axioms foldSide_head
#print axioms foldSide_fin

end P1K2
