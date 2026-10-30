-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/RunIsAtBorder.lean: `RunIs` (Johnson/Desc/Kinds/Law/TwelveOurs.lean), the premise
by which the law on the output head's twelve reads is carried to the kind's own letters, at the
state right behind the output head's own sub-protocol, with the reads' tables laid silently.

Why. The spender of the row claim_read_same_index reads the output head's runs of claims at the
state s behind the fourth place of the head's segment, through `withTables P s`
(Johnson/Desc/Kinds/Law/K6SilentCode.lean): s with the tables laid that the next place's quiet step
would make. Between s and that state stands no commitment, no later decision and no earlier run.

What is stated and shown.
  `hc6_of_size`, `hlsJ_of_floor`: two public premises of `runIs_at_twelve` (Reads/RunIsLean.lean)
    follow: a segment's call is below 6 where the layout has at most six calls; ls is at most the
    layout's number of column coordinates where that number is the kind's (hJ) and ls + lt is at
    most the floor.
  `Nums W`: three closed facts on the public values: at most six calls; ls + lt is at most the
    floor; ls is at most lNI + lPd.
  `runIs_at_border`: **where the output head's own decision accepts from s0 to s, the ledger at s0
    is well laid, `withTables` answers e at s, and all the kind's letters are there at e: `RunIs R`
    holds at these letters**, R being the run of the public shape, layout and list of rounds'
    numbers, with the covered positions, what was heard and the tables of e itself. `RunIs` reads of
    R the shape, the layout, what was heard and the covered positions alone: so the border b is free
    here, and nothing is said by it of R's other three fields.
  `ReachGives`: what a state behind the fourth place must bring: a member of the table's list for
    the output head's own rounds, dressed as the chain dresses it (Reads/RowAtLot.lean), accepts
    from some s0 to it, and the ledger at s0 is well laid.
  `runIs_at_reach`: **the same in the spender's shape**: for every state with `ReachGives`, every e
    that `withTables` answers and every answer of `lettersAt` at e.

Premises. On a state: `ReachGives`, of which "well laid" is the one clause that no accept brings.
Public: hJ, for which a law in the goals' scope is stated as `cols_in_scope` in
Johnson/Goal/Meaning/HeadColsScope.lean, which this file does not import; and `Nums W`.

Limits. That a state reached by the chain's fold behind the fourth place has `ReachGives` is not
shown.
(Where this and lean/THEOREM.md differ, the page holds.)
No states are shown at which the premises hold together. Nothing on soundness.


-/
import Johnson.Desc.Reads.RowAtLot
import Johnson.Desc.Kinds.Law.K6Silent
import Johnson.Desc.Kinds.Law.RowRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtSeat

open OnBytes.Model.Head (HL callNo)
open VerifiableInference.Desc (Block Claim Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law

/-- A segment's call is below 6 where the layout has at most six calls. -/
theorem hc6_of_size {L : HL} (h : L.calls.size ≤ 6) :
    ∀ seg q, callNo L seg = some q → q < 6 := by
  intro seg q hq
  unfold OnBytes.Model.Head.callNo at hq
  obtain ⟨hlt, -⟩ := Array.findIdx?_eq_some_iff_getElem.1 hq
  omega

/-- ls is at most the layout's number of column coordinates. -/
theorem hlsJ_of_floor {h : OnBytes.Model.Head.Shape} {L : HL}
    (hJ : ∀ q, q < 6 → (L.calls.getD q default).lJ =
      (letI := sizesOf h; lJ (OnBytes.Model.Head.keyFloor h) (callKeys q)))
    (hf : h.ls + h.lt ≤ OnBytes.Model.Head.keyFloor h) :
    ∀ q, q < 6 → h.ls ≤ (L.calls.getD q default).lJ := by
  intro q hq
  rw [hJ q hq]
  have h1 : h.ls ≤ OnBytes.Model.Head.keyFloor h - h.lt := by omega
  exact Nat.le_trans h1 (Nat.le_max_right _ _)

/-- Three closed facts on the public values. -/
structure Nums (W : OnBytes.Model.Verify.Public) : Prop where
  six : W.HLy.calls.size ≤ 6
  floor : W.hS.ls + W.hS.lt ≤ OnBytes.Model.Head.keyFloor W.hS
  hls : W.hS.ls ≤ (letI := sizesOf W.hS; Norm.lNI + Norm.lPd)

/-- **RunIs at the state behind the output head's own sub-protocol, with the tables laid silently.**
RunIs reads of the run its shape, layout, heard values and covered positions alone: b is free. -/
theorem runIs_at_border (W : OnBytes.Model.Verify.Public) (place : Place)
    (b : OnBytes.Model.Head.Border) {rounds : Given → List Round}
    {weights : Given → Behind → SumOnMatrix} {s0 s e : S} {rs4 : List Fmt.RoundView}
    (h4 : decideBy rounds (fun _ => Head.hear) weights (parOf W.hS (Law.workOf W))
      (seatAt W.hS (Law.readsOf W)) s0 rs4 = .ok s)
    (hWL : WellLaid ((seatAt W.hS (Law.readsOf W)).ledger s0))
    (hJ : ∀ q, q < 6 → (W.HLy.calls.getD q default).lJ =
      (letI := sizesOf W.hS; lJ (OnBytes.Model.Head.keyFloor W.hS) (callKeys q)))
    (N : Nums W) (hw : withTables ⟨place, W.hS, W.HLy, W.H⟩ s = some e)
    [g : Given] [bh : Behind] {pl : Places}
    (hl : lettersAt (parOf W.hS (Law.workOf W)) (seatAt W.hS (Law.readsOf W)) e =
      .ok (g, bh, pl)) :
    ∃ a cov x t, e.here = .head a ∧ e.covered W.hS.T W.hS.V = .ok cov ∧ a.x = some x ∧
      a.t = some t ∧ ReadsQuiet.tables W.hS W.HLy W.H cov x = .ok t ∧
      RunIs ⟨W.hS, W.HLy, b, W.H, cov, x, t, Law.readsOf W⟩ := by
  obtain ⟨a, cov, x, t, ha, hop, hcov, hx, ht, rfl⟩ := (withTables_iff _ s e).1 hw
  have hlsJ := hlsJ_of_floor hJ N.floor
  obtain ⟨g0, H, F, left, s1, s2', hg, hh, -, e2, hs2⟩ := decideBy_more h4
  have hs2' : s = s2' := hs2
  subst hs2'
  obtain ⟨z, y, -, -, hP, hgE⟩ := Came.given_ok _ _ _ _ hg
  subst hgE
  have hz : W.hS.ls + W.hS.lt ≤ z.1.size := by
    obtain ⟨p1, p2⟩ := hP 0 _ (Came.call_get (by decide))
    exact size_of_tail (z.2 0) z.1 (J := (W.HLy.calls.getD 0 default).lJ)
      (by rw [hJ 0 (by decide)]; exact p1) p2 (hlsJ 0 (by decide))
  have hzt : (@fromLookup (sizesOf W.hS) (OnBytes.Model.Head.keyFloor W.hS) z.1 z.2).norm.zt.size =
      W.hS.lt := last_size z.1 (n := W.hS.lt) (Nat.le_trans (Nat.le_add_left _ _) hz)
  obtain ⟨a1, a2, a3, a4⟩ := @heard_sizes (sizesOf W.hS) (parOf W.hS (Law.workOf W)).policy
    (requestOf s0) ⟨y⟩
    (@fromLookup (sizesOf W.hS) (OnBytes.Model.Head.keyFloor W.hS) z.1 z.2).norm _ _ _ _ _ hWL hh
    hzt
  obtain ⟨o2, x2, q2, hx2, hG2, hZl, hqH, hqN, p1, p2, p3, p4⟩ :=
    laid_by_hearing W.hS (Law.readsOf W) e2
  have eo : a = o2 := by
    rw [q2] at ha
    exact (VerifiableInference.Desc.First.Here.head.inj ha).symm
  subst eo
  have ex : x = x2 := by
    rw [hx2] at hx
    exact (Option.some.inj hx).symm
  subst ex
  refine ⟨{ a with t := some t }, cov, x, t, rfl, hcov, hx, rfl, ht, ?_⟩
  exact runIs_at_twelve W.hS W.HLy b W.H (Law.readsOf W) (Law.workOf W)
    { s with here := .head { a with t := some t } } { a with t := some t }
    cov x t rfl hop hcov hx ht hG2 hZl hl hJ hlsJ (hc6_of_size N.six) (by rw [hqH]; decide)
    (by rw [hqN]; decide) (by rw [p1]; exact a1) (by rw [p2]; exact a2) (by rw [p3]; exact a3)
    (by rw [p4]; exact a4) N.hls

/-- What a state behind the fourth place must bring. -/
def ReachGives (Z : ProofFile.Pub) (G : ProofFile.Ground) (same : S → S → Bool) (but : Place → Bool)
    (a4 : Place) (n4 : String) (s : S) : Prop :=
  ∃ (B4 : Block S Claim) (s0 : S) (rs4 : List Fmt.RoundView) (gs4 : List (List (ℕ × List UInt64))),
    B4 ∈ P4.k6Hear Z G ∧ (dressed same but a4 n4 B4).decide s0 rs4 gs4 = .ok s ∧
    WellLaid ((seatAt G.W.hS (Law.readsOf G.W)).ledger s0)

/-- **The same in the spender's shape.** -/
theorem runIs_at_reach (Z : ProofFile.Pub) (G : ProofFile.Ground) (same : S → S → Bool)
    (but : Place → Bool) (a4 : Place) (n4 : String) (place : Place)
    (b : OnBytes.Model.Head.Border)
    (hJ : ∀ q, q < 6 → (G.W.HLy.calls.getD q default).lJ =
      (letI := sizesOf G.W.hS; lJ (OnBytes.Model.Head.keyFloor G.W.hS) (callKeys q)))
    (N : Nums G.W) :
    ∀ s, ReachGives Z G same but a4 n4 s → ∀ (e : S) (v : Given × Behind × Places),
      withTables ⟨place, G.W.hS, G.W.HLy, G.W.H⟩ s = some e →
      lettersAt (parOf G.W.hS (Law.workOf G.W)) (seatAt G.W.hS (Law.readsOf G.W)) e = .ok v →
      ∃ a cov x t, e.here = .head a ∧ e.covered G.W.hS.T G.W.hS.V = .ok cov ∧ a.x = some x ∧
        a.t = some t ∧ ReadsQuiet.tables G.W.hS G.W.HLy G.W.H cov x = .ok t ∧
        (letI := v.1; letI := v.2.1
         RunIs ⟨G.W.hS, G.W.HLy, b, G.W.H, cov, x, t, Law.readsOf G.W⟩) := by
  rintro s ⟨B4, s0, rs4, gs4, hB4, h4, hWL⟩ e ⟨g, bh, pl⟩ hw hl
  obtain ⟨ms, hs⟩ := k6_is hB4
  obtain ⟨iU3, hi, h4k⟩ := seated_yes hs (dressed_yes h4)
  have er : Law.readsOf G.W = iU3 := by
    unfold VerifiableInference.Desc.Kinds.Head.Law.readsOf
    rw [hi]
    rfl
  rw [← er] at h4k
  have h4' : decideBy (fun _ => rounds) (fun _ => Head.hear) (fun _ _ => forTheMerge)
      (parOf G.W.hS (Law.workOf G.W)) (seatAt G.W.hS (Law.readsOf G.W)) s0 rs4 = .ok s := h4k
  exact runIs_at_border (g := g) (bh := bh) G.W place b h4' hWL hJ N hw hl

end VerifiableInference.Reads.AtSeat

#print axioms VerifiableInference.Reads.AtSeat.hc6_of_size
#print axioms VerifiableInference.Reads.AtSeat.hlsJ_of_floor
#print axioms VerifiableInference.Reads.AtSeat.runIs_at_border
#print axioms VerifiableInference.Reads.AtSeat.runIs_at_reach
