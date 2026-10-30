-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/RowAtLot.lean: the row claim_read_same_index at the output head, for the four
forms of the policy, at the sub-protocols as the tables of the proof file's IOP hand them to the
first chain and as the chain dresses them.

Why. `row_at_seat` (Reads/RowAtSeat.lean) speaks of two terms. The IOP as written in Lean does not
hold these terms bare. A table (`ProofFile.Lot`, Johnson/Desc/ProofFile/LotCore.lean) hands a sub-protocol
in; the maker lays a test on a mark of failure over its decision and gives it the place's name
(Johnson/Desc/ProofFile/OnlineDescriptionFromBlockTables.lean, `partsAt`); the driver writes the place into it
(Johnson/Desc/First/Driver/Chain.lean, `blockAt`); and the chain lays a guard over its decision and
over each of its runs of claims (Johnson/Desc/SeatGuard.lean, `Block.guarded`). A sub-protocol
without claims is first carried to the type of claims (`Block.retype`, Johnson/Desc/Block.lean).

What is stated and shown.
  `placed a n b`, `dressed same but a n b`: b under the first three of these; b under all four.
  `dressed_yes`: where the dressed sub-protocol accepts, b accepts, with the same state behind.
  `dressed_claims`: each run of claims of the dressed one is a run of b under the same name; where
    the first accepts, so does the second, with the same answer.
  `k6_is`: a member of the table's list for the output head's own rounds (`P4.k6Hear`,
    Johnson/Desc/ProofFile/Lot/K6K7.lean) is `Head.seatedClaims` at the ground's public values and
    at the number of the last segment.
  `quiet_is`: at a segment of the head's kind, what the table of the commitments lays behind the
    reads' commitment (`ProofFile.orLoud` of `ProofFile.readsQuietAt`, Johnson/Desc/ProofFile/Lots/Makers.lean;
    laid by `ProofFile.k1Pure`, Lots/PureLots.lean) is `K8.ReadsQuiet.head` at the ground's public values.
  `row_at_lot`: **`row_at_seat` at these**: the fourth sub-protocol is a member of `P4.k6Hear Z G`,
    dressed; the fifth is the commitment `K1.laterAt` with the table's quiet step laid behind it,
    carried to the type of claims, dressed; the run "policy" is a run of the dressed fourth.

Limits. No theorem here names the list of all tables, the fold over the chain's flat list, or the
verifier. That the maker finds these two members at the fourth and the fifth place, and that the
chain runs the claims where `KeptAll` ends, is read and not shown. The premises on states of
`row_at_seat` stand as they are. No states are shown at which the premises hold together. Four forms
of 35. The full size alone. Nothing on soundness.


-/
import Johnson.Desc.Reads.RowAtSeat
import Johnson.Desc.ProofFile.Lot.K6K7
import Johnson.Desc.ProofFile.Lots.Makers
import Johnson.Desc.ProofFile.Frames1
import Johnson.Desc.Sound.SeatGuardLaws
import Johnson.Desc.K1.Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.AtSeat

open VerifiableInference.Desc (Block Claim Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K8 (ReadsQuiet.head)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Reads.AtHead

/-- A sub-protocol with the test on a mark of failure, the place's name and the place. -/
def placed (a : Place) (n : String) (b : Block S Claim) : Block S Claim :=
  { { ProofFile.guardMark b with name := n } with place := a }

/-- A sub-protocol as the first chain holds it. -/
def dressed (same : S → S → Bool) (but : Place → Bool) (a : Place) (n : String)
    (b : Block S Claim) : Block S Claim :=
  Block.guarded same but (placed a n b)

/-- Where the dressed sub-protocol accepts, the bare one accepts, with the same state behind. -/
theorem dressed_yes {same : S → S → Bool} {but : Place → Bool} {a : Place} {n : String}
    {b : Block S Claim} {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h : (dressed same but a n b).decide s rs gs = .ok s') : b.decide s rs gs = .ok s' := by
  have h1 := VerifiableInference.Desc.guarded_under same but (placed a n b) s rs gs s' h
  have h2 : ((b.decide s rs gs).bind fun t =>
      match t.failed with
      | none => .ok t
      | some m => .error ("marked: " ++ m)) = .ok s' := h1
  cases hb : b.decide s rs gs with
  | error e =>
    rw [hb] at h2
    cases h2
  | ok t =>
    rw [hb] at h2
    have h3 : (match t.failed with
      | none => (.ok t : Except String S)
      | some m => .error ("marked: " ++ m)) = .ok s' := h2
    split at h3
    · rw [Except.ok.inj h3]
    · cases h3

/-- Each run of claims of the dressed sub-protocol is a run of the bare one. -/
theorem dressed_claims {same : S → S → Bool} {but : Place → Bool} {a : Place} {n : String}
    {b : Block S Claim} {c : String × (ℕ → S → Except String (List Claim × S))}
    (hc : c ∈ (dressed same but a n b).claims) :
    ∃ c₀ ∈ b.claims, c₀.1 = c.1 ∧ ∀ k t y, c.2 k t = .ok y → c₀.2 k t = .ok y := by
  obtain ⟨c₀, h₀, e, hy⟩ := VerifiableInference.Desc.guarded_claims_under same but (placed a n b)
    c hc
  exact ⟨c₀, h₀, e, fun k t y h => (hy k t y h).1⟩

/-- A member of the table's list for the output head's own rounds. -/
theorem k6_is {Z : ProofFile.Pub} {G : ProofFile.Ground} {B : Block S Claim} (h : B ∈ P4.k6Hear Z G) :
    ∃ ms, seatedClaims G.W (G.built.size - 1) ms = some B := by
  unfold P4.k6Hear at h
  cases hb : P4.headBefore Z G with
  | none =>
    rw [hb] at h
    cases h
  | some ms =>
    rw [hb] at h
    exact ⟨ms, Option.mem_toList.1 h⟩

/-- What the table of the commitments lays behind the reads' commitment, at the head's segment. -/
theorem quiet_is (G : ProofFile.Ground) (l : ℕ) (X : OnBytes.Model.Stages.LinkH) (nm why : String)
    (a : Place) (hX : X.kind = 2) {g : ℕ}
    (hl : (G.built.toList.map fun Y => (Y.kind, Y.g))[l]? = some (2, g)) :
    ProofFile.orLoud nm a why (ProofFile.readsQuietAt G l X 5) =
      ReadsQuiet.head ⟨⟨1, some l, 5, .K1⟩, G.W.hS, G.W.HLy, G.W.H⟩ := by
  unfold ProofFile.readsQuietAt VerifiableInference.Desc.K8.ReadsQuiet.blockAt
  rw [hX, hl]
  rfl

/-- **The row at the head, at the tables' sub-protocols as the chain dresses them.** -/
theorem row_at_lot (Z : ProofFile.Pub) (G : ProofFile.Ground) (iU3 cols : ℕ)
    (hi : G.W.H.tl.ix.U.getD 2 none = some iU3) (U : Public (fillOf G.W iU3 cols))
    (same : S → S → Bool) (but : Place → Bool) (a4 a5 : Place) (n4 n5 : String)
    {B4 : Block S Claim} (hB4 : B4 ∈ P4.k6Hear Z G)
    (X : OnBytes.Model.Stages.LinkH) (hX : X.kind = 2) {g : ℕ}
    (hl : (G.built.toList.map fun Y => (Y.kind, Y.g))[G.built.size - 1]? = some (2, g))
    (nm why : String) (aq : Place)
    (q : OnBytes.Params.First) (gp : _root_.Desc.Plain.GPar) (reads : Option (List ℕ))
    {s0 s2 s4 s : S} {rs4 : List Fmt.RoundView} {gs4 : List (List (ℕ × List UInt64))}
    (h4 : (dressed same but a4 n4 B4).decide s0 rs4 gs4 = .ok s2)
    {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h5 : (dressed same but a5 n5
      (((VerifiableInference.Desc.K1.laterAt q gp (G.built.size - 1) 5 1 reads).andThen
        (VerifiableInference.Desc.K1.laterAt (Cl := Unit) q gp (G.built.size - 1) 5 1 reads).name
        (ProofFile.orLoud nm aq why (ProofFile.readsQuietAt G (G.built.size - 1) X 5))).retype)).decide
        s2 rs gs = .ok s4)
    (k : KeptAll iU3 s4 s)
    {c : String × (ℕ → S → Except String (List Claim × S))}
    (hc : c ∈ (dressed same but a4 n4 B4).claims) (hname : c.1 = "policy") {n : ℕ}
    {y : List Claim × S} (hrun : c.2 n s = .ok y)
    (hWL : WellLaid ((seatAt G.W.hS iU3).ledger s0))
    (hcols : ∀ o, s4.here = .head o → ∃ tr, o.F.trees[iU3]? = some tr ∧ tr.K = cols)
    (hzb : ∀ o x, s2.here = .head o → o.x = some x →
      x.g1.zb0.size = x.g1.shape.kT + x.g1.shape.cK + 5 ∧
      x.g1.zb1.size = x.g1.shape.kT + x.g1.shape.cK + 5) :
    HeadClaimW (fillOf G.W iU3 cols).letters ∧ (fillOf G.W iU3 cols).AtClose s ∧
      y.1 = ((fillOf G.W iU3 cols).letters.letters.forms () s).map asClaim := by
  obtain ⟨ms, hs⟩ := k6_is hB4
  obtain ⟨c₀, hc₀, e₀, hy₀⟩ := dressed_claims hc
  have h5' := dressed_yes h5
  rw [quiet_is G (G.built.size - 1) X nm why aq hX hl] at h5'
  exact row_at_seat G.W (G.built.size - 1) iU3 cols hi U hs (dressed_yes h4)
    (VerifiableInference.Desc.K1.parLater q gp (G.built.size - 1) 5 1) (G.built.size - 1) 1 reads
    h5' k hc₀ (e₀.trans hname) (hy₀ n s y hrun) hWL hcols hzb

end VerifiableInference.Reads.AtSeat

#print axioms VerifiableInference.Reads.AtSeat.dressed_yes
#print axioms VerifiableInference.Reads.AtSeat.dressed_claims
#print axioms VerifiableInference.Reads.AtSeat.k6_is
#print axioms VerifiableInference.Reads.AtSeat.quiet_is
#print axioms VerifiableInference.Reads.AtSeat.row_at_lot
