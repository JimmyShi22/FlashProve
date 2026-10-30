-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ClosingPasses.lean: the kind "the code switch" (K2): THE
CLOSING OVER MORE SEGMENTS PASSES THROUGH WHAT THE CLOSING OVER FEWER RETURNED: where the closing
(`closingFrom`, Honest/K2/Closing.lean) over the first l₀ segments returned x₀ at one function of
own data, list of challenges and reader of stretches, the closing over the first l, l₀ ≤ l, at
another such three that agree with the first there, goes on from x₀; and where it returns, its next
step has laid the rows of segment number l₀ AT x₀. Statements with their proofs; no definition.

  `take_split`           the first l of a list are its first l₀ and what of the first l lies behind
  `closingFrom_passes`   THE LAW
  `closingFrom_head`     where the closing's first step returns, `segmentGroupRows` has returned
  `closing_lays_at`      THE END: the rows of segment number l₀, laid at x₀

By: `closingFrom_append` (Honest/K2/Law/ClosingGrows.lean) · `closingFrom_grows`
(Honest/K2/Law/ClosingSame.lean) · `OkGives.bind` (Honest/K2/Law/RowsOfSegment.lean) ·
`segmentLeft_inv` (Honest/K2/Law/SegmentLeftInv.lean): of what it says of a step's return the first
clause alone is spent.

Limits. On texts with refusals: own data, challenges and readers of stretches are letters: no
sentence on what a stretch holds. That the two threes agree over the first l₀ segments are premises
(`GivesAll`; the own data at the segments' numbers; the challenges at the segments' own numbers).
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingSame
import Johnson.Desc.ProofFile.Honest.K2.Law.RowsOfSegment
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentLeftInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left)

theorem take_split {α : Type} (l : List α) {a b : Nat} (h : a ≤ b) :
    l.take a ++ (l.take b).drop a = l.take b := by
  have e := List.take_append_drop a (l.take b)
  rwa [List.take_take, Nat.min_eq_left h] at e

/-- **THE LAW.** -/
theorem closingFrom_passes (table : FreshTable) {own₀ own : Nat → Nat → Nat → Nat → Cb.Gl.E}
    {heard₀ heard : List Fmt.Drawn} {k₀ k : Nat → Except String Stretch} (hk : GivesAll k₀ k)
    (segs : List SegmentPub) {l₀ l : Nat} (hl : l₀ ≤ l)
    (ho : ∀ i, i < (segs.take l₀).length → own₀ (0 + i) = own (0 + i))
    (hg : ∀ S ∈ segs.take l₀, challengesOr0 heard₀ S.gamma = challengesOr0 heard S.gamma)
    {x₀ : Option (Left × List OnBytes.OracleShape) × Nat}
    (h₀ : closingFrom table own₀ heard₀ k₀ (segs.take l₀) 0 0 none = .ok x₀) :
    closingFrom table own heard k (segs.take l) 0 0 none =
      closingFrom table own heard k ((segs.take l).drop l₀) (0 + (segs.take l₀).length) x₀.2
        x₀.1 := by
  have e1 : closingFrom table own heard k (segs.take l₀) 0 0 none = .ok x₀ :=
    closingFrom_grows table hk (segs.take l₀) 0 0 none ho hg x₀ h₀
  calc closingFrom table own heard k (segs.take l) 0 0 none
      = closingFrom table own heard k (segs.take l₀ ++ (segs.take l).drop l₀) 0 0 none := by
        rw [take_split segs hl]
    _ = (closingFrom table own heard k (segs.take l₀) 0 0 none).bind fun x =>
          closingFrom table own heard k ((segs.take l).drop l₀) (0 + (segs.take l₀).length) x.2
            x.1 := closingFrom_append table own heard k _ _ 0 0 none
    _ = _ := by
        rw [e1]
        rfl

/-- Where the closing's first step returns, that segment's rows were laid. -/
theorem closingFrom_head {table : FreshTable} {own : Nat → Nat → Nat → Nat → Cb.Gl.E}
    {heard : List Fmt.Drawn} {k : Nat → Except String Stretch} {S : SegmentPub}
    {rest : List SegmentPub} {j base : Nat} {prev : Option (Left × List OnBytes.OracleShape)}
    {y : Option (Left × List OnBytes.OracleShape) × Nat}
    (h : closingFrom table own heard k (S :: rest) j base prev = .ok y) :
    ∃ R, segmentGroupRows table S (prev.map (·.1)) ((prev.map (·.2)).getD []) (own j) k base true =
      .ok R := by
  have g : OkGives (fun _ : Option (Left × List OnBytes.OracleShape) × Nat =>
      ∃ R, segmentGroupRows table S (prev.map (·.1)) ((prev.map (·.2)).getD []) (own j) k base true =
        .ok R)
      ((segmentLeft table S (prev.map (·.1)) ((prev.map (·.2)).getD []) (own j) heard k
        base).bind fun W =>
          closingFrom table own heard k rest (j + 1) (base + S.messages) (some W)) :=
    OkGives.bind fun W hW _ _ =>
      (segmentLeft_inv (W := W.1) (kept := W.2) hW).imp fun _ hR => hR.1
  exact g y h

/-- **THE END.** S: the segment number l₀. -/
theorem closing_lays_at (table : FreshTable) {own₀ own : Nat → Nat → Nat → Nat → Cb.Gl.E}
    {heard₀ heard : List Fmt.Drawn} {k₀ k : Nat → Except String Stretch} (hk : GivesAll k₀ k)
    (segs : List SegmentPub) {l₀ l : Nat} (hl : l₀ ≤ l)
    (ho : ∀ i, i < (segs.take l₀).length → own₀ (0 + i) = own (0 + i))
    (hg : ∀ S ∈ segs.take l₀, challengesOr0 heard₀ S.gamma = challengesOr0 heard S.gamma)
    {x₀ : Option (Left × List OnBytes.OracleShape) × Nat}
    (h₀ : closingFrom table own₀ heard₀ k₀ (segs.take l₀) 0 0 none = .ok x₀)
    {S : SegmentPub} {rest : List SegmentPub} (hS : (segs.take l).drop l₀ = S :: rest)
    {y : Option (Left × List OnBytes.OracleShape) × Nat}
    (h : closingFrom table own heard k (segs.take l) 0 0 none = .ok y) :
    ∃ R, segmentGroupRows table S (x₀.1.map (·.1)) ((x₀.1.map (·.2)).getD [])
      (own (0 + (segs.take l₀).length)) k x₀.2 true = .ok R := by
  rw [closingFrom_passes table hk segs hl ho hg h₀, hS] at h
  exact closingFrom_head h

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.take_split
#print axioms ProofFile.Honest.K2.Law.closingFrom_passes
#print axioms ProofFile.Honest.K2.Law.closingFrom_head
#print axioms ProofFile.Honest.K2.Law.closing_lays_at
