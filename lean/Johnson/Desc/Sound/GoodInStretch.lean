-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/GoodInStretch.lean: THE ROW'S DEBT, STRETCH BY STRETCH: `EachGoodIn` over a list
of pieces is `EachGoodIn` over its stretches, each from its own number on; and it reads its two
tables at the stretch's own boundaries alone. Small lemmas with their proofs.

Why. The rule for one chain (`chainKnowIn`, Johnson/Desc/Sound/KnowInProofs.lean) takes
`EachGoodIn on R 0 (p :: l)` at ONE pair of tables for the whole chain. A kind's files prove its law
for a stretch of the chain (a block; a link's three blocks around the batching), from a number j on,
at tables of its own make. These lemmas say when such laws add up to the rule's premise.

Main names:
  `eachGoodIn_append_iff`: over l₁ ++ l₂ from i: over l₁ from i and over l₂ from i + l₁.length,
    both ways. (The way from the two to the whole stands also in a file on a link's
    law, as `eachGoodIn_append`, Johnson/Desc/LinkLaw4.lean.)
  `eachGoodIn_congr`: two pairs of tables that agree at the boundaries i .. i + l.length owe the
    same over l from i.
  `goodIn_weaken`: one piece: the promise in front may grow and the one behind shrink; the relation
    behind may grow and the one in front shrink: FOR A STRETCH's TWO ENDS: there implications do
    where `eachGoodIn_glue` asks equations: weaken the first and the last piece, then glue.
  `eachGoodIn_glue`: a stretch's law at its own tables, which agree with the chain's at the
    stretch's boundaries, between what is owed in front of it and behind it: the whole.

Limits: THE TABLES MUST AGREE AS FUNCTIONS at each boundary of the stretch, its first and its last
too: a stretch whose own promise at its last boundary says less than the chain's table there does
not fit: its law must first be strengthened. Nothing on acceptance; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.GoodIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)

variable {S Cl W : Type} {C : CK} {F : Frame}

/-- Over two lists in a row. -/
theorem eachGoodIn_append_iff (on : ℕ → S × F.E.Str → Prop) (R : ℕ → S × F.E.Str → W → Prop) :
    ∀ (l₁ l₂ : List (Piece C F S Cl W)) (i : ℕ),
      EachGoodIn on R i (l₁ ++ l₂) ↔
        EachGoodIn on R i l₁ ∧ EachGoodIn on R (i + l₁.length) l₂
  | [], l₂, i => by
    show EachGoodIn on R i l₂ ↔ True ∧ EachGoodIn on R (i + 0) l₂
    rw [Nat.add_zero, true_and]
  | p :: l₁, l₂, i => by
    show (p.GoodIn (on i) (on (i + 1)) (R i) (R (i + 1)) ∧ EachGoodIn on R (i + 1) (l₁ ++ l₂)) ↔
      (p.GoodIn (on i) (on (i + 1)) (R i) (R (i + 1)) ∧ EachGoodIn on R (i + 1) l₁) ∧
        EachGoodIn on R (i + (l₁.length + 1)) l₂
    rw [eachGoodIn_append_iff on R l₁ l₂ (i + 1), and_assoc,
      show i + 1 + l₁.length = i + (l₁.length + 1) by omega]

/-- The tables are read at the stretch's own boundaries alone. -/
theorem eachGoodIn_congr (on on' : ℕ → S × F.E.Str → Prop)
    (R R' : ℕ → S × F.E.Str → W → Prop) :
    ∀ (l : List (Piece C F S Cl W)) (i : ℕ),
      (∀ k, i ≤ k → k ≤ i + l.length → on k = on' k ∧ R k = R' k) →
      EachGoodIn on R i l → EachGoodIn on' R' i l
  | [], _, _, _ => trivial
  | p :: l, i, h, g => by
    have h0 := h i (Nat.le_refl i) (Nat.le_add_right i _)
    have h1 := h (i + 1) (Nat.le_succ i) (by rw [List.length_cons]; omega)
    refine ⟨?_, eachGoodIn_congr on on' R R' l (i + 1) (fun k hk hk' => h k (by omega)
      (by rw [List.length_cons]; omega)) g.2⟩
    rw [← h0.1, ← h0.2, ← h1.1, ← h1.2]
    exact g.1

/-- **A stretch's law at its own tables, laid into the chain's.** -/
theorem eachGoodIn_glue (on onJ : ℕ → S × F.E.Str → Prop)
    (R relJ : ℕ → S × F.E.Str → W → Prop) (front mid back : List (Piece C F S Cl W)) (i : ℕ)
    (hfit : ∀ k, i + front.length ≤ k → k ≤ i + front.length + mid.length →
      onJ k = on k ∧ relJ k = R k)
    (g₁ : EachGoodIn on R i front) (g₂ : EachGoodIn onJ relJ (i + front.length) mid)
    (g₃ : EachGoodIn on R (i + front.length + mid.length) back) :
    EachGoodIn on R i (front ++ mid ++ back) := by
  rw [eachGoodIn_append_iff, eachGoodIn_append_iff, List.length_append, ← Nat.add_assoc]
  exact ⟨⟨g₁, eachGoodIn_congr onJ on relJ R mid _ hfit g₂⟩, g₃⟩

/-- What a piece owes between stronger promises and relations it owes between weaker ones: the
promise in front may grow, the promise behind may shrink; the relation behind may grow, the relation
in front may shrink. -/
theorem goodIn_weaken (p : Piece C F S Cl W) (on₁ on₂ on₁' on₂' : S × F.E.Str → Prop)
    (R₁ R₂ R₁' R₂' : S × F.E.Str → W → Prop) (h1 : ∀ a, on₂ a → on₁ a) (h2 : ∀ b, on₁' b → on₂' b)
    (h3 : ∀ b w, R₂' b w → R₁' b w) (h4 : ∀ a w, R₁ a w → R₂ a w)
    (g : p.GoodIn on₁ on₁' R₁ R₁') : p.GoodIn on₂ on₂' R₂ R₂' := by
  intro a ha
  refine _root_.Iop.Doomed.mono _ _ ?_ (g a (h1 a ha))
  intro τ hτ b hb
  exact ⟨h2 b (hτ b hb).1, fun w hw => h4 a _ ((hτ b hb).2 w (h3 b w hw))⟩


end VerifiableInference.Desc.Sound
