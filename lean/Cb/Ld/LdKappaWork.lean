-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaWork.lean: bounds on the errors of round-by-round soundness when some rounds have proof
of work. The property is "every round's error, counting its proof-of-work bits, is at most κ". It is
treated for a part all of whose rounds have w bits, and for a request's preamble with w bits at the
rounds that draw locations and none elsewhere.

Definitions and theorems: glue on Cb/Ld/LdKappaBits.lean and Cb/Req1/LdReqBelow.lean; framework
only; nothing is evaluated.
A list of errors (`Err`) holds one number for each round, a count, not a probability: how many
values of that round's verifier message may let a prover that has lost (`Doomed`) escape. (`Err`,
`Doomed`: Iop/Rbr.lean.) `Err.Below ε κ` (Iop/InteractiveOracleProof.lean) says of a list ε of errors, round by
round: e ≤ κ · v, with e the round's error and v the number of values of its verifier message.
`Err.BelowB ε B κ` (Cb/Ld/LdKappaBits.lean): the list B has one entry b for each round, and e ≤ κ ·
(2^b · v): b bits of proof of work count as a factor 2^b. A list, a chain, a list of moves or a part
is at most κ if every round's error in it is (`Chain.ErrBelow`, `LdProg.Below`,
Cb/Req1/LdReqBelow.lean; with bits: `Chain.BelowB`). These errors are numbers that a link lists (the
data fields `Link.P.err`, `LinkA.err`): that a link is sound at the numbers that it lists is no
statement of this file; for a request's preamble, under `LdReq.Hyp`, that tie is
`Spec.ldReqStart_goodB` (Cb/Req1/LdReqStart.lean) (that condition itself asks soundness of some of
the parts one level down: for these the tie carries soundness, it does not found it).

Why: e ≤ κ · (2^w · v) says the same as e ≤ (κ · 2^w) · v. So a part all of whose rounds have w
bits is at most κ, proof of work counted, if and only if it is at most κ · 2^w without proof of
work (`Iop.belowB_unif`, for a list of errors): for such parts all rules on `Err.Below` that exist
can be used as they stand, at the number κ · 2^w. A composed list is cut into such parts.

Main names:
  `LdSeg.BelowW`, `LdSegs.BelowW`, `LdReq.BelowW`: `LdSeg.Below`, `LdSegs.Below`, `LdReq.Below` of
    Cb/Req1/LdReqBelow.lean, with the part "locations" at most κ · 2^w and all else at most κ.
  `ldReq_belowW`: a request's preamble, round by round.

Limits: this file says nothing on the value of any number. It says nothing on the way back, but for
`Iop.belowB_unif`, which is an equivalence. It does not say why b bits of proof of work may be
counted as a factor 2^b: `Err.BelowB` counts them so by definition (see `Iop.belowB_iff_G`,
Cb/Ld/LdKappaBits.lean; `Iop.Err.below_grind_iff`, Iop/GrindProofs.lean; `InteractiveOracleProof.grind` and the
limits in the head of Iop/Grind.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdKappaBits
import Cb.Req1.LdReqBelow
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Iop
open scoped ENNReal

theorem belowB_unif :
    ∀ {s : Shape} (ε : Err s) (κ : ℝ≥0∞) (w : ℕ),
      Err.BelowB ε (List.replicate s.nAll w) κ ↔ Err.Below ε (κ * 2 ^ w)
  | [], _, _, _ => ⟨fun _ => trivial, fun _ => rfl⟩
  | _ :: _, (_, ε), κ, w =>
    ⟨fun h => ⟨by rw [mul_assoc]; exact h.1, (belowB_unif ε κ w).1 h.2⟩,
      fun h => ⟨by rw [← mul_assoc]; exact h.1, (belowB_unif ε κ w).2 h.2⟩⟩

theorem belowB_none {s : Shape} (ε : Err s) (κ : ℝ≥0∞) (h : Err.Below ε κ) :
    Err.BelowB ε (List.replicate s.nAll 0) κ :=
  (belowB_unif ε κ 0).2 (by simpa using h)

open IOR

theorem IOR.Chain.belowB_mk {K : Type} {A B C : Joint K} (c : Chain K A B) (l : Link K B C)
    (L₁ L₂ : List ℕ) (κ : ℝ≥0∞) (h₁ : c.BelowB L₁ κ) (h₂ : Err.BelowB l.P.err L₂ κ) :
    (c.snoc l).BelowB (L₁ ++ L₂) κ :=
  (Chain.belowB_snoc c l _ κ).2 ⟨L₁, L₂, rfl, h₁, h₂⟩

theorem IOR.Chain.belowB_app {K : Type} {A B C : Joint K} (c : Chain K A B) (c' : Chain K B C)
    (L₁ L₂ : List ℕ) (κ : ℝ≥0∞) (h₁ : c.BelowB L₁ κ) (h₂ : c'.BelowB L₂ κ) :
    (c.append c').BelowB (L₁ ++ L₂) κ :=
  (chain_belowB_append c c' κ _).2 ⟨L₁, L₂, rfl, h₁, h₂⟩

theorem IOR.ChainA.belowB_mk {K : Type} {A B C : Joint K} (c : ChainA K A B) (a : LinkA K B C)
    (L₁ L₂ : List ℕ) (κ : ℝ≥0∞) (h₁ : c.BelowB L₁ κ) (h₂ : Err.BelowB a.err L₂ κ) :
    (c.snoc a).BelowB (L₁ ++ L₂) κ :=
  (ChainA.belowB_snoc c a _ κ).2 ⟨L₁, L₂, rfl, h₁, h₂⟩

theorem IOR.ChainA.belowB_app {K : Type} {A B C : Joint K} (c : ChainA K A B) (c' : ChainA K B C)
    (L₁ L₂ : List ℕ) (κ : ℝ≥0∞) (h₁ : c.BelowB L₁ κ) (h₂ : c'.BelowB L₂ κ) :
    (c.append c').BelowB (L₁ ++ L₂) κ :=
  (chainA_belowB_append c c' κ _).2 ⟨L₁, L₂, rfl, h₁, h₂⟩

theorem IOR.Chain.belowB_unif {K : Type} {A B : Joint K} (c : Chain K A B) (κ : ℝ≥0∞) (w : ℕ) :
    c.ErrBelow (κ * 2 ^ w) → c.BelowB (List.replicate c.nAll w) κ := by
  induction c with
  | one l => intro h; rw [Chain.nAll]; exact (Chain.belowB_one l _ κ).2 ((Iop.belowB_unif l.P.err κ w).2 ((Chain.errBelow_one l _).1 h))
  | snoc c l ih =>
      intro h
      rw [Chain.nAll, List.replicate_add]
      exact Chain.belowB_mk c l _ _ κ (ih ((Chain.errBelow_snoc c l _).1 h).1)
        ((Iop.belowB_unif l.P.err κ w).2 ((Chain.errBelow_snoc c l _).1 h).2)

end Iop

namespace Cb
open Iop Prob Hiop IOR IOR.Chain
open scoped ENNReal

section
variable {E Kc : Type} [Field E] [Fintype E] {A : Joint Kc}

theorem LdProg.onto_belowB {a b : LdStage E Kc} (p : LdProg a b) (κ : ℝ≥0∞) (w : ℕ)
    (c₀ : Chain Kc A a.J) (L : List ℕ) (h0 : c₀.BelowB L κ) :
    p.Below (κ * 2 ^ w) → (p.onto c₀).BelowB (L ++ List.replicate p.nAll w) κ := by
  induction p with
  | nil => intro _; rw [LdProg.onto_nil, LdProg.nAll]; simpa using h0
  | snoc p m ih =>
      intro h
      rw [LdProg.onto_snoc, LdProg.nAll, List.replicate_add, ← List.append_assoc]
      exact Chain.belowB_app _ _ _ _ κ (ih ((LdProg.below_snoc p m _).1 h).1)
        (Chain.belowB_unif m.chain κ w ((LdProg.below_snoc p m _).1 h).2)

theorem LdProg.onto_belowB0 {a b : LdStage E Kc} (p : LdProg a b) (κ : ℝ≥0∞) (c₀ : Chain Kc A a.J)
    (L : List ℕ) (h0 : c₀.BelowB L κ) (h : p.Below κ) :
    (p.onto c₀).BelowB (L ++ List.replicate p.nAll 0) κ :=
  p.onto_belowB κ 0 c₀ L h0 (by simpa using h)

/-- the bits of a segment: none, but w at the rounds of its part "locations" (0 for the rounds of
body, batching, fold and the one sending) -/
def LdSeg.bits {a d : LdStage E Kc} (s : LdSeg a d) (w : ℕ) : List ℕ :=
  (((List.replicate s.body.nAll 0 ++ List.replicate s.bat.nAll 0) ++
        List.replicate s.fold.nAll 0) ++
      List.replicate s.snd.link.R.shape.nAll 0) ++
    List.replicate s.loc.nAll w

structure LdSeg.BelowW {a d : LdStage E Kc} (s : LdSeg a d) (w : ℕ) (κ : ℝ≥0∞) : Prop where
  body : s.body.Below κ
  bat  : s.bat.Below κ
  fold : s.fold.Below κ
  snd  : Err.Below s.snd.link.P.err κ
  loc  : s.loc.Below (κ * 2 ^ w)

theorem LdSeg.onto_belowB {a d : LdStage E Kc} (s : LdSeg a d) (w : ℕ) (κ : ℝ≥0∞)
    (c₀ : Chain Kc A a.J) (L : List ℕ) (h0 : c₀.BelowB L κ) (h : s.BelowW w κ) :
    (s.onto c₀).BelowB (L ++ s.bits w) κ := by
  unfold LdSeg.onto LdSeg.bits
  simp only [← List.append_assoc]
  exact s.loc.onto_belowB κ w _ _
    (Chain.belowB_mk _ _ _ _ κ
      (s.fold.onto_belowB0 κ _ _
        (s.bat.onto_belowB0 κ _ _ (s.body.onto_belowB0 κ c₀ L h0 h.body) h.bat) h.fold)
      (belowB_none _ κ h.snd)) h.loc

def LdSegs.bits (w : ℕ) : {a b : LdStage E Kc} → LdSegs a b → List ℕ
  | _, _, .nil _ => []
  | _, _, .snoc S s => S.bits w ++ s.bits w

def LdSegs.BelowW (w : ℕ) (κ : ℝ≥0∞) : {a b : LdStage E Kc} → LdSegs a b → Prop
  | _, _, .nil _ => True
  | _, _, .snoc S s => S.BelowW w κ ∧ s.BelowW w κ

theorem LdSegs.onto_belowB {a b : LdStage E Kc} (S : LdSegs a b) (w : ℕ) (κ : ℝ≥0∞)
    (c₀ : Chain Kc A a.J) (L : List ℕ) (h0 : c₀.BelowB L κ) :
    S.BelowW w κ → (S.onto c₀).BelowB (L ++ S.bits w) κ := by
  induction S with
  | nil => intro _; rw [LdSegs.onto_nil, LdSegs.bits]; simpa using h0
  | snoc S s ih =>
      intro h
      rw [LdSegs.BelowW] at h
      rw [LdSegs.onto_snoc, LdSegs.bits, ← List.append_assoc]
      exact s.onto_belowB w κ _ _ (ih h.1) h.2

/-- the bits of a request's preamble: its segments' bits in a row; 0 for first sending, further
first moves and last part -/
def LdReq.bits {a z : LdStage E Kc} (r : LdReq a z) (w : ℕ) : List ℕ :=
  ((List.replicate r.first.link.R.shape.nAll 0 ++ List.replicate r.more.nAll 0) ++ r.segs.bits w) ++
    List.replicate r.last.nAll 0

structure LdReq.BelowW {a z : LdStage E Kc} (r : LdReq a z) (w : ℕ) (κ : ℝ≥0∞) : Prop where
  first : Err.Below r.first.link.P.err κ
  more  : r.more.Below κ
  segs  : r.segs.BelowW w κ
  last  : r.last.Below κ

theorem LdReq.chain_belowB {a z : LdStage E Kc} (r : LdReq a z) (w : ℕ)
    (κ : ℝ≥0∞) (h : r.BelowW w κ) : r.chain.BelowB (r.bits w) κ :=
  r.last.onto_belowB0 κ _ _
    (r.segs.onto_belowB w κ _ _
      (r.more.onto_belowB0 κ _ _ ((Chain.belowB_one _ _ κ).2 (belowB_none _ κ h.first)) h.more)
      h.segs) h.last

end

/-- A request's preamble with proof of work at the rounds that draw locations: `r.BelowW w κ` gives
`Err.BelowB (r.FP w₀).err (r.bits w) κ`. -/
theorem ldReq_belowW {E Kc : Type} [Field E] [Fintype E] {Xi Wi : Type} {E0 : ExtSpec}
    (A : Rels Kc Xi E0 Wi) (z : LdStage E Kc) (r : LdReq (LdStage.start E Kc A) z) (w₀ : Wi) (w : ℕ)
    (κ : ℝ≥0∞) (h : r.BelowW w κ) :
    Err.BelowB (r.FP w₀).err (r.bits w) κ :=
  (chain_belowB r.chain (ldStartW _ w₀) κ _).2 (r.chain_belowB w κ h)

end Cb
