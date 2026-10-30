-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdReqBelow.lean: every round-by-round error of a request's preamble, as a probability, is at
most a number κ, if every move's is.

In round-by-round soundness each round of a reduction has an error: a number of values of the
verifier message (`Err`, Iop/Rbr.lean). This file shows that one bound on these errors passes from
the reductions of a request's preamble to their composition.

Definitions, statements (each a `Prop` in `Iop.Spec` or `Cb.Spec`) and proofs. A chain (`IOR.Chain`,
Ior/KnowCollRulesChain.lean) is a sequence of interactive oracle reductions, each an `IOR.Link` with
its honest side, extractor and numbers, among them its list of errors `l.P.err`: one count for each
round. A request `r : LdReq a z` (Cb/Req1/LdReq.lean) is a first sending, further moves, segments
and a last part; `r.chain` is the chain of them all.
The theorem on the holographic protocol asks of each sub-protocol's list of errors: in every round,
the count of bad verifier messages is at most κ times the number of verifier messages (`Err.Below`,
Iop/InteractiveOracleProof.lean). No sum of errors is formed: the bound is round by round. These errors are numbers
that a link lists (the data fields `Link.P.err`, `Nums.err`): that a link is sound at the numbers
that it lists is no statement of this file.

Main names:
  `c.ErrBelow κ`: every link of the chain c has `Err.Below` at κ. `Spec.chain_errBelow`: then the
    chain as one link has it. `Spec.errBelow_append`: `c.append c'` has it if and only if c and c'
    have.
  `p.Below κ`, `s.Below κ`, `S.Below κ`, `r.Below κ`: the same through a list of moves, a segment, a
    list of segments, a request.
  `Spec.ldReq_below`: `r.Below κ` → the errors of the request as a chain, and as one reduction
    (`r.F`, with its numbers `r.FP`, Cb/Req1/LdReqStart.lean, for a request that starts at a
    `LdStage.start`), as a probability, are at most κ.
  `Spec.ldSeg_below_named`: what `Err.Below` at κ says for the moves whose block is named. A
    sending: the sum over the members of (multiplicity of a seed) · (L choose 2) · (number of the
    sample map) is at most κ · (number of joint seeds); many rows into one: the evader's number is
    at most κ · (number of its seeds); a split, a step: nothing; the locations:
    (|P| - e - 1)^t ≤ κ · |P|^t; bridge-to-fold: what it says of the link `l`, a parameter of the
    move.

Limits: This file says nothing on the value of any number. It says nothing on proof of work (the
same rule for `Err.BelowG` is not written here).
Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdReqStart

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR.Chain
variable {K : Type}

/-- Every link's errors, as a probability, are at most κ, round by round. -/
def ErrBelow : {A B : Joint K} → Chain K A B → ℝ≥0∞ → Prop
  | _, _, .one l, κ => Err.Below l.P.err κ
  | _, _, .snoc c l, κ => c.ErrBelow κ ∧ Err.Below l.P.err κ

variable {A B C : Joint K}
theorem errBelow_one (l : Link K A B) (κ : ℝ≥0∞) :
    (Chain.one l).ErrBelow κ ↔ Err.Below l.P.err κ := by rw [ErrBelow]
theorem errBelow_snoc (c : Chain K A B) (l : Link K B C) (κ : ℝ≥0∞) :
    (c.snoc l).ErrBelow κ ↔ c.ErrBelow κ ∧ Err.Below l.P.err κ := by rw [ErrBelow]

end IOR.Chain

namespace Spec
open IOR

def chain_errBelow : Prop :=
  ∀ (K : Type) (A B : Joint K) (c : Chain K A B) (d : A.W) (κ : ℝ≥0∞),
    c.ErrBelow κ → Err.Below (c.link d).P.err κ

def errBelow_append : Prop :=
  ∀ (K : Type) (A B C : Joint K) (c : Chain K A B) (c' : Chain K B C) (κ : ℝ≥0∞),
    (c.append c').ErrBelow κ ↔ c.ErrBelow κ ∧ c'.ErrBelow κ

end Spec

open IOR IOR.Chain

theorem chain_errBelow : Spec.chain_errBelow := by
  intro K A B c d κ
  induction c with
  | one l => intro h; rw [link_one]; exact (errBelow_one l κ).1 h
  | snoc c l ih =>
      intro h
      rw [link_snoc]
      exact Err.Below.app (ih ((errBelow_snoc c l κ).1 h).1) ((errBelow_snoc c l κ).1 h).2

theorem errBelow_append : Spec.errBelow_append := by
  intro K A B C c c' κ
  induction c' with
  | one l => rw [append_one, errBelow_snoc, errBelow_one]
  | snoc c' l ih => rw [append_snoc, errBelow_snoc, errBelow_snoc, ih, and_assoc]

end Iop

namespace Cb
open Iop Prob Hiop IOR IOR.Chain
open scoped ENNReal

section
variable {E Kc : Type} [Field E] [Fintype E]

def LdProg.Below : {a b : LdStage E Kc} → LdProg a b → ℝ≥0∞ → Prop
  | _, _, .nil _, _ => True
  | _, _, .snoc p m, κ => p.Below κ ∧ m.chain.ErrBelow κ

structure LdSeg.Below {a d : LdStage E Kc} (s : LdSeg a d) (κ : ℝ≥0∞) : Prop where
  body : s.body.Below κ
  bat  : s.bat.Below κ
  fold : s.fold.Below κ
  snd  : Err.Below s.snd.link.P.err κ
  loc  : s.loc.Below κ

def LdSegs.Below : {a b : LdStage E Kc} → LdSegs a b → ℝ≥0∞ → Prop
  | _, _, .nil _, _ => True
  | _, _, .snoc S s, κ => S.Below κ ∧ s.Below κ

structure LdReq.Below {a z : LdStage E Kc} (r : LdReq a z) (κ : ℝ≥0∞) : Prop where
  first : Err.Below r.first.link.P.err κ
  more  : r.more.Below κ
  segs  : r.segs.Below κ
  last  : r.last.Below κ

end

namespace Spec

/-- Every round of a request's preamble. -/
def ldReq_below : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E],
    (∀ (a z : LdStage E Kc) (r : LdReq a z) (w₀ : a.W) (κ : ℝ≥0∞),
      r.Below κ → Err.Below (r.chain.link w₀).P.err κ) ∧
    ∀ (Xi Wi : Type) (E0 : ExtSpec) (A : Rels Kc Xi E0 Wi) (z : LdStage E Kc)
        (r : LdReq (LdStage.start E Kc A) z) (w₀ : Wi) (κ : ℝ≥0∞),
      r.Below κ → Err.Below (r.FP w₀).err κ

/-- What `Err.Below` says for the moves whose block is named. -/
def ldSeg_below_named : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (κ : ℝ≥0∞),
    (∀ (a : LdStage E Kc) (d : LdSendD a),
      Err.Below d.link.P.err κ ↔
      (ldSendFamErr d.N d.Sd d.L : ℝ≥0∞) ≤ κ * (Fintype.card d.Sd.D : ℝ≥0∞)) ∧
    (∀ D : LdBatD E Kc,
      Err.Below D.link.P.err κ ↔ (D.Z.err : ℝ≥0∞) ≤ κ * (Fintype.card D.Z.D : ℝ≥0∞)) ∧
    (∀ D : LdSplD E Kc, Err.Below D.link.P.err κ) ∧
    (∀ D : LdLocD E Kc,
      Err.Below D.link.P.err κ ↔
      (((Fintype.card D.P - D.e - 1) ^ D.t : ℕ) : ℝ≥0∞) ≤
        κ * (Fintype.card (Fin D.t → D.P) : ℝ≥0∞)) ∧
    (∀ (D : LdFoldD E Kc) (l : Link Kc D.src.J D.mid),
      Err.Below (D.link l).P.err κ ↔ Err.Below l.P.err κ) ∧
    (∀ (a b : LdStage E Kc) f g m back, (LdMv.step a b f g m back).chain.ErrBelow κ)

end Spec

section
variable {E Kc : Type} [Field E] [Fintype E] {A : Joint Kc}

theorem LdProg.below_snoc {a b c : LdStage E Kc} (p : LdProg a b) (m : LdMv b c) (κ : ℝ≥0∞) :
    (p.snoc m).Below κ ↔ p.Below κ ∧ m.chain.ErrBelow κ := by
  rw [LdProg.Below]
theorem LdSegs.below_snoc {a b c : LdStage E Kc} (S : LdSegs a b) (s : LdSeg b c) (κ : ℝ≥0∞) :
    (S.snoc s).Below κ ↔ S.Below κ ∧ s.Below κ := by
  rw [LdSegs.Below]

theorem LdProg.onto_below {a b : LdStage E Kc} (p : LdProg a b) (κ : ℝ≥0∞) :
    ∀ c₀ : Chain Kc A a.J, c₀.ErrBelow κ → p.Below κ → (p.onto c₀).ErrBelow κ := by
  induction p with
  | nil => intro c₀ h0 _; rw [LdProg.onto_nil]; exact h0
  | snoc p m ih =>
      intro c₀ h0 h
      rw [LdProg.onto_snoc]
      exact (errBelow_append Kc _ _ _ _ _ κ).2
        ⟨ih c₀ h0 ((LdProg.below_snoc p m κ).1 h).1, ((LdProg.below_snoc p m κ).1 h).2⟩

theorem LdSeg.onto_below {a d : LdStage E Kc} (s : LdSeg a d) (κ : ℝ≥0∞) (c₀ : Chain Kc A a.J)
    (h0 : c₀.ErrBelow κ) (h : s.Below κ) : (s.onto c₀).ErrBelow κ :=
  s.loc.onto_below κ _
    ((errBelow_snoc _ _ κ).2
      ⟨s.fold.onto_below κ _ (s.bat.onto_below κ _ (s.body.onto_below κ _ h0 h.body) h.bat) h.fold,
        h.snd⟩) h.loc

theorem LdSegs.onto_below {a b : LdStage E Kc} (S : LdSegs a b) (κ : ℝ≥0∞) :
    ∀ c₀ : Chain Kc A a.J, c₀.ErrBelow κ → S.Below κ → (S.onto c₀).ErrBelow κ := by
  induction S with
  | nil => intro c₀ h0 _; rw [LdSegs.onto_nil]; exact h0
  | snoc S s ih =>
      intro c₀ h0 h
      rw [LdSegs.onto_snoc]
      exact s.onto_below κ _ (ih c₀ h0 ((LdSegs.below_snoc S s κ).1 h).1)
        ((LdSegs.below_snoc S s κ).1 h).2

theorem LdReq.chain_below {a z : LdStage E Kc} (r : LdReq a z) (κ : ℝ≥0∞) (h : r.Below κ) :
    r.chain.ErrBelow κ :=
  r.last.onto_below κ _
    (r.segs.onto_below κ _ (r.more.onto_below κ _ ((errBelow_one _ κ).2 h.first) h.more) h.segs)
    h.last

end

theorem ldReq_below : Spec.ldReq_below := fun _ Kc _ _ =>
  ⟨fun _ _ r w₀ κ h => chain_errBelow Kc _ _ r.chain w₀ κ (r.chain_below κ h),
    fun _ _ _ _ _ r w₀ κ h => chain_errBelow Kc _ _ r.chain (ldStartW _ w₀) κ (r.chain_below κ h)⟩

theorem ldSeg_below_named : Spec.ldSeg_below_named := by
  intro E Kc _ _ κ
  refine ⟨fun a d => ?_, fun D => ?_, fun D => ?_, fun D => ?_,
    fun D l => Iff.rfl, fun a b f g m back => ?_⟩
  · constructor
    · intro h; exact h.1
    · intro h; exact ⟨h, by simp, trivial⟩
  · constructor
    · intro h; exact h.1
    · intro h; exact ⟨h, trivial⟩
  · exact ⟨by simp, trivial⟩
  · constructor
    · intro h; exact h.1
    · intro h; exact ⟨h, trivial⟩
  · exact (errBelow_one _ κ).2 trivial

end Cb
