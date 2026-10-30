-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/LedgerClaim.lean: what a matrix of field elements of the committed matrix's shape
holds,
and the claim of a request on it: the two letters on meaning of the description made of the three
files' protocols, as written terms, at the reference sizes.

Definitions and theorems. The description takes A : D.Claims X (OnBytes/Slice/DecoderRec.lean): the
matrices, when a matrix is in range, and the claim of an instance on a matrix. This file writes the
last two, over any number of rows and columns,
so that it names no decoder; Johnson/Flat/ClaimsLedger.lean lays them into a D.Claims.

Main names:
  SaysC M W: the integer matrix W says the cells of M (each cell is the cast of W's entry), and W is
    0 outside M's shape.
  Holds M i: the well-formed matrix of digits i (Cm.Idx, Cm/RelBase.lean) says M.
  InRange M: M holds an index.
  RelL s M x: M holds an index i, and some trace T meets the library's relaxed relation with the
  cost
    ledger at the protocol's prime and at exact match: Policy.LedgerRel.Rno Cb.Gl.p
    (Policy.ppOf s AcceptancePolicy.exact) i x T (Policy/Rel/LedgerRel.lean): r < e; every cell that a segment
    reads is below 2^18 in absolute value; the conditions modulo the prime.
  indexOf M, nextTok s M: the index that M holds, and the integer model's next token there.
  WellFormed x, Req, buildReq: a request with r < e, and y = 0 if e is before the window's end; the
    type of these; the builder into it.
  holds_unique: a matrix holds at most one index.
  relL_iff: at a lawful table of scales RelL s M x says: M holds an index at which x is true under
    exact match (Policy.IsTrueUnder): by the library's ledger_relation_at_protocol_prime.
  sound_core: at a lawful table of scales: if a request is built from a prompt with output tokens
  and
    RelL holds of it at M, the output tokens are nextTok's at M.

WHAT ENFORCES WHICH CLAUSE, by reading of the verifier's Lean text (no theorem here):
  InRange: the key file's lookups (the parameter item "ranges", OnBytes/Key/Ranges.lean): single
    entries, and pairs of digits of two-byte weights, each in a range. That the key file's item is
    the planner's at the shipped layout is a public premise, not written here.
  r < e, and y = 0 if e is before the window's end: the program's reader of a request refuses all
    else (Model.Head.stFromCall, OnBytes/Model/HeadLayout.lean, "statement-range"), BEFORE it opens
    the proof file. The proof file's protocol holds that refusal only if its first block runs the
    reader on the instance's words; else the instances must be cut to Req.
  below 2^18: each sub-proof's smallness test, whose bound is twice 2^17 (lbz,
  OnBytes/Model/Frame.lean;
    noWrap, OnBytes/Model/LayerLayout.lean, reckons with 2^(1 + lbz)). The lift of a cell from the
    field to the integers is the one integer of that size with that residue.
  the conditions modulo the prime: the sub-proofs' claims.

Limits: nothing on a protocol. The reference sizes and exact match alone. indexOf picks by choice
and
cannot be run; by holds_unique the choice is of one. The tables inside the conditions are the
library's. That a table of scales read from a file is lawful is a premise.

-/
import Johnson.Road.Lane5SoundLedger
import Policy.Rel.LedgerRelLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles.Flat

open Inst.Model
open Inst.Model.Layout (kRef hRef)

/-- The field of the cells. -/
abbrev GE : Type := Cb.Gl.E

variable {rows cols : ℕ}

/-- The integer matrix W says the cells of M, and is 0 outside M's shape. -/
def SaysC (M : Fin rows → Fin cols → GE) (W : Mat) : Prop :=
  (∀ y c, M y c = ((W y.val c.val : ℤ) : GE)) ∧ ∀ y c, ¬ (y < rows ∧ c < cols) → W y c = 0

/-- The matrix holds the index. -/
def Holds (M : Fin rows → Fin cols → GE) (i : Cm.Idx) : Prop := SaysC M i.mat

/-- **In range**: the matrix holds an index. -/
def InRange (M : Fin rows → Fin cols → GE) : Prop := ∃ i : Cm.Idx, Holds M i

/-- **The claim of a request on a matrix**: the matrix holds an index at which some trace meets the
relaxed relation with the cost ledger, at the protocol's prime and at exact match. -/
def RelL (s : Cm.Scales) (M : Fin rows → Fin cols → GE) (x : Instance ppref) : Prop :=
  ∃ i : Cm.Idx, Holds M i ∧
    ∃ T, Policy.LedgerRel.Rno Cb.Gl.p (Policy.ppOf s AcceptancePolicy.exact) i x T

theorem RelL.inRange {s : Cm.Scales} {M : Fin rows → Fin cols → GE} {x : Instance ppref}
    (h : RelL s M x) : InRange M := ⟨h.choose, h.choose_spec.1⟩

/-- Two digits with one residue are one. -/
theorem digit_eq {a b : ℤ} (ha : -2 ^ 7 ≤ a ∧ a < 2 ^ 7) (hb : -2 ^ 7 ≤ b ∧ b < 2 ^ 7)
    (h : ((a : ℤ) : GE) = ((b : ℤ) : GE)) : a = b := by
  have h1 : (Cb.Gl.p : ℤ) ∣ b - a := ((CharP.intCast_eq_intCast GE Cb.Gl.p).1 h).dvd
  have hp : (256 : ℤ) < (Cb.Gl.p : ℤ) := by
    have e : Cb.Gl.p = 18446744069414584321 := Code.pGold_eq
    rw [e]
    norm_num
  have h2 : |b - a| < (Cb.Gl.p : ℤ) := by
    refine lt_trans ?_ hp
    rw [abs_lt]
    constructor <;> omega
  have h3 := Int.eq_zero_of_abs_lt_dvd h1 h2
  omega

/-- **A matrix holds at most one index.** -/
theorem holds_unique (hr : rows ≤ hRef) (hc : cols ≤ 2 ^ kRef) {M : Fin rows → Fin cols → GE}
    {i i' : Cm.Idx} (h : Holds M i) (h' : Holds M i') : i = i' := by
  have hm : ∀ y c, i.mat y c = i'.mat y c := by
    intro y c
    by_cases hin : y < rows ∧ c < cols
    · have e : ((i.mat y c : ℤ) : GE) = ((i'.mat y c : ℤ) : GE) :=
        (h.1 ⟨y, hin.1⟩ ⟨c, hin.2⟩).symm.trans (h'.1 ⟨y, hin.1⟩ ⟨c, hin.2⟩)
      exact digit_eq (i.wf.1 y (lt_of_lt_of_le hin.1 hr) c (lt_of_lt_of_le hin.2 hc))
        (i'.wf.1 y (lt_of_lt_of_le hin.1 hr) c (lt_of_lt_of_le hin.2 hc)) e
    · rw [h.2 y c hin, h'.2 y c hin]
  refine Subtype.ext ?_
  funext y c
  have e := hm y.val c.val
  unfold Cm.Idx.mat Cm.ext at e
  rw [dif_pos ⟨y.2, c.2⟩, dif_pos ⟨y.2, c.2⟩] at e
  exact e

open Classical in
/-- The index that the matrix holds, if it holds one. -/
noncomputable def indexOf (M : Fin rows → Fin cols → GE) : Option Cm.Idx :=
  if h : InRange M then some h.choose else none

theorem indexOf_eq (hr : rows ≤ hRef) (hc : cols ≤ 2 ^ kRef) {M : Fin rows → Fin cols → GE}
    {i : Cm.Idx} (h : Holds M i) : indexOf M = some i := by
  have hin : InRange M := ⟨i, h⟩
  unfold indexOf
  rw [dif_pos hin]
  exact congrArg some (holds_unique hr hc hin.choose_spec h)

/-- The integer model's next token at the index that the matrix holds; none if it holds none. -/
noncomputable def nextTok (s : Cm.Scales) (M : Fin rows → Fin cols → GE) (l : List Token) :
    Option Token :=
  (indexOf M).bind fun i => IntegerModel.nextToken s i.index l

/-- **The meaning**: at a lawful table of scales, a built request of which the claim holds at M has
the output tokens that the integer model gives at the index that M holds. -/
theorem sound_core {s : Cm.Scales} (lawful : s.Lawful) (hr : rows ≤ hRef) (hc : cols ≤ 2 ^ kRef)
    {M : Fin rows → Fin cols → GE} {x' : List Token × List Token} {b : List Token}
    {x : Instance ppref} (hb : requestOfTokens x' b = some x) (hR : RelL s M x) :
    ∀ position (h : position < x'.2.length),
      nextTok s M (x'.1 ++ x'.2.take position) = some x'.2[position] := by
  obtain ⟨i, hi, hT⟩ := hR
  intro position h
  unfold nextTok
  rw [indexOf_eq hr hc hi]
  exact OnBytes.Road.L5.sound_ledger_exact lawful i x' b x hb hT position h

/-- **The language of the claim**: at a lawful table of scales it says that the matrix holds an
index
at which the request is true under exact match. -/
theorem relL_iff {s : Cm.Scales} (lawful : s.Lawful) (M : Fin rows → Fin cols → GE)
    (x : Instance ppref) :
    RelL s M x ↔ ∃ i : Cm.Idx, Holds M i ∧ Policy.IsTrueUnder s AcceptancePolicy.exact i x := by
  have L := Policy.ledger_relation_at_protocol_prime s lawful AcceptancePolicy.exact AcceptancePolicy.exact_ok
  constructor
  · rintro ⟨i, hi, T, hT⟩
    exact ⟨i, hi, (L i x).1 T hT⟩
  · rintro ⟨i, hi, ht⟩
    exact ⟨i, hi, _, Policy.ledger_sub _ _ _ _ _ ((L i x).2 ht)⟩

/-! ## Requests that the program's reader takes -/

/-- What the program's reader of a request asks beside the lengths (Model.Head.stFromCall,
OnBytes/Model/HeadLayout.lean): r < e, and y = 0 if e is before the window's end. -/
def WellFormed (x : Instance ppref) : Prop := x.r < x.e ∧ (x.e < ppref.T → x.y.val = 0)

instance (x : Instance ppref) : Decidable (WellFormed x) := by
  unfold WellFormed
  infer_instance

/-- The requests that the reader takes. -/
abbrev Req : Type := {x : Instance ppref // WellFormed x}

/-- The builder into these: requestOfTokens, and none where the reader would refuse. -/
def buildReq (x' : List Token × List Token) (b : List Token) : Option Req :=
  (requestOfTokens x' b).bind fun x => if h : WellFormed x then some ⟨x, h⟩ else none

theorem buildReq_some {x' : List Token × List Token} {b : List Token} {x : Req}
    (h : buildReq x' b = some x) : requestOfTokens x' b = some x.1 := by
  unfold buildReq at h
  cases hq : requestOfTokens x' b with
  | none =>
    rw [hq] at h
    cases h
  | some y =>
    rw [hq] at h
    have h' : (if hw : WellFormed y then some (⟨y, hw⟩ : Req) else none) = some x := h
    split at h'
    · cases h'
      rfl
    · cases h'

end VerifiableInference.OnPublicFiles.Flat

#print axioms VerifiableInference.OnPublicFiles.Flat.relL_iff
#print axioms VerifiableInference.OnPublicFiles.Flat.buildReq_some
#print axioms VerifiableInference.OnPublicFiles.Flat.holds_unique
#print axioms VerifiableInference.OnPublicFiles.Flat.sound_core
