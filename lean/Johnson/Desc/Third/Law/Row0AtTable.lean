-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Row0AtTable.lean: ROW 0 OF THE LAST CHAIN's TABLE OF JOINTS
(Johnson/Desc/Last/BordersLast.lean · Johnson/Desc/Sound/BordersLastQ.lean): THE TWO CONJUNCTS THAT
EachOwn ASKS AT THE CHAIN's FIRST BLOCK ("K14, second part"), AT THE TABLE's OWN LETTERS onQ₃ |
meansQ₃ | insQ₃ | outsQ₃ | startLast, general in N · Mg · ML · Pm · PL · Oc, in the kit of
challenges, in the witness's type and in the type of claims. One structure of Prop, theorems.

OBJECT   (batchLinearConstraintsSecondPart p).decide (Johnson/Desc/Third/K14BatchLinearConstraintsSecondPart.lean), through the piece x that holds
         it: all that is asked of x.b is YesOf (a yes of x.b is a yes of the block at the chain's
         own record): paid by make for the wrap of a description's pieces, with the block as it is
         (make_wrap) and carried to the description's type of claims by Block.retype (make_retype).
USER     eachOwn_of_rows (Johnson/Desc/Sound/QuietRows.lean), its premise h₀: TO THE LETTER the
         conclusion of rowZero: CALLED HERE BY NAME (eachOwn_of_rowZero). The same term is the body
         of RowZeroOwed (Johnson/Flat/Last/LastOnePage.lean), which eachOwn_last | eachOwn_last_arm
         take. From EachOwn the table's owner goes by LastJoinPlain to the last chain's Leads.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean):
         ONE OF FOUR blocks beneath it.
LETTERS  p : P₁₄ (the codes, the shape) · x · lo · the family Ok | words | omW | wv IN WHAT WAS
         HANDED TO THE CHAIN (the public part, the first chain's last record, the shared chain's
         last record) · ρ, a reading into a field.

  RowZeroLeft          **WHAT IS LEFT AT ROW 0**: fifteen things in four lots, each with its payer:
    THE MAKE           wrap · hand · idle: whoever cuts the pieces (make_wrap | make_retype pay the
                       first two; idle is the cut's choice of the extractor: the table's row says
                       "lays nothing").
    WHAT RIDES         ocBelow · lo_le · tree · omegaBelow · pins: conditions on the meanings'
                       letters and three tests on the plan's numbers: the four premises of the
                       table's own step of the promise (LastPromOf, LastProm.lean) and row 1's
                       PinsReadBelow (QuietRows.lean) at this piece's base: one payer for all rows:
                       whoever fills Mg | Pm | Oc.
    THE BOOK-KEEPING   atDot · fence · shape: what PL.shape 0 (with Oc) and the block's own yes must
                       give at the record in front, and that PL.shape 1 follows: whoever fills
                       PL.shape.
    THE MEANINGS       reads · rows · ev · dot: the words that the witness gives, through the
                       record: "rows" behind gives RowsHold; RowsHold in front gives the table's
                       ev; the semantic (Dot) in front gives the table's dot: whoever fills ML.rows,
                       Mg.ev, Mg.dot. NOTE: ev IS NO BOOK-KEEPING STEP: for (Dot) these files carry
                       "the row says" to an equation on readers (DotSem); for (Eval) they hand over
                       RowsHold raw: the law on what the row (Eval) says of W's words, and that it
                       is the row made off the claim, hides in ev or shifts to whoever spends Mg.ev.
  rowZero              **the row**: RowZeroLeft gives both conjuncts. The promise behind: by
                       lastPromOf: CALLED. The own law: by row0_own. The three pins ride by
                       out_behind | cellStays | colStays: CALLED.
  eachOwn_of_rowZero   THE CALL.
  make_wrap · make_retype   the first two fields, by make.
What is not claimed. NO MEMBER OF RowZeroLeft IS SHOWN. A closed family at which reads, fence, atDot
and dot are had together: Johnson/Desc/Third/Law/Row0AtWords.lean; ev at a filling: Row0Ev.lean;
the book-keeping at the filling fillZ: Row0AtFillZ.lean. A piece that refuses all has
both conjuncts. Nothing is said on rows 1 to 3. No soundness of a verifier; nothing on hiding.

-/
import Johnson.Desc.Sound.LastProm
import Johnson.Desc.Sound.QuietRows
import Johnson.Desc.Third.Law.Row0Frames

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Third.Law
open OnBytes OnBytes.Params
open OnBytes.Means (Words)
open OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open _root_.Run.PQ (CK)

variable {P S₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame} {K : Type} [Field K] (ρ : Model.Reading K)
  (N : NumbersS) (Mg : MeaningS S₂ (P × S₁) Wt) (ML : MeaningL S₃ Wt) (Pm : PromMeaning S₂)
  (PL : PromMeaningL S₂ S₃ (P × S₁)) (Oc : P × S₁ → Strs → Prop)

/-- **WHAT IS LEFT AT ROW 0** (K14's second part), of the piece x that stands there. Cl₀: the type
of claims at which the block is named (its decision reads none). -/
structure RowZeroLeft (Cl₀ : Type) (p : P₁₄) (x : Piece C Fr ((P × S₁ × S₂) × S₃) Cl Wt) (lo : ℕ)
    (Ok : P × S₁ × S₂ → S₃ → S₃ → Prop) (words : P × S₁ × S₂ → S₃ → Wt → Words K)
    (omW wv : P × S₁ × S₂ → Wt → Nat → K) : Prop where
  /-- a yes of the piece's block is a yes of the block at the chain's own record -/
  wrap : YesOf (fun t : (P × S₁ × S₂) × S₃ => t.2) (batchLinearConstraintsSecondPart p : Block S₃ Cl₀) x.b
  /-- a yes leaves what was handed to the chain -/
  hand : ∀ a τ b, x.ior.red.out a τ = some b → b.1.1 = a.1.1
  /-- its extractor is the identity -/
  idle : ∀ a τ w, x.ext a τ w = w
  /-- the slot's own condition reads the stored table and the trees below lo alone -/
  ocBelow : OcReadsBelow lo Oc
  lo_le : lo ≤ x.base
  /-- the promise on a message and its pin read its tree alone -/
  tree : ReadsTree Mg Pm
  /-- Omega's tree lies below the piece's base -/
  omegaBelow : (N.tenant .oOmega).1 < x.base
  /-- the three pins read below its base -/
  pins : PinsReadBelow (S₃ := S₃) N Mg ML x.base
  /-- the promise in front and the block's own yes give the premises of the (Dot) joint, and that
  the own group's open rows name messages of the statement alone -/
  atDot : ∀ (a : ((P × S₁ × S₂) × S₃) × Fr.E.Str) (s' : S₃), onQ₃ N Mg Pm PL Oc 0 a →
    (∃ rs gs, (batchLinearConstraintsSecondPart p : Block S₃ Cl₀).decide a.1.2 rs gs = .ok s') →
    AtDot p a.1.2 ∧ Names a.1.2
  /-- the promise in front and the block's own yes give the fence of the two records, AT WHAT WAS
  HANDED -/
  fence : ∀ (a : ((P × S₁ × S₂) × S₃) × Fr.E.Str) (s' : S₃), onQ₃ N Mg Pm PL Oc 0 a →
    (∃ rs gs, (batchLinearConstraintsSecondPart p : Block S₃ Cl₀).decide a.1.2 rs gs = .ok s') → Says p a.1.2 s' →
    Ok a.1.1 a.1.2 s'
  /-- the book-keeping behind the block follows from the promise in front and the block's own yes -/
  shape : ∀ (a : ((P × S₁ × S₂) × S₃) × Fr.E.Str) (s' : S₃), onQ₃ N Mg Pm PL Oc 0 a →
    (∃ rs gs, (batchLinearConstraintsSecondPart p : Block S₃ Cl₀).decide a.1.2 rs gs = .ok s') → Says p a.1.2 s' →
    PL.shape 1 (a.1.1.1, a.1.1.2.1) a.1.1.2.2 s' = true
  /-- inside the fence the words are read aright, at every handed part -/
  reads : ∀ u, Reads p (Ok u) (words u) (omW u) (wv u)
  /-- inside the promise behind, the table's "rows" gives: all open rows of the own group hold of
  the words read through the record behind -/
  rows : ∀ (b : ((P × S₁ × S₂) × S₃) × Fr.E.Str) w, onQ₃ N Mg Pm PL Oc 1 b → ML.rows b.1.2 w →
    RowsHold ρ b.1.2 (words b.1.1 b.1.2 w)
  /-- inside the promise in front, the own group's open rows give the table's (Eval) -/
  ev : ∀ (a : ((P × S₁ × S₂) × S₃) × Fr.E.Str) w, onQ₃ N Mg Pm PL Oc 0 a →
    RowsHold ρ a.1.2 (words a.1.1 a.1.2 w) → Mg.ev (a.1.1.1, a.1.1.2.1) (strsOf Fr a.2) w
  /-- inside the promise in front, the semantic (Dot) gives the table's (Dot) -/
  dot : ∀ (a : ((P × S₁ × S₂) × S₃) × Fr.E.Str) w, onQ₃ N Mg Pm PL Oc 0 a →
    DotSem ρ p (omW a.1.1) (wv a.1.1) a.1.2 w →
    Mg.dot (a.1.1.1, a.1.1.2.1) a.1.1.2.2 (strsOf Fr a.2) w

variable {ρ N Mg ML Pm PL Oc}

/-- **ROW 0's TWO CONJUNCTS OF EachOwn.** -/
theorem rowZero {Cl₀ : Type} {p : P₁₄} {x : Piece C Fr ((P × S₁ × S₂) × S₃) Cl Wt} {lo : ℕ}
    {Ok : P × S₁ × S₂ → S₃ → S₃ → Prop} {words : P × S₁ × S₂ → S₃ → Wt → Words K}
    {omW wv : P × S₁ × S₂ → Wt → Nat → K}
    (h : RowZeroLeft ρ N Mg ML Pm PL Oc Cl₀ p x lo Ok words omW wv) :
    x.Own (onQ₃ N Mg Pm PL Oc 0) (onQ₃ N Mg Pm PL Oc 1) (meansQ₃ N Mg ML) (insQ₃ 0) (outsQ₃ 0) ∧
      x.Frames (onQ₃ N Mg Pm PL Oc 0) (onQ₃ N Mg Pm PL Oc 1) (meansQ₃ N Mg ML)
        (openAfter insQ₃ outsQ₃ (· ∈ startLast) 0) (insQ₃ 0) := by
  have eI : insL₃ 0 = [.ev, .dot] := by decide
  have eO : outsL₃ 0 = [.rows] := by decide
  refine ⟨row0_own ρ p (fun t : (P × S₁ × S₂) × S₃ => t.2) (fun t => t.1) x h.wrap h.idle
    Ok words omW wv h.reads _ _ (fun a τ b _ ho => h.hand a τ b ho) _ _ _
    (fun a _ b ha _ hy hs => h.fence a b.1.2 ha hy hs) h.atDot
    (fun a τ b ha hout hy hs => ?_) (fun b w hb hw => ?_) (fun a w ha hr hd i hi => ?_), ?_⟩
  · refine lastPromOf P S₁ S₂ S₃ Cl Wt C Fr N Mg Pm PL Oc lo x h.ocBelow h.lo_le h.tree h.omegaBelow
      h.hand 0 a τ b ha hout ?_ (fun hl => absurd hl (by decide))
    rw [h.hand a τ b hout]
    exact h.shape a b.1.2 ha hy hs
  · refine h.rows b w hb (hw .rows ?_)
    show ItemL.rows ∈ outsL₃ 0
    rw [eO]
    exact List.mem_singleton.2 rfl
  · have hi' : i ∈ insL₃ 0 := hi
    rw [eI] at hi'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
    rcases hi' with rfl | rfl
    · exact h.ev a w ha hr
    · exact h.dot a w ha hd
  · intro a τ b w i ha hout _ hO hI hm
    rw [h.idle]
    have e1 := h.hand a τ b hout
    have e2 := out_behind x a b τ hout
    have hc : ∀ z, (strsOf Fr b.2).cell z = (strsOf Fr a.2).cell z := by
      rw [e2]
      exact fun z => cellStays C Fr x.base x.ds a.2 τ z
    have hl : ∀ j z, j < x.base → (strsOf Fr b.2).col j z = (strsOf Fr a.2).col j z := by
      rw [e2]
      exact fun j z hj => colStays C Fr x.base x.ds a.2 τ j z hj
    have hm' : i.holds N Mg ML (a.1.1.1, a.1.1.2.1) a.1.1.2.2 b.1.2 (strsOf Fr b.2) w := by
      rw [← e1]
      exact hm
    have hO' : i ∈ startLast := hO
    have hI' : ¬ i ∈ insL₃ 0 := hI
    rw [eI] at hI'
    simp only [startLast, List.mem_cons, List.not_mem_nil, or_false] at hO' hI'
    rcases hO' with rfl | rfl | rfl | rfl | rfl
    · exact h.pins .pinI (Or.inl rfl) _ _ a.1.2 _ _ w hc hl hm'
    · exact h.pins .pinV (Or.inr (Or.inl rfl)) _ _ a.1.2 _ _ w hc hl hm'
    · exact absurd (Or.inl rfl) hI'
    · exact absurd (Or.inr rfl) hI'
    · exact h.pins .pinO (Or.inr (Or.inr rfl)) _ _ a.1.2 _ _ w hc hl hm'

/-- **THE CALL**: EachOwn at the table, of its four rows, with row 0 from what is left of it. -/
theorem eachOwn_of_rowZero {Cl₀ : Type} {p : P₁₄} {lo : ℕ}
    {Ok : P × S₁ × S₂ → S₃ → S₃ → Prop} {words : P × S₁ × S₂ → S₃ → Wt → Words K}
    {omW wv : P × S₁ × S₂ → Wt → Nat → K}
    (x₀ x₁ x₂ x₃ : Piece C Fr ((P × S₁ × S₂) × S₃) Cl Wt)
    (h₀ : RowZeroLeft ρ N Mg ML Pm PL Oc Cl₀ p x₀ lo Ok words omW wv)
    (h₁ : RowOneOwed N Mg ML Pm PL Oc x₁)
    (h₂ : x₂.Own (onQ₃ N Mg Pm PL Oc 2) (onQ₃ N Mg Pm PL Oc 3) (meansQ₃ N Mg ML) (insQ₃ 2)
        (outsQ₃ 2) ∧
      x₂.Frames (onQ₃ N Mg Pm PL Oc 2) (onQ₃ N Mg Pm PL Oc 3) (meansQ₃ N Mg ML)
        (openAfter insQ₃ outsQ₃ (· ∈ startLast) 2) (insQ₃ 2))
    (h₃ : RowThreeOwed N Mg Pm PL Oc x₃) :
    EachOwn (onQ₃ N Mg Pm PL Oc) (meansQ₃ N Mg ML) insQ₃ outsQ₃ (· ∈ startLast) 0
      [x₀, x₁, x₂, x₃] :=
  eachOwn_of_rows N Mg ML Pm PL Oc x₀ x₁ x₂ x₃ (rowZero h₀) h₁ h₂ h₃

/-- The first two fields by make, at the wrap in which a description's pieces hold blocks. -/
theorem make_wrap (p : P₁₄) (x : Piece C Fr ((P × S₁ × S₂) × S₃) Cl Wt)
    (hb : x.b = Block.lift Prod.snd (fun t s => (t.1, s)) (below (batchLinearConstraintsSecondPart p))) :
    YesOf (fun t : (P × S₁ × S₂) × S₃ => t.2) (batchLinearConstraintsSecondPart p : Block S₃ Cl) x.b ∧
      ∀ a τ b, x.ior.red.out a τ = some b → b.1.1 = a.1.1 :=
  ⟨by rw [hb]; exact yesOf_wrap _, fun a τ b h => out_fst x _ hb a b τ h⟩

/-- The same where the block is carried to the description's type of claims. -/
theorem make_retype {Cl₀ : Type} (p : P₁₄) (x : Piece C Fr ((P × S₁ × S₂) × S₃) Cl Wt)
    (hb : x.b = Block.lift Prod.snd (fun t s => (t.1, s))
      (below ((batchLinearConstraintsSecondPart p : Block S₃ Cl₀).retype (Cl' := Cl)))) :
    YesOf (fun t : (P × S₁ × S₂) × S₃ => t.2) (batchLinearConstraintsSecondPart p : Block S₃ Cl₀) x.b ∧
      ∀ a τ b, x.ior.red.out a τ = some b → b.1.1 = a.1.1 :=
  ⟨by rw [hb]; exact yesOf_wrap_retype _, fun a τ b h => out_fst x _ hb a b τ h⟩

end VerifiableInference.Desc.Third.Law
