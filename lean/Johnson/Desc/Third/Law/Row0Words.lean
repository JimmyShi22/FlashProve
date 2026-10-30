-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Row0Words.lean: the last chain's first block ("K14, second part") in the form
of the rule of composition (Johnson/Desc/Third/Law/Row0.lean), WHERE THE WORDS ARE READ OFF THE
WITNESS THROUGH THE RECORD: words : record → witness → words: a message's number in a statement goes
to a component of the witness by the record's book, so the record behind and the record in front
may read differently. BEHIND: all open rows of the own group hold of the words read through the
record behind. IN FRONT: all open rows of the own group hold of the
words read through the record in front, AND THE SEMANTIC (Dot): its equation at two readers of the
witness, omW for Omega and wv for W, which name no record. Theorems.

  value_congr · says_congr   what a row says of words hangs on the words of the statement's messages
                       alone.
  RowsThere ρ s m      the own group is there, has an open row, and all its open rows hold of m.
  rowsHold_of_there    it gives RowsHold. (row0_backW spends RowsHold alone: behind the block's yes
                       the group is there, with (Dot) as its last open row, by Says.)
  Reads p Ok words omW wv   WHAT IS ASKED OF words, at a yes of the block from s to s', INSIDE A
                       FENCE Ok s s' (a letter: the book-keeping of the two records: Says reads
                       neither record's book, so without a fence no words that truly reads a book
                       could meet it): an older message's words are the same through both records;
                       Omega's words through the record behind, at Omega's layout, are omW's, BELOW
                       THE NUMBER OF MATRIX ROWS; W's, at W's layout, are wv's, BELOW 2 ^ kCol: as
                       far as (Dot)'s two sums run.
  dotEq_congr          (Dot)'s equation hangs on its two vectors below these bounds alone.
  DotSem ρ p s w       the semantic (Dot): at the weights and the point of the two ends at hand.
  row0_backW           **behind a yes.**
  row0_goodInW         the row, at the chain's own record.
OBJECT   (batchLinearConstraintsSecondPart p).decide, through law_k14Second.
USER     row0_backW: row0_own (Johnson/Desc/Third/Law/Row0Own.lean), so rowZero. Reads: the field
         reads of RowZeroLeft. row0_goodInW IS A FORERUNNER: nobody calls it.
LETTERS  ρ · Ok · words · omW · wv: at a table they are families in what was handed to the chain.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean), through row 0.
What is not claimed. THAT A words WITH Reads IS THERE, AT A FENCE THAT A REAL RUN MEETS: here both
are letters (a closed family: Johnson/Desc/Third/Law/Row0AtWords.lean). All that
Johnson/Desc/Third/Law/Row0.lean does not claim.

-/
import Johnson.Desc.Third.Law.Row0

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Third.Law
open OnBytes OnBytes.Params
open OnBytes.Means (Words)
open VerifiableInference.Desc.Sound (Frame Piece goodIn_of_sure)
open _root_.Desc.K14.Law (DotEq)
open _root_.Run.PQ (CK)

variable {K : Type} [Field K] (ρ : Model.Reading K)

/-- What a row sums to hangs on the words of the statement's messages alone. -/
theorem value_congr (T : Statement) (r : OnBytes.Row) (m m' : Words K)
    (h : ∀ o < T.oracles.size, ∀ part i, m o part i = m' o part i) :
    Means.value ρ T r m = Means.value ρ T r m' := by
  unfold Means.value Means.onTable
  refine Finset.sum_congr rfl fun o ho => ?_
  have ho' := Finset.mem_range.1 ho
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by rw [h o ho']

/-- So does what it says. -/
theorem says_congr (T : Statement) (r : OnBytes.Row) (m m' : Words K)
    (h : ∀ o < T.oracles.size, ∀ part i, m o part i = m' o part i) :
    Means.Says ρ T r m ↔ Means.Says ρ T r m' := by
  unfold Means.Says
  rw [value_congr ρ T r m m' h]

/-- The own group is there, has an open row, and all its open rows hold of the words. -/
def RowsThere (s : S₃) (m : Words K) : Prop :=
  ∃ G, s.st.groups[s.loc.own]? = some G ∧ G.rows.toList ≠ [] ∧
    Means.AllSay ρ s.st G.rows.toList m

/-- It gives RowsHold. -/
theorem rowsHold_of_there (s : S₃) (m : Words K) (h : RowsThere ρ s m) : RowsHold ρ s m := by
  obtain ⟨G, hG, _, hs⟩ := h
  intro G' hG'
  obtain rfl : G = G' := Option.some.inj (hG.symm.trans hG')
  exact hs

variable {W : Type}

/-- **What is asked of the reading of words through a record**, inside the fence Ok. -/
structure Reads (p : P₁₄) (Ok : S₃ → S₃ → Prop) (words : S₃ → W → Words K)
    (omW wv : W → Nat → K) : Prop where
  older : ∀ s s' w, Ok s s' → Says p s s' → ∀ o < s.st.oracles.size, ∀ part i,
    words s' w o part i = words s w o part i
  omega : ∀ s s' w, Ok s s' → Says p s s' → ∀ y < p.S.matrixRows,
    words s' w s.st.oracles.size .main ((linLayOmega s.st.codes p.S).index y) = omW w y
  w : ∀ s s' w, Ok s s' → Says p s s' → ∀ c < 2 ^ p.S.kCol,
    words s' w s.loc.w .main ((linLayW s.st.codes p.S).index c) = wv w c

/-- (Dot)'s equation hangs on its two vectors below the bounds of its sums alone. -/
theorem dotEq_congr (R k : Nat) (g om om' : Nat → K) (psi : List K) (V V' : Nat → K)
    (h1 : ∀ y < R, om y = om' y) (h2 : ∀ c < 2 ^ k, V c = V' c) (h : DotEq R k g om psi V) :
    DotEq R k g om' psi V' := by
  unfold DotEq at h ⊢
  have e1 : ∑ y ∈ Finset.range R, g y * om' y = ∑ y ∈ Finset.range R, g y * om y :=
    Finset.sum_congr rfl fun y hy => by rw [h1 y (Finset.mem_range.1 hy)]
  have e2 : ∑ c ∈ Finset.range (2 ^ k), _root_.Desc.K14.Law.eqK psi c * V' c =
      ∑ c ∈ Finset.range (2 ^ k), _root_.Desc.K14.Law.eqK psi c * V c :=
    Finset.sum_congr rfl fun c hc => by rw [h2 c (Finset.mem_range.1 hc)]
  rw [e1, e2]
  exact h

/-- The semantic (Dot), at the weights and the point of the two ends at hand. -/
def DotSem (p : P₁₄) (omW wv : W → Nat → K) (s : S₃) (w : W) : Prop :=
  ∃ b, s.loc.border = some b ∧
    DotEq p.S.matrixRows p.S.kCol (fun y => (b.g.map fun g => ρ.val (g.entry y)).sum) (omW w)
      (b.shared.psi.map ρ.val) (wv w)

/-- **Behind a yes.** -/
theorem row0_backW (p : P₁₄) (Ok : S₃ → S₃ → Prop) (words : S₃ → W → Words K)
    (omW wv : W → Nat → K) (hR : Reads p Ok words omW wv) (s s' : S₃) (ok : Ok s s')
    (h : Says p s s')
    (hk : Later.Carries s.st s'.st) (a : AtDot p s) (n : Names s) (w : W)
    (hs : RowsHold ρ s' (words s' w)) :
    RowsHold ρ s (words s w) ∧ DotSem ρ p omW wv s w := by
  obtain ⟨r1, b, hb, hd⟩ := row0_back ρ p s s' h hk a n (words s' w) hs
  refine ⟨fun G hG r hr => ?_, b, hb, ?_⟩
  · exact (says_congr ρ s.st r _ _ (hR.older s s' w ok h)).1 (r1 G hG r hr)
  · exact dotEq_congr _ _ _ _ _ _ _ _ (hR.omega s s' w ok h) (hR.w s s' w ok h) hd

variable {Cl : Type} {C : CK} {F : Frame}

/-- **The row, with the words read through the record.** -/
theorem row0_goodInW (p : P₁₄) (pc : Piece C F S₃ Cl W) (hb : pc.b = batchLinearConstraintsSecondPart p)
    (hext : ∀ a τ w, pc.ext a τ w = w) (Ok : S₃ → S₃ → Prop) (words : S₃ → W → Words K)
    (omW wv : W → Nat → K) (hR : Reads p Ok words omW wv) (Prm : S₃ × F.E.Str → Prop)
    (hOk : ∀ a τ b, Prm a → pc.ior.red.out a τ = some b → Says p a.1 b.1 → Ok a.1 b.1)
    (hkeep : ∀ a τ b, AtDot p a.1 → Names a.1 → pc.ior.red.out a τ = some b → Prm a → Prm b)
    (Rc : S₃ × F.E.Str → W → Prop)
    (hback : ∀ a τ b w, AtDot p a.1 → Names a.1 → Prm a → pc.ior.red.out a τ = some b → Rc b w →
      Rc a w) :
    pc.GoodIn (fun a => AtDot p a.1 ∧ Names a.1 ∧ Prm a)
      (fun b => (∃ s, AtDot p s ∧ Says p s b.1) ∧ Prm b)
      (fun a w => RowsHold ρ a.1 (words a.1 w) ∧ DotSem ρ p omW wv a.1 w ∧ Rc a w)
      (fun b w => RowsThere ρ b.1 (words b.1 w) ∧ Rc b w) := by
  refine goodIn_of_sure pc _ _ _ _ fun a τ b ha hout => ?_
  obtain ⟨_, rs, gs, hd⟩ := pc.out_of_decide a τ b hout
  rw [hb] at hd
  have hk := (law_k14Second (Cl := Cl) p).1 _ _ _ _ hd
  have hs := (law_k14Second (Cl := Cl) p).2 _ _ _ _ hd
  refine ⟨⟨⟨a.1, ha.1, hs⟩, hkeep a τ b ha.1 ha.2.1 hout ha.2.2⟩, fun w hw => ?_⟩
  rw [hext]
  obtain ⟨r1, r2⟩ := row0_backW ρ p Ok words omW wv hR a.1 b.1 (hOk a τ b ha.2.2 hout hs) hs hk
    ha.1 ha.2.1 w (rowsHold_of_there ρ _ _ hw.1)
  exact ⟨r1, r2, hback a τ b w ha.1 ha.2.1 ha.2.2 hout hw.2⟩

end VerifiableInference.Desc.Third.Law
