-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/LinkSoundRec.lean: round-by-round soundness of the written link RECORD BY RECORD, with
no bound of half the distance on the decoder's radius, from hypotheses on the tables' code and one
hypothesis on the rounds after the fifth.




Beyond half the code's
distance a table has a list of tables of code words near it, and the format stores with it each
row's answers to a sample. A record here is a seed with such answers. This file has the theorem for
each pair of records r, one for the first table and one for the copy. The language (`Sz.LangR`) has
a way out for each table: the record does not single one table out of that table's list (a collision
at the record's seed). Else both tables decode, each with its own record, to tables that agree
before the cut. It is the language `DecR.LangE2` at `wayColl` (OnBytes/Slice/JoinDecRec2.lean) less
its first clause, on tables in the place of raw strings; `Sz.LangE2T` has all four clauses
(`Sz.langE2T_iff`), and `link_sound_recE2` is the theorem for it. The decision may depend on the
records; the error counts do not (for those of the rounds after the fifth that is asked).

How. The library's link (Cb/Ld/LdLink.lean) has a pair of records as its instance. Its first joint's
relaxed relation, enlarged by the statements outside its conditions, says: both decode and agree on
the layout, or a condition fails. With the two conditions "no collision at the record's seed" that
is the language, by logic. For these conditions the library counts the bad fold points from eM < d,
e0 ≤ eM, e1 ≤ eM, a count of exceptional fold points and a bound on lists at each of the two radii
(`ldLk_foldErr_rec`). Further hypotheses: (a) and (b) of OnBytes/Slice/LinkSound.lean's head.

Main definitions: `Sz.onR`, `Sz.LangR`, `Sz.LangE2T`, `ClosesR`.
Main theorems: `langR_of_first`, `foldErr_atR`, `link_sound_at`, `link_sound_rec`,
`link_sound_recE2`;
`Sz.langE2T_iff` (the language on raw strings).


Not claimed. All that OnBytes/Slice/LinkSound.lean does not claim. THAT THE HYPOTHESIS ON THE ROUNDS
AFTER THE FIFTH (`ClosesR`) HOLDS OF ANY DECISION AT A SAMPLE WITH AN ANSWER: with a record the last
joint's relation asks the record's row of each fold, of the first table's too
(OnBytes/Slice/BatSemRec.lean has them in the field; no decision is shown to test them). THAT AN
ENTRY FILE'S CHAIN WITH A RECORD BEGINS WITH THESE FIVE ROUNDS: by the format's own Lean text
(Fmt/M3Plan.lean, "What is not claimed") its plan has a further first entry, and answers stand in
the statement; `written` has neither. That the counts of exceptional fold points and the lists are
small, at any radius: they are letters. With large counts the statement is true for free. How often
a collision occurs. Where a record's seed comes from: r is any pair, and AT A SEED WITH A COLLISION
THE THEOREM SAYS NOTHING, so against a prover that may choose a seed it says nothing wherever some
seed has a collision. Z is any sample map: at `Sample.nil`, beyond half the distance, every table
with two tables of code words near it that differ in their messages is in the language. That one
string has one record: at two records one string may decode to two tables. That the argument cut is
the format's `S.P.cut` (l - 3 s): a hypothesis. Nothing ties Z's number of answers to the format's
s. That a setting's radii meet e0 ≤ eM.
Nothing on files, on a hash
function or on a program.

-/
import OnBytes.Slice.CorePeelRec
import OnBytes.Slice.LinkAtRec
import OnBytes.Slice.DecoderRecTyped
import OnBytes.Slice.LinkSound

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run Blocks

namespace Sz
variable (S : Sz) (Z : Sample GE S.En)

/-- The condition on a table: at its record's seed no two tables of code words near it with
different message parts have the same answers. -/
def onR : ((S.lkR Z).D.X.Row → S.Pos → GE) → (S.lkR Z).D.X.Rec → Prop :=
  fun f r => ¬ (S.lkR Z).D.X.Coll f r.1

/-- **The language of the link, at a pair of records**: the first table's record does not single one
table out, or the copy's does not, or both tables decode, each with its own record, to tables that
agree before the cut. -/
def LangR (cut : ℕ) (r : (S.lkR Z).X0) (y : (S.Pos → Run.PQ.SgX) × (S.Pos → Run.PQ.SgX)) : Prop :=
  (S.toDecR Z cut).coll y.1 r.1.1 ∨ (S.toDecR Z cut).coll y.2 r.2.1 ∨
    ∃ u₀ u₁, (S.toDecR Z cut).dcd y.1 r.1 = some u₀ ∧ (S.toDecR Z cut).dcd y.2 r.2 = some u₁ ∧
      (S.toDecR Z cut).Agree u₁ u₀

/-- The language with the further way out "the first table does not decode with its record": the
four clauses of `DecR.LangE2` at `wayColl`, on tables, in the order of `DecR.lgE_iff`
(OnBytes/Slice/DecoderRecTyped.lean). -/
def LangE2T (cut : ℕ) (r : (S.lkR Z).X0) (y : (S.Pos → Run.PQ.SgX) × (S.Pos → Run.PQ.SgX)) :
    Prop :=
  (S.toDecR Z cut).dcd y.1 r.1 = none ∨ S.LangR Z cut r y

/-- **The language with four clauses is `DecR.LangE2` at `wayColl`**, at the raw forms of the two
tables. -/
theorem langE2T_iff (cut : ℕ) (r : (S.lkR Z).X0)
    (y : (S.Pos → Run.PQ.SgX) × (S.Pos → Run.PQ.SgX)) :
    S.LangE2T Z cut r y ↔
      DecR.LangE2 (DecR.wayColl (S.toDecR Z cut)) r.1 r.2 (rawOf (Equiv.refl _) y.1)
        (rawOf (Equiv.refl _) y.2) := by
  unfold DecR.LangE2 DecR.wayColl
  rw [(S.toDecR Z cut).collRaw_rawOf (Equiv.refl _) rfl y.1,
    (S.toDecR Z cut).collRaw_rawOf (Equiv.refl _) rfl y.2,
    (S.toDecR Z cut).dcdRaw_rawOf (Equiv.refl _) rfl y.1,
    (S.toDecR Z cut).dcdRaw_rawOf (Equiv.refl _) rfl y.2]
  exact Iff.rfl

end Sz

/-- **The first joint's relaxed relation gives the language.** No bound on the radius is asked, and
nothing of the record. -/
theorem langR_of_first (S : Sz) (Z : Sample GE S.En) (cut : ℕ) (hcut : S.P.cut = cut)
    (r : (S.lkR Z).X0) (y : (S.lkR Z).E0.Str)
    (h : ∃ w, ((S.lkR Z).j0 (S.onR Z) (S.onR Z)).cf.relR (r, y) w) : S.LangR Z cut r y := by
  obtain ⟨w, hw | hoff⟩ := h
  · obtain ⟨U₀, U₁, h0, h1, hsame⟩ := hw
    refine Or.inr (Or.inr ⟨U₀, U₁, h0, h1, fun n j hj => ?_⟩)
    exact (hsame n ⟨j.val, hcut ▸ hj⟩).symm
  · by_cases h0 : (S.toDecR Z cut).coll y.1 r.1.1
    · exact Or.inl h0
    · by_cases h1 : (S.toDecR Z cut).coll y.2 r.2.1
      · exact Or.inr (Or.inl h1)
      · exact absurd ⟨h0, h1⟩ hoff

/-- **The bad fold points**, from the library's count for the pairing "neither table has a collision
at its record's seed". -/
theorem foldErr_atR (S : Sz) (Z : Sample GE S.En) (d bad₀ L₀ bad₁ L₁ : ℕ)
    (hdist : HasDist (S.ixR Z).G d) (hM : S.eM < d) (h0 : S.e0 ≤ S.eM) (h1 : S.e1 ≤ S.eM)
    (hm0 : (S.ixR Z).MCAeq S.e0 bad₀)
    (hl0 : ∀ f : (S.ixR Z).Row → S.Pos → GE, ListLE (DecodesTo (S.ixR Z).G S.e0 f) L₀)
    (hm1 : (S.ixR Z).MCAeq S.e1 bad₁)
    (hl1 : ∀ f : (S.ixR Z).Row → S.Pos → GE, ListLE (DecodesTo (S.ixR Z).G S.e1 f) L₁) :
    (S.lkR Z).FoldErr (S.onR Z) (S.onR Z)
      (bad₀ + L₀ * (S.P.v * Fintype.card GE ^ (S.P.v - 1)))
      (bad₁ + L₁ * (S.P.v * Fintype.card GE ^ (S.P.v - 1))) :=
  ldLk_foldErr_rec (S.lkR Z) d bad₀ L₀ bad₁ L₁ hdist hM h0 h1 hm0 hl0 hm1 hl1

section
variable (S : Sz) (Z : Sample GE S.En) (r : (S.lkR Z).X0) (d1 d2 d3 d4 d5 : PQ.RD)
  (tl : List PQ.RD) (xs : List PQ.XO) (dec : PQ.View → Bool)

/-- **The hypothesis on the rounds after the fifth, at the pair of records r.** After every
transcript of the five rounds, if the statement that the library's verifier holds then (`st4R`) has
no witness in the last joint's relaxed relation (enlarged by the statements outside its condition),
the prover has lost in the rounds that follow. -/
def ClosesR (εt : Err (PQ.uL (ckP .two) tl)) : Prop :=
  ∀ (y : (S.lkR Z).E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5,
    (∀ w, ¬ (S.lkR Z).j4.cf.relR (st4R S Z r d1 d2 d3 d4 d5 y c1 m2 c2 m3 c4 c5) w) →
    Doomed (PQ.uL (ckP .two) tl) εt fun b =>
      (written S d1 d2 d3 d4 d5 tl xs dec).accept () y
        (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, b) = false

/-- The written link at one pair of records. -/
theorem link_sound_at (cut d bad₀ L₀ bad₁ L₁ : ℕ) (L : Bool → ℕ) (hcut : S.P.cut = cut)
    (hdist : HasDist (S.ixR Z).G d) (hM : S.eM < d) (h0 : S.e0 ≤ S.eM) (h1 : S.e1 ≤ S.eM)
    (hm0 : (S.ixR Z).MCAeq S.e0 bad₀)
    (hl0 : ∀ f : (S.ixR Z).Row → S.Pos → GE, ListLE (DecodesTo (S.ixR Z).G S.e0 f) L₀)
    (hm1 : (S.ixR Z).MCAeq S.e1 bad₁)
    (hl1 : ∀ f : (S.ixR Z).Row → S.Pos → GE, ListLE (DecodesTo (S.ixR Z).G S.e1 f) L₁)
    (hpl : Function.Injective (S.lkR Z).D.pl) (hlist : ∀ a, ((S.lkR Z).N.om a).ListLE (L a))
    (hev : ∀ a, ((S.lkR Z).N.om a).Evades) (hd : DrawsOK S d1 d2 d3 d4 d5)
    (εt : Err (PQ.uL (ckP .two) tl)) (hc : ClosesR S Z r d1 d2 d3 d4 d5 tl xs dec εt) :
    (written S d1 d2 d3 d4 d5 tl xs dec).Sound (fun _ y => S.LangR Z cut r y)
      (0, coreErrR S Z d1 d2 d3 d4 d5 (bad₀ + L₀ * (S.P.v * Fintype.card GE ^ (S.P.v - 1)))
        (bad₁ + L₁ * (S.P.v * Fintype.card GE ^ (S.P.v - 1))) L εt) := by
  intro x y hy
  refine doomed_cons_all _ _ fun m0 c0 => ?_
  have hpass : ∀ τ, PQ.passSL (ckP .two) (d1 :: d2 :: d3 :: d4 :: d5 :: tl)
      (PQ.rhoSL (ckP .two) (d1 :: d2 :: d3 :: d4 :: d5 :: tl) τ) = false →
      (written S d1 d2 d3 d4 d5 tl xs dec).accept x y (m0, c0, τ) = false := by
    intro τ hτ
    show (PQ.passSL _ _ _ && _ && _ && _) = false
    rw [hτ]
    rfl
  refine core_peelR S Z r d1 d2 d3 d4 d5 (S.onR Z) (S.onR Z) _ _ L
    (foldErr_atR S Z d bad₀ L₀ bad₁ L₁ hdist hM h0 h1 hm0 hl0 hm1 hl1) hpl hlist hev hd _ εt y
    (fun w hw => hy (langR_of_first S Z cut hcut r y ⟨w, hw⟩)) _ ?_ ?_ ?_ ?_ ?_
    (fun m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 h => hc y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 h)
  · intro m1 c1 τ h
    exact hpass _ (by simp only [PQ.passSL, PQ.rhoSL, h, Bool.false_and])
  · intro m1 c1 m2 c2 τ h
    exact hpass _ (by simp only [PQ.passSL, PQ.rhoSL, h, Bool.false_and, Bool.and_false])
  · intro m1 c1 m2 c2 m3 c3 τ h
    exact hpass _ (by simp only [PQ.passSL, PQ.rhoSL, h, Bool.false_and, Bool.and_false])
  · intro m1 c1 m2 c2 m3 c3 m4 c4 τ h
    exact hpass _ (by simp only [PQ.passSL, PQ.rhoSL, h, Bool.false_and, Bool.and_false])
  · intro m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 τ h
    exact hpass _ (by simp only [PQ.passSL, PQ.rhoSL, h, Bool.false_and, Bool.and_false])

end

/-- **If at each pair of records the rounds after the fifth close it (`ClosesR`, shown of no
decision at a sample with an answer), the written link is round-by-round sound record by record for
`Sz.LangR`**, which has a way out for each table; the other hypotheses: the head. The decision is a
function of the pair of records. The error counts do not depend on the records (for εt: asked). Of
the decoder's radius eM < d is asked, and not that twice it be below d. -/
theorem link_sound_rec (S : Sz) (Z : Sample GE S.En) (d1 d2 d3 d4 d5 : PQ.RD) (tl : List PQ.RD)
    (xs : List PQ.XO) (dec : (S.lkR Z).X0 → PQ.View → Bool) (cut d bad₀ L₀ bad₁ L₁ : ℕ)
    (L : Bool → ℕ) (hcut : S.P.cut = cut) (hdist : HasDist (S.ixR Z).G d) (hM : S.eM < d)
    (h0 : S.e0 ≤ S.eM) (h1 : S.e1 ≤ S.eM) (hm0 : (S.ixR Z).MCAeq S.e0 bad₀)
    (hl0 : ∀ f : (S.ixR Z).Row → S.Pos → GE, ListLE (DecodesTo (S.ixR Z).G S.e0 f) L₀)
    (hm1 : (S.ixR Z).MCAeq S.e1 bad₁)
    (hl1 : ∀ f : (S.ixR Z).Row → S.Pos → GE, ListLE (DecodesTo (S.ixR Z).G S.e1 f) L₁)
    (hpl : Function.Injective (S.lkR Z).D.pl) (hlist : ∀ a, ((S.lkR Z).N.om a).ListLE (L a))
    (hev : ∀ a, ((S.lkR Z).N.om a).Evades) (hd : DrawsOK S d1 d2 d3 d4 d5)
    (εt : Err (PQ.uL (ckP .two) tl))
    (hc : ∀ r, ClosesR S Z r d1 d2 d3 d4 d5 tl xs (dec r) εt) (r : (S.lkR Z).X0) :
    (written S d1 d2 d3 d4 d5 tl xs (dec r)).Sound (fun _ y => S.LangR Z cut r y)
      (0, coreErrR S Z d1 d2 d3 d4 d5 (bad₀ + L₀ * (S.P.v * Fintype.card GE ^ (S.P.v - 1)))
        (bad₁ + L₁ * (S.P.v * Fintype.card GE ^ (S.P.v - 1))) L εt) :=
  link_sound_at S Z r d1 d2 d3 d4 d5 tl xs (dec r) cut d bad₀ L₀ bad₁ L₁ L hcut hdist hM h0 h1 hm0
    hl0 hm1 hl1 hpl hlist hev hd εt (hc r)

/-- The same for the language with four clauses, which is the wider one. -/
theorem link_sound_recE2 (S : Sz) (Z : Sample GE S.En) (d1 d2 d3 d4 d5 : PQ.RD) (tl : List PQ.RD)
    (xs : List PQ.XO) (dec : (S.lkR Z).X0 → PQ.View → Bool) (cut d bad₀ L₀ bad₁ L₁ : ℕ)
    (L : Bool → ℕ) (hcut : S.P.cut = cut) (hdist : HasDist (S.ixR Z).G d) (hM : S.eM < d)
    (h0 : S.e0 ≤ S.eM) (h1 : S.e1 ≤ S.eM) (hm0 : (S.ixR Z).MCAeq S.e0 bad₀)
    (hl0 : ∀ f : (S.ixR Z).Row → S.Pos → GE, ListLE (DecodesTo (S.ixR Z).G S.e0 f) L₀)
    (hm1 : (S.ixR Z).MCAeq S.e1 bad₁)
    (hl1 : ∀ f : (S.ixR Z).Row → S.Pos → GE, ListLE (DecodesTo (S.ixR Z).G S.e1 f) L₁)
    (hpl : Function.Injective (S.lkR Z).D.pl) (hlist : ∀ a, ((S.lkR Z).N.om a).ListLE (L a))
    (hev : ∀ a, ((S.lkR Z).N.om a).Evades) (hd : DrawsOK S d1 d2 d3 d4 d5)
    (εt : Err (PQ.uL (ckP .two) tl))
    (hc : ∀ r, ClosesR S Z r d1 d2 d3 d4 d5 tl xs (dec r) εt) (r : (S.lkR Z).X0) :
    (written S d1 d2 d3 d4 d5 tl xs (dec r)).Sound (fun _ y => S.LangE2T Z cut r y)
      (0, coreErrR S Z d1 d2 d3 d4 d5 (bad₀ + L₀ * (S.P.v * Fintype.card GE ^ (S.P.v - 1)))
        (bad₁ + L₁ * (S.P.v * Fintype.card GE ^ (S.P.v - 1))) L εt) :=
  fun x y hy => link_sound_rec S Z d1 d2 d3 d4 d5 tl xs dec cut d bad₀ L₀ bad₁ L₁ L hcut hdist hM
    h0 h1 hm0 hl0 hm1 hl1 hpl hlist hev hd εt hc r x y fun h => hy (Or.inr h)

end OnBytes.Slice
