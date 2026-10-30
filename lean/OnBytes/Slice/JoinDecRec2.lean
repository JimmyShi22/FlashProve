-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/JoinDecRec2.lean: the join for stored tables with a record, where THE JOIN pays for
"the record does not single one table out".

THIS IS WHAT WOULD BE CLAIMED; NOTHING IS SHOWN. Definitions, one lemma of logic, and an
implication: no part that meets its hypotheses with a bound below 1 is written.

Why. OnBytes/Slice/DecoderRec.lean names three candidates for who pays for the seeds at which two
members of a table's list with different message parts have the same answers, and writes two: a part
pays once a table; each part pays itself. This file writes the third. EVERY language has the way out
for each table that it touches, so no part's soundness speaks of where a seed comes from; that both
ways out are shut comes from the verifier's yes outside ONE rare set of outcomes, X', over the one
oracle, whose bound bX' is a term of the join already.

Main definitions: `DecR.LangK2`, `DecR.LangE2` (the key's and the entry's languages with the way
out; the proof's is `DecR.LangP`); `good4R`. Main theorems: `DecR.langK_of_langK2`,
`langE_of_langE2` (from a language with the way out to the one of DecoderRec.lean that shuts it,
where it is shut: for a compiled part whose interactive theorem has the way out and which pays for
it itself); `DecR.path2` (the path, given that both ways out are shut); `join_id_decR2_run`, over
`join_id_run4` (OnBytes/Slice/JoinOut4.lean).

What turns against `join_id_decR_run`. Two languages are weaker. `hYes` has two clauses more:
outside X' the way out is shut for the first raw string, as the key's part reads it off the
committer's own log, at the key's seed; and for the second, as the proof's part reads it off the
whole log, at the proof's seed.

What is not claimed. THAT SUCH AN X' IS RARE: not shown. That the seeds in the records that `recK`
and `recF` read off the checkers' values are the oracle's at the names of the two roots: asked
nowhere; without it no such X' is rare. It would need besides: that a table is settled when its seed
is first asked; that the strings of a seed's round were not asked, at a start that the name's call
then answers, before the table stood; a count of the seeds that collide (for the programs' sample:
`coll_count`, OnBytes/Slice/RecordColl.lean, for one table, among all seeds); the passage from that
count to a probability (over uniform blocks: OnBytes/Slice/SeedBias.lean, SeedTie.lean; for one
table and one key fixed before the oracle is drawn, over a uniform oracle: SeedOracle.lean; for a
maker that picks them after questions: not written); one try for each table's name that a maker
asks, with no factor for work. `join_id_decR2_run` IS A FORM THAT NOTHING USES; used are `LangK2`,
`LangE2` and the two lemmas: the plan is that every interactive theorem has these languages, and
that the compiled key's and entry's parts shut the way out themselves. The form with what is fine
written out (OnBytes/Slice/FineAtRec.lean) and the step to every committer (WrapLaw.lean) are
written for the first two candidates alone. All limits in the heads of JoinDecRec.lean,
JoinOut4.lean and DecoderRec.lean hold here too.

-/
import OnBytes.Slice.JoinDecRec
import OnBytes.Slice.JoinOut4

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch MeasureTheory
open OnBytes.Tie (IdKey idCode firstId)
open scoped ENNReal

namespace DecR
variable {D : DecR} {X : Type}

/-- The key's language WITH THE WAY OUT: the way out is open, or with its record the string decodes
and the matrix is in range. -/
def LangK2 (A : D.Claims X) (w : Way D) (rec : D.Rec) (y : Raw Run.PQ.SgX) : Prop :=
  w y rec.1 ∨ ∃ u, D.dcdRaw y rec = some u ∧ A.inRange (A.mat u)

/-- The entry's language with the way out FOR BOTH TABLES: the first string with its record does not
decode, or either string's way out is open, or both decode, to tables that agree before the pads. -/
def LangE2 (w : Way D) (rec₀ rec₁ : D.Rec) (y₀ y₁ : Raw Run.PQ.SgX) : Prop :=
  D.dcdRaw y₀ rec₀ = none ∨ w y₀ rec₀.1 ∨ w y₁ rec₁.1 ∨
    ∃ u₀ u₁, D.dcdRaw y₀ rec₀ = some u₀ ∧ D.dcdRaw y₁ rec₁ = some u₁ ∧ D.Agree u₁ u₀

/-- **From the key's language with the way out to the one that shuts it**, where the way out is
shut: what a compiled part calls, whose interactive theorem has the way out and which pays for the
way out itself. -/
theorem langK_of_langK2 (A : D.Claims X) (w : Way D) {rec : D.Rec} {y : Raw Run.PQ.SgX}
    (h0 : ¬ w y rec.1) (hK : LangK2 A w rec y) : LangK A w rec y := by
  rcases hK with h | ⟨u, hu, hr⟩
  · exact absurd h h0
  · exact ⟨u, hu, h0, hr⟩

/-- The like for the entry's language, where the COPY's way out is shut. -/
theorem langE_of_langE2 (w : Way D) {rec₀ rec₁ : D.Rec} {y₀ y₁ : Raw Run.PQ.SgX}
    (h1 : ¬ w y₁ rec₁.1) (hE : LangE2 w rec₀ rec₁ y₀ y₁) : LangE w rec₀ rec₁ y₀ y₁ := by
  rcases hE with h | h | h | ⟨u₀, u₁, a, b, c⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact absurd h h1
  · exact Or.inr (Or.inr ⟨u₀, u₁, a, b, c, h1⟩)

/-- **The path where no part shuts a way out**: that both are shut (`h0`, `h1`) comes from outside
the three languages. The proof's language is `LangP`, which has the way out already. -/
theorem path2 (A : D.Claims X) (w : Way D) {rec₀ rec₁ : D.Rec} {y₀ y₁ : Raw Run.PQ.SgX} {x : X}
    (h0 : ¬ w y₀ rec₀.1) (h1 : ¬ w y₁ rec₁.1) (hK : LangK2 A w rec₀ y₀)
    (hE : LangE2 w rec₀ rec₁ y₀ y₁) (hP : LangP A w x rec₁ y₁) :
    ∃ u, D.dcdRaw y₀ rec₀ = some u ∧ A.inRange (A.mat u) ∧ A.Rel (A.mat u) x :=
  path A w (langK_of_langK2 A w h0 hK) (langE_of_langE2 w h1 hE) hP

end DecR

variable {β δ Xi : Type} {D : DecR}

/-- What the three parts' languages give together where every language has the way out; it names
the second raw string. -/
def good4R {OK OE OF : Type} (A : D.Claims Xi) (w : DecR.Way D) (recK : OK → D.Rec)
    (recE₀ recE₁ : OE → D.Rec) (recF : OF → D.Rec) (xOf : OF → Xi) (oK : OK) (oE : OE) (oF : OF)
    (y₀ y₁ : Raw Run.PQ.SgX) : Prop :=
  DecR.LangK2 A w (recK oK) y₀ ∧ DecR.LangE2 w (recE₀ oE) (recE₁ oE) y₀ y₁ ∧
    DecR.LangP A w (xOf oF) (recF oF) y₁

/-- **THIS IS WHAT WOULD BE CLAIMED; NOTHING IS SHOWN. The join for stored tables with a record,
WHERE THE JOIN PAYS for "the record does not single one table out".** Against `join_id_decR_run`
(OnBytes/Slice/JoinDecRec.lean): the key's and the entry's languages have the way out too (`LangK2`,
`LangE2`); `hYes` has TWO CLAUSES MORE: outside X' the way out is shut for the first raw string, as
the key's part reads it off the committer's own log, at the key's seed, and for the second, as the
proof's part reads it off the whole log, at the proof's seed. So X' must hold the outcomes in which
a way out is open, and bX' is the price. Every other sign is that theorem's. -/
theorem join_id_decR2_run (w : DecR.Way D) (S₀ : Finset (List Bool))
    (S₁ : Tab → Finset (List Bool))
    (C : OComp (rom 256) β) (dig : β → ZKCP.Digest 256) (P : β → OComp (rom 256) δ)
    (key : Tab → Tab → δ → IdKey) (tC tP : ℕ) (hC : C.QueryBound tC)
    (hP : ∀ b, (P b).QueryBound tP)
    (K E F : Tab → Tab → PartO 256 ((β × Trace (rom 256)) × δ) Run.PQ.SgX)
    (hK : ∀ T₀ T₁, (K T₀ T₁).OK) (hE : ∀ T₀ T₁, (E T₀ T₁).OK) (hF : ∀ T₀ T₁, (F T₀ T₁).OK)
    (bS : ℕ → ℕ → ℝ≥0∞) (hS : ∀ T₀ T₁, (K T₀ T₁).Stable bS)
    (hKE : ∀ T₀ T₁, SameRaw (K T₀ T₁) (E T₀ T₁)) (hEF : ∀ T₀ T₁, SameRaw (E T₀ T₁) (F T₀ T₁))
    (A : Tab → Tab → D.Claims Xi) (xOf : ∀ T₀ T₁, (F T₀ T₁).Out → Xi)
    (recK : ∀ T₀ T₁, (K T₀ T₁).Out → D.Rec) (recE₀ recE₁ : ∀ T₀ T₁, (E T₀ T₁).Out → D.Rec)
    (recF : ∀ T₀ T₁, (F T₀ T₁).Out → D.Rec)
    (hLK : ∀ T₀ T₁ oK Y, (K T₀ T₁).Lang oK [Y] → DecR.LangK2 (A T₀ T₁) w (recK T₀ T₁ oK) Y)
    (hLE : ∀ T₀ T₁ oE Y₀ Y₁, (E T₀ T₁).Lang oE [Y₀, Y₁] →
      DecR.LangE2 w (recE₀ T₀ T₁ oE) (recE₁ T₀ T₁ oE) Y₀ Y₁)
    (hLF : ∀ T₀ T₁ oF Y, (F T₀ T₁).Lang oF [Y] →
      DecR.LangP (A T₀ T₁) w (xOf T₀ T₁ oF) (recF T₀ T₁ oF) Y)
    (X' : Tab → Tab → Fam (rom 256) → Set (((β × Trace (rom 256)) × δ) × Trace (rom 256)))
    (bX' : ℝ≥0∞)
    (hX' : ∀ T₀ T₁, Rom.Pr (twoExp (pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ C))
      fun b => pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ (P b))).withTrace (X' T₀ T₁) ≤ bX')
    (hid : ∀ k s, idCode k = some s → s ∉ S₀ ∧ ∀ T₀, s ∉ S₁ T₀)
    (V : β × δ → OComp (rom 256) Bool) (hV : ∀ x, (V x).NoCoin)
    (Fine : ((β × Trace (rom 256)) × δ) × Trace (rom 256) → Prop)
    (FineT : Tab → Tab → ((β × Trace (rom 256)) × δ) × Trace (rom 256) → Prop)
    (hFine : ∀ T₀ T₁ w, FineT T₀ T₁ w → Fine w)
    (hoff₀ : ∀ w, ¬ Fine w → ¬ Fine (offBoth S₀ w))
    (hoff₁ : ∀ T₀ w, ¬ Fine w → ¬ Fine (offBoth (S₁ T₀) w))
    (hYes : ∀ T₀ T₁ g z,
      (V (z.1.1.1, z.1.2)).det (over S₀ T₀ (over (S₁ T₀) T₁ g)) = true → z ∉ X' T₀ T₁ g →
      (∃ s, idCode (key T₀ T₁ z.1.2) = some s ∧
        over S₀ T₀ (over (S₁ T₀) T₁ g) () s = dig z.1.1.1) ∧ ∃ oK oE oF cm',
        ((K T₀ T₁).chk z.1).det g = some oK ∧ ((E T₀ T₁).chk z.1).det g = some oE ∧
        ((F T₀ T₁).chk z.1).det g = some oF ∧
        (K T₀ T₁).roots oK = [Run.bytesToDig (key T₀ T₁ z.1.2).2.2.root] ∧
        (E T₀ T₁).roots oE = [Run.bytesToDig (key T₀ T₁ z.1.2).2.2.root, cm'] ∧
        (F T₀ T₁).roots oF = [cm'] ∧
        recE₀ T₀ T₁ oE = recK T₀ T₁ oK ∧ recF T₀ T₁ oF = recE₁ T₀ T₁ oE ∧
        ¬ w ((K T₀ T₁).raw z.1.1.2 (Run.bytesToDig (key T₀ T₁ z.1.2).2.2.root))
          (recK T₀ T₁ oK).1 ∧
        ¬ w ((F T₀ T₁).raw z.2 cm') (recF T₀ T₁ oF).1 ∧
        (firstId (dig z.1.1.1) z.1.1.2 = some (key T₀ T₁ z.1.2) → NoClash z.2 →
          (∃ τ, z.2 = z.1.1.2 ++ τ) →
          goodDecR (A T₀ T₁) (xOf T₀ T₁ oF) (recK T₀ T₁ oK)
            ((K T₀ T₁).raw z.1.1.2 (Run.bytesToDig (key T₀ T₁ z.1.2).2.2.root)) →
          FineT T₀ T₁ z))
    (B : ℝ≥0∞)
    (hB : ∀ T₀ T₁, (K T₀ T₁).bound (tC + tP) + ((E T₀ T₁).bound (tC + tP) +
      ((F T₀ T₁).bound (tC + tP) +
        (bS tC tP + ((((tC + tP + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 + bX')))) ≤ B) :
    Rom.Pr (twoExp (twoExp C P) fun x => V (x.1.1, x.2))
      (fun _ => {z | z.2 = true ∧ ¬ Fine z.1}) ≤ B :=
  join_id_run4 S₀ S₁ C dig P key tC tP hC hP K E F hK hE hF bS hS hKE hEF
    (fun T₀ T₁ => good4R (A T₀ T₁) w (recK T₀ T₁) (recE₀ T₀ T₁) (recE₁ T₀ T₁) (recF T₀ T₁)
      (xOf T₀ T₁))
    (fun T₀ T₁ oK oE oF Y₀ Y₁ lK lE lF =>
      ⟨hLK T₀ T₁ oK Y₀ lK, hLE T₀ T₁ oE Y₀ Y₁ lE, hLF T₀ T₁ oF Y₁ lF⟩)
    X' bX' hX' hid V hV Fine FineT hFine hoff₀ hoff₁
    (fun T₀ T₁ g z hy hx => by
      obtain ⟨hI, oK, oE, oF, cm', cK, cE, cF, rK, rE, rF, t0, t1, w0, w1, hG⟩ :=
        hYes T₀ T₁ g z hy hx
      refine ⟨hI, oK, oE, oF, cm', cK, cE, cF, rK, rE, rF, fun hf hc hs hg => hG hf hc hs ?_⟩
      obtain ⟨gK, gE, gP⟩ := hg
      rw [t0] at gE
      rw [t1] at gP w1
      exact DecR.path2 _ w w0 w1 gK gE gP)
    B hB

end OnBytes.Slice
