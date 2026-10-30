-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/EntryFromLink.lean: THE CARRIER FOR THE ENTRY: soundness record by record of the
library's written link (`written`, OnBytes/Slice/LinkSound.lean), for the language on tables
`Sz.LangE2T` (OnBytes/Slice/LinkSoundRec.lean), passes to the sibling's written link of a
description (`Link0 D`, OnBytes/TypedOracleCompiler/Slice/EntryX.lean), for the language `lgEX`
(OnBytes/TypedOracleCompiler/Slice/EntryXJudge.lean), WITH ONE LIST OF ERROR COUNTS FOR ALL INSTANCES.

Why. The entry's judge in the sibling (`entry_judge_record`) asks: for every instance x (both
tables' answers, both tables' seeds) the protocol `Link0 D (dec x)` is round-by-round sound for
`lgEX` at x, with one list of counts ε, below a bound. OnBytes/Slice/LinkChainJoh.lean concludes
soundness of `written S ...` at a pair of records. This is said under the hypotheses that stand in
the statement itself, which this comment does not list; it is no claim that they hold. The two
protocols are one text over two kinds of rounds' data, and their shapes are two types.
OnBytes/TypedOracleCompiler/Slice/EntryAccept.lean carries soundness between them at one decision, in the form
"there are counts": record by record that gives counts that may hang on the record.
OnBytes/Slice/ShapeMap.lean names the carried counts (`fwd`), and the map of shapes does not look at
the decision. So, given one list on the library's side, one list serves all instances.

Main definitions: `recOf` (the pair of records of an instance).
Main theorems.
 `sound_ofLib_named`   soundness passes at one decision, with the counts `fwd (sOneUp C ds) ε`.
 `lgE_of_langE2T`      the language on tables gives the typed language.
 `entry_hS`            THE CARRIER: what `entry_judge_record` calls hS and hb, from soundness of
                       `written` at each instance's pair of records with one list of counts.

Asked by `entry_hS` of the description D: its plan's field is the second (so its kit is the
library's "challenges as hash blocks" there); its rounds' data are the library's d1, ..., d5 and tl,
read as the sibling's (`ofLib`); its stored tables have 2^a positions, a the tables' code's; its
openings are xs. Of the sizes: nothing; the sample map is `recZ` at the tables' code's l, and the
cut is l - 3 s, with lg and s letters.

Not claimed. NO SOUNDNESS IS PROVED: it is a hypothesis (H). That any description meets the four
conditions: not here (OnBytes/TypedOracleCompiler/Slice/SmallRecDesc.lean and FullRecDesc.lean show them of two).
That the format's number s of answers is the letter s. That the decision at x reads the answers as
`an` does: not here (OnBytes/TypedOracleCompiler/Slice/EntryRow13.lean takes the decision at keys written of `an`'s
answers). Nothing on a round with two roots: `ofLib` has at most one. Nothing on a compiler, a
wiring, a page, bytes or a file. The compiler under OnBytes/TypedOracleCompiler/ is the one that
`innerCompiledVerifier` is made with; it builds on definitions of Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryAccept
import OnBytes.TypedOracleCompiler.Slice.EntryXJudge
import OnBytes.Slice.LinkSoundRec

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open OnBytes.Slice OnBytes.Slice.ShapeMap TypedOracleCompiler.Run TypedOracleCompiler.Slice.CarryOne
open _root_.Iop (Err InteractiveOracleProof twoExternalStrings)
open _root_.Run.PQ (View SgX)
open scoped ENNReal

/-- Soundness passes from the library's protocol to the sibling's at the library's rounds' data,
at one decision, with named counts. The map of shapes does not look at the decision. -/
theorem sound_ofLib_named (C : _root_.Run.PQ.CK) (ds : List _root_.Run.PQ.RD) (a : ℕ)
    (xs : List _root_.Run.PQ.XO) (dec : View → Bool)
    (Lg : Unit → (twoExternalStrings (2 ^ a) SgX).Str → Prop)
    (ε : Err (_root_.Run.PQ.skeletonOverBothExternalStrings C ds a xs dec).up.loc.shape)
    (h : (_root_.Run.PQ.skeletonOverBothExternalStrings C ds a xs dec).up.loc.Sound Lg ε) :
    (PQ.skeletonOverBothExternalStrings C (ds.map PQ.ofLib) a xs dec).up.loc.Sound Lg (fwd (sOneUp C ds) ε) :=
  sound (PQ.skeletonOverBothExternalStrings C (ds.map PQ.ofLib) a xs dec).up.loc (_root_.Run.PQ.skeletonOverBothExternalStrings C ds a xs dec).up.loc
    (sOneUp C ds) (fun x y τ hτ => (EntryAccept.accept_back C ds a xs dec x y τ).symm.trans hτ) Lg ε
    (firstZero_of_flat (sOneUp C ds) (flat_sOne C ds) ε) h

section
variable {An : Type} (S : Sz) (lg s : ℕ)

/-- The pair of records of an instance "both tables' answers; both tables' seeds". -/
def recOf
    (an : An → (decRec S.P.T S.P.v S.eM lg s).ix.Row × (decRec S.P.T S.P.v S.eM lg s).Z.S → GE)
    (x : (An × An) × ((Fin s → (Fin lg → GE) × NZ) × (Fin s → (Fin lg → GE) × NZ))) :
    (S.lkR (recZ S.P.T.l lg s)).X0 :=
  ((x.2.1, an x.1.1), (x.2.2, an x.1.2))

/-- The language on tables gives the typed language at the instance's pair of records. -/
theorem lgE_of_langE2T
    (an : An → (decRec S.P.T S.P.v S.eM lg s).ix.Row × (decRec S.P.T S.P.v S.eM lg s).Z.S → GE)
    (x : (An × An) × ((Fin s → (Fin lg → GE) × NZ) × (Fin s → (Fin lg → GE) × NZ)))
    (y : (S.Pos → SgX) × (S.Pos → SgX))
    (h : S.LangE2T (recZ S.P.T.l lg s) (S.P.T.l - 3 * s) (recOf S lg s an x) y) :
    DecR.LgE (D := decRec S.P.T S.P.v S.eM lg s) (Equiv.refl _) an id (x.1.1, x.2.1)
      (x.1.2, x.2.2) y.1 y.2 :=
  (S.langE2T_iff (recZ S.P.T.l lg s) (S.P.T.l - 3 * s) (recOf S lg s an x) y).1 h

/-- THE CARRIER FOR THE ENTRY. If at each instance's pair of records the library's written link
is round-by-round sound for `Sz.LangE2T`, with ONE list of counts ε below e, then at a description D
with these rounds' data, openings, positions and kit the sibling's written link is round-by-round
sound for `lgEX` at each instance, with ONE list of counts below e. -/
theorem entry_hS
    (an : An → (decRec S.P.T S.P.v S.eM lg s).ix.Row × (decRec S.P.T S.P.v S.eM lg s).Z.S → GE)
    (d1 d2 d3 d4 d5 : _root_.Run.PQ.RD) (tl : List _root_.Run.PQ.RD)
    (xs : List _root_.Run.PQ.XO) (D : PQ.XD) (hf : D.base.plan.field = .two)
    (hds : D.ds = (d1 :: d2 :: d3 :: d4 :: d5 :: tl).map PQ.ofLib) (ha : D.a = S.P.T.a)
    (hxs : D.xs = xs)
    (dec : (An × An) × ((Fin s → (Fin lg → GE) × NZ) × (Fin s → (Fin lg → GE) × NZ)) →
      View → Bool)
    (ε : Err (written S d1 d2 d3 d4 d5 tl xs fun _ => true).shape) (e : ℝ≥0∞)
    (hb : Err.Below ε e)
    (H : ∀ x, (written S d1 d2 d3 d4 d5 tl xs (dec x)).Sound
      (fun _ y => S.LangE2T (recZ S.P.T.l lg s) (S.P.T.l - 3 * s) (recOf S lg s an x) y) ε) :
    ∃ ε' : Err (Link0 D fun _ => true).shape,
      (∀ x, (Link0 D (dec x)).Sound (fun _ => lgEX S.P.T S.P.v S.eM lg s D an x) ε') ∧
        Err.Below ε' e := by
  have key : ∀ (C' : _root_.Run.PQ.CK) (ds' : List PQ.RD) (a' : ℕ)
      (xs' : List _root_.Run.PQ.XO), C' = _root_.Run.ckP .two →
      ds' = (d1 :: d2 :: d3 :: d4 :: d5 :: tl).map PQ.ofLib → a' = S.P.T.a → xs' = xs →
      ∃ ε' : Err (PQ.skeletonOverBothExternalStrings C' ds' a' xs' fun _ => true).up.loc.shape,
        (∀ x, (PQ.skeletonOverBothExternalStrings C' ds' a' xs' (dec x)).up.loc.Sound
          (fun _ (y : (Fin (2 ^ a') → SgX) × (Fin (2 ^ a') → SgX)) =>
            DecR.LgE (D := decRec S.P.T S.P.v S.eM lg s) (Equiv.refl _) an id (x.1.1, x.2.1)
              (x.1.2, x.2.2) y.1 y.2) ε') ∧ Err.Below ε' e := by
    rintro _ _ _ _ rfl rfl rfl rfl
    refine ⟨fwd (sOneUp _ _) ε, fun x => ?_, below _ _ _ hb⟩
    exact sound_ofLib_named _ _ _ _ (dec x) _ ε fun u y hy =>
      H x u y fun h => hy (lgE_of_langE2T S lg s an x y h)
  exact key D.C D.ds D.a D.xs (congrArg _root_.Run.ckP hf) hds ha hxs

end

end TypedOracleCompiler.Slice
