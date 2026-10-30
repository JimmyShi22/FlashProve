-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlocksJohnson.lean: UNDER A NAMED, UNPROVED STATEMENT ON TWO CODES: a fold, the base
case and a code switch of a proximity test are taken off at a radius below the Johnson radius.

OnBytes/Slice/BlocksBySource.lean takes off a fold and the base case of a proximity test below half
a stage's distance, and OnBytes/Slice/CsJoint.lean a code switch. There the two facts on codes that
the blocks ask are theorems: a word has one code word near it, and a line through two words has few
exceptional points (a point θ is exceptional if f₀ + θ f₁ agrees with a code word on all but e
positions, while f₀ and f₁ do not both agree with code words on those same positions). Beyond half
the distance, below the Johnson radius, the first fact is still a theorem, with a longer list: the
Johnson bound, from the distance alone (the library's `ld_list_johnson`, Cb/Ld/LdRelJohnson.lean).
Of the second the library's own page of limits says that what it proves outright holds only within
half the distance. This file takes it as a hypothesis with a name, `Sg.CountsAt`: at the radius e a
line through two words has at most bC exceptional points for one main row and at most bZ for one
mask row repeated to the main rows' length. Both are named, since the road by which
OnBytes/Slice/NumbersHalf.lean gets the second from a fact on Reed-Solomon codes asks a radius below
half the repeated mask code's own distance (`Sg.dZ`; `Code.MCAOn.subcode`, Code/Mutual.lean). Where
2 e is below that distance, which can be larger than the stage's, the second is a theorem already,
and the main row's count alone is open (`Sg.countsAt_of_main`). Rows cost nothing at any radius, and
a pair of tables has the sum of the two counts (the library's `ld_rows_free`, `ld_mca_pair`).

The blocks themselves (`fold_block`, OnBytes/Slice/FoldPeel.lean; `base_block`, Base.lean;
`cs_block`, BlockCs.lean) take the list and the counts as letters. Of the radius their statements
ask at most e < d (in `Cb.Spec.CodesOK`), and nowhere that twice the radius be below the distance.
So this file only fills them. The library has the same fillers for its own records
(Cb/Ld/LdTowerJohn.lean: `ldJohn_errOK`, `ldJohn_base`, `ldJohn_switch`); by a reading, lists,
counts and hypotheses agree.

Main definitions: `Sg.CountsAt`, `Sg.InJ`, `Sg.lstJ`.
Main theorems.
 `Fit.listJ`          the Johnson bound for a code with the laws and a distance.
 `errOK_joh`          the numbers of a folding: lists by the Johnson bound, counts as given.
 `fold_holds_joh`, `base_holds_joh`, `cs_holds_joh`   the three blocks, in the form in which the
                     blocks are joined.
 `Sg.countsAt_src`, `Sg.inJ_of_half`   below half the stage's distance the hypothesis is a theorem,
                     at the counts by source, and the radius is below the Johnson radius.
 `Sg.countsAt_of_main`   below half the repeated mask code's own distance the mask row's half of
                     the hypothesis is a theorem.
 `mixed_inJ`          at a stage made by hand a radius beyond half the distance is below the Johnson
                     radius.

Not claimed. THIS IS NO PROOF OF SOUNDNESS AT THE JOHNSON RADIUS. No statement on a proof, a file or
a verifier's yes follows from this file at a radius of half the distance or more. Nothing here on
the batching before the first fold. THAT `Sg.CountsAt` HOLDS AT ANY RADIUS OF HALF THE DISTANCE OR
MORE, AT ANY COUNTS BELOW THE NUMBER OF FIELD ELEMENTS, IS NOT SHOWN HERE. At bC = bZ = the number
of field elements it holds of every code at every radius (`Sg.countsAt_full`,
OnBytes/Slice/ManyAtLetters.lean). The counts of a fold's repeated rounds and of the base case's
first round are then no smaller than the number of values that such a round draws: in a round
without work they say nothing; in a round with b test bits their share of the challenge values is
about 2^-b, which is the work's alone, with no fact on a code behind it. What the hypothesis assumes
is the size of the two numbers. It is not the statement that the library calls `BCHKS46`
(Cb/Gen/CodeListRS.lean) and assumes in some theorems: this file derives it from nothing.
OnBytes/Slice/CountsBchks.lean derives the main row's half from that statement's form at one pair of
fields; the mask row's half is a theorem where 2 e is below the repeated mask code's own distance;
elsewhere OnBytes/Slice/MaskBchks.lean derives it from the same statement, at the price of a list.
That the planner's numbers under the rule of the Johnson radius (OnBytes/Params/Distance.lean:
`johnsonCount`, `johnsonList`) are bC, bZ and `Sg.lstJ` is not shown. Nothing on a stored table, its
decoder or the link between two stored tables, and nothing on a record. No number is stated at a
file: `mixed_inJ` is at a stage made by hand, and says nothing of the main row's count. The blocks
are applied at no stage here.

-/
import Cb.Gen.JohnsonListProofs
import Cb.Ld.LdRelJohnsonProofs
import OnBytes.Slice.BlocksBySource
import OnBytes.Slice.CsJoint

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

section
variable {E P : Type} [Field E] [Fintype E] [Fintype P]

/-- The Johnson bound: below the Johnson radius for the number of positions and the distance d, a
word has at most `listMax` code words within e positions. -/
theorem Fit.listJ {C : LdCode E P} {d : ℕ} (h : Fit C d) {e : ℕ}
    (hj : InJohnson (Fintype.card P) d e) : C.ListAt e (listMax (Fintype.card P) d e) :=
  ld_list_johnson E P C d e h.laws h.dist hj

/-- The numbers of a folding below the Johnson radius. If the three codes of the folding Y have the
laws and the distance d, e is below d and below the Johnson radius, and one row under each of the
three codes has the given count of exceptional points, then every stage has lists by the Johnson
bound, and every halving of each of the three tables has the given count. -/
theorem errOK_joh (Y : SumPar E P) (d e bC bZ bW : ℕ) (h : Spec.CodesOK E P Y.C Y.Z Y.Zw d e)
    (hj : InJohnson (Fintype.card P) d e) (hbC : Y.C.MCAat e bC) (hbZ : Y.Z.MCAat e bZ)
    (hbW : Y.Zw.MCAat e bW) :
    Y.ErrOK e (fun _ => listMax (Fintype.card P) d e) (fun _ => bC) (fun _ => bZ) (fun _ => bW) :=
  have hC : Fit Y.C d := ⟨h.1.1, h.2.1.1⟩
  have hZ : Fit Y.Z d := ⟨h.1.2.1, h.2.1.2.1⟩
  have hW : Fit Y.Zw d := ⟨h.1.2.2, h.2.1.2.2⟩
  { list := fun _ _ => ((hC.il _).pair ((hZ.il _).pair (hW.il _))).listJ hj
    mcaC := fun _ _ _ => hC.mcaRows hbC _
    mcaS := fun _ _ _ => hZ.mcaRows hbZ _
    mcaW := fun _ _ _ => hW.mcaRows hbW _ }

end

namespace Sg

/-- **THE NAMED HYPOTHESIS.** At the radius e a line through two words has at most bC exceptional
points for one main row, and at most bZ for one mask row repeated to the main rows' length. -/
structure CountsAt (s : Sg) (e bC bZ : ℕ) : Prop where
  main : s.cM.MCAat e bC
  mask : s.cZ.MCAat e bZ

/-- The radius e is below the stage's distance and below the Johnson radius for the stage's number
of positions and its distance. (The first follows from the second; it is kept since the blocks ask
it.) -/
def InJ (s : Sg) (e : ℕ) : Prop := e < s.d ∧ InJohnson (2 ^ s.C.a) s.d e

/-- The Johnson bound on a list at the stage's number of positions and its distance. It has a
meaning only under `InJ`, and it grows as e nears the Johnson radius. -/
def lstJ (s : Sg) (e : ℕ) : ℕ := listMax (2 ^ s.C.a) s.d e

variable {s : Sg}

/-- A stage has 2^a positions. -/
theorem card_Ps (s : Sg) : Fintype.card s.Ps = 2 ^ s.C.a := Fintype.card_fin _

/-- The Johnson bound for a code on the stage's positions with the stage's distance. -/
theorem listJ_of {C : LdCode GE s.Ps} (h : Fit C s.d) {e : ℕ} (hj : s.InJ e) :
    C.ListAt e (s.lstJ e) := by
  have h1 := h.listJ (e := e) (by rw [card_Ps]; exact hj.2)
  rwa [card_Ps] at h1

/-- The tables before the fold: at most bC + bZ exceptional points. -/
theorem CountsAt.cIn (h : s.Sized) {e bC bZ : ℕ} (hc : s.CountsAt e bC bZ) :
    s.cIn.MCAat e (bC + bZ) :=
  ld_mca_pair GE s.Ps _ _ e _ _ ((fit_cM h).mcaRows hc.main _) ((fit_cZ h).mcaRows hc.mask _)

/-- Below half the stage's distance the hypothesis is a theorem, at the counts by source. -/
theorem countsAt_src (h : s.Sized) (hp : s.Pos) {e : ℕ} (h2 : 2 * e < s.d) :
    s.CountsAt e (s.cntC e) (s.cntZ e) :=
  ⟨mcaSrc_cM h hp h2, mcaSrc_cZ h hp h2⟩

/-- Below half the repeated mask code's own distance the mask row's half of the hypothesis is a
theorem, at the count by source: the main row's count alone is asked. -/
theorem countsAt_of_main (h : s.Sized) (hp : s.Pos) {e bC : ℕ} (h2 : 2 * e < s.dZ)
    (hm : s.cM.MCAat e bC) : s.CountsAt e bC (s.cntZ e) := by
  refine ⟨hm, ?_⟩
  unfold cntZ
  split
  · exact mcaThird_cZ h ‹_›
  · exact mca_half_rep s.Z s.C.a h.short h.small hp.someZ h.roomZ e h2

/-- A radius below half the stage's distance is below the Johnson radius. -/
theorem inJ_of_half (h : s.Sized) (hp : s.Pos) {e : ℕ} (h2 : 2 * e < s.d) : s.InJ e := by
  refine ⟨by omega, inJohnson_of_unique _ _ _ ?_ h2⟩
  have h1 := hp.someC
  have h3 := h.roomC
  have h4 : s.d ≤ s.dC := min_le_left _ _
  unfold Sg.dC at h4
  omega

end Sg

/-- The numbers of a fold below the Johnson radius, under the named hypothesis. -/
theorem foldNums_joh {s : Sg} (hs : s.Sized) {e bC bZ : ℕ} (hj : s.InJ e)
    (hc : s.CountsAt e bC bZ) :
    (s.par 0).ErrOK e (fun _ => s.lstJ e) (fun _ => bC) (fun _ => bZ) (fun _ => bZ) := by
  have h := errOK_joh (s.par 0) s.d e bC bZ bZ (Sg.codesOK hs hj.1)
    (by rw [Sg.card_Ps]; exact hj.2) hc.main hc.mask hc.mask
  rwa [Sg.card_Ps] at h

/-- A fold is taken off, at the format's rounds, below the Johnson radius, under the named
hypothesis, in the form in which the blocks are joined. -/
theorem fold_holds_joh (s : Sg) (hs : s.Sized) (e bC bZ : ℕ) (hj : s.InJ e)
    (hc : s.CountsAt e bC bZ) (dE dT : PQ.RD) (na nb : String) (hdE : IsRd dE (Fmt.M1.rEps na))
    (hdT : IsRd dT (Fmt.M1.rTwo nb)) :
    FoldHolds s e dE dT (foldErr s dE dT (fun _ => s.lstJ e) (fun _ => bC) (fun _ => bZ)
      (fun _ => bZ)) :=
  fun t εt G col hno bad hp H =>
    fold_block s s.d e _ _ _ _ (Sg.codesOK hs hj.1) (foldNums_joh hs hj hc) dE dT
      (foldRounds_of hdE hdT) t εt G col hno bad hp H

/-- The numbers of the base case below the Johnson radius, under the named hypothesis. -/
theorem baseCodes_joh {s : Sg} (h : s.Sized) {e bC bZ : ℕ} (hj : s.InJ e)
    (hc : s.CountsAt e bC bZ) : BaseCodes s e (bC + bZ) (s.lstJ e) :=
  ⟨(Sg.fit_cIn h).laws, hc.cIn h, Sg.listJ_of ((Sg.fit_cIn h).il Bool) hj⟩

/-- The base case is taken off, at the format's two rounds, below the Johnson radius, under the
named hypothesis, in the form in which the blocks are joined. -/
theorem base_holds_joh (s : Sg) (h0 : s.h = 0) (g0 : s.g = 0) (hs : s.Sized) (e bC bZ : ℕ)
    (hj : s.InJ e) (hc : s.CountsAt e bC bZ) (dL dB : PQ.RD) (work tree : ℕ)
    (hL : IsRd dL Fmt.M1.rLambda) (hB : IsRd dB (Fmt.M1.rBase work s.st tree)) :
    BaseHolds s e dL dB (baseErr s e (bC + bZ) (s.lstJ e) dL dB) :=
  fun G col mk last hlast hno bad hp H =>
    base_block s h0 g0 e (bC + bZ) (s.lstJ e) dL dB (baseCodes_joh hs hj hc)
      (rLambda_sd hL) (rBase_sd (s := s.st) hB (le_trans hs.small (by decide))) G col mk last hlast
      hno bad hp H

/-- A code switch is taken off, with the next stage's lists by the Johnson bound. It asks no count:
the named hypothesis does not occur. -/
theorem cs_holds_joh {s s' : Sg} (hf : CsFit s s') (hs : s.Sized) (hs' : s'.Sized) (e e' : ℕ)
    (hj : s'.InJ e') {dS dC : PQ.RD} {work tree W : ℕ} (hS : IsRd dS (Fmt.M1.rSeed s'.st))
    (hC : IsRd dC (Fmt.M1.rCs work s.st tree W)) :
    CsHolds s s' e e' dS dC (csErr hf e (s'.lstJ e') dS dC) :=
  cs_block hf e e' (s'.lstJ e') (Sg.fit_cMid hs).laws (Sg.listJ_of (Sg.fit_cIn hs') hj) dS dC
    (csRounds_of hS hC (le_trans hs.small (by norm_num)))

/-- The range of radii is not empty beyond half the distance: at the stage made by hand `mixedSg`
(OnBytes/Slice/BlocksBySource.lean; no file's) the radius 2,400,000 is below the Johnson radius,
twice it is not below the stage's distance, the Johnson bound on a list is 22, and twice the radius
is below the repeated mask code's own distance, so that `Sg.countsAt_of_main` applies. -/
theorem mixed_inJ :
    mixedSg.InJ 2400000 ∧ mixedSg.d ≤ 2 * 2400000 ∧ mixedSg.lstJ 2400000 = 22 ∧
      2 * 2400000 < mixedSg.dZ := by
  unfold Sg.InJ Sg.lstJ InJohnson listMax
  decide +kernel

end OnBytes.Slice
