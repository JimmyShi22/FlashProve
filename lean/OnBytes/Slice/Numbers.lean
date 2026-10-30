-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Numbers.lean: the numbers that the library's proximity blocks ask of the codes of a
stage, at radii below a third of the distance.

The library's blocks take a code as a record (Cb.LdCode) and ask four kinds of facts of it: the laws
(linear, injective, reads what it declares), a distance, a bound on the list of code words near a
word (ListAt), and a bound on the exceptional points of a line (MCAat). The folding asks them in two
records, Spec.CodesOK and SumPar.ErrOK. For every code with the laws and the distance d the library
proves: at most one code word within e positions if 2 e < d, and at most e + 1 exceptional points
if 3 e < d. Laws and distance pass to tables of rows and to codes side by side. This file puts
these facts together for the codes of a stage (OnBytes/Slice/Stage.lean), which are built of single
rows under the format's codes (OnBytes/Slice/LdOfFacts.lean).

Main definitions.
 Fit C d       the code C has the laws and the distance d.
 Sg.Sized      what is asked of a stage's sizes: at most 2^32 positions, a mask code that is not
               longer than the main code, and no more coefficients than positions.
 Sg.d          the distance of a stage: the smaller of the distances of its two codes, the mask
               code's taken as repeated to the main code's length.
Main theorems.
 errOK_third   for every folding: if its three codes meet CodesOK at d and e, and 3 e < d, then
               ErrOK holds with all lists 1 and all counts of exceptional points e + 1.
 Sg.fit_cM, fit_cZ, fit_cIn, fit_cFr, fit_cMid   the codes of a stage have the laws and the distance
               of the stage.
 Sg.codesOK    CodesOK for the main row and the mask row of a stage, for e < d.
 Sg.list_cIn, list_cMid, list_cFr, list_pairs   lists of one code word, for 2 e < d.
 Sg.mca_cIn, mca_cMid   at most e + 1 exceptional points, for 3 e < d.
 toySg1_sized, toySg1_d and their like   the three stages of the small test configuration
               (OnBytes/Slice/ToySg.lean) meet Sized, and their distances are 7618, 8022 and 32216.


Not claimed. Nothing at a radius of a third of the distance or more for the exceptional points, or
of half the distance or more for the lists. Nothing on how many positions of a word are hidden.
Nothing on protocols.
-/
import Cb.Ld.LdBaseCode
import Cb.Ld.LdSumStepStage
import OnBytes.Slice.Stage
import OnBytes.Slice.LdOfFacts
import OnBytes.Slice.ToySg

set_option autoImplicit false

namespace OnBytes.Slice
open Cb Prob

/-! ## Any code with the laws and a distance -/

section
variable {E P : Type} [Field E] [Fintype P]

/-- The code C has the laws and the distance d. -/
structure Fit (C : LdCode E P) (d : ℕ) : Prop where
  /-- encoder and reading are linear, the encoder is injective, the reading is local -/
  laws : C.Laws
  /-- a code word other than 0 is not 0 at d positions or more -/
  dist : C.Dist d

namespace Fit
variable {C C' : LdCode E P} {d : ℕ}

/-- A smaller number is a distance too. -/
theorem mono (h : Fit C d) {d' : ℕ} (hd : d' ≤ d) : Fit C d' :=
  ⟨h.laws, fun m r hmr => hd.trans (h.dist m r hmr)⟩

/-- Tables of rows under the code. -/
theorem il (h : Fit C d) (R : Type) [Fintype R] [DecidableEq R] : Fit (C.il R) d :=
  ⟨ld_laws_il E P C R h.laws, ld_dist_il E P C R d h.dist⟩

/-- Two codes side by side. -/
theorem pair (h : Fit C d) (h' : Fit C' d) : Fit (C.pair C') d :=
  ⟨ld_laws_pair E P C C' h.laws h'.laws, ld_dist_pair E P C C' d h.dist h'.dist⟩

variable [Fintype E]

/-- The list below half the distance: at most one code word is within e positions of a word. -/
theorem list (h : Fit C d) {e : ℕ} (h2 : 2 * e < d) : C.ListAt e 1 :=
  ld_list_unique E P C d e h.laws h.dist h2

/-- Agreement below a third of the distance: a line has at most e + 1 exceptional points. -/
theorem mca (h : Fit C d) {e : ℕ} (h3 : 3 * e < d) : C.MCAat e (e + 1) :=
  ld_mca_third E P C d e h.laws h.dist h3

end Fit

variable [Fintype E]

/-- The numbers of a folding below a third of the distance. If the three codes of the folding Y
have the laws and the distance d, then at a radius e with 3 e < d every stage has lists of one code
word, and every halving of each of the three tables has at most e + 1 exceptional points. -/
theorem errOK_third (Y : SumPar E P) (d e : ℕ) (h : Spec.CodesOK E P Y.C Y.Z Y.Zw d e)
    (h3 : 3 * e < d) :
    Y.ErrOK e (fun _ => 1) (fun _ => e + 1) (fun _ => e + 1) (fun _ => e + 1) :=
  have hC : Fit Y.C d := ⟨h.1.1, h.2.1.1⟩
  have hZ : Fit Y.Z d := ⟨h.1.2.1, h.2.1.2.1⟩
  have hW : Fit Y.Zw d := ⟨h.1.2.2, h.2.1.2.2⟩
  have h2 : 2 * e < d := by omega
  { list := fun _ _ => ((hC.il _).pair ((hZ.il _).pair (hW.il _))).list h2
    mcaC := fun _ _ _ => (hC.il _).mca h3
    mcaS := fun _ _ _ => (hZ.il _).mca h3
    mcaW := fun _ _ _ => (hW.il _).mca h3 }

end

/-! ## One row under a code of the format -/

/-- The distance of one row, read at as many positions as the code has. -/
theorem ldOf_dist_at (C : Fmt.M1.Code) (a : ℕ) (h : C.a = a) (ha : a ≤ 32)
    (hk : C.r + C.l ≤ 2 ^ a) : (ldOf C a).Dist (2 ^ a - (C.r + C.l) + 1) := by
  subst h
  exact ldOf_dist C ha hk

/-- One row under a code of the format, read at as many positions as the code has (C.a = a), has the
laws and the distance 2^a - (C.r + C.l) + 1, if a ≤ 32 and C.r + C.l ≤ 2^a. -/
theorem fit_ldOf (C : Fmt.M1.Code) (a : ℕ) (h : C.a = a) (ha : a ≤ 32) (hk : C.r + C.l ≤ 2 ^ a) :
    Fit (ldOf C a) (2 ^ a - (C.r + C.l) + 1) :=
  ⟨ldOf_laws C a (h ▸ ha) (h ▸ hk), ldOf_dist_at C a h ha hk⟩

/-- One row under a code of the format, repeated to a group's length (C.a ≤ a), has the laws and the
distance 2^C.a - (C.r + C.l) + 1, times the 2^(a - C.a) copies, if C.a ≤ 32 and the code has room
for C.r + C.l symbols (C.r + C.l ≤ 2^C.a). -/
theorem fit_ldRep (C : Fmt.M1.Code) (a : ℕ) (h : C.a ≤ a) (ha : C.a ≤ 32)
    (hk : C.r + C.l ≤ 2 ^ C.a) : Fit (ldRep C a) (2 ^ (a - C.a) * (2 ^ C.a - (C.r + C.l) + 1)) :=
  ⟨ldRep_laws C a h ha hk, ldRep_dist C a h ha hk⟩

/-! ## The codes of a stage -/

namespace Sg

/-- What is asked of a stage's sizes. -/
structure Sized (s : Sg) : Prop where
  /-- the points of the code are different -/
  small : s.C.a ≤ 32
  /-- the mask rows are not longer than the main rows -/
  short : s.Z.a ≤ s.C.a
  /-- a main row has no more coefficients than positions -/
  roomC : s.C.r + s.C.l ≤ 2 ^ s.C.a
  /-- a mask row has no more coefficients than positions -/
  roomZ : s.Z.r + s.Z.l ≤ 2 ^ s.Z.a

/-- The distance of a main row. -/
def dC (s : Sg) : ℕ := 2 ^ s.C.a - (s.C.r + s.C.l) + 1

/-- The distance of a mask row, repeated to the main rows' length. -/
def dZ (s : Sg) : ℕ := 2 ^ (s.C.a - s.Z.a) * (2 ^ s.Z.a - (s.Z.r + s.Z.l) + 1)

/-- The distance of a stage: the smaller of the two. -/
def d (s : Sg) : ℕ := min s.dC s.dZ

variable {s : Sg}

/-- One main row. -/
theorem fit_cM (h : s.Sized) : Fit s.cM s.d :=
  (fit_ldOf s.C s.C.a rfl h.small h.roomC).mono (Nat.min_le_left _ _)

/-- One mask row. -/
theorem fit_cZ (h : s.Sized) : Fit s.cZ s.d :=
  (fit_ldRep s.Z s.C.a h.short (h.short.trans h.small) h.roomZ).mono (Nat.min_le_right _ _)

/-- The tables before the fold. -/
theorem fit_cIn (h : s.Sized) : Fit s.cIn s.d := ((fit_cM h).il _).pair ((fit_cZ h).il _)

/-- The fresh mask rows. -/
theorem fit_cFr (h : s.Sized) : Fit s.cFr s.d := (fit_cZ h).il _

/-- The three folded rows. -/
theorem fit_cMid (h : s.Sized) : Fit s.cMid s.d := (fit_cM h).pair ((fit_cZ h).pair (fit_cZ h))

/-- What a folding asks of its three codes: the main row, the mask row, and the mask row once
more for the fresh mask. -/
theorem codesOK (h : s.Sized) {e : ℕ} (he : e < s.d) :
    Spec.CodesOK GE s.Ps s.cM s.cZ s.cZ s.d e :=
  ⟨⟨(fit_cM h).laws, (fit_cZ h).laws, (fit_cZ h).laws⟩,
    ⟨(fit_cM h).dist, (fit_cZ h).dist, (fit_cZ h).dist⟩, he⟩

/-- The list of the tables before the fold. -/
theorem list_cIn (h : s.Sized) {e : ℕ} (h2 : 2 * e < s.d) : s.cIn.ListAt e 1 := (fit_cIn h).list h2

/-- The list of the fresh mask rows. -/
theorem list_cFr (h : s.Sized) {e : ℕ} (h2 : 2 * e < s.d) : s.cFr.ListAt e 1 := (fit_cFr h).list h2

/-- The list of the three folded rows. -/
theorem list_cMid (h : s.Sized) {e : ℕ} (h2 : 2 * e < s.d) : s.cMid.ListAt e 1 :=
  (fit_cMid h).list h2

/-- The list of pairs of tables, which the base case asks. -/
theorem list_pairs (h : s.Sized) {e : ℕ} (h2 : 2 * e < s.d) : (s.cIn.il Bool).ListAt e 1 :=
  ((fit_cIn h).il Bool).list h2

/-- The exceptional points of a line of tables before the fold. -/
theorem mca_cIn (h : s.Sized) {e : ℕ} (h3 : 3 * e < s.d) : s.cIn.MCAat e (e + 1) :=
  (fit_cIn h).mca h3

/-- The exceptional points of a line of triples of folded rows. -/
theorem mca_cMid (h : s.Sized) {e : ℕ} (h3 : 3 * e < s.d) : s.cMid.MCAat e (e + 1) :=
  (fit_cMid h).mca h3

end Sg

/-! ## The three stages of the small test configuration -/

/-- The first stage meets what is asked of a stage's sizes. -/
theorem toySg1_sized : toySg1.Sized := ⟨by decide, by decide, by decide, by decide⟩

/-- The second stage meets what is asked of a stage's sizes. -/
theorem toySg2_sized : toySg2.Sized := ⟨by decide, by decide, by decide, by decide⟩

/-- The third stage meets what is asked of a stage's sizes. -/
theorem toySg3_sized : toySg3.Sized := ⟨by decide, by decide, by decide, by decide⟩

/-- The distance of the first stage: 2^13 - 575 + 1, that of its main rows. -/
theorem toySg1_d : toySg1.d = 7618 := by decide

/-- The distance of the second stage: 2^13 - 171 + 1, that of both kinds of rows. -/
theorem toySg2_d : toySg2.d = 8022 := by decide

/-- The distance of the third stage: 2^15 - 553 + 1, that of its mask row. -/
theorem toySg3_d : toySg3.d = 32216 := by decide

end OnBytes.Slice

#print axioms OnBytes.Slice.errOK_third
#print axioms OnBytes.Slice.Sg.codesOK
#print axioms OnBytes.Slice.Sg.list_cIn
#print axioms OnBytes.Slice.Sg.list_cFr
#print axioms OnBytes.Slice.Sg.list_cMid
#print axioms OnBytes.Slice.Sg.list_pairs
#print axioms OnBytes.Slice.Sg.mca_cIn
#print axioms OnBytes.Slice.Sg.mca_cMid
#print axioms OnBytes.Slice.toySg1_sized
#print axioms OnBytes.Slice.toySg2_sized
#print axioms OnBytes.Slice.toySg3_sized
#print axioms OnBytes.Slice.toySg1_d
#print axioms OnBytes.Slice.toySg2_d
#print axioms OnBytes.Slice.toySg3_d
