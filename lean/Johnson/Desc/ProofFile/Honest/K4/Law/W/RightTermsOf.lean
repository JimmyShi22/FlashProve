-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/RightTermsOf.lean: CONDITIONAL.

Not shown here. That the hypotheses hold anywhere: no example is known. THAT THE HONEST SIDE's JOBS
ARE MADE (hS, hJ; StackAt), THAT ITS STRUCTURE OF THE FORMS HAS THE VERIFIER's FOUR FIELDS
(EnvKeys), THAT THE POINTS, THE PANELS AND THE TWO WEIGHTS ARE THE VERIFIER's (TermsAt.part in
right_terms; htT, hrt, hzx in right_terms_of; hp or NamedTie, and hfin, for the back): hypotheses.
WHERE K4Ground IS ASKED THE STATEMENT SPEAKS OF SHAPES WITH ROUTED EXPERTS AND THE LIBRARY's ELEVEN
SWITCHES ALONE (K4Ground.sw), and says nothing at any other shape. By a walk over the files'
imports the closure holds seven modules under Johnson/RecCompile/ (Join, Wire, Pass, CmsGlue,
CmsBcs, Cms, Bcs), through Law/SlotsTrue.lean's imports; none under Johnson/Goal/ or Johnson/D/;
under Johnson/RecCompile/ none of the names Honest…, Both…, PassH…. No property is claimed.

The layers' own rounds (sub-protocol K4), the prover's side: FIVE FIELDS OF THE RIGHT HALF, IN THE
STRUCTURES' OWN TEXTS: rt, sc, sel of OpenedRight, as a term of RightTerms (Law/W/RightAll.lean),
from rt_read, sc_read, sel_read (Johnson/Road/K4/C/TermsField.lean); sideA, sideB, as a term of
OpenedRightBack (Law/W/Halves.lean), from sides_read (Johnson/Road/K4/C/StackSides.lean).

  `pts3 Q w h ds`   the sampled values as the second token sumcheck's job finds them.
  `term_word`      end value number e, as the left half names it, is member e of the job's list.
  **`right_terms`**   RightTerms, from TermsAt.
  **`right_terms_of`**   RightTerms, from the public facts on the layout (K4Ground), the two makers'
      returns and nine further hypotheses.
  **`right_back`**    OpenedRightBack.
  **`right_back_of`**   OpenedRightBack, with six of right_back's premises paid (sides_read_of,
      Johnson/Road/K4/C/StackSidesOf.lean).
  **`right_back_ground`**   OpenedRightBack, from K4Ground, at a world whose entries are entryTrue.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RightAll
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RightStack
import Johnson.Desc.ProofFile.Honest.K4.Law.SkelEnv
import Johnson.Road.K4.C.TermsField
import Johnson.Road.K4.C.TermsAtOf
import Johnson.Road.K4.C.StackSides
import Johnson.Road.K4.C.StackSidesOf
import Johnson.Road.K4.C.NamedPart

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes (E zeroE)
open OnBytes.Model (Reading World HFun HTailF2 Forest.Heard Tsc)
open OnBytes.Model.Layer (Own stackEnd TableAsk TableAt layTables tableAsks funsOf matIx)
open OnBytes.Road (Mats matsR admitted_of_layout)
open OnBytes.Road.K4 (entryOf entryTrue)
open OnBytes.Road.K4.W (K4Ground)
open OnBytes.Road.K4.C (TermsAt termsAt_of rt_read sc_read sel_read sides_ends sides_read
  sides_read_of CellsOn CellsAre PtsPart NamedTie named_part)
open Inst.Model.FFSeg (Dim)
open OnBytes.Desc.First.K4.RtPub (EnvKeys shA_eq)
open OnBytes.Desc.First.K4.Honest

/-- What the honest side's two jobs share, pinned by its full name: under this namespace the bare
name Sides is another structure's. -/
local notation "HSides" => OnBytes.Desc.First.K4.Honest.Sides

/-- The sampled values as the second token sumcheck's job finds them. -/
def pts3 (Q : K4Pub) (w : K4In) (h ds : List Fmt.Drawn) : Pts :=
  ptsOf Q w (h ++ ds.take (rJ3 Q.P Q.g))

variable {Q : K4Pub} {w : K4In} {h ds : List Fmt.Drawn} {o : Own} {Wd : World Cb.Gl.E}
  {r : List TableAt × List (TableAsk × List (Nat × Nat)) × Nat} {fo' : Forest.Heard}
  {pts : List (String × Array E)} {tl : HTailF2} {Mm : Mats Cb.Gl.E} {G : Nat → Prop}
  {funs : Array HFun}

/-- End value number e, as the left half names it, is member e of the job's list. -/
theorem term_word {S : HSides} {J : Job}
    (hS : OnBytes.Desc.First.K4.Honest.Sides.of Q w (pts3 Q w h ds) = some S)
    (hJ : jobTermsOn S = some J) (e : Nat) :
    wTerm Q w h ds e = (J.ends (ownE ds (rJ3 Q.P Q.g + 1) Q.P.y.h.lt)).getD e zeroE := by
  show ((((jobTerms Q w (pts3 Q w h ds)).map
    (·.ends (ownE ds (rJ3 Q.P Q.g + 1) Q.P.y.h.lt))).getD []).getD e zeroE) = _
  unfold jobTerms
  rw [hS]
  show ((((jobTermsOn S).map (·.ends (ownE ds (rJ3 Q.P Q.g + 1) Q.P.y.h.lt))).getD []).getD e
    zeroE) = _
  rw [hJ]
  rfl

/-- **THE FIELDS rt, sc, sel OF OpenedRight.** CONDITIONAL: on every hypothesis named. -/
theorem right_terms {S : HSides} {J : Job}
    (hS : OnBytes.Desc.First.K4.Honest.Sides.of Q w (pts3 Q w h ds) = some S)
    (hJ : jobTermsOn S = some J)
    (A : TermsAt S J (ownE ds (rJ3 Q.P Q.g + 1) Q.P.y.h.lt) Wd r fo' pts tl Mm G funs)
    (K : EnvKeys S.v o.v) (h3 : S.v.y.h.p3 = true) : RightTerms Wd Q o w h ds := by
  obtain ⟨H0, tT0, hH, hE⟩ := sides_ends hS
  refine ⟨fun i hi x hx => ?_, fun lm hl x hx => ?_, fun i hi x hx => ?_⟩
  · rw [term_word hS hJ]
    exact rt_read A hH hE i (by rw [K.y]; exact hi) x (by rw [rowR_eq K]; exact hx)
  · rw [term_word hS hJ, ← K.y]
    exact sc_read A hH hE h3 lm (by rw [K.y]; exact hl) x (by rw [shA_eq K]; exact hx)
  · rw [term_word hS hJ, ← K.y]
    rw [← K.y] at hx
    exact sel_read A hH hE h3 i (by rw [K.y]; exact hi) x (by rw [shA_eq K]; exact hx)

/-- **THE SAME FROM THE PUBLIC FACTS ON THE LAYOUT**, with TermsAt built (termsAt_of,
Johnson/Road/K4/C/TermsAtOf.lean). CONDITIONAL: on every hypothesis named. -/
theorem right_terms_of {hsh : OnBytes.Model.Layer.Shape} {pc : List (List String)} {D : Dim}
    {S : HSides} {J : Job}
    (Gd : K4Ground hsh pc o.v Q.P.rd r tl o.H o.hd o.hd2 pts o.funs D)
    (hS : OnBytes.Desc.First.K4.Honest.Sides.of Q w (pts3 Q w h ds) = some S)
    (hJ : jobTermsOn S = some J) (hy : Q.P.y = o.v.y) (hg : Q.g = o.v.g)
    (hmats : matsOf Q = matsR o.v.y o.v.g)
    (K : EnvKeys S.v o.v) {tT : Tsc} (htT : o.H.tT = some tT)
    (hrt : J.cube.pointOf (ownE ds (rJ3 Q.P Q.g + 1) Q.P.y.h.lt) = tT.r)
    (hzx : (pts3 Q w h ds).fo.zx = o.H.fo.zx) (C : CellsAre Q w Mm)
    (hW : Wd.entry = entryTrue tl o Mm) : RightTerms Wd Q o w h ds :=
  right_terms hS hJ (termsAt_of Gd hS hJ hy hg hmats K htT hrt hzx C hW) K
    (by rw [K.y, (admitted_of_layout Gd.lay Gd.sw.p3).shape]; exact Gd.sw.p3)

/-- **THE FIELDS sideA, sideB.** CONDITIONAL: on every hypothesis named. hfin: the verifier's call
of stackEnd, at the honest side's panels and weights, returns what the verifier holds. -/
theorem right_back {seen : Seen} {SD : StackData} {e : List E}
    (A : StackAt Q w h ds seen o SD e) {fo : Forest.Heard} {pt : List (String × Array E)}
    (hR : readsAt Q w fo pt = some SD.R)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hf : funsOf Q.P.y fo' pts r.2.1 = some funs) (hp : PtsPart pt pts)
    (hfo : (∀ i, G i → i ≠ (matIx Q.P.y).iB) ∨ fo' = fo)
    (hm : (tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (hNM : tl.NM = tl.mats.size)
    (hC : CellsOn G (matsOf Q) w.cell Mm) {H1 V : Array E} {a b : E}
    (hfin : stackEnd SD.S.v.y SD.bl o.K.rs SD.S.Q.hp.lamS SD.om H1 V a b = some o.K.fin)
    (hy : SD.S.v.y = Q.P.y)
    (hW : Wd.entry = entryOf Reading.gl tl funs SD.S.v.iU3 SD.S.v.K3 Mm)
    (hA : ∀ s ∈ o.K.fin.Alin.slots.toList, False) (hB : ∀ s ∈ o.K.fin.Blin.slots.toList, False)
    (hGA : ∀ x ∈ o.K.fin.Alin.ents.toList, ∀ z : HFun × Nat × Nat, z.1 ∈ funs →
      tl.tabAt z.1 z.2.1 z.2.2 = some (x.row * SD.S.v.K3 + x.idx) → G z.1.mat)
    (hGB : ∀ x ∈ o.K.fin.Blin.ents.toList, ∀ z : HFun × Nat × Nat, z.1 ∈ funs →
      tl.tabAt z.1 z.2.1 z.2.2 = some (x.row * SD.S.v.K3 + x.idx) → G z.1.mat) :
    OpenedRightBack Wd Q o w h ds seen := by
  have hE := A.ends
  rw [A.rs] at hE
  obtain ⟨e1, e2⟩ := sides_read hR hl hf hp hfo hm hNM hC hE hfin hW hA hB hGA hGB
  refine ⟨?_, ?_⟩
  · rw [stack_word A 0]
    exact e1
  · rw [stack_word A, show 1 + (1 + Q.P.y.LamM) = 2 + SD.S.v.y.LamM by rw [hy]; omega]
    exact e2

/-- **THE SAME, WITH SIX PREMISES PAID**: the reads are the maker's own; the two forms name no slot;
their entries lie off the matrix of the lookup's planes; nothing is asked of the two looks.
CONDITIONAL: on every hypothesis named. -/
theorem right_back_of {seen : Seen} {SD : StackData} {e : List E}
    (A : StackAt Q w h ds seen o SD e)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hf : funsOf Q.P.y fo' pts r.2.1 = some funs)
    (hp : PtsPart (namedPts Q (pts4 Q w h ds)) pts)
    (hm : (tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (hNM : tl.NM = tl.mats.size)
    (C : CellsAre Q w Mm) {H1 V : Array E} {a b : E}
    (hfin : stackEnd SD.S.v.y SD.bl o.K.rs SD.S.Q.hp.lamS SD.om H1 V a b = some o.K.fin)
    (hy : SD.S.v.y = Q.P.y)
    (hW : Wd.entry = entryOf Reading.gl tl funs SD.S.v.iU3 SD.S.v.K3 Mm) :
    OpenedRightBack Wd Q o w h ds seen := by
  have hE := A.ends
  rw [A.rs] at hE
  obtain ⟨e1, e2⟩ := sides_read_of A.data hl hf hp hm hNM C hE hfin hW
  refine ⟨?_, ?_⟩
  · rw [stack_word A 0]
    exact e1
  · rw [stack_word A, show 1 + (1 + Q.P.y.LamM) = 2 + SD.S.v.y.LamM by rw [hy]; omega]
    exact e2

/-- **THE SAME FROM THE PUBLIC FACTS ON THE LAYOUT**, at a world whose entries are entryTrue, with
the points' premise brought down to nine equations (NamedTie, Johnson/Road/K4/C/NamedPart.lean).
CONDITIONAL: on every hypothesis named. -/
theorem right_back_ground {hsh : OnBytes.Model.Layer.Shape} {pc : List (List String)} {D : Dim}
    {seen : Seen} {SD : StackData} {e : List E}
    (Gd : K4Ground hsh pc o.v Q.P.rd r tl o.H o.hd o.hd2 pts o.funs D)
    (A : StackAt Q w h ds seen o SD e) (hy : Q.P.y = o.v.y) (hg : Q.g = o.v.g)
    (hmats : matsOf Q = matsR o.v.y o.v.g) (K : EnvKeys SD.S.v o.v)
    (N : NamedTie Q (pts4 Q w h ds) o.H o.hd o.hd2) (C : CellsAre Q w Mm) {H1 V : Array E}
    {a b : E}
    (hfin : stackEnd SD.S.v.y SD.bl o.K.rs SD.S.Q.hp.lamS SD.om H1 V a b = some o.K.fin)
    (hW : Wd.entry = entryTrue tl o Mm) : OpenedRightBack Wd Q o w h ds seen := by
  have e0 : entryTrue tl o Mm = entryOf Reading.gl tl o.funs o.v.iU3 o.v.K3 Mm := rfl
  exact right_back_of (fo' := o.H.fo) (funs := o.funs) A (by rw [hmats, hy, hg]; exact Gd.tables)
    (by rw [hy]; exact Gd.funs) (named_part (by rw [hy]; exact Gd.points) N)
    (Gd.mats.trans hmats.symm) Gd.NM C hfin (K.y.trans hy.symm) (by rw [hW, e0, K.iU3, K.K3])

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.term_word
#print axioms ProofFile.Honest.K4.W.right_terms
#print axioms ProofFile.Honest.K4.W.right_terms_of
#print axioms ProofFile.Honest.K4.W.right_back
#print axioms ProofFile.Honest.K4.W.right_back_of
#print axioms ProofFile.Honest.K4.W.right_back_ground
