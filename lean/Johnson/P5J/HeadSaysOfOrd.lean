--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/HeadSaysOfOrd.lean: THE WAY BACK AT THE LOOKUP ON THE OUTPUT HEAD's CALLS, FROM THE
INTEGER MODEL's RECORD OF THE HEAD: where the list of integer matrices that is read off a tuple of
messages meets `Hd.HeadOrdLB` (Johnson/Road/HeadL5BL.lean), and the committed matrix of weights is
read as an index's, the joint in front of the lookup says of these messages, at the token, what it
asks (`HeadSays`, Johnson/Desc/First/Look/K3HeadGoodIn.lean), at the library's own map of the head's
cells (`adrOf`). Statements and proofs. NO ACCEPTANCE OF ANY TEXT THAT RUNS IS CLAIMED.

Why. Whoever writes the honest side takes, in front of each lookup, the right side of the joint at
every tuple of messages. For the layers and attention it follows from the meaning's
clauses on keys. The meaning's clause on the head is a conclusion without a list; the list stands in
`Hd.HeadOrdLB`, whose second clause is the landed Policy.HeadCl.

Main names.
  `listCells h L b Mz W`: the kind's record of cells of a list Mz and a matrix of weights W: the
    library's `Hd.cellsH`, and the output matrix that the layout reads in W.
  `same_listCells`: it agrees with the caller's cells inside the ranges, where the messages are read
    as Mz (MatsAre; every entry below 2^18) and as the index's matrix.
  `says_of_ord`: THE STATEMENT. `says_of_ord_agree`: the same where the record holds of another list
    that agrees with Mz within the four ranges of Hd.SmallH (`Meaning.AgreeH`): a list that is not
    cut to the sizes, as the library's honest trace's.

How. Johnson/Desc/Kinds/Law/LibBackWhole.lean (nine_of_headCl) at listCells;
Johnson/P5J/HeadSaysBack.lean (says_of_same).

Limits. ONE WAY. PREMISES THAT NOBODY PAYS HERE. On public data: six calls; `HeadTabs`; the test on
the request; y < V; Same, Wide, More at the request's record; the table off the rows of call 3 is
the library's EX on 16 bits; the normalisation's three numbers in the record are the kind's (npOf):
none is paid here. On the messages: MatsAre IS AN EQUATION AT ALL NUMBERS (it forces Mz to be 0
outside the sizes of tl and fixes the matrix of the planes too); every entry of Mz is below 2^18;
the caller's entry (a, b) of the committed matrix is the cast of the index's AT EVERY a AND b. That
all premises hold together is not shown here. The full size alone. The joint is the base joint's
right side, at the decoded messages. The proved lookup block has no honest side.
Not claimed: anything on completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.HeadSaysBack
import Johnson.Desc.Kinds.Law.LibBackWhole
import Johnson.Goal.Meaning.HidHeadCongr
import Johnson.Road.HeadTabL
import Inst.Model.All.NoWrap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes (E okE OracleShape)
open OnBytes.Model (HTailF2)
open OnBytes.Model.Head (HL Border)
open OnBytes.Model.Verify (borderOf)
open OnBytes.Road (Mats)
open Inst.Model (ppref AcceptancePolicy Mat Instance)
open VerifiableInference.Desc.Kinds.Head VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Desc.Kinds.HeadJoin (Same Wide More cellsN)
open VerifiableInference.Desc.Kinds.Norm (lt ls d S2 T)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First.Look

/-- The kind's record of cells, of a list of integer matrices and a matrix of weights. -/
def listCells (h : OnBytes.Model.Head.Shape) (L : HL) (b : Border) (Mz : Mats ℤ) (W : Mat) :
    NCells where
  cell := fun M φ i =>
    match M with
    | .wide => (OnBytes.Road.Hd.cellsH h L b Mz).hf φ i
    | .act => (OnBytes.Road.Hd.cellsH h L b Mz).hd φ i
    | .row => (OnBytes.Road.Hd.cellsH h L b Mz).hr φ i
  Wh := (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef W).H
  stream := (OnBytes.Road.Hd.cellsH h L b Mz).x

/-- The library's record made of these cells is the library's own. -/
theorem cellsN_listCells (h : OnBytes.Model.Head.Shape) (L : HL) (b : Border) (Mz : Mats ℤ)
    (W : Mat) : cellsN (listCells h L b Mz W) = OnBytes.Road.Hd.cellsH h L b Mz := rfl

variable [Sizes] [Policy] [Request]
variable {h : OnBytes.Model.Head.Shape} {L : HL} {ly : OnBytes.Model.Layer.Lay}
  {x : VerifiableInference.Desc.First.Look.Place} {sT : ℕ} {tl : HTailF2} {D : Sent}
  {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E}
  {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ} {y : ℕ} {m : (laySg x D rad oW).Msg}
  {pol : AcceptancePolicy} {i : Cm.Idx} {xq : Instance ppref} {Mz Mh : Mats ℤ}

/-- **These cells agree with the caller's inside the ranges.** -/
theorem same_listCells (b : Border) (Wd : Wide) (hM : MatsAre x tl D rad oW wOf nr nc m Mz)
    (hs : ∀ a r c, |Mz a r c| < 2 ^ 18)
    (hW : ∀ a b, wOfE (msgLay x tl D rad oW wOf nr nc m) a b = ((i.mat a b : ℤ) : Cb.Gl.E)) :
    SameCells (listCells h L b Mz i.mat)
      (headCells (adrOf h L b) x tl D rad oW wOf nr nc m) := by
  obtain ⟨c1, c2⟩ := head_cells_cast (adr := adrOf h L b) m Mz hM hs
  refine ⟨fun f t _ _ => (c1 .wide f t).symm, fun f t _ _ => (c1 .act f t).symm,
    fun f t _ _ => (c1 .row f t).symm, fun f t _ _ => (c2 f t).symm, fun k v hk hv => ?_⟩
  have hk' : k < 5120 := by rw [← Wd.d]; exact hk
  have hv' : v < 202048 := by rw [← Wd.V]; exact hv
  have e : (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef i.mat).H k v =
      Inst.Model.Head.Hof i.mat k v := Inst.Model.Head.Hof_weightsOf i.mat hk' hv'
  have hb : |Inst.Model.Head.Hof i.mat k v| ≤ 2 ^ 12 := by
    rw [← e]
    exact Inst.Model.All.abs_H i.wf k v
  rw [head_wh_cast (adr := adrOf h L b) m i.mat (hW _ _) (hW _ _) hb]
  exact e

/-- **WHAT THE JOINT IN FRONT SAYS, FROM THE INTEGER MODEL's RECORD OF THE HEAD.** -/
theorem says_of_ord (six : x.fs.NC = 6) (HT : HeadTabs x sT) (hreq : Request.ok = true)
    (hy : y < V) (S : Same (Inst.Model.Head.Req.of pol xq)) (Wd : Wide)
    (M : letI : Token := ⟨y⟩
      More (Inst.Model.Head.Req.of pol xq))
    (htab : ∀ u, u < 2 ^ 16 → (tabOf (rowH x) u : Int) = Inst.Model.EX u)
    (O : OnBytes.Road.Hd.HeadOrdLB h L ly npOf pol i.mat xq Mz)
    (hM : MatsAre x tl D rad oW wOf nr nc m Mz) (hs : ∀ a r c, |Mz a r c| < 2 ^ 18)
    (hW : ∀ a b, wOfE (msgLay x tl D rad oW wOf nr nc m) a b = ((i.mat a b : ℤ) : Cb.Gl.E)) :
    HeadSays (adrOf h L (borderOf ly)) x tl D rad oW wOf nr nc y m := by
  letI : Token := ⟨y⟩
  obtain ⟨keys, guests⟩ := Came.nine_of_headCl sT (tabOf (rowH x))
    (listCells h L (borderOf ly) Mz i.mat) pol i.mat xq HT.plan hreq hy S Wd M htab rfl
    (OnBytes.Road.Hd.small_cellsHL h L (borderOf ly) hs) O.2.1
  exact says_of_same six HT hreq hy _ (same_listCells (borderOf ly) Wd hM hs hW) keys guests

/-- **The same where the record holds of a list that agrees with Mz within the four ranges.** -/
theorem says_of_ord_agree (N : OnBytes.Road.Hd.NumH h L)
    (Bd : OnBytes.Road.Hd.BorderH (borderOf ly)) (six : x.fs.NC = 6) (HT : HeadTabs x sT)
    (hreq : Request.ok = true) (hy : y < V) (S : Same (Inst.Model.Head.Req.of pol xq))
    (Wd : Wide)
    (M : letI : Token := ⟨y⟩
      More (Inst.Model.Head.Req.of pol xq))
    (htab : ∀ u, u < 2 ^ 16 → (tabOf (rowH x) u : Int) = Inst.Model.EX u)
    (O : OnBytes.Road.Hd.HeadOrdLB h L ly npOf pol i.mat xq Mh)
    (A : Meaning.AgreeH h L (borderOf ly) Mh Mz)
    (hM : MatsAre x tl D rad oW wOf nr nc m Mz) (hs : ∀ a r c, |Mz a r c| < 2 ^ 18)
    (hW : ∀ a b, wOfE (msgLay x tl D rad oW wOf nr nc m) a b = ((i.mat a b : ℤ) : Cb.Gl.E)) :
    HeadSays (adrOf h L (borderOf ly)) x tl D rad oW wOf nr nc y m :=
  says_of_ord six HT hreq hy S Wd M htab (Meaning.headOrd_congr N Bd A O) hM hs hW

end P5J

#print axioms P5J.cellsN_listCells
#print axioms P5J.same_listCells
#print axioms P5J.says_of_ord
#print axioms P5J.says_of_ord_agree
