-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadDict.lean: one dictionary for the library's family of matrices, with the verifier's
matrices named by the labels of its plans: the output head's labels, and the seam before the head.

The library's model speaks of one family of integer matrices, indexed by (segment, row, column). The
verifier has a list of matrices for each sub-proof, and its plans give each entry of a list a label
(the field aId of a record TMat). A matrix that a sub-proof borrows bears its owner's label.
Johnson/Road/FormsKeysDictA.lean has a formula for the labels of the layer sub-proofs (labA) and
fills the feed-forward segments from matrices that are named by labels (libOfA). This file does the
same for the head's sub-proof, and puts both into one definition.

Main definitions, all of this file.
 - labH: the label of entry n of the head's list: 256 (1 + NGr) + n; but for the borrowed stream,
   entry NHf + 3, the label that labA gives the stream which goes out of the last group.
 - mzH: the head's list, from matrices Z that are named by labels.
 - D5: the library's family from matrices Z that are named by labels: segment 24 from labH, the even
   segments below it from labA, the odd segments from a letter At.

What is compared with what.
 - bordersOf_labels, planG_mats, planG_labels, plansFrom_length, plan_labels, last_label: texts of
   the verifier with each other (bordersOf, planG, plansG against tailsOf, all in
   OnBytes/Model/LayerPlan.lean): a plan's list has the labels of the list of tailsOf.
 - matsH_own, labH_mats, public_plans, labH_of_public: the formula labH against the verifier's own
   matsH, planH2, ownerOf (OnBytes/Model/HeadPlan.lean, OnBytes/Model/VerifyPublic.lean).
 - labH_lent: labH at the borrowed entry against the layers' formula labA.
 - D5_24, D5_even, D5_libOfA, D5_headMx_24, D5_headMx_22: definitions of these files with each
   other.
 - lentH_D5: the hypothesis LentH of Johnson/Road/HeadPlace.lean holds of matrices that are named by
   labels, because the two matrices have one label.
 - link24_D5: the library's conditions on segment 24 at D5 against keys and identities at the cells
   that the verifier's rule reads in the matrices with the head's labels (HeadOrd,
   Johnson/Road/HeadL5.lean).
 - seam_D5: two families D5 agree on a slot of an even segment if their matrices agree at one label.

The hypotheses. The labels: the verifier's functions return; hf has four parts. link24_D5: those of
Johnson/Road/HeadL5.lean's link24_iff, and twelve groups of layers. At the full-size example alone.

Which value is which: labels are public numbers; the entries of Z are hidden values, here any
integers.

What is not claimed. That a matrix which bears another sub-proof's label is the matrix to which the
owner committed: how the smallness test ties the two is not looked at. The labels of attention's
matrices are not looked at: At is a letter. Past a matrix's own rows and columns, and in the slots
from 6 on of segment 24 and from 8 on of an even segment, D5 holds whatever Z holds at the label
that the formula names, not 0. The program does not import this file.
-/
import Johnson.Road.HeadL5
import Johnson.Road.HeadMade
import Johnson.Road.FormsKeysDictA

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model (ppref Instance Mat)
open Inst.Model.All (DF)
open OnBytes.Model (TMat T2Foreign HTailF2 Settings)
open OnBytes.Model.Layer (Lay Pub HPlan2 Scales bordersOf planG plansFrom plansG tailsOf matIx)
open OnBytes.Model.Head (HL Border Owner HPlanH2 matsH planH2)
open OnBytes.Model.Verify (Public publicOf borderOf ownerOf)

/-! ## The labels in the plans of the layer sub-proofs -/

/-- bordersOf keeps the matrices' order, number and labels. -/
theorem bordersOf_labels {y : Lay} {ms : Array TMat}
    {r : Array TMat × Array (Option ℕ) × Array T2Foreign} (h : bordersOf y ms = .ok r) :
    (r.1.map fun M => M.aId) = ms.map fun M => M.aId := by
  unfold bordersOf at h
  obtain ⟨-, h⟩ := ok_of_refuse h
  have e := (Except.ok.inj h).symm
  subst e
  have H : ∀ (l : List (TMat × ℕ))
      (s : Array TMat × Array (Option ℕ) × Array T2Foreign × ℕ),
      ((l.foldl (fun (s : Array TMat × Array (Option ℕ) × Array T2Foreign × ℕ) x =>
        if (x.1.kind == 0 && (x.2 == (Model.Layer.matIx y).iXO ||
            (y.h.p4 && x.2 == (Model.Layer.matIx y).iQA))) = true then
          (s.1.push x.1, s.2.1.push (some s.2.2.2), s.2.2.1, s.2.2.2 + 1)
        else if (x.1.kind == 1) = true then
          (s.1.push { x.1 with foreign := some s.2.2.1.size, ttOff := 0 }, s.2.1.push none,
           s.2.2.1.push { name := "PXf" ++ toString s.2.2.1.size, K := x.1.k, a := 2, m := x.1.m,
                          wp := x.1.wp }, s.2.2.2)
        else (s.1.push x.1, s.2.1.push none, s.2.2.1, s.2.2.2)) s).1.toList.map
          fun M => M.aId) =
        (s.1.toList.map fun M => M.aId) ++ l.map fun x => x.1.aId := by
    intro l
    induction l with
    | nil =>
      intro s
      simp
    | cons x l ih =>
      intro s
      rw [List.foldl_cons, ih]
      split_ifs <;> simp
  have h1 := H ms.toList.zipIdx (#[], #[], #[], 0)
  apply Array.ext'
  rw [Array.toList_map, Array.toList_map]
  refine Eq.trans h1 ?_
  have h2 : (ms.toList.zipIdx.map fun x => x.1.aId) =
      (ms.toList.zipIdx.map (·.1)).map fun M => M.aId := by
    rw [List.map_map]
    rfl
  rw [h2, List.zipIdx_map_fst]
  simp

/-- The list of matrices in the plan of group g is what bordersOf makes of the list that the public
numbers hold for the group. -/
theorem planG_mats {P : Pub} {g : ℕ} {O : Option HPlan2} {hp : HPlan2}
    (h : planG P g O = .ok hp) :
    ∃ b, bordersOf P.y (P.tails.getD g {}).mats = .ok b ∧ hp.tl.mats = b.1 := by
  unfold planG at h
  obtain ⟨b, hb, h⟩ := ok_of_bind h
  obtain ⟨t1, h1, h⟩ := ok_of_bind h
  obtain ⟨a, ha, h⟩ := ok_of_bind h
  obtain ⟨Tp, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_refuse h
  obtain ⟨s1, -⟩ := shape_mats h1
  obtain ⟨a1, -⟩ := addTrees_keeps ha
  have k2 : hp.tl.mats = a.1.mats := by
    cases O with
    | none =>
      obtain ⟨-, h⟩ := ok_of_refuse h
      obtain ⟨-, h⟩ := ok_of_refuse h
      have e := (Except.ok.inj h).symm
      subst e
      rfl
    | some O =>
      cases hb2 : O.tl.ix.TX.back? with
      | none =>
        simp only [hb2] at h
        have h' : (Except.error "internal-g-owner-shape" : Except String HPlan2) = .ok hp := h
        cases h'
      | some t =>
        simp only [hb2] at h
        obtain ⟨-, h⟩ := ok_of_refuse h
        obtain ⟨-, h⟩ := ok_of_refuse h
        obtain ⟨t3, h3, h⟩ := ok_of_bind h
        obtain ⟨pe, -, h⟩ := ok_of_bind h
        obtain ⟨-, h⟩ := ok_of_refuse h
        obtain ⟨-, h⟩ := ok_of_refuse h
        have e := (Except.ok.inj h).symm
        subst e
        exact (borderMeans_keeps h3).1
  exact ⟨b, hb, by rw [k2, a1, s1]⟩

/-- So it has that list's labels, in order. -/
theorem planG_labels {P : Pub} {g : ℕ} {O : Option HPlan2} {hp : HPlan2}
    (h : planG P g O = .ok hp) :
    (hp.tl.mats.map fun M => M.aId) = (P.tails.getD g {}).mats.map fun M => M.aId := by
  obtain ⟨b, hb, e⟩ := planG_mats h
  rw [e]
  exact bordersOf_labels hb

/-- plansFrom returns as many plans as it is asked for. -/
theorem plansFrom_length (P : Pub) : ∀ (n g : ℕ) (O : Option HPlan2) (l : List HPlan2),
    plansFrom P n g O = .ok l → l.length = n
  | 0, g, O, l, h => by
    have e : l = [] := (Except.ok.inj h).symm
    rw [e]
    rfl
  | n + 1, g, O, l, h => by
    unfold plansFrom at h
    obtain ⟨p, -, h⟩ := ok_of_bind h
    obtain ⟨rest, hr, h⟩ := ok_of_bind h
    have e : l = p :: rest := (Except.ok.inj h).symm
    rw [e, List.length_cons, plansFrom_length P n (g + 1) (some p) rest hr]

/-- In the plans that plansG returns for the public numbers of the layout y there is one plan for
each group, and the list of matrices in the plan of group g has the labels of the list of tailsOf.
-/
theorem plan_labels {y : Lay} {sc : Scales} {rope : Array ℕ} {wsLay : Model.WsLay} {V : ℕ}
    {tokv : Array ℕ} {set : Settings} {P : Pub} (hP : Pub.of y sc rope wsLay V tokv set = .ok P)
    {G : Array HPlan2} (hG : plansG P = .ok G) :
    G.size = y.NGr ∧ ∀ g hp, G[g]? = some hp →
      (hp.tl.mats.map fun M => M.aId) = ((tailsOf y).getD g {}).mats.map fun M => M.aId := by
  unfold Pub.of at hP
  obtain ⟨-, hP⟩ := ok_of_refuse hP
  obtain ⟨rd, -, hP⟩ := ok_of_bind hP
  have e := (Except.ok.inj hP).symm
  subst e
  unfold plansG at hG
  obtain ⟨l, hl, hG⟩ := ok_of_bind hG
  have e := (Except.ok.inj hG).symm
  subst e
  refine ⟨?_, fun g hp hg => ?_⟩
  · have k := plansFrom_length _ _ _ _ _ hl
    simpa using k
  · have hg' : l[g]? = some hp := by simpa using hg
    obtain ⟨O', hO⟩ := plansFrom_at _ _ 0 none l hl g hp hg'
    rw [Nat.zero_add] at hO
    exact planG_labels hO

/-- A member of an array, from the images of the array's members. -/
theorem label_at {a b : Array TMat} (h : (a.map fun M => M.aId) = b.map fun M => M.aId) {n : ℕ}
    {M : TMat} (hn : a[n]? = some M) : (b.getD n {}).aId = M.aId := by
  have k0 := congrArg (fun z : Array ℕ => z[n]?) h
  have k : (a[n]?).map (fun M => M.aId) = (b[n]?).map (fun M => M.aId) := by simpa using k0
  rw [hn] at k
  cases hb : b[n]? with
  | none =>
    rw [hb] at k
    cases k
  | some N =>
    rw [hb] at k
    have e : b.getD n {} = N := by simp [Array.getD_eq_getD_getElem?, hb]
    have e2 : M.aId = N.aId := Option.some.inj k
    rw [e, e2]

/-- **The label of the stream that goes out of the last group**, in the last plan's own list, is the
one that the layers' formula gives. -/
theorem last_label {y : Lay} {sc : Scales} {rope : Array ℕ} {wsLay : Model.WsLay} {V : ℕ}
    {tokv : Array ℕ} {set : Settings} {P : Pub} (hP : Pub.of y sc rope wsLay V tokv set = .ok P)
    {G : Array HPlan2} (hG : plansG P = .ok G) {Pl : HPlan2} (hb : G.back? = some Pl)
    {stream : TMat} (hs : Pl.tl.mats[firstM y 5]? = some stream) :
    stream.aId = labA y (y.NGr - 1) (matIx y).iXO := by
  obtain ⟨hsz, hall⟩ := plan_labels hP hG
  have hb' : G[G.size - 1]? = some Pl := hb
  have hpos : 0 < G.size := by
    by_contra hn
    have e0 : G = #[] := Array.eq_empty_of_size_eq_zero (by omega)
    rw [e0] at hb'
    simp at hb'
  rw [hsz] at hb' hpos
  have k := label_at (hall _ _ hb') hs
  rw [← k]
  exact labA_tails y (by omega) (by
    show y.parts.getD 0 0 + y.parts.getD 1 0 + 3 < y.parts.getD 0 0 + y.parts.getD 1 0 + 5
    omega)

/-! ## The head's labels -/

/-- The label of entry n of the list of matrices of the head's sub-proof: 256 (1 + NGr) + n; but for
the borrowed stream, entry NHf + 3, the label of the stream that goes out of the last group of
layers. -/
def labH (h : Model.Head.Shape) (y : Lay) (n : ℕ) : ℕ :=
  if n = h.NHf + 3 then labA y (y.NGr - 1) (matIx y).iXO else (1 + y.NGr) * 256 + n

/-- The labels of the head's own matrices in the list matsH, for hf in four parts. -/
theorem matsH_own {h : Model.Head.Shape} (L : HL) (b : Border) (gid sid : ℕ) (hN : h.NHf = 4)
    {n : ℕ} (hn : n < 7) : ((matsH h L b gid sid).getD n {}).aId = gid * 256 + n := by
  have c : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
  unfold Model.Head.matsH
  rw [hN]
  rcases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- **labH is the label that the verifier's plan gives.** G: the plans that plansG returns for the
public numbers of the layout y; O: what ownerOf makes of them; hp: what planH2 returns on O and the
number of groups of y. For hf in four parts. -/
theorem labH_mats {y : Lay} {sc : Scales} {rope : Array ℕ} {wsLay : Model.WsLay} {V : ℕ}
    {tokv : Array ℕ} {set : Settings} {P : Pub} (hP : Pub.of y sc rope wsLay V tokv set = .ok P)
    {G : Array HPlan2} (hG : plansG P = .ok G) {O : Owner} (hO : ownerOf y G = .ok O)
    {g : Settings} {h : Model.Head.Shape} {L : HL} {b : Border} {lkW : ℕ} {hp : HPlanH2}
    (hpl : planH2 g h L b O y.NGr lkW = .ok hp) (hN : h.NHf = 4) {n : ℕ} (hn : n < h.NHf + 4) :
    (hp.tl.mats.getD n {}).aId = labH h y n := by
  unfold labH
  by_cases e : n = h.NHf + 3
  · rw [if_pos e, e]
    obtain ⟨Pl, stream, hb, hs, a1, -, -⟩ := lent_label hO hpl hN
    rw [a1]
    exact last_label hP hG hb hs
  · rw [if_neg e]
    obtain ⟨stream, -, hm⟩ := planH2_label hpl
    rw [hm]
    exact matsH_own L b (1 + y.NGr) stream.aId hN (by omega)

/-- With twelve groups of layers the head's borrowed matrix bears the label that the layers' formula
gives the stream which goes out of group 11. -/
theorem labH_lent (h : Model.Head.Shape) {y : Lay} (h12 : y.NGr = 12) :
    labH h y (h.NHf + 3) = labA y 11 (matIx y).iXO := by
  have e : labH h y (h.NHf + 3) = labA y (y.NGr - 1) (matIx y).iXO := if_pos rfl
  have e2 : y.NGr - 1 = 11 := by omega
  rw [e, e2]

/-- Two more lines of the verifier's public part, on its own results: the layers' public numbers are
what Pub.of returns on the layout, and the plans of the groups are what plansG returns on them. -/
theorem public_plans {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOf pol KL lay = .ok X) :
    ∃ sc rope wsLay V tokv set, Pub.of X.y sc rope wsLay V tokv set = .ok X.layers ∧
      plansG X.layers = .ok X.G := by
  unfold Model.Verify.publicOf at h
  obtain ⟨⟨P, y⟩, hpl, h⟩ := ok_of_bind h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨_, h⟩ := ok_of_either h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨⟨A0, hCallsA⟩, h⟩ := ok_of_either2 h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  cases h
  obtain ⟨e1, -⟩ := pub_fields (by assumption)
  unfold Model.Verify.Public.y
  dsimp only
  rw [e1]
  exact ⟨_, _, _, _, _, _, by assumption, by assumption⟩

/-- **In what the public part returns, the head's list has the labels labH.** -/
theorem labH_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOf pol KL lay = .ok X) (hN : X.hS.NHf = 4) {n : ℕ} (hn : n < X.hS.NHf + 4) :
    (X.H.tl.mats.getD n {}).aId = labH X.hS X.y n := by
  obtain ⟨sc, rope, wsLay, V, tokv, set, hP, hG⟩ := public_plans h
  have A := publicH_of_public h
  obtain ⟨H0, hH, e⟩ := A.plan
  rw [e]
  exact labH_mats hP hG A.owner hH hN hn

/-! ## One dictionary -/

/-- The list of the head's sub-proof, from matrices Z that are named by labels. -/
def mzH (h : Model.Head.Shape) (y : Lay) (Z : ℕ → ℕ → ℕ → ℤ) : Mats ℤ :=
  fun n r c => Z (labH h y n) r c

/-- **The library's family of matrices, from matrices Z that are named by the labels of the
verifier's plans.** Segment 24 slot by slot from the head's labels; an even segment 2 g below it
slot by slot from the labels of group g; an odd segment 2 g + 1 is At g, a letter. The formula does
not name a sub-proof: a label is a name for all. Read at the matrices of one sub-proof, its own and
its copies, it lays each copy at its owner's place, which is where the library's conditions read a
borrowed cell. -/
def D5 (h : Model.Head.Shape) (y : Lay) (At Z : ℕ → ℕ → ℕ → ℤ) : ℕ → ℕ → ℕ → ℤ :=
  stackedH y (mzA y Z) At (mzH h y Z)

/-- Segment 24. -/
theorem D5_24 (h : Model.Head.Shape) (y : Lay) (At Z : ℕ → ℕ → ℕ → ℤ) (r c : ℕ) :
    D5 h y At Z 24 r c = Z (labH h y (r / 65536)) (r % 65536) c := rfl

/-- An even segment below 24. -/
theorem D5_even (h : Model.Head.Shape) (y : Lay) (At Z : ℕ → ℕ → ℕ → ℤ) {s : ℕ} (h2 : s % 2 = 0)
    (h24 : s ≠ 24) (r c : ℕ) :
    D5 h y At Z s r c = Z (labA y (s / 2) (slotNo y (r / 65536))) (r % 65536) c := by
  show (if s = 24 then mzH h y Z (r / 65536) (r % 65536) c
      else if s % 2 = 0 then mzA y Z (s / 2) (slotNo y (r / 65536)) (r % 65536) c
      else At (s / 2) r c) = _
  rw [if_neg h24, if_pos h2]
  rfl

/-- On an even segment below 24, at a row of the library's shape, D5 is the layers' libOfA. -/
theorem D5_libOfA (h : Model.Head.Shape) (y : Lay) (At Z : ℕ → ℕ → ℕ → ℤ) {s r : ℕ}
    (h2 : s % 2 = 0) (h24 : s < 24) (hr : r < 2 ^ 19) (c : ℕ) :
    D5 h y At Z s r c = libOfA y Z s r c := by
  unfold D5
  rw [stackedH_libOf y (mzA y Z) At (mzH h y Z) h2 (by omega) hr c, libOfA_eq y Z h24]

/-- In segment 24 D5 is the family that Johnson/Road/HeadL5.lean fills from the head's list
alone. -/
theorem D5_headMx_24 (h : Model.Head.Shape) (y : Lay) (At Z : ℕ → ℕ → ℕ → ℤ) (r c : ℕ) :
    D5 h y At Z 24 r c = headMx h y (mzH h y Z) 24 r c := rfl

/-- So it is in slot 7 of segment 22, where the conditions of segment 24 read the stream: with
twelve groups of layers. -/
theorem D5_headMx_22 (h : Model.Head.Shape) {y : Lay} (h12 : y.NGr = 12)
    (At Z : ℕ → ℕ → ℕ → ℤ) {r : ℕ} (hr : r / 65536 = 7) (c : ℕ) :
    D5 h y At Z 22 r c = headMx h y (mzH h y Z) 22 r c := by
  rw [D5_even h y At Z (s := 22) (by decide) (by decide), hr]
  show Z (labA y 11 (matIx y).iXO) (r % 65536) c = Z (labH h y (h.NHf + 3)) (r % 65536) c
  rw [labH_lent h h12]

/-- **The seam before the head, by definition.** For matrices that are named by labels the head's
copy of the stream is the lender's matrix: the two have one label. -/
theorem lentH_D5 (h : Model.Head.Shape) {y : Lay} (h12 : y.NGr = 12) (Z : ℕ → ℕ → ℕ → ℤ) :
    LentH h y (mzH h y Z) (mzA y Z 11) := by
  intro r _ c _
  show Z (labH h y (h.NHf + 3)) r c = Z (labA y 11 (matIx y).iXO) r c
  rw [labH_lent h h12]

section Link

variable {h : Model.Head.Shape} {tau : Array F} {L : HL} {hy : Model.Layer.Shape}
  {pc : List (List String)} {y : Lay}

/-- **Link 24 is in order at D5 if and only if the matrices with the head's labels are.** Left: all
entries of these matrices are small, and the conditions of segment 24 of the library's model hold at
D5. Right: HeadOrd at the head's list read by labels. At: any letter. -/
theorem link24_D5 (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z1 : Sized hy DF)
    (Z2 : Sized2 hy DF) (h12 : y.NGr = 12) (s : Cm.Scales) (x : Instance ppref)
    (he : x.e = 1024) (Wz : Mat) (At Z : ℕ → ℕ → ℕ → ℤ) :
    ((∀ a r c, |mzH h y Z a r c| < 2 ^ 18) ∧
      (Cm.Seg.TS.segM s 24).Holds Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wz)
        (Cm.Seg.TS.cM (D5 h y At Z))) ↔ HeadOrd h L y s.nf Wz x (mzH h y Z) := by
  unfold HeadOrd D5
  rw [segM24_iff s x he Wz,
    matHolds_iff_cells hF hL hl S Z1 Z2 (mzA y Z) At (mzH h y Z) (lentH_D5 h h12 Z) s.nf x Wz]

end Link

/-- **The seam between two links, from their labels.** Two families D5, of two sub-proofs' matrices
Z and Z', agree on slot number t of the even segment 2 g if Z and Z' agree at the label that group g
gives the matrix of that slot. -/
theorem seam_D5 (h : Model.Head.Shape) (y : Lay) (At At' Z Z' : ℕ → ℕ → ℕ → ℤ) {g t : ℕ}
    (hg : g < 12) (hZ : ∀ r c, Z' (labA y g (slotNo y t)) r c = Z (labA y g (slotNo y t)) r c)
    {r : ℕ} (hr : r / 65536 = t) (c : ℕ) :
    D5 h y At' Z' (2 * g) r c = D5 h y At Z (2 * g) r c := by
  rw [D5_even h y At' Z' (s := 2 * g) (by omega) (by omega),
    D5_even h y At Z (s := 2 * g) (by omega) (by omega), hr, show 2 * g / 2 = g by omega]
  exact hZ _ _

#print axioms bordersOf_labels
#print axioms plan_labels
#print axioms last_label
#print axioms labH_mats
#print axioms labH_lent
#print axioms public_plans
#print axioms labH_of_public
#print axioms D5_libOfA
#print axioms D5_headMx_22
#print axioms lentH_D5
#print axioms link24_D5
#print axioms seam_D5

end OnBytes.Road.Hd
