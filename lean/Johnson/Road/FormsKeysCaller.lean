-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysCaller.lean: what the identities on a layer sub-proof come to, at the records
that the verifier's own caller builds: the form that the lookup's end leaves is worth the weighted
sum of the extensions of the library's eight key vectors.

The files on the forms and the keys compare, piece by piece, the verifier's Lean text for a layer
sub-proof with the library's definitions. This file joins them in one statement. It takes the
panels' and the claims' environments as the check of a layer sub-proof builds them (hearStack and
the check itself, OnBytes/Model/Layer.lean): both from one environment of the forms, with the calls'
weights of the lookup; and the calls' points and weights in the letters in which the lookup makes
them from its two points (Forest.pad, OnBytes/Model/Look.lean). From these it concludes the ties
between the verifier's points and weights and the library's that the record SigFits and the theorem
start_stack ask for.

What is compared with what. The verifier's own functions (layout, joinPart through startOf, panelsA,
panelsT, placePanels, stackEnd, weightClaims, callWeight) with the library's own wc, zc, keyVec,
ClT, Sig1, Gpos (Inst/Model/FF/Objects.lean, Inst/Model/FF/Trace.lean), at the cells cellsOf D
(cellsAt p.v.y Mm), the weights fun l => layerR D.P lk M (L0 + l), the table of scales sclOf of the
verifier's scale file, and the one point zOf ρ H.fo.zx H.fo.zy. Between the two stand definitions of
these files: startOf, padOf, vecOf, aG, bG, wvOf, rPort, rTrueP, rOff, cellsAt, cellsOf, zOf,
zetaOf.

Main theorems.
 - sigFits_of_look: the record SigFits (Johnson/Road/FormsKeysPortSig.lean), concluded.
 - whole_of_look: start_stack (Johnson/Road/FormsKeysWhole.lean) with the record, the ties and the
   worth of the eight factors concluded. whole_lib: the same with its first part on wc and zc.
 - sig1_port: Sig1 at rPort is Gpos at the end point of the second token sumcheck plus the linear
   part of Sig1 at what was sent less the true contractions. whole_gpos: whole_lib with its second
   and third part on Gpos.
 - lookup_end: under three more equations in the world, the worth of the form that the lookup's end
   leaves.
 - shortQa_of_holds: the short tables of qa at the token point, from the tables' own statements.
 - capstone: lookup_end with one hypothesis on the reads, Holds.
 - keys_in_vectors, vector_entry: the library's keys are entries of its key vectors, and every entry
   is a key or a padding value.

The hypotheses of capstone on the world, and what each stands for. None is a claim of the verifier's
list; between "the form of a claim is worth 0" and each of them lie random steps, which are not
looked at.
 - Hd, Holds: every table of the reads holds what it says of the matrices Mm. Hidden values. It
   stands for the smallness test.
 - hH: the never-sent vector number 0 is the honest vector of the gated products at the library's
   token point. It stands for the product layers.
 - hB0: the start form is worth the sum of the products of the two long vectors. It stands for the
   batched sumcheck. That the two long vectors are those on which the verifier's sumcheck ends is
   the matter of stack_slots (Johnson/Road/FormsKeysEnd.lean), which is not used here.
 - hB3: what the second token sumcheck leaves is worth Sig1 at the record rPort, which holds the
   array shownT as it is. Given hB0, it stands for the element from which om is made.
 - hB2: the hidden sum that the second token sumcheck claims is ClT. Given hB3, it stands for that
   sumcheck.
No part of whole_lib is claimed by itself. That its left side is 0 is the matter of the batched
sumcheck. Then the element from which om is made parts the third from the first two; the second
token sumcheck gives the second from the third; the first is what is left, and the lookup reads it.
What KT is worth is not looked at: H.KT is a field of a free record here, and a wrong sign in the
line that makes it (hearTerms, OnBytes/Model/Layer.lean) would be seen by nothing in these files.
Of the claims that the check of a layer sub-proof lists (the lookup's own, the norms', the ledger's,
the shown values', the gated products', the one-hot rows', the planes', the embedding's, the
smallness test's, the row of the batched sumcheck, the two on the sides' hidden values, the merge's)
none is a hypothesis of a theorem of this file.

The public hypotheses of capstone, and where they are run or proved.
 - The verifier's lines hy, hs, hg, hrd, hl, ht; the tests on the calls' points hZ, hzt, hm, ha,
   hpt; hw, hparts; hpts, hfun: run together at a made-up shape with the library's eight calls
   (Johnson/Road/FormsKeysRun8.lean) and at the two shipped examples' files
   (Johnson/Road/FormsKeysRunK.lean). hs0: shape_of_layout, Johnson/Road/FormsKeysShape.lean, has
   such an s0.
 - S: switchesR8, switchesK. hρ: gl_numerals. The sizes D must meet Z, hc and Zw together, so they
   have the shape's nine numbers, its cap, its number of layers and the vocabulary of the weights'
   shape. dimV h V (Johnson/Road/FormsKeysAimV.lean) meets Z and hc for every shape (sized_dimV),
   and Zw for the shape of the weights that the verifier's public part makes (sizedW_dimV):
   theorems. The library's reference sizes at the full-size example: Z by sizedKF
   (Johnson/Road/FormsKeysRunK.lean) and Zw by sizedW_KF (Johnson/Road/FormsKeysRunWK.lean),
   theorems at numbers that are written by hand after the example's file; hc there by no theorem and
   no run of these files. The sizes dimOf h do not meet Zw with hlw: their vocabulary is 0, on which
   wsLayOf refuses.
 - hN, hTS, hp, hcl, env: run together at the made-up shape (Johnson/Road/FormsKeysPansRun.lean). In
   capstone hTS is the caller's own line that makes the list of the calls of the second walk; that
   the list is 0, 1, 2, 5 is concluded (ts_eq, Johnson/Road/FormsKeysPansTS.lean).
 - hfl: run for all eight calls: it holds at the made-up shape and at the full-size example; at the
   small example it fails for four calls (FormsKeysRun8.lean, FormsKeysRunK.lean). SO THE THEOREMS
   OF THIS FILE DO NOT APPLY AT THE SMALL EXAMPLE'S NUMBERS.
 - hpad: run as an equality of numbers and of words (FormsKeysRun8.lean, FormsKeysRunK.lean); at
   call 6 it is a condition on tb.
 - hsx, hsy, hzk: run (Johnson/Road/FormsKeysRunZ.lean); hsx and hsy follow
   from the lookup's lines
   (sizes_of_pad, Johnson/Road/FormsKeysLookP.lean). he, hHe, hcrt: the letters of the lookup and of
   the caller; by reading.
 - Zw, hsL, hlw: sizedW_of_layout (FormsKeysAimV.lean); run (Johnson/Road/FormsKeysRunW.lean,
   Johnson/Road/FormsKeysRunWK.lean).
 - htm, hNM: plan_sizes, Johnson/Road/FormsKeysPlan.lean.
 - h4, hT, hom, hlam, hst: the profile; the caller's own lines. stackEnd returns at a made-up
   shape with five calls (Johnson/Road/FormsKeysRun.lean).
 - R, the rotary tables: met by tables that are written from the verifier's; against the library's
   reference tables a run on the table's words at the full-size example (FormsKeysRunK.lean).
 - All public hypotheses together in one environment, but for S, Z, hρ, htm and hNM, which are
   theorems: run at the made-up shape with the library's eight calls,
   Johnson/Road/FormsKeysCallerRun.lean. At the shipped examples: no run of
   all together.

How far this is from the library's relation of the segment. That relation (TraceSpec.RF in
Blocks/Segment.lean at the trace of Inst/Model/FF/Trace.lean) has three clauses, none of which is an
equation at a point. For each: what is reached here, and which part of the protocol is there for it
by the design. That the part shows the clause is shown by nothing here and has not been looked at.
 - The cells are small integers. Not reached: nothing here says that a cell is the cast of an
   integer. The part: the smallness test, for which Hd stands here.
 - Every key lies in its table. Reached as far as the equation of capstone: the key side of the
   lookup ends at the extensions of the library's key vectors, whose entries are the library's keys
   and padding values (keys_in_vectors, vector_entry). The part: the lookup's product trees with the
   elements alpha and theta.
 - Every identity is 0. Not reached. The part: the norms', the ledger's, the one-hot rows', the
   planes' and the embedding's claims, which no file here reads.
In the library's folders Inst, Blocks, Cm and Cb no theorem names TS, Sig0 or Sig1 of
Inst/Model/FF/Objects.lean, and of this segment's keyVec keyVecAt alone speaks.

What is not claimed. All statements are identities in a world. No distribution of a challenge is
used, and nothing is said on soundness. Mm and M are any functions, tied to no commitment. No
witness meets the hypotheses on the world together with the public ones. The program does not import
this file.
-/
import Johnson.Road.FormsKeysWhole
import Johnson.Road.FormsKeysLookT
import Johnson.Road.FormsKeysO
import Johnson.Road.FormsKeysSigT
import Johnson.Road.FormsKeysPansTS

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff CallD Seg WsShape WsClaim HFun HTailF2 Level lastOf wsLayOf
  eqTab)
open OnBytes.Model.Layer (Env Lay Heard Reads TableAsk TableAt PanelEnv ClaimEnv Panels StackEnd
  layout scalesHeld readsOf layTables tableAsks panelsA panelsT placePanels stackEnd pointsOf funsOf
  matIx)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam LW Pan Sig1 ClT Gpos rdTrue wc zc famsIn fSh hhU zpos aC keyVec
  fams used lut layerR call len pos present key keyIdx)

variable {K : Type} [Field K]

/-! ## Tools -/

omit [Field K] in
/-- A segment that some call holds is found by callOf. -/
theorem callOf_some {v : Env} {n : String} (hs : HasSeg v.y n) :
    ∃ q cd s, v.callOf n = some (q, cd, s) := by
  obtain ⟨c, hc, s, hs, hn⟩ := hs
  cases hf : v.callOf n with
  | some x => exact ⟨x.1, x.2.1, x.2.2, rfl⟩
  | none =>
    exfalso
    unfold Env.callOf at hf
    obtain ⟨i, hi⟩ := exists_zipIdx v.y.calls.toList 0 c hc
    have h1 := List.findSome?_eq_none_iff.mp hf (c, i) hi
    have h2 : c.seg? n = none := by simpa using h1
    unfold CallD.seg? at h2
    have h3 := List.find?_eq_none.mp h2 s hs
    simp [hn] at h3

omit [Field K] in
/-- With the library's lines there are eight calls, and call number k is there with the library's
line. -/
theorem lines_calls {y : Lay} (hN : LinesAre y) :
    y.calls.size = 8 ∧ ∀ k : Fin 8, ∃ cd, y.calls[k.val]? = some cd ∧
      cd.segs.map (·.name) = (fams k).map segName := by
  have h8 : y.calls.size = 8 := by
    have h1 := congrArg List.length hN
    simpa using h1
  refine ⟨h8, fun k => ?_⟩
  have hk : k.val < y.calls.size := by rw [h8]; exact k.isLt
  refine ⟨y.calls[k.val], Array.getElem?_eq_getElem hk, ?_⟩
  have e := line_at hN k
  have eg : y.calls.getD k.val default = y.calls[k.val] := by simp [Array.getD, hk]
  rw [eg] at e
  exact e

/-- ShortTrue reads the token point on its first lt coordinates alone. -/
theorem ShortTrue.congr {ρ : Reading K} {W : World K} {v : Env} {b mat lt : ℕ} {c : Cells K}
    {u u' : ℕ → K} (H : ShortTrue ρ W v b mat lt c u) (h : ∀ j, j < lt → u j = u' j) :
    ShortTrue ρ W v b mat lt c u' := by
  intro φ a ha
  rw [H φ a ha, ext_congr_pt lt _ h]

/-- The library's keys are entries of its key vectors: the library's own theorem keyVecAt
(Inst/Model/FF/IndexFacts.lean), at this field. Entry (l | pos s x | i) of the key vector of the
call of the family s is the key of s at layer l, entry x and position i. -/
theorem keys_in_vectors [scl : Scl] (D : Dim) (t : Cell → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
    {s : Fam} {l x i : ℕ} (hx : x < len D s) (hi : i < D.T) (hp : present s l = true) :
    keyVec D t tb L0 w (call s) (keyIdx D (call s) l (pos D s x) i) = key D t tb L0 w s l x i :=
  Inst.Model.FFSeg.IndexFacts.keyVecAt K D t tb L0 w s l x i hx hi hp

/-- Every entry of a key vector is the padding value of the call's table or a key of the family that
takes the entry's column. -/
theorem vector_entry [scl : Scl] (D : Dim) (t : Cell → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
    (c : Fin 8) (X : ℕ) :
    keyVec D t tb L0 w c X = (((lut tb c).pad : ℤ) : K) ∨
      ∃ s x, Inst.Model.FFSeg.famAt D c (X / D.T % 2 ^ Inst.Model.FFSeg.lJ D c) = some (s, x) ∧
        keyVec D t tb L0 w c X =
          key D t tb L0 w s (X / D.T / 2 ^ Inst.Model.FFSeg.lJ D c) x (X % D.T) := by
  unfold keyVec
  cases hf : Inst.Model.FFSeg.famAt D c (X / D.T % 2 ^ Inst.Model.FFSeg.lJ D c) with
  | none => exact Or.inl rfl
  | some sx =>
    obtain ⟨s, x⟩ := sx
    by_cases hp : present s (X / D.T / 2 ^ Inst.Model.FFSeg.lJ D c) = true
    · refine Or.inr ⟨s, x, rfl, ?_⟩
      simp [hp]
    · refine Or.inl ?_
      simp [hp]

/-! ## Sig1 at the record rPort -/

section Sig1

variable [scl : Scl] (ρ : Reading K) (y : Lay) (shownT : Array E) (hv : ℕ → ℕ → K) (D : Dim)
  (t : Cell → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (z zh : ℕ → K)

/-- The library's record of the true contractions of the cells, with the never-sent vectors hv. The
record rPort is this record with the sent values in three fields. -/
def rTrueP : Inst.Model.FFSeg.Rd K :=
  rdTrue D t z zh (fun l j => hv 0 (l * 2 ^ ceilLog2 y.h.f + j)) fun l' j => hv (1 + l') j

/-- That record with, in the three fields, what was sent less the true contraction. -/
def rOff : Inst.Model.FFSeg.Rd K :=
  withEnds (rTrueP y hv D t z zh)
    (fun ν => (rPort ρ y shownT hv D t z zh).R2 ν - (rTrueP y hv D t z zh).R2 ν)
    (fun l => (rPort ρ y shownT hv D t z zh).sc2 l - (rTrueP y hv D t z zh).sc2 l)
    (fun l e => (rPort ρ y shownT hv D t z zh).sel2 l e - (rTrueP y hv D t z zh).sel2 l e)

/-- Sig1 at the record rPort is the library's Gpos at the end point zh, plus the linear part of Sig1
at what was sent less the true contractions: Sig1 at the record rOff less the share of the panel QK
(which reads none of the three fields: share_QK_ends, Johnson/Road/FormsKeysSigL.lean). For any sent
values. Asked, as in sig1_gpos (Johnson/Road/FormsKeysSigG.lean): what the panel QK needs of the
sizes; in each layer the shifts of queries and keys are equal or both at least 16; the never-sent
vectors from number 1 on are the honest vectors of the routed gated products at zh. -/
theorem sig1_port (C : D.ChOK)
    (hk : ∀ l, l < D.nl →
      (D.Pl l).kq = (D.Pl l).kk ∨ (16 ≤ (D.Pl l).kq ∧ 16 ≤ (D.Pl l).kk))
    (hH2 : ∀ l', l' < D.ne → ∀ j, j < D.fe →
      hv (1 + l') j = hhU D t (2 * l' + 1) (D.fe + j) zh) :
    Sig1 D (rPort ρ y shownT hv D t z zh) tb L0 w z zh =
      Gpos D t tb L0 w z zh + (Sig1 D (rOff ρ y shownT hv D t z zh) tb L0 w z zh -
        Pan.QK.share D (rTrueP y hv D t z zh) tb L0 w z zh) := by
  have key := sig1_affine D (rTrueP y hv D t z zh) tb L0 w z zh (rTrueP y hv D t z zh).R2
    (fun ν => (rPort ρ y shownT hv D t z zh).R2 ν - (rTrueP y hv D t z zh).R2 ν)
    (rTrueP y hv D t z zh).sc2
    (fun l => (rPort ρ y shownT hv D t z zh).sc2 l - (rTrueP y hv D t z zh).sc2 l)
    (rTrueP y hv D t z zh).sel2
    (fun l e => (rPort ρ y shownT hv D t z zh).sel2 l e - (rTrueP y hv D t z zh).sel2 l e) 1
  have a1 : (fun ν => (rTrueP y hv D t z zh).R2 ν +
      1 * ((rPort ρ y shownT hv D t z zh).R2 ν - (rTrueP y hv D t z zh).R2 ν)) =
      (rPort ρ y shownT hv D t z zh).R2 := funext fun ν => by ring
  have a2 : (fun l => (rTrueP y hv D t z zh).sc2 l +
      1 * ((rPort ρ y shownT hv D t z zh).sc2 l - (rTrueP y hv D t z zh).sc2 l)) =
      (rPort ρ y shownT hv D t z zh).sc2 := funext fun l => by ring
  have a3 : (fun l e => (rTrueP y hv D t z zh).sel2 l e +
      1 * ((rPort ρ y shownT hv D t z zh).sel2 l e - (rTrueP y hv D t z zh).sel2 l e)) =
      (rPort ρ y shownT hv D t z zh).sel2 := funext fun l => funext fun e => by ring
  rw [a1, a2, a3, one_mul] at key
  have eP : withEnds (rTrueP y hv D t z zh) (rPort ρ y shownT hv D t z zh).R2
      (rPort ρ y shownT hv D t z zh).sc2 (rPort ρ y shownT hv D t z zh).sel2 =
      rPort ρ y shownT hv D t z zh := rfl
  have e0 : withEnds (rTrueP y hv D t z zh) (rTrueP y hv D t z zh).R2 (rTrueP y hv D t z zh).sc2
      (rTrueP y hv D t z zh).sel2 = rTrueP y hv D t z zh := rfl
  have g : Sig1 D (rTrueP y hv D t z zh) tb L0 w z zh = Gpos D t tb L0 w z zh :=
    sig1_gpos D t tb L0 w z zh _ _ C hk hH2
  rw [eP, e0, g] at key
  exact key

end Sig1

/-! ## The seventh family of tables, from the tables' own statements -/

omit [Field K] in
/-- The numbers of the short tables of qa at the token point, at profile 4. -/
theorem qaShort_numbers (y : Lay) (rd : Reads) (g : ℕ) (h4 : y.h.p4 = true)
    (hQS : "zt" ∈ rd.rdQS) :
    ∃ a ∈ tableAsks y rd g, a.name = "qa" ++ "@" ++ "zt" ∧ a.M0 = firstM y 3 ∧
      a.parts = partsM y 3 ∧ a.L = y.T ∧ a.point = "zt" ∧ a.lng = false := by
  refine ⟨⟨"qa" ++ "@" ++ "zt", (matIx y).iQA, 1, y.T, "zt", false⟩, ?_, rfl, rfl, rfl, rfl, rfl,
    rfl⟩
  refine List.mem_append_left _ (List.mem_append_right _ ?_)
  rw [if_pos h4]
  exact List.mem_map.mpr ⟨"zt", hQS, rfl⟩

/-- The short tables of qa at the token point are true of the cells that are read in the entries of
M, if every table of the verifier's list holds what it says of M. The hypotheses are those of
trueAt_of_holds (Johnson/Road/FormsKeysTrue.lean), and profile 4. -/
theorem shortQa_of_holds (ρ : Reading K) (W : World K) {h : Model.Layer.Shape}
    {pc : List (List String)} {v : Env} {rd : Reads}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} (hy : layout h pc = .ok v.y)
    (S : Switches h) (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
    (hl : layTables (matsR v.y v.g) (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    {tl : HTailF2} (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR v.y v.g)
    (hNM : tl.NM = tl.mats.size) {H : Heard} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)} {funs : Array HFun}
    (hp : pointsOf v.y H hd hd2 = some pts) (hfun : funsOf v.y H.fo pts r.2.1 = some funs)
    (h4 : h.p4 = true) (M : Mats K) (Hd : ∀ Fn ∈ funs, Holds ρ W tl v.iU3 v.K3 M Fn) :
    ∀ tb, v.tabAt ("qa" ++ "@" ++ "zt") = some tb →
      ShortTrue ρ W v tb 3 v.y.h.lt (cellsAt v.y M) (pt ρ H.ztF) := by
  intro tb htb
  have hT := (laid2_of_layout hy).T
  have e := (admitted_of_layout hy S.p3).shape
  subst e
  have s3 : HasSeg v.y "O" := hasSeg_of_layout hy S .O
  have hQS : "zt" ∈ rd.rdQS :=
    readsOf_short_qa hrd (anyZ_of_seg s3 (by rw [h4]; simp [Model.Layer.readsZ]))
  obtain ⟨a, ha, an, aM, ap, aL, aP, al⟩ := qaShort_numbers v.y rd v.g h4 hQS
  obtain ⟨-, -, -, fz⟩ := pointsOf_names hp
  obtain ⟨-, hT5⟩ := tails_sizes v.y hg
  obtain ⟨a', ha', an', phi, hphi, hfn⟩ := family_of_name hl ht hfun htb
  have ea : a' = a := ask_of_name hrd ha' ha (an'.trans an.symm)
  subst ea
  have b0 : (a'.name == "b-bits-0") = false := by rw [an']; simp
  have b1 : (a'.name == "b-bits-1") = false := by rw [an']; simp
  have b2 : (a'.name == "b-pin") = false := by rw [an']; simp
  obtain ⟨hsz, hph⟩ := phiOf_inv hphi b0 b1 b2 aP fz
  rw [al] at hsz hph
  have hsz' : H.ztF.size = v.y.h.lt := hsz
  have hph' : phi = eqTab H.ztF := hph
  have L1 : Laid1 ρ W v tl funs tb 3 a'.L (rowsM v.y 3 / a'.L) phi := by
    refine laid1_family hl ht htb (fun q' hq' e => ask_of_name hrd hq' ha' (e.trans an'.symm)) aM
      (fun p hp' => ?_) (fun p hp' => ?_) hfn
    · rw [ap] at hp'
      rw [aM]
      exact tails_pair v.y hg (by omega) hp'
    · rw [ap] at hp'
      rw [aM]
      obtain ⟨hi, -, -⟩ := hT5 3 p (by omega) hp'
      have hsz2 : tl.mats.size = ((Model.Layer.tailsOf v.y).getD v.g {}).mats.size := by
        have h1 := congrArg Array.size htm
        simpa [matsR] using h1
      have hi' : firstM v.y 3 + p < tl.mats.size := by
        rw [hsz2]
        exact hi
      have e := getD_map_sizes tl.mats hi'
      rw [htm, tails_pair v.y hg (by omega) hp'] at e
      exact ⟨by rw [hNM]; exact hi', (congrArg Prod.fst e).symm, (congrArg Prod.snd e).symm⟩
  rw [aL, hph'] at L1
  have hTz : v.y.T = 2 ^ H.ztF.size := by rw [hsz']; exact hT
  rw [← hsz']
  refine (shortTrue_iff_phi ρ W v tb 3 _ H.ztF).mpr fun φ a hφ => ?_
  rw [short_of_holds Hd L1 hφ, hTz]

/-! ## The record SigFits, from the lookup's letters -/

section Look

variable {ρ : Reading K} {Wo : World K} {h : Model.Layer.Shape} {pc : List (List String)}
  {p : PanelEnv} {c : ClaimEnv} {rd : Reads} {mats : Array (ℕ × ℕ)}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {D : Dim} {s : WsShape} {lk : ℕ}
  {tb : Tables} {zx zy Zp zt : Array E} {ends : Array (Array E)} {s0 : Model.Forest.Shape}
  {cc : Cells K}
  (hy : layout h pc = .ok p.v.y) (S : Switches h) (hs : scalesHeld h p.v.sc = .ok ())
  (hg : p.v.g < p.v.y.NGr) (hrd : readsOf p.v.y = .ok rd)
  (hl : layTables mats (tableAsks p.v.y rd p.v.g) 0 = some r) (ht : p.v.tab = r.1)
  (hρ : Numerals ρ) (Z : Sized h D) (hc : D.cap = h.lidb) (hN : LinesAre p.v.y)
  (hfl : ∀ k : Fin 8, h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D k))
  (hsx : zx.size = p.v.y.fo.dT) (hsy : zy.size = p.v.y.fo.rK)
  (hzk : p.v.zk = (Array.range p.v.y.fo.NC).map fun q =>
    zy.extract (p.v.y.fo.rK - p.v.y.fo.iota.getD q 0) zy.size ++ zx)
  (he : p.e = (Array.range p.v.y.fo.NC).map (Model.Forest.callWeight p.v.y.fo zy))
  (hZ : lastOf zx p.v.y.h.la = .ok Zp) (hzt : lastOf zx p.v.y.h.lt = .ok zt)
  (hm : p.v.zk.mapM (fun z => (lastOf z p.v.y.h.la).toOption) = some ends)
  (ha : ends.all (· == Zp) = true)
  (hs0 : Model.Forest.shape p.v.y.cl p.v.y.h.lidb = .ok s0)
  (hpt : ((List.range s0.NC).all fun q =>
    (p.v.zk.getD q #[]).size == ((s0.calls[q]?).map (·.n)).getD 0) = true)
  (env : p.v = c.v) (Zw : SizedW s D.P) (hsL : s.L = h.L)
  (hlw : wsLayOf s true lk = .ok c.wsLay) (h4 : h.p4 = true) (hrt : c.rt.size = D.lT)
  (R : ∀ lam, lam < c.v.y.Lam → RopeFits ρ c D tb (c.v.g * c.v.y.Lam) lam)
  (T : TrueAt ρ Wo p.v h.lt cc (pt ρ Zp) (pt ρ zt))
  (T2 : TrueAt2 ρ Wo p.v h.lt cc (pt ρ Zp) (pt ρ c.rt))
  (Ro : ∀ b, p.v.tabAt ("qa" ++ "@" ++ "zt") = some b → ShortTrue ρ Wo p.v b 3 h.lt cc (pt ρ zt))

include hy S Z hc hN hfl hsx hsy hzk in
/-- The points, the weights and the token point of look_fits, the ties of all families and the
lengths of the calls' points, with the library's lines for the hypotheses on the calls. -/
theorem look_of_lines :
    (∀ k : Fin 8, ∀ j, j < aC D k →
      pt ρ (p.v.zk.getD k.val #[]) j = zc D (zOf ρ zx zy) k j) ∧
    (∀ k : Fin 8, ρ.val (Model.Forest.callWeight p.v.y.fo zy k.val) = wc D (zOf ρ zx zy) k) ∧
    (∀ zt', lastOf zx D.lT = .ok zt' → ∀ j, j < D.lT → zpos D (zOf ρ zx zy) j = pt ρ zt' j) ∧
    (∀ f0 : Fam, CallTieV ρ p.v h D (zOf ρ zx zy) f0) ∧
    ∀ k : Fin 8, (p.v.zk.getD k.val #[]).size = aC D k := by
  obtain ⟨h8, Hc⟩ := lines_calls hN
  have H : ∀ k : Fin 8, ∃ cd, p.v.y.calls[k.val]? = some cd ∧
      cd.segs.map (·.name) = (fams k).map segName ∧
      h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D k) := fun k => by
    obtain ⟨cd, a, b⟩ := Hc k
    exact ⟨cd, a, b, hfl k⟩
  obtain ⟨a, b, d⟩ := look_fits (ρ := ρ) hy S Z hc h8 H hsx hsy hzk
  have hNC : p.v.y.fo.NC = 8 := by rw [(fo_of_layout hy).2.1, (fo_of_layout hy).2.2, h8]
  exact ⟨a, b, d, fun f0 => callTieV_of_look hy S Z hc h8 H hsx hsy hzk f0,
    fun k => size_of_look (treesFit_of_layout hy S Z hc h8 H) hNC hsx hsy hzk k⟩

include hy hN he in
/-- The weight of call number k in the panels' environment is what the lookup computes. -/
theorem e_of_look (k : Fin 8) :
    p.e.getD k.val zeroE = Model.Forest.callWeight p.v.y.fo zy k.val := by
  have hNC : p.v.y.fo.NC = 8 := by
    rw [(fo_of_layout hy).2.1, (fo_of_layout hy).2.2, (lines_calls hN).1]
  rw [he, range_map_getD' _ _ _ (by rw [hNC]; exact k.isLt)]

include hy S hs hg hrd hl ht hρ Z hc hN hfl hsx hsy hzk he hZ hzt hm ha hs0 hpt env Zw hsL hlw h4
  hrt R T T2 Ro in
/-- The record SigFits, concluded. From the verifier's own lines, the library's lines of calls, the
bound hfl for all eight calls, the letters in which the lookup makes the calls' points and weights
from its two points zx and zy, the tests on the calls' points, the layout of the weights, profile 4,
the length of the end point of the second token sumcheck and the rotary tables; and, on the world:
the six families of tables at the lookup's point, the four at that end point, and the short tables
of qa at the token point are true of the cells cc. The library's point is zOf ρ zx zy, one for all
calls. -/
theorem sigFits_of_look :
    SigFits (scl := sclOf h p.v.sc p.v.g p.v.y.Lam) ρ Wo p c h pc s D lk (c.v.g * c.v.y.Lam) cc
      (cellsOf D cc) (pt ρ Zp) (zOf ρ zx zy) (pt ρ c.rt) (zetaOf ρ c D) tb := by
  obtain ⟨Lz, Lw, Lp, Lt, Ls⟩ := look_of_lines (ρ := ρ) hy S Z hc hN hfl hsx hsy hzk
  have A := admitted_of_layout hy S.p3
  have sh := A.shape
  have hzt' : lastOf zx D.lT = .ok zt := by
    rw [Z.lT, ← sh]
    exact hzt
  have hu : ∀ j, j < h.lt → pt ρ zt j = zpos D (zOf ρ zx zy) j := fun j hj =>
    (Lp zt hzt' j (by rw [Z.lT]; exact hj)).symm
  have hll : p.v.y.h.ll = D.lL := by
    rw [sh]
    exact Z.lL.symm
  have hyc : layout h pc = .ok c.v.y := by
    rw [← env]
    exact hy
  obtain ⟨bo, hbo⟩ := found_o hy S hrd hl ht h4
  obtain ⟨q, cd, sg, hqk⟩ := callOf_some (hasSeg_of_layout hy S .QK)
  obtain ⟨q1, q2, q3, q4⟩ := Lt .QK q cd sg hqk
  have hpt' := test_of_port hy hs0 hpt
  have hla : p.v.y.h.la = p.v.y.ls + p.v.y.h.lt := by
    rw [sh]
    exact A.la
  have CS := (calls_share ρ p.v hZ hzt hm ha hla).2
  have hwts : ∀ f0 : Fam, byBlocks f0 = true → WtsTie ρ p.v D (pt ρ Zp) f0 := fun f0 hb =>
    wtsTie_of_call hy S Z hb fun q' cd' s' hc' => by
      obtain ⟨hq', -, -⟩ := callOf_spec hc'
      have hlt := lt_of_call hq'
      exact CS q' cd'.lJ (point_there hy S.p3 hpt' hlt hq') (size_of_test hy hpt' hlt hq')
        (lJ_of_layout hy cd' (Array.mem_of_getElem? hq'))
  letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
  exact
    { port := portFits_of_layout hy S hs hg hrd hl ht hρ Z cc _ _ _ (T.congr hu) T2
      aim := aimFits_of_layout hyc S Z (by rw [← env]; exact hg) Zw hsL hlw fun _ _ => rfl
      env := env
      lines := hN
      el := fun k _ => elTie_of_point hll
        (by
          rw [Ls k, hll]
          exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))
        (Lz k)
      wc := fun k _ => by rw [e_of_look hy hN he k]; exact Lw k
      tie := fun f0 _ => (callTieV_iff c h D _ f0).mpr (by rw [← env]; exact Lt f0)
      ew := fun f0 _ => ewTie_of_tie hy S Z (Lt f0)
      wts := fun f0 hf => hwts f0 (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl <;> rfl)
      p4 := by rw [sh]; exact h4
      o := hasShort_o_of_layout hy S h4 Z cc _ hbo ((Ro bo hbo).congr hu)
      qk := ⟨q, cd, sg,
        qkFits_of_layout hyc S Z (by rw [← env]; exact hqk) q1 q2 (by rw [← env]; exact q3),
        by rw [← env]; exact q4⟩
      rt := hrt
      rope := R
      zh := fun _ _ => rfl }

variable (M : Wm K) (hh : ℕ → ℕ → K) {TS : List ℕ} (hTS : TS = [0, 1, 2, 5])
  {pans' : Panels} {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans')
  (hcl : c.weightClaims TS = some cl) {om : Array E} (hom : ρ.val (om.getD 0 zeroE) = 1)
  {rs H1 V : Array E} {lam : ℕ} {shownA shownB : E} {s' : StackEnd}
  (hst : stackEnd p.v.y (placePanels pans'.bl).1 rs lam om H1 V shownA shownB = some s')
  (hlam : (ceilLog2 (placePanels pans'.bl).2 == lam) = true)
  (H : Heard) (hHe : H.fo.e = p.e) {tT : Model.Tsc} (hT : H.tT = some tT) (alpha theta : E)
  {weighed : Array (Array Bool)} (hw : p.v.y.calls.mapM p.v.weighedOf = some weighed)
  {parts : List Aff}
  (hparts : (p.v.y.calls.zip weighed).toList.zipIdx.mapM
    (fun x => p.v.joinPart alpha theta x.2 x.1.1 x.1.2) = some parts)
  (hpad : ∀ k : Fin 8,
    ρ.val (ofF ((p.v.y.cl.getD k.val {}).tauAt (p.v.y.cl.getD k.val {}).t0)) =
      (((lut tb k).pad : ℤ) : K))
  (hH : letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
    ∀ l, l < D.nl → ∀ j, j < fSh D l → hh 0 (l * 2 ^ ceilLog2 p.v.y.h.f + j) =
      hhU D (cellsOf D cc) l j (zpos D (zOf ρ zx zy)))

include hy S hs hg hrd hl ht hρ Z hc hN hfl hsx hsy hzk he hZ hzt hm ha hs0 hpt env Zw hsL hlw h4
  hrt R T T2 Ro hTS hp hcl hom hst hlam hHe hT hw hparts hpad hH

/-- The start form of the batched sumcheck less the sum of the products of the two long vectors, at
the records that the verifier's own caller builds. start_stack (Johnson/Road/FormsKeysWhole.lean)
with the record SigFits, the ties of the calls and the worth of the eight factors all concluded:
from the hypotheses of sigFits_of_look; the start form reads the weights of the panels' environment
(hHe); the two lines in which joinStart makes the marks and the factors (hw, hparts); the padding
keys are the library's (hpad). What stays beside them: the verifier's lists and the end of the
batched sumcheck return (hp, hcl, hst) with the caller's tests (hTS, hlam); om[0] reads as 1 (hom);
the second token sumcheck has been heard (hT); and hH, that the never-sent vector number 0 is
honest. -/
theorem whole_of_look :
    letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
    (startOf H om parts).value ρ Wo -
        ∑ Y ∈ range (2 ^ lam), vecOf (aG ρ Wo p.v.y om hh) (placePanels pans'.bl).1.toList Y *
          vecOf (bG ρ Wo (wvOf ρ c.wsLay M cl)) (placePanels pans'.bl).1.toList Y =
      ((∑ q : Fin 8, ρ.val (H.fo.e.getD q.val zeroE) *
          (ρ.val alpha - (q.val : K) * ρ.val theta -
            Blocks.ext (aC D q)
              (keyVec D (cellsOf D cc) tb (c.v.g * c.v.y.Lam)
                (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l)) q)
              (pt ρ (p.v.zk.getD q.val #[])))) +
        ρ.val (padOf H) - H.fo.cEnd.value ρ Wo) +
      (ClT D (cellsOf D cc) tb (c.v.g * c.v.y.Lam)
          (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l)) (zOf ρ zx zy) - Wo.slot tT.sCl) +
      ρ.val (om.getD 1 zeroE) *
        (H.KT.value ρ Wo -
          Sig1 D (rPort ρ p.v.y p.shownT hh D (cellsOf D cc) (zOf ρ zx zy) (pt ρ c.rt)) tb
            (c.v.g * c.v.y.Lam) (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l))
            (zOf ρ zx zy) (pt ρ c.rt)) := by
  letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
  have SF := sigFits_of_look hy S hs hg hrd hl ht hρ Z hc hN hfl hsx hsy hzk he hZ hzt hm ha hs0
    hpt env Zw hsL hlw h4 hrt R T T2 Ro
  obtain ⟨Lz, -, -, -, -⟩ := look_of_lines (ρ := ρ) hy S Z hc hN hfl hsx hsy hzk
  obtain ⟨h8, Hc⟩ := lines_calls hN
  have hn : ∀ (k : Fin 8) (cd : CallD), p.v.y.calls[k.val]? = some cd →
      cd.segs.map (·.name) = (fams k).map segName := fun k cd hk => by
    obtain ⟨cd', a, b⟩ := Hc k
    have e : cd' = cd := Option.some.inj (a.symm.trans hk)
    rw [← e]
    exact b
  obtain ⟨hlen, hpv⟩ := parts_of_lines hy S hs hg hrd hl ht hρ Z hZ hzt hm ha hs0 hpt cc T tb
    (c.v.g * c.v.y.Lam) (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l)) alpha theta hw hparts
    h8 hn hfl hpad
  exact start_stack SF M hh hTS hp hcl hom hst hlam H hHe parts hT hlen alpha theta hpv hc
    (fun q _ => Lz q) hH

/-- whole_of_look with the first part on the library's own objects too: the calls' weights are the
library's wc, and the key vectors are extended at the library's points zc of the calls, at the one
point zOf ρ zx zy. -/
theorem whole_lib :
    letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
    (startOf H om parts).value ρ Wo -
        ∑ Y ∈ range (2 ^ lam), vecOf (aG ρ Wo p.v.y om hh) (placePanels pans'.bl).1.toList Y *
          vecOf (bG ρ Wo (wvOf ρ c.wsLay M cl)) (placePanels pans'.bl).1.toList Y =
      ((∑ q : Fin 8, wc D (zOf ρ zx zy) q *
          (ρ.val alpha - (q.val : K) * ρ.val theta -
            Blocks.ext (aC D q)
              (keyVec D (cellsOf D cc) tb (c.v.g * c.v.y.Lam)
                (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l)) q)
              (zc D (zOf ρ zx zy) q))) +
        ρ.val (padOf H) - H.fo.cEnd.value ρ Wo) +
      (ClT D (cellsOf D cc) tb (c.v.g * c.v.y.Lam)
          (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l)) (zOf ρ zx zy) - Wo.slot tT.sCl) +
      ρ.val (om.getD 1 zeroE) *
        (H.KT.value ρ Wo -
          Sig1 D (rPort ρ p.v.y p.shownT hh D (cellsOf D cc) (zOf ρ zx zy) (pt ρ c.rt)) tb
            (c.v.g * c.v.y.Lam) (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l))
            (zOf ρ zx zy) (pt ρ c.rt)) := by
  letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
  have W0 := whole_of_look hy S hs hg hrd hl ht hρ Z hc hN hfl hsx hsy hzk he hZ hzt hm ha hs0 hpt
    env Zw hsL hlw h4 hrt R T T2 Ro M hh hTS hp hcl hom hst hlam H hHe hT
    alpha theta hw hparts hpad hH
  obtain ⟨Lz, Lw, -, -, -⟩ := look_of_lines (ρ := ρ) hy S Z hc hN hfl hsx hsy hzk
  have hwc : ∀ q : Fin 8, ρ.val (H.fo.e.getD q.val zeroE) = wc D (zOf ρ zx zy) q := fun q => by
    rw [hHe, e_of_look hy hN he q]
    exact Lw q
  have e1 : ∑ q : Fin 8, ρ.val (H.fo.e.getD q.val zeroE) *
        (ρ.val alpha - (q.val : K) * ρ.val theta -
          Blocks.ext (aC D q)
            (keyVec D (cellsOf D cc) tb (c.v.g * c.v.y.Lam)
              (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l)) q)
            (pt ρ (p.v.zk.getD q.val #[]))) =
      ∑ q : Fin 8, wc D (zOf ρ zx zy) q *
        (ρ.val alpha - (q.val : K) * ρ.val theta -
          Blocks.ext (aC D q)
            (keyVec D (cellsOf D cc) tb (c.v.g * c.v.y.Lam)
              (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l)) q)
            (zc D (zOf ρ zx zy) q)) :=
    Finset.sum_congr rfl fun q _ => by rw [hwc q, ext_congr_pt (aC D q) _ (Lz q)]
  rw [e1] at W0
  exact W0

/-- whole_lib with the second and the third part on the library's Gpos, the summand of the sumcheck
over the positions. The second part: ClT is the sum over the cube of Gpos under the equality weights
of the library's token point (clT_gpos, Johnson/Road/FormsKeysSigT.lean). The third: Sig1 at rPort
is Gpos at the end point of the second token sumcheck, plus the linear part of Sig1 at what was sent
less the true contractions (sig1_port). Asked beside: the three hypotheses of sig1_port. -/
theorem whole_gpos (C : D.ChOK)
    (hk : letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
      ∀ l, l < D.nl → (D.Pl l).kq = (D.Pl l).kk ∨ (16 ≤ (D.Pl l).kq ∧ 16 ≤ (D.Pl l).kk))
    (hH2 : letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
      ∀ l', l' < D.ne → ∀ j, j < D.fe →
        hh (1 + l') j = hhU D (cellsOf D cc) (2 * l' + 1) (D.fe + j) (pt ρ c.rt)) :
    letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
    (startOf H om parts).value ρ Wo -
        ∑ Y ∈ range (2 ^ lam), vecOf (aG ρ Wo p.v.y om hh) (placePanels pans'.bl).1.toList Y *
          vecOf (bG ρ Wo (wvOf ρ c.wsLay M cl)) (placePanels pans'.bl).1.toList Y =
      ((∑ q : Fin 8, wc D (zOf ρ zx zy) q *
          (ρ.val alpha - (q.val : K) * ρ.val theta -
            Blocks.ext (aC D q)
              (keyVec D (cellsOf D cc) tb (c.v.g * c.v.y.Lam)
                (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l)) q)
              (zc D (zOf ρ zx zy) q))) +
        ρ.val (padOf H) - H.fo.cEnd.value ρ Wo) +
      (Blocks.ext D.lT (fun i => Gpos D (cellsOf D cc) tb (c.v.g * c.v.y.Lam)
          (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l)) (zOf ρ zx zy)
          (Blocks.cubePt D.lT i)) (zpos D (zOf ρ zx zy)) - Wo.slot tT.sCl) +
      ρ.val (om.getD 1 zeroE) *
        (H.KT.value ρ Wo -
          (Gpos D (cellsOf D cc) tb (c.v.g * c.v.y.Lam)
              (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l)) (zOf ρ zx zy) (pt ρ c.rt) +
            (Sig1 D (rOff ρ p.v.y p.shownT hh D (cellsOf D cc) (zOf ρ zx zy) (pt ρ c.rt)) tb
                (c.v.g * c.v.y.Lam) (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l))
                (zOf ρ zx zy) (pt ρ c.rt) -
              Pan.QK.share D (rTrueP p.v.y hh D (cellsOf D cc) (zOf ρ zx zy) (pt ρ c.rt)) tb
                (c.v.g * c.v.y.Lam) (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l))
                (zOf ρ zx zy) (pt ρ c.rt)))) := by
  letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
  have W1 := whole_lib hy S hs hg hrd hl ht hρ Z hc hN hfl hsx hsy hzk he hZ hzt hm ha hs0 hpt
    env Zw hsL hlw h4 hrt R T T2 Ro M hh hTS hp hcl hom hst hlam H hHe hT alpha theta hw hparts
    hpad hH
  have SF := sigFits_of_look hy S hs hg hrd hl ht hρ Z hc hN hfl hsx hsy hzk he hZ hzt hm ha hs0
    hpt env Zw hsL hlw h4 hrt R T T2 Ro
  rw [sig1_port ρ p.v.y p.shownT hh D (cellsOf D cc) tb _ _ _ _ C hk hH2,
    clT_gpos D (cellsOf D cc) tb _ _ _ SF.aim.f2] at W1
  exact W1

/-- THE END OF THE LOOKUP'S KEY SIDE, ON THE LIBRARY'S KEY VECTORS. Under the hypotheses of
whole_lib, and three equations in the world, which stand for random steps of the protocol and are
shown by nothing here: the start form is worth the sum of the products of the two long vectors (hB0:
the batched sumcheck); what the second token sumcheck leaves is worth the library's Sig1 at the
record rPort (hB3: given hB0, the element from which om is made parts this from the rest); the
hidden sum that the second token sumcheck claims is the library's ClT (hB2: given hB3, the second
token sumcheck). Then the form that the lookup's end leaves is worth the sum over the eight calls of
the library's weight of the call times alpha - q theta less the extension of the library's key
vector of the call at the library's point of the call, plus the padding trees' number. -/
theorem lookup_end
    (hB0 : (startOf H om parts).value ρ Wo =
      ∑ Y ∈ range (2 ^ lam), vecOf (aG ρ Wo p.v.y om hh) (placePanels pans'.bl).1.toList Y *
        vecOf (bG ρ Wo (wvOf ρ c.wsLay M cl)) (placePanels pans'.bl).1.toList Y)
    (hB3 : letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
      H.KT.value ρ Wo =
        Sig1 D (rPort ρ p.v.y p.shownT hh D (cellsOf D cc) (zOf ρ zx zy) (pt ρ c.rt)) tb
          (c.v.g * c.v.y.Lam) (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l))
          (zOf ρ zx zy) (pt ρ c.rt))
    (hB2 : letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
      Wo.slot tT.sCl = ClT D (cellsOf D cc) tb (c.v.g * c.v.y.Lam)
        (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l)) (zOf ρ zx zy)) :
    letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
    H.fo.cEnd.value ρ Wo =
      (∑ q : Fin 8, wc D (zOf ρ zx zy) q *
        (ρ.val alpha - (q.val : K) * ρ.val theta -
          Blocks.ext (aC D q)
            (keyVec D (cellsOf D cc) tb (c.v.g * c.v.y.Lam)
              (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l)) q)
            (zc D (zOf ρ zx zy) q))) + ρ.val (padOf H) := by
  letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
  have W1 := whole_lib hy S hs hg hrd hl ht hρ Z hc hN hfl hsx hsy hzk he hZ hzt hm ha hs0 hpt
    env Zw hsL hlw h4 hrt R T T2 Ro M hh hTS hp hcl hom hst hlam H hHe hT
    alpha theta hw hparts hpad hH
  rw [hB0, hB3, hB2, sub_self, sub_self, sub_self, mul_zero, add_zero, add_zero] at W1
  exact (sub_eq_zero.mp W1.symm).symm

end Look

/-! ## The capstone -/

section Holds

variable {ρ : Reading K} {Wo : World K} {h : Model.Layer.Shape} {pc : List (List String)}
  {p : PanelEnv} {c : ClaimEnv} {rd : Reads}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {D : Dim} {s : WsShape} {lk : ℕ}
  {tb : Tables} {Zp : Array E} {ends : Array (Array E)} {s0 : Model.Forest.Shape} {H : Heard}
  {tT : Model.Tsc} {tl : HTailF2} {hd : Level} {hd2 : Option Level}
  {pts : List (String × Array E)} {funs : Array HFun}

/-- THE CAPSTONE. lookup_end with ONE hypothesis on the reads: every table of the verifier's list
holds what it says of the matrices Mm (Hd). The cells are those that are read in the entries of Mm,
by the library's own rule for a cell's place; the weights are those that the library's layout reads
in the matrix M; the library's point is made from the lookup's two points H.fo.zx and H.fo.zy. The
public hypotheses are the verifier's own lines and tests, the library's lines of calls, hfl and hpad
for all eight calls, the letters in which the lookup makes the calls' points and weights, and the
rotary tables. On the world: Hd, hH, hB0, hB3, hB2; each stands for random steps and is shown by
nothing here; none is a claim of the verifier's list. Then the form that the lookup's end leaves is
worth the sum over the eight calls of the library's weight of the call times alpha - q theta less
the extension of the library's key vector of the call at the library's point of the call, plus the
padding trees' number. -/
theorem capstone (hy : layout h pc = .ok p.v.y) (S : Switches h)
    (hs : scalesHeld h p.v.sc = .ok ()) (hg : p.v.g < p.v.y.NGr) (hrd : readsOf p.v.y = .ok rd)
    (hl : layTables (matsR p.v.y p.v.g) (tableAsks p.v.y rd p.v.g) 0 = some r)
    (ht : p.v.tab = r.1) (hρ : Numerals ρ) (Z : Sized h D) (hc : D.cap = h.lidb)
    (hN : LinesAre p.v.y) (hfl : ∀ k : Fin 8, h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D k))
    (hsx : H.fo.zx.size = p.v.y.fo.dT) (hsy : H.fo.zy.size = p.v.y.fo.rK)
    (hzk : p.v.zk = (Array.range p.v.y.fo.NC).map fun q =>
      H.fo.zy.extract (p.v.y.fo.rK - p.v.y.fo.iota.getD q 0) H.fo.zy.size ++ H.fo.zx)
    (he : p.e = (Array.range p.v.y.fo.NC).map (Model.Forest.callWeight p.v.y.fo H.fo.zy))
    (hZ : lastOf H.fo.zx p.v.y.h.la = .ok Zp) (hzt : lastOf H.fo.zx p.v.y.h.lt = .ok H.ztF)
    (hm : p.v.zk.mapM (fun z => (lastOf z p.v.y.h.la).toOption) = some ends)
    (ha : ends.all (· == Zp) = true)
    (hs0 : Model.Forest.shape p.v.y.cl p.v.y.h.lidb = .ok s0)
    (hpt : ((List.range s0.NC).all fun q =>
      (p.v.zk.getD q #[]).size == ((s0.calls[q]?).map (·.n)).getD 0) = true)
    (env : p.v = c.v) (Zw : SizedW s D.P) (hsL : s.L = h.L)
    (hlw : wsLayOf s true lk = .ok c.wsLay) (h4 : h.p4 = true) (hcrt : c.rt = tT.r)
    (R : ∀ lam, lam < c.v.y.Lam → RopeFits ρ c D tb (c.v.g * c.v.y.Lam) lam)
    (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR p.v.y p.v.g) (hNM : tl.NM = tl.mats.size)
    (hpts : pointsOf p.v.y H hd hd2 = some pts)
    (hfun : funsOf p.v.y H.fo pts r.2.1 = some funs) (hT : H.tT = some tT) (Mm : Mats K)
    (Hd : ∀ Fn ∈ funs, Holds ρ Wo tl p.v.iU3 p.v.K3 Mm Fn)
    (M : Wm K) (hh : ℕ → ℕ → K) {TS : List ℕ}
    (hTS : rd.tscCalls.mapM p.v.y.callNo = some TS)
    {pans' : Panels} {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans')
    (hcl : c.weightClaims TS = some cl) {om : Array E} (hom : ρ.val (om.getD 0 zeroE) = 1)
    {rs H1 V : Array E} {lam : ℕ} {shownA shownB : E} {s' : StackEnd}
    (hst : stackEnd p.v.y (placePanels pans'.bl).1 rs lam om H1 V shownA shownB = some s')
    (hlam : (ceilLog2 (placePanels pans'.bl).2 == lam) = true)
    (hHe : H.fo.e = p.e) (alpha theta : E)
    {weighed : Array (Array Bool)} (hw : p.v.y.calls.mapM p.v.weighedOf = some weighed)
    {parts : List Aff}
    (hparts : (p.v.y.calls.zip weighed).toList.zipIdx.mapM
      (fun x => p.v.joinPart alpha theta x.2 x.1.1 x.1.2) = some parts)
    (hpad : ∀ k : Fin 8,
      ρ.val (ofF ((p.v.y.cl.getD k.val {}).tauAt (p.v.y.cl.getD k.val {}).t0)) =
        (((lut tb k).pad : ℤ) : K))
    (hH : letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
      ∀ l, l < D.nl → ∀ j, j < fSh D l → hh 0 (l * 2 ^ ceilLog2 p.v.y.h.f + j) =
        hhU D (cellsOf D (cellsAt p.v.y Mm)) l j (zpos D (zOf ρ H.fo.zx H.fo.zy)))
    (hB0 : (startOf H om parts).value ρ Wo =
      ∑ Y ∈ range (2 ^ lam), vecOf (aG ρ Wo p.v.y om hh) (placePanels pans'.bl).1.toList Y *
        vecOf (bG ρ Wo (wvOf ρ c.wsLay M cl)) (placePanels pans'.bl).1.toList Y)
    (hB3 : letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
      H.KT.value ρ Wo =
        Sig1 D (rPort ρ p.v.y p.shownT hh D (cellsOf D (cellsAt p.v.y Mm))
            (zOf ρ H.fo.zx H.fo.zy) (pt ρ c.rt)) tb
          (c.v.g * c.v.y.Lam) (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l))
          (zOf ρ H.fo.zx H.fo.zy) (pt ρ c.rt))
    (hB2 : letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
      Wo.slot tT.sCl = ClT D (cellsOf D (cellsAt p.v.y Mm)) tb (c.v.g * c.v.y.Lam)
        (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l)) (zOf ρ H.fo.zx H.fo.zy)) :
    letI : Scl := sclOf h p.v.sc p.v.g p.v.y.Lam
    H.fo.cEnd.value ρ Wo =
      (∑ q : Fin 8, wc D (zOf ρ H.fo.zx H.fo.zy) q *
        (ρ.val alpha - (q.val : K) * ρ.val theta -
          Blocks.ext (aC D q)
            (keyVec D (cellsOf D (cellsAt p.v.y Mm)) tb (c.v.g * c.v.y.Lam)
              (fun l => layerR D.P lk M (c.v.g * c.v.y.Lam + l)) q)
            (zc D (zOf ρ H.fo.zx H.fo.zy) q))) + ρ.val (padOf H) := by
  have sh := (admitted_of_layout hy S.p3).shape
  obtain ⟨Z1, hZ1, T⟩ := trueAt_of_holds ρ Wo hy S hg hrd hl ht htm hNM hpts hzt hfun Mm Hd
  obtain ⟨Z2, hZ2, hr2, T2⟩ :=
    trueAt2_of_holds ρ Wo hy S hg hrd hl ht htm hNM hpts hfun hT Mm Hd
  have e1 : Z1 = Zp := Except.ok.inj (hZ1.symm.trans hZ)
  have e2 : Z2 = Zp := Except.ok.inj (hZ2.symm.trans hZ)
  subst e1
  subst e2
  have Ro := shortQa_of_holds ρ Wo hy S hg hrd hl ht htm hNM hpts hfun h4 Mm Hd
  rw [sh] at T T2 Ro
  rw [← hcrt] at T2 hr2
  have hrt : c.rt.size = D.lT := by rw [hr2, sh, Z.lT]
  exact lookup_end hy S hs hg hrd hl ht hρ Z hc hN hfl hsx hsy hzk he hZ hzt hm ha hs0 hpt env Zw
    hsL hlw h4 hrt R T T2 Ro M hh (ts_eq hy S.p3 hN hrd hTS) hp hcl hom hst hlam H hHe hT alpha
    theta hw hparts hpad hH hB0 hB3 hB2

end Holds

#print axioms vector_entry
#print axioms sig1_port
#print axioms shortQa_of_holds
#print axioms sigFits_of_look
#print axioms whole_of_look
#print axioms whole_lib
#print axioms whole_gpos
#print axioms lookup_end
#print axioms capstone

end OnBytes.Road
