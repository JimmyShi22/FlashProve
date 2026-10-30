-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/LayersSay.lean: what the 24 sub-proofs of the layers say, without the head's
sub-proof.

The statement is LayersSay (Johnson/Goal/Meaning/LayersSayStatement.lean); the theorem is layersSay,
at the end of this file. It says: if each of the 12 groups of layers and each of the 12 attention
sub-proofs is in order at its own list of integer matrices (LayerOrd, AttOrd: every entry below 2^18
in absolute value, every identity of its segment 0 modulo the protocol's prime, every key an entry
of its lookup table), every copy among these lists has the entries of its original, and the stream
that the last group's list holds behind the last layer is below 2^39 in absolute value, then no
range condition of any of the 48 layers fails on the integer program's stream, and that last stream
is the program's.

Why it is needed. The library's road from the sub-proofs' conditions to "the request is true"
(under_of_ords, Johnson/Road/Lane5TopL.lean) takes all 25 sub-proofs at once, the head's in the
library's older letters. Here the head's conditions are left out: of a head only the bound 2^39 is
asked, which the final normalisation's range condition gives (Meaning.last_bound,
Johnson/Meaning/Halves.lean). So a law on the head that is stated in plain integers can be joined to
the layers' laws.

How it is proved.
  1. Premise24: the library's premise (Premise, Johnson/Road/Lane5.lean) for the links 0 .. 23. The
     24 links' matrices are laid into one family (one24), with 0 in the head's own cells, and read
     as a trace (trace24). The segments' conditions hold of that family (holds_one24), its cells are
     small (small_one24), so the field relations of the 24 segments hold (rfl_of_premise24:
     Cm.Lay.RFL, whose third clause is the bound).
  2. The library's statement on the layers alone (Cm.TP.Lay.stream_eqK, part1K, part3K,
     Cm/TargetPLayers.lean) then gives the stream and the range conditions (layers_of_premise24).
  3. The lists give Premise24 (premise24_of_lists: the first two cases of premiseL_of_ords). In the
     place of the head's list stands a list that holds the last group's outgoing stream at every
     number: the layers' conditions read nothing else of it.
  4. The last stream of trace24 is the stream that the last group's list holds (last_eq, by the
     library's dictionaries dict_mz and dict_D5).

The premises can be met together: layersSay_met. Wherever all 25 sub-proofs are in order, the bound
holds of the last group's list: lastOf_bound_of_ords.

What is not claimed. That a proof file which a verifier accepts has such lists. Nothing on the head,
on probabilities or on hiding. The reference model's sizes; the library's lookup tables (tbRef).
-/
import Johnson.Goal.Meaning.LayersSayStatement
import Johnson.Meaning.Scope
import Johnson.Goal.Meaning.Ties

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model Inst.Model.All

/-! ## 1. The premise for the layers' 24 links alone -/

/-- **The premise, without the head's link**: each of the 24 links of the layers is in order at its
own matrices, and holds at every place that its segment may read what the owner's link holds there.
-/
structure Premise24 (h : Cm.Seg.Hd) (seg : Segs) (Wz : Mat) (x : Instance ppref) (A : ℕ → Mx) :
    Prop where
  link : ∀ k < 24, LinkOK h seg Wz x k (A k)
  seam : ∀ k < 24, ∀ q ∈ Cm.Seg.reads h k, Cm.Seg.at' (A k) q = Cm.Seg.at' (A q.1) q

/-- One family of matrices: the cells of each of the 24 segments as its own link holds them; the
head's own cells are 0. -/
def one24 (A : ℕ → Mx) : Mx := fun k r c => if k = 24 then 0 else A k k r c

variable {h : Cm.Seg.Hd} {seg : Segs} {Wz : Mat} {x : Instance ppref} {A : ℕ → Mx}

/-- The 24 segments' conditions hold at that one family. -/
theorem holds_one24 (L : SegLaws h seg) (P : Premise24 h seg Wz x A) {k : ℕ} (hk : k < 24) :
    (seg k).Holds Cm.Seg.TS.fmtRef x (Cm.TP.castW Cb.Gl.p Wz) (Cm.Seg.TS.cM (one24 A)) := by
  have hk' : k < Cm.Seg.nSeg := by
    show k < 25
    omega
  refine Cb.Req.holds_congr (L.wf k hk')
    (fun q hq => congrArg (fun z : ℤ => (z : Cb.Gl.E)) ?_) (P.link k hk).holds
  have hq' := L.places k hk' q hq
  have hle : q.1 ≤ k := (Cm.lay_reads h L.ok k hk' q hq').1
  show Cm.Seg.at' (A k) q = one24 A q.1 q.2.1 q.2.2
  unfold one24
  rw [if_neg (by omega)]
  exact P.seam k hk q hq'

/-- All cells of that family are below 2^18. -/
theorem small_one24 (L : SegLaws h seg) (P : Premise24 h seg Wz x A) (n : Cm.Seg.Name)
    (hn : n.Valid h) : |Cm.Seg.at' (one24 A) n.place| < 2 ^ 18 := by
  have h25 : n.place.1 < 25 := (Cm.lay_inShape h L.ok n hn).1
  show |one24 A n.place.1 n.place.2.1 n.place.2.2| < 2 ^ 18
  unfold one24
  by_cases e : n.place.1 = 24
  · rw [if_pos e]
    norm_num
  · rw [if_neg e]
    exact (P.link n.place.1 (by omega)).small n hn rfl

section Ledger
variable {s : Cm.Scales} {pol : AcceptancePolicy} {i : Cm.Idx}

/-- The trace made of the 24 links' matrices. -/
noncomputable def trace24 (A : ℕ → Mx) : Trace := Cm.Seg.ofMat Cm.Seg.Hd.main (one24 A)

/-- **The field relations of the 24 segments**, from the premise and a bound on the last stream. -/
theorem rfl_of_premise24 (P : Premise24 Cm.Seg.Hd.main (Policy.segPol s pol) i.mat x A)
    (last : ∀ a < ppref.T, ∀ j < ppref.d, |St (trace24 A) 11 8 a j| < 2 ^ 39) :
    Cm.Lay.RFL Cb.Gl.p s.kap s.nf (fun _ => tbRef) i.mat (tokOf x.prompt) (trace24 A) := by
  have b : Cm.Below (2 ^ 18) (trace24 A) := (Policy.lay_below_main (2 ^ 18) _).2 fun n hn => by
    show |Cm.Seg.get (Cm.Seg.ofMat Cm.Seg.Hd.main (one24 A)) n| < 2 ^ 18
    rw [Cm.lay_ofMat_get]
    unfold Cm.Seg.rd
    rw [if_pos hn]
    exact small_one24 (laws_main s pol) P n hn
  have ff : ∀ g < nGr, Cm.Seg.TS.FFAt s g i.mat x (trace24 A) := fun g hg =>
    ((Policy.segsPol_ok s pol).ffOf g hg x (one24 A) i.mat).1
      (holds_one24 (laws_main s pol) P (by have : g < 12 := hg; omega))
  have att : ∀ g < nGr, Cm.Seg.TS.AttAt s g (trace24 A) := fun g hg =>
    ((Policy.segsPol_ok s pol).attOf g hg x (one24 A) i.mat).1
      (holds_one24 (laws_main s pol) P (by have : g < 12 := hg; omega))
  exact ⟨fun g hg => ⟨fun a => b.ff g hg a.val a.property, (ff g hg).1, (ff g hg).2⟩,
    fun g hg => ⟨fun a ha => b.att g hg a ha, (att g hg).1, (att g hg).2⟩,
    fun a ha j hj => by
      show |Head.xv (trace24 A).vHead j a| < 2 ^ 39
      rw [(trace24 A).x_head hj ha]
      exact last a ha j hj⟩

/-- Under the field relations of the 24 segments no range condition of a layer's two blocks fails on
the program's stream. The steps are those of `Cm.TP.Lay.runsK_of` (Cm/TargetPLayers.lean), which
asks the final normalisation's conditions too and returns them unchanged. -/
theorem layersRun_of {p : ℕ} [Cm.TI.Big p] [Fact p.Prime] {κ : ℕ → LayerScale} {nf : NormPar}
    {tbG : ℕ → Tables} {W : Mat} {T : Trace} {prompt : Fin ppref.T → Fin ppref.V}
    (hL : LawfulK κ nf tbG) (hW : Layout.WFW ppref Layout.kRef W Layout.hRef)
    (h : Cm.Lay.RFL p κ nf tbG W (tokOf prompt) T) :
    ∀ L < ppref.layers,
      Att.OK (ppref.at (κ L)) (tbsOf tbG L) ((Layout.weightsOf ppref Layout.kRef W).layer L) L
          (XK ppref κ (tbsOf tbG) (Layout.weightsOf ppref Layout.kRef W) prompt (2 * L)) ∧
        FF.OK (ppref.at (κ L)) (tbsOf tbG L) ((Layout.weightsOf ppref Layout.kRef W).layer L) L
          (XK ppref κ (tbsOf tbG) (Layout.weightsOf ppref Layout.kRef W) prompt (2 * L + 1)) := by
  have hS := Cm.TP.Lay.stream_eqK hL hW h
  have htok := tokOf_lt prompt
  intro L hL'
  have hL'' : L < 48 := hL'
  obtain ⟨g, l, hl, rfl⟩ : ∃ g l, l < 4 ∧ L = 4 * g + l := ⟨L / 4, L % 4, by omega, by omega⟩
  have hg : g < nGr := by unfold nGr; omega
  rw [layer_eq hL'', show 2 * (4 * g + l) = 8 * g + 2 * l by ring,
    Cm.Lay.tbsOf_at tbG g hl, ← kapG_lt κ g hl]
  exact ⟨(att_ok_congr (P := PG κ g l) (hS g hg (2 * l) (by omega))).1
      (FFSeg.Part1.att (scl := SFK κ nf g) (Cm.TP.Lay.part1K hL hW htok h hg hl)),
    (ff_ok_congr (P := PG κ g l) (hS g hg (2 * l + 1) (by omega))).1
      (FFSeg.Part3.ok (scl := SFK κ nf g) ((Cm.TP.Lay.part3K hL hW htok h hg).1 l hl))⟩

/-- **The 24 links give the layers' half of the plain statements**, of the program's own stream; and
the stream that the last group's matrices hold behind the last layer is the program's last stream.
last: that stream is below 2^39 in absolute value, which a head gives. -/
theorem layers_of_premise24 (hs : s.Lawful)
    (P : Premise24 Cm.Seg.Hd.main (Policy.segPol s pol) i.mat x A)
    (last : ∀ a < ppref.T, ∀ j < ppref.d, |St (trace24 A) 11 8 a j| < 2 ^ 39) :
    Meaning.SaysLayers (Policy.ppOf s pol) i.index.val x
        (Meaning.streamOf (Policy.ppOf s pol) i.index.val x) ∧
      Agree ppref (St (trace24 A) 11 8)
        (Meaning.streamOf (Policy.ppOf s pol) i.index.val x (2 * ppref.layers)) := by
  haveI : Cm.TI.Big Cb.Gl.p := ⟨Policy.ledger_gl_big⟩
  haveI : Fact (Nat.Prime Cb.Gl.p) := ⟨Code.pGold_prime⟩
  have hL := hs.lawfulK
  have hR := rfl_of_premise24 P last
  have hS := Cm.TP.Lay.stream_eqK (p := Cb.Gl.p) hL i.wf hR
  have hrun := layersRun_of (p := Cb.Gl.p) hL i.wf hR
  refine ⟨⟨fun pos h j _ => ?_, fun L hL' => (hrun L hL').1,
    fun L _ => fun _ _ _ _ => by rw [Meaning.stream_att], fun L hL' => (hrun L hL').2,
    fun L _ => fun _ _ _ _ => by rw [Meaning.stream_ff]⟩,
    fun a ha j hj => hS 11 (by decide) 8 le_rfl a ha j hj⟩
  show (if h : pos < ppref.T then i.index.val.Emb (x.prompt ⟨pos, h⟩) j else 0) = _
  rw [dif_pos h]

end Ledger

/-! ## 2. From the sub-proofs' lists -/

open OnBytes.Model.Layer (Lay matIx)
open OnBytes.Road.Rows.Norms (numA labZ numA_labA mzA_labZ)

/-- **Each of the layers' 24 links is in order, and every copy among them is its original**, by list
numbers: the first, second, fourth and fifth clause of OrdsN (Johnson/Meaning/Lists.lean). Nothing
is said of the head's sub-proof. -/
structure OrdsN24 (hL : Model.Layer.Shape) (sc : Model.Layer.Scales) (y : Lay)
    (SA : ℕ → Attention.Shape) (Wz : Mat) (x : Instance ppref) (MG : ℕ → Mats ℤ) (MA : ℕ → Zs) :
    Prop where
  layer : ∀ g < 12, LayerOrd hL sc y g (MG g) Wz x
  att : ∀ g < 12, AttOrd (SA g) (MA g)
  seamFF : ∀ g, 0 < g → g < 12 → ∀ r c, MG g (matIx y).iXI r c = MG (g - 1) (matIx y).iXO r c
  seamA : ∀ g < 12, ∀ r c, MA g ((SA g).cf.NAs + 3) r c = MG g (matIx y).iQA r c

/-- The 24 lists under their labels. In the place of the head's list stands a list that holds the
last group's outgoing stream at every number: the layers' conditions read nothing else of it. -/
def zOf24 (hH : Model.Head.Shape) (y : Lay) (SA : ℕ → Attention.Shape) (MG : ℕ → Mats ℤ)
    (MA : ℕ → Zs) : ℕ → ℕ → ℕ → ℕ → ℤ :=
  zOf hH y SA MG MA fun _ => MG 11 (matIx y).iXO

/-- The library's matrices of the 24 links, from the lists. -/
def mx24 (hH : Model.Head.Shape) (y : Lay) (SA : ℕ → Attention.Shape) (MG : ℕ → Mats ℤ)
    (MA : ℕ → Zs) : ℕ → Mx :=
  allMx hH y SA MA (zOf24 hH y SA MG MA)

section Lists
variable {hL : Model.Layer.Shape} {pc : List (List String)} {y : Lay} {sc : Model.Layer.Scales}
  {SA : ℕ → Attention.Shape} {MG : ℕ → Mats ℤ} {MA : ℕ → Zs}

/-- Reader and owner agree at the label of what is borrowed. The steps are those of
ordsL_of_lists (Johnson/Meaning/Lists.lean). -/
theorem labels24 (hH : Model.Head.Shape) (hXO : (matIx y).iXO < 256)
    (O : OrdsN24 hL sc y SA Wz x MG MA) : Hd.LabelsAgree y (zOf24 hH y SA MG MA) where
  ff g h0 hg r c := by
    unfold zOf24
    rw [zOf_even hH y SA MG MA _ hg, zOf_even hH y SA MG MA _ (show g - 1 < 12 by omega)]
    show MG g (numA y g (labA y (g - 1) (matIx y).iXO)) r c =
      MG (g - 1) (numA y (g - 1) (labA y (g - 1) (matIx y).iXO)) r c
    rw [← Hd.labA_in y h0, numA_labA y g _ hXO, Hd.labA_in y h0, numA_labA y (g - 1) _ hXO]
    exact O.seamFF g h0 hg r c
  att g hg r c := by
    unfold zOf24
    rw [zOf_odd hH y SA MG MA _ g, zOf_even hH y SA MG MA _ hg]
    show MA g ((SA g).cf.NAs + 3) r c = MG g (numA y g (labA y g (matIx y).iQA)) r c
    rw [numA_labA y g _ hXO]
    exact O.seamA g hg r c
  head r c := by
    unfold zOf24
    rw [zOf_head, show (22 : ℕ) = 2 * 11 from rfl,
      zOf_even hH y SA MG MA _ (show 11 < 12 by omega)]
    show MG 11 (matIx y).iXO r c = MG 11 (numA y 11 (labA y 11 (matIx y).iXO)) r c
    rw [numA_labA y 11 _ hXO]

/-- **Under the public hypotheses on the layers the lists give the premise for the 24 links.** The
steps are the first two cases of premiseL_of_ords (Johnson/Road/Lane5TopL.lean). -/
theorem premise24_of_lists (hy : Model.Layer.layout hL pc = .ok y) (S : Switches hL)
    (Zd : Sized hL All.DF) (Z2 : Sized2 hL All.DF) (hp4 : hL.p4 = true)
    (hXO : (matIx y).iXO < 256) (hH : Model.Head.Shape) (nf : NormPar) (pol : AcceptancePolicy)
    (hSA : ∀ g < 12, AttSized (SA g))
    (hsh : ∀ g < 12, ((scalesOf hL sc nf).kap (4 * g)).sh = (SA g).cf.sh.getD 0 0)
    (hE : ∀ g < 12, ∀ ι : ℕ, ι < (SA g).u0 → (((SA g).Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι)
    (O : OrdsN24 hL sc y SA Wz x MG MA) :
    Premise24 Cm.Seg.Hd.main (Policy.segPol (scalesOf hL sc nf) pol) Wz x
      (mx24 hH y SA MG MA) := by
  refine ⟨fun k hk => ?_, fun k hk =>
    Hd.seam_reads Cm.Seg.Hd.main hH (fun _ => atOf SA MA) (labels24 hH hXO O) k
      (by show k < 25; omega)⟩
  have hk' : k < Cm.Seg.nSeg := by
    show k < 25
    omega
  rcases Cm.Seg.seg_cases hk' with ⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩ | rfl
  · have hg' : g < 12 := hg
    refine linkOK_congr (laws_main _ pol) hk'
      (dict_D5 hy S Zd Z2 hp4 hH Cm.Seg.Hd.main (atOf SA MA) (zOf24 hH y SA MG MA (2 * g)) hg)
      (linkOK_pol pol (by omega) (linkOK_layer hy S Zd Z2 hp4 Cm.Seg.Hd.main hg nf ?_))
    unfold zOf24
    rw [zOf_even hH y SA MG MA _ hg', mzA_labZ y g (MG g) hXO]
    exact O.layer g hg'
  · exact linkOK_congr (laws_main _ pol) hk'
      (attMx_D5 Cm.Seg.Hd.main hH y (SA g) hg (MA g) (atOf SA MA) (zOf24 hH y SA MG MA (2 * g + 1))
        (fun _ _ => rfl) (fun r c => by unfold zOf24; rw [zOf_odd hH y SA MG MA _ g]))
      (linkA_of_ordL hg (hSA g hg) (hsh g hg) (hE g hg) (O.att g hg) pol Wz x)
  · omega

/-- **The last stream of the trace of a family of matrices** that holds, at the places of segment 22
which that segment may read, what the library's dictionary makes of a list Mz: it is the stream that
Mz holds behind the group's last layer (`Meaning.lastOf`). -/
theorem stream_is_lastOf (hy : Model.Layer.layout hL pc = .ok y) (S : Switches hL)
    (Zd : Sized hL All.DF) (Z2 : Sized2 hL All.DF) (hp4 : hL.p4 = true) (M : Mx) (Mz : Mats ℤ)
    (hM : ∀ q ∈ Cm.Seg.reads Cm.Seg.Hd.main 22, q.1 = 22 →
      Cm.Seg.at' M q = Cm.Seg.at' (libMZ y 11 Mz) q) :
    Agree ppref (St (Cm.Seg.ofMat Cm.Seg.Hd.main M) 11 8) (Meaning.lastOf y Mz) := by
  intro a ha j hj
  show FFSeg.val ((Cm.Seg.ofMat Cm.Seg.Hd.main M).tR 11) .x8 0 j a =
    FFSeg.val (cellsOf DF (cellsAt y Mz)) .x8 0 j a
  unfold FFSeg.val
  refine congrArg (· + _) (Finset.sum_congr rfl fun k hk => congrArg (_ * ·) ?_)
  have hc : (⟨.x8, k, 0, j, a⟩ : FFSeg.Cell).Valid DF :=
    ⟨Finset.mem_range.1 hk, Nat.zero_lt_one, hj, ha⟩
  have hn : (Cm.Seg.Name.ff 11 ⟨.x8, k, 0, j, a⟩).Valid Cm.Seg.Hd.main :=
    ⟨by decide, hc, fun e => by cases e⟩
  have own : Cm.Seg.ownFF 11 ⟨.x8, k, 0, j, a⟩ = .ff 11 ⟨.x8, k, 0, j, a⟩ :=
    Cm.Seg.ownFF_own fun e => by cases e
  have mem : (Cm.Seg.Name.ff 11 ⟨.x8, k, 0, j, a⟩).place ∈ Cm.Seg.reads Cm.Seg.Hd.main 22 :=
    Or.inl ⟨11, ⟨.x8, k, 0, j, a⟩, rfl, by decide, hc, by rw [own]⟩
  have e2 : Cm.Seg.at' (libMZ y 11 Mz) (Cm.Seg.ownFF 11 ⟨.x8, k, 0, j, a⟩).place =
      cellsOf DF (cellsAt y Mz) ⟨.x8, k, 0, j, a⟩ := dict_mz hy S Zd Z2 hp4 11 Mz _ hc
  rw [own] at e2
  rw [Trace.tR_valid _ 11 hc, Cm.Seg.vFF_eq, own, ← e2]
  show Cm.Seg.rd Cm.Seg.Hd.main M (.ff 11 ⟨.x8, k, 0, j, a⟩) = _
  unfold Cm.Seg.rd
  rw [if_pos hn]
  exact hM _ mem rfl

/-- **The last stream of the trace made of the 24 lists is the stream that the last group's list
holds.** -/
theorem last_eq (hy : Model.Layer.layout hL pc = .ok y) (S : Switches hL)
    (Zd : Sized hL All.DF) (Z2 : Sized2 hL All.DF) (hp4 : hL.p4 = true) (hH : Model.Head.Shape)
    (hXO : (matIx y).iXO < 256) :
    Agree ppref (St (trace24 (mx24 hH y SA MG MA)) 11 8) (Meaning.lastOf y (MG 11)) :=
  stream_is_lastOf hy S Zd Z2 hp4 _ _ fun q mem h22 => by
    obtain ⟨s, r, c⟩ := q
    obtain rfl : s = 22 := h22
    have e := dict_D5 hy S Zd Z2 hp4 hH Cm.Seg.Hd.main (atOf SA MA) (zOf24 hH y SA MG MA 22)
      (show 11 < 12 by decide) (22, r, c) mem
    have z : mzA y (zOf24 hH y SA MG MA 22) 11 = MG 11 := by
      unfold zOf24
      rw [show (22 : ℕ) = 2 * 11 from rfl, zOf_even hH y SA MG MA _ (show 11 < 12 by decide),
        mzA_labZ y 11 (MG 11) hXO]
    rw [z] at e
    dsimp only [Cm.Seg.at'] at e
    dsimp only [Cm.Seg.at', one24, mx24, allMx]
    rw [if_neg (by decide)]
    exact e.symm

end Lists

end OnBytes.Road.L5

/-! ## 3. The law -/

namespace Meaning

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (matIx)
open VerifiableInference.OnPublicFiles.Flat (scalesAt)

/-- **What the layers' 24 sub-proofs say** (the statement:
Johnson/Goal/Meaning/LayersSayStatement.lean). -/
theorem layersSay : LayersSay := by
  intro Z pp lay X hR h A i x MG MA layer att seamFF seamA last
  have E := Hd.eleven_of_core h A (Hd.npOf X.hS)
  have B := E.1
  obtain ⟨h3, h1⟩ := Hd.parts_ref B.lay B.switches B.sized2
  have hXO : (matIx X.y).iXO < 256 := by
    show X.y.parts.getD 0 0 + X.y.parts.getD 1 0 + 3 < 256
    omega
  obtain ⟨-, tS⟩ := VerifiableInference.Meaning.readings_agree Z pp lay X hR h
  have tS := tS (A.num 2)
  have hs : (scalesAt X).Lawful := tS ▸ lawful_of_read hR
  have P := premise24_of_lists B.lay B.switches B.sized B.sized2 B.p4 hXO X.hS (Hd.npOf X.hS)
    pp.pol E.2.1 E.2.2.1 E.2.2.2.1 ⟨layer, att, seamFF, seamA⟩
  have eq := last_eq (SA := Hd.shapeA X) (MG := MG) (MA := MA) B.lay B.switches B.sized B.sized2
    B.p4 X.hS hXO
  have key : SaysLayers (Policy.ppOf (Cm.Scales.of pp) pp.pol) i.index.val x
        (streamOf (Policy.ppOf (Cm.Scales.of pp) pp.pol) i.index.val x) ∧
      Agree ppref (St (trace24 (mx24 X.hS X.y (Hd.shapeA X) MG MA)) 11 8)
        (streamOf (Policy.ppOf (Cm.Scales.of pp) pp.pol) i.index.val x (2 * ppref.layers)) := by
    rw [tS]
    exact layers_of_premise24 hs P fun a ha j hj => by
      rw [eq a ha j hj]
      exact last a ha j hj
  exact ⟨key.1, fun a ha j hj => (eq a ha j hj).symm.trans (key.2 a ha j hj)⟩

/-- **Wherever all 25 sub-proofs are in order, the last group's list holds a last stream below
2^39.** The lists are named by labels, as OrdsL names them; the last group's list is
`mzA X.y (Zl (2 * 11)) 11`. By the library's statement on the head's cells
(Policy.ledger_head_noWrap). -/
theorem lastOf_bound_of_ords {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray}
    {X : Model.Verify.Public} (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (A : Hd.PublicCore X.P) {i : Cm.Idx}
    {x : Instance ppref} {Zl : ℕ → ℕ → ℕ → ℕ → ℤ} {ZA : ℕ → Zs} (hre : x.r < x.e)
    (O : OrdsL (layerShape X.P) X.layers.sc X.y X.hS X.HLy (Hd.npOf X.hS) (Hd.polOf X.hS)
      (Hd.shapeA X) i.mat x Zl ZA) :
    ∀ pos < ppref.T, ∀ j < ppref.d, |lastOf X.y (mzA X.y (Zl (2 * 11)) 11) pos j| < 2 ^ 39 := by
  have E := Hd.eleven_of_core h A (Hd.npOf X.hS)
  have B := E.1
  obtain ⟨tP, tS⟩ := VerifiableInference.Meaning.readings_agree Z pp lay X hR h
  have tS := tS (A.num 2)
  have hs : (scalesAt X).Lawful := tS ▸ lawful_of_read hR
  have hpol : Policy.PolCond (Hd.polOf X.hS) := tP ▸ polCond_of_read hR
  have R := rnoL_of_premise hre (premiseL_of_ords B.lay B.switches B.sized B.sized2 B.p4 B.groups
    B.full B.head E.2.1 E.2.2.1 E.2.2.2.1 O)
  have cells := stream_is_lastOf B.lay B.switches B.sized B.sized2 B.p4
    (one (allMx X.hS X.y (Hd.shapeA X) ZA Zl)) (mzA X.y (Zl (2 * 11)) 11) fun q mem h22 => by
      obtain ⟨s, r, c⟩ := q
      obtain rfl : s = 22 := h22
      exact (dict_D5 B.lay B.switches B.sized B.sized2 B.p4 X.hS Cm.Seg.Hd.main
        (atOf (Hd.shapeA X) ZA) (Zl (2 * 11)) (show 11 < 12 by decide) (22, r, c) mem).symm
  have hlast := (Policy.ledger_head_noWrap Cb.Gl.p Code.pGold_prime Policy.ledger_gl_big
    (scalesAt X).nf hs.nf i.weights.H (abs_H i.wf) (Hd.polOf X.hS) hpol x _
    (Policy.ledger_headRF R.2.1 R.2.2)).1
  intro a ha j hj
  rw [← cells a ha j hj]
  show |FFSeg.xS DF ((Cm.Seg.ofMat Cm.Seg.Hd.main
    (one (allMx X.hS X.y (Hd.shapeA X) ZA Zl))).tR 11) 8 j a| < 2 ^ 39
  rw [← Trace.x_head _ hj ha]
  exact hlast a ha j hj

/-- **The premises of LayersSay can be met together**: under its public premises some index, some
request for the next token and some lists of the 24 sub-proofs meet them. The lists are those of a
whole proof in order (ordsL_met_scope, Johnson/Meaning/Scope.lean); the bound on the last stream is
the library's statement on the head's cells (Policy.ledger_head_noWrap). -/
theorem layersSay_met (Z : VerifierAndGoals.PublicFiles) (pp : ScalesAndPolicy) (lay : Option ByteArray)
    (X : Model.Verify.Public) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (A : Hd.PublicCore X.P) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (MG : ℕ → Mats ℤ) (MA : ℕ → Zs),
      x.r = 1023 ∧ x.e = 1024 ∧
      (∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g (MG g) i.mat x) ∧
      (∀ g < 12, AttOrd (Hd.shapeA X g) (MA g)) ∧
      (∀ g, 0 < g → g < 12 → ∀ r c,
        MG g (matIx X.y).iXI r c = MG (g - 1) (matIx X.y).iXO r c) ∧
      (∀ g < 12, ∀ r c, MA g ((Hd.shapeA X g).cf.NAs + 3) r c = MG g (matIx X.y).iQA r c) ∧
      ∀ pos < ppref.T, ∀ j < ppref.d, |lastOf X.y (MG 11) pos j| < 2 ^ 39 := by
  have B := (Hd.eleven_of_core h A (Hd.npOf X.hS)).1
  obtain ⟨tP, tS⟩ := VerifiableInference.Meaning.readings_agree Z pp lay X hR h
  obtain ⟨i, x, Zl, ZA, hr, he, O⟩ := ordsL_met_scope h A hR (tS (A.num 2)) tP
  have N := lists_of_ordsL B.groups O
  have hre : x.r < x.e := by
    rw [hr, he]
    decide
  exact ⟨i, x, _, ZA, hr, he, N.layer, N.att, N.seamFF, N.seamA,
    lastOf_bound_of_ords hR h A hre O⟩

end Meaning

#print axioms OnBytes.Road.L5.layers_of_premise24
#print axioms OnBytes.Road.L5.premise24_of_lists
#print axioms OnBytes.Road.L5.last_eq
#print axioms Meaning.layersSay
#print axioms Meaning.lastOf_bound_of_ords
#print axioms Meaning.layersSay_met
