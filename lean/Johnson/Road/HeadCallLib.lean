-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadCallLib.lean: the form of a lookup call's key vector of the output head, with the
library's keys in the call's columns.

Johnson/Road/HeadCols.lean shows that the form of a call's key vector is worth the multilinear
extension of one function on the call's columns and the positions, if the form of each segment is
worth the weighted extensions of that segment's keys, plus a rest. Johnson/Road/HeadLines.lean,
HeadLinesB.lean and HeadLinesC.lean say what the forms of the nine segments are worth. This file
puts the nine statements into one and feeds it to the first.

The keys. Under each of the verifier's nine names stands the family's key of
Johnson/Road/HeadSizes.lean (sizes as letters), but under "HD0" a factor c times it: the verifier
divides the third digit of a margin by 2^23, and c stands for its inverse of that number.

The rests. Two keys are not affine in the cells. The key of NF holds the product of a value of the
stream and the reciprocal; the key of HD0 holds logits. In their place the forms have the first slot
of a sumcheck each. So the form of a call is worth the extension plus two brackets: slot minus what
the slot is meant to hold. Where both brackets are 0 the form is worth the extension.

Main definitions: nameOf, famOf (families and the verifier's names); keyC, kvOf (the keys); wOf (the
weights of a segment's entries); meantNF, meantHD0, dlC, dlOf (the rests); LinesFit (all that the
nine statements ask); Found (a segment is the one that its name finds).
Main theorems: line_any; keyForm_keys; keyForm_keys_brackets; keyForm_keys_zero; sum_one, sum_none,
nf_here, nf_absent;
kv_ref, kv_ref_HD0, kv_plain, kv_plain_HD0 (at the library's sizes the keys are the
library's).

What is not claimed. Nothing is said about what a slot holds, about when a world is true, or about
what a verifier's acceptance shows. Every theorem on a form begins "if the routine succeeds": none
says that it does. That the record LinesFit and the property Found hold of a run of the verifier is
not shown here. The program does not import this file.
-/
import Johnson.Road.HeadCols
import Johnson.Road.HeadLinesB
import Johnson.Road.HeadLinesC

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open OnBytes.Model (Reading World Aff Fork SubM)
open Inst.Model (NormPar)
open HeadSizes (Sizes)

/-! ## Names -/

/-- The verifier's name of a family. -/
def nameOf : Inst.Model.Head.Fam → String
  | .NF => "NF" | .NFH => "NFH" | .HD0 => "HD0" | .HD1 => "HD1" | .ROW => "ROW" | .HD2 => "HD2"
  | .HE0 => "HE0" | .HE1 => "HE1" | .CNF => "CNF"

/-- The family with a name of the verifier's. -/
def famOf (sn : String) : Option Inst.Model.Head.Fam :=
  if sn = "NF" then some .NF else if sn = "NFH" then some .NFH
  else if sn = "HD0" then some .HD0 else if sn = "HD1" then some .HD1
  else if sn = "ROW" then some .ROW else if sn = "HD2" then some .HD2
  else if sn = "HE0" then some .HE0 else if sn = "HE1" then some .HE1
  else if sn = "CNF" then some .CNF else none

/-- A family is the family with its name. -/
theorem famOf_name (s : Inst.Model.Head.Fam) : famOf (nameOf s) = some s := by
  cases s <;> rfl

section Keys

variable {K : Type} [Field K]

/-- The keys as the verifier looks them up: the third digit of a margin has the factor c. -/
def keyC (c : K) (z : Sizes) (np : NormPar) (t : Inst.Model.Head.Cells K) (H : ℕ → ℕ → K)
    (y : Inst.Model.Head.Req) : Inst.Model.Head.Fam → ℕ → ℕ → K
  | .HD0 => fun x i => c * HeadSizes.key z np t H y .HD0 x i
  | s => HeadSizes.key z np t H y s

/-- The keys under the verifier's names; 0 under any other name. -/
def kvOf (c : K) (z : Sizes) (np : NormPar) (t : Inst.Model.Head.Cells K) (H : ℕ → ℕ → K)
    (y : Inst.Model.Head.Req) (sn : String) : ℕ → ℕ → K :=
  match famOf sn with
  | some s => keyC c z np t H y s
  | none => fun _ _ => 0

theorem kvOf_name (c : K) (z : Sizes) (np : NormPar) (t : Inst.Model.Head.Cells K)
    (H : ℕ → ℕ → K) (y : Inst.Model.Head.Req) (s : Inst.Model.Head.Fam) :
    kvOf c z np t H y (nameOf s) = keyC c z np t H y s := by
  unfold kvOf
  rw [famOf_name]

variable (ρ : Reading K) (W : World K)

/-- The weight of entry x of the segment g of call number q: the equality weight of the entry's
column at the column coordinates of the call's key point. -/
def wOf (R : Model.Head.Run) (q : ℕ) (g : Model.Seg) (x : ℕ) : K :=
  ρ.val ((Model.eqTab (Model.Head.zjOf R.L R.x.g1 q)).getD (g.pos.getD x 0) zeroE)

/-- The part of the keys of NF that is not affine in the cells, under the weights of the segment g:
the products of a value of the stream and the reciprocal. -/
def meantNF (R : Model.Head.Run) (q : ℕ) (z : Sizes) (t : Inst.Model.Head.Cells K) (u : ℕ → K)
    (g : Model.Seg) : K :=
  wsum (wOf ρ R q g) R.h.lt u g.n (fun x i =>
    HeadSizes.xv z t x i * Inst.Model.Ledger.R (fun n => Inst.Model.Head.Dv t n i))

/-- The part of the keys of HD0 that is not affine in the cells, under the weights of the segment g:
at a covered position, the logit of the checked token less the logit of the entry. -/
def meantHD0 (R : Model.Head.Run) (q : ℕ) (z : Sizes) (t : Inst.Model.Head.Cells K)
    (H : ℕ → ℕ → K) (y : Inst.Model.Head.Req) (u : ℕ → K) (g : Model.Seg) : K :=
  wsum (wOf ρ R q g) R.h.lt u g.n (fun x i => ((y.rho i : ℤ) : K) *
    (HeadSizes.lg z t H i (y.win i) - HeadSizes.lg z t H i x))

/-- What the form of a segment is worth beyond the weighted extensions of its keys. NF: less the
products of stream and reciprocal. HD0: c times the first slot of the logits' sumcheck, scaled, less
the differences of logits. The other families: nothing. -/
def dlC (R : Model.Head.Run) (q : ℕ) (c : K) (z : Sizes) (t : Inst.Model.Head.Cells K)
    (H : ℕ → ℕ → K) (y : Inst.Model.Head.Req) (u : ℕ → K) :
    Inst.Model.Head.Fam → Model.Seg → K
  | .NF, g => -meantNF ρ R q z t u g
  | .HD0, g => c * ((2 : K) ^ R.h.lPd * W.slot R.x.tH.sCl - meantHD0 ρ R q z t H y u g)
  | _, _ => 0

/-- The same, by the segment's name. -/
def dlOf (R : Model.Head.Run) (q : ℕ) (c : K) (z : Sizes) (t : Inst.Model.Head.Cells K)
    (H : ℕ → ℕ → K) (y : Inst.Model.Head.Req) (u : ℕ → K) (g : Model.Seg) : K :=
  match famOf g.name with
  | some s => dlC ρ W R q c z t H y u s g
  | none => 0

theorem dlOf_name {R : Model.Head.Run} {q : ℕ} {c : K} {z : Sizes}
    {t : Inst.Model.Head.Cells K} {H : ℕ → ℕ → K} {y : Inst.Model.Head.Req} {u : ℕ → K}
    {g : Model.Seg} {s : Inst.Model.Head.Fam} (h : g.name = nameOf s) :
    dlOf ρ W R q c z t H y u g = dlC ρ W R q c z t H y u s g := by
  unfold dlOf
  rw [h, famOf_name]

end Keys

section Lines

variable {K : Type} [Field K]

/-! ## What the nine statements ask -/

/-- All that the statements on the nine segments' forms ask of a run of the head's check, a world,
cells and a request. K3: the number of columns of the array that stores the reads. (low | u): the
point that the calls' key points share: low for the entries of a block, u for the positions. -/
structure LinesFit (ρ : Reading K) (W : World K) (R : Model.Head.Run) (z : Sizes) (K3 : ℕ)
    (t : Inst.Model.Head.Cells K) (y : Inst.Model.Head.Req) (low u : ℕ → K) : Prop where
  laid : Laid R z
  req : ReqFits R z y
  /-- the margins' digits are cut at 8 bits, and the ledger has five limbs -/
  sh : R.h.digSh = 8
  XL : R.h.XL = 5
  /-- the call that the run knows as the margins' call has the segment HD0 -/
  qH : Model.Head.callNo R.L "HD0" = some R.x.qH
  /-- at a covered position the checked token is an entry of the vocabulary -/
  win : ∀ i, i < z.T → R.cov.hOn.getD i false = true → y.win i < z.V
  Sa : 2 ^ R.h.ls ∣ z.Va
  Va : z.Va ≤ z.V
  /-- four tables of the reads are true of the cells -/
  long : LongAt W R K3 "hf@Z" R.h.ls R.h.lt low u t.hf
  hd : ShortAt W R K3 "hd@zt_FC" R.h.lt u t.hd
  hr : ShortAt W R K3 "hr@zt_ROW" R.h.lt u t.hr
  phiC : ShortAt W R K3 "hr@phiC" R.h.lt u
    (fun φ i => ((HeadSizes.rhoC z y i : ℤ) : K) * t.hr φ i)
  /-- the segments -/
  sNF : SegFit ρ R "NF" z.d low
  sNFH : SegFit ρ R "NFH" z.d low
  sHD0 : SegFit ρ R "HD0" z.V low
  sHD1 : SegFit ρ R "HD1" z.V low
  sROW : SegHas R "ROW" 120
  sHD2 : SegFit ρ R "HD2" z.V low
  sHE0 : SegFit ρ R "HE0" z.Va low
  sHE1 : SegFit ρ R "HE1" (z.V - z.Va) low
  sCNF : SegFit ρ R "CNF" z.d low
  /-- the position coordinates of the calls whose forms read them -/
  uHD0 : PosFit ρ R "HD0" u
  uHD1 : PosFit ρ R "HD1" u
  uHD2 : PosFit ρ R "HD2" u
  uHE0 : PosFit ρ R "HE0" u
  uHE1 : PosFit ρ R "HE1" u

/-- The segment g of call number q is the one that its name finds: no earlier call and no earlier
segment of the call has that name. -/
def Found (R : Model.Head.Run) (q : ℕ) (g : Model.Seg) : Prop :=
  Model.Head.callNo R.L g.name = some q ∧ (R.L.calls.getD q default).seg? g.name = some g

variable {ρ : Reading K} {W : World K}

/-! ## From the weights that a routine returns to the weights of the columns -/

/-- A weighted sum reads its weights at the indices below n alone. -/
theorem wsum_weights {g g' : ℕ → K} (lt : ℕ) (u : ℕ → K) {n : ℕ} (F : ℕ → ℕ → K)
    (h : ∀ x, x < n → g x = g' x) : wsum g lt u n F = wsum g' lt u n F := by
  unfold wsum
  exact sum_congr rfl fun x hx => by rw [h x (mem_range.mp hx)]

/-- A weighted sum reads its point at the coordinates below lt alone. -/
theorem wsum_point (g : ℕ → K) {lt : ℕ} {u u' : ℕ → K} (n : ℕ) (F : ℕ → ℕ → K)
    (h : ∀ j, j < lt → u j = u' j) : wsum g lt u n F = wsum g lt u' n F := by
  unfold wsum
  exact sum_congr rfl fun x _ => by rw [ext_point _ h]

/-- The statement on a segment's form, on the weights of the columns. The form is worth Φ of a
weighted sum under the weights that the routine ewOf returns; the segment with the name sn has n
entries; q and g are the call and the segment that the name finds. -/
theorem line_found {R : Model.Head.Run} {sn : String} {n q : ℕ} {g : Model.Seg} {F : Fork}
    {C : Ctx} {v : K} {u : ℕ → K} {Fk : ℕ → ℕ → K} (Φ : K → K) (S : SegHas R sn n)
    (fq : Model.Head.callNo R.L sn = some q)
    (fg : (R.L.calls.getD q default).seg? sn = some g)
    (hv : ∃ ew, Ok (Model.Head.ewOf R sn) F C ew F C ∧
      v = Φ (wsum (fun x => ρ.val (ew.getD x zeroE)) R.h.lt u n Fk)) :
    v = Φ (wsum (wOf ρ R q g) R.h.lt u g.n Fk) := by
  obtain ⟨ew, h1, rfl⟩ := hv
  obtain ⟨q0, g0, hq0, hg0, hn, hp⟩ := S
  rw [fq] at hq0
  obtain rfl := Option.some.inj hq0
  rw [fg] at hg0
  obtain rfl := Option.some.inj hg0
  obtain ⟨_, _, q1, g1, hq1, hg1, rfl⟩ := ok_ewOf h1
  rw [fq] at hq1
  obtain rfl := Option.some.inj hq1
  rw [fg] at hg1
  obtain rfl := Option.some.inj hg1
  rw [hn]
  congr 1
  exact wsum_weights _ _ _ fun x hx =>
    congrArg ρ.val (ewFrom_getD _ _ (by rw [hp]; exact hx))

/-! ## The nine statements in one -/

/-- The form of any of the nine segments: it is worth the weighted extensions of the segment's keys,
under the weights of the segment's columns, plus the segment's rest. c is the program's inverse of
2^(sh + 15). -/
theorem line_any (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} {F G : Fork} {C D : Ctx}
    {a : Aff} {low u : ℕ → K} {t : Inst.Model.Head.Cells K} (H : ℕ → ℕ → K)
    {y : Inst.Model.Head.Req} (X : LinesFit ρ W R z (colsOf F R.iU3) t y low u) {q : ℕ}
    {g : Model.Seg} (fd : Found R q g) {s : Inst.Model.Head.Fam} (hs : g.name = nameOf s)
    (h : Ok (Model.Head.LINE R g.name) F C a G D) :
    G = F ∧ D = C ∧ a.value ρ W = wsum (wOf ρ R q g) R.h.lt u g.n
        (kvOf (ρ.val (invE (Model.Head.pw (R.h.digSh + 15)))) z (npOf R.h) t H y g.name) +
      dlOf ρ W R q (ρ.val (invE (Model.Head.pw (R.h.digSh + 15)))) z t H y u g := by
  obtain ⟨fq, fg⟩ := fd
  rw [dlOf_name ρ W hs]
  rw [hs] at h fq fg ⊢
  rw [kvOf_name]
  cases s
  case NF =>
    obtain ⟨e1, e2, hv⟩ := line_NF hρ X.laid H y X.long X.sNF h
    refine ⟨e1, e2, ?_⟩
    rw [line_found (fun v => v) X.sNF.has fq fg hv, wsum_sub]
    exact sub_eq_add_neg _ _
  case NFH =>
    obtain ⟨e1, e2, hv⟩ := line_NFH hρ X.laid H y X.long X.sNFH h
    refine ⟨e1, e2, ?_⟩
    rw [line_found (fun v => v) X.sNFH.has fq fg hv]
    exact (add_zero _).symm
  case HD0 =>
    obtain ⟨e1, e2, hv⟩ := line_HD0 hρ X.laid H X.req X.sh X.XL X.qH X.win X.long X.phiC X.sHD0
      X.uHD0 h
    refine ⟨e1, e2, ?_⟩
    generalize ρ.val (invE (Model.Head.pw (R.h.digSh + 15))) = c at hv ⊢
    have h2 : a.value ρ W = c * ((2 : K) ^ R.h.lPd * W.slot R.x.tH.sCl +
        wsum (wOf ρ R q g) R.h.lt u g.n (fun x i =>
          HeadSizes.key z (npOf R.h) t H y .HD0 x i - ((y.rho i : ℤ) : K) *
            (HeadSizes.lg z t H i (y.win i) - HeadSizes.lg z t H i x))) :=
      line_found (fun v => c * ((2 : K) ^ R.h.lPd * W.slot R.x.tH.sCl + v)) X.sHD0.has fq fg hv
    rw [h2, wsum_sub]
    show _ = wsum (wOf ρ R q g) R.h.lt u g.n
        (fun x i => c * HeadSizes.key z (npOf R.h) t H y .HD0 x i) +
      c * ((2 : K) ^ R.h.lPd * W.slot R.x.tH.sCl -
        wsum (wOf ρ R q g) R.h.lt u g.n (fun x i => ((y.rho i : ℤ) : K) *
          (HeadSizes.lg z t H i (y.win i) - HeadSizes.lg z t H i x)))
    rw [wsum_smul]
    ring
  case HD1 =>
    obtain ⟨e1, e2, hv⟩ := line_HD1 hρ X.laid H X.req X.long X.sHD1 X.uHD1 h
    refine ⟨e1, e2, ?_⟩
    rw [line_found (fun v => v) X.sHD1.has fq fg hv]
    exact (add_zero _).symm
  case ROW =>
    obtain ⟨e1, e2, hv⟩ := line_ROW hρ z X.XL H y X.hr h
    refine ⟨e1, e2, ?_⟩
    rw [line_found (fun v => v) X.sROW fq fg hv]
    exact (add_zero _).symm
  case HD2 =>
    obtain ⟨e1, e2, hv⟩ := line_HD2 hρ X.laid H X.req X.long X.sHD2 X.uHD2 h
    refine ⟨e1, e2, ?_⟩
    rw [line_found (fun v => v) X.sHD2.has fq fg hv]
    exact (add_zero _).symm
  case HE0 =>
    obtain ⟨e1, e2, hv⟩ := line_HE0 hρ X.laid H X.req X.Va X.long X.sHE0 X.uHE0 h
    refine ⟨e1, e2, ?_⟩
    rw [line_found (fun v => v) X.sHE0.has fq fg hv]
    exact (add_zero _).symm
  case HE1 =>
    obtain ⟨e1, e2, hv⟩ := line_HE1 hρ X.laid H X.req X.Sa X.long X.sHE1 X.uHE1 h
    refine ⟨e1, e2, ?_⟩
    rw [line_found (fun v => v) X.sHE1.has fq fg hv]
    exact (add_zero _).symm
  case CNF =>
    obtain ⟨e1, e2, hv⟩ := line_CNF hρ X.laid H y X.long X.hd X.sCNF h
    refine ⟨e1, e2, ?_⟩
    rw [line_found (fun v => v) X.sCNF.has fq fg hv]
    exact (add_zero _).symm

/-! ## The form of a call -/

/-- The form of call number q's key vector, with the families' keys in the call's columns. p: the
call's key point, the columns' coordinates first, then the positions', which are u. Every segment of
the call bears one of the nine names and is the segment that its name finds. If f has the segments'
keys in their columns and the padding key in the columns without a mark, the form is worth the
extension of f at p, plus the first slot of a sumcheck in the call with the segment NF, plus the
segments' rests. -/
theorem keyForm_keys (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} {q : ℕ} {laid : Array ℕ}
    {F G : Fork} {C D : Ctx} {x : Aff × Array ℕ} {low u : ℕ → K} {t : Inst.Model.Head.Cells K}
    (H : ℕ → ℕ → K) {y : Inst.Model.Head.Req}
    (X : LinesFit ρ W R z (colsOf F R.iU3) t y low u) {f : ℕ → ℕ → K} {p : ℕ → K}
    (hJ : (R.L.calls.getD q default).J = 2 ^ (R.L.calls.getD q default).lJ)
    (hz : (Model.Head.zjOf R.L R.x.g1 q).size = (R.L.calls.getD q default).lJ)
    (hp : ∀ k, k < (R.L.calls.getD q default).lJ → pt ρ (Model.Head.zjOf R.L R.x.g1 q) k = p k)
    (hu : ∀ k, k < R.h.lt → p ((R.L.calls.getD q default).lJ + k) = u k)
    (hN : ∀ g ∈ (R.L.calls.getD q default).segs, Found R q g ∧ ∃ s, g.name = nameOf s)
    (Kf : ∀ w, (R.L.calls.getD q default).segs.foldlM
        (fun w g => Model.Head.markColumns R w g)
        (Array.replicate (R.L.calls.getD q default).J 0) = some w →
      KeyFn (R.L.calls.getD q default).segs w (R.L.calls.getD q default).J
        (kvOf (ρ.val (invE (Model.Head.pw (R.h.digSh + 15)))) z (npOf R.h) t H y)
        (ρ.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) f)
    (h : Ok (Model.Head.keyForm R q laid) F C x G D) :
    G = F ∧ D = C ∧ x.1.value ρ W =
      Blocks.ext ((R.L.calls.getD q default).lJ + R.h.lt)
          (fun X => f (X / 2 ^ R.h.lt) (X % 2 ^ R.h.lt)) p +
        (if q = R.x.qN then W.slot R.x.tN.sCl else 0) +
        ((R.L.calls.getD q default).segs.map
          (dlOf ρ W R q (ρ.val (invE (Model.Head.pw (R.h.digSh + 15)))) z t H y u)).sum :=
  keyForm_ext _ _ hJ hz hp
    (fun g hg a G' D' ha => by
      obtain ⟨fd, s, hs⟩ := hN g hg
      obtain ⟨e1, e2, hv⟩ := line_any hρ H X fd hs ha
      refine ⟨e1, e2, ?_⟩
      rw [hv, wsum_point _ _ _ hu]
      rfl)
    Kf h

/-! ## Where the two slots hold what they are meant to hold -/

/-- A sum over the segments with one name, in a list without that name. -/
theorem sum_none {l : List Model.Seg} {sn : String} (A : Model.Seg → K)
    (h : ∀ g ∈ l, g.name ≠ sn) : (l.map fun g => if g.name = sn then A g else 0).sum = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, if_neg (h a (by simp)), zero_add]
    exact ih fun g hg => h g (by simp [hg])

/-- A sum over the segments with one name, in a list whose names differ: it is the term of the one
segment with that name. -/
theorem sum_one {l : List Model.Seg} {sn : String} (A : Model.Seg → K)
    (hp : l.Pairwise fun a b => a.name ≠ b.name) {g0 : Model.Seg} (h0 : g0 ∈ l)
    (hn : g0.name = sn) : (l.map fun g => if g.name = sn then A g else 0).sum = A g0 := by
  induction l with
  | nil => cases h0
  | cons a l ih =>
    rw [List.pairwise_cons] at hp
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h0 with h1 | h1
    · have e := sum_none (l := l) (sn := sn) A fun g hg hgn =>
        hp.1 g hg ((h1 ▸ hn).trans hgn.symm)
      rw [← h1, if_pos hn, e, add_zero]
    · have ne : a.name ≠ sn := fun ha => hp.1 g0 h1 (ha.trans hn.symm)
      rw [if_neg ne, zero_add]
      exact ih hp.2 h1

/-- Two lists of terms, each term of the first the negative of its fellow. -/
theorem sum_neg_of {l : List Model.Seg} {a b : Model.Seg → K} (h : ∀ g ∈ l, a g = -b g) :
    (l.map a).sum = -(l.map b).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, h x (by simp),
      ih fun g hg => h g (by simp [hg])]
    ring

/-- Where the two slots hold what they are meant to hold, the form of a call is worth the extension
alone. hH: for a segment HD0 of the call, the first slot of the logits' sumcheck, scaled, is the
weighted extension of the differences of logits. hNF: the first slot of the sumcheck of stream and
reciprocal, which the form has in one call, is the weighted extension of the products, summed over
the call's segments NF. -/
theorem keyForm_keys_zero (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} {q : ℕ}
    {laid : Array ℕ} {F G : Fork} {C D : Ctx} {x : Aff × Array ℕ} {low u : ℕ → K}
    {t : Inst.Model.Head.Cells K} (H : ℕ → ℕ → K) {y : Inst.Model.Head.Req}
    (X : LinesFit ρ W R z (colsOf F R.iU3) t y low u) {f : ℕ → ℕ → K} {p : ℕ → K}
    (hJ : (R.L.calls.getD q default).J = 2 ^ (R.L.calls.getD q default).lJ)
    (hz : (Model.Head.zjOf R.L R.x.g1 q).size = (R.L.calls.getD q default).lJ)
    (hp : ∀ k, k < (R.L.calls.getD q default).lJ → pt ρ (Model.Head.zjOf R.L R.x.g1 q) k = p k)
    (hu : ∀ k, k < R.h.lt → p ((R.L.calls.getD q default).lJ + k) = u k)
    (hN : ∀ g ∈ (R.L.calls.getD q default).segs, Found R q g ∧ ∃ s, g.name = nameOf s)
    (Kf : ∀ w, (R.L.calls.getD q default).segs.foldlM
        (fun w g => Model.Head.markColumns R w g)
        (Array.replicate (R.L.calls.getD q default).J 0) = some w →
      KeyFn (R.L.calls.getD q default).segs w (R.L.calls.getD q default).J
        (kvOf (ρ.val (invE (Model.Head.pw (R.h.digSh + 15)))) z (npOf R.h) t H y)
        (ρ.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) f)
    (hH : ∀ g ∈ (R.L.calls.getD q default).segs, g.name = "HD0" →
      (2 : K) ^ R.h.lPd * W.slot R.x.tH.sCl = meantHD0 ρ R q z t H y u g)
    (hNF : (if q = R.x.qN then W.slot R.x.tN.sCl else 0) =
      ((R.L.calls.getD q default).segs.map fun g =>
        if g.name = "NF" then meantNF ρ R q z t u g else 0).sum)
    (h : Ok (Model.Head.keyForm R q laid) F C x G D) :
    G = F ∧ D = C ∧ x.1.value ρ W =
      Blocks.ext ((R.L.calls.getD q default).lJ + R.h.lt)
        (fun X => f (X / 2 ^ R.h.lt) (X % 2 ^ R.h.lt)) p := by
  obtain ⟨e1, e2, hv⟩ := keyForm_keys hρ H X hJ hz hp hu hN Kf h
  refine ⟨e1, e2, ?_⟩
  have e : ∀ g ∈ (R.L.calls.getD q default).segs,
      dlOf ρ W R q (ρ.val (invE (Model.Head.pw (R.h.digSh + 15)))) z t H y u g =
        -(if g.name = "NF" then meantNF ρ R q z t u g else 0) := by
    intro g hg
    obtain ⟨_, s, hs⟩ := hN g hg
    rw [dlOf_name ρ W hs]
    cases s
    case NF =>
      have hs' : g.name = "NF" := hs
      show -meantNF ρ R q z t u g = _
      rw [if_pos hs']
    case HD0 =>
      rw [if_neg (by rw [hs]; decide)]
      show ρ.val (invE (Model.Head.pw (R.h.digSh + 15))) *
        ((2 : K) ^ R.h.lPd * W.slot R.x.tH.sCl - meantHD0 ρ R q z t H y u g) = _
      rw [hH g hg hs, sub_self, mul_zero, neg_zero]
    all_goals
      rw [if_neg (by rw [hs]; decide)]
      exact neg_zero.symm
  rw [hv, sum_neg_of e, hNF]
  ring

/-- Three lists of terms, each term of the first a combination of its fellows. -/
theorem sum_lin_of {l : List Model.Seg} {a b d : Model.Seg → K} (c : K)
    (h : ∀ g ∈ l, a g = -b g + c * d g) :
    (l.map a).sum = -(l.map b).sum + c * (l.map d).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
      h x (by simp), ih fun g hg => h g (by simp [hg])]
    ring

/-- The form of a call in two brackets. The first: the first slot of the sumcheck of stream and
reciprocal, which the form has in one call, less the weighted extensions of the products, summed
over the call's segments NF. The second, times the program's inverse of 2^(sh + 15): for each
segment HD0 of the call, the first slot of the logits' sumcheck, scaled, less the weighted extension
of the differences of logits. In a list whose names differ each sum has one term at most (sum_one,
sum_none). -/
theorem keyForm_keys_brackets (hρ : Numerals ρ) {R : Model.Head.Run} {z : Sizes} {q : ℕ}
    {laid : Array ℕ} {F G : Fork} {C D : Ctx} {x : Aff × Array ℕ} {low u : ℕ → K}
    {t : Inst.Model.Head.Cells K} (H : ℕ → ℕ → K) {y : Inst.Model.Head.Req}
    (X : LinesFit ρ W R z (colsOf F R.iU3) t y low u) {f : ℕ → ℕ → K} {p : ℕ → K}
    (hJ : (R.L.calls.getD q default).J = 2 ^ (R.L.calls.getD q default).lJ)
    (hz : (Model.Head.zjOf R.L R.x.g1 q).size = (R.L.calls.getD q default).lJ)
    (hp : ∀ k, k < (R.L.calls.getD q default).lJ → pt ρ (Model.Head.zjOf R.L R.x.g1 q) k = p k)
    (hu : ∀ k, k < R.h.lt → p ((R.L.calls.getD q default).lJ + k) = u k)
    (hN : ∀ g ∈ (R.L.calls.getD q default).segs, Found R q g ∧ ∃ s, g.name = nameOf s)
    (Kf : ∀ w, (R.L.calls.getD q default).segs.foldlM
        (fun w g => Model.Head.markColumns R w g)
        (Array.replicate (R.L.calls.getD q default).J 0) = some w →
      KeyFn (R.L.calls.getD q default).segs w (R.L.calls.getD q default).J
        (kvOf (ρ.val (invE (Model.Head.pw (R.h.digSh + 15)))) z (npOf R.h) t H y)
        (ρ.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) f)
    (h : Ok (Model.Head.keyForm R q laid) F C x G D) :
    G = F ∧ D = C ∧ x.1.value ρ W =
      Blocks.ext ((R.L.calls.getD q default).lJ + R.h.lt)
          (fun X => f (X / 2 ^ R.h.lt) (X % 2 ^ R.h.lt)) p +
        ((if q = R.x.qN then W.slot R.x.tN.sCl else 0) -
          ((R.L.calls.getD q default).segs.map fun g =>
            if g.name = "NF" then meantNF ρ R q z t u g else 0).sum) +
        ρ.val (invE (Model.Head.pw (R.h.digSh + 15))) *
          ((R.L.calls.getD q default).segs.map fun g =>
            if g.name = "HD0" then
              (2 : K) ^ R.h.lPd * W.slot R.x.tH.sCl - meantHD0 ρ R q z t H y u g
            else 0).sum := by
  obtain ⟨e1, e2, hv⟩ := keyForm_keys hρ H X hJ hz hp hu hN Kf h
  refine ⟨e1, e2, ?_⟩
  have e : ∀ g ∈ (R.L.calls.getD q default).segs,
      dlOf ρ W R q (ρ.val (invE (Model.Head.pw (R.h.digSh + 15)))) z t H y u g =
        -(if g.name = "NF" then meantNF ρ R q z t u g else 0) +
          ρ.val (invE (Model.Head.pw (R.h.digSh + 15))) *
            (if g.name = "HD0" then
              (2 : K) ^ R.h.lPd * W.slot R.x.tH.sCl - meantHD0 ρ R q z t H y u g
            else 0) := by
    intro g hg
    obtain ⟨_, s, hs⟩ := hN g hg
    rw [dlOf_name ρ W hs]
    cases s
    case NF =>
      have hs' : g.name = "NF" := hs
      show -meantNF ρ R q z t u g = _
      rw [if_pos hs', if_neg (by rw [hs]; decide), mul_zero, add_zero]
    case HD0 =>
      have hs' : g.name = "HD0" := hs
      show ρ.val (invE (Model.Head.pw (R.h.digSh + 15))) *
        ((2 : K) ^ R.h.lPd * W.slot R.x.tH.sCl - meantHD0 ρ R q z t H y u g) = _
      rw [if_pos hs', if_neg (by rw [hs]; decide), neg_zero, zero_add]
    all_goals
      rw [if_neg (by rw [hs]; decide), if_neg (by rw [hs]; decide), neg_zero, mul_zero, add_zero]
      rfl
  rw [hv, sum_lin_of _ e]
  ring

/-- The hypothesis hNF of keyForm_keys_zero in the call that has the slot: the names of the call's
segments differ, g0 is its segment NF, and the slot holds the weighted extension of the
products. -/
theorem nf_here {R : Model.Head.Run} {q : ℕ} {z : Sizes} {t : Inst.Model.Head.Cells K}
    {u : ℕ → K} {l : List Model.Seg} (hp : l.Pairwise fun a b => a.name ≠ b.name)
    (hq : q = R.x.qN) {g0 : Model.Seg} (h0 : g0 ∈ l) (hn : g0.name = "NF")
    (hs : W.slot R.x.tN.sCl = meantNF ρ R q z t u g0) :
    (if q = R.x.qN then W.slot R.x.tN.sCl else 0) =
      (l.map fun g => if g.name = "NF" then meantNF ρ R q z t u g else 0).sum := by
  rw [if_pos hq, sum_one _ hp h0 hn, hs]

/-- The same hypothesis in a call without the slot and without a segment NF. -/
theorem nf_absent {R : Model.Head.Run} {q : ℕ} {z : Sizes} {t : Inst.Model.Head.Cells K}
    {u : ℕ → K} {l : List Model.Seg} (hq : q ≠ R.x.qN) (h : ∀ g ∈ l, g.name ≠ "NF") :
    (if q = R.x.qN then W.slot R.x.tN.sCl else 0) =
      (l.map fun g => if g.name = "NF" then meantNF ρ R q z t u g else 0).sum := by
  rw [if_neg hq, sum_none _ h]

end Lines

/-! ## At the library's sizes, in the library's names -/

section Ref

variable {K : Type} [Field K]

/-- The nine families but HD0: under the verifier's name stands the key of
Policy/Rel/LedgerHead.lean. -/
theorem kv_ref (c : K) (np : NormPar) (t : Inst.Model.Head.Cells K) (H : ℕ → ℕ → K)
    (y : Inst.Model.Head.Req) {s : Inst.Model.Head.Fam} (hs : s ≠ .HD0) :
    kvOf c HeadSizes.ref np t H y (nameOf s) = Policy.LedgerHead.key np t H y s := by
  rw [kvOf_name]
  funext x i
  refine Eq.trans ?_ (HeadSizes.key_ref np t H y s x i)
  cases s
  case HD0 => exact absurd rfl hs
  all_goals rfl

/-- HD0: under the verifier's name stands c times the key of Policy/Rel/LedgerHead.lean. -/
theorem kv_ref_HD0 (c : K) (np : NormPar) (t : Inst.Model.Head.Cells K) (H : ℕ → ℕ → K)
    (y : Inst.Model.Head.Req) :
    kvOf c HeadSizes.ref np t H y "HD0" =
      fun x i => c * Policy.LedgerHead.key np t H y .HD0 x i := by
  have e := kvOf_name c HeadSizes.ref np t H y .HD0
  refine e.trans ?_
  funext x i
  exact congrArg (fun k => c * k) (HeadSizes.key_ref np t H y .HD0 x i)

/-- The family of the nine that a family of the plain head is. -/
def toFam : Cm.Plain.Fam → Inst.Model.Head.Fam
  | .NF => .NF | .NFH => .NFH | .HD0 => .HD0 | .HD1 => .HD1 | .ROW => .ROW | .HD2 => .HD2
  | .CNF => .CNF

/-- The seven families of the plain head but HD0: under the verifier's name stands the key of
Cm/TargetPHead.lean. -/
theorem kv_plain (c : K) (np : NormPar) (t : Inst.Model.Head.Cells K) (H : ℕ → ℕ → K)
    (y : Inst.Model.Head.Req) {f : Cm.Plain.Fam} (hf : f ≠ .HD0) :
    kvOf c HeadSizes.ref np t H y (nameOf (toFam f)) = Cm.Plain.TP.key np t H y f := by
  rw [kvOf_name]
  funext x i
  refine Eq.trans ?_ (HeadSizes.plainKey_ref np t H y f x i)
  cases f
  case HD0 => exact absurd rfl hf
  all_goals rfl

/-- A request without a counted position below 1,024 has none at all: no position from 1,023 on is
counted. -/
theorem rhoC_all {y : Inst.Model.Head.Req} (h0 : ∀ i, i < 1024 → y.rhoC i = 0) (i : ℕ) :
    y.rhoC i = 0 := by
  by_cases hi : i < 1024
  · exact h0 i hi
  · show HeadSizes.rhoC HeadSizes.ref y i = 0
    unfold HeadSizes.rhoC
    have hT : HeadSizes.ref.T = 1024 := rfl
    rw [hT, if_neg]
    rintro ⟨_, h2⟩
    have h3 : min y.e (1024 - 1) ≤ 1024 - 1 := Nat.min_le_right _ _
    omega

/-- HD0 for a request without a counted position: under the verifier's name stands c times the key
of Cm/TargetPHead.lean. -/
theorem kv_plain_HD0 (c : K) (np : NormPar) (t : Inst.Model.Head.Cells K) (H : ℕ → ℕ → K)
    {y : Inst.Model.Head.Req} (h0 : ∀ i, i < 1024 → y.rhoC i = 0) :
    kvOf c HeadSizes.ref np t H y "HD0" = fun x i => c * Cm.Plain.TP.key np t H y .HD0 x i := by
  rw [kv_ref_HD0]
  funext x i
  rw [key_HD0_plain np H (rhoC_all h0 i) x]

end Ref

#print axioms famOf_name
#print axioms line_found
#print axioms line_any
#print axioms keyForm_keys
#print axioms keyForm_keys_zero
#print axioms keyForm_keys_brackets
#print axioms sum_one
#print axioms nf_here
#print axioms nf_absent
#print axioms kv_ref
#print axioms kv_ref_HD0
#print axioms kv_plain
#print axioms kv_plain_HD0

end OnBytes.Road.Hd
