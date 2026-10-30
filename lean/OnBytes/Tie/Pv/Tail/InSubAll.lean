-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/InSubAll.lean: the tail of the link of a sub-proof, whole, at a lay of the
committed entries and the verifier's own record tl : OnBytes.Model.HTailF2: the smallness test's
round, the sending of the digits, the lookup on the digits, the laying of one ledger and the draw
that batches it, behind any front.

`link_at_lay` (InSubLay.lean) has the link at letters that are read off a lay Y of the committed
entries of the three tuples of messages, with the smallness test's premises on letters paid. It
leaves the lookup as a letter: the seam's letters T with `DatOK` and `Reads`; the lookup's `KnowAt`
between two conditions on statements; that the digits read off the late message are the cells of the
digits' array; and that the condition behind the lookup bounds the caller's ledger and the lookup's
share of the exponents. Here these are paid for the lookup of a sub-proof at the verifier's own
public numbers (`Cb.Fo.forB` at h := tl.f9; `look_forBOn`, DigLookOn.lean), whose rounds and errors
are those that the verifier's planner makes (`forB_four_gl`,
OnBytes/Tie/Pv/Lookup/Forest/FoAt.lean). The field is the challenge field `Cb.Gl.E`.

The lookup's names of entries: J₀ := Option (the committed entries): the entry with a given address
in the lay, if there is one.

Main names:
  `enY Y`, `mkY Y`: the entry whose address in the lay is a given cell, or the mask row's entry
    under a given slot. `zext_enY`: read with 0 where there is none, that is `Lay.cellAt`.
  `onC`: the late message's entries as a reading of all committed entries, 0 elsewhere.
  `i3Y`: where the lookup's entries stand among the entries at the link's end. `via_i3Y`: read
    through it, the entries at the link's end are the committed entries. `cell_late`, `digs_zl`,
    `digs_zh`: a cell of the digits' array is read alike off all messages and off the late one, and
    the digits that the seam reads are these cells, in the verifier's own columns.
  `cond2`, `cond3`: the front's condition at the statement in front of the lookup; behind the
    lookup, that and the number of the out-statement's rows (`P3`). `loL`, `layL`, `lastL`: the
    plain share of the ledger with its exponents (the caller's claims numbered from 0 on, the
    lookup's end claims from a on); the ledger that is laid; the last block: the lookup, the laying,
    the draw that batches the ledger.
  `look_lay`: the lookup's `KnowAt` between the joints and conditions that `link_at_lay` asks.
    `cond_lo`: `cond3` gives what it asks of the plain share.
  `tail_link_lay`: `link_at_lay` at the seam's letters `lateO`, the block `forB` at h := tl.f9, L :=
    `digL` at `enY`, `mkY`, the end claims `CbQ.DatQ.endCl` and the condition `cond3`; the plain
    share of the ledger with its exponents (lo) stays a letter, with the premise that `cond3` gives
    `LoOK`.
  `tail_link_numbered`: the same at the plain share `loL`: that premise is paid from two
    inequalities on public numbers.
Limits: what is left as premises: the front's `KnowAt` into the joint with the ledger (h₀); on the
two sendings: hF₁, hL₁, hE₁, hF₂, hL₂, hE₂; `Size.Uniq` at the characteristic; on public data, those
of `link_at_lay`: `LayOK`, `SameShapes`, `Fits`, every table in the third vector, the shapes' rows
of symbols, the record's first columns and number of matrices, and that pc and the number of indices
make n₃; that every entry whose address is a cell of the digits' array stands in the late message
(hZZ); in `tail_link_numbered` two inequalities on public numbers: n ≤ a and a + (1 + Fo.nRows
tl.f9) ≤ pc; and three Bools on public numbers: FoNums.ok tl.f9, shapeTest2 tl Cb.Gl.p, colsTest tl,
which are true at a given sub-proof by a run, no proof term. jLK (the sub-proof's next free slot
when the lookup begins) is a letter. In `loL` the caller's claims stand in a row from 0 on and the
lookup's end claims are numbered in the order of `endCl`: that this is the verifier's order is not
said. The link has the form of a sub-proof in which the draw that batches the ledger follows the
lookup on the digits at once; a sub-proof with further rounds between the smallness test's messages
and that draw is not covered. Equality of entries is decided classically. Nothing on an honest
prover. At the record that a plan makes, whose fields funs and cfFirst are empty, the premises on
the tables and on the first columns cannot be met: the theorems are meant at a closed record
(`OnBytes.Tie.Pv.Tail.Closed.closedAt`), in which the tables' shapes and the first columns are laid.
The lay Y is a letter: a lay that lacks the entries of the digits' array, of the array with the bits
of the counts or of the mask row keeps every premise true, and what is said of the digits is then
empty; the theorems are meant at the lay of the link's own shape. The exponents of the numbered
share are not the verifier's at the layers' sub-proofs: that share is sound for the link, but it is
not the form that the verifier tests. The head's sub-proof has further rounds between the smallness
test's messages and the closing draw and is not covered.

-/
import OnBytes.Tie.Pv.Tail.InSubLay
import OnBytes.Tie.Pv.Tail.DigLookOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.DgP OnBytes.Road.Rows OnBytes.Tie.Pv.Tail.Port Cb.Pv.Tail
open Iop Prob Hiop Cb IOR Reduction Cb.Sub Cb.Pv.Att Cb.LdLkp Cb.Fo CbQ

open scoped Classical

section
variable {J : Type} (Y : Road.Rows.Lay J)

/-- The entry whose address is a given cell, if there is one. -/
noncomputable def enY (n : Ent3) : Option J :=
  if h : ∃ i, Y.addr i = .cell n.1 n.2.1 n.2.2 then some h.choose else none

/-- The entry of the mask row under a given slot, if there is one. -/
noncomputable def mkY (j : ℕ) : Option J :=
  if h : ∃ i, Y.addr i = .mask j then some h.choose else none

/-- Read with 0 where there is no such entry, that is the lay's reading of a cell. -/
theorem zext_enY {K : Type} [Field K] [Fintype J] (m : J → K) (n : Ent3) :
    zext m (enY Y n) = Y.cellAt m n.1 n.2.1 n.2.2 := by
  unfold enY
  split
  · next h => exact (Y.cellAt_addr m n.1 n.2.1 n.2.2 h.choose h.choose_spec).symm
  · next h => exact (Y.cellAt_none m n.1 n.2.1 n.2.2 fun i e => h ⟨i, e⟩).symm

end

section
variable {K : Type} [Field K] {s : Size} {Ja Jb Jc : Type}

/-- The late message's entries as a reading of all committed entries. -/
def onC (v : Jc → K) : JAll Ja Jb Jc → K := Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) v)

/-- Where the lookup's entries stand among the entries at the link's end. -/
def i3Y : Option (Option (JAll Ja Jb Jc)) → Option (JEnd s Ja Jb Jc)
  | some (some j) => some (iJE j)
  | _ => none

/-- Read through `i3Y`, values at the link's end are their values at the committed entries. -/
theorem via_i3Y (m : JEnd s Ja Jb Jc → K) :
    viaO i3Y m = zext (zext fun j : JAll Ja Jb Jc => m (iJE j)) := by
  funext o
  rcases o with _ | _ | j <;> rfl

end

variable {Ja Jb Jc : Type} [Fintype Ja] [Fintype Jb] [Fintype Jc] (ρ : Reading Cb.Gl.E)
  (Y : Road.Rows.Lay (JAll Ja Jb Jc)) (tl : HTailF2) {X₀ Xe : Type} {Ex : ExtSpec}

section
variable {K Wp Wp₂ : Type} (S₁ N₁ N₂ : Sig Cb.Gl.E)
  (bk₁ : N₁.Msg → Dig Cb.Gl.E (sizeOf tl).size × Wp₂ → Wp)
  (Br : Rels K Xe Ex (S₁.Msg × Wp)) (ra : S₁.Msg → Ja → Cb.Gl.E) (rb : N₁.Msg → Jb → Cb.Gl.E)
  (rc : N₂.Msg → Jc → Cb.Gl.E) (funsAt : Xe → Array HFun) (hcols : colsTest tl = true)
  (jLK : ℕ) (ex : Exps (sizeOf tl).size)

set_option quotPrecheck false in
local notation "Ql" => hostLay (Wp₁ := Dig Cb.Gl.E (sizeOf tl).size × Wp₂) ρ Y tl S₁ N₁ bk₁ Br ra rb
  funsAt Prod.fst
set_option quotPrecheck false in
local notation "lf" => (S₁.sum N₁).left N₂ (T := OMsg.Msg)
set_option quotPrecheck false in
local notation "rt" => (S₁.sum N₁).right N₂ (T := OMsg.Msg)
set_option quotPrecheck false in
local notation "eU" => fun (u : N₂.Msg) => zext (onC (Ja := Ja) (Jb := Jb) (rc u))
set_option quotPrecheck false in
local notation "dgs" => digsU hcols (fun u => zext (eU u)) fun n => some (enY Y n)
set_option quotPrecheck false in
local notation "Tl" => lateO (Ql).let hcols eU (enY Y) fun u w => (dgs u, w)
set_option quotPrecheck false in
local notation "ents" => fun (m : ((S₁.sum N₁).sum N₂).Msg) =>
  Sum.elim (ra (S₁.left N₁ (T := OMsg.Msg) (lf m)))
    (Sum.elim (rb (S₁.right N₁ (T := OMsg.Msg) (lf m))) (rc (rt m)))
set_option quotPrecheck false in
local notation "Qd" => portQJ tl fun n => some (enY Y n)
set_option quotPrecheck false in
local notation "Dl" => tail3Lay ρ Y tl S₁ N₁ N₂ bk₁ Br ra rb rc funsAt Prod.fst (Tl)
  (fun x => x.1.1) (Qd).endCl i3Y ex
set_option quotPrecheck false in
local notation "Lp" => (forB Cb.Gl.E tl.f9
  (digL Cb.Gl.E tl (enY Y) (mkY Y) jLK
    ((Xe × TWhole.Ledger Cb.Gl.E ((Ja ⊕ JCell (sizeOf tl).size) ⊕ Jb)) × Dr (sizeOf tl).size))
  TWhole.V₀ TWhole.V₀C (Ex := Ex))

/-- A cell of the digits' array is read alike off all messages and off the late one. -/
theorem cell_late
    (hZZ : ∀ i r c, Y.addr i = .cell tl.ix.ZZ r c → ∃ jc : Jc, i = Sum.inr (Sum.inr jc))
    (m : ((S₁.sum N₁).sum N₂).Msg) (r c : ℕ) :
    Y.cellAt (ents m) tl.ix.ZZ r c = Y.cellAt (onC (rc (rt m))) tl.ix.ZZ r c :=
  cellAt_congr Y _ _ _ _ _ fun i hi => by
    obtain ⟨jc, rfl⟩ := hZZ i r c hi
    rfl

set_option quotPrecheck false in
local notation "Aff0" => affLay (Wp₁ := Dig Cb.Gl.E (sizeOf tl).size × Wp₂) ρ Y tl S₁ N₁ bk₁ Br ra
    rb
  funsAt Prod.fst
set_option quotPrecheck false in
local notation "Rc" => recOf (Wp₁ := Dig Cb.Gl.E (sizeOf tl).size × Wp₂) ρ Y tl S₁ N₁ bk₁ Br ra rb
  funsAt Prod.fst (X' := (Dl).X') fun x => x.1.1

/-- The digits that the seam reads are the cells of the digits' array: the low ones. -/
theorem digs_zl
    (hZZ : ∀ i r c, Y.addr i = .cell tl.ix.ZZ r c → ∃ jc : Jc, i = Sum.inr (Sum.inr jc))
    (m : ((S₁.sum N₁).sum N₂).Msg) (μ : Fin (sizeOf tl).size.NM) (v : Fin (sizeOf tl).size.tau)
    (i : Fin ((sizeOf tl).size.m μ)) :
    ((Tl).digs (rt m)).zl μ v i =
      Y.cellAt (ents m) tl.ix.ZZ v ((tl.zzCol μ 0 0).getD 0 + i) := by
  have h0 : 0 < mOf tl μ.val := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  rw [(dgP_ix_lo hcols μ.isLt h0 v.isLt).1]
  show zext (onC (rc (rt m))) (enY Y (tl.ix.ZZ, v.val, offOf tl μ.val + i.val)) =
    Y.cellAt (ents m) tl.ix.ZZ v.val (offOf tl μ.val + 0 + i.val)
  rw [zext_enY, Nat.add_zero, cell_late Y tl S₁ N₁ N₂ ra rb rc hZZ]

/-- The same for the high ones. -/
theorem digs_zh
    (hZZ : ∀ i r c, Y.addr i = .cell tl.ix.ZZ r c → ∃ jc : Jc, i = Sum.inr (Sum.inr jc))
    (m : ((S₁.sum N₁).sum N₂).Msg) (μ : Fin (sizeOf tl).size.NM) (v : Fin (sizeOf tl).size.tau)
    (i : Fin ((sizeOf tl).size.m μ)) :
    ((Tl).digs (rt m)).zh μ v i =
      Y.cellAt (ents m) tl.ix.ZZ v ((tl.zzCol μ 1 0).getD 0 + i) := by
  have h0 : 0 < mOf tl μ.val := lt_of_le_of_lt (Nat.zero_le _) i.isLt
  rw [(dgP_ix_hi hcols μ.isLt h0 v.isLt).1]
  show zext (onC (rc (rt m))) (enY Y (tl.ix.ZZ, v.val, tl.mz + (offOf tl μ.val + i.val))) =
    Y.cellAt (ents m) tl.ix.ZZ v.val (tl.mz + (offOf tl μ.val + 0) + i.val)
  rw [zext_enY, Nat.add_zero, Nat.add_assoc, cell_late Y tl S₁ N₁ N₂ ra rb rc hZZ]

/-- The front's condition on statements, at the statement in front of the lookup. -/
abbrev cond2 {N : ℕ} (ok : LayOK Y tl N) (n : ℕ) :
    ((Ql).let.X × Dr (sizeOf tl).size) × Ex.Str → Prop := fun b =>
  (virtJ (baseAnd (symsLay Y tl ra) Br) (Aff0 ok) (msgV ra (symsLay Y tl ra)) n).on (b.1.1, b.2)

set_option quotPrecheck false in
local notation "C2" => cond2 (Wp₂ := Wp₂) ρ Y tl S₁ N₁ bk₁ Br ra rb funsAt

/-- The condition behind the lookup: the front's, and the number of the out-statement's rows. -/
abbrev cond3 {N : ℕ} (ok : LayOK Y tl N) (n : ℕ) : (Dl).X' × Ex.Str → Prop :=
  P3 (C2 ok n) (Fo.nRows tl.f9)

set_option quotPrecheck false in
local notation "C3" => cond3 ρ Y tl S₁ N₁ N₂ bk₁ Br ra rb rc funsAt hcols ex

/-- The plain share of the ledger with its exponents: the caller's claims numbered from 0 on, the
lookup's end claims numbered from a on. -/
noncomputable abbrev loL (a : ℕ) (x' : (Dl).X') :
    List (ℕ × TWhole.Form Cb.Gl.E (JEnd (sizeOf tl).size Ja Jb Jc)) :=
  numbered 0 (((Dl).pr x').1.2.map (pushF (Dl).i12)) ++ numbered a ((Dl).endCl x')

set_option quotPrecheck false in
local notation "Lo" => loL ρ Y tl S₁ N₁ N₂ bk₁ Br ra rb rc funsAt hcols ex

/-- The ledger that is laid behind the lookup: the plain share, and the verifier's own rows at the
record of the statement. -/
noncomputable abbrev layL
    (lo : (Dl).X' → List (ℕ × TWhole.Form Cb.Gl.E (JEnd (sizeOf tl).size Ja Jb Jc)))
    (pc n₃ : ℕ) (x' : (Dl).X') : TWhole.Ledger Cb.Gl.E (JEnd (sizeOf tl).size Ja Jb Jc) :=
  layP ρ Y (Dl) (Rc) iJE lo pc n₃ x'

set_option quotPrecheck false in
local notation "Ly" => layL ρ Y tl S₁ N₁ N₂ bk₁ Br ra rb rc funsAt hcols ex

/-- The last block: the lookup, the laying of the ledger, the draw that batches it. -/
noncomputable abbrev lastL
    (lo : (Dl).X' → List (ℕ × TWhole.Form Cb.Gl.E (JEnd (sizeOf tl).size Ja Jb Jc)))
    (pc n₃ : ℕ) :=
  ((Lp).R.post (fun x' => some (x', Ly lo pc n₃ x')) (ExtMap.id Ex)).seq
    (IOR.draw Cb.Gl.E
      (TWhole.ledNx (J := JEnd (sizeOf tl).size Ja Jb Jc) (P := (Dl).X')) Ex)

set_option quotPrecheck false in
local notation "T2" => lastL (Ex := Ex) ρ Y tl S₁ N₁ N₂ bk₁ Br ra rb rc funsAt hcols jLK ex

/-- The lookup's knowledge soundness, between the joints and conditions that `link_at_lay` asks. -/
theorem look_lay {N : ℕ} (ok : LayOK Y tl N) (n : ℕ) (H : FoNums.ok tl.f9 = true)
    (hshape : shapeTest2 tl Cb.Gl.p = true) (k₂ : ((S₁.sum N₁).sum N₂).Msg × Wp₂ → K)
    (hZZ : ∀ i r c, Y.addr i = .cell tl.ix.ZZ r c → ∃ jc : Jc, i = Sum.inr (Sum.inr jc)) :
    TWhole.KnowAt (Lp).R (ranCond ((Tl).inD₁ lf rt k₂) (C2 ok n))
      (ranCond (outD (Tl) lf rt k₂ (Dl)) (C3 ok n)) idW (Lp).e := by
  have hlo : ∀ (m : ((S₁.sum N₁).sum N₂).Msg) (i : Pl tl),
      zext (ents m) (enY Y ((portQ tl).lo i)) = eU (rt m) (enY Y ((portQ tl).lo i)) := by
    intro m i
    show zext (ents m) (enY Y ((portQ tl).lo i)) = zext (onC (rc (rt m))) (enY Y ((portQ tl).lo i))
    rw [zext_enY, zext_enY]
    exact cell_late Y tl S₁ N₁ N₂ ra rb rc hZZ m _ _
  have hhi : ∀ (m : ((S₁.sum N₁).sum N₂).Msg) (i : Pl tl),
      zext (ents m) (enY Y ((portQ tl).hi i)) = eU (rt m) (enY Y ((portQ tl).hi i)) := by
    intro m i
    show zext (ents m) (enY Y ((portQ tl).hi i)) = zext (onC (rc (rt m))) (enY Y ((portQ tl).hi i))
    rw [zext_enY, zext_enY]
    exact cell_late Y tl S₁ N₁ N₂ ra rb rc hZZ m _ _
  refine TWhole.knowAt_mono
    (look_forBOn (Ql).let hcols eU (enY Y) (fun u w => (dgs u, w)) (mkY Y) jLK H hshape lf rt k₂
      (C2 ok n) (fun m => zext (ents m)) hlo hhi)
    (fun _ h => h) (fun _ _ _ h => h) ?_ (fun _ h => h)
  rintro b w _ ⟨h1, h2⟩
  refine ⟨h1, ?_⟩
  have g := (pushOL_holds i3Y ((Qd).endCl b.1) ((Dl).msg₃ w.1)).1 h2
  rw [via_i3Y] at g
  exact g

/-- The condition behind the lookup gives what `link_at_lay` asks of the plain share. -/
theorem cond_lo {N : ℕ} (ok : LayOK Y tl N) (n a pc : ℕ) (hna : n ≤ a)
    (hpc : a + (1 + Fo.nRows tl.f9) ≤ pc) (x' : (Dl).X') (y : Ex.Str) (hp : C3 ok n (x', y)) :
    LoOK (Dl) (Lo a) pc x' := by
  have e : ((Dl).endCl x').length = 1 + Fo.nRows tl.f9 := by
    show (((Qd).endCl x').map (pushO i3Y)).length = _
    rw [List.length_map, endCl_length, hp.2]
  exact loOK_numbered (Dl) pc a x' (le_trans hp.1.2 hna) (by rw [e]; exact hpc)

/-- The tail of the link of a sub-proof, whole, at a lay of the committed entries and the
verifier's own record and numbers, behind any front. -/
theorem tail_link_lay (Sd₁ : N₁.Seeds) (Sd₂ : N₂.Seeds) (L₁ : N₁.O → ℕ) (L₂ : N₂.O → ℕ) {N : ℕ}
    (ok : LayOK Y tl N)
    {R₀ : IOR X₀ Ex (Xe × TWhole.Ledger Cb.Gl.E ((Ja ⊕ JCell (sizeOf tl).size) ⊕ Jb)) Ex}
    {A : Rels K X₀ Ex (S₁.Msg × Wp)} {ε₀ : Err R₀.shape} (n : ℕ)
    (h₀ : TWhole.KnowAt R₀ A
      (virtJ (baseAnd (symsLay Y tl ra) Br) (Aff0 ok) (msgV ra (symsLay Y tl ra)) n) idW ε₀)
    (hu : (sizeOf tl).size.Uniq Cb.Gl.p)
    (k₁ k₁' : (S₁.sum N₁).Msg × (Dig Cb.Gl.E (sizeOf tl).size × Wp₂) → K)
    (H : FoNums.ok tl.f9 = true) (hshape : shapeTest2 tl Cb.Gl.p = true)
    (k₂ : ((S₁.sum N₁).sum N₂).Msg × Wp₂ → K)
    (hZZ : ∀ i r c, Y.addr i = .cell tl.ix.ZZ r c → ∃ jc : Jc, i = Sum.inr (Sum.inr jc))
    (hsh : ∀ e, SameShapes tl (funsAt e)) (hnm : tl.NM = tl.mats.size)
    (hfirst : tl.cfFirst = tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0])
    (hfit : Fits tl) (htree : ∀ e, ∀ Fn ∈ (funsAt e).toList, Fn.tree = 2)
    (hmS : ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).mS = Alg.symRows (tl.shp.getD mu {}).m)
    (lo : (Dl).X' → List (ℕ × TWhole.Form Cb.Gl.E (JEnd (sizeOf tl).size Ja Jb Jc)))
    (pc n₃ : ℕ) (hn : ∀ x', pc + topOf (Rc x') (Rc x').funs = n₃)
    (hP : ∀ x' y, C3 ok n (x', y) → LoOK (Dl) lo pc x')
    (d : S₁.Wit × Wp) (d' : (S₁.sum N₁).Wit × (Dig Cb.Gl.E (sizeOf tl).size × Wp₂))
    (hF₁ : Sd₁.Fair) (hL₁ : ∀ i, (N₁.om i).ListLE (L₁ i)) (hE₁ : ∀ i, (N₁.om i).Evades)
    (hF₂ : Sd₂.Fair) (hL₂ : ∀ i, (N₂.om i).ListLE (L₂ i)) (hE₂ : ∀ i, (N₂.om i).Evades) :
    (frame2Red S₁ N₁ N₂ Sd₁ Sd₂ R₀ (R (Ql).let) (T2 lo pc n₃)).KnowInto (S₁.over A).on
      (((S₁.sum N₁).sum N₂).over
        (ledOutA (ranCond (baseD (Tl) lf rt k₂ (Dl)) (C3 ok n)) (Dl).msg₃)).on
      (S₁.over A).relR
      (((S₁.sum N₁).sum N₂).over
        (ledOutA (ranCond (baseD (Tl) lf rt k₂ (Dl)) (C3 ok n)) (Dl).msg₃)).relR
      (frame2Ext S₁ N₁ N₂ Sd₁ Sd₂ bk₁ (fun u w => (dgs u, w)) R₀ (R (Ql).let) (T2 lo pc n₃) d d')
      (frame2Err S₁ N₁ N₂ Sd₁ Sd₂ L₁ L₂ R₀ (R (Ql).let) (T2 lo pc n₃) ε₀ (eps (Ql).let)
        (Err.app (Lp).e (Nums.draw K Cb.Gl.E
          (TWhole.ledNx (J := JEnd (sizeOf tl).size Ja Jb Jc) (P := (Dl).X')) Ex
          (n₃ - 1)).err)) :=
  link_at_lay (X' := TX (((Ql).let.X × Dr (sizeOf tl).size) × Cb.Gl.E) Cb.Gl.E
      (Option (Option (JAll Ja Jb Jc)))) (L := (Lp).R) (η := (Lp).e)
    ρ Y tl S₁ N₁ N₂ bk₁ Br ra rb rc funsAt Prod.fst (Tl) (fun x => x.1.1)
    (Qd).endCl i3Y ex Sd₁ Sd₂ L₁ L₂ ok n h₀ Cb.Gl.p hu k₁ k₁'
    (lateU_ok (Ql).let hcols _ _ _ hshape) (fun _ _ => rfl) k₂ (C3 ok n)
    (look_lay ρ Y tl S₁ N₁ N₂ bk₁ Br ra rb rc funsAt hcols jLK ex ok n H hshape k₂ hZZ)
    (digs_zl ρ Y tl S₁ N₁ N₂ bk₁ Br ra rb rc funsAt hcols hZZ)
    (digs_zh ρ Y tl S₁ N₁ N₂ bk₁ Br ra rb rc funsAt hcols hZZ)
    hsh hnm hfirst hfit htree hmS lo pc n₃ hn hP d d' hF₁ hL₁ hE₁ hF₂ hL₂ hE₂

/-- The same with the plain share numbered: the caller's claims from 0 on, the lookup's end claims
from a on. -/
theorem tail_link_numbered (Sd₁ : N₁.Seeds) (Sd₂ : N₂.Seeds) (L₁ : N₁.O → ℕ) (L₂ : N₂.O → ℕ) {N : ℕ}
    (ok : LayOK Y tl N)
    {R₀ : IOR X₀ Ex (Xe × TWhole.Ledger Cb.Gl.E ((Ja ⊕ JCell (sizeOf tl).size) ⊕ Jb)) Ex}
    {A : Rels K X₀ Ex (S₁.Msg × Wp)} {ε₀ : Err R₀.shape} (n : ℕ)
    (h₀ : TWhole.KnowAt R₀ A
      (virtJ (baseAnd (symsLay Y tl ra) Br) (Aff0 ok) (msgV ra (symsLay Y tl ra)) n) idW ε₀)
    (hu : (sizeOf tl).size.Uniq Cb.Gl.p)
    (k₁ k₁' : (S₁.sum N₁).Msg × (Dig Cb.Gl.E (sizeOf tl).size × Wp₂) → K)
    (H : FoNums.ok tl.f9 = true) (hshape : shapeTest2 tl Cb.Gl.p = true)
    (k₂ : ((S₁.sum N₁).sum N₂).Msg × Wp₂ → K)
    (hZZ : ∀ i r c, Y.addr i = .cell tl.ix.ZZ r c → ∃ jc : Jc, i = Sum.inr (Sum.inr jc))
    (hsh : ∀ e, SameShapes tl (funsAt e)) (hnm : tl.NM = tl.mats.size)
    (hfirst : tl.cfFirst = tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0])
    (hfit : Fits tl) (htree : ∀ e, ∀ Fn ∈ (funsAt e).toList, Fn.tree = 2)
    (hmS : ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).mS = Alg.symRows (tl.shp.getD mu {}).m)
    (a pc n₃ : ℕ) (hna : n ≤ a) (hpc : a + (1 + Fo.nRows tl.f9) ≤ pc)
    (hn : ∀ x', pc + topOf (Rc x') (Rc x').funs = n₃)
    (d : S₁.Wit × Wp) (d' : (S₁.sum N₁).Wit × (Dig Cb.Gl.E (sizeOf tl).size × Wp₂))
    (hF₁ : Sd₁.Fair) (hL₁ : ∀ i, (N₁.om i).ListLE (L₁ i)) (hE₁ : ∀ i, (N₁.om i).Evades)
    (hF₂ : Sd₂.Fair) (hL₂ : ∀ i, (N₂.om i).ListLE (L₂ i)) (hE₂ : ∀ i, (N₂.om i).Evades) :
    (frame2Red S₁ N₁ N₂ Sd₁ Sd₂ R₀ (R (Ql).let) (T2 (Lo a) pc n₃)).KnowInto (S₁.over A).on
      (((S₁.sum N₁).sum N₂).over
        (ledOutA (ranCond (baseD (Tl) lf rt k₂ (Dl)) (C3 ok n)) (Dl).msg₃)).on
      (S₁.over A).relR
      (((S₁.sum N₁).sum N₂).over
        (ledOutA (ranCond (baseD (Tl) lf rt k₂ (Dl)) (C3 ok n)) (Dl).msg₃)).relR
      (frame2Ext S₁ N₁ N₂ Sd₁ Sd₂ bk₁ (fun u w => (dgs u, w)) R₀ (R (Ql).let) (T2 (Lo a) pc n₃) d
          d')
      (frame2Err S₁ N₁ N₂ Sd₁ Sd₂ L₁ L₂ R₀ (R (Ql).let) (T2 (Lo a) pc n₃) ε₀ (eps (Ql).let)
        (Err.app (Lp).e (Nums.draw K Cb.Gl.E
          (TWhole.ledNx (J := JEnd (sizeOf tl).size Ja Jb Jc) (P := (Dl).X')) Ex
          (n₃ - 1)).err)) :=
  tail_link_lay ρ Y tl S₁ N₁ N₂ bk₁ Br ra rb rc funsAt hcols jLK ex Sd₁ Sd₂ L₁ L₂ ok n h₀ hu k₁ k₁'
      H
    hshape k₂ hZZ hsh hnm hfirst hfit htree hmS (Lo a) pc n₃ hn
    (cond_lo ρ Y tl S₁ N₁ N₂ bk₁ Br ra rb rc funsAt hcols ex ok n a pc hna hpc)
    d d' hF₁ hL₁ hE₁ hF₂ hL₂ hE₂

end

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.zext_enY
#print axioms OnBytes.Tie.Pv.Tail.via_i3Y
#print axioms OnBytes.Tie.Pv.Tail.cell_late
#print axioms OnBytes.Tie.Pv.Tail.digs_zl
#print axioms OnBytes.Tie.Pv.Tail.digs_zh
#print axioms OnBytes.Tie.Pv.Tail.look_lay
#print axioms OnBytes.Tie.Pv.Tail.cond_lo
#print axioms OnBytes.Tie.Pv.Tail.tail_link_lay
#print axioms OnBytes.Tie.Pv.Tail.tail_link_numbered
