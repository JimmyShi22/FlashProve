-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/InSubLay.lean: the link of a sub-proof (`sub_link_fr_batch_of`,
Cb/Pv/Tail/InSubOf.lean) at letters that are read off a lay of the committed entries and a record of
the verifier: one value at which the smallness test's premises on letters are paid together.

The letters: the early entries are Ja and the cells behind the committed symbols; the late entries
are the entries Jb of the reads' message; the symbols, the vector of reads and the tables' weights
are the readings of OnBytes/Tie/Pv/Tail/HostLay.lean; the entries at the link's end are the sum of
Cb/Pv/Tail/HostSum.lean; the lookup's end claims are carried onto these along a partial map `i3`
(Cb/Pv/Tail/PushO.lean); the ledger that is laid is `layP` (OnBytes/Tie/Pv/Tail/MeetLay.lean): the
caller's claims and the lookup's end claims under exponents of their own (`lo`), the verifier's own
rows at the record of the statement.

Main names:
  `symsLay`, `wLay`, `tabLay`, `hostLay`: the frame's letters. `isT_lay`: its reads are given by
    tables.
  `affLay`, `haff_lay`: the forms of the late entries; the second law of Cb/Pv/Tail/InLink.lean.
  `tail3Lay`: the letters of the last block. `recOf`: the record of a statement behind the lookup.
  `link_at_lay`: `sub_link_fr_batch_of`'s statement at these values. Paid here: `Size.OK`; the three
    laws `hcell`, `haff`, `htab`; the laws on the entries at the link's end; the law on the reads
    that are not kept; the two premises on the ledger that is laid.

Limits: premises of `link_at_lay` that are left: the front's `KnowAt`; the two sendings' six; the
three inequalities `Size.Uniq`; the lookup's letters T with `DatOK` and `Reads`, its `KnowAt`
between the two conditions, and that the digits read off the late message are the cells of the
digits' array; on public data: `LayOK`, `SameShapes`, `Fits`, every table in the third vector, the
shapes' rows of symbols, the record's first columns, pc and the number of indices make n₃; and that
the condition P₃ behind the lookup gives `LoOK`.
`LayOK` asks that the reads' message, as it is read here, holds nothing but the row of reads. That
the values which `i3` gives are the lookup's own entries is the matter of the lookup's `KnowAt`.
Equality of entries is decided classically.
Which record tl is meant: in a plan's own record the list of tables and the list of first columns
are still empty (a run fills them): there the premise on the first columns fails and `SameShapes`
lets no statement have a table, so the premises cannot hold together at a real sub-proof.
`link_at_lay` is meant at a record in which the tables' shapes and the first columns are laid
(`closedAt`); none is built here.
The lay Y is a letter: a lay that lacks the entries of the digits' array or of the mask row keeps
every premise true, and then what is said of the digits is empty. The theorem is meant at the lay of
the link's own shape.
The plain share `lo` with its exponents is a letter too: that these are the exponents under which
the verifier weighs its claims is not said. A share that is numbered in a row serves the link's
soundness; at a layers' sub-proof it is not the form that the verifier tests.
The draw that batches the ledger follows the lookup on the digits at once. The head's sub-proof has
further rounds between the smallness test's messages and its closing draw: it is not covered.

-/
import Cb.Pv.Tail.InSubOf
import Cb.Pv.Tail.PushO
import OnBytes.Tie.Pv.Tail.HostLay
import OnBytes.Tie.Pv.Tail.MeetLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Road.Rows OnBytes.Tie.Pv.Tail.Port Cb.Pv.Tail
open Iop Prob Hiop Cb IOR Reduction Cb.Sub Cb.Pv.Att Cb.LdLkp CbQ

open scoped Classical

variable {E : Type} [Field E] [Fintype E] {Ja Jb Jc : Type} [Fintype Ja] [Fintype Jb] [Fintype Jc]
  (ρ : Reading E) (Y : Lay (JAll Ja Jb Jc)) (tl : HTailF2) {X₀ Xe : Type} {Ex : ExtSpec}

/-- The symbols, read off the early entries. -/
def symsLay {M₁ : Type} (ra : M₁ → Ja → E) (m : M₁) : Syms E (sizeOf tl).size :=
  fun μ i' c => symLay Y tl (ra m) μ i' c

/-- The reads' weights: the tables' weights of the statement, on their stretches. -/
def wLay (funsAt : Xe → Array HFun) (e : Xe) (μ : Fin (sizeOf tl).size.NM)
    (r : Fin ((sizeOf tl).size.nr μ)) (i : Fin ((sizeOf tl).size.m μ)) : E :=
  wOf (sizeOf tl) (phiLay ρ (funsAt e)) μ r i

/-- The reads: the entries of the vector of reads at the tables' places. -/
def tabLay {U₁ : Type} (rb : U₁ → Jb → E) (u : U₁) (μ : Fin (sizeOf tl).size.NM)
    (r : Fin ((sizeOf tl).size.nr μ)) (c : Fin ((sizeOf tl).size.k μ)) : E :=
  tabOf (sizeOf tl) (u3Lay Y tl (rb u)) μ r c

section
variable {K Wp Wp₁ Wp₂ : Type} (S₁ N₁ N₂ : Sig E) (bk₁ : N₁.Msg → Wp₁ → Wp)
  (Br : Rels K Xe Ex (S₁.Msg × Wp)) (ra : S₁.Msg → Ja → E) (rb : N₁.Msg → Jb → E)
  (rc : N₂.Msg → Jc → E) (funsAt : Xe → Array HFun) (dig : Wp₁ → Dig E (sizeOf tl).size)

/-- The frame's letters at the lay. -/
noncomputable abbrev hostLay : Host E (sizeOf tl).size (Ja ⊕ JCell (sizeOf tl).size) Jb :=
  hostAt S₁ N₁ bk₁ Br (msgV ra (symsLay Y tl ra)) rb (wLay ρ tl funsAt) (symsLay Y tl ra)
    (tabLay Y tl rb) dig

omit [Fintype E] in
theorem isT_lay : IsT (hostLay ρ Y tl S₁ N₁ bk₁ Br ra rb funsAt dig)
    (fun e => phiLay ρ (funsAt e)) (fun m => symLay Y tl (ra m)) fun u => u3Lay Y tl (rb u) :=
  ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

local notation "Ql" => hostLay ρ Y tl S₁ N₁ bk₁ Br ra rb funsAt dig

/-- The form of a late entry: the form of its read, on the cells' places. -/
noncomputable def affLay {N : ℕ} (ok : LayOK Y tl N) (e : Xe) (b : Jb) :
    TWhole.Aff E (Ja ⊕ JCell (sizeOf tl).size) :=
  affV (J₀ := Ja) (Ql).let (e, []) (itLay Y tl ok b)

omit [Fintype E] in
theorem haff_lay {N : ℕ} (ok : LayOK Y tl N) (x : (Ql).let.X) (b : Jb)
    (v : Ja ⊕ JCell (sizeOf tl).size → E) :
    (affLay ρ Y tl S₁ N₁ bk₁ Br ra rb funsAt dig ok x.1 b).val v =
      (affRead (Ql).let x (itLay Y tl ok b)).val fun i => v (Sum.inr i) :=
  haff_val (Ql).let (x.1, []) (itLay Y tl ok b) v

set_option quotPrecheck false in
local notation "lf" => (S₁.sum N₁).left N₂ (T := OMsg.Msg)
set_option quotPrecheck false in
local notation "rt" => (S₁.sum N₁).right N₂ (T := OMsg.Msg)

variable (T : LateU (hostLay ρ Y tl S₁ N₁ bk₁ Br ra rb funsAt dig).let N₂.Msg Wp₂) [Fintype T.J]
  {X' : Type}
  (pr : X' → (hostLay ρ Y tl S₁ N₁ bk₁ Br ra rb funsAt dig).let.X × Dr (sizeOf tl).size)
  (endT : X' → TWhole.Ledger E T.J) (i3 : T.J → Option (JEnd (sizeOf tl).size Ja Jb Jc))
  (ex : Exps (sizeOf tl).size)

/-- The letters of the last block at the lay. -/
noncomputable abbrev tail3Lay : Tail3 (Ql) ((S₁.sum N₁).sum N₂).Msg
    (JEnd (sizeOf tl).size Ja Jb Jc) where
  X' := X'
  pr := pr
  msg₃ := msgEnd ra rb rc (fun m => S₁.left N₁ (T := OMsg.Msg) (lf m))
    (fun m => S₁.right N₁ (T := OMsg.Msg) (lf m)) rt (symsLay Y tl ra)
    fun m => vals (Ql).let (lf m) (T.digs (rt m))
  endCl := fun x' => (endT x').map (pushO i3)
  i12 := i12E
  is := isE
  e := ex
  keep := keepT (sizeOf tl)

/-- The record of a statement behind the lookup. -/
def recOf (x' : X') : HTailF2 := recLay tl (funsAt (pr x').1.1) (pr x').2

local notation "Dl" => tail3Lay ρ Y tl S₁ N₁ N₂ bk₁ Br ra rb rc funsAt dig T pr endT i3 ex
local notation "Rc" => recOf ρ Y tl S₁ N₁ bk₁ Br ra rb funsAt dig pr

/-- The link of a sub-proof at the lay: the smallness test's premises on letters are paid. -/
theorem link_at_lay (Sd₁ : N₁.Seeds) (Sd₂ : N₂.Seeds) (L₁ : N₁.O → ℕ) (L₂ : N₂.O → ℕ) {N : ℕ}
    (ok : LayOK Y tl N)
    {R₀ : IOR X₀ Ex (Xe × TWhole.Ledger E ((Ja ⊕ JCell (sizeOf tl).size) ⊕ Jb)) Ex}
    {A : Rels K X₀ Ex (S₁.Msg × Wp)} {ε₀ : Err R₀.shape} (n : ℕ)
    (h₀ : TWhole.KnowAt R₀ A
      (virtJ (baseAnd (symsLay Y tl ra) Br) (affLay ρ Y tl S₁ N₁ bk₁ Br ra rb funsAt dig ok)
        (msgV ra (symsLay Y tl ra)) n) idW ε₀)
    (p : ℕ) [CharP E p] (hu : (sizeOf tl).size.Uniq p)
    (k₁ k₁' : (S₁.sum N₁).Msg × Wp₁ → K) {pp : ℕ}
    (hQ : T.Q.DatOK (sizeOf tl).size.lo (sizeOf tl).size.hi pp) (hr : T.Reads)
    (k₂ : ((S₁.sum N₁).sum N₂).Msg × Wp₂ → K)
    {L : IOR ((Xe × TWhole.Ledger E ((Ja ⊕ JCell (sizeOf tl).size) ⊕ Jb)) ×
      Dr (sizeOf tl).size) Ex X' Ex} {η : Err L.shape} (P₃ : X' × Ex.Str → Prop)
    (hL : TWhole.KnowAt L
      (ranCond (T.inD₁ lf rt k₂) fun b =>
        (virtJ (baseAnd (symsLay Y tl ra) Br) (affLay ρ Y tl S₁ N₁ bk₁ Br ra rb funsAt dig ok)
          (msgV ra (symsLay Y tl ra)) n).on (b.1.1, b.2))
      (ranCond (outD T lf rt k₂ (Dl)) P₃) idW η)
    (hzl : ∀ m μ v i, (T.digs (rt m)).zl μ v i =
      Y.cellAt (Sum.elim (ra (S₁.left N₁ (T := OMsg.Msg) (lf m)))
        (Sum.elim (rb (S₁.right N₁ (T := OMsg.Msg) (lf m))) (rc (rt m)))) tl.ix.ZZ v
        ((tl.zzCol μ 0 0).getD 0 + i))
    (hzh : ∀ m μ v i, (T.digs (rt m)).zh μ v i =
      Y.cellAt (Sum.elim (ra (S₁.left N₁ (T := OMsg.Msg) (lf m)))
        (Sum.elim (rb (S₁.right N₁ (T := OMsg.Msg) (lf m))) (rc (rt m)))) tl.ix.ZZ v
        ((tl.zzCol μ 1 0).getD 0 + i))
    (hsh : ∀ e, SameShapes tl (funsAt e)) (hnm : tl.NM = tl.mats.size)
    (hfirst : tl.cfFirst = tl.mats.foldl (fun a M => a.push (a.getD (a.size - 1) 0 + M.k)) #[0])
    (hfit : Fits tl) (htree : ∀ e, ∀ Fn ∈ (funsAt e).toList, Fn.tree = 2)
    (hmS : ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).mS = Alg.symRows (tl.shp.getD mu {}).m)
    (lo : X' → List (ℕ × TWhole.Form E (JEnd (sizeOf tl).size Ja Jb Jc))) (pc n₃ : ℕ)
    (hn : ∀ x', pc + topOf (Rc x') (Rc x').funs = n₃)
    (hP : ∀ x' y, P₃ (x', y) → LoOK (Dl) lo pc x')
    (d : S₁.Wit × Wp) (d' : (S₁.sum N₁).Wit × Wp₁)
    (hF₁ : Sd₁.Fair) (hL₁ : ∀ i, (N₁.om i).ListLE (L₁ i)) (hE₁ : ∀ i, (N₁.om i).Evades)
    (hF₂ : Sd₂.Fair) (hL₂ : ∀ i, (N₂.om i).ListLE (L₂ i)) (hE₂ : ∀ i, (N₂.om i).Evades) :
    (frame2Red S₁ N₁ N₂ Sd₁ Sd₂ R₀ (R (Ql).let)
        ((L.post (fun x' => some (x', layP ρ Y (Dl) (Rc) iJE lo pc n₃ x')) (ExtMap.id Ex)).seq
          (IOR.draw E (TWhole.ledNx (J := JEnd (sizeOf tl).size Ja Jb Jc) (P := X'))
            Ex))).KnowInto (S₁.over A).on
      (((S₁.sum N₁).sum N₂).over
        (ledOutA (ranCond (baseD T lf rt k₂ (Dl)) P₃) (Dl).msg₃)).on (S₁.over A).relR
      (((S₁.sum N₁).sum N₂).over
        (ledOutA (ranCond (baseD T lf rt k₂ (Dl)) P₃) (Dl).msg₃)).relR
      (frame2Ext S₁ N₁ N₂ Sd₁ Sd₂ bk₁ T.bk R₀ (R (Ql).let)
        ((L.post (fun x' => some (x', layP ρ Y (Dl) (Rc) iJE lo pc n₃ x')) (ExtMap.id Ex)).seq
          (IOR.draw E (TWhole.ledNx (J := JEnd (sizeOf tl).size Ja Jb Jc) (P := X'))
            Ex)) d d')
      (frame2Err S₁ N₁ N₂ Sd₁ Sd₂ L₁ L₂ R₀ (R (Ql).let)
        ((L.post (fun x' => some (x', layP ρ Y (Dl) (Rc) iJE lo pc n₃ x')) (ExtMap.id Ex)).seq
          (IOR.draw E (TWhole.ledNx (J := JEnd (sizeOf tl).size Ja Jb Jc) (P := X')) Ex))
        ε₀ (eps (Ql).let)
        (Err.app η (Nums.draw K E
          (TWhole.ledNx (J := JEnd (sizeOf tl).size Ja Jb Jc) (P := X')) Ex
          (n₃ - 1)).err)) := by
  have hT := isT_lay ρ Y tl S₁ N₁ bk₁ Br ra rb funsAt dig
  have paid := lay_paid ρ Y T lf rt (Dl) (Rc) iJE lo pc n₃ hT
    (fun x' => sizeOf_recLay tl _ (hsh _) _) (fun _ _ => rfl)
    (fun x' m => atT_lay ρ Y tl (Ql) ra rb rc funsAt ok hsh hnm hfirst (pr x').1 (lf m) (rt m)
      (T.digs (rt m)) (pr x').2 (hzl m) (hzh m))
    (fun x' => fits_recLay tl hfit _ _) (fun x' => htree _) (fun _ => hmS) hn P₃ hP
  exact sub_link_fr_batch_of S₁ N₁ N₂ Sd₁ Sd₂ L₁ L₂ bk₁ Br (msgV ra (symsLay Y tl ra)) rb
    (wLay ρ tl funsAt) (symsLay Y tl ra) (tabLay Y tl rb) dig
    (affLay ρ Y tl S₁ N₁ bk₁ Br ra rb funsAt dig ok) n h₀ (sizeOf_ok tl) p hu Sum.inr
    (itLay Y tl ok) (fun _ _ => rfl) (haff_lay ρ Y tl S₁ N₁ bk₁ Br ra rb funsAt dig ok)
    (fun u b => htab_lay Y tl ok (rb u) b) k₁ k₁' T hQ hr k₂ (Dl) P₃ hL
    (fun m j => h12E ra rb rc (fun m => S₁.left N₁ (T := OMsg.Msg) (lf m))
      (fun m => S₁.right N₁ (T := OMsg.Msg) (lf m)) rt (symsLay Y tl ra)
      (fun m => vals (Ql).let (lf m) (T.digs (rt m))) m j) (fun _ _ => rfl)
    (fun x msg μ r h => hk_thetaQ hT x msg μ r h)
    (layP ρ Y (Dl) (Rc) iJE lo pc n₃) n₃ paid.1 paid.2 d d' hF₁ hL₁ hE₁ hF₂ hL₂ hE₂

end

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.isT_lay
#print axioms OnBytes.Tie.Pv.Tail.haff_lay
#print axioms OnBytes.Tie.Pv.Tail.link_at_lay
