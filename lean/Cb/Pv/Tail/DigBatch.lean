-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tail/DigBatch.lean: the last block of a sub-proof's link: the lookup on the digits, the laying
of one ledger, and the draw that batches it; its `KnowAt` from the lookup's own.

The link of a sub-proof (`sub_link_dig`, Cb/Pv/Tail/InSubSeam.lean) asks `KnowAt` of its last block
from the joint `inD₁` at which the lookup on the digits starts. Through the lookup there ride: the
base joint in front of the first sending; the caller's ledger of plain claims; every tie and every
read of the smallness test. Behind the lookup all of these but the base joint, and the lookup's own
end claims, are laid as one ledger on the entries of all messages, and one element is drawn that
batches the ledger into one form. The base joint rides on beside the draw
(`batchA_knowAt`, Cb/Pv/Att/BatchRide.lean).

Main names:
  `pushF`, `pushF_holds`: a form on entries J, carried along a map of J into more entries.
  `eqs_of_cl`: if the claims of the smallness test hold (Cb/Pv/Tail/Claims.lean), every tie and
    every read does.
  `Tail3`: the letters: the lookup's output statement X' and what it keeps of the statement in
    front (`pr`); the entries of all messages (`J₃`, `msg₃`); the lookup's end claims (`endCl`); the
    places of the caller's entries (`i12`) and of the test's entries (`is`) among them.
  `outD`: the joint behind the lookup: what rides, and the lookup's end claims hold.
  `baseD`: the base joint in front of the first sending, read at the messages of the whole link.
  `layD`: the one ledger: the caller's claims, the lookup's end claims, the ties, the kept reads.
  `outD_of_lay`: under two laws on `msg₃` (`h12`, `hs`) and the law on the reads that are not kept:
    the base joint and the one ledger give `outD`.
  `dig_know`: `KnowAt` of the lookup, the laying and the draw in a row, from `inD₁` to "the base
    joint, and the one form holds", with the lookup's errors and then n - 1 for a ledger of at most
    n claims. General in the ledger `lay` that is laid, if it gives `layD`. Conditions on statements
    stand beside the joints (`ranCond`, Cb/Pv/Att/RanCond.lean): P₂ in front of the lookup, P₃
    behind it: the bound on the ledger's length and "it gives `layD`" are asked under P₃ alone.
  `hlay_layout`: at one statement: a ledger that is laid out by exponents (`layout`,
    Cb/Pv/Tail/Claims.lean) gives `layD`, if its list has every form of `layD`, with exponents that
    differ and are below n.

Limits: the lookup is a letter: its `KnowAt` from `inD₁` under P₂ to `outD` under P₃ is a premise.
The caller's ledger stands in the statement, and the lookup's end claims are read off its output
statement: without a condition that bounds both no n serves. The ledger is
batched by the places of its claims; that these places are a program's exponents is not said.
Nothing on an honest prover.


Terms: lean/GLOSSARY.md.
-/
import Cb.Pv.Att.BatchRide
import Cb.Pv.Att.RanCond
import Cb.Pv.Tail.InSubSeam

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail
open Iop Prob Cb IOR TWhole Cb.Pv.Att

/-! ## A form carried along a map of the entries -/

section Push
variable {E J J' : Type} [Field E] [Fintype J] [Fintype J'] [DecidableEq J']

/-- The form f on the entries J, as a form on the entries J', along i : J → J'. -/
def pushF (i : J → J') (f : Form E J) : Form E J' :=
  ⟨fun j' => ∑ j, if i j = j' then f.co j else 0, f.tg⟩

theorem pushF_gap (i : J → J') (f : Form E J) (m : J' → E) :
    (pushF i f).gap m = f.gap fun j => m (i j) := by
  unfold pushF Form.gap
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by simp [ite_mul, Finset.sum_ite_eq]

theorem pushF_holds (i : J → J') (f : Form E J) (m : J' → E) :
    (pushF i f).Holds m ↔ f.Holds fun j => m (i j) := by
  unfold Form.Holds
  rw [pushF_gap]

theorem pushL_holds (i : J → J') (L : Ledger E J) (m : J' → E) :
    Ledger.Holds (L.map (pushF i)) m ↔ Ledger.Holds L fun j => m (i j) := by
  unfold Ledger.Holds
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact forall₂_congr fun f _ => pushF_holds i f m

end Push

variable {K : Type} [Field K] {s : Size}

/-- If the claims of the smallness test hold, every tie and every read does. -/
theorem eqs_of_cl (Λ : Letters K s) (e : Exps s) (keep : ∀ μ : Fin s.NM, Fin (s.nr μ) → Bool)
    (x : Λ.X) (β : Dr s) (msg : Λ.M) (Z : Dig K s)
    (hk : ∀ μ r, keep μ r = false → (∀ i, Λ.w x μ r i = 0) ∧ ∀ c, Λ.tab msg μ r c = 0)
    (h : (cl Λ e keep (x, β)).Holds (vals Λ msg Z)) : Late.Eqs x β msg Z := by
  refine ⟨fun μ u i' => (tie_iff Λ β msg Z μ u i').1 (h _ ?_), fun μ u r => ?_⟩
  · exact List.mem_map.2 ⟨(e.tie μ u i', tieForm β μ u i'),
      List.mem_append_left _ (List.mem_flatMap.2 ⟨μ, List.mem_finRange _,
        List.mem_flatMap.2 ⟨u, List.mem_finRange _,
          List.mem_map.2 ⟨i', List.mem_finRange _, rfl⟩⟩⟩), rfl⟩
  · cases hr : keep μ r with
    | false =>
      obtain ⟨h1, h2⟩ := hk μ r hr
      simp [h1, h2]
    | true =>
      refine (read_iff Λ x β msg Z μ u r).1 (h _ ?_)
      exact List.mem_map.2 ⟨(e.read μ u r, readForm Λ x β μ u r),
        List.mem_append_right _ (List.mem_flatMap.2 ⟨μ, List.mem_finRange _,
          List.mem_flatMap.2 ⟨u, List.mem_finRange _,
            List.mem_map.2 ⟨r, List.mem_filter.2 ⟨List.mem_finRange _, hr⟩, rfl⟩⟩⟩), rfl⟩

/-! ## The letters -/

variable {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂]

/-- What the last block brings beside the frame's letters Q and the seam's letters T. -/
structure Tail3 (Q : Host K s J₁ J₂) (MM J₃ : Type) where
  /-- the lookup's output statement, and what it keeps of the statement in front -/
  X' : Type
  pr : X' → Q.let.X × Dr s
  /-- the entries of all messages -/
  msg₃ : MM → J₃ → K
  /-- the lookup's end claims -/
  endCl : X' → Ledger K J₃
  /-- the places of the caller's entries and of the smallness test's entries -/
  i12 : J₁ ⊕ J₂ → J₃
  is : J s → J₃
  /-- the exponents of the test's claims, and which reads are kept -/
  e : Exps s
  keep : ∀ μ : Fin s.NM, Fin (s.nr μ) → Bool

variable {Q : Host K s J₁ J₂} {U W₀ MM J₃ : Type} [Fintype J₃] [DecidableEq J₃]
  (T : LateU Q.let U W₀) (left : MM → Q.M) (right : MM → U) (k₂ : MM × W₀ → Q.Kc)
  (D : Tail3 Q MM J₃)

/-- The joint behind the lookup: what rides, and the lookup's end claims hold. -/
def outD : Rels Q.Kc D.X' Q.Ex (MM × W₀) where
  rel x y v := (T.eqs₁ left right k₂).relR (D.pr x, y) v ∧ Ledger.Holds (D.endCl x) (D.msg₃ v.1)
  relR b v :=
    (T.eqs₁ left right k₂).relR (D.pr b.1, b.2) v ∧ Ledger.Holds (D.endCl b.1) (D.msg₃ v.1)
  on _ := True
  core := k₂

/-- The base joint in front of the first sending, read at the messages of the whole link. -/
def baseD : Rels Q.Kc D.X' Q.Ex (MM × W₀) where
  rel x y v := Q.B₀.relR ((D.pr x).1.1, y)
    (Q.left (left v.1), Q.bk₁ (Q.right (left v.1)) (T.bk (right v.1) v.2))
  relR b v := Q.B₀.relR ((D.pr b.1).1.1, b.2)
    (Q.left (left v.1), Q.bk₁ (Q.right (left v.1)) (T.bk (right v.1) v.2))
  on _ := True
  core := k₂

/-- The one ledger: the caller's claims, the lookup's end claims, the ties and the kept reads. -/
def layD (x' : D.X') : Ledger K J₃ :=
  (D.pr x').1.2.map (pushF D.i12) ++
    (D.endCl x' ++ (cl Q.let D.e D.keep (D.pr x')).map (pushF D.is))

/-- The base joint and the one ledger give the joint behind the lookup. -/
theorem outD_of_lay
    (h12 : ∀ m j, D.msg₃ m (D.i12 j) =
      Sum.elim (Q.msg₁ (Q.left (left m))) (Q.ent (Q.right (left m))) j)
    (hs : ∀ m j, D.msg₃ m (D.is j) = vals Q.let (left m) (T.digs (right m)) j)
    (hk : ∀ (x : Q.let.X) (msg : Q.let.M) μ r, D.keep μ r = false →
      (∀ i, Q.let.w x μ r i = 0) ∧ ∀ c, Q.let.tab msg μ r c = 0)
    (x' : D.X') (y : Q.Ex.Str) (v : MM × W₀) (hb : (baseD T left right k₂ D).relR (x', y) v)
    (hl : Ledger.Holds (layD D x') (D.msg₃ v.1)) : (outD T left right k₂ D).relR (x', y) v := by
  have g1 : Ledger.Holds ((D.pr x').1.2.map (pushF D.i12)) (D.msg₃ v.1) :=
    fun f hf => hl f (List.mem_append_left _ hf)
  have g2 : Ledger.Holds (D.endCl x') (D.msg₃ v.1) :=
    fun f hf => hl f (List.mem_append_right _ (List.mem_append_left _ hf))
  have g3 : Ledger.Holds ((cl Q.let D.e D.keep (D.pr x')).map (pushF D.is)) (D.msg₃ v.1) :=
    fun f hf => hl f (List.mem_append_right _ (List.mem_append_right _ hf))
  rw [pushL_holds, show (fun j => D.msg₃ v.1 (D.i12 j)) = _ from funext (h12 v.1)] at g1
  rw [pushL_holds, show (fun j => D.msg₃ v.1 (D.is j)) = _ from funext (hs v.1)] at g3
  exact ⟨⟨⟨hb, g1⟩, eqs_of_cl Q.let D.e D.keep (D.pr x').1 (D.pr x').2 (left v.1)
    (T.digs (right v.1)) (fun μ r h => hk _ _ μ r h) g3⟩, g2⟩

/-- The last block: the lookup, the laying of a ledger, the draw that batches it. -/
theorem dig_know [Fintype K] {L : IOR (Q.let.X × Dr s) Q.Ex D.X' Q.Ex} {η : Err L.shape}
    (P₂ : (Q.let.X × Dr s) × Q.Ex.Str → Prop) (P₃ : D.X' × Q.Ex.Str → Prop)
    (hL : KnowAt L (ranCond (T.inD₁ left right k₂) P₂) (ranCond (outD T left right k₂ D) P₃)
      (fun _ _ _ wp => wp) η)
    (h12 : ∀ m j, D.msg₃ m (D.i12 j) =
      Sum.elim (Q.msg₁ (Q.left (left m))) (Q.ent (Q.right (left m))) j)
    (hs : ∀ m j, D.msg₃ m (D.is j) = vals Q.let (left m) (T.digs (right m)) j)
    (hk : ∀ (x : Q.let.X) (msg : Q.let.M) μ r, D.keep μ r = false →
      (∀ i, Q.let.w x μ r i = 0) ∧ ∀ c, Q.let.tab msg μ r c = 0)
    (lay : D.X' → Ledger K J₃) (n : ℕ) (hn : ∀ x' y, P₃ (x', y) → (lay x').length ≤ n)
    (hlay : ∀ x' y m, P₃ (x', y) → Ledger.Holds (lay x') (D.msg₃ m) →
      Ledger.Holds (layD D x') (D.msg₃ m)) :
    KnowAt ((L.post (fun x' => some (x', lay x')) (ExtMap.id Q.Ex)).seq
        (IOR.draw K (ledNx (J := J₃) (P := D.X')) Q.Ex))
      (ranCond (T.inD₁ left right k₂) P₂)
      (ledOutA (ranCond (baseD T left right k₂ D) P₃) D.msg₃) (fun _ _ _ wp => wp)
      (Err.app η (Nums.draw Q.Kc K (ledNx (J := J₃) (P := D.X')) Q.Ex (n - 1)).err) :=
  knowAt_seq
    (knowAt_postMap (B' := ledInA (ranCond (baseD T left right k₂ D) P₃) n D.msg₃)
      (fun x' => (x', lay x')) hL (fun x y h => ⟨⟨trivial, h.2⟩, hn x y h.2⟩)
      fun x y w h hw =>
        outD_of_lay T left right k₂ D h12 hs hk x y w hw.1 (hlay x y w.1 h.2 hw.2))
    (batchA_knowAt (ranCond (baseD T left right k₂ D) P₃) n D.msg₃)

/-- At one statement: a ledger that is laid out by exponents gives the one ledger. -/
theorem hlay_layout (n : ℕ) (x' : D.X') (Lx : List (ℕ × Form K J₃))
    (hmem : ∀ f, f ∈ layD D x' → ∃ z ∈ Lx, z.2 = f)
    (hinj : ∀ z ∈ Lx, ∀ z' ∈ Lx, z.1 = z'.1 → z = z') (hlt : ∀ z ∈ Lx, z.1 < n) (m : MM)
    (h : Ledger.Holds (layout n Lx) (D.msg₃ m)) : Ledger.Holds (layD D x') (D.msg₃ m) := by
  intro f hf
  obtain ⟨z, hz, rfl⟩ := hmem f hf
  exact (layout_holds n Lx (D.msg₃ m) hinj hlt).1 h z hz

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.pushF_holds
#print axioms Cb.Pv.Tail.eqs_of_cl
#print axioms Cb.Pv.Tail.outD_of_lay
#print axioms Cb.Pv.Tail.dig_know
#print axioms Cb.Pv.Tail.hlay_layout
