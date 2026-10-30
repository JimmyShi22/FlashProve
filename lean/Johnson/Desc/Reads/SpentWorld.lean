-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/SpentWorld.lean: the pieces of Reads/Bridge.lean joined, and Reads/Pull.lean at
sizes that are the row's.

All of this file is a tool: it holds for all letters, records, lays and worlds, and names no
description of the protocol.

Why. Reads/Bridge.lean has three pieces: `spent` at the library's letters of the smallness test; the
premise on virtual rows (`RowsAre`), under which a form's part in U3 is the value in a world of its
entries of that array; and the place of a cell in the library's vector of reads. They meet only
where the row's letter cols is the K3 of `thetaAt` and the row's letter iU3 is its iU3. Here they
are joined, with these two equalities built in: `thetaAt` is taken at `L.iU3 l` and `L.cols l`.

What is here.
  `allU3B_of`: the Boolean `allU3B` from the statement "every table of the list lies in the third
    vector".
  `spent_world`: from the row, `Spent` and `RowsAre` at the committed vector of reads: one family of
    integer matrices, small and with the committed packing, such that for every form of the link the
    value in the world of the form's entries of U3 is the sum of what the uses of that form mean,
    each times the clause's coefficient.
  `rows_of_cells`: where entry i of virtual row r of the array is cell (iU3, r, i) of the lay, for i
    below K3, `RowsAre` holds at the library's vector of reads.
  `spent_cells`: the three together, at `thetaAt ρ Y (L.tl l s) (L.iU3 l) (L.cols l)`.
  `pull_at`: `pull_of_row` (Reads/Pull.lean) at letters of sizes t with `L.size l s = t`.

Premises of `spent_cells` that the row does not give: the letter val is a reading's map; the letter
funs is the list of the state's record; every table of it lies in the third vector; and in the world
W the virtual rows of U3's array are its rows.

Of OnBytes/Model/ this file names what Reads/Bridge.lean names.

Limits. That U3's virtual rows are its rows is a premise here. It is shown of no state and no
description. Nothing is said of a form's slots, its constant or its entries of other arrays. Nothing
on soundness.


-/
import Johnson.Desc.Reads.Bridge
import Johnson.Desc.Reads.Pull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads

open Cb.Pv.Tail Iop
open OnBytes (E zeroE)
open OnBytes.Model (HTailF2 HFun Aff Ent Reading World)
open OnBytes.Road.Rows (Lay)
open OnBytes.Tie.Pv.Tail (thetaAt)

variable {K : Type}

/-- The Boolean from the statement. -/
theorem allU3B_of {funs : Array HFun} (h : ∀ Fn ∈ funs.toList, Fn.tree = 2) :
    allU3B funs = true :=
  List.all_eq_true.2 fun Fn hFn => beq_iff_eq.2 (h Fn hFn)

/-- **What is spent, in a world.** -/
theorem spent_world [CommRing K] (ρ : Reading K) (L : Letters K) (hval : L.val = ρ.val)
    (H : ClaimReadSameIndex L) {l : L.Link} (hl : l ∈ L.links) {s : L.State}
    (hs : L.AtClose l s) {t : TSize} (Θ : TLetters K t) {msg : Θ.M} (hS : Spent L l s Θ msg)
    (W : World K) (hW : RowsAre W (L.iU3 l) (L.cols l) (Θ.u3 msg)) :
    ∃ a : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < t.NM → ∀ c, c < t.k μ → ∀ i, i < t.m μ → |a μ c i| < 2 * (t.beta : ℤ)) ∧
      (∀ μ, μ < t.NM → ∀ c, c < t.k μ → ∀ i', i' < Alg.symRows (t.m μ) →
        Θ.sym msg μ i' c =
          ((Alg.pack (t.rad : ℤ) (fun i : Fin (t.m μ) => a μ c i) i' : ℤ) : K)) ∧
      ∀ (n : ℕ) (f : Aff), (L.forms l s)[n]? = some f →
        ((f.ents.toList.filter fun x => x.tree == L.iU3 l).map (Ent.value ρ W)).sum =
          ((L.usesAt l n).map fun u => L.coef l s u * (L.meant l s u).sum a).sum := by
  obtain ⟨a, h1, h2, -, h4⟩ := hS
  refine ⟨a, h1, h2, fun n f hf => ?_⟩
  rw [← u3Value_world ρ hW f ((H l hl s hs).2.2.2 n f hf).1, ← hval]
  exact h4 n f hf

/-- Where the virtual rows of the array are its rows, the premise on virtual rows holds at the
library's vector of reads. -/
theorem rows_of_cells {J : Type} [Field K] [Fintype J] (Y : Lay J) (tl : HTailF2) (iU3 K3 : ℕ)
    (m : OnBytes.Tie.Pv.Tail.JE Y tl → K) (W : World K)
    (hW : ∀ r i, i < K3 →
      W.entry iU3 r i = Y.cellAt (OnBytes.Tie.Pv.Tail.glue Y tl m fun _ => 0) iU3 r i) :
    RowsAre W iU3 K3 (OnBytes.Tie.Pv.Tail.u3At Y tl iU3 K3 m) :=
  fun r i hi => (hW r i hi).trans (rows_u3At Y tl iU3 K3 m r i hi).symm

/-- **The three pieces together**, at the library's letters with the row's iU3 and cols. -/
theorem spent_cells {J : Type} [Field K] [Fintype J] (ρ : Reading K) (Y : Lay J) (L : Letters K)
    (H : ClaimReadSameIndex L) {l : L.Link} (hl : l ∈ L.links) {s : L.State}
    (hs : L.AtClose l s) (hval : L.val = ρ.val) (hf : L.funs l s = (L.tl l s).funs)
    (h2 : allU3B (L.tl l s).funs = true) (X : Type) (Ex : ExtSpec) (W₀ : Type)
    (ride : X × Ex.Str → (OnBytes.Tie.Pv.Tail.JE Y (L.tl l s) → K) →
      Dig K (OnBytes.Tie.Pv.Tail.sizeOf (L.tl l s)).size × W₀ → Prop) {x : X}
    {msg : OnBytes.Tie.Pv.Tail.JE Y (L.tl l s) → K}
    (h : relIn (thetaAt ρ Y (L.tl l s) (L.iU3 l) (L.cols l) X Ex W₀ ride).letters x msg)
    (W : World K)
    (hW : ∀ r i, i < L.cols l → W.entry (L.iU3 l) r i =
      Y.cellAt (OnBytes.Tie.Pv.Tail.glue Y (L.tl l s) msg fun _ => 0) (L.iU3 l) r i) :
    ∃ a : ℕ → ℕ → ℕ → ℤ,
      ∀ (n : ℕ) (f : Aff), (L.forms l s)[n]? = some f →
        ((f.ents.toList.filter fun x => x.tree == L.iU3 l).map (Ent.value ρ W)).sum =
          ((L.usesAt l n).map fun u => L.coef l s u * (L.meant l s u).sum a).sum := by
  obtain ⟨a, -, -, h3⟩ := spent_world ρ L hval H hl hs
    (thetaAt ρ Y (L.tl l s) (L.iU3 l) (L.cols l) X Ex W₀ ride)
    (spent_thetaAt ρ Y L H hl hs hval hf h2 (L.iU3 l) (L.cols l) X Ex W₀ ride h) W
    (rows_of_cells Y (L.tl l s) (L.iU3 l) (L.cols l) msg W hW)
  exact ⟨a, h3⟩

/-- pull_of_row, at letters of sizes that are the row's. -/
theorem pull_at [Field K] (L : Letters K) (H : ClaimReadSameIndex L) {l : L.Link}
    (hl : l ∈ L.links) {s : L.State} (hs : L.AtClose l s) {t : TSize} (ht : L.size l s = t)
    (Θ : TLetters K t) (x : Θ.X) (hphi : Θ.phi x = L.phi l s) (ha : Apart t) (N : ℕ)
    (hN : ∀ u ∈ L.uses l, L.place l u < N) (v : JCell t.size → K) :
    (∀ u ∈ L.uses l, pulled Θ x N v (L.place l u) = (L.meant l s u).sumAt (atCell v)) ∧
      ∀ (n : ℕ) (f : Aff), (L.forms l s)[n]? = some f →
        u3Value L.val (L.iU3 l) (L.cols l) f (pulled Θ x N v) =
          ((L.usesAt l n).map fun u => L.coef l s u * (L.meant l s u).sumAt (atCell v)).sum := by
  subst ht
  exact pull_of_row L H hl hs Θ x hphi ha N hN v

end VerifiableInference.Reads

#print axioms VerifiableInference.Reads.allU3B_of
#print axioms VerifiableInference.Reads.spent_world
#print axioms VerifiableInference.Reads.rows_of_cells
#print axioms VerifiableInference.Reads.spent_cells
#print axioms VerifiableInference.Reads.pull_at
