-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/Bridge.lean: what is spent of the row claim_read_same_index (`spent`,
Reads/Stated.lean), at the letters of the smallness test that the library has; and the premise on
virtual rows, by name.

All of this file is a tool: it holds for all letters, records and lays, and names no description of
the protocol.

Why. The row reads the smallness test's sizes and weights as `sizeU3 tl funs` and `phiU3 val funs`:
off a record and a list of tables, the tables of the third vector alone. The library's own letters
of the typed smallness test (`thetaAt`, OnBytes/Tie/Pv/Tail/LettersAt.lean) stand at `sizeOf tl` and
`phiAt`: off the record's own list, all tables. The sizes are an index of the letters' type. Here
the two are shown to be one, under two premises, and `spent` is said again at the library's letters.

The two premises, at a link and a state. The letter funs is the list of the state's record: `L.funs
l s = (L.tl l s).funs`. Every table of that list lies in the third vector (`allU3B`, a Boolean on
the public list). Neither is asked by the row. Both are owed by whoever fills the letters.

What is here.
  `Spent L l s Θ msg`: the conclusion of `spent`, by name, at letters Θ of any sizes.
  `spent_at`: `spent`, at letters Θ of sizes t with `L.size l s = t`.
  `u3Tabs_all`, `sizeU3_eq`, `phiU3_eq`: under the second premise `sizeU3 tl tl.funs = sizeOf tl`,
    and `phiU3 ρ.val tl.funs = phiAt ρ tl`.
  `spent_thetaAt`: `spent` at the library's letters, from the row, the two premises and a reading.

The premise on virtual rows. An entry of a form names a virtual row of its array (`Ent`,
OnBytes/Model/Hide.lean). The row takes that number for the vector's own row (`placeOf`).
  `RowsAre W iU3 cols u`: in the world W, entry i of virtual row r of array iU3 is u (r * cols + i),
    for i below cols. It is owed wherever `spent`'s sum is taken for a part of a form's value.
  `u3Value_world`: under it, and where the entries lie inside their rows, a form's part in U3 at u
    is the value in W of its entries of that array (`Ent.value`, OnBytes/Model/HideLaws.lean).
  `rows_u3At`: the library's vector of reads at (iU3, K3) has cell (iU3, r, i) of the lay at the
    place r * K3 + i. So at these letters `RowsAre` says that entry i of virtual row r is that cell,
    but only where the row's letter cols is K3 and the row's letter iU3 is the iU3 of `thetaAt`. In
    `spent_thetaAt` these two are free numbers beside `L.iU3 l` and `L.cols l`. Neither equality is
    a premise or a clause here, and no theorem joins the three pieces.

    (Where this and lean/THEOREM.md differ, the page holds.)

Of OnBytes/Model/ this file names the records `HTailF2`, `HFun`, `Aff`, `Ent`, `Reading` and
`World`, and the measure `Ent.value`. Over that record it names, from OnBytes/Tie/Pv/Tail/,
`sizeOf`, `phiAt`, `thetaAt`, `JE`, `u3At` and `glue`: definitions that read the record's numbers
and lists. It names no routine of that program, and says nothing of its verdicts.

Limits. It does not say that a description's link runs the smallness test at these letters. That
U3's virtual rows are its rows, in order, is shown nowhere here. Nothing on soundness.


-/
import Johnson.Desc.Reads.Stated
import OnBytes.Tie.Pv.Tail.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads

open Cb.Pv.Tail Iop
open OnBytes (E zeroE)
open OnBytes.Model (HTailF2 HFun Aff Ent Reading World)
open OnBytes.Road.Rows (Lay)
open OnBytes.Tie.Pv.Tail (phiAt thetaAt)

variable {K : Type}

/-- The conclusion of spent, at letters of the smallness test of any sizes: one family of integer
matrices, small and with the committed packing; each use's entry of U3 is the use's sum of cells;
the value of each form's part in U3, at the committed U3, is the sum of what its uses mean, each
times the clause's coefficient. -/
def Spent [CommRing K] (L : Letters K) (l : L.Link) (s : L.State) {t : TSize} (Θ : TLetters K t)
    (msg : Θ.M) : Prop :=
  ∃ a : ℕ → ℕ → ℕ → ℤ,
    (∀ μ, μ < t.NM → ∀ c, c < t.k μ → ∀ i, i < t.m μ → |a μ c i| < 2 * (t.beta : ℤ)) ∧
    (∀ μ, μ < t.NM → ∀ c, c < t.k μ → ∀ i', i' < Alg.symRows (t.m μ) →
      Θ.sym msg μ i' c =
        ((Alg.pack (t.rad : ℤ) (fun i : Fin (t.m μ) => a μ c i) i' : ℤ) : K)) ∧
    (∀ u ∈ L.uses l, Θ.u3 msg (L.place l u) = (L.meant l s u).sum a) ∧
    (∀ (n : ℕ) (f : Aff), (L.forms l s)[n]? = some f →
      u3Value L.val (L.iU3 l) (L.cols l) f (Θ.u3 msg) =
        ((L.usesAt l n).map fun u => L.coef l s u * (L.meant l s u).sum a).sum)

/-- spent, at letters of sizes that are the row's. -/
theorem spent_at [CommRing K] (L : Letters K) (H : ClaimReadSameIndex L) {l : L.Link}
    (hl : l ∈ L.links) {s : L.State} (hs : L.AtClose l s) {t : TSize} (ht : L.size l s = t)
    (Θ : TLetters K t) {x : Θ.X} (hphi : Θ.phi x = L.phi l s) {msg : Θ.M}
    (h : relIn Θ.letters x msg) : Spent L l s Θ msg := by
  subst ht
  exact spent L H hl hs Θ hphi h

/-- Every table of the list lies in the third vector. A Boolean on the public list. -/
def allU3B (funs : Array HFun) : Bool := funs.toList.all fun Fn => Fn.tree == 2

theorem u3Tabs_all {funs : Array HFun} (h : allU3B funs = true) : u3Tabs funs = funs.toList :=
  List.filter_eq_self.2 fun Fn hFn => List.all_eq_true.1 h Fn hFn

/-- Where all tables lie in the third vector the row's sizes are the library's. -/
theorem sizeU3_eq (tl : HTailF2) (h : allU3B tl.funs = true) :
    sizeU3 tl tl.funs = OnBytes.Tie.Pv.Tail.sizeOf tl := by
  unfold sizeU3
  rw [u3Tabs_all h]
  rfl

/-- And the row's weights are the library's. -/
theorem phiU3_eq [Field K] (ρ : Reading K) (tl : HTailF2) (h : allU3B tl.funs = true) :
    phiU3 ρ.val tl.funs = phiAt ρ tl := by
  funext n j
  unfold phiU3 phiAt
  rw [u3Tabs_all h, List.getD_eq_getElem?_getD, Array.getElem?_toList,
    ← Array.getD_eq_getD_getElem?]

/-- **Spent at the library's letters of the smallness test.** -/
theorem spent_thetaAt {J : Type} [Field K] [Fintype J] (ρ : Reading K) (Y : Lay J) (L : Letters K)
    (H : ClaimReadSameIndex L) {l : L.Link} (hl : l ∈ L.links) {s : L.State}
    (hs : L.AtClose l s) (hval : L.val = ρ.val) (hf : L.funs l s = (L.tl l s).funs)
    (h2 : allU3B (L.tl l s).funs = true) (iU3 K3 : ℕ) (X : Type) (Ex : ExtSpec) (W₀ : Type)
    (ride : X × Ex.Str → (OnBytes.Tie.Pv.Tail.JE Y (L.tl l s) → K) →
      Dig K (OnBytes.Tie.Pv.Tail.sizeOf (L.tl l s)).size × W₀ → Prop) {x : X}
    {msg : OnBytes.Tie.Pv.Tail.JE Y (L.tl l s) → K}
    (h : relIn (thetaAt ρ Y (L.tl l s) iU3 K3 X Ex W₀ ride).letters x msg) :
    Spent L l s (thetaAt ρ Y (L.tl l s) iU3 K3 X Ex W₀ ride) msg := by
  have ht : L.size l s = OnBytes.Tie.Pv.Tail.sizeOf (L.tl l s) := by
    show sizeU3 (L.tl l s) (L.funs l s) = _
    rw [hf]
    exact sizeU3_eq _ h2
  have hphi : (thetaAt ρ Y (L.tl l s) iU3 K3 X Ex W₀ ride).phi x = L.phi l s := by
    show phiAt ρ (L.tl l s) = phiU3 L.val (L.funs l s)
    rw [hval, hf]
    exact (phiU3_eq ρ _ h2).symm
  exact spent_at L H hl hs ht _ hphi h

/-! ## The premise on virtual rows -/

/-- In the world W the entries of the virtual rows of array iU3 are the vector u, laid in rows of
cols entries. -/
def RowsAre (W : World K) (iU3 cols : ℕ) (u : ℕ → K) : Prop :=
  ∀ r i, i < cols → W.entry iU3 r i = u (r * cols + i)

/-- Under that premise a form's part in U3, at u, is the value in W of its entries of the array. -/
theorem u3Value_world [CommRing K] (ρ : Reading K) {W : World K} {iU3 cols : ℕ} {u : ℕ → K}
    (hW : RowsAre W iU3 cols u) (f : Aff)
    (hin : ∀ x ∈ f.ents.toList, x.tree = iU3 → x.idx < cols) :
    u3Value ρ.val iU3 cols f u =
      ((f.ents.toList.filter fun x => x.tree == iU3).map (Ent.value ρ W)).sum := by
  unfold u3Value entsU3
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
  obtain ⟨hm, ht⟩ := List.mem_filter.1 hx
  have ht' : x.tree = iU3 := beq_iff_eq.1 ht
  show ρ.val x.coef * u (x.row * cols + x.idx) = ρ.val x.coef * W.entry x.tree x.row x.idx
  rw [ht', hW _ _ (hin x hm ht')]

/-- The library's vector of reads has cell (iU3, r, i) of the lay at the place r * K3 + i. -/
theorem rows_u3At {J : Type} [Field K] [Fintype J] (Y : Lay J) (tl : HTailF2) (iU3 K3 : ℕ)
    (m : OnBytes.Tie.Pv.Tail.JE Y tl → K) (r i : ℕ) (hi : i < K3) :
    OnBytes.Tie.Pv.Tail.u3At Y tl iU3 K3 m (r * K3 + i) =
      Y.cellAt (OnBytes.Tie.Pv.Tail.glue Y tl m fun _ => 0) iU3 r i := by
  have h1 : (r * K3 + i) / K3 = r := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi, Nat.add_zero]
  have h2 : (r * K3 + i) % K3 = i := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  unfold OnBytes.Tie.Pv.Tail.u3At
  rw [h1, h2]

end VerifiableInference.Reads

#print axioms VerifiableInference.Reads.spent_at
#print axioms VerifiableInference.Reads.u3Tabs_all
#print axioms VerifiableInference.Reads.sizeU3_eq
#print axioms VerifiableInference.Reads.phiU3_eq
#print axioms VerifiableInference.Reads.spent_thetaAt
#print axioms VerifiableInference.Reads.u3Value_world
#print axioms VerifiableInference.Reads.rows_u3At
