-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/DeclRow.lean: the row claim_read_same_index (Reads/Stated.lean) in two halves,
over the kinds' declarations of their reads (Reads/Decl.lean).

Between the smallness test's tables and the relation's clauses stands what a kind declares: for each
read a matrix, a make, a run's length, a number of entries, a first entry, weights.
  THE JOIN (Joined): at every entry of a declared read the smallness test's table has the cells that
    the declaration's make counts off, and the declared weights. It speaks of the declaration, the
    tables and the sizes of the matrices: of no form and no clause.
  THE ADDRESS (Addressed): what a use means is an entry of a declared read: the form's place is the
    read's first entry plus an index below its number of entries; the relation's own address of each
    cell is the address that the make gives at THAT index; the weights are the declared ones. It
    speaks of the text, the relation, the declaration and the sizes of the matrices: of no table.
  Both read the rows and columns of a matrix in the smallness test's record (t.m, t.k), at the
  declared matrix's FIRST part.
THE ROW IN THIS FORM (it is to speak of the one written description at the release's plan). THIS IS
THE FORM IN WHICH THE ROW IS TO BE SHOWN: it asks more than ClaimReadSameIndex: Whole, and the
name.
  ClaimByDecls L decls: at every link and state with closed tables: every table of the third vector
    has as many weights as its run is long (lensB); every declared read is whole (Whole: its run is
    not empty, its number of entries is that of its parts' tables, its make fits) and joined; every
    use is addressed in a declared read whose name is the letter read's: the read that the clause
    means; the uses are tied to the text (Tied).
  THE NAME. Without it a use is addressed by its place alone: where the text takes one table for
    another on the same matrix, with the same run, a lazy letter for the weights follows the place,
    and nothing fails. With it the place must lie in the table that the clause means
    (decl_tooth_name, Reads/DeclTeeth.lean [not in this library]). Where two declarations bear one
    name, either answers:
    that names are distinct is not asked. Nor that tables are: two declarations with one matrix, one
    run, one first entry and weights of one reading, under two names, are both joined by one table.
    The name's clause is then idle between the two; they are one read, and no other sum follows.
  WHO OWES Whole. It stands under "for all states with closed tables" and reads a matrix's rows off
    the state's record. So, like the test on lengths, it must follow from the plan and from what is
    heard, or the letter AtClose must carry it: a test behind the closing does not pay it.
THE TEST ON LENGTHS (lensB, Reads/Stated.lean) is asked of the TABLES' arrays, which the record of
  a table holds. A declaration has a function and no array: with lensB and the join, its weights
  below the run's length are entries that stand in a table's array. That a kind's OWN arrays are as
  long as their runs, and that a heard point has all its coordinates, is that kind's to state.
THE EQUATION, in two forms (statements on tables). BOTH SPEAK OF A WHOLE LINK: no table more, none
less, in this order. Where the tables of several kinds are laid in one link, in turns, no kind can
state either of its own declarations alone: ds is then the link's whole list, and it wants an owner.
What a kind can show alone is PartsLaid; with two premises more it gives the join (joined_of_parts,
Reads/Join.lean).
  TablesAre t phi val ds: the list of tables IS the list to which the declarations ds unfold, in
    order, and table for table the weights below the run's length are the declared ones.
  FunsAre t funs ds: the same on the smallness test's own list, with two things more: each table
    lies in the third vector, so that no table of the list lies elsewhere; each array is as long as
    its run. tables_of_funs: it gives TablesAre at the sizes and weights of the row, and lensB.
TOOLS: ReadDecl.meant; same_of_join_address: the two halves give SameIndex; claim_of_decls: the row
  in this form gives ClaimReadSameIndex; joined_weights, addressed_weights: of a declaration's
  weights only those below the run's length are read; at_of_map_eq, tree_of_tablesOf,
  u3Tabs_of_funsAre: steps of tables_of_funs.
A further letter: decls, the kinds' declarations at a link and a state.

Limits. The join at an entry that no form names is asked too: more than is spent. A declaration
that is made from the smallness test's list has a join that is true by its make: the join is worth
what stands between the two texts. The parts of a declared matrix are read at the sizes of its first
part: where the parts differ, the join may fail. It need not: on paper, at two parts of which the
last is wider, it holds, and count is then less than the tables' length. As in Reads/Stated.lean
for the rest.
Uses of `verify-on-bytes`'s records (OnBytes/Model/): HFun, in laidOf, FunsAre; HTailF2, in
tables_of_funs; as in Reads/Stated.lean for the rest.

-/
import Johnson.Desc.Reads.Stated
import Johnson.Desc.Reads.Decl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads

open Cb.Pv.Tail
open OnBytes (E zeroE)
open OnBytes.Model (HTailF2 HFun)

variable {K : Type}

/-- What entry i of a declared read means, at its place. The parts' sizes: those of the first. -/
def ReadDecl.meant (val : E → K) (t : TSize) (d : ReadDecl E) (i : ℕ) : Meant K :=
  ⟨d.start + i, d.len, d.cells (t.m d.mat) (t.k d.mat) i, fun j => val (d.w j)⟩

/-- **The join.** At every entry of the declared read the table has what the declaration means. -/
def Joined (t : TSize) (phi : ℕ → ℕ → K) (val : E → K) (d : ReadDecl E) : Prop :=
  ∀ i, i < d.count → SameIndex t phi (d.meant val t i)

/-- **The address.** e is what some entry of the declared read means: place, length, each cell's
address, each weight. -/
def Addressed (t : TSize) (val : E → K) (d : ReadDecl E) (e : Meant K) : Prop :=
  ∃ i, i < d.count ∧ e.pos = d.start + i ∧ e.len = d.len ∧
    ∀ j, j < d.len → e.cell j = d.cells (t.m d.mat) (t.k d.mat) i j ∧ e.w j = val (d.w j)

/-- The two halves give SameIndex. -/
theorem same_of_join_address {t : TSize} {phi : ℕ → ℕ → K} {val : E → K} {d : ReadDecl E}
    {e : Meant K} (hJ : Joined t phi val d) (hA : Addressed t val d e) : SameIndex t phi e := by
  obtain ⟨i, hi, a1, a2, a3⟩ := hA
  obtain ⟨n, T, c, sg, h1, h2, h3, h4, h5, h6, h7⟩ := hJ i hi
  have h6' : d.len = T.len := h6
  refine ⟨n, T, c, sg, h1, h2, h3, h4, a1.trans h5, a2.trans h6, fun j hj => ?_⟩
  obtain ⟨b1, b2⟩ := a3 j (by rw [h6']; exact hj)
  obtain ⟨c1, c2⟩ := h7 j hj
  exact ⟨b1.trans c1, c2.trans b2.symm⟩

/-- Of the weights only those below the run's length are read: by the join. -/
theorem joined_weights {t : TSize} {phi : ℕ → ℕ → K} {val : E → K} {d : ReadDecl E} (w' : ℕ → E)
    (h : ∀ j, j < d.len → w' j = d.w j) (hJ : Joined t phi val d) :
    Joined t phi val { d with w := w' } := by
  intro i hi
  obtain ⟨n, T, c, sg, h1, h2, h3, h4, h5, h6, h7⟩ := hJ i hi
  have h6' : d.len = T.len := h6
  refine ⟨n, T, c, sg, h1, h2, h3, h4, h5, h6, fun j hj => ⟨(h7 j hj).1, ?_⟩⟩
  show phi n j = val (w' j)
  rw [h j (by rw [h6']; exact hj)]
  exact (h7 j hj).2

/-- The same: by the address. -/
theorem addressed_weights {t : TSize} {val : E → K} {d : ReadDecl E} {e : Meant K} (w' : ℕ → E)
    (h : ∀ j, j < d.len → w' j = d.w j) (hA : Addressed t val d e) :
    Addressed t val { d with w := w' } e := by
  obtain ⟨i, hi, a1, a2, a3⟩ := hA
  refine ⟨i, hi, a1, a2, fun j hj => ⟨(a3 j hj).1, ?_⟩⟩
  show e.w j = val (w' j)
  rw [h j hj]
  exact (a3 j hj).2

/-! ## The equation -/

/-- The tables to which a list of declarations unfolds, in order, each with its weights. -/
def tablesOf (t : TSize) (ds : List (ReadDecl E)) : List (Laid × (ℕ → E)) :=
  ds.flatMap fun d => (d.tabs (t.m d.mat) (t.k d.mat)).map fun x => (x, d.w)

/-- The three numbers that the typed smallness test keeps of a table. -/
def Laid.tab (x : Laid) : Tab := ⟨x.mat, x.len, x.start⟩

/-- The four numbers of a table of the smallness test's own list. -/
def laidOf (Fn : HFun) : Laid := ⟨Fn.tree, Fn.mat, Fn.len, Fn.start⟩

/-- **The equation.** The list of tables is the list to which the declarations unfold: no table
more, none less, in this order; and the weights below the run's length are the declared ones. The
vector's number is not read: t.tabs has none. -/
def TablesAre (t : TSize) (phi : ℕ → ℕ → K) (val : E → K) (ds : List (ReadDecl E)) : Prop :=
  t.tabs = (tablesOf t ds).map (fun x => x.1.tab) ∧
    ∀ n x, (tablesOf t ds)[n]? = some x → ∀ j, j < x.1.len → phi n j = val (x.2 j)

/-- **The equation on the smallness test's own list.** Table for table, in order, no table more and
none less: the four numbers, the vector's among them, are those to which the declarations unfold;
the array of weights is as long as the run; its entries are the declared weights. -/
def FunsAre (t : TSize) (funs : Array HFun) (ds : List (ReadDecl E)) : Prop :=
  funs.toList.map laidOf = (tablesOf t ds).map (fun x => x.1) ∧
    ∀ (n : ℕ) (Fn : HFun) (x : Laid × (ℕ → E)),
      funs.toList[n]? = some Fn → (tablesOf t ds)[n]? = some x →
      Fn.phi.size = Fn.len ∧ ∀ j, j < Fn.len → Fn.phi.getD j zeroE = x.2 j

/-- Two lists with one image: at a number at which the one has an item, the other has one, with the
same image. -/
theorem at_of_map_eq {α β γ : Type} {f : α → γ} {g : β → γ} {l : List α} {l' : List β}
    (h : l.map f = l'.map g) {n : ℕ} {a : α} (ha : l[n]? = some a) :
    ∃ b, l'[n]? = some b ∧ g b = f a := by
  have h1 : (l'.map g)[n]? = some (f a) := by
    rw [← h, List.getElem?_map, ha, Option.map_some]
  rw [List.getElem?_map] at h1
  cases hb : l'[n]? with
  | none =>
    rw [hb, Option.map_none] at h1
    cases h1
  | some b =>
    rw [hb, Option.map_some] at h1
    exact ⟨b, rfl, Option.some.inj h1⟩

/-- Every table to which a declaration unfolds lies in the third vector. -/
theorem tree_of_tablesOf {t : TSize} {ds : List (ReadDecl E)} {x : Laid × (ℕ → E)}
    (h : x ∈ tablesOf t ds) : x.1.tree = vectorOfReads := by
  unfold tablesOf at h
  obtain ⟨d, -, h1⟩ := List.mem_flatMap.1 h
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h1
  unfold ReadDecl.tabs at hy
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 hy
  rfl

/-- Under the equation the list has no table outside the third vector. -/
theorem u3Tabs_of_funsAre {t : TSize} {funs : Array HFun} {ds : List (ReadDecl E)}
    (h : FunsAre t funs ds) : u3Tabs funs = funs.toList := by
  refine List.filter_eq_self.2 fun Fn hFn => ?_
  obtain ⟨n, hn⟩ := List.getElem?_of_mem hFn
  obtain ⟨x, hx, hl⟩ := at_of_map_eq h.1 hn
  have h2 : x.1.tree = vectorOfReads := tree_of_tablesOf (List.mem_of_getElem? hx)
  have hl' : x.1 = laidOf Fn := hl
  rw [hl'] at h2
  have h3 : Fn.tree = 2 := h2
  exact beq_iff_eq.2 h3

/-- **The equation on the list gives the equation at the row's sizes and weights, and the test on
lengths.** -/
theorem tables_of_funs {tl : HTailF2} {funs : Array HFun} {ds : List (ReadDecl E)} (val : E → K)
    (h : FunsAre (sizeU3 tl funs) funs ds) :
    TablesAre (sizeU3 tl funs) (phiU3 val funs) val ds ∧ lensB funs = true := by
  have hu := u3Tabs_of_funsAre h
  refine ⟨⟨?_, fun n x hx j hj => ?_⟩, ?_⟩
  · have h1 := congrArg (List.map Laid.tab) h.1
    rw [List.map_map, List.map_map] at h1
    show (u3Tabs funs).map (fun Fn => (⟨Fn.mat, Fn.len, Fn.start⟩ : Tab)) = _
    rw [hu]
    exact h1
  · obtain ⟨Fn, hFn, hl⟩ := at_of_map_eq h.1.symm hx
    have hl' : laidOf Fn = x.1 := hl
    have hlen : Fn.len = x.1.len := congrArg Laid.len hl'
    have hg : (u3Tabs funs).getD n default = Fn := by
      rw [hu]
      show (funs.toList[n]?).getD default = Fn
      rw [hFn, Option.getD_some]
    show val (((u3Tabs funs).getD n default).phi.getD j zeroE) = val (x.2 j)
    rw [hg, (h.2 n Fn x hFn hx).2 j (by rw [hlen]; exact hj)]
  · unfold lensB
    rw [hu]
    refine List.all_eq_true.2 fun Fn hFn => ?_
    obtain ⟨n, hn⟩ := List.getElem?_of_mem hFn
    obtain ⟨x, hx, -⟩ := at_of_map_eq h.1 hn
    exact beq_iff_eq.2 (h.2 n Fn x hn hx).1

/-! ## The row over declarations -/

/-- **claim_read_same_index over declarations.** At every link, at every state with the tables
closed: the test on lengths says yes; every declared read is whole and joined; every use is
addressed in a declared read of the name that its clause means; the uses are tied to the text. -/
def ClaimByDecls [CommRing K] (L : Letters K) (decls : L.Link → L.State → List (ReadDecl E)) :
    Prop :=
  ∀ l ∈ L.links, ∀ s, L.AtClose l s →
    lensB (L.funs l s) = true ∧
    (∀ d ∈ decls l s,
      d.Whole ((L.size l s).m d.mat) ((L.size l s).k d.mat) ∧
      Joined (L.size l s) (L.phi l s) L.val d) ∧
    (∀ u ∈ L.uses l, ∃ d ∈ decls l s, d.name = L.read l u ∧
      Addressed (L.size l s) L.val d (L.meant l s u)) ∧
    Tied L l s

/-- The row over declarations gives the row. Whole and the name are not spent. -/
theorem claim_of_decls [CommRing K] (L : Letters K) (decls : L.Link → L.State → List (ReadDecl E))
    (H : ClaimByDecls L decls) : ClaimReadSameIndex L := by
  intro l hl s hs
  obtain ⟨hB, hJ, hA, hT⟩ := H l hl s hs
  refine ⟨hB, fun u hu => ?_, hT⟩
  obtain ⟨d, hd, -, ha⟩ := hA u hu
  exact same_of_join_address (hJ d hd).2 ha

end VerifiableInference.Reads

#print axioms VerifiableInference.Reads.same_of_join_address
#print axioms VerifiableInference.Reads.joined_weights
#print axioms VerifiableInference.Reads.addressed_weights
#print axioms VerifiableInference.Reads.at_of_map_eq
#print axioms VerifiableInference.Reads.tree_of_tablesOf
#print axioms VerifiableInference.Reads.u3Tabs_of_funsAre
#print axioms VerifiableInference.Reads.tables_of_funs
#print axioms VerifiableInference.Reads.claim_of_decls
