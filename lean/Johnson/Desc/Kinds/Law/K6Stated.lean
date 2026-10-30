-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6Stated.lean: THE STATED FUNCTION OF THE READS' ARRAY AT THE HEAD's LINK:
for
the table of joints' term that sets each array of a segment's second sending to its stated function
of the first sending's arrays: THE OUTPUT HEAD's READS IN TRUTH, AS A PLAIN FUNCTION of the record,
the data, the array's name, the row and the column. And: at data whose cells of the reads' array are
this function, the premise hA of Law/K6Silent.lean's k6Out_of_items holds. Definitions, statements
and
proofs.

  truthTab v c, truthOf v c name i   entry i of the read whose table bears the name, in truth: the
                   sum of the cells c under the read's weights, at the letters v. Twelve names.
  truthOf_head, truthOf_norm   it is readAt and readAtN. truthOf_congr: it reads cell and stream
                   alone.
  inStretch, tabAtCol tt pos   the first table of the list in whose stretch the column lies.
  statedReads W P cells   THE FUNCTION: at the record s and the data D: the tables as the reads'
                   quiet step will lay them (withTables); the letters read there; the table in whose
                   stretch the column lies; the read in truth of cells s D at (column - the table's
                   first entry). 0 where any of these is not there. Array's name and row are not
                   read: the caller sets it at the reads' array, row 0.
  TabsApart tt     A NAMED PREMISE: no column lies in two tables' stretches.
  tabAtCol_of       under it the table found by the column is the table found by the name.
  entriesAlike_of_stated   MAIN: see its docstring.
  k6Out_of_items_stated   Law/K6Silent.lean's k6Out_of_items with hA paid so.

WHAT IT IS NOT. **AT THE THREE TABLES OF THE LOOKUP's PLANES ("bH-bits-0", "bH-bits-1", "bH-pin")
statedReads ANSWERS 0: IT IS NOT THE STATED FUNCTION OF THE WHOLE ARRAY**: one stated function
serves every item that the table's row opens at that border, "planes" among them, whose forms name
just these entries: with 0 there that item is false of an honest witness: the row cannot be closed
with this function until truthTab holds the three planes' reads in truth. It fails shut.
cells, FROM THE DATA's FIELD ELEMENTS TO THE INTEGER CELLS, IS A LETTER: the tie of the components
to
it is the caller's, AND IS ASKED AT WHAT IS READ ALONE: the two tables of integers
cell and stream; not the stored weights, which no function of the record and the data can see.
TabsApart, TabBelow (each table ends below the vector's length) and
"the vector's length is at most the array's width" are premises: on the tables' arithmetic and the
plan: other files' to show. That
these
sums are what the smallness test's equations enforce (the run's weights are the kind's letters) is
said nowhere here. Nothing on soundness.
LETTERS. No letter stands under "there is" in the top.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K6Silent
import Johnson.Desc.Kinds.Law.ReadsAre

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff World)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (worldOwn)
open Norm (lt ls d lPd T S2)

/-! ## 1 The reads in truth, by the table's name -/

/-- The twelve tables' names, each with its read in truth at the letters v and the cells c. -/
def truthTab (v : Given × Behind × Places) (c : NCells) : List (String × (Nat → E)) :=
  letI := v.1
  letI := v.2.1
  [(nameOf .wideAtKeys, readAt c.toCells (Read.of .wideAtKeys)),
   (nameOf .wideAtCosts, readAt c.toCells (Read.of .wideAtCosts)),
   (nameOf .actAtLogits, readAt c.toCells (Read.of .actAtLogits)),
   (nameOf .rowAtCosts, readAt c.toCells (Read.of .rowAtCosts)),
   (nameOf .rowCount, readAt c.toCells (Read.of .rowCount)),
   (nameOfN .streamAtSquares, readAtN c (FinalNorm.Read.of .streamAtSquares)),
   (nameOfN .streamAtNormed, readAtN c (FinalNorm.Read.of .streamAtNormed)),
   (nameOfN .actAtKeys, readAtN c (FinalNorm.Read.of .actAtKeys)),
   (nameOfN .rowAtKeys, readAtN c (FinalNorm.Read.of .rowAtKeys)),
   (nameOfN .rowAtPV, readAtN c (FinalNorm.Read.of .rowAtPV)),
   (nameOfN .rowAtProducts, readAtN c (FinalNorm.Read.of .rowAtProducts)),
   (nameOfN .rowAtNormed, readAtN c (FinalNorm.Read.of .rowAtNormed))]

/-- Entry i of the read whose table bears the name, in truth; 0 at another name. -/
def truthOf (v : Given × Behind × Places) (c : NCells) (name : String) (i : Nat) : E :=
  match (truthTab v c).lookup name with
  | some f => f i
  | none => 0

theorem truthOf_head (v : Given × Behind × Places) (c : NCells) (r : Read) (i : Nat) :
    truthOf v c (nameOf r) i =
      (letI := v.1
       letI := v.2.1
       readAt c.toCells (Read.of r) i) := by
  cases r <;> simp [truthOf, truthTab, nameOf, nameOfN, List.lookup]

theorem truthOf_norm (v : Given × Behind × Places) (c : NCells) (r : FinalNorm.Read) (i : Nat) :
    truthOf v c (nameOfN r) i =
      (letI := v.1
       letI := v.2.1
       readAtN c (FinalNorm.Read.of r) i) := by
  cases r <;> simp [truthOf, truthTab, nameOf, nameOfN, List.lookup]

/-- The reads in truth read the cells' two tables of integers alone: not the stored weights. -/
theorem truthOf_congr (v : Given × Behind × Places) (c c' : NCells) (h1 : c.cell = c'.cell)
    (h2 : c.stream = c'.stream) : truthOf v c = truthOf v c' := by
  obtain ⟨⟨cell, Wh⟩, stream⟩ := c
  obtain ⟨⟨cell', Wh'⟩, stream'⟩ := c'
  simp only at h1 h2
  subst h1
  subst h2
  rfl

/-! ## 2 The table in whose stretch a column lies -/

/-- The column lies in the table's stretch. -/
def inStretch (pos : Nat) (x : String × Nat × Nat) : Bool :=
  Decidable.decide (x.2.1 ≤ pos) && Decidable.decide (pos < x.2.1 + x.2.2)

/-- The first table of the list in whose stretch the column lies. -/
def tabAtCol (tt : OnBytes.Model.Head.Tables) (pos : Nat) : Option (String × Nat × Nat) :=
  tt.tab.find? (inStretch pos)

/-- **No column lies in two tables' stretches.** -/
def TabsApart (tt : OnBytes.Model.Head.Tables) : Prop :=
  ∀ x ∈ tt.tab, ∀ y ∈ tt.tab, ∀ pos, inStretch pos x = true → inStretch pos y = true → x = y

/-- Under it the table found by the column is the table found by the name. -/
theorem tabAtCol_of {tt : OnBytes.Model.Head.Tables} (hA : TabsApart tt) {name : String}
    {x : String × Nat × Nat} (hx : tt.tab.find? (fun e => e.1 == name) = some x) (i : Nat)
    (hi : i < x.2.2) : tabAtCol tt (x.2.1 + i) = some x := by
  have hm : x ∈ tt.tab := List.mem_of_find?_eq_some hx
  have hin : inStretch (x.2.1 + i) x = true := by
    unfold inStretch
    simp
    omega
  unfold tabAtCol
  cases hf : tt.tab.find? (inStretch (x.2.1 + i)) with
  | none =>
    have := List.find?_eq_none.mp hf x hm
    rw [hin] at this
    exact absurd rfl this
  | some y =>
    rw [hA y (List.mem_of_find?_eq_some hf) x hm _ (List.find?_some hf) hin]

/-! ## 3 The function -/

/-- **THE STATED FUNCTION OF THE READS' ARRAY AT THE HEAD's LINK.** cells: from the data to the
integer cells: a letter. -/
noncomputable def statedReads (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH)
    (cells : S → Bound K → NCells) : S → Bound K → Nat × String → Nat → Nat → K :=
  fun s D _ _ pos =>
    match withTables P s with
    | none => 0
    | some e =>
      match e.here, lettersAt (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) e with
      | .head o, .ok v =>
        match o.t.bind fun tt => tabAtCol tt pos with
        | some x => rd (truthOf v (cells s D) x.1 (pos - x.2.1))
        | none => 0
      | _, _ => 0

/-- **AT DATA WHOSE CELLS OF THE READS' ARRAY ARE THE STATED FUNCTION: THE SEAT's ENTRIES ARE WORTH
THE READS IN TRUTH.** D': the stated data; cU: the reads' array's name in the link's list. -/
theorem entriesAlike_of_stated (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH)
    (cells : S → Bound K → NCells) (s e : S) (a : K9.Part) (D D' : Bound K) (d : Pinned)
    (v : Given × Behind × Places) (he : withTables P s = some e)
    (hv : lettersAt (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) e = .ok v)
    (cU : Nat × String) (hArr : a.L.arrayOf[readsOf W]? = some cU)
    (hcell : ∀ pos, D'.cell cU.1 cU.2 0 pos = statedReads W P cells s D cU 0 pos)
    (hd1 : d.1.cell = (cells s D).cell) (hd2 : d.1.stream = (cells s D).stream)
    (hApart : ∀ o tt, e.here = .head o → o.t = some tt → TabsApart tt)
    (hBelow : ∀ o tt F tr, e.here = .head o → o.t = some tt → e.fork? = some F →
      F.trees[readsOf W]? = some tr → ∀ x ∈ tt.tab, x.2.1 + x.2.2 ≤ tr.K)
    (W₂ : World K) :
    letI := v.1
    letI := v.2.1
    EntriesAlike (worldOwn a [] D') W₂ v.2.2.final (normReadsAtCells d.1) v.2.2.head
      (readsAt d.1.toCells) := by
  obtain ⟨g, bh, pl⟩ := v
  obtain ⟨H, x, k1, _, k3, k4⟩ := lettersAt_ok W.hS (readsOf W) (parOf W.hS (workOf W)) hv
  obtain ⟨o, F, tt, tr, ho, hF, ht, htr, _, a1, a2, a3⟩ := reads_are W.hS (readsOf W) e x k3
  obtain ⟨w1, w2⟩ := reads_within W.hS (readsOf W) e x k3 tt o ho ht
  have hAp := hApart o tt ho ht
  have hBe := hBelow o tt F tr ho ht hF htr
  have k1' : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) e = .ok g := k1
  have epl : pl = ⟨x.1, x.2⟩ := by
    have := congrArg (fun w : Given × Behind × Places => w.2.2) k4
    exact this
  -- one entry
  have one : ∀ (name : String) (t : String × Nat × Nat) (i : Nat),
      tt.tab.find? (fun e => e.1 == name) = some t → firstOf tt name = t.2.1 → i < t.2.2 →
      vW (worldOwn a [] D') (entryAt (readsOf W) tr.K (firstOf tt name + i)) =
        rd (truthOf (g, bh, pl) d.1 name i) := by
    intro name t i hfind hfirst hi
    have hm : t ∈ tt.tab := List.mem_of_find?_eq_some hfind
    have hlt : t.2.1 + i < tr.K := by
      have := hBe t hm
      omega
    have hname : t.1 = name := by
      have := List.find?_some hfind
      simpa using this
    rw [hfirst]
    unfold entryAt vW
    rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, Aff.value_ent]
    show (match a.L.arrayOf[readsOf W]? with
      | some b => D'.cell b.1 b.2 0 (t.2.1 + i)
      | none => 0) = _
    rw [hArr]
    show D'.cell cU.1 cU.2 0 (t.2.1 + i) = _
    rw [hcell]
    unfold statedReads
    simp only [he, ho, hv, ht, Option.bind_some, tabAtCol_of hAp hfind i hi]
    rw [hname, Nat.add_sub_cancel_left, truthOf_congr _ d.1 (cells s D) hd1 hd2]
  -- the sizes at the letters are the seat's
  obtain ⟨z, y, hgf⟩ := given_form k1'
  have hsz : g.sizes = (parOf W.hS (workOf W)).sizes := by rw [hgf]
  subst epl
  apply EntriesAlike.mk
  · intro r i hi
    have hi : i < @readLenN (parOf W.hS (workOf W)).sizes r := hsz ▸ hi
    obtain ⟨t, h1, h2, h3⟩ := w1 r
    show vW _ (x.1.entry r i) = _
    rw [a1 r i, one (nameOfN r) t i h1 h2 (Nat.lt_of_lt_of_le hi h3), truthOf_norm]
    unfold vW
    exact (Aff.value_ofConst _ _ _).symm
  · intro i hi
    have hi : i < @wideLenN (parOf W.hS (workOf W)).sizes := hsz ▸ hi
    obtain ⟨t, h1, h2, h3⟩ := w2 .wideAtKeys
    have hi' : i < t.2.2 := by
      refine Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hi ?_) h3
      exact Nat.div_le_div_right (Nat.le_add_right _ _)
    show vW _ (x.1.wide i) = _
    rw [a2 i, one "hf@Z" t i h1 h2 hi', show ("hf@Z" : String) = nameOf .wideAtKeys from rfl,
      truthOf_head]
    unfold vW
    exact (Aff.value_ofConst _ _ _).symm
  · intro r i hi
    have hi : i < @readLen (parOf W.hS (workOf W)).sizes r := hsz ▸ hi
    obtain ⟨t, h1, h2, h3⟩ := w2 r
    show vW _ (x.2.entry r i) = _
    rw [a3 r i, one (nameOf r) t i h1 h2 (Nat.lt_of_lt_of_le hi h3), truthOf_head]
    unfold vW
    exact (Aff.value_ofConst _ _ _).symm

/-- **k6Out_of_items AT STATED DATA WHOSE CELLS OF THE READS' ARRAY ARE statedReads**: the premise
hA is gone; in its place: the array's name in the link's list; the cells' equation (at the table's
term for the stated data: its own unfolding); the tie of the components to the letter cells; two
facts on the tables. -/
theorem k6Out_of_items_stated (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH)
    (l piece b : Nat) (states : Nat → List (K9.RunOf S))
    (KS : K6States W.hS (readsOf W) (parOf W.hS (workOf W)) l piece states b)
    (Rd : K9.Readers) (St : Sound.Stated) (own : List (Nat × Nat)) (s : S)
    (rdW : Nat × Nat → Sound.MsgQ) (d : Pinned) (a : K9.Part) (ha : K9.segAt? s = some a)
    (hRd : ∀ name, K6Name name → Rd.forms b name s = k6Silent P states b name s)
    (hok : (parOf W.hS (workOf W)).ok = true)
    (hT : K6HeardAt W.hS (readsOf W) (parOf W.hS (workOf W)) s)
    (hmask : ∀ j, j < a.F.mf.size → (St.at1 s (Sound.dataQ own a rdW)).mask j = rd (d.2 j))
    (cells : S → Bound K → NCells) (cU : Nat × String)
    (hArr : a.L.arrayOf[readsOf W]? = some cU)
    (hcell : ∀ pos, (St.at1 s (Sound.dataQ own a rdW)).cell cU.1 cU.2 0 pos =
      statedReads W P cells s (Sound.dataQ own a rdW) cU 0 pos)
    (hd1 : d.1.cell = (cells s (Sound.dataQ own a rdW)).cell)
    (hd2 : d.1.stream = (cells s (Sound.dataQ own a rdW)).stream)
    (hApart : ∀ e o tt, withTables P s = some e → e.here = .head o → o.t = some tt →
      TabsApart tt)
    (hBelow : ∀ e o tt F tr, withTables P s = some e → e.here = .head o → o.t = some tt →
      e.fork? = some F → F.trees[readsOf W]? = some tr → ∀ x ∈ tt.tab, x.2.1 + x.2.2 ≤ tr.K)
    (hWt : WeightAt W s d.1.toCells d.2)
    (hbare : ∀ gk, s.lookHeard? = some gk → gk.cEnd.ents = #[])
    (hn : Sound.formsTQ Rd St own b "norm" s rdW) (hp : Sound.formsTQ Rd St own b "policy" s rdW)
    (hl : Sound.formsTQ Rd St own b "logits" s rdW)
    (hj : Sound.formsTQ Rd St own b "join" s rdW) : K6Out W s d :=
  k6Out_of_items W P l piece b states KS Rd St own s rdW d a ha hRd hok hT hmask
    (fun e v he hv => entriesAlike_of_stated W P cells s e a (Sound.dataQ own a rdW) _ d v he hv cU
      hArr hcell hd1 hd2 (fun o tt => hApart e o tt he) (fun o tt F tr => hBelow e o tt F tr he) _)
    hWt hbare hn hp hl hj

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6Out_of_items_stated
#print axioms VerifiableInference.Desc.Kinds.Head.Law.truthOf_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.truthOf_norm
#print axioms VerifiableInference.Desc.Kinds.Head.Law.truthOf_congr
#print axioms VerifiableInference.Desc.Kinds.Head.Law.tabAtCol_of
#print axioms VerifiableInference.Desc.Kinds.Head.Law.entriesAlike_of_stated
