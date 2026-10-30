-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/KeyRideTools.lean. THE TABLE OF JOINTS OF THE KEY FILE:
TOOLS FOR THE RIDERS OF A ROW THAT CLOSES PINS AND LAYS MESSAGES (the four proximity tests' rows:
1.15, 2.9, 2.10, 3.2): what a row reads, and how an item goes from the record behind and a witness
w to the record in front and w with messages laid. Statements with proofs; one structure.
OBJECT. Means.Says, RowHolds, formAt, valOf, srowAt, rowsHold, PIN, DotOmAt.
USER. Johnson/RunOne/Law/KeyRide15.lean and KeyRide23.lean.
LETTERS. All free: statements, rows, words, the reading G, the seats at_, the plan K, the reader R,
the ring's reading ρ, the laid messages ls, the riders' messages ks, the laid tables tbl.

WHAT A ROW READS:
  value_names       a row's value is a sum over the messages that it NAMES.
  says_reads        SO: of the statement a row reads the sizes of the two tables of the messages
                    that it names, and of the words those messages' alone: at two statements and
                    two families of words.
  offTables_reads   "it reads as 0 on every table that is not there" goes over under the same.
  rowHolds_reads    the same of the tables' own sentence RowHolds, at the reading.
  formAt_reads      a mask form reads the mask entries at its own slots alone (machine words; no
                    ring).
  formAt_read       a mask form, read: the sum over its slots of the coefficient times the entry;
                    formAt_read_congr: so it reads alike at entries that read alike wherever a
                    coefficient does not read 0.
THE TOOLS (general in ls, ks and tbl):
  LayTies           the four public ties: the seats of ks are theirs, what the rows read there is
                    what is pinned, none of ks is laid, the seats lie apart.
  valOf_layG        at a number that the plan sends into ks, or to no component, the rows read at
                    the laid witness what they read at w.
  ride_row          a fenced row: from one statement and w to another statement and the laid
                    witness.
  ride_srowAt       a message's sample rows, across two statements under K1.SmpStay;
                    ride_srowAt_same: at one statement.
  ride_rowsHold     a stretch of a group's open rows.
  ride_pinG         a pin.
  ride_dotOm        the claim (DotOm): no ring.
Limits. RULES: AS EMPTY AS THEIR PREMISES. Nothing on soundness; nothing on hiding.

-/
import Johnson.RunOne.KeyRows23At
import Johnson.Desc.Key.KeyRowAgree
import Johnson.Desc.Key.KeyLay
import Johnson.Desc.Key.KeyQuiet
import Johnson.Desc.K1.Law.SmpStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.KeyRideTools
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.RunOne.KeyRows23

/-! ## 1 What a row reads -/

section
variable {GE : Type} [CommRing GE] (ρ : Model.Reading GE)

/-- Beyond the statement's messages a table has no entry. -/
theorem tableSize_beyond (S : Statement) (o : Nat) (h : S.oracles.size ≤ o) (pt : Part) :
    Means.tableSize S o pt = 0 := by
  have e : S.oracles[o]? = none := Array.getElem?_eq_none h
  simp [Means.tableSize, Statement.has, e]

theorem onTable_beyond (S : Statement) (r : OnBytes.Row) (g : Means.Words GE) (o : Nat)
    (h : S.oracles.size ≤ o) (pt : Part) : Means.onTable ρ S r g o pt = 0 := by
  unfold Means.onTable
  rw [tableSize_beyond S o h pt, Finset.range_zero, Finset.sum_empty]

theorem onTable_off (S : Statement) (r : OnBytes.Row) (g : Means.Words GE) (o : Nat)
    (h : o ∉ r.oracles) (pt : Part) : Means.onTable ρ S r g o pt = 0 := by
  unfold Means.onTable
  exact Finset.sum_eq_zero fun i _ => by
    rw [Third.Law.coefficient_off_names ρ r o h pt i, zero_mul]

/-- **A row's value is a sum over the messages that it names.** -/
theorem value_names (S : Statement) (r : OnBytes.Row) (g : Means.Words GE) :
    Means.value ρ S r g =
      ∑ o ∈ r.oracles.toFinset, (Means.onTable ρ S r g o .main + Means.onTable ρ S r g o .mask) :=
          by
  unfold Means.value
  have h1 : ∑ o ∈ Finset.range S.oracles.size,
        (Means.onTable ρ S r g o .main + Means.onTable ρ S r g o .mask) =
      ∑ o ∈ Finset.range S.oracles.size ∪ r.oracles.toFinset,
        (Means.onTable ρ S r g o .main + Means.onTable ρ S r g o .mask) :=
    Finset.sum_subset Finset.subset_union_left fun o _ ho => by
      have hs : S.oracles.size ≤ o := by simpa using ho
      rw [onTable_beyond ρ S r g o hs .main, onTable_beyond ρ S r g o hs .mask, add_zero]
  have h2 : ∑ o ∈ r.oracles.toFinset,
        (Means.onTable ρ S r g o .main + Means.onTable ρ S r g o .mask) =
      ∑ o ∈ Finset.range S.oracles.size ∪ r.oracles.toFinset,
        (Means.onTable ρ S r g o .main + Means.onTable ρ S r g o .mask) :=
    Finset.sum_subset Finset.subset_union_right fun o _ ho => by
      have hn : o ∉ r.oracles := by simpa using ho
      rw [onTable_off ρ S r g o hn .main, onTable_off ρ S r g o hn .mask, add_zero]
  rw [h1, h2]

theorem onTable_reads (A B : Statement) (r : OnBytes.Row) (g g' : Means.Words GE) (o : Nat)
    (pt : Part)
    (hsz : Means.tableSize A o pt = Means.tableSize B o pt) (hw : g o = g' o) :
    Means.onTable ρ A r g o pt = Means.onTable ρ B r g' o pt := by
  unfold Means.onTable
  rw [hsz, hw]

/-- **What a row reads**: of the statement the sizes of the tables of the messages that it names; of
the words those messages' alone. -/
theorem says_reads (A B : Statement) (r : OnBytes.Row) (g g' : Means.Words GE)
    (hsz : ∀ o ∈ r.oracles, ∀ pt, Means.tableSize A o pt = Means.tableSize B o pt)
    (hw : ∀ o ∈ r.oracles, g o = g' o) : Means.Says ρ A r g ↔ Means.Says ρ B r g' := by
  have e : Means.value ρ A r g = Means.value ρ B r g' := by
    rw [value_names ρ A r g, value_names ρ B r g']
    refine Finset.sum_congr rfl fun o ho => ?_
    have ho' : o ∈ r.oracles := List.mem_toFinset.1 ho
    rw [onTable_reads ρ A B r g g' o .main (hsz o ho' .main) (hw o ho'),
      onTable_reads ρ A B r g g' o .mask (hsz o ho' .mask) (hw o ho')]
  unfold Means.Says
  rw [e]

/-- Tables of one size are both there or both not. -/
theorem has_of_size (A B : Statement) (o : Nat) (pt : Part)
    (h : Means.tableSize A o pt = Means.tableSize B o pt) (hB : B.has o pt = false) :
    A.has o pt = false := by
  cases hA : A.has o pt with
  | false => rfl
  | true =>
    simp [Means.tableSize, hA, hB] at h

theorem offTables_reads (A B : Statement) (r : OnBytes.Row)
    (hsz : ∀ o ∈ r.oracles, ∀ pt, Means.tableSize A o pt = Means.tableSize B o pt)
    (h : OffTables ρ A r) : OffTables ρ B r := by
  intro o pt i hB
  by_cases ho : o ∈ r.oracles
  · exact h o pt i (has_of_size A B o pt (hsz o ho pt) hB)
  · exact Third.Law.coefficient_off_names ρ r o ho pt i

/-- **The tables' own sentence reads no more.** -/
theorem rowHolds_reads (A B : Statement) (r : OnBytes.Row) (val val' : Nat → Part → Nat → E)
    (hoff : OffTables ρ A r)
    (hsz : ∀ o ∈ r.oracles, ∀ pt, Means.tableSize A o pt = Means.tableSize B o pt)
    (hv : ∀ o ∈ r.oracles, ∀ pt i, ρ.val (val o pt i) = ρ.val (val' o pt i)) :
    RowHolds (fun u v => ρ.val u = ρ.val v) A val r ↔
      RowHolds (fun u v => ρ.val u = ρ.val v) B val' r := by
  rw [rowHolds_iff_says ρ A val r hoff,
    rowHolds_iff_says ρ B val' r (offTables_reads ρ A B r hsz hoff)]
  exact says_reads ρ A B r _ _ hsz fun o ho => funext fun pt => funext fun i => hv o ho pt i

end

/-- **A mask form reads the mask entries at its own slots alone.** -/
theorem formAt_reads (mk mk' : Slot → E) (f : MaskForm) (h : ∀ q ∈ f, mk q.1 = mk' q.1) :
    formAt mk f = formAt mk' f := by
  unfold formAt
  exact List.foldl_ext _ _ _ fun s q hq => by rw [h q hq]

section
variable {GE : Type} [CommRing GE] (ρ : Model.Reading GE)

/-- **A mask form, read**: the sum over its slots of the coefficient times the entry. -/
theorem formAt_read (mk : Slot → E) (f : MaskForm) :
    ρ.val (formAt mk f) = (f.map fun q => ρ.val q.2 * ρ.val (mk q.1)).sum := by
  have key : ∀ (l : MaskForm) (s : E),
      ρ.val (l.foldl (fun s x => addE s (mulE x.2 (mk x.1))) s) =
        ρ.val s + (l.map fun q => ρ.val q.2 * ρ.val (mk q.1)).sum := by
    intro l
    induction l with
    | nil =>
      intro s
      simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
    | cons q l ih =>
      intro s
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, ρ.add, ρ.mul, add_assoc]
  unfold formAt
  rw [key f zeroE, ρ.zero, zero_add]

/-- Two families of mask entries that read alike wherever a slot's coefficient does not read 0: the
form reads alike. -/
theorem formAt_read_congr (mk mk' : Slot → E) (f : MaskForm)
    (h : ∀ q ∈ f, ρ.val (mk q.1) = ρ.val (mk' q.1) ∨ ρ.val q.2 = 0) :
    ρ.val (formAt mk f) = ρ.val (formAt mk' f) := by
  rw [formAt_read ρ mk f, formAt_read ρ mk' f]
  refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
  rcases h q hq with e | e
  · rw [e]
  · rw [e, zero_mul, zero_mul]

end

/-! ## 2 The tools: from a witness to the witness with messages laid -/

section
variable {A Cells M Smp Rec : Type} (G : Reading A Cells M Smp Rec) (at_ : Where) (K : KPlan)
  (R : KRead Cells M) (ls ks : List Nat) (tbl : Nat → M) (w : Wit Cells Unit M)

/-- **The four public ties** between the laid messages ls and the riders' messages ks. -/
structure LayTies : Prop where
  arr : ArrOk G at_ ks
  reads : ReadsPinned G at_ R ks
  off : ∀ k ∈ ks, k ∉ ls
  apart : SeatsApart at_ ls ks

variable {G at_ R ls ks}

theorem of_layG (T : LayTies G at_ R ls ks) (k : Nat) (hk : k ∈ ks) :
    R.of (layAt at_ ls tbl w) k = R.of w k :=
  reads_layAt_off G at_ R ls ks tbl w T.arr T.reads T.off T.apart k hk

/-- **At a number that the plan sends into ks, or to no component, nothing turns by the laying.** -/
theorem valOf_layG (T : LayTies G at_ R ls ks) (o : Nat) (hn : ∀ k, K.num o = some k → k ∈ ks) :
    valOf K R (layAt at_ ls tbl w) o = valOf K R w o := by
  funext pt i
  cases hk : K.num o with
  | none => simp only [valOf, hk]
  | some k =>
    simp only [valOf, hk]
    rw [of_layG tbl w T k (hn k hk)]

variable {GE : Type} [CommRing GE] (ρ : Model.Reading GE)

/-- **A fenced row rides**: St in front, St' behind. -/
theorem ride_row (T : LayTies G at_ R ls ks) (hsame : R.same = fun u v => ρ.val u = ρ.val v)
    (St St' : Statement) (Gr : OnBytes.Group) (r : OnBytes.Row) (hri : Means.RowIn St Gr r)
    (hsz : ∀ o ∈ Gr.members.toList, ∀ pt, Means.tableSize St o pt = Means.tableSize St' o pt)
    (hn : ∀ o ∈ Gr.members.toList, ∀ k, K.num o = some k → k ∈ ks)
    (hb : RowHolds R.same St' (valOf K R w) r) :
    RowHolds R.same St (valOf K R (layAt at_ ls tbl w)) r := by
  rw [hsame] at hb ⊢
  refine (rowHolds_reads ρ St St' r _ _ (offTables_of_rowIn ρ _ _ r hri)
    (fun o ho pt => hsz o (names_of_rowIn hri o ho) pt) (fun o ho pt i => ?_)).2 hb
  rw [valOf_layG K tbl w T o (hn o (names_of_rowIn hri o ho))]

/-- **A message's sample rows ride at one statement.** -/
theorem ride_srowAt_same (T : LayTies G at_ R ls ks)
    (hsame : R.same = fun u v => ρ.val u = ρ.val v) (St : Statement) (k : Nat)
    (hin : ∀ o, K.orc k = some o → SampleIn St o)
    (hnum : ∀ o, K.orc k = some o → ∀ j, K.num o = some j → j ∈ ks)
    (hu : srowAt R K St k w) : srowAt R K St k (layAt at_ ls tbl w) := by
  obtain ⟨o, x, ho, hx, h1, h2, h3⟩ := hu
  refine ⟨o, x, ho, hx, h1, h2, fun r hr' => ?_⟩
  refine ride_row K tbl w ρ T hsame St St { code := 0, members := #[o] } r (hin o ho x hx r hr')
    (fun _ _ _ => rfl) (fun o' h' j hj => ?_) (h3 r hr')
  have e : o' = o := by simpa using h'
  rw [e] at hj
  exact hnum o ho j hj

/-- **A message's sample rows ride across two statements.** St in front, St' behind. -/
theorem ride_srowAt (T : LayTies G at_ R ls ks) (hsame : R.same = fun u v => ρ.val u = ρ.val v)
    (St St' : Statement) (k : Nat) (hS : K1.SmpStay St St')
    (h0 : ∀ o, K.orc k = some o → ∃ x, St.oracles[o]? = some x ∧ x.sampled = true)
    (hin : ∀ o, K.orc k = some o → SampleIn St o)
    (hnum : ∀ o, K.orc k = some o → ∀ j, K.num o = some j → j ∈ ks)
    (hu : srowAt R K St' k w) : srowAt R K St k (layAt at_ ls tbl w) := by
  obtain ⟨o, x', ho, hx', _, h2, h3⟩ := hu
  obtain ⟨x, hxa, hsx⟩ := h0 o ho
  obtain ⟨x'', hx'', e1, _, e3⟩ := hS.2 o x hxa hsx
  have e : x'' = x' := Option.some.inj (hx''.symm.trans hx')
  subst e
  refine ⟨o, x, ho, hxa, hsx, e3 ▸ h2, fun r hr' => ?_⟩
  refine ride_row K tbl w ρ T hsame St St' { code := 0, members := #[o] } r
    (hin o ho x hxa r hr') (fun o' h' pt => ?_) (fun o' h' j hj => ?_) (h3 r (e3 ▸ hr'))
  · have e : o' = o := by simpa using h'
    rw [e]
    exact (Third.Law.tableSize_same St St' o o x x'' hxa hx'' e1 hS.1 pt).symm
  · have e : o' = o := by simpa using h'
    rw [e] at hj
    exact hnum o ho j hj

/-- **A stretch of a group's open rows rides.** St in front, St' behind. -/
theorem ride_rowsHold (T : LayTies G at_ R ls ks) (hsame : R.same = fun u v => ρ.val u = ρ.val v)
    (St St' : Statement) (g lo n : Nat) (hS : K1.SmpStay St St')
    (hgrp : ∀ G', St'.groups[g]? = some G' → ∃ G₀, St.groups[g]? = some G₀ ∧ G₀.rows = G'.rows)
    (hopen : OpenIn St g)
    (hmem : ∀ G₀, St.groups[g]? = some G₀ → ∀ o ∈ G₀.members.toList,
      (∃ x, St.oracles[o]? = some x ∧ x.sampled = true) ∧ ∀ k, K.num o = some k → k ∈ ks)
    (hu : rowsHold R.same St' (valOf K R w) g lo n) :
    rowsHold R.same St (valOf K R (layAt at_ ls tbl w)) g lo n := by
  obtain ⟨G', hG', hlen, hn0, hrows⟩ := hu
  obtain ⟨G₀, hG₀, er⟩ := hgrp G' hG'
  refine ⟨G₀, hG₀, by rw [er]; exact hlen, hn0, fun r hr' => ?_⟩
  have hr₀ : r ∈ G₀.rows.toList := List.mem_of_mem_drop (List.mem_of_mem_take hr')
  refine ride_row K tbl w ρ T hsame St St' G₀ r (hopen G₀ hG₀ r hr₀) (fun o ho pt => ?_)
    (fun o ho => (hmem G₀ hG₀ o ho).2) (hrows r (by rw [← er]; exact hr'))
  obtain ⟨⟨x, hx, hsx⟩, _⟩ := hmem G₀ hG₀ o ho
  obtain ⟨x', hx', e1, _, _⟩ := hS.2 o x hx hsx
  exact (Third.Law.tableSize_same St St' o o x x' hx hx' e1 hS.1 pt).symm

end

section
variable {XI P S Cells M Smp Rec : Type} (F : FileDescription XI) {G : Reading (P × S) Cells M Smp Rec}
  {at_ : Where} {R : KRead Cells M} {ls ks : List Nat} (tbl : Nat → M)

/-- **A pin rides.** -/
theorem ride_pinG (T : LayTies G at_ R ls ks) (k : Nat) (hk : k ∈ ks) (a b : P × S) (y y' : Strs)
    (w : Wit Cells Unit M) (e : G.smp b (at_ k).1 (at_ k).2 = G.smp a (at_ k).1 (at_ k).2)
    (hw : wordOf F y' (at_ k).1 (at_ k).2 = wordOf F y (at_ k).1 (at_ k).2)
    (hu : PIN F G (at_ k).1 (at_ k).2 b y' w) :
    PIN F G (at_ k).1 (at_ k).2 a y (layAt at_ ls tbl w) :=
  pin_of_msgOf F G _ _ a y w _ (msgOf_layAt_off G at_ ls ks tbl w T.arr T.off T.apart k hk)
    (rides_pin2_at F G _ _ a b y y' w e hw hu)

end

section
variable {A Cells M Smp Rec : Type} {G : Reading A Cells M Smp Rec} {at_ : Where} (K : KPlan)
  {R : KRead Cells M} {ls ks : List Nat} (tbl : Nat → M) (w : Wit Cells Unit M)

/-- **(DotOm) rides**: it reads the witness's messages 4 and 2 alone. -/
theorem ride_dotOm (T : LayTies G at_ R ls ks) (h4 : 4 ∈ ks) (h2 : 2 ∈ ks) (g : List Tensor)
    (psi : List E) (cd : Codes)
    (hu : DotOmAt R.same K.lin g psi (omOf K R cd w) (vOf' K R cd w)) :
    DotOmAt R.same K.lin g psi (omOf K R cd (layAt at_ ls tbl w))
      (vOf' K R cd (layAt at_ ls tbl w)) := by
  have eo : omOf K R cd (layAt at_ ls tbl w) = omOf K R cd w := funext fun y => by
    unfold omOf
    rw [of_layG tbl w T 4 h4]
  have ev : vOf' K R cd (layAt at_ ls tbl w) = vOf' K R cd w := funext fun c => by
    unfold vOf'
    rw [of_layG tbl w T 2 h2]
  rw [eo, ev]
  exact hu

end

end Johnson.RunOne.Law.KeyRideTools

#print axioms Johnson.RunOne.Law.KeyRideTools.value_names
#print axioms Johnson.RunOne.Law.KeyRideTools.says_reads
#print axioms Johnson.RunOne.Law.KeyRideTools.offTables_reads
#print axioms Johnson.RunOne.Law.KeyRideTools.rowHolds_reads
#print axioms Johnson.RunOne.Law.KeyRideTools.formAt_reads
#print axioms Johnson.RunOne.Law.KeyRideTools.formAt_read
#print axioms Johnson.RunOne.Law.KeyRideTools.formAt_read_congr
#print axioms Johnson.RunOne.Law.KeyRideTools.of_layG
#print axioms Johnson.RunOne.Law.KeyRideTools.valOf_layG
#print axioms Johnson.RunOne.Law.KeyRideTools.ride_row
#print axioms Johnson.RunOne.Law.KeyRideTools.ride_srowAt_same
#print axioms Johnson.RunOne.Law.KeyRideTools.ride_srowAt
#print axioms Johnson.RunOne.Law.KeyRideTools.ride_rowsHold
#print axioms Johnson.RunOne.Law.KeyRideTools.ride_pinG
#print axioms Johnson.RunOne.Law.KeyRideTools.ride_dotOm
