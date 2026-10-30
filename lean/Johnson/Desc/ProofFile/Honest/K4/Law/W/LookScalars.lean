-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/LookScalars.lean: THE TWO TOPS HAVE NO HYPOTHESIS. THE
SCALARS OF A LOOKUP's TABLE OF ROUNDS ADD UP TO THE LIBRARY's NUMBER `Face.slots`, at every face;
so, at a proof file's lookup of shape h, to the library's number `Forest.elems` h.

What is here. PUBLIC DATA ALONE: names of rounds and counts. The library has, for a lookup with the
public face f, a table of rounds as entries of the plan (`entriesV` f,
Johnson/Desc/First/Look/Via/Rounds.lean; its pieces: `MaskedSum.entries`,
Johnson/Desc/Part/MaskedSum4.lean; `levelEntries`, `runEntries`,
Johnson/Desc/First/ProdV/Level.lean) and a number, `Face.slots` f
(Johnson/Desc/First/Look/K3LookupGeneral.lean), which that definition's own docstring calls "the number of
hidden values that the rounds take": its words, not a statement of this file. Here: the scalars of
that table's entries, counted by the book's maker's own `scalarsIn` outside `frameNames`
(Honest/BookOf.lean), add up to that number. THAT `Face.slots` AT A PROOF FILE's LOOKUP IS
`Forest.elems` (OnBytes/Model/Forest.lean) IS A LAW OF THE AUTHORS OF THE KIND "LOOKUP":
`slots_elems` (Honest/K3/Law/SlotsElems.lean): it is called. Definitions, statements and proofs.

  `ownOfEntries`, `foldl_ownEntries`, `ownOfEntries_append`, `own_flat`, `own_work`: the own
      scalars of a list of entries; the work bits are not counted.
  `own_entry` (on hn), `own_draw`, `own_drawE`: one entry of a masked sumcheck; an entry that
      sends nothing.
  `degs`, `degs_cons`, `endsOf`, `own_vars`, `own_masked`: a masked sumcheck's entries, at every
      call.
  `degs_replicate`, `degs_bits`, `leaf_low` (on n ≤ d), `leaf_sum`, `degs_leaves`, `const_sum`:
      sums.
  `own_noVar`, `own_level`, `own_run`, `own_leaves`, `own_bitsCall`: the table's pieces.
  `entriesV_slots`: **THE STATEMENT.** `entriesV_elems`: so at a proof file's lookup of shape h.

Kin. Of the authors of the kind "lookup", where no other owner is named. `entries_stages`,
`slots_stages` (Honest/K3/RowLaw.lean), both under 2 ≤ f.planes: the stages' entries are `entriesV`
f; the stages' slots add up to `Face.slots` f: they count from the calls (`MaskedSum.ownSlots`), not
from the entries' bytes. What is here is the general law for the total alone, without the premise;
part by part nothing is shown here. SHORT SUMS ARE TYPED AGAIN HERE: Honest/K3/RowLaw.lean has three
of them: `leaf_low` is their `sum_leaf_low`, `leaf_sum` their `sum_leaf` up to the order of the sum,
`const_sum` their `sum_range_const`; importing that file would add two modules. Further: 1 + `degs`
vs is `MaskedSum.ownSlots` vs (the library's `ownSlots_eq`, Johnson/Desc/Part/MaskedSumSound.lean);
`degs_leaves` and `degs_bits` are kin of `own_leafVars` and `own_bits`
(Honest/K3/Law/PlanesReturn.lean). The library's `fromKeys_length`
(Johnson/Desc/First/Look/KeyLaw/Out.lean) has another list of the length `Face.slots`.

Not shown here. THAT ANY SUB-PROTOCOL OF A DESCRIPTION DECLARES THIS TABLE's ROUNDS: no description
is named in this file; and the library's kind declares the planner's entries, which agree with this
table's in all but the work bits (`entriesFit`, Via/Rounds.lean): hence `own_work`. That
`Forest.elems` is what the verifier's ledger moves by. Nothing on what is sent: declared numbers are
counted. IT STANDS OVER FILES OF OTHER WRITERS THAT ARE NO PART OF THE SEALED LIBRARY YET:
Honest/BookOf.lean and Honest/K3/Law/SlotsElems.lean, and what lies beneath them. Nothing on
soundness, on completeness or on any other property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.BookOf
import Johnson.Desc.ProofFile.Honest.K3.Law.SlotsElems
import Johnson.Desc.First.Look.Via.Rounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W
open OnBytes
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call)
open VerifiableInference.Desc.K3 (entriesV faceOf drawEntry noVar leafVars bitsCall)
open VerifiableInference.Desc.First.ProdV (runEntries levelEntries)

/-! ## 1 The own scalars of a list of entries -/

/-- The own scalars of a list of entries of the plan: each counted by the book's maker's own
`scalarsIn`, unless its name stands in `frameNames`. -/
def ownOfEntries (es : List Fmt.Entry) : Nat :=
  es.foldl (fun n e =>
    if frameNames.contains e.name then n else n + scalarsIn { entry := e }) 0

theorem foldl_ownEntries : ∀ (es : List Fmt.Entry) (a : Nat),
    es.foldl (fun n e => if frameNames.contains e.name then n
      else n + scalarsIn { entry := e }) a = a + ownOfEntries es
  | [], _ => rfl
  | e :: es, a => by
    show List.foldl (fun n e => if frameNames.contains e.name then n
        else n + scalarsIn { entry := e }) a (e :: es) =
      a + List.foldl (fun n e => if frameNames.contains e.name then n
        else n + scalarsIn { entry := e }) 0 (e :: es)
    rw [List.foldl_cons, List.foldl_cons,
      foldl_ownEntries es (if frameNames.contains e.name then a
        else a + scalarsIn { entry := e }),
      foldl_ownEntries es (if frameNames.contains e.name then 0
        else 0 + scalarsIn { entry := e })]
    by_cases hc : frameNames.contains e.name = true
    · rw [if_pos hc, if_pos hc]
      omega
    · rw [if_neg hc, if_neg hc]
      omega

theorem ownOfEntries_append (A C : List Fmt.Entry) :
    ownOfEntries (A ++ C) = ownOfEntries A + ownOfEntries C := by
  show (A ++ C).foldl (fun n e => if frameNames.contains e.name then n
    else n + scalarsIn { entry := e }) 0 = _
  rw [List.foldl_append, foldl_ownEntries C]
  rfl

theorem own_flat {α : Type} (F : α → List Fmt.Entry) : ∀ L : List α,
    ownOfEntries (L.flatMap F) = (L.map fun i => ownOfEntries (F i)).sum
  | [] => rfl
  | i :: L => by
    rw [List.flatMap_cons, ownOfEntries_append, own_flat F L, List.map_cons, List.sum_cons]

/-- The work bits are not counted. -/
theorem own_work : ∀ es : List Fmt.Entry,
    ownOfEntries (es.map fun e => { e with work := 0 }) = ownOfEntries es
  | [] => rfl
  | e :: es => by
    show ownOfEntries ([{ e with work := 0 }] ++ es.map fun e => { e with work := 0 }) =
      ownOfEntries ([e] ++ es)
    rw [ownOfEntries_append, ownOfEntries_append, own_work es]
    rfl

/-- CONDITIONAL: on hn. One entry of a masked sumcheck under a name that is a segment's own. -/
theorem own_entry {name : String} (hn : frameNames.contains name = false) (sent drawn nz : Nat)
    (es : List Fmt.Entry) :
    ownOfEntries (MaskedSum.entry name sent drawn nz :: es) = sent + ownOfEntries es := by
  show List.foldl (fun n e => if frameNames.contains e.name then n
    else n + scalarsIn { entry := e }) 0
      (MaskedSum.entry name sent drawn nz :: es) = _
  rw [List.foldl_cons, foldl_ownEntries]
  show (if frameNames.contains name then 0 else 0 + (24 * sent - 32 * 0 - 24 * 0) / 24) +
    ownOfEntries es = sent + ownOfEntries es
  rw [hn, if_neg (by decide)]
  omega

/-- An entry that sends nothing, whatever its name. -/
theorem own_draw (name : String) (n z : Nat) : ownOfEntries [MaskedSum.entry name 0 n z] = 0 := by
  show (if frameNames.contains name then 0 else 0 + (24 * 0 - 32 * 0 - 24 * 0) / 24) = 0
  split <;> rfl

theorem own_drawE (name : String) (n : Nat) : ownOfEntries [drawEntry name n] = 0 :=
  own_draw name n 0

/-! ## 2 A masked sumcheck's entries -/

/-- How many scalars the rounds on the variables declare. -/
def degs (vs : List Var) : Nat := (vs.map fun v => v.d - 1).sum

theorem degs_cons (v : Var) (vs : List Var) : degs (v :: vs) = v.d - 1 + degs vs := by
  unfold degs
  rw [List.map_cons, List.sum_cons]

/-- How many scalars the ends declare. -/
def endsOf : Option Ends → Nat
  | none => 0
  | some e => e.dY + e.n

theorem own_vars : ∀ vs : List Var,
    ownOfEntries (vs.map fun v => MaskedSum.entry "PSC round" (v.d - 1) 1 0) = degs vs
  | [] => rfl
  | v :: vs => by
    rw [List.map_cons, own_entry (name := "PSC round") (by decide), own_vars vs, degs_cons]

/-- **A masked sumcheck's entries, at every call.** -/
theorem own_masked (k : Call) :
    ownOfEntries (MaskedSum.entries k) = k.lead + 1 + degs k.vs + endsOf k.ends := by
  unfold MaskedSum.entries
  rw [ownOfEntries_append, ownOfEntries_append, own_vars,
    own_entry (name := "PSC epsilon") (by decide)]
  cases k.ends with
  | none =>
    show k.lead + 1 + 0 + degs k.vs + 0 = k.lead + 1 + degs k.vs + 0
    omega
  | some e =>
    show k.lead + 1 + 0 + degs k.vs +
      ownOfEntries [MaskedSum.entry "PSC Y" e.dY 1 1, MaskedSum.entry "PSC values" e.n 0 0] =
        k.lead + 1 + degs k.vs + (e.dY + e.n)
    rw [own_entry (name := "PSC Y") (by decide), own_entry (name := "PSC values") (by decide)]
    show k.lead + 1 + 0 + degs k.vs + (e.dY + (e.n + 0)) = _
    omega

/-! ## 3 Sums -/

theorem degs_replicate (z : E) : ∀ m : Nat, degs (List.replicate m (Var.point z 3)) = 2 * m
  | 0 => rfl
  | m + 1 => by
    rw [List.replicate_succ, degs_cons, degs_replicate z m]
    show 3 - 1 + 2 * m = 2 * (m + 1)
    omega

theorem degs_bits (z : E) : ∀ n : Nat,
    degs ((List.replicate n z).map fun x => Var.point x 3) = 2 * n
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.map_cons, degs_cons, degs_bits z n]
    show 3 - 1 + 2 * n = 2 * (n + 1)
    omega

/-- CONDITIONAL: on n ≤ d. -/
theorem leaf_low (d : Nat) : ∀ n : Nat, n ≤ d →
    ((List.range n).map fun j => (if j < d then 3 else 2) - 1).sum = 2 * n
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append, leaf_low d n (by omega), List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, if_pos (by omega)]
    omega

theorem leaf_sum (d : Nat) : ∀ k : Nat,
    ((List.range (d + k)).map fun j => (if j < d then 3 else 2) - 1).sum = 2 * d + k
  | 0 => leaf_low d d (Nat.le_refl _)
  | k + 1 => by
    show ((List.range (d + k + 1)).map fun j => (if j < d then 3 else 2) - 1).sum = _
    rw [List.range_succ, List.map_append, List.sum_append, leaf_sum d k, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, if_neg (by omega)]
    omega

theorem degs_leaves (f : VerifiableInference.Desc.K3.Face) :
    degs (leafVars f #[]) = 2 * f.d + f.mu := by
  show (((List.range (f.mu + f.d)).map fun j =>
    Var.point ((#[] : Array E).getD j zeroE) (if j < f.d then 3 else 2)).map
      fun v => v.d - 1).sum = _
  rw [List.map_map, Nat.add_comm f.mu f.d]
  exact leaf_sum f.d f.mu

theorem const_sum (c : Nat) : ∀ n : Nat, ((List.range n).map fun _ => c).sum = n * c
  | 0 => by
    show 0 = 0 * c
    omega
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, const_sum c n, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, Nat.succ_mul]
    omega

/-! ## 4 The table's pieces -/

theorem own_noVar (dY n : Nat) : ownOfEntries (MaskedSum.entries (noVar dY n)) = 1 + dY + n := by
  rw [own_masked]
  show 0 + 1 + 0 + (dY + n) = 1 + dY + n
  omega

theorem own_level (m : Nat) : ownOfEntries (levelEntries m) = 2 * m + 5 := by
  unfold levelEntries
  rw [ownOfEntries_append, own_masked, own_draw]
  show 0 + 1 + degs (List.replicate m (Var.point zeroE 3)) + 4 + 0 = 2 * m + 5
  rw [degs_replicate]
  omega

theorem own_run (m0 n : Nat) :
    ownOfEntries (runEntries m0 n) = ((List.range n).map fun i => 2 * (m0 + i) + 5).sum := by
  unfold runEntries
  rw [own_flat]
  simp only [own_level]

theorem own_leaves (f : VerifiableInference.Desc.K3.Face) :
    ownOfEntries (MaskedSum.entries { lead := 0, vs := leafVars f #[], ends := none }) =
      1 + f.mu + 2 * f.d := by
  rw [own_masked]
  show 0 + 1 + degs (leafVars f #[]) + 0 = 1 + f.mu + 2 * f.d
  rw [degs_leaves]
  omega

theorem own_bitsCall (n : Nat) :
    ownOfEntries (MaskedSum.entries (bitsCall (List.replicate n zeroE))) = 1 + 2 * n + 2 + 1 := by
  rw [own_masked]
  show 0 + 1 + degs ((List.replicate n zeroE).map fun x => Var.point x 3) + (2 + 1) = _
  rw [degs_bits, Nat.zero_add, Nat.add_assoc (1 + 2 * n) 2 1]

/-! ## 5 The statement -/

/-- **THE SCALARS OF A LOOKUP's TABLE OF ROUNDS ADD UP TO `Face.slots`.** No hypothesis. -/
theorem entriesV_slots (f : VerifiableInference.Desc.K3.Face) :
    ownOfEntries (entriesV f) = f.slots := by
  have hs : ownOfEntries (if f.shifted then [drawEntry "LKP shift" 1] else []) = 0 := by
    split
    · exact own_drawE _ _
    · rfl
  unfold entriesV VerifiableInference.Desc.K3.Face.slots
  simp only [ownOfEntries_append, hs, own_drawE, own_noVar, own_flat, own_run, own_leaves,
    own_bitsCall, const_sum, Nat.zero_add]
  omega

/-- **At a proof file's lookup of shape h: `Forest.elems` h.** No hypothesis. -/
theorem entriesV_elems (h : Model.Forest.Shape) :
    ownOfEntries (entriesV (faceOf h)) = Model.Forest.elems h :=
  (entriesV_slots (faceOf h)).trans (ProofFile.Honest.K3.Law.Spec.slots_elems h)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.foldl_ownEntries
#print axioms ProofFile.Honest.K4.W.ownOfEntries_append
#print axioms ProofFile.Honest.K4.W.own_flat
#print axioms ProofFile.Honest.K4.W.own_work
#print axioms ProofFile.Honest.K4.W.own_entry
#print axioms ProofFile.Honest.K4.W.own_draw
#print axioms ProofFile.Honest.K4.W.own_drawE
#print axioms ProofFile.Honest.K4.W.degs_cons
#print axioms ProofFile.Honest.K4.W.own_vars
#print axioms ProofFile.Honest.K4.W.own_masked
#print axioms ProofFile.Honest.K4.W.degs_replicate
#print axioms ProofFile.Honest.K4.W.degs_bits
#print axioms ProofFile.Honest.K4.W.leaf_low
#print axioms ProofFile.Honest.K4.W.leaf_sum
#print axioms ProofFile.Honest.K4.W.degs_leaves
#print axioms ProofFile.Honest.K4.W.const_sum
#print axioms ProofFile.Honest.K4.W.own_noVar
#print axioms ProofFile.Honest.K4.W.own_level
#print axioms ProofFile.Honest.K4.W.own_run
#print axioms ProofFile.Honest.K4.W.own_leaves
#print axioms ProofFile.Honest.K4.W.own_bitsCall
#print axioms ProofFile.Honest.K4.W.entriesV_slots
#print axioms ProofFile.Honest.K4.W.entriesV_elems
