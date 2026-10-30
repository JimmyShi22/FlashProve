-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadPlanes.lean: K6's INSTANCE OF THE PLANES' LAW: "planes", the part of the
output head's row of the table of joints that stands on neither side of Law/RowRides.lean |
Law/RowFront.lean: the head's readers of a column of the planes of its lookup's
counts are entries of the vector of reads: so the three clauses that a calling kind owes the lookup
on the planes (K3HostPlanes, Johnson/Meaning/PlanesLaw.lean) hold at the head's readers wherever the
entries of virtual rows meet the law of the reads: STATED AND PROVED.

planeEntry_at · head_readers · head_host_planes: THE INSTANCE: the three statements and two of the
three proofs follow, to the letter, a text of this project, not in this repository.
The law itself (host_planes_of_laid, Johnson/Meaning/PlanesKit.lean, over PlanesLaw.lean
| PlanesForms.lean) is not this file's.
planesAt_readers · head_host_planes_at: THE SAME AT THE SEAT's OWN READER planesAt iU3 AT A
RECORD (Johnson/Stored/HeadSeatAt.lean): what the lookup's run "planes" is handed (callerReaders
(planesAt iU3) s) IS these two functions, at the record's table of tables and the width of the
ledger's tree iU3.
These two also take as premises: the reads' array is there (F.trees[iU3]? = some tr)
with a column (tr.K is not 0): the seat's reader planesAt refuses without them.

WHAT IT DOES NOT SAY. THE LAW OF THE READS (ReadsAll) IS A PREMISE. LEFT TO THE HEAD's OWN TEXT, ALL
PREMISES:
· the three tables are in the program's table of its tables with at least the planes' columns
  (h0 h1 hP l0 l1 lP)
· at these first entries tables lie in the head's list funs, on blocks of 2^lm rows of the matrix
  iB, under the lookup's own weights (three LaidAt)
· Forest.phiB g lm 0 | 1 return
· that matrix has its rows in one block and at least the planes' columns (hm hk)
· its cells are the lookup's (h4)
· cols is the width at which the law of the reads is asked.
g (what the lookup has heard), funs, mats, cellM, ν are letters.
It is no law on a decision or a step: no run of the head's text but the reader.
Nothing on soundness; no chance.


-/
import Johnson.Meaning.PlanesKit
import Johnson.Stored.HeadSeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head
open Cb Cb.Fo Cb.Fo.NumsEq TwV
open OnBytes OnBytes.Model Fo Meaning.Planes

/-- Where the program's table of its tables has the read's table, and the column lies below that
table's length, the head's reader returns the entry of the vector of reads at the table's first
entry plus the column. -/
theorem planeEntry_at {tab : List (String × Nat × Nat)} {iU3 cols : Nat} {x : PlaneRead}
    {e : String × Nat × Nat}
    (hf : (tab.find? fun e => e.1 == (match x with
      | .bits0 => "bH-bits-0" | .bits1 => "bH-bits-1" | .pin => "bH-pin")) = some e)
    {i : Nat} (hi : i < e.2.2) :
    planeEntry tab iU3 cols x i = some (u3Form iU3 cols (e.2.1 + i)) := by
  unfold planeEntry
  cases x <;>
  · dsimp only at hf ⊢
    rw [hf]
    show (if i < e.2.2 then some (Aff.ent iU3 ((e.2.1 + i) / cols) ((e.2.1 + i) % cols))
      else none) = _
    rw [if_pos hi]
    rfl

/-- **The head's readers of the planes' columns are entries of the vector of reads**, at every
column
of the planes, if each of the three tables is in the program's table of its tables with at least the
planes' columns. bit e col and pin col: callerReaders' two functions, with {} where there is none.
-/
theorem head_readers {tab : List (String × Nat × Nat)} {iU3 cols : Nat} {sh : FoNums.Sh} {lm : Nat}
    {e0 e1 eP : String × Nat × Nat}
    (h0 : (tab.find? fun e => e.1 == "bH-bits-0") = some e0)
    (h1 : (tab.find? fun e => e.1 == "bH-bits-1") = some e1)
    (hP : (tab.find? fun e => e.1 == "bH-pin") = some eP)
    (l0 : sh.NC * 2 ^ (sh.kT + 5 - lm) ≤ e0.2.2) (l1 : sh.NC * 2 ^ (sh.kT + 5 - lm) ≤ e1.2.2)
    (lP : sh.NC * 2 ^ (sh.kT + 5 - lm) ≤ eP.2.2) :
    ReadersAre sh lm iU3 cols e0.2.1 e1.2.1 eP.2.1
      (fun e col => (planeEntry tab iU3 cols (if e == 0 then .bits0 else .bits1) col).getD {})
      (fun col => (planeEntry tab iU3 cols .pin col).getD {}) := by
  refine ⟨fun col hc => ?_, fun col hc => ?_, fun col hc => ?_⟩
  · show (planeEntry tab iU3 cols .bits0 col).getD {} = _
    rw [planeEntry_at (x := .bits0) h0 (lt_of_lt_of_le hc l0)]
    rfl
  · show (planeEntry tab iU3 cols .bits1 col).getD {} = _
    rw [planeEntry_at (x := .bits1) h1 (lt_of_lt_of_le hc l1)]
    rfl
  · show (planeEntry tab iU3 cols .pin col).getD {} = _
    rw [planeEntry_at (x := .pin) hP (lt_of_lt_of_le hc lP)]
    rfl

/-- **K6's instance of the planes' law.** g: what the head's lookup has heard. funs, mats: the
head's
list of tables and of matrices. iB: the number of the matrix bH. cols: the width of the array of the
reads, the very number at which the law of the reads is asked. -/
theorem head_host_planes {K : Type} [CommRing K] (ρ : Reading K) {mats : Array TMat}
    {funs : Array HFun} {cellM : Nat → Nat → Nat → K} (g : Forest.Heard) {lm iB iU3 cols : Nat}
    {b0 b1 : Array E} (y0 : Forest.phiB g lm 0 = some b0) (y1 : Forest.phiB g lm 1 = some b1)
    {tab : List (String × Nat × Nat)} {e0 e1 eP : String × Nat × Nat}
    (h0 : (tab.find? fun e => e.1 == "bH-bits-0") = some e0)
    (h1 : (tab.find? fun e => e.1 == "bH-bits-1") = some e1)
    (hP : (tab.find? fun e => e.1 == "bH-pin") = some eP)
    (l0 : planeCols g.shape lm ≤ e0.2.2) (l1 : planeCols g.shape lm ≤ e1.2.2)
    (lP : planeCols g.shape lm ≤ eP.2.2)
    (T0 : LaidAt funs e0.2.1 iB (2 ^ lm) b0) (T1 : LaidAt funs e1.2.1 iB (2 ^ lm) b1)
    (TP : LaidAt funs eP.2.1 iB (2 ^ lm) (Forest.phiP lm))
    (hm : (mats.getD iB {}).m / 2 ^ lm = 1) (hk : planeCols g.shape lm ≤ (mats.getD iB {}).k)
    (ν : _root_.Fo.Pl → K)
    (h4 : ∀ r < 2 ^ lm, ∀ c < planeCols g.shape lm, cellM iB r c = ν (.cell r c))
    (W : World K) (hA : ReadsAll ρ mats funs W.entry iU3 cols cellM) :
    K3HostPlanes g.shape lm (rdL ρ g.zb0) (rdL ρ g.zb1) ν (fun f => f.value ρ W)
      (fun e col => (planeEntry tab iU3 cols (if e == 0 then .bits0 else .bits1) col).getD {})
      (fun col => (planeEntry tab iU3 cols .pin col).getD {}) :=
  host_planes_of_laid ρ g y0 y1 T0 T1 TP hm hk ν h4 (head_readers h0 h1 hP l0 l1 lP) W hA


open VerifiableInference.Desc.First (S HeadOwn)

/-- **What the lookup's run "planes" is handed at a record**: the seat's reader planesAt iU3,
through callerReaders: planeEntry at the record's table of tables and the width of the ledger's tree
iU3. -/
theorem planesAt_readers (iU3 : Nat) {s : S} {o : HeadOwn} {F : Fork} {tt : Head.Tables}
    (ho : s.here = .head o) (hF : s.fork? = some F) (ht : o.t = some tt)
    {tr : HTree} (htr : F.trees[iU3]? = some tr) (hK : tr.K ≠ 0) :
    callerReaders (planesAt iU3) s = some
      (fun e col => planeEntry tt.tab iU3 (((F.trees[iU3]?).map (·.K)).getD 1)
          (if e == 0 then .bits0 else .bits1) col,
        planeEntry tt.tab iU3 (((F.trees[iU3]?).map (·.K)).getD 1) .pin) := by
  unfold callerReaders planesAt
  simp [ho, hF, ht, htr, hK]

/-- **K6's instance at the seat's own reader, at a record.** -/
theorem head_host_planes_at {K : Type} [CommRing K] (ρ : Reading K) {mats : Array TMat}
    {funs : Array HFun} {cellM : Nat → Nat → Nat → K} (g : Forest.Heard) {lm iB iU3 : Nat}
    {b0 b1 : Array E} (y0 : Forest.phiB g lm 0 = some b0) (y1 : Forest.phiB g lm 1 = some b1)
    {s : S} {o : HeadOwn} {F : Fork} {tt : Head.Tables}
    (ho : s.here = .head o) (hF : s.fork? = some F) (ht : o.t = some tt)
    {tr : HTree} (htr : F.trees[iU3]? = some tr) (hK : tr.K ≠ 0)
    {e0 e1 eP : String × Nat × Nat}
    (h0 : (tt.tab.find? fun e => e.1 == "bH-bits-0") = some e0)
    (h1 : (tt.tab.find? fun e => e.1 == "bH-bits-1") = some e1)
    (hP : (tt.tab.find? fun e => e.1 == "bH-pin") = some eP)
    (l0 : planeCols g.shape lm ≤ e0.2.2) (l1 : planeCols g.shape lm ≤ e1.2.2)
    (lP : planeCols g.shape lm ≤ eP.2.2)
    (T0 : LaidAt funs e0.2.1 iB (2 ^ lm) b0) (T1 : LaidAt funs e1.2.1 iB (2 ^ lm) b1)
    (TP : LaidAt funs eP.2.1 iB (2 ^ lm) (Forest.phiP lm))
    (hm : (mats.getD iB {}).m / 2 ^ lm = 1) (hk : planeCols g.shape lm ≤ (mats.getD iB {}).k)
    (ν : _root_.Fo.Pl → K)
    (h4 : ∀ r < 2 ^ lm, ∀ c < planeCols g.shape lm, cellM iB r c = ν (.cell r c))
    (W : World K)
    (hA : ReadsAll ρ mats funs W.entry iU3 (((F.trees[iU3]?).map (·.K)).getD 1) cellM) :
    ∃ r, callerReaders (planesAt iU3) s = some r ∧
      K3HostPlanes g.shape lm (rdL ρ g.zb0) (rdL ρ g.zb1) ν (fun f => f.value ρ W)
        (fun e col => (r.1 e col).getD {}) (fun col => (r.2 col).getD {}) :=
  ⟨_, planesAt_readers iU3 ho hF ht htr hK,
    head_host_planes ρ g y0 y1 h0 h1 hP l0 l1 lP T0 T1 TP hm hk ν h4 W hA⟩

end VerifiableInference.Desc.Kinds.Head

#print axioms VerifiableInference.Desc.Kinds.Head.head_host_planes
#print axioms VerifiableInference.Desc.Kinds.Head.planesAt_readers
#print axioms VerifiableInference.Desc.Kinds.Head.head_host_planes_at
