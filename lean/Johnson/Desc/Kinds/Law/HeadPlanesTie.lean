-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadPlanesTie.lean: the output head's debt to its lookup on the planes, and
the head's row's clause on "planes", from the smallness test's tie in the place of the law of the
reads.

Law/HeadPlanesHost.lean and Law/RowPlanesHost.lean have the law of the reads (Fo.ReadsAll) as a
premise. The smallness test's sentence "the sent reads are the true ones" is said as one plain
formula over the carried record: TieOf tl A, and TieAt A s w at a record
(Johnson/Desc/First/K8/LawItems.lean); Johnson/Desc/First/K8/LawTie.lean shows it of what stands in
front of that test's block. Johnson/Meaning/PlanesTieK8Cells.lean spells the formula as the law of
the reads AT NAMED CELLS (readsAll_of_tie_cells; cellA tl A: the integers behind the symbols that A
shows at the record's symbol arrays), under two premises on the tables' numbers. Here these two are
paid at the head's own tables, and the two laws are stated from the tie. The form follows the
layers' instance of the planes' law from the tie, at the named cells.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  u3_of_lie, tl_of_lie: at a record in which the tables lie, the array of the reads that the record
      of the smallness test names is the plan's; S.tl? reads that record.
  k6_readsAll_of_tie: TieOf at the record's own record of the smallness test gives the law of the
      reads at the cells cellA, at every table of entries that agrees with A at row 0 of the array
      of the reads, below K3.
  k6_host_planes_of_tie: so the three clauses at the seat's own reader.
  k6_NM: a public record's plan of the head has NHf + 4 matrices.
  rowPlanes_of_tie: THE ROW'S CLAUSE ON "planes" FROM TieAt, at a public record.
  k6_planes_behind: THE THREE CLAUSES RIGHT BEHIND THE BLOCK THAT MAKES THE TABLES, from TieAt at
      that very record: the record in front of the smallness test's own block. No later record is
      named.

Every letter under "there is", and the clause that pins it. r: by callerReaders. k6_planes_behind:
o, cov, x, t by TabsLie's fields. No integers stand under "there is".
Letters under "for all" that one premise alone reads: none. A is read by the tie, by the premise on
the world and by h4. w is read through A w alone: it is the caller's witness.

Premises that nobody pays here. The tie itself. htr, hK: the array of the reads is there in the
record's ledger, and the plan's number of reads is at most its width (that the width is not 0
follows: Law/HeadTabsBelow.lean's tables_pos). On the world: its entries at row 0 of that array,
below that width, are A's cells. h4: the named cells of the planes' matrix are the lookup's cells.
And those that stay of the two laws: TabsLie, hlk, hsh, hW (or hm, hk, hNM).
Limits. Ties in one world: no draw, no error term: these lie with whoever shows the tie. At a column
to whose symbols no small integers pack, cellA is 0. No values are shown at which the premises hold
together. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.HeadTabsBelow
import Johnson.Desc.Kinds.Law.HeadPlanesNumbers
import Johnson.Meaning.PlanesTieK8Cells

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model OnBytes.K.Kc
open Cb Cb.Fo Cb.Fo.NumsEq TwV Fo Meaning.Planes
open Cb.Fo.Pin
open OnBytes.Tie.Pv.Tail Cb.Pv.Tail
open Meaning.Reads (cellA)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.K8 (TieOf TieAt)
open VerifiableInference.Desc.K8
open Planes

section
variable {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2} {s : S}
  {o : HeadOwn} {cov : Model.Head.Covered} {x : Model.Head.Heard} {t : Model.Head.Tables}

/-- The array of the reads that the record names is the plan's. -/
theorem u3_of_lie (Z : TabsLie h L hp s o cov x t) :
    Port.u3Of o.tl = (hp.tl.ix.U.getD 2 none).getD 0 := by
  unfold Port.u3Of
  rw [Z.ix]

/-- At a record in which the tables lie, S.tl? reads the head's link's record. -/
theorem tl_of_lie (Z : TabsLie h L hp s o cov x t) : s.tl? = some o.tl := by
  simp [S.tl?, Z.here, Z.opened]

/-- **The smallness test's tie, spelled as the law of the reads at the head's own tables and at the
named cells**, at every table of entries that agrees with A at row 0 of the array of the reads,
below K3. -/
theorem k6_readsAll_of_tie (Z : TabsLie h L hp s o cov x t) {A : Nat → Nat → Nat → Cb.Gl.E}
    (htie : TieOf o.tl A) {K3 : Nat} (hK : hp.nU.getD 2 0 ≤ K3) (hNM : h.NHf + 4 ≤ hp.tl.NM)
    (entry : Nat → Nat → Nat → Cb.Gl.E)
    (he : ∀ pos < K3, entry (Port.u3Of o.tl) 0 pos = A (Port.u3Of o.tl) 0 pos) :
    ReadsAll Reading.gl o.tl.mats o.tl.funs entry (Port.u3Of o.tl) K3 (cellA o.tl A) :=
  Meaning.Reads.readsAll_of_tie_cells htie K3 (k6_places_below Z.made o.tl Z.funs Z.mats hK)
    (fun f hf _ => k6_mats_below Z.made o.tl Z.funs (by rw [Z.nm]; exact hNM) f hf) entry he

/-- **The three clauses at the seat's own reader, from the smallness test's tie.** -/
theorem k6_host_planes_of_tie (Z : TabsLie h L hp s o cov x t) {A : Nat → Nat → Nat → Cb.Gl.E}
    (htie : TieOf o.tl A) {tr : HTree} (htr : o.F.trees[Port.u3Of o.tl]? = some tr)
    (hK : hp.nU.getD 2 0 ≤ tr.K) (hNM : h.NHf + 4 ≤ hp.tl.NM)
    (hm : (hp.tl.mats.getD (h.NHf + 1 + 1) {}).m / 2 ^ h.lmbH = 1)
    (hk : planeCols x.g1.shape h.lmbH ≤ (hp.tl.mats.getD (h.NHf + 1 + 1) {}).k)
    (ν : _root_.Fo.Pl → Cb.Gl.E) (W : World Cb.Gl.E)
    (hW : ∀ pos < tr.K, W.entry (Port.u3Of o.tl) 0 pos = A (Port.u3Of o.tl) 0 pos)
    (h4 : ∀ r < 2 ^ h.lmbH, ∀ c < planeCols x.g1.shape h.lmbH,
      cellA o.tl A (h.NHf + 1 + 1) r c = ν (.cell r c)) :
    ∃ r, callerReaders (planesAt (Port.u3Of o.tl)) s = some r ∧
      K3HostPlanes x.g1.shape h.lmbH (rdL Reading.gl x.g1.zb0) (rdL Reading.gl x.g1.zb1) ν
        (fun f => f.value Reading.gl W) (fun e col => (r.1 e col).getD {})
        (fun col => (r.2 col).getD {}) := by
  have hK0 : tr.K ≠ 0 := by
    have : 0 < hp.nU.getD 2 0 := tables_pos Z.made
    omega
  exact k6_host_planes_at Reading.gl Z (Port.u3Of o.tl) htr hK0 hm hk ν h4 W
    (k6_readsAll_of_tie Z htie hK hNM W.entry hW)

end

/-- A public record's plan of the head has NHf + 4 matrices. -/
theorem k6_NM {pol KL : ByteArray} {layout : Option ByteArray} {W : OnBytes.Model.Verify.Public}
    (hW : Verify.publicOf pol KL layout = .ok W) : W.H.tl.NM = W.hS.NHf + 4 := by
  obtain ⟨stream, _, hm, hn⟩ := Fo.Pub.public_mats hW
  rw [hn, hm]
  simp [Model.Head.matsH]

/-- **The row's clause on "planes", from the smallness test's tie at the carried record**, at a
public record. Wt: the type of the caller's witness; A: its table of cells. -/
theorem rowPlanes_of_tie {pol KL : ByteArray} {layout : Option ByteArray}
    {W : OnBytes.Model.Verify.Public} (hW : Verify.publicOf pol KL layout = .ok W) {sP : S}
    {o : HeadOwn} {cov : Model.Head.Covered} {x : Model.Head.Heard} {t : Model.Head.Tables}
    (Z : TabsLie W.hS W.HLy W.H sP o cov x t) (hlk : sP.look? = sP.lookHeard?)
    (hsh : x.g1.shape = W.HLy.fs) {Wt : Type} {A : Wt → Nat → Nat → Nat → Cb.Gl.E} {w : Wt}
    (htie : TieAt A sP w) {tr : HTree} (htr : o.F.trees[readsOf W]? = some tr)
    (hK : W.H.nU.getD 2 0 ≤ tr.K) (ν : _root_.Fo.Pl → Cb.Gl.E) (Wd : World Cb.Gl.E)
    (hWd : ∀ pos < tr.K, Wd.entry (readsOf W) 0 pos = A w (readsOf W) 0 pos)
    (h4 : ∀ r < 2 ^ W.hS.lmbH, ∀ c < planeCols x.g1.shape W.hS.lmbH,
      cellA o.tl (A w) (W.hS.NHf + 1 + 1) r c = ν (.cell r c)) :
    K6OutP W W.hS.lmbH sP Wd ↔ K6InP W.hS.lmbH sP Wd ν := by
  obtain ⟨tl, htl, ht⟩ := htie
  obtain rfl : o.tl = tl := Option.some.inj ((tl_of_lie Z).symm.trans htl)
  have eU : Port.u3Of o.tl = readsOf W := u3_of_lie Z
  have hA := k6_readsAll_of_tie Z ht hK (Nat.le_of_eq (k6_NM hW).symm) Wd.entry
    (by rw [eU]; exact hWd)
  rw [eU] at hA
  have hK0 : tr.K ≠ 0 := by
    have : 0 < W.H.nU.getD 2 0 := tables_pos Z.made
    omega
  exact rowPlanes_public hW Z hlk hsh htr hK0 ν h4 Wd hA

/-- **The three clauses right behind the block that makes the tables**, as it is laid at the head's
link of a public record: for every witness and table of cells with the smallness test's tie at that
very record, which is the record in front of the smallness test's own block. -/
theorem k6_planes_behind {pol KL : ByteArray} {layout : Option ByteArray}
    {W : OnBytes.Model.Verify.Public} (hW : Verify.publicOf pol KL layout = .ok W) (l : Nat)
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hd : (ReadsQuiet.head ⟨⟨1, some l, 5, .K1⟩, W.hS, W.HLy, W.H⟩).decide s rs gs = .ok s') :
    ∃ o cov x t, TabsLie W.hS W.HLy W.H s' o cov x t ∧
      (x.g1.shape = W.HLy.fs →
        ∀ tr : HTree, o.F.trees[readsOf W]? = some tr → W.H.nU.getD 2 0 ≤ tr.K →
        ∀ (Wt : Type) (A : Wt → Nat → Nat → Nat → Cb.Gl.E) (w : Wt), TieAt A s' w →
          ∀ (ν : _root_.Fo.Pl → Cb.Gl.E) (Wd : World Cb.Gl.E),
            (∀ pos < tr.K, Wd.entry (readsOf W) 0 pos = A w (readsOf W) 0 pos) →
            (∀ r < 2 ^ W.hS.lmbH, ∀ c < planeCols x.g1.shape W.hS.lmbH,
              cellA o.tl (A w) (W.hS.NHf + 1 + 1) r c = ν (.cell r c)) →
            ∃ r, callerReaders (planesAt (readsOf W)) s' = some r ∧
              K3HostPlanes x.g1.shape W.hS.lmbH (rdL Reading.gl x.g1.zb0)
                (rdL Reading.gl x.g1.zb1) ν (fun f => f.value Reading.gl Wd)
                (fun e col => (r.1 e col).getD {}) (fun col => (r.2 col).getD {})) := by
  obtain ⟨o, cov, x, t, Z⟩ := tabsLie_behind hd
  refine ⟨o, cov, x, t, Z, fun hsh tr htr hK Wt A w htie ν Wd hWd h4 => ?_⟩
  obtain ⟨tl, htl, ht⟩ := htie
  obtain rfl : o.tl = tl := Option.some.inj ((tl_of_lie Z).symm.trans htl)
  have eU : Port.u3Of o.tl = readsOf W := u3_of_lie Z
  have hA := k6_readsAll_of_tie Z ht hK (Nat.le_of_eq (k6_NM hW).symm) Wd.entry
    (by rw [eU]; exact hWd)
  rw [eU] at hA
  have hK0 : tr.K ≠ 0 := by
    have : 0 < W.H.nU.getD 2 0 := tables_pos Z.made
    omega
  exact k6_host_planes_public Reading.gl hW Z hsh (readsOf W) htr hK0 ν h4 Wd hA

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_planes_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_readsAll_of_tie
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_host_planes_of_tie
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6_NM
#print axioms VerifiableInference.Desc.Kinds.Head.Law.rowPlanes_of_tie
