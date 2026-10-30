-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RowPlanesHost.lean: the output head's row's clause on "planes", at a record
in which the head's tables lie as the description's own text made them.

Law/RowPlanes.lean states the clause (rowPlanes: what the row opens on "planes" holds just where
what it closes holds) with the tables as premises: letters for the list of tables, the list of
matrices, the planes' matrix's number, the number of its rows, and nine premises on three tables.
Here all of these are the record's own, by Law/HeadPlanesHost.lean (TabsLie; tables_planes).

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  lookHeard_of_lie: at a record with TabsLie at which S.look? and S.lookHeard? agree, the lookup's
      run reads x.g1, the record of which the tables' weights were made.
  rowPlanes_host: K6OutP W lmbH sP Wd IFF K6InP lmbH sP Wd nu, at the public record's numbers,
      layout and plan (W.hS, W.HLy, W.H).
  blockAt_head: what K8.ReadsQuiet.blockAt lays at the head's link (piece 5 of link l).
  rowPlanes_behind: the same at the record right behind a yes of that block.

The text that the law speaks of: K8.ReadsQuiet.head at W.hS, W.HLy, W.H (its decision lays the
tables), and the lookup's run "planes" at the head's readers (K6OutP; Law/RowPlanes.lean's
planesRun_at). Who calls it: nobody yet.

Letters under "for all" that one premise alone reads: none. Wd (the world) is read by both sides and
by the law of the reads; it is tied to no ledger and no record here. nu is read by K6InP and h4;
cellM by h4 and the law of the reads.

Premises that nobody pays here. (1) THE LAW OF THE READS at Wd's entries, the record's own matrices
and list of tables, the reads' array and its width in the record's ledger; that array is asked to be
there, with a column (htr, hK0): the seat's reader refuses else. (2) hm, hk: the planes'
matrix has its rows in one block of 2 ^ lmbH and at least the planes' columns. (3) h4: its cells are
the lookup's. (4) hlk: S.look? and S.lookHeard? agree at the record: Law/RowPins.lean's look_behind
shows it behind the head's own rounds' block, and readsQuiet_keeps hands it over the block that
makes the tables; the one block between the two is not treated. (5) In rowPlanes_host: TabsLie at
sP.
Limits. The run "planes" is run at a later record than the one behind the block that makes the
tables: that TabsLie and hlk hold there still is not shown. That the three forms are worth 0 is the
batching's to give. No values are shown at which the premises hold together. No draw, no error term,
nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.RowPlanes
import Johnson.Desc.Kinds.Law.HeadPlanesHost
import Johnson.Desc.K8.ReadsQuietAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model OnBytes.K.Kc
open Cb Cb.Fo Cb.Fo.NumsEq TwV Fo Meaning.Planes
open Cb.Fo.Pin
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K8
open Planes

/-- Where the two homes of what the lookup returned agree, the lookup's run reads the record of
which the tables' weights were made. -/
theorem lookHeard_of_lie {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2}
    {s : S} {o : HeadOwn} {cov : Model.Head.Covered} {x : Model.Head.Heard}
    {t : Model.Head.Tables} (Z : TabsLie h L hp s o cov x t) (hlk : s.look? = s.lookHeard?) :
    s.lookHeard? = some x.g1 := by
  rw [← hlk]
  simp [S.look?, Z.here, Z.opened, Z.heard]

/-- **The row's clause on "planes", at a record in which the tables lie.** -/
theorem rowPlanes_host (W : OnBytes.Model.Verify.Public) {sP : S} {o : HeadOwn}
    {cov : Model.Head.Covered} {x : Model.Head.Heard} {t : Model.Head.Tables}
    (Z : TabsLie W.hS W.HLy W.H sP o cov x t) (hlk : sP.look? = sP.lookHeard?)
    {tr : HTree} (htr : o.F.trees[readsOf W]? = some tr) (hK0 : tr.K ≠ 0)
    {cellM : Nat → Nat → Nat → K}
    (hm : (W.H.tl.mats.getD (W.hS.NHf + 1 + 1) {}).m / 2 ^ W.hS.lmbH = 1)
    (hk : planeCols x.g1.shape W.hS.lmbH ≤ (W.H.tl.mats.getD (W.hS.NHf + 1 + 1) {}).k)
    (ν : _root_.Fo.Pl → K)
    (h4 : ∀ r < 2 ^ W.hS.lmbH, ∀ c < planeCols x.g1.shape W.hS.lmbH,
      cellM (W.hS.NHf + 1 + 1) r c = ν (.cell r c))
    (Wd : World K)
    (hA : ReadsAll Reading.gl o.tl.mats o.tl.funs Wd.entry (readsOf W) tr.K cellM) :
    K6OutP W W.hS.lmbH sP Wd ↔ K6InP W.hS.lmbH sP Wd ν := by
  obtain ⟨b0, b1, e0, e1, eP, y0, y1, h0, h1, hP, l0, l1, lP, T0, T1, TP⟩ := tables_planes Z.made
  have hF : sP.fork? = some o.F := by simp [S.fork?, Z.here, Z.opened]
  have eK : ((o.F.trees[readsOf W]?).map (·.K)).getD 1 = tr.K := by
    rw [htr]
    rfl
  rw [Z.mats, Z.funs, ← eK] at hA
  exact rowPlanes W x.g1 y0 y1 (lookHeard_of_lie Z hlk) Z.here hF Z.laid htr hK0 h0 h1 hP
    (len_fits hm hk l0) (len_fits hm hk l1) (len_fits hm hk lP) T0 T1 TP hm hk ν h4 Wd hA

/-- At the head's link K8.ReadsQuiet.blockAt lays the block that makes the tables at these letters.
kinds: for each link its kind (2: the head's) and its group of layers. -/
theorem blockAt_head (G : Array Layer.HPlan2) (hS : Model.Head.Shape) (HLy : Model.Head.HL)
    (H : Model.Head.HPlanH2) {kinds : List (Nat × Nat)} {l g : Nat}
    (hk : kinds[l]? = some (2, g)) :
    ReadsQuiet.blockAt G hS HLy H kinds l =
      some (ReadsQuiet.head ⟨⟨1, some l, 5, .K1⟩, hS, HLy, H⟩) := by
  simp [ReadsQuiet.blockAt, hk]

/-- **The same right behind the block that makes the tables**, as it is laid at the head's link. The
letters under "there is" are pinned by TabsLie's fields. -/
theorem rowPlanes_behind (W : OnBytes.Model.Verify.Public) (l : Nat) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (hd : (ReadsQuiet.head ⟨⟨1, some l, 5, .K1⟩, W.hS, W.HLy, W.H⟩).decide s rs gs = .ok s')
    (hlk : s.look? = s.lookHeard?) :
    ∃ o cov x t, TabsLie W.hS W.HLy W.H s' o cov x t ∧
      ∀ (tr : HTree), o.F.trees[readsOf W]? = some tr → tr.K ≠ 0 →
      ∀ (cellM : Nat → Nat → Nat → K),
        (W.H.tl.mats.getD (W.hS.NHf + 1 + 1) {}).m / 2 ^ W.hS.lmbH = 1 →
        planeCols x.g1.shape W.hS.lmbH ≤ (W.H.tl.mats.getD (W.hS.NHf + 1 + 1) {}).k →
        ∀ ν : _root_.Fo.Pl → K,
          (∀ r < 2 ^ W.hS.lmbH, ∀ c < planeCols x.g1.shape W.hS.lmbH,
            cellM (W.hS.NHf + 1 + 1) r c = ν (.cell r c)) →
          ∀ Wd : World K,
            ReadsAll Reading.gl o.tl.mats o.tl.funs Wd.entry (readsOf W) tr.K cellM →
            (K6OutP W W.hS.lmbH s' Wd ↔ K6InP W.hS.lmbH s' Wd ν) := by
  obtain ⟨o, cov, x, t, Z⟩ := tabsLie_behind hd
  obtain ⟨k1, k2, _⟩ := readsQuiet_keeps hd
  exact ⟨o, cov, x, t, Z, fun tr htr hK0 cellM hm hk ν h4 Wd hA =>
    rowPlanes_host W Z (by rw [k1, k2]; exact hlk) htr hK0 hm hk ν h4 Wd hA⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.lookHeard_of_lie
#print axioms VerifiableInference.Desc.Kinds.Head.Law.rowPlanes_host
#print axioms VerifiableInference.Desc.Kinds.Head.Law.blockAt_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.rowPlanes_behind
