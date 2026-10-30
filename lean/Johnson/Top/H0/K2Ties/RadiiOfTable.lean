-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/RadiiOfTable.lean: the code switch's law at the closed constant
(P5J.mgAtAll): THE NAMED TEST membersPlanB IS A THEOREM AT THE CONSTANT's OWN TERMS, AT ALL 25
SWITCHES, RADII AND ALL: the radii's clause (MembersShapeAt.lean's hB) FROM «THE MADE TABLE IS THE
WRITTEN ONE», WITH NO VALUE OF A RADIUS. WHY NO VALUE IS WANTED. The made table's row holds the
rows' own (shape, radius) entries, and a member of the table of joints bears the radius of the rows'
entry at its sending and place: so both radii are ONE TERM, once the indices are tied; and the
indices hang on the rows' labels and numbers of entries alone, which are the made sendings'.
  Wc               the written sendings' labels and numbers of sampled messages (off proofSends0)
  radTieB          THE TIE OF THE INDICES, a test on written values alone (psFull · N0Full ·
                   tableFullLit's kept numbers · Wc)
  radTie_written   it accepts at all 25 switches: by decide +kernel
  shifted · radTie_rejects  a negative test, by the kernel
  radii_of_rows    the radii's clause at rad := P5T.radOf R, for rows R with the written labels and
                   numbers of entries, at a row that holds R's own entries
  radii_of_table   the same at rad := At.rad Zp Z.lay
  membersPlan_const  membersPlanB Zp (At.rad Zp Z.lay) (At.N Zp cF) (m + 1) r = true at r :=
                   tableFullLit[m], m < 25
THE PREMISES: hl: the head is live · hZ: in scope · L: LaidAt · hy: the pin madePinnedAt ·
hT : tableOf Z.pol Z.lay Z.KL = .ok tableFullLit: WHAT THE NAMED TEST tableWrittenB
(K2Caller/TableWritten.lean) SAYS: no new name.
CALLED: RowsAddr.lean · MembersShapeAt.lean · tableOf_iff (Opts/TableFrom.lean) · sends_of_laid ·
first_is_fifth (Opts/SendsOfLaid.lean | SendsKeys.lean) · pub_files (CarryAtLaw.lean).
LIMITS. The full size alone. hT is not shown here: it hangs on the second reading of the three
public files. No soundness is claimed.
-/
import Johnson.Top.H0.K2Ties.RowsAddr
import Johnson.Top.H0.K2Ties.MembersShapeAt
import Johnson.Top.H0.Opts.SendsKeys
import Johnson.Top.H0.Opts.SendsOfLaid
import Johnson.Desc.ProofFile.Law.CarryAtLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (madePinnedAt)
open VerifiableInference.Desc.First.K2Caller (SwRow tableFullLit tableOf tableOf_iff membersPlanB
  keptEntries)
open Johnson.G (SendRow sendRowsOf linkRows linkList proofSends0)
open P1Opts (sampledOf sends_of_laid first_is_fifth)
open P5T (PSeat psFull N0Full mineAt firstRows radOf)
open P5J (LaidAt TS)

/-- The written sendings' labels and numbers of sampled messages. -/
def Wc : List (String × ℕ) := proofSends0.sends.map fun x => (x.label, (sampledOf x).length)

/-- **THE TIE OF THE INDICES, AS A TEST ON WRITTEN VALUES.** At the switch into group m + 1: each
seat of the plan with a sample, at (sending k, place j), that sits at the a-th kept tenant has the
address (k, j) at the a-th kept number in link m's list; that sits at the i-th new tenant has k the
first sending of link m + 1 and j = i. -/
def radTieB (ps : List PSeat) (m : ℕ) : Bool :=
  (tableFullLit[m]?).any fun r =>
    (List.range proofSends0.sends.length).all fun k => (mineAt ps k).zipIdx.all fun pj =>
      (((N0Full.keptOf m).zip r.kept).all fun qi =>
        pj.1.seat != qi.1 || (addrsFrom (ofLink m) 0 Wc)[qi.2]? == some (k, pj.2)) &&
      ((N0Full.sent (m + 1) 0).zipIdx.all fun qi =>
        pj.1.seat != qi.1 || ((Wc.map (·.1)).findIdx (ofLink (m + 1)), qi.2) == (k, pj.2))

set_option maxRecDepth 1000000 in
/-- **IT ACCEPTS AT ALL 25 SWITCHES.** -/
theorem radTie_written : ((List.range 25).all fun m => radTieB psFull m) = true := by
  decide +kernel

/-- The plan's seats with every sending's number one more. -/
def shifted (ps : List PSeat) : List PSeat := ps.map fun p => { p with send := p.send + 1 }

set_option maxRecDepth 1000000 in
/-- **A negative test**: with every sending's number one more the tie rejects at the first
switch. -/
theorem radTie_rejects : radTieB (shifted psFull) 0 = false := by decide +kernel

/-- **THE RADII's CLAUSE, FROM THE TIE OF THE INDICES**: at rows R whose first chain's labels and
numbers of sampled entries are the written ones, at a row r that holds R's own entries. -/
theorem radii_of_rows {R : List SendRow} {m : ℕ} {r : SwRow}
    (hW : (firstRows R).map (fun x => (x.label, x.sampled.length)) = Wc)
    (hlo : r.lo = linkList R m)
    (hl : r.l = ((linkRows R (m + 1)).head?.map (·.sampled)).getD [])
    (hm : m < 25) (hr : tableFullLit[m]? = some r) :
    ∀ k j p, k < proofSends0.sends.length → (mineAt psFull k)[j]? = some p →
      ∀ qe ∈ (N0Full.keptOf m).zip (keptEntries r) ++ (N0Full.sent (m + 1) 0).zip r.l,
        p.seat = qe.1 → radOf R k j = qe.2.2 := by
  intro k j p hk hp qe hqe hs
  have h := List.all_eq_true.1 radTie_written m (List.mem_range.2 hm)
  unfold radTieB at h
  rw [hr] at h
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 h k (List.mem_range.2 hk)) (p, j)
    (List.mem_zipIdx_iff_getElem?.2 hp)
  rw [Bool.and_eq_true] at h1
  obtain ⟨t1, t2⟩ := h1
  have hLab : (firstRows R).map (·.label) = Wc.map (·.1) := by
    rw [← hW, List.map_map]
    rfl
  rw [radOf_entry]
  rcases List.mem_append.1 hqe with hq | hq
  · unfold keptEntries at hq
    rw [List.zip_map_right] at hq
    obtain ⟨⟨q, i⟩, hmem, rfl⟩ := List.mem_map.1 hq
    have t := List.all_eq_true.1 t1 (q, i) hmem
    rw [Bool.or_eq_true] at t
    rcases t with t | t
    · exact absurd hs (bne_iff_ne.1 t)
    · have ea : (addrsFrom (ofLink m) 0 Wc)[i]? = some (k, j) := eq_of_beq t
      have e2 : r.lo[i]? = entry (firstRows R) (k, j) := by
        rw [hlo, linkList_at, hW, ea]
        rfl
      show _ = (r.lo.getD i default).2
      rw [List.getD_eq_getElem?_getD, e2]
      cases entry (firstRows R) (k, j) <;> rfl
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem hq
    obtain ⟨a1, a2⟩ := List.getElem?_zip_eq_some.1 hi
    have t := List.all_eq_true.1 t2 (qe.1, i) (List.mem_zipIdx_iff_getElem?.2 a1)
    rw [Bool.or_eq_true] at t
    rcases t with t | t
    · exact absurd hs (bne_iff_ne.1 t)
    · have ea : ((Wc.map (·.1)).findIdx (ofLink (m + 1)), i) = (k, j) := eq_of_beq t
      rw [hl, linkHead_at, hLab, ea] at a2
      rw [a2]
      rfl

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **THE RADII's CLAUSE AT THE CONSTANT's OWN RADII, FROM «THE MADE TABLE IS THE WRITTEN ONE».** -/
theorem radii_of_table (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hZ : VerifierAndGoals.InScope Z = true) (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r₀ Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hT : tableOf Z.pol Z.lay Z.KL = .ok tableFullLit) {m : ℕ} (hm : m < 25) {r : SwRow}
    (hr : tableFullLit[m]? = some r) :
    ∀ k j p, k < proofSends0.sends.length → (mineAt psFull k)[j]? = some p →
      ∀ qe ∈ (N0Full.keptOf m).zip (keptEntries r) ++ (N0Full.sent (m + 1) 0).zip r.l,
        p.seat = qe.1 → P5J.At.rad Zp Z.lay k j = qe.2.2 := by
  obtain ⟨p, R, -, hR, e⟩ := tableOf_iff.1 hT
  obtain ⟨hlo, hl'⟩ := made_row _ _ R m r (by rw [← e]; exact hr)
  obtain ⟨k0, k1, k2, e', p1, p2, hs⟩ := sends_of_laid hl L.pub
  have hF := first_rows_labels hR hs (first_is_fifth hs)
  rw [sends_at hZ L hy] at hF
  have hW : (firstRows R).map (fun x => (x.label, x.sampled.length)) = Wc := by
    have h2 := congrArg (List.map fun t : String × List OracleShape => (t.1, t.2.length)) hF
    rw [List.map_map, List.map_map] at h2
    unfold Wc
    refine Eq.trans (List.map_congr_left fun x _ => ?_) h2
    simp
  have hrad : P5J.At.rad Zp Z.lay = radOf R := by
    obtain ⟨e1, e2⟩ := ProofFile.Law.pub_files L.pub
    unfold P5J.At.rad P5T.rowsAt?
    rw [e1, e2, hR]
    rfl
  rw [hrad]
  exact radii_of_rows hW hlo hl' hm hr

/-- **THE NAMED TEST membersPlanB IS A THEOREM AT THE CONSTANT's OWN TERMS, AT ALL 25 SWITCHES.** -/
theorem membersPlan_const (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hZ : VerifierAndGoals.InScope Z = true) (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r₀ Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (hT : tableOf Z.pol Z.lay Z.KL = .ok tableFullLit) {m : ℕ} (hm : m < 25) {r : SwRow}
    (hr : tableFullLit[m]? = some r) :
    membersPlanB Zp (P5J.At.rad Zp Z.lay) (P5J.At.N Zp cF) (m + 1) r = true :=
  membersPlan_at (at_written hZ L hy) (sends_at hZ L hy) hm hr _
    (radii_of_table hl hZ L hy hT hm hr)

end

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.radTie_rejects
#print axioms VerifiableInference.Desc.First.K2Ties.radii_of_rows
#print axioms VerifiableInference.Desc.First.K2Ties.radii_of_table
#print axioms VerifiableInference.Desc.First.K2Ties.membersPlan_const

#print axioms VerifiableInference.Desc.First.K2Ties.radTie_written
