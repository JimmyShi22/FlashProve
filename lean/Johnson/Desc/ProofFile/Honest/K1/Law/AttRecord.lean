-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/AttRecord.lean: ON THE ROAD TO THE
ITEM "tie m" AT AN ATTENTION's SEGMENT: WHAT THE RECORD OF THE SMALLNESS TEST IS BEHIND THE READS'
MEMBER's ACCEPTED STEP, AND THAT ITS TABLES LIE IN THE VECTOR OF READS. Three statements and their
proofs. No definition. PUBLIC: blocks, a verifier's state, sizes and first entries: no witness, no
coin is read, no cell.

  entriesOf_funBack   a table's number of entries by the two spellings: entriesOf (Johnson/Meaning/
                      PlanesLaw.lean) at funBack f is K5Law.szOf at f
  tablesLie_att       where attention's tablesP returns t at the sizes of mats: TablesLie mats
                      (t.funs.map funBack) nW (Johnson/HonestTrace/Reads.lean)
  att_record          behind an accepted step of a member that lies under the library's reads'
                      block at a link of the kind 1: the library's block itself says yes there,
                      from s to s'; there is a state s₁ with: the sending's own decision says yes
                      from s to s₁; the quiet step readsAtSO says yes from s₁ to s'; and s₁'s open
                      attention's part a, what its own rounds heard hh, what the lookup returned
                      g, points p and tables t with: ptsFrom's return at s₁'s own data; tablesP's
                      return at p; the guard of order's yes; and s'.tl? is a.tl with the list
                      closed over (tabsBack t).funs

BY CALLS, ALL SEALED: of attention's house: K5Law.tablesP_laid, tablesP_fits, lay_in, lay_apart
(Johnson/Desc/First/Att/Claims/ReadsApart.lean), total_is_nW (Claims/TablesTile.lean), elems_sz,
matsOf_getD (Johnson/Desc/K5/Honest/Law/U3Law.lean), quiet_is (Law/ReadsAfter.lean), readsAtSO_iff
(Law/ReadsStep.lean); of the kind K1's: joined_yes, rounds_k1Reads. att_record's road is
layers_record's (LayersRecord.lean).

Limits. That a step is accepted is a premise (a law under "Stepped"). Nothing says that a.tl is the
plan's, nor that it is the record of s's own part. Nothing ties p or t to what a prover heard.
Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.LayersRecord
import Johnson.Desc.First.Att.Claims.TablesTile
import Johnson.Desc.K5.Honest.Law.U3Law
import Johnson.Desc.K5.Honest.Law.ReadsAfter
import Johnson.HonestTrace.Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open OnBytes.Model (HTailF2 HFun TMat)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att (P.Fun1 P.Geo P.LookIn P.Pts P.TablesP funBack tabsBack)
open VerifiableInference.Desc.Sound (MsgT roundsFit_len)
open VerifiableInference.Desc.K1 (joined_yes rounds_k1Reads)
open OnBytes.HonestTrace (TablesLie)
open Meaning.Planes (entriesOf stretches)
open OnBytes.Model.Stages (LinkH)
open ProofFile.Honest.FirstThread (Letters)

/-- A table's number of entries, by the two spellings. -/
theorem entriesOf_funBack (mats : Array TMat) (f : P.Fun1) :
    entriesOf mats (funBack f) = K5Law.szOf (K5Law.matsOf mats) f := by
  rw [← H2K5.Honest.U3Law.elems_sz]
  unfold entriesOf stretches H2K5.Honest.elemsOf H2K5.Honest.blocksOf
  rw [H2K5.Honest.U3Law.matsOf_getD]
  rfl

/-- **The tables that attention's tablesP returns lie in the vector of reads**: each ends below nW,
and two that hold one entry are one. Public: sizes, weights' lengths, first entries. -/
theorem tablesLie_att {g : P.Geo} {nW : ℕ} {lk : P.LookIn} {p : P.Pts} {t : P.TablesP}
    {mats : Array TMat}
    (h : First.Att.P.tablesP g (K5Law.matsOf mats) nW lk p = some t) :
    TablesLie mats (t.funs.map funBack) nW := by
  have hl := K5Law.tablesP_laid h
  have hf := K5Law.tablesP_fits h
  have ht := K5Law.total_is_nW h
  have back : ∀ F ∈ (t.funs.map funBack).toList,
      ∃ f ∈ K5Law.layFrom 0 (K5Law.laidBy g lk p), funBack f = F := by
    intro F hF
    rw [Array.toList_map, List.mem_map] at hF
    obtain ⟨f, hf', e⟩ := hF
    exact ⟨f, hl ▸ hf', e⟩
  refine ⟨fun F hF => ?_, fun F hF F' hF' col hc col' hc' he => ?_⟩
  · obtain ⟨f, hm, rfl⟩ := back F hF
    rw [entriesOf_funBack]
    have := (K5Law.lay_in _ 0 hf f hm).2
    rw [ht, Nat.zero_add] at this
    exact this
  · obtain ⟨f, hm, rfl⟩ := back F hF
    obtain ⟨f', hm', rfl⟩ := back F' hF'
    rw [entriesOf_funBack] at hc hc'
    have e : f = f' := K5Law.lay_apart _ 0 hf f hm f' hm' (f.start + col) (Nat.le_add_right _ _)
      (Nat.add_lt_add_left hc _)
      (by have : (funBack f).start + col = (funBack f').start + col' := he
          show f'.start ≤ f.start + col
          have h2 : f.start + col = f'.start + col' := this
          omega)
      (by have h2 : f.start + col = f'.start + col' := he
          omega)
    rw [e]

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr' X' P Cells Tok : Type}

/-- **What the record of the smallness test is behind an accepted step of the reads' member at an
attention's segment.** The sister of layers_record and head_record. s₁ IS TIED AT BOTH ENDS:
the sending's own decision says yes
from s to s₁, and the quiet step readsAtSO from s₁ to s'. a is s₁'s open attention's part. THE
POINTS p ARE TIED TOO: they are what the verifier's ptsFrom makes
OF THE STATE s₁ (what its own rounds heard hh, what the lookup returned g, its ledger a.F). THEY
ARE NOT TIED TO WHAT A PROVER HEARD: that tie lies in AttPlanS' last clause (TieReadsAttS.lean), a
premise. SO THE RECORD's PUBLIC PART IS THAT OF THE STATE BEHIND THE SENDING, NOT THE PLAN's: the
quiet step closes the list that the state holds. That a.tl is the record of s's own part is NOT
said here (the library's k1_leaves, Johnson/Desc/K5/Honest/Law/ReadsAfter.lean, has it where s's
part is open). -/
theorem att_record {L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT} {m : ℕ}
    {Z : ProofFile.Pub} {G : ProofFile.Ground} {X : LinkH} {pr : ℕ} {reads : Option (List ℕ)}
    {A : OnBytes.Attention.Plan} (hk : X.kind = 1) (hA : G.W.A[X.g]? = some A) {k : Coins Bk}
    {s s' : S} {μ : Mid (Local W₀ Rc Xi Tr') X'} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Xi Tr') X'} {cols : List OpenedColumn} {blk : Block S Cl}
    (hU : blk.UnderR ((IM.k1Reads Z G m X pr reads).retype : Block S Cl))
    (hS : L.thread.Stepped blk k s μ E ds y cols s') :
    ∃ (r₁ r₂ : Fmt.RoundView) (gs gs₁ : List (List (ℕ × List UInt64))) (s₁ : S) (a : First.AttOwn)
      (hh : First.Att.P.Heard) (g : OnBytes.Model.Forest.Heard) (p : First.Att.P.Pts)
      (t : First.Att.P.TablesP),
      (IM.k1Reads Z G m X pr reads).decide s [r₁, r₂] gs = .ok s' ∧
      (K1.laterAt (Cl := Unit) G.first (K1.gpOf Z) m pr 1 reads).decide s [r₁, r₂] gs₁ = .ok s₁ ∧
      First.Att.readsAtSO A s₁ = .ok s' ∧
      s₁.here = .att a ∧ s₁.heard5? = some hh ∧ a.g = some g ∧
      First.Att.P.ptsFrom (First.Att.P.parCOf A).geo g.zk hh a.F = some p ∧
      First.Att.P.tablesP (First.Att.P.parCOf A).geo (First.Att.P.parCOf A).mats
        (First.Att.P.parCOf A).nW (First.Att.P.lookOfO (First.Att.P.parCOf A).geo.lmb g) p =
        some t ∧
      First.K8.Order.orderOk { a.tl with funClosed := true, funs := (tabsBack t).funs } a.L
        s₁.st = true ∧
      s'.tl? = some { a.tl with funClosed := true, funs := (tabsBack t).funs } := by
  unfold Thread.Stepped at hS
  obtain ⟨hfit, -, hdec, -⟩ := Block.step_ok.1 (step_under hU hS.2)
  have hlen : ((roundsOf y.1).map noDigest).length = 2 := by
    rw [List.length_map, roundsFit_len _ _ hfit]
    exact rounds_k1Reads Z G m X pr reads
  obtain ⟨r₁, r₂, hr⟩ := List.length_eq_two.1 hlen
  rw [hr] at hdec
  have hdec : (IM.k1Reads Z G m X pr reads).decide s [r₁, r₂] _ = .ok s' := hdec
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ :=
    joined_yes _ _ _ _ _ (IM.k1Quiet G m X) s s' r₁ r₂ _ hdec
  rw [H2K5.Honest.quiet_is G m X hk hA] at h3
  obtain ⟨a, hh, g, p, t, ha, h5, hg, -, hp, ht, -, hord, e⟩ :=
    (H2K5.Honest.readsAtSO_iff A s₁ s').1 h3
  refine ⟨r₁, r₂, _, gs₁, s₁, a, hh, g, p, t, hdec, h1, h3, ha, h5, hg, hp, ht, hord, ?_⟩
  rw [e]
  rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.entriesOf_funBack
#print axioms ProofFile.Honest.K1.tablesLie_att
#print axioms ProofFile.Honest.K1.att_record
