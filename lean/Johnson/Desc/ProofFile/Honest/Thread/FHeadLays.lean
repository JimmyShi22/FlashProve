-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/FHeadLays.lean: the column `hl` of the gathering
(`owesS_head_form`, GatherHeadForm.lean) at the rider clauses `csHead` (CsHead.lean), from the
column `hK`. `fHead_hK_whole` (FHeadKeepsWhole.lean) gives, at every accepting step from the
invariant, the clause of `fHead` (FHead.lean) at the sub-protocol's place. For 17 of the 55 clauses
of `csHead` that clause states the rider's fact, in three cases together with a rider that holds
before the step. `laysAtS_of_clause` (LaysOfKeeps.lean) turns this into `LaysAtS`. The other 38
clauses hang on one of the three open arguments `ν`, `st`, `R` of `csHead`. They stay hypotheses. No
definition.

  1  `fHead_clause_hear`   the clause of `fHead` at the `i`-th hearing sub-protocol of segment `l`,
     with the place written out
  2  `head_riders`   the invariant before a step gives `ridersOf (csHead ν st R)` there
  3  `fHead_lays_x`, `fHead_lays_t`, `fHead_lays_fold0`, `fHead_lays_fold1`, `fHead_lays_wo`,
     `fHead_lays_own`   `LaysAtS` at the numbers 341, 342, 343, 345, 346 and `28 * g + 4`
  4  `fHead_hl`   **the column `hl`**, from four hypotheses in the forms of `csHead_lays`
     (GatherLays.lean)

All lemmas hold for every `Kp`: `LaysAtS` does not read `keeps`. `fHead_lays_fold1` calls
`fHead_h3H` (FHeadStaysAll.lean), whose hypothesis `rngWrittenB = true` is `rngWritten_holds`
(K3/Law/Thread/RngWrittenHolds.lean) of the authors of K3's lemmas. Their proof rests on two
evaluations by the kernel (`decide +kernel`).

What `fHead_hl` leaves as hypotheses.
  * `hB`: `ProofFile.baseOf` returns at the public part (a hypothesis of `fHead_hK_whole`).
  * `hnx`: sub-protocol 345 establishes `a.F.next = ν`. `hs`, `hst`: the lookups on the digits
    establish `st 24` and `st l`. `hatt`: the lookup on the calls of an attention segment
    establishes `R g a.g`.

Other authors prove `LaysAt` or `LaysAtS` for some of the same six facts from the laws of their own
steps: `k6_lays` (K6/Law/Lays.lean), `k1_laysS_t` (K1/Law/LaysT.lean), `lays_foldDrawn_thread`
(K3/Law/Thread/HeadDigitsAtLink.lean), `headMergeLaysWo` (K11/Plays/Riders.lean), `k4_laysS_own`
(K4/Law/LaysOwn.lean). They are not called here: each needs further hypotheses or further files, and
`hK` is proved already.

Limits.
  * That an accepting step exists at any state is not shown.
  * Full size only, under the library's `AtMgA` at the hash function `secondHashFunction`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.LaysOfKeeps
import Johnson.Desc.ProofFile.Honest.Thread.GatherLays
import Johnson.Desc.ProofFile.Honest.Thread.FHeadKeepsWhole
import Johnson.Desc.ProofFile.Honest.Thread.FHeadStaysAll
import Johnson.Desc.ProofFile.Honest.Thread.HeadPlaceAt
import Johnson.Desc.ProofFile.Honest.Thread.CsHeadAt
import Johnson.Desc.ProofFile.Honest.K1.Law.KeepsReads
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RngWrittenHolds
import Johnson.Desc.K6.Honest.Law.Keeps
import Johnson.Desc.K8.Honest.KeepsFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place KindName)
open VerifiableInference.Desc.First (kindsBeforeBatching)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.K3.Law.AtThr (rngWritten_holds)
open ProofFile.Honest.K1 (K1ReadsKeepsM k1_reads_lays_t)
open VerifiableInference.Desc.First.K8.Honest (K8KeepsM)
open VerifiableInference.Desc.Kinds.Head.Honest (K6Keeps)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)

section
variable (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- The clause of `fHead` at a hearing sub-protocol of a segment, with the place written out. -/
theorem fHead_clause_hear {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {l i : Nat} {κ : KindName}
    (hl : l < 25) (hk : (kindsBeforeBatching (IM.subAt l) (l == 0))[i]? = some κ) :
    ∀ blk, (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[14 * l + i + 2]? =
        some blk →
      ∀ k s m E ds y cols s',
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
        (14 * l + i + 2) k s m E →
      drawsFit blk.rounds ds = true →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      fHead Zp cF Bs.G₀ P1L20.bearing (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made)
        (VerifiableInference.Desc.K13.whereOf Zp) κ
        { chain := 1, link := some l, piece := i + 1, kind := κ } s s' := by
  intro blk hblk k s m E ds y cols s' hA hd hS
  have hb : 14 * l + i + 2 <
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs.length := by
    by_contra hn
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at hblk
    cases hblk
  have c := fHead_hK_whole h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hB _ hb blk hblk k s m E
    ds y cols s' hA hd hS
  have hb' : cF.blocksInOrder[14 * l + i + 2]? = some blk := hblk
  rw [head_place_hear h hl hk hb'] at c
  exact c

end

variable (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option OnBytes.Model.Forest.Heard → Prop)
  (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)

/-- The invariant at a border gives the rider clauses there. -/
theorem head_riders {b : Nat} {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env}
    (hA : ThrS
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) Kp w).thread
      Said b k s m E) : ridersOf (csHead ν st R) b m.st.input s := by
  have hT := hA.1
  unfold Thr at hT
  obtain ⟨-, -, -, -, -, hr, -⟩ := hT
  exact hr.2

variable {Bs : ProofFile.PureBase} (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)

include hB

/-- Sub-protocol 341 (K6) establishes "the field `x` is set". -/
theorem fHead_lays_x :
    LaysAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) Kp w).thread
      Said 341 (riderHead 342 347 fun a => a.x.isSome = true) :=
  laysAtS_of_clause _ _
    (fHead_clause_hear h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) Kp w Said hB
      (l := 24) (i := 3) (κ := .K6) (by decide) rfl)
    fun _ s _ _ s' _ c => (show K6Keeps s s' from c).heard

/-- Sub-protocol 342 (K1, the reads) establishes "the field `t` is set". -/
theorem fHead_lays_t :
    LaysAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) Kp w).thread
      Said 342 (riderHead 343 348 fun a => a.t.isSome = true) :=
  laysAtS_of_clause _ _
    (fHead_clause_hear h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) Kp w Said hB
      (l := 24) (i := 4) (κ := .K1) (by decide) rfl)
    fun _ s _ _ s' hA c => by
      have c1 : K1ReadsKeepsM s s' := ((fHead_K1_later Zp cF Bs.G₀ P1L20.bearing
        (K11.parOf Zp Bs.G₀) (H2U.p12OfMade Zp.made) (VerifiableInference.Desc.K13.whereOf Zp)
        (p := { chain := 1, link := some 24, piece := 4 + 1, kind := .K1 }) (l := 24) rfl
        (show (4 + 1 : Nat) ≠ 1 by decide) s s').1 c).1
      exact k1_reads_lays_t c1.1 (csHead_in_head
        (head_riders h H Q test carryX item n₁ n₂ b₀ Vd ν st R Kp w Said hA) (by omega) (by omega))

/-- Sub-protocol 343 (K8) establishes "`tl.foldDrawn` is 0". -/
theorem fHead_lays_fold0 :
    LaysAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) Kp w).thread
      Said 343 (riderHead 344 345 fun a => a.tl.foldDrawn = 0) :=
  laysAtS_of_clause _ _
    (fHead_clause_hear h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) Kp w Said hB
      (l := 24) (i := 5) (κ := .K8) (by decide) rfl)
    fun _ s _ _ s' hA c => by
      obtain ⟨a, ha⟩ := csHead_in_head
        (head_riders h H Q test carryX item n₁ n₂ b₀ Vd ν st R Kp w Said hA) (by omega) (by omega)
      exact (show K8KeepsM s s' from c).fold0_head a ha

/-- Sub-protocol 345 (K3, the lookup on the digits) establishes "`tl.foldDrawn` is 1". -/
theorem fHead_lays_fold1 :
    LaysAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) Kp w).thread
      Said 345 (riderHead 346 347 fun a => a.tl.foldDrawn = 1) := by
  obtain ⟨sh, k345⟩ := fHead_h3H h rngWritten_holds
  exact laysAtS_of_clause _ _
    (fHead_clause_hear h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) Kp w Said hB
      (l := 24) (i := 7) (κ := .K3) (by decide) rfl)
    fun _ s _ _ s' hA c => by
      obtain ⟨a, ha, h0⟩ := csHead_fold0_at
        (head_riders h H Q test carryX item n₁ n₂ b₀ Vd ν st R Kp w Said hA) (by omega) (by omega)
      refine k3Head_fold1 (k345 s s' c) fun a' ha' => ?_
      obtain rfl : a = a' := VerifiableInference.Desc.First.Here.head.inj (ha.symm.trans ha')
      exact h0

/-- Sub-protocol 346 (K11, the merge) establishes "the field `wo` is set". -/
theorem fHead_lays_wo :
    LaysAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) Kp w).thread
      Said 346 (riderHead 347 352 fun a => a.wo.isSome = true) :=
  laysAtS_of_clause _ _
    (fHead_clause_hear h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) Kp w Said hB
      (l := 24) (i := 8) (κ := .K11) (by decide) rfl)
    fun _ s _ _ s' _ c => by
      have c1 : Johnson.Desc.First.ForkMerge.Returns.K11KeepsYesAt (K11.parOf Zp Bs.G₀) _ s s' := c
      exact k11_wo c1.2.1

/-- Sub-protocol `28 * g + 4` (K4) establishes "the segment's own rounds have returned
something". -/
theorem fHead_lays_own {g : Nat} (hg : g < 12) :
    LaysAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) Kp w).thread
      Said (28 * g + 4) ⟨28 * g + 5, 28 * g + 10, fun _ _ s => ∃ o, s.own? = some o⟩ := by
  have e : 28 * g + 4 = 14 * (2 * g) + 2 + 2 := by omega
  rw [e]
  exact laysAtS_of_clause _ _
    (fHead_clause_hear h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) Kp w Said hB
      (l := 2 * g) (i := 2) (κ := .K4) (by omega) (head_kind_lay hg rfl))
    fun _ s _ _ s' _ c => k4_own (show ProofFile.Honest.K4.K4KeepsM s s' from c)

/-- **The column `hl` at `csHead`.** -/
theorem fHead_hl
    (hnx : LaysAtS
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) Kp w).thread
      Said 345 (riderHead 346 346 fun a => a.F.next = ν))
    (hs : LaysAtS
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) Kp w).thread
      Said 345 ⟨346, 347, fun _ _ s => st 24 s⟩)
    (hst : ∀ l, l < 24 →
      LaysAtS
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) Kp w).thread
        Said (14 * l + 8) ⟨14 * l + 9, 14 * l + 9, fun _ _ s => st l s⟩)
    (hatt : ∀ g, g < 12 →
      LaysAtS
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) Kp w).thread
        Said (14 * (2 * g + 1) + 3)
        (riderAtt (14 * (2 * g + 1) + 4) (14 * (2 * g + 1) + 9) fun a => R g a.g)) :
    ∀ b, ∀ c ∈ csHead ν st R, c.lo = b + 1 →
      LaysAtS
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf (csHead ν st R)) Kp w).thread
        Said b c :=
  csHead_lays _ _
    (fHead_lays_x h H Q test carryX item n₁ n₂ b₀ Vd ν st R Kp w Said hB)
    (fHead_lays_t h H Q test carryX item n₁ n₂ b₀ Vd ν st R Kp w Said hB)
    (fHead_lays_wo h H Q test carryX item n₁ n₂ b₀ Vd ν st R Kp w Said hB) hnx
    (fHead_lays_fold0 h H Q test carryX item n₁ n₂ b₀ Vd ν st R Kp w Said hB)
    (fHead_lays_fold1 h H Q test carryX item n₁ n₂ b₀ Vd ν st R Kp w Said hB) hs hst hatt
    fun _ hg => fHead_lays_own h H Q test carryX item n₁ n₂ b₀ Vd ν st R Kp w Said hB hg

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.fHead_clause_hear
#print axioms ProofFile.Honest.FirstThread.head_riders
#print axioms ProofFile.Honest.FirstThread.fHead_lays_x
#print axioms ProofFile.Honest.FirstThread.fHead_lays_t
#print axioms ProofFile.Honest.FirstThread.fHead_lays_fold0
#print axioms ProofFile.Honest.FirstThread.fHead_lays_fold1
#print axioms ProofFile.Honest.FirstThread.fHead_lays_wo
#print axioms ProofFile.Honest.FirstThread.fHead_lays_own
#print axioms ProofFile.Honest.FirstThread.fHead_hl
