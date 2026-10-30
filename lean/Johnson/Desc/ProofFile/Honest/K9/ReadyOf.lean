-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/ReadyOf.lean: THE PREMISE `ready` OF `accepted_bat_at_head` (Honest/K9/BatAtHead.lean), CUT INTO ITS
GUARDS. The batching's draw makes thirteen tests on book-keeping before it reads the drawn element (`drawReady`,
Honest/K9/BatYes.lean; the mark "the one equation has been made" is asked beside them). Here each test, or group of tests, is a
named sentence on a state that stands in front of a batching, and `ready` follows from these sentences.

  `Front cF Zp l s`      s stands in front of the batching of segment l: it is reached by the first chain's own first
                        14 l + `IM.nAt l` + 2 sub-protocols; it has no mark of failure; a segment is open; no count of rows
                        waits; the open segment's number is l
  `standBatB`, `standBat_all`, `stand_bat`   the test on the written list of places, by Lean's kernel, and what it gives
  **`front_of_thr`**     where the thread's invariant holds at that number, `Front` holds
  `Fresh F`              of a ledger: the batching element is not drawn; no claim is counted; the one equation has not been
                        made; no weight, no coefficient and no constant is laid
  `LinkReady L`          of a segment's book-keeping: its list of arrays is a segment's and is closed; the draw has not run;
                        all of the segment's moments have passed
  `open_of_stand`        a state that stands inside an open segment holds book-keeping, a ledger and the smallness test's
                        record
  `owed_of_none`         where no count waits, the batching's lens reads "nothing is owed"
  `ready_of_parts`       the lens's answer and the thirteen tests, from the parts
  **`ready_of`**         `ready`, to the letter, from four sentences at `Front`: `Fresh`, `LinkReady`, "the slots taken are
                        the ledger's number of slots" and "claims are planned"; paid here: the lens answers, nothing is
                        owed, and the list of coefficients has a coefficient a slot

Limits. The four sentences are premises. The full size and the hash function `secondHashFunction` alone: the hypothesis's. It is not
proved that the invariant holds at any run. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K9.BatAtHead
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.First.Att.K05T2
import Johnson.LPFE1R.PartAtBatch
import Johnson.P5J.SlotsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open Johnson.Desc.First.Walk.Tied (Reach)

/-! ## The state in front of a batching -/

/-- **s stands in front of the batching of segment l.** -/
structure Front (cF : Chain TS ProofFile.Cl) (Zp : ProofFile.Pub) (l : ℕ) (s : S) : Prop where
  reach : ∃ z, Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 2) (z, s)
  clean : s.failed = none
  stand : standOf s = .link (IM.subAt l)
  none : s.noneWaits = true
  number : ∀ L, s.link? = some L → L.link = l

/-- The test on the written list of places: at each number 14 l + `IM.nAt l` + 2 the list says "inside the open segment
l", and no count of rows may wait there. -/
def standBatB : Bool :=
  (List.range 25).all fun l =>
    match P5J.At.ps[14 * l + IM.nAt l + 2]? with
    | some p =>
      (match standAt P5J.At.links p with
        | .link sub => sub == IM.subAt l
        | _ => false) && !mayWait P5J.At.links p && p.link == some l
    | none => false

/-- It accepts: by Lean's kernel. -/
theorem standBat_all : standBatB = true := by decide +kernel

theorem stand_bat {l : ℕ} (hl : l < 25) :
    ∃ p, P5J.At.ps[14 * l + IM.nAt l + 2]? = some p ∧ standAt P5J.At.links p = .link (IM.subAt l) ∧
      mayWait P5J.At.links p = false ∧ p.link = some l := by
  have k := List.all_eq_true.1 standBat_all l (List.mem_range.2 hl)
  cases hp : P5J.At.ps[14 * l + IM.nAt l + 2]? with
  | none =>
    rw [hp] at k
    cases k
  | some p =>
    rw [hp] at k
    have k' : ((match standAt P5J.At.links p with
      | .link sub => sub == IM.subAt l
      | _ => false) && !mayWait P5J.At.links p && p.link == some l) = true := k
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at k'
    obtain ⟨⟨k1, k2⟩, k3⟩ := k'
    cases hs : standAt P5J.At.links p with
    | link sub =>
      rw [hs] at k1
      obtain rfl : sub = IM.subAt l := beq_iff_eq.1 k1
      exact ⟨p, rfl, hs, k2, k3⟩
    | between => rw [hs] at k1; cases k1
    | headFront => rw [hs] at k1; cases k1
    | fin => rw [hs] at k1; cases k1
    | mem => rw [hs] at k1; cases k1

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₀ : Local W₀ Rc ProofFile.Inst Tr)

/-- **Where the invariant holds in front of the batching of segment l, `Front` holds.** -/
theorem front_of_thr {l : ℕ} (hl : l < 25) {k : Coins Bk} {s : TS}
    {μ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).thread
      (14 * l + IM.nAt l + 2) k s μ En) : Front cF Zp l s := by
  obtain ⟨p, hp, hs, hw, hpl⟩ := stand_bat hl
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hlen : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  have hb : 14 * l + IM.nAt l + 2 ≤ cF.blocksInOrder.length := by
    rw [hlen]
    unfold IM.nAt
    split <;> omega
  have hR := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀ hb hT
  unfold Thr at hT
  obtain ⟨-, -, ⟨hf, hP⟩, -, -, -, -⟩ := hT
  have hf' : s.failed.isNone = true := hf
  have hn : s.failed = none := Option.isNone_iff_eq_none.1 hf'
  have hP' : onAt (P5J.At.N Zp cF) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).mgP P5J.At.links
      P5J.At.ps[14 * l + IM.nAt l + 2]?
      (((openSets P5J.At.links P5J.At.ps (start P5J.At.links))[14 * l + IM.nAt l + 2]?).getD [])
      (((pubSets (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).mgP.more P5J.At.links
        P5J.At.ps)[14 * l + IM.nAt l + 2]?).getD []) (μ.st.input.x.pub, s) noStrs := hP
  rw [hp] at hP'
  have hsh := Att.P.onAt_shape hP' hn
  unfold shapeAt at hsh
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, hw, Bool.false_eq_true, or_false] at hsh
  refine ⟨⟨_, hR⟩, hn, hsh.1.1.trans hs, hsh.1.2, fun L hL => ?_⟩
  have h3 := hsh.2
  rw [hL, Option.all_some, hpl] at h3
  exact (Option.some.inj (beq_iff_eq.1 h3)).symm

end

/-! ## The sentences -/

/-- **Of a ledger: nothing of the batching has happened to it.** -/
structure Fresh (F : Fork) : Prop where
  drawn : F.thetaDrawnF = false
  count : F.nClaim = 0
  door : F.doorShutF = false
  empty : Desc.K9.ledgerEmpty F = true

/-- **Of a segment's book-keeping: it is ready for the draw.** -/
structure LinkReady (L : LinkCtx) : Prop where
  planned : L.list.planned = true
  link : L.list.link = true
  handed : L.handed = false
  moments : L.moments = L.check.momentsOf L.link

/-- A state that stands inside an open segment holds book-keeping, a ledger and the smallness test's record. -/
theorem open_of_stand {s : S} {sub : ModelPart} (h : standOf s = .link sub) :
    ∃ L F tl, s.link? = some L ∧ s.fork? = some F ∧ s.tl? = some tl := by
  unfold standOf at h
  cases hh : s.here with
  | between => rw [hh] at h; cases h
  | lay a => exact ⟨a.L, a.F, a.tl, by simp [S.link?, hh], by simp [S.fork?, hh], by simp [S.tl?, hh]⟩
  | att a => exact ⟨a.L, a.F, a.tl, by simp [S.link?, hh], by simp [S.fork?, hh], by simp [S.tl?, hh]⟩
  | head a =>
    rw [hh] at h
    cases hi : s.inLink with
    | false =>
      rw [hi] at h
      cases h
    | true =>
      have ho : a.opened = true := by
        by_contra ho
        simp [S.inLink, S.fork?, hh, ho] at hi
      exact ⟨a.L, a.F, a.tl, by simp [S.link?, hh, ho], by simp [S.fork?, hh, ho], by simp [S.tl?, hh, ho]⟩
  | fin a => rw [hh] at h; cases h
  | mem a => rw [hh] at h; cases h

/-- Where no count waits, the lens reads "nothing is owed". -/
theorem owed_of_none {s : S} (h : s.noneWaits = true) : Desc.K9.owedOf s = none := by
  unfold S.noneWaits at h
  unfold Desc.K9.owedOf
  cases e : s.rowsOwed with
  | none => rfl
  | some n =>
    rw [e] at h
    obtain rfl : n = 0 := by simpa using h
    rfl

/-- The lens's answer, from the parts. -/
theorem lens_of_parts {s : S} {L : LinkCtx} {F : Fork} {tl : HTailF2} {u : ℕ} (hL : s.link? = some L)
    (hF : s.fork? = some F) (ht : s.tl? = some tl) (hu : Desc.K9.usedOf s = some u) :
    ∃ a, Desc.K9.atS.get? s = some a ∧ a.owed = Desc.K9.owedOf s ∧ a.used = u ∧ a.L = L ∧ a.F = F := by
  cases hq : Desc.K9.atS.get? s with
  | none => simp [Desc.K9.atS, hL, hF, ht, hu] at hq
  | some a =>
    simp [Desc.K9.atS, hL, hF, ht, hu] at hq
    subst hq
    exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- The lens's answer and the tests, from the parts. -/
theorem ready_of_parts {s : S} {L : LinkCtx} {F : Fork} {tl : HTailF2} {u : ℕ} (hL : s.link? = some L)
    (hF : s.fork? = some F) (ht : s.tl? = some tl) (hu : Desc.K9.usedOf s = some u) (hn : s.noneWaits = true)
    (fr : Fresh F) (lr : LinkReady L) (used : u = F.ns) (plan : F.planClaimsF ≠ 0) (size : F.LS.size = F.ns) :
    ∃ a, Desc.K9.atS.get? s = some a ∧ drawReady a = true ∧ a.F.doorShutF = false := by
  obtain ⟨a, ha, e1, e2, e3, e4⟩ := lens_of_parts hL hF ht hu
  refine ⟨a, ha, ?_, by rw [e4]; exact fr.door⟩
  unfold drawReady
  rw [e1, e2, e3, e4]
  simp only [owed_of_none hn, lr.planned, lr.link, lr.handed, lr.moments, fr.drawn, fr.count, fr.empty, used, size,
    Option.isNone_none, beq_self_eq_true, Bool.not_false, Bool.and_self, Bool.and_true, Bool.true_and, bne_iff_ne, ne_eq]
  exact plan

/-! ## The premise -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The number of slots taken is told in front of every batching. -/
theorem used_at_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} {s : S} (hS : Front cF Zp l s) :
    ∃ u, Desc.K9.usedOf s = some u := by
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨Bs, base, O⟩ := h.laid.opened
    obtain ⟨z, hz⟩ := hS.reach
    exact Option.isSome_iff_exists.1 (LinkJoin.used_at_347 h.scope h.reads O hz)
  · have hs := hS.stand
    have hsub : IM.subAt l ≠ .head := by
      unfold IM.subAt
      rw [if_neg h24]
      split <;> exact fun e => nomatch e
    unfold standOf at hs
    cases hh : s.here with
    | between => rw [hh] at hs; cases hs
    | lay a => exact ⟨a.tl.slotB, by simp [Desc.K9.usedOf, hh]⟩
    | att a => exact ⟨a.F.next, by simp [Desc.K9.usedOf, hh]⟩
    | head a =>
      rw [hh] at hs
      dsimp only at hs
      split at hs
      · exact absurd (Stand.link.inj hs).symm hsub
      · cases hs
    | fin a => rw [hh] at hs; cases hs
    | mem a => rw [hh] at hs; cases hs

/-- The list of coefficients has a coefficient a slot, in front of every batching. -/
theorem size_at_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) {s : S}
    (hS : Front cF Zp l s) {L : LinkCtx} {F : Fork} (hL : s.link? = some L) (hF : s.fork? = some F) :
    F.LS.size = F.ns := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨A, B, c, e, _, hs⟩ := LinkJoin.slots_at_reached _ h.laid.pub h.headSpots h.laid.value
  have he : HEq cF c :=
    congr_arg_heq (fun X : VerifiableInference.Desc.FileDescription ProofFile.Inst => X.first) e
  obtain rfl : cF = c := eq_of_heq he
  obtain ⟨z, hz⟩ := hS.reach
  have hk : 14 * l + IM.nAt l + 2 ≤ (Meaning.K2.frontOf cF).length := by
    rw [Meaning.Carry.front_len h.scope h.reads O]
    unfold IM.nAt
    split <;> omega
  exact (LinkJoin.slots_field (hs _ _ hz hk) hF hL rfl).2

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₀ : Local W₀ Rc ProofFile.Inst Tr)

/-- **The premise `ready` of `accepted_bat_at_head`, from four sentences on the states in front of the batching.** -/
theorem ready_of {l : ℕ} (hl : l < 25)
    (fresh : ∀ s, Front cF Zp l s → ∀ F, s.fork? = some F → Fresh F)
    (link : ∀ s, Front cF Zp l s → ∀ L, s.link? = some L → LinkReady L)
    (used : ∀ s, Front cF Zp l s → ∀ F u, s.fork? = some F → Desc.K9.usedOf s = some u → u = F.ns)
    (plan : ∀ s, Front cF Zp l s → ∀ F, s.fork? = some F → F.planClaimsF ≠ 0)
    {Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop} :
    ∀ κ s m En,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀).thread Said (14 * l + IM.nAt l + 2) κ s m En →
      ∃ a, Desc.K9.atS.get? s = some a ∧ drawReady a = true ∧ a.F.doorShutF = false := by
  intro κ s m En hT
  have hS := front_of_thr h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₀ hl hT.1
  obtain ⟨L, F, tl, hL, hF, ht⟩ := open_of_stand hS.stand
  obtain ⟨u, hu⟩ := used_at_front h hS
  exact ready_of_parts hL hF ht hu hS.none (fresh s hS F hF) (link s hS L hL) (used s hS F u hF hu)
    (plan s hS F hF) (size_at_front h hl hS hL hF)

end

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.standBat_all
#print axioms ProofFile.Honest.K9.stand_bat
#print axioms ProofFile.Honest.K9.front_of_thr
#print axioms ProofFile.Honest.K9.open_of_stand
#print axioms ProofFile.Honest.K9.owed_of_none
#print axioms ProofFile.Honest.K9.lens_of_parts
#print axioms ProofFile.Honest.K9.ready_of_parts
#print axioms ProofFile.Honest.K9.used_at_front
#print axioms ProofFile.Honest.K9.size_at_front
#print axioms ProofFile.Honest.K9.ready_of
