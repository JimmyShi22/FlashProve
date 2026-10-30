-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/RestJoinOk.lean: THE SMALLNESS TEST: OF THE NINE FACTS THAT
Johnson/Desc/ProofFile/Honest/K8/LeftFront.lean ASKS AT THE STATE IN FRONT OF THE BATCHING SEVEN ARE
NOT WANTED: another house's sentence `K8Behind` at the kind's own share stands under TWO, and the
same second half. By what `K8Behind` itself hands: the library's promise on what is fixed in front,
which holds the static clauses (`StaticOk`, Johnson/Desc/First/Link/Law/OkJoin.lean, inside
`OkCore`, Johnson/Desc/First/Link/Law/OkOne.lean, which the promise of each of the three sorts of
link holds). THE THREE ON THE BLOCKS OF THE DIGITS' ROWS: the static clauses say that the verifier's
two computations of the number of blocks agree (the field `blocks`). THE TWO ON THE DIGITS' ARRAY's
LAST VIRTUAL ROWS: they follow from a clause of the second half: "the first shapes" count that
array's virtual rows behind the routine that lays the weights, and that routine leaves every array's
look (the library's `coef_looks`, Johnson/Desc/First/Batch/Law/K8Tests.lean). THE TWO THAT KEEP
OTHER ARRAYS APART FROM THE DIGITS': the static clauses say of every piece of the two lookup calls
that the array of the bits is not the piece's, and that no matrix's array with virtual row 0 is the
piece's place (the field `piece` of `CoefOK`, OnBytes/Tie/Pv/Lookup/Ends/FoTailPlanes.lean); and two
clauses of the second half ("the first shapes", "the pieces tile") put a piece into the digits'
array at virtual row 0. None of the library's goals.

  `hasRow_of_size`   an array that has n + 1 virtual rows in a ledger is there, with each row up to
                   n
  `wants_first`   the verifier's second computation wants at least one block, and first a piece of
                   call 0, number 0, at virtual row 0
  `piece_first`   where call 0 is as expected and the pieces tile, a piece sits in the digits' array
                   at virtual row 0
  `k8Rest_ofN`   the kept slots are the ledger's slice · the window ends inside the coefficients ·
                   the two numbers of blocks agree · the data's powers · CoefOK at some ledger · the
                   lengths of the vectors · `ValuesLeft` ⊢ `K8Rest`
  `FrontLeftN nU tl F`   TWO: the window ends inside F's number of slots · the lengths of the
                   vectors are the place's
  `FrontAtStandN …`   the named premise: these two at the state in front of the batching, with the
                   promise in hand
  **`restAtStand_ok`**   K8At · ThetaAt at the order · the order's split · PowOn behind
                   "K8.equations" · what is fixed holds the data but for the fourteen fields · the
                   promise holds the static clauses · FrontAtStandN · ValuesAtStand ⊢ RestAtStand
  **`k8Behind_ok`**   the same premises ⊢ K8Behind Lk p φ Ok nU T b (k8Share nU)
  **`okStatic_of_core`**   the sixth of these premises, from `OkCore`, AT THE LIBRARY's OWN READER
                   `pi8`: so at each sort's own promise it is paid
Limits. AN IMPLICATION STILL: `FrontAtStandN` AND `ValuesAtStand` ARE PAID BY NOBODY. OF THE SEVEN
NOTHING IS PROVED FROM NOTHING: THREE HANG ON THE PROMISE ALONE; TWO ARE FOLDED INTO "the first
shapes"; TWO HANG ON THE PROMISE AND ON "the first shapes" AND "the pieces tile": these clauses stay
premises in the second half. THE PROMISE ITSELF IS A PREMISE OF `K8Behind` (it stands inside `Fx9`):
who shows it of an honest state is the other house.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.LeftFront
import Johnson.Desc.First.Link.Law.OkOne
import Johnson.Desc.First.Batch.Law.K8Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open Fo (HasRow)
open OnBytes.Tie.Pv.Tail.Port (Powered)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.First.K8.Honest (ThetaAt rest_powers rest_sizes)
open VerifiableInference.Desc.K9L (Pub9 fixed9 pubOf)
open VerifiableInference.Desc.LinkJoin (PowOn OkCore StaticOk pi8 Q)
open ProofFile.Honest.K9 (BatStand K8Behind LsLaid k8Entry)

/-- An array that has n + 1 virtual rows in a ledger is there, with each row up to n. -/
theorem hasRow_of_size {F : Fork} {t n e : Nat} (h : (F.trees.getD t {}).rows.size = n + 1)
    (he : e ≤ n) : HasRow F t e := by
  refine ⟨?_, by omega⟩
  by_contra hc
  have e0 : F.trees.getD t {} = {} := by simp [Array.getD, hc]
  rw [e0] at h
  exact absurd h (by simp)

/-- The second computation wants at least one block, and first a piece of call 0, number 0, at
virtual row 0. -/
theorem wants_first {tl : HTailF2} {nbW : Nat} {W : List Want} (h : tl.wants = some (nbW, W)) :
    0 < nbW ∧ ∃ w ∈ W, w.call = 0 ∧ w.i = 0 ∧ w.row = 0 := by
  unfold HTailF2.wants at h
  simp only at h
  split at h
  · cases h
  · obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj h)
    subst e1 e2
    refine ⟨by split <;> omega, _, List.mem_flatMap.2 ⟨0, by simp, List.mem_cons_self⟩, rfl, rfl,
      Nat.zero_mul _⟩

/-- Where the first shapes hold and the pieces tile, a piece sits in the digits' array at virtual
row 0. -/
theorem piece_first {tl : HTailF2} {g : Forest.Heard} {G : Fork} {nbW : Nat} {W : List Want}
    (hW : tl.wants = some (nbW, W)) (hc : tl.callHeld g nbW 0 = true)
    (r5 : tl.piecesTile G W = true) :
    ∃ a ∈ Fo.allPieces tl, a.2.tree = tl.ix.ZZ ∧ a.2.row = 0 := by
  obtain ⟨hpos, w, hw, c0, i0, w0⟩ := wants_first hW
  have hsz : (tl.zOf 0).pieces.size = nbW := by
    simp only [HTailF2.callHeld, Bool.and_eq_true, beq_iff_eq] at hc
    exact hc.1.1.1.1.1.1.1.2
  have h0 : 0 < (tl.zOf 0).pieces.size := by omega
  simp only [HTailF2.piecesTile, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at r5
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := r5.2 w hw
  rw [c0, i0] at h1 h2
  rw [w0] at h2
  refine ⟨(0, (tl.zOf 0).pieces.getD 0 {}), ?_, h1, h2⟩
  unfold Fo.allPieces
  refine List.mem_append_left _ (List.mem_map.2 ⟨_, ?_, rfl⟩)
  have e0 : (tl.zOf 0).pieces.getD 0 {} = (tl.zOf 0).pieces[0] := by simp [Array.getD, h0]
  rw [e0]
  exact Array.mem_toList_iff.2 (Array.getElem_mem h0)

/-- `K8Rest`, with "the two numbers of blocks agree" for the three facts on the blocks; the two
virtual rows come out of the first shapes; the two facts that keep other arrays apart come out of
the library's `CoefOK` at the piece at virtual row 0. -/
theorem k8Rest_ofN {nU : Array Nat} {tl : HTailF2} {F : Fork}
    (hls : tl.lsTail = F.LS.extract tl.slotA tl.slotB) (hin : tl.slotB ≤ F.LS.size)
    (hw : tl.wants.map (·.1) = some tl.zzBlocks) (hP : Powered tl F.theta) {Fs : Fork}
    (hC : Fo.CoefOK tl Fs) (r1 : (nU == tl.nUF) = true) (hV : ValuesLeft tl F) :
    K8Rest nU tl F := by
  obtain ⟨g, jo, nbW, W, hg, hjo, hW, r4, r5, r6, r7, r9, r10, r11⟩ := hV
  have hn : nbW = tl.zzBlocks := by
    rw [hW] at hw
    exact Option.some.inj hw
  have hz : ((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.size = (2 * nbW + 1) + 1 := by
    have h4 := r4
    simp only [Bool.and_eq_true, beq_iff_eq] at h4
    exact h4.1.1
  have hc0 : tl.callHeld g nbW 0 = true := by
    have h4 := r4
    simp only [Bool.and_eq_true, List.all_eq_true] at h4
    exact h4.2 0 (by simp)
  obtain ⟨a0, ha0, at0, ar0⟩ := piece_first hW hc0 r5
  obtain ⟨-, -, -, pB, pm⟩ := hC.piece a0 ha0
  have hB : tl.ix.BZ ≠ tl.ix.ZZ := by
    rw [← at0]
    exact pB
  have hm : ∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ tl.ix.ZZ := fun mu hmu e =>
    pm mu hmu ⟨e.trans at0.symm, ar0.symm⟩
  have hl := (K9L.coef_looks tl g F).symm
  have hR : HasRow F tl.ix.ZZ tl.zzRowReads := by
    refine hasRow_of_looks hl (hasRow_of_size hz ?_)
    unfold HTailF2.zzRowReads
    omega
  have hT : HasRow F tl.ix.ZZ tl.zzRowTies := by
    refine hasRow_of_looks hl (hasRow_of_size hz ?_)
    unfold HTailF2.zzRowTies
    omega
  have s2 : (tl.lsTail.size == tl.slotB - tl.slotA) = true := by
    rw [hls]
    exact size_laid tl F hin
  have s3 : selfSlots tl F = true := by
    unfold selfSlots
    rw [hls]
    exact beq_self_eq_true _
  have s7 := rest_sizes tl g F nbW hP hR hT hB hm hn
  have s8 := rest_powers tl g F nbW hP hR hT hB hm hn
  refine ⟨r1, s2, s3, g, jo, nbW, W, hg, hjo, hW, r4, r5, r6, ?_, s8, r9, r10, r11⟩
  simp only [Bool.and_eq_true] at s7 r7 ⊢
  obtain ⟨⟨⟨⟨⟨c3, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩ := r7
  exact ⟨⟨⟨⟨⟨⟨⟨s7.1, s7.2⟩, c3⟩, c4⟩, c5⟩, c6⟩, c7⟩, c8⟩

/-- Two facts on the data and the ledger in front of the batching. -/
def FrontLeftN (nU : Array Nat) (tl : HTailF2) (F : Fork) : Prop :=
  tl.slotB ≤ F.ns ∧ (nU == tl.nUF) = true

/-- The promise of each sort holds the static clauses. -/
theorem okStatic_of_core {β : Type} {nU : Array ℕ} {tlD : HTailF2} {Ok : Q β → Prop}
    (hc : ∀ q, Ok q → OkCore nU tlD q) :
    ∀ q tlb v, Ok q → (pi8 q.1).1 = some tlb → q.2 = some v → StaticOk tlb v.F :=
  fun q tlb v h ht hv => (hc q h).static tlb v ht hv

section
variable {α : Type} (Lk : Link S Claim) (p : Desc.K9.Where) (φ : S → α)
  (Ok : α × Option Pub9 → Prop) (nU : Array ℕ)
  {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Claim V W X Pb) (b : ℕ)

/-- **The named premise**: the two at the state in front of the batching. -/
def FrontAtStandN : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    Ok (fixed9 φ s) → ∀ tlS a, s.tl? = some tlS → Desc.K9.atS.get? s = some a →
      FrontLeftN nU tlS a.F

variable {Lk p φ Ok nU T b} {u : HTailF2} {π : α → Option HTailF2 × Option (Array HFun)}

/-- **The join, with the promise spent.** -/
theorem restAtStand_ok {k : Desc.K9.SegSort} {pW : K8.ParW} (hK : K8At Lk k pW)
    (hTh : ThetaAt Lk Lk.order) {pre post : List (ℕ × String)}
    (hsp : Lk.order = pre ++ k8Entry k :: post) (hPw : PowOn Lk post)
    (hrd : ∀ s : S, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (hOkS : ∀ q tlb v, Ok q → (π q.1).1 = some tlb → q.2 = some v → StaticOk tlb v.F)
    (hFront : FrontAtStandN Lk p φ Ok nU T b) (hVals : ValuesAtStand Lk p φ Ok nU T b) :
    RestAtStand Lk p φ Ok nU T b := by
  intro κ s m En ds y cols s' x z G hS hT hsh z₂ hFx hg hf hL tl₂ F hz hzF
  have hV := hVals κ s m En ds y cols s' x z G hS hT hsh z₂ hFx hg hf hL tl₂ F hz hzF
  obtain ⟨hOk, hφ, u9, b9, hq2, hb9, hGo⟩ := hFx
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 (show (Desc.K9.atS.get? s).map pubOf = some u9
    from hq2)
  have hFb : F = b9.F := Option.some.inj (hzF.symm.trans (Desc.K9.get_fork z₂ b9 hb9))
  obtain ⟨a', ha', -, hsz⟩ := hg
  obtain rfl : a' = b9 := Option.some.inj (ha'.symm.trans hb9)
  have e1 : z₂.tl?.map (blank u) = s.tl?.map (blank u) := by
    have h3 : π (φ z₂) = π (φ s) := congrArg π hφ
    rw [hrd, hrd] at h3
    exact congrArg (·.1) h3
  rw [hz] at e1
  cases hs : s.tl? with
  | none =>
    rw [hs] at e1
    exact nomatch e1
  | some tlS =>
    rw [hs] at e1
    have hbl : blank u tl₂ = blank u tlS := Option.some.inj e1
    obtain ⟨fin, f1⟩ := hFront κ s m En ds y cols s' x z G hS hOk tlS a hs ha
    have hSt : StaticOk (blank u tlS) (pubOf a).F :=
      hOkS (fixed9 φ s) (blank u tlS) (pubOf a) hOk (by
        show (π (φ s)).1 = _
        rw [hrd, hs]
        rfl) hq2
    rw [← hbl] at hSt
    have hw : tl₂.wants.map (·.1) = some tl₂.zzBlocks := hSt.blocks
    have hC : Fo.CoefOK tl₂ (pubOf a).F := LinkJoin.coefOK_blank hSt.coef
    have eB : tl₂.slotB = tlS.slotB := congrArg (·.slotB) hbl
    have eU : tl₂.nUF = tlS.nUF := congrArg (·.nUF) hbl
    have hns : F.ns = a.F.ns := by
      rw [hFb]
      exact hGo.1.ns
    have hsz' : F.LS.size = F.ns := by
      rw [hFb]
      exact hsz
    obtain ⟨F', tl, hF', ht', hz'⟩ := hL
    have hFF : F = F' := Option.some.inj (hzF.symm.trans (hf.trans hF'))
    have htl : tl₂ = { tl with lsTail := F'.LS.extract tl.slotA tl.slotB } :=
      Option.some.inj (hz.symm.trans hz')
    obtain ⟨hG, hx, hP⟩ := powered_at_stand hK hTh hsp hPw hS
    have hGF : G = F' := Option.some.inj (hG.symm.trans hF')
    have hPow : Powered tl₂ F.theta := by
      rw [htl, hFF, ← hGF]
      exact powered_laid ⟨hx, hP⟩ ht' _
    have hls : tl₂.lsTail = F.LS.extract tl₂.slotA tl₂.slotB := by
      rw [htl, hFF]
    exact k8Rest_ofN hls (by omega) hw hPow hC (by rw [eU]; exact f1) hV

/-- **So the kind's last run returns outside the kind's own share.** -/
theorem k8Behind_ok {k : Desc.K9.SegSort} {pW : K8.ParW} (hK : K8At Lk k pW)
    (hTh : ThetaAt Lk Lk.order) {pre post : List (ℕ × String)}
    (hsp : Lk.order = pre ++ k8Entry k :: post) (hPw : PowOn Lk post)
    (hrd : ∀ s : S, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (hOkS : ∀ q tlb v, Ok q → (π q.1).1 = some tlb → q.2 = some v → StaticOk tlb v.F)
    (hFront : FrontAtStandN Lk p φ Ok nU T b) (hVals : ValuesAtStand Lk p φ Ok nU T b) :
    K8Behind Lk p φ Ok nU T b (k8Share nU) :=
  k8Behind_of_rest Lk p φ Ok nU T b (restAtStand_ok hK hTh hsp hPw hrd hOkS hFront hVals)

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.hasRow_of_size
#print axioms ProofFile.Honest.K8.wants_first
#print axioms ProofFile.Honest.K8.piece_first
#print axioms ProofFile.Honest.K8.k8Rest_ofN
#print axioms ProofFile.Honest.K8.okStatic_of_core
#print axioms ProofFile.Honest.K8.restAtStand_ok
#print axioms ProofFile.Honest.K8.k8Behind_ok
