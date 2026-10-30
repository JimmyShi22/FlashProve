-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/LeftFront.lean: THE SMALLNESS TEST: THE NAMED PREMISE `LeftAtStand`
(Johnson/Desc/ProofFile/Honest/K8/RestJoin.lean) CUT IN TWO: ITS EIGHT FACTS ON THE PLAN AND THE
LEDGER, AND ITS CLAUSE ON THE LENGTHS OF THE VECTORS, ARE ASKED AT THE STATE IN FRONT OF THE
BATCHING (`FrontAtStand`): OF THAT STATE's DATA AND LEDGER, BEFORE ANY ELEMENT IS DRAWN; what stays
at the state at which the tests are called is the nine clauses and six conjuncts on what the runs
and the adding have laid (`ValuesAtStand`). The carrying is by what another house's sentence
`K8Behind` itself hands: the state goes on from what is fixed in front (the library's `Fx9`: the
arrays have their looks; the number of slots stays), and one coefficient stands for each slot
(`good9`). None of the library's goals.

  `hasRow_of_looks`   a ledger whose arrays have another's looks has its virtual rows
  `FrontLeft nU tl F`   `PlanLeft tl` (Johnson/Desc/K8/Honest/PlanLeft.lean: five facts) · the
                   digits' array has its two last virtual rows in F · the window ends inside F's
                   number of slots · the lengths of the vectors are the place's
  `ValuesLeft tl F`   what the lookup heard, the joining object and the wanted pieces are there ·
                   the first shapes · the pieces tile · the points · six conjuncts of the shapes ·
                   the planes' weights · the reads' shape and weights
  **`k8Left_of`**   pointwise: the four ties between (tl, F) and (tlS, Fs) · FrontLeft nU tlS Fs ·
                   ValuesLeft tl F ⊢ K8Left nU tl F
  **`leftAtStand_of`**   what is fixed in front holds the test's data but for the fourteen fields
                   that the runs write (one premise: the field `reads` of the other house's
                   `SealLaw`, to the letter) · FrontAtStand · ValuesAtStand ⊢ LeftAtStand
Limits. AN IMPLICATION STILL: `FrontAtStand` AND `ValuesAtStand` ARE PAID BY NOBODY: THE DEBT IS CUT
IN TWO, NOT PAID. Of the first, five facts hold at whatever the verifier's maker of the data returns
and pass the three later routines by which the plans lay the data (PlanLeft.lean): that the state in
front has a plan's data but for the fourteen fields is not shown. The premise on what is fixed is
the other house's to pay.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.RestJoin
import Johnson.Desc.K8.Honest.PlanLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open Fo (HasRow)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims (coefBody)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.First.K8.Honest (PlanLeft planLeft_of_blank)
open VerifiableInference.Desc.K9L (Pub9 fixed9 pubOf)
open ProofFile.Honest.K9 (BatStand LsLaid)

/-- A ledger whose arrays have another's looks has its virtual rows. -/
theorem hasRow_of_looks {F G : Fork} (h : G.trees.map LinkJoin.look = F.trees.map LinkJoin.look)
    {t e : Nat} (hr : HasRow F t e) : HasRow G t e := by
  obtain ⟨h1, h2⟩ := hr
  have hs : G.trees.size = F.trees.size := by simpa using congrArg Array.size h
  have ht : t < G.trees.size := hs ▸ h1
  have he : LinkJoin.look G.trees[t] = LinkJoin.look F.trees[t] := by
    have h3 := congrArg (fun A => A[t]?) h
    simpa [ht, h1] using h3
  have e1 : G.trees.getD t {} = G.trees[t] := by simp [Array.getD, ht]
  have e2 : F.trees.getD t {} = F.trees[t] := by simp [Array.getD, h1]
  refine ⟨ht, ?_⟩
  rw [e1]
  rw [e2] at h2
  have e3 : (G.trees[t]).rows.size = (F.trees[t]).rows.size := congrArg (·.2.2.2) he
  omega

/-- What is asked of the data and the ledger in front of the batching. -/
def FrontLeft (nU : Array Nat) (tl : HTailF2) (F : Fork) : Prop :=
  PlanLeft tl ∧ HasRow F tl.ix.ZZ tl.zzRowReads ∧ HasRow F tl.ix.ZZ tl.zzRowTies ∧
    tl.slotB ≤ F.ns ∧ (nU == tl.nUF) = true

/-- What stays at the data and the ledger at which the tests are called. -/
def ValuesLeft (tl : HTailF2) (F : Fork) : Prop :=
  ∃ (g : Forest.Heard) (jo : Nat) (nbW : Nat) (W : List Want),
    tl.heard = some g ∧ tl.joinObj9 = some jo ∧ tl.wants = some (nbW, W) ∧
    (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.size == 2 * nbW + 2 && tl.forestHeld g &&
      [0, 1].all (tl.callHeld g nbW)) = true ∧
    tl.piecesTile (coefBody tl g F) W = true ∧ tl.pointsHeld g = true ∧
    ((((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW + 1) {}).L.size ==
        2 * tl.mz &&
      tl.gamX.size == tl.NM && tl.gamV.size == tl.NM &&
      (List.range tl.NM).all (tl.tieShapeHeld (coefBody tl g F)) &&
      tl.shp.foldl (fun n s => n + s.m) 0 == tl.mz &&
      tl.planesShapeHeld (coefBody tl g F) g) = true ∧
    tl.planesWeightsHeld (coefBody tl g F) g jo = true ∧
    tl.readShapeHeld
      (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).L = true ∧
    tl.readWeightsHeld (coefBody tl g F)
      (((coefBody tl g F).trees.getD tl.ix.ZZ {}).rows.getD (2 * nbW) {}).L = true

/-- **Pointwise.** -/
theorem k8Left_of {nU : Array Nat} {u tl tlS : HTailF2} {F Fs : Fork}
    (hb : blank u tl = blank u tlS)
    (hl : F.trees.map LinkJoin.look = Fs.trees.map LinkJoin.look) (hns : F.ns = Fs.ns)
    (hsz : F.LS.size = F.ns) (hF : FrontLeft nU tlS Fs) (hV : ValuesLeft tl F) :
    K8Left nU tl F := by
  obtain ⟨hP, hR, hT, hin, r1⟩ := hF
  obtain ⟨b0, b1, b2, hB, hm⟩ := planLeft_of_blank hb hP
  have eB : tl.slotB = tlS.slotB := congrArg (·.slotB) hb
  have eI : tl.ix = tlS.ix := congrArg (·.ix) hb
  have eK : tl.blocks = tlS.blocks := congrArg (·.blocks) hb
  have eR : tl.zzRowReads = tlS.zzRowReads := by
    unfold HTailF2.zzRowReads HTailF2.zzBlocks
    rw [eK]
  have eT : tl.zzRowTies = tlS.zzRowTies := by
    unfold HTailF2.zzRowTies HTailF2.zzBlocks
    rw [eK]
  have eU : tl.nUF = tlS.nUF := congrArg (·.nUF) hb
  refine ⟨by omega, b0, b1, b2, ?_, ?_, hB, hm, by rw [eU]; exact r1, hV⟩
  · rw [eI, eR]
    exact hasRow_of_looks hl hR
  · rw [eI, eT]
    exact hasRow_of_looks hl hT

section
variable {α : Type} (Lk : Link S Claim) (p : Desc.K9.Where) (φ : S → α)
  (Ok : α × Option Pub9 → Prop) (nU : Array ℕ)
  {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Claim V W X Pb) (b : ℕ)

/-- **The first named premise**: at the state in front of the batching. -/
def FrontAtStand : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    Ok (fixed9 φ s) → ∀ tlS a, s.tl? = some tlS → Desc.K9.atS.get? s = some a →
      FrontLeft nU tlS a.F

/-- **The second**: at the state at which the tests are called. -/
def ValuesAtStand : Prop :=
  ∀ κ s m En ds y cols s' x z G, BatStand Lk p T b κ s m En ds y cols s' x z G →
    Lk.tests s' = .ok () → k8Share nU s' = none → ∀ z₂, K9L.Fx9 φ Ok (fixed9 φ s) z₂ →
      K9L.good9 z₂ → z₂.fork? = s'.fork? → LsLaid s' z₂ →
        ∀ tl F, z₂.tl? = some tl → z₂.fork? = some F → ValuesLeft tl F

variable {Lk p φ Ok nU T b} {u : HTailF2} {π : α → Option HTailF2 × Option (Array HFun)}

/-- **The cut.** -/
theorem leftAtStand_of (hrd : ∀ s : S, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (hFront : FrontAtStand Lk p φ Ok nU T b) (hVals : ValuesAtStand Lk p φ Ok nU T b) :
    LeftAtStand Lk p φ Ok nU T b := by
  intro κ s m En ds y cols s' x z G hS hT hsh z₂ hFx hg hf hL tl F hz hzF
  have hV := hVals κ s m En ds y cols s' x z G hS hT hsh z₂ hFx hg hf hL tl F hz hzF
  obtain ⟨hOk, hφ, u9, b9, hq2, hb9, hGo⟩ := hFx
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 (show (Desc.K9.atS.get? s).map pubOf = some u9
    from hq2)
  obtain rfl : F = b9.F := Option.some.inj (hzF.symm.trans (Desc.K9.get_fork z₂ b9 hb9))
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
    exact k8Left_of (Option.some.inj e1) hGo.2.2.1 hGo.1.ns hsz
      (hFront κ s m En ds y cols s' x z G hS hOk tlS a hs ha) hV

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.hasRow_of_looks
#print axioms ProofFile.Honest.K8.k8Left_of
#print axioms ProofFile.Honest.K8.leftAtStand_of
