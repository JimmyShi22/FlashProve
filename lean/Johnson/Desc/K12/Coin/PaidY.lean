-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/PaidY.lean: THE LAWS OF Paid.lean WITH TWO CLAUSES FEWER IN THE PROMISE: what
a yes of the piece holds need not be promised. Definitions, statements and proofs.

`PayK` (Johnson/Desc/K12/Law/Tuple/BatValsPay.lean) asks, among seven clauses, that the layout's k
and h be the first stage's. A yes of the piece holds that (`yes_fits`, YesHolds.lean, with "h ≤ k"
of the first stage, `yes_hk`), and a promise is owed only at statements from which the piece ever
puts out (`leads_of_yes`, LawY.lean).

  `yes_hk`: where the piece puts out: the first stage's h is at most its k (a clause of `pubOk`,
    through the chain's own stages).
  `PayY`: `PayK` without these two clauses. `payK_of_yes`: with a yes it gives `PayK`.
  `k12_lawPaidY`, `k12_lawPaidYO`: the two arms at `PayY`.
Limits: those of Paid.lean. NO SOUNDNESS IS CLAIMED. `PayY` is a premise; no member of it is shown.

-/
import Johnson.Desc.K12.Coin.Paid
import Johnson.Desc.K12.Coin.YesHolds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker OnBytes.Means
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.JointK
open H2K.Pub (sgOf pub_of_ok)
open H2K.First (Plain)
open H2K.Pin (NTuple PayK)

theorem yes_hk {W : Type} (F : Frame) (π : P12) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (base : ℕ) (dB : RDT) (dt : List RDT)
    (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (x : T12 × F.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) (dB :: dt))) (b : T12 × F.E.Str)
    (hb : (pieceT F W π base dB dt e₀ εt).ior.red.out x τ = some b) (a : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (hs : π.nums.stages = a :: rest) : a.h ≤ a.k := by
  obtain ⟨_, k, hst, _⟩ := yes_step (pieceT F W π base dB dt e₀ εt) rfl x τ b hb
  have hst' : (proximityTestKind guardedProximityTestParts π : Blk').step F.ft x.1 (rvT (ckP .two) (dB :: dt) τ)
      (sView (ckP .two) ⟨F.a, base, F.all, dB :: dt, F.key, F.all⟩ x.2 τ).opened = .ok (b.1, k) :=
    hst
  obtain ⟨_, _, hdec⟩ := Prox.step_ok F.ft _ x.1 b.1 _ _ k hst'
  obtain ⟨_, hpub, _⟩ := k12_guards π he x.1 b.1 _ _ hp hdec
  obtain ⟨a', rest', _, _, c, hs', _, _, _, hstg, _⟩ :=
    pub_of_ok (.at (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) fun _ => 0) π
      x.1.st.codes hpub
  obtain ⟨rfl, rfl⟩ := List.cons.inj (hs'.symm.trans hs)
  obtain ⟨l', hl'⟩ := stagesOf_ne c
  have h1 : (sgOf a').st = a' := (List.cons.inj ((hl'.symm.trans hstg).trans hs)).1
  have h2 : a'.h + (a'.k - a'.h) = a'.k := congrArg (·.k) h1
  omega

/-- `PayK` without the two clauses that a yes of the piece holds. -/
def PayY (π : P12) (rad : Sg → ℕ) (v₀ : ℕ) (t : T12) : Prop :=
  ∀ (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group) (Ly : GroupLayout) (D : Plain),
    Fixes π t a rest G0 Ly D →
    (sgOf a).StageJ (rad (sgOf a)) ∧
    combineAt (begun t.st t.g G0) t.g ⟨Ly, runRows t.st G0⟩ = true ∧
    2 ^ Ly.logEll = (sgOf a).C.l ∧ 2 ^ Ly.logEllZk = (sgOf a).Z.l ∧
    (sgOf a).lstJ (rad (sgOf a)) * ((runRows t.st G0).size - 1) ≤ v₀

theorem payK_of_yes {W : Type} (F : Frame) (π : P12) (he : π.early = true)
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true) (rad : Sg → ℕ) (v₀ : ℕ) (base : ℕ)
    (dB : RDT) (dt : List RDT) (e₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (x : T12 × F.E.Str)
    (hy : ∃ τ b, (pieceT F W π base dB dt e₀ εt).ior.red.out x τ = some b)
    (h : PayY π rad v₀ x.1) : PayK π rad v₀ x.1 := by
  intro a rest G0 Ly D hf
  obtain ⟨τ, b, hb⟩ := hy
  obtain ⟨p1, p2, p3, p4, p5⟩ := h a rest G0 Ly D hf
  obtain ⟨f1, f2⟩ := yes_fits F π he hp base dB dt e₀ εt x τ b hb a rest G0 Ly D hf
  have hk := yes_hk F π he hp base dB dt e₀ εt x τ b hb a rest hf.1
  refine ⟨p1, p2, ?_, f2, p3, p4, p5⟩
  rw [f1]
  show a.k = a.h + (a.k - a.h)
  omega

/-- **The first arm, at the shorter promise.** -/
theorem k12_lawPaidY (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (v₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt)
    (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0]) (hlog : dB.entry.logN ≤ 64) :
    (pieceT F W π base dB dt (v₀ * (bsRound .two dB.entry dB.kind).w) εt).ior.red.Leads
      (fun x => FirstOpens π num no base x.1 ∧ PayY π rad v₀ x.1)
      (fun x _ => QN π (NTuple F π no rad rd) x)
      (pieceT F W π base dB dt (v₀ * (bsRound .two dB.entry dB.kind).w) εt).err :=
  Reduction.Leads.conseq
    (leads_of_yes (k12_lawPaid F W π num no L mC mS mW rad rd base dB dt v₀ εt hA h1 hlog))
    (fun x hx hy => ⟨hx.1, payK_of_yes F π hA.early hA.planOk rad v₀ base dB dt _ εt x hy hx.2⟩)
    (fun _ _ _ _ _ h => h)

/-- **The second arm, at the shorter promise.** -/
theorem k12_lawPaidYO (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (v₀ : ℕ) (εt : Err (uLT (ckP .two) dt))
    (hA : AtPlaceOwn F π num L mC mS mW rad base dB dt εt)
    (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0]) (hlog : dB.entry.logN ≤ 64) :
    (pieceT F W π base dB dt (v₀ * (bsRound .two dB.entry dB.kind).w) εt).ior.red.Leads
      (fun x => FirstOpensOwn π num no base x.1 ∧ PayY π rad v₀ x.1)
      (fun x _ => QN π (NTuple F π no rad rd) x)
      (pieceT F W π base dB dt (v₀ * (bsRound .two dB.entry dB.kind).w) εt).err :=
  Reduction.Leads.conseq
    (leads_of_yes (k12_lawPaidO F W π num no L mC mS mW rad rd base dB dt v₀ εt hA h1 hlog))
    (fun x hx hy => ⟨hx.1, payK_of_yes F π hA.early hA.planOk rad v₀ base dB dt _ εt x hy hx.2⟩)
    (fun _ _ _ _ _ h => h)

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.yes_hk
#print axioms VerifiableInference.Desc.K12.Coin.payK_of_yes
#print axioms VerifiableInference.Desc.K12.Coin.k12_lawPaidY
#print axioms VerifiableInference.Desc.K12.Coin.k12_lawPaidYO
