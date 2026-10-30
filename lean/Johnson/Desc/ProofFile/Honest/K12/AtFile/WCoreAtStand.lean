-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WCoreAtStand.lean: at a stand of the last thread at number 2 the
record agrees with the closed shape, at the record itself, not at the test's state on entry.

  core_at_stand    sameCore_at_seat at a stand, as lines_front_narrow (WLine.lean) reaches it

Limits.
- hF, hE: the field and the way in, at the stand.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WLine

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open OnBytes
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃)
open ProofFile.Honest.K12.Light (ManyJob)
open ProofFile.Honest.LastThread (lettersLast)
open P5J (F0T AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {x : VerifiableInference.Desc.First.Look.Place}
  (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl) {Bk : ProverCoinCounts}
  {W₀ Rc Tr X₀ X Wt : Type} (H : Prover W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X)
  (N : VerifiableInference.Desc.Shared.NumbersS)
  (Mg : Local W₀ Rc ProofFile.Inst Tr →
    VerifiableInference.Desc.Shared.MeaningS Desc.K14.St (ProofFile.InstPub × P5J.TS) Wt)
  (ML : VerifiableInference.Desc.Last.MeaningL S₃ Wt)
  (PL : VerifiableInference.Desc.Last.PromMeaningL Desc.K14.St S₃ (ProofFile.InstPub × P5J.TS))
  (order : S₃ → Prop) (taken : List Fmt.TreeSource)
  (ends : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn →
    (ProofFile.InstPub × P5J.TS) × Desc.K14.St)
  (wit : Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn → Wt)
  (table : Fmt.TreeSource → Coins Bk → Local W₀ Rc ProofFile.Inst Tr → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table)
  (fixed : Fmt.TreeSource → ℕ) (item n₁ n₂ : ℕ) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : ℕ → Local W₀ Rc ProofFile.Inst Tr → S₃ → Prop)
  (Kp : VerifiableInference.Desc.Place → S₃ → S₃ → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **At a stand the record agrees with the closed shape.** -/
theorem core_at_stand (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (A : ManyJob (Local W₀ Rc ProofFile.Inst Tr) X) {k : Coins Bk} {st : S₃}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hF : FieldAtW (F0T OnBytes.secondHashFunction Zp Np cF) (lettersLast Zp Np cF H N Mg ML PL order taken ends
                  wit table fixed item n₁ n₂ Vd Rd Kp w).thread Said 2)
    (u : ThrS (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp
      w).thread Said 2 k st m E)
    (hE : enterOwn st = .ok (A.rec₀ m.st.input (frontOf m))) :
    SameCore [4, 197, 198, 199] st.loc.own 0
      (VerifiableInference.Desc.Ground.Sh.coreSh ⟨st.st, st.book, st.roots⟩) narrowW := by
  obtain ⟨base, cols, e₁, e₂, hEn, -, -, hs⟩ := hF k st m E u
  obtain ⟨⟨-, -, -, -, hM, -, -⟩, -⟩ := u
  obtain ⟨s₀, rs, gs, hbeg, h₁, hTied⟩ := made_at_W Zp Np cF H N Mg ML PL order taken ends wit table
    fixed item n₁ n₂ Vd Rd Kp w hM
  have hst := hs s₀ hbeg
  obtain ⟨r₁, r₂, rest, c₁, c₂, hseen, -, -, -, -, -, f₁, f₂⟩ := hEn
  obtain ⟨hc, -, -⟩ := sameCore_at_seat h _ f₁ f₂ hst h₁ hE (ToldDesc.ownAt Np) rfl hTied
  have e : A.rec₀ m.st.input (frontOf m) =
      { st := st.st, book := st.book, roots := st.roots, g := st.loc.own
        pass := .nothing, mask := st.loc.mask } := (Except.ok.inj hE).symm
  rw [e] at hc
  exact hc

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.core_at_stand
