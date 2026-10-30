-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WLine.lean: the clauses `lines` and `front` of `StandAtW` by the narrow
road: no whole shape of the first chain: `sameCore_at_seat` (WFrontAtSeat.lean) ties the record on entry to the
closed shape `narrowW` at what `linesB` reads; the taken sources' yes at the fold pays its one premise.

  `elems_of_fits`, `okDrawn_at_stand`   at a stand every round seen has canonical elements
  `lines_front_narrow`   `linesB` and `FrontAsksD` at the state on entry, at a stand where the field stands:
                   no other premise on the run

By what. `sameCore_at_seat`; `lines_of_narrow` (CoreNarrow.lean); `rows_at_file` (WFrontEnd.lean).

Limits.
- hm, ht: the job's public numbers: `mems_lit` (CoreMems.lean) at the filling.
- NOT IN FRONT OF A LAW OVER COINS.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WEnds
import Johnson.Desc.ProofFile.Honest.K12.AtFile.CoreNarrow
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontAtSeat
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open OnBytes
open OnBytes.Slice (PlainRow)
open VerifiableInference.Desc (Chain foldBlocks)
open VerifiableInference.Desc.First.K2 (OkDrawn)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃ SharedOut start₃E firstOfS sharedOfEnd)
open VerifiableInference.Desc.Last (fillAt)
open H2K.Member (piWFull codesFull)
open ProofFile.Honest.Sh (testSh)
open ProofFile.Honest.K12 (frontFiveB frontAsksD_of_five FrontAsksD)
open ProofFile.Honest.K12.AtProof (fourOf treesW)
open ProofFile.Honest.K12.Light (ManyJob)
open ProofFile.Honest.LastThread (lettersLast)
open P5J (F0T TS AtMgA)

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **What `drawsFit` says of the drawn elements: they are canonical.** -/
theorem elems_of_fits : ∀ (ds : List Fmt.DeclaredRound) (l : List Fmt.Drawn), drawsFit ds l = true →
    ∀ R ∈ l, ∀ x ∈ R.elems, (x.1 < VerifiableInference.Desc.fieldPrimeWord ∧
      x.2.1 < VerifiableInference.Desc.fieldPrimeWord) ∧ x.2.2 < VerifiableInference.Desc.fieldPrimeWord
  | [], [], _, _, hR, _, _ => by cases hR
  | [], _ :: _, h, _, _, _, _ => by simp [drawsFit] at h
  | _ :: _, [], h, _, _, _, _ => by simp [drawsFit] at h
  | d :: ds, R₀ :: Rs, h, R, hR, x, hx => by
    simp only [drawsFit, Bool.and_eq_true] at h
    rcases List.mem_cons.1 hR with rfl | hR'
    · have hd := h.1
      unfold drawFit at hd
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hd
      exact hd.1.2 x hx
    · exact elems_of_fits ds Rs h.2 R hR' x hx

/-- **At a stand every round seen has canonical elements.** -/
theorem okDrawn_at_stand (T : Thread Bk S Cl V W X Pb) {b : ℕ} {k : Coins Bk} {s : S} {m : Mid W X}
    {E : Env} (u : Thr T b k s m E) : ∀ y ∈ m.seen, OkDrawn y := by
  obtain ⟨-, hfit, -, -, ⟨hmap, -⟩, -, -⟩ := u
  intro y hy e he
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
  have hR : y.drawn ∈ m.st.heard := by
    rw [← hmap]
    exact List.mem_map_of_mem hy
  have hg := elems_of_fits _ _ hfit y.drawn hR x hx
  simp only [OnBytes.okE, OnBytes.okF, OnBytes.E.ofTriple, Bool.and_eq_true, decide_eq_true_eq]
  exact hg

end

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

/-- **The clauses `lines` and `front` at a stand, by the narrow road.** -/
theorem lines_front_narrow (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (A : ManyJob (Local W₀ Rc ProofFile.Inst Tr) X) (he : A.p.early = true)
    (hp : A.p = (fourOf Np).W) (hm : A.mems.map (·.shape) = memsW)
    (ht : A.trees = treesW piWFull) {k : Coins Bk} {st : S₃}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hF : FieldAtW (F0T OnBytes.secondHashFunction Zp Np cF) (lettersLast Zp Np cF H N Mg ML PL order taken ends
                  wit table fixed item n₁ n₂ Vd Rd Kp w).thread Said 2)
    (u : ThrS (lettersLast Zp Np cF H N Mg ML PL order taken ends wit table fixed item n₁ n₂ Vd Rd Kp
      w).thread Said 2 k st m E)
    (hE : enterOwn st = .ok (A.rec₀ m.st.input (frontOf m))) :
    linesB A codesFull 3 (testSh (A.rec₀ m.st.input (frontOf m))) = true ∧
      ∃ Dp, FrontAsksD A.toRun.toTest m.st.input (frontOf m) codesFull Dp := by
  obtain ⟨base, cols, e₁, e₂, hEn, -, -, hs⟩ := hF k st m E u
  have u' := u.1
  obtain ⟨⟨-, -, -, -, hM, -, -⟩, -⟩ := u
  obtain ⟨s₀, rs, gs, hbeg, h₁, hTied⟩ := made_at_W Zp Np cF H N Mg ML PL order taken ends wit table
    fixed item n₁ n₂ Vd Rd Kp w hM
  have hst := hs s₀ hbeg
  obtain ⟨r₁, r₂, rest, c₁, c₂, hseen, -, -, -, -, -, f₁, f₂⟩ := hEn
  have hv : ∀ y ∈ r₁, OkDrawn y := fun y hy => okDrawn_at_stand _ u' y (by
    rw [hseen]
    exact List.mem_append_left _ hy)
  obtain ⟨hc, hmask, hpass⟩ := sameCore_at_seat h _ f₁ f₂ hst h₁ hE (ToldDesc.ownAt Np) rfl hTied
  have hl := lines_of_narrow h.toAtMg A hp hm ht hc hmask hpass
  have h5 : frontFiveB A.p codesFull (testSh (A.rec₀ m.st.input (frontOf m))) = true := by
    have k' := hl
    unfold linesB at k'
    simp only [Bool.and_eq_true] at k'
    exact k'.1.1
  obtain ⟨ht₁, hd₁, hc₁⟩ := rows_at_file h _ hv f₁ f₂ hst h₁ hE
  exact ⟨hl, frontAsksD_of_five A.toRun.toTest m.st.input (frontOf m) codesFull he h5 ht₁ hd₁ hc₁⟩

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.elems_of_fits
#print axioms ProofFile.Honest.K12.AtFile.okDrawn_at_stand
#print axioms ProofFile.Honest.K12.AtFile.lines_front_narrow
