-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontClaims.lean: the test claimsB on the open rows at the
state on entry to a proximity test, at the first chain's test and at the last chain's own test.

  claimsB_of_passes     the sentence of WFrontOpenRows.lean gives claimsB at a group not under test
  group_of_frontFive    the public test on the shape says that the group is there and not under test
  claimsB_at_finish     the first chain's test, at border 354, where that public test says yes
  passes_takeOver, passes_second   Omega's taking over and the block "K14, second part" keep the sentence
  claimsB_at_own        the last chain's own test
  openOrd_at_start      the start of the last chain keeps the open rows in order

Limits.
- At the first chain's test the group's presence and its mark come from frontFiveB, which stands as a
  premise.
- That any row lies open is not said.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontOpenRows
import Johnson.Desc.ProofFile.Honest.K12.FrontAtShape
import Johnson.Desc.Third.Law.Keeps
import Johnson.Desc.Third.Law.AtDoor
import Johnson.Desc.Third.Law.Start
import Johnson.Desc.K12.Seat.Own
import Johnson.Desc.K12.SeatLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.Ground (ok rowL)
open VerifiableInference.Desc.K12 (T12 P12 enterFinish)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut takeOver batchLinearConstraintsSecondPart start₃E)
open VerifiableInference.Desc.Third.Law (takeOver_inv k14Second_inv start₃E_st)
open ProofFile.Honest.Sh (claimsB TestSh testSh)
open ProofFile.Honest.K12 (frontFiveB)
open Desc.Plain (DState)

/-- At a group that is not under test the sentence gives the front's test on the open rows. -/
theorem claimsB_of_passes {t : T12} {G : Group} (h : OpenRowsPass t.st)
    (hG : t.st.groups[t.g]? = some G) (hr : G.inRun = false) : claimsB t = true := by
  unfold claimsB
  rw [hG]
  simp only [Option.any_some, List.all_eq_true]
  exact h.2 t.g G hG hr

/-- The public test on the shape says that the group is there and not under test. -/
theorem group_of_frontFive {p : P12} {K : Codes} {t : T12}
    (h : frontFiveB p K (testSh t) = true) :
    ∃ G : Group, t.st.groups[t.g]? = some G ∧ G.inRun = false := by
  unfold frontFiveB at h
  simp only [Bool.and_eq_true] at h
  have hd := h.1.1.1.1.2
  unfold ProofFile.Honest.Sh.doorB ProofFile.Honest.Sh.frontOwesB at hd
  simp only [Bool.and_eq_true] at hd
  have h2 : ok (ProofFile.Honest.Sh.frontLS (VerifiableInference.Desc.Ground.Sh.coreSh
            ⟨t.st, t.book, t.roots⟩) t.g t.mask) = true := hd.1.2.1.2
  rw [ProofFile.Honest.Sh.frontLS_eq] at h2
  simp only [ok, VerifiableInference.Desc.K12.frontL, List.all_cons, Bool.and_eq_true] at h2
  obtain ⟨c1, c2, -⟩ := h2
  obtain ⟨G, hG⟩ := Option.isSome_iff_exists.mp c1
  refine ⟨G, hG, ?_⟩
  rw [hG] at c2
  simpa [VerifiableInference.Desc.Ground.on] using c2

/-- Omega is taken over: the sentence stays. -/
theorem passes_takeOver (S : Params.LinShape) (own : ℕ) (o : SharedOut)
    (d : DState VerifiableInference.Desc.Third.Loc₃)
    (r : ℕ × DState VerifiableInference.Desc.Third.Loc₃) (h : takeOver S own o d = .ok r) :
    PassStays d.st r.2.st := by
  obtain ⟨_, _, _, a, d₁, _, _, _, ha, _, h1, h2⟩ := takeOver_inv S own o d r h
  exact groundKeeps_openRows.trans
    (groundKeeps_openRows.trans (groundKeeps_openRows.adopt _ _ _ _ _ ha)
      (groundKeeps_openRows.elsewhere _ _ _ _ _ h1))
    (groundKeeps_openRows.join _ _ _ _ _ h2)

/-- **The block "K14, second part" keeps the sentence, and leaves the own group there and not under
test.** -/
theorem passes_second {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s')
    (hA : OpenRowsPass s.st) :
    OpenRowsPass s'.st ∧ ∃ G : Group, s'.st.groups[s.loc.own]? = some G ∧ G.inRun = false := by
  obtain ⟨x, a, dot, b, _, ha, _, hb, e⟩ := k14Second_inv p s s' rs gs h
  subst e
  refine ⟨groundKeeps_openRows.addRow _ _ _ _ hb (passes_takeOver _ _ _ _ _ ha hA), ?_⟩
  unfold VerifiableInference.Desc.Ground.addRowP at hb
  split at hb
  · rename_i hok
    obtain rfl := Option.some.inj hb
    obtain ⟨G, hG, C⟩ := VerifiableInference.Desc.K9L.rowL_clauses _ _ _ hok
    refine ⟨{ G with rows := G.rows.push dot }, ?_, C.noTest⟩
    show (a.2.st.groups.modify s.loc.own fun G => { G with rows := G.rows.push dot })[s.loc.own]? = _
    rw [Array.getElem?_modify, if_pos rfl, hG]
    rfl
  · cases hb

/-- **The test on the open rows at the last chain's own test.** -/
theorem claimsB_at_own {Cl : Type} (p : P₁₄) {s₀ s : S₃} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} {t : T12}
    (h₁ : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ rs gs = .ok s) (h₂ : enterOwn s = .ok t)
    (hA : OpenRowsPass s₀.st) : claimsB t = true := by
  obtain ⟨hP, G, hG, hr⟩ := passes_second p s₀ s rs gs h₁ hA
  obtain ⟨_, _, _, _, _, _, _, _, e⟩ := k14Second_inv p s₀ s rs gs h₁
  have et : t = { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing
                  mask := s.loc.mask } := (Except.ok.inj h₂).symm
  have hl : s.loc.own = s₀.loc.own := by rw [e]
  subst et
  exact claimsB_of_passes hP (by rw [hl]; exact hG) hr

/-- The last chain's start lays the first chain's last statement: so what holds there holds at the
start. -/
theorem openOrd_at_start {codes : Codes} {S : Params.LinShape} {st₁ : Statement} {book₁ : TreeBook}
    {roots₁ w₁ own₁ : ℕ} {mask₁ : Option ℕ} {pile₁ : List TensorRow} {o : SharedOut} {s₀ : S₃}
    (h : start₃E codes S st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀)
    (hO : Johnson.AtFull.Shape.OpenOrd st₁) : Johnson.AtFull.Shape.OpenOrd s₀.st := by
  rw [start₃E_st _ _ _ _ _ _ _ _ _ _ _ h]
  exact hO

section Head
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The test on the open rows at the first chain's test**, where the public test on the shape says
yes. -/
theorem claimsB_at_finish (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {s : S}
    (hr : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 354 (pI, s)) {T : T12}
    (he : enterFinish s = .ok T) {p : P12} {K : Codes} (h5 : frontFiveB p K (testSh T) = true) :
    claimsB T = true := by
  obtain ⟨G, hG, hi⟩ := group_of_frontFive h5
  obtain ⟨-, rs, cols, hf⟩ := (reach_raw hr).fold
  have hP : OpenRowsPass s.st := openRowsPass_reached h 354 0 pI rs cols _ hf
  obtain ⟨o, -, -, -, rfl⟩ := VerifiableInference.Desc.K12.Seat.enterFinish_ok s T he
  exact claimsB_of_passes hP hG hi

end Head

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.claimsB_of_passes
#print axioms ProofFile.Honest.K12.AtFile.group_of_frontFive
#print axioms ProofFile.Honest.K12.AtFile.passes_second
#print axioms ProofFile.Honest.K12.AtFile.claimsB_at_own
#print axioms ProofFile.Honest.K12.AtFile.openOrd_at_start
#print axioms ProofFile.Honest.K12.AtFile.claimsB_at_finish
