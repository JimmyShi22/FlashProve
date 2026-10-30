--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/K6SilentBack.lean: THE WAY BACK OF Law/K6Silent.lean's k6Out_of_items: FROM
K6Out AT ONE STATE OF THE VERIFIER AND GIVEN COMPONENTS TO THE TABLE's SENTENCE formsTQ AT THE
OUTPUT HEAD's FOUR RUNS ("norm" · "policy" · "logits" · "join") AND TO WeightAt. STATED AND PROVED:
A MIRROR OF THAT THEOREM's PROOF, over Law/K6ClaimsBack.lean: no new mathematics.
WHAT IT CANNOT GIVE, FIRST. · The items "planes" and "small", which the table's row opens at the
same border: K6Out does not read them · A WITNESS: rdW and d are letters, tied by hmask and hA:
that some witness has the honest run's components is not said · that its premises on the state hold
at an honest state · an example. Nothing on soundness or on hiding.
THE ONE PREMISE MORE THAN ON THE WAY THERE. formsTQ begins "there are a part a and an answer R of
the reader; its late slots are admitted; each of its forms is admitted": K6Out does not say that.
It is the public test with code K9.formsInT (Johnson/Desc/First/Batch/FormsIn.lean): hIn.
  test_says         what K9.formsInT's yes says, where the open segment's part is a.
  **forms_of_k6Out**  under k6Out_of_items' own premises on the state (K6States · hRd · hok · hT ·
                    hmask · hA · hbare) and hIn: K6Out W s d gives WeightAt W s d.1.toCells d.2 and
                    formsTQ Rd St own b name s rdW at the four names. With k6Out_of_items: an iff
                    under these premises.

-/
import Johnson.Desc.Kinds.Law.K6Silent
import Johnson.Desc.Kinds.Law.K6ClaimsBack

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff Reading World)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Block Claim Link)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K9 (Readers readerOf lateOf segAt? RunOf)
open VerifiableInference.Desc.Sound (Stated formsTQ worldOwn dataQ slotW)
open Norm (lt ls d lPd T S2)

/-- What the public test's yes says. -/
theorem test_says (Rd : Readers) (own : List (Nat × Nat)) (b : Nat) (name : String) (s : S)
    (a : K9.Part) (ha : segAt? s = some a) (h : K9.formsInT Rd own b name s = true) :
    ∃ R, Rd.forms b name s = some R ∧ K9.lateOk R.late a = true ∧
      ∀ f ∈ R.forms, K9.affInT own (K9.mergeOf s) R.late a f = true := by
  unfold K9.formsInT at h
  rw [ha] at h
  cases hR : Rd.forms b name s with
  | none =>
    rw [hR] at h
    exact absurd (show false = true from h) Bool.false_ne_true
  | some R =>
    rw [hR] at h
    have h' : (K9.lateOk R.late a &&
        R.forms.all fun f => K9.affInT own (K9.mergeOf s) R.late a f) = true := h
    obtain ⟨h1, h2⟩ := Eq.mp (Bool.and_eq_true _ _) h'
    exact ⟨R, rfl, h1, fun f hf => List.all_eq_true.1 h2 f hf⟩

/-- **FROM K6Out, AT ONE STATE, TO formsTQ AT THE HEAD's FOUR RUNS AND WeightAt.** The letters are
k6Out_of_items'. -/
theorem forms_of_k6Out (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH) (l piece b : Nat)
    (states : Nat → List (RunOf S))
    (K : K6States W.hS (readsOf W) (parOf W.hS (workOf W)) l piece states b)
    (Rd : Readers) (St : Stated) (own : List (Nat × Nat)) (s : S) (rdW : Nat × Nat → Sound.MsgQ)
    (d : Pinned) (a : K9.Part) (ha : segAt? s = some a)
    (hRd : ∀ name, K6Name name → Rd.forms b name s = k6Silent P states b name s)
    (hok : (parOf W.hS (workOf W)).ok = true)
    (hT : K6HeardAt W.hS (readsOf W) (parOf W.hS (workOf W)) s)
    (hmask : ∀ j, j < a.F.mf.size → (St.at1 s (dataQ own a rdW)).mask j = rd (d.2 j))
    (hA : ∀ e v, withTables P s = some e →
      lettersAt (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) e = .ok v →
      (letI := v.1
       letI := v.2.1
       EntriesAlike (worldOwn a [] (St.at1 s (dataQ own a rdW)))
         (worldE ((seatAt W.hS (readsOf W)).ledger s) d.2 noEnt)
         v.2.2.final (normReadsAtCells d.1) v.2.2.head (readsAt d.1.toCells)))
    (hbare : ∀ gk, s.lookHeard? = some gk → gk.cEnd.ents = #[])
    (hIn : ∀ name, K6Name name → K9.formsInT Rd own b name s = true)
    (hO : K6Out W s d) :
    WeightAt W s d.1.toCells d.2 ∧ ∀ name, K6Name name → formsTQ Rd St own b name s rdW := by
  obtain ⟨g, H, F0, G, rs, hg, hH, hW0, hh, hLt⟩ := hT
  have hB := heardBare_of_hear hW0 hh
  -- what a test says
  have test : ∀ name, K6Name name → ∃ e R, withTables P s = some e ∧
      readerOf states b name e = some R ∧ Rd.forms b name s = some R ∧
      K9.lateOk R.late a = true ∧
      ∀ f ∈ R.forms, K9.affInT own (K9.mergeOf s) R.late a f = true := by
    intro name hnm
    obtain ⟨R, hR, h1, h2⟩ := test_says Rd own b name s a ha (hIn name hnm)
    have hR' := hR
    rw [hRd name hnm] at hR'
    obtain ⟨e, he, hRe⟩ := Option.bind_eq_some_iff.mp hR'
    exact ⟨e, R, he, hRe, hR, h1, h2⟩
  obtain ⟨e, Rn, he, hRn, qn, on, an⟩ := test "norm" (Or.inl rfl)
  obtain ⟨e2, Rp, he2, hRp, qp, op, ap⟩ := test "policy" (Or.inr (Or.inl rfl))
  obtain rfl : e = e2 := Option.some.inj (he.symm.trans he2)
  obtain ⟨e3, Rl, he3, hRl, ql, ol, al⟩ := test "logits" (Or.inr (Or.inr (Or.inl rfl)))
  obtain rfl : e = e3 := Option.some.inj (he.symm.trans he3)
  obtain ⟨e4, Rj, he4, hRj, qj, oj, aj⟩ := test "join" (Or.inr (Or.inr (Or.inr rfl)))
  obtain rfl : e = e4 := Option.some.inj (he.symm.trans he4)
  obtain ⟨v, fsn, hv, ln, en, tn⟩ := reader_own K "norm" (Or.inl rfl) e Rn hRn
  obtain ⟨v2, fsp, hv2, lp, ep, tp⟩ := reader_own K "policy" (Or.inr (Or.inl rfl)) e Rp hRp
  obtain rfl : v = v2 := Except.ok.inj (hv.symm.trans hv2)
  obtain ⟨v3, fsl, hv3, ll, el, tl⟩ := reader_own K "logits" (Or.inr (Or.inr rfl)) e Rl hRl
  obtain rfl : v = v3 := Except.ok.inj (hv.symm.trans hv3)
  obtain ⟨v4, gk, hv4, hgke, ej, tj⟩ := reader_join K e Rj hRj
  obtain rfl : v = v4 := Except.ok.inj (hv.symm.trans hv4)
  -- the letters at e are the state's own
  have hse := front_withTables he
  obtain ⟨H', x, k1, k2, _, k4⟩ := lettersAt_ok W.hS (readsOf W) (parOf W.hS (workOf W)) hv
  have e1 : (Except.ok v.1 : Except String Given) = .ok g := by
    rw [← k1, given_front W.hS (readsOf W) _ hse, hg]
  obtain rfl := Except.ok.inj e1
  have e2 := heard_front W.hS (readsOf W) hse H hH
  rw [k2] at e2
  obtain rfl := Option.some.inj e2
  have eH : (v.2.1.norm, v.2.1.final, v.2.1.head) = H' := by rw [k4]
  have hgk : s.lookHeard? = some gk := by rw [← (fork_withTables he).2]; exact hgke
  -- the part's ledger is the state's
  have hF : (seatAt W.hS (readsOf W)).ledger s = a.F := by
    show s.fork?.getD {} = a.F
    rw [seg_fork ha]
    rfl
  have hslot : ∀ j, (worldOwn a [] (St.at1 s (dataQ own a rdW))).slot j =
      (worldE ((seatAt W.hS (readsOf W)).ledger s) d.2 noEnt).slot j := by
    intro j
    rw [worldE_eq, hF]
    show slotW a.F [] _ j = _
    rw [Sound.slotW_ledger a.F [] _ j rfl]
    show _ =
      Reading.gl.val (a.F.vp.getD j zeroE) - Reading.gl.val (a.F.mf.getD j zeroE) * rd (d.2 j)
    by_cases hj : j < a.F.mf.size
    · rw [hmask j hj]
    · have e0 : a.F.mf.getD j zeroE = zeroE := by
        simp [Array.getD, hj]
      rw [e0, Reading.gl.zero, zero_mul, zero_mul]
  obtain ⟨hd, hJ⟩ := sizes_of_plan _ _ e v.1 hok k1
  subst eH
  have hc : vW (worldOwn a [] (St.at1 s (dataQ own a rdW))) gk.cEnd =
      vW (worldE ((seatAt W.hS (readsOf W)).ledger s) d.2 noEnt) gk.cEnd := by
    unfold vW
    refine value_agree0 Reading.gl _ _ gk.cEnd (fun y _ => hslot y.1) fun y hy => ?_
    rw [hbare gk hgk] at hy
    simp at hy
  obtain ⟨hWt, h35, hj⟩ := claims_of_k6Out W s d v.1 _ (v.2.2.final, v.2.2.head) gk
    (worldOwn a [] (St.at1 s (dataQ own a rdW))) hg hH hgk
    (k6Exchange_of_entries v.1 _ (v.2.2.final, v.2.2.head) d.1 _ _ hslot (hA e v he hv) hB hd hJ)
    (seat_zero_of_true v.1 _ (v.2.2.final, v.2.2.head) d.1 _ _ hslot (hA e v he hv) hB hd) hc hO
  have h35' : ∀ name fs, (claimsSeat v).lookup name = some fs → ∀ f, f ∈ fs →
      f.value Reading.gl (worldOwn a [] (St.at1 s (dataQ own a rdW))) = 0 := h35
  refine ⟨hWt, fun name hnm => ?_⟩
  rcases hnm with rfl | rfl | rfl | rfl
  · refine ⟨a, Rn, ha, qn, on, fun f hf => ⟨an f hf, ?_⟩⟩
    rw [tn]
    exact h35' "norm" fsn ln f (en ▸ hf)
  · refine ⟨a, Rp, ha, qp, op, fun f hf => ⟨ap f hf, ?_⟩⟩
    rw [tp]
    exact h35' "policy" fsp lp f (ep ▸ hf)
  · refine ⟨a, Rl, ha, ql, ol, fun f hf => ⟨al f hf, ?_⟩⟩
    rw [tl]
    exact h35' "logits" fsl ll f (el ▸ hf)
  · refine ⟨a, Rj, ha, qj, oj, fun f hf => ⟨aj f hf, ?_⟩⟩
    rw [ej] at hf
    obtain rfl := List.mem_singleton.1 hf
    rw [tj]
    exact hj

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.test_says
#print axioms VerifiableInference.Desc.Kinds.Head.Law.forms_of_k6Out
