--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/K6OpenedBack.lean: THE WAY BACK OF Law/K6OpenedCut.lean's k6Out_cut_of_forms:
FROM K6Out AT THE COMPONENTS THAT THE LAW READS OFF A WITNESS (compCut, Law/K6Cut.lean) TO THE
TABLE's SENTENCE formsTQ AT THE OUTPUT HEAD's FOUR RUNS, AT THAT WITNESS's OWN MESSAGES (seatTab),
AND TO WeightAt. STATED AND PROVED: TWO CALLS OVER Law/K6SilentBack.lean, with the premises met as
on the way there: no new mathematics.
WHAT IT CANNOT GIVE, FIRST. · The items formsT 24 3 "planes" and constr 24 "small", which the
table's row opens at the same border: opened_cut takes both and spends neither; K6Out does not read
them: they want honest facts of their own · A WITNESS: the theorem stands at every w: that some w
has compCut ... w = the cells and the mask row of an honest run is another statement · RecordDue at
an honest state · an example. Nothing on soundness or on hiding.
  forms_of_k6Out_statedAll   the way back of Law/K6StatedPlanes.lean's k6Out_of_items_statedAll.
  **Came.forms_of_k6Out_cut**  under RecordDue, the plan's test, one test on N and the public test
      K9.formsInT at the four names: K6Out Wp s (compCut ... w) gives WeightAt at compCut's two
      components and formsTQ Rd St (N.sent 24 0) 3 r s (seatTab cs arr msR w) at the four names.
      WITH k6Out_cut_of_forms: AN IFF UNDER THESE PREMISES.

-/
import Johnson.Desc.Kinds.Law.K6OpenedCut
import Johnson.Desc.Kinds.Law.K6SilentBack

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Params (ReqLayout)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning)
open VerifiableInference.Desc.Sound (Mem MsgT namedOnce Piece Frame Sending onQ strsOf meaningSig)
open VerifiableInference.Desc.K9L (Bound)

/-- **The way back at stated data whose cells of the reads' array are statedAll.** The letters are
k6Out_of_items_statedAll's. -/
theorem forms_of_k6Out_statedAll (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH)
    (l piece b : Nat) (states : Nat → List (K9.RunOf S))
    (KS : K6States W.hS (readsOf W) (parOf W.hS (workOf W)) l piece states b)
    (Rd : K9.Readers) (St : Sound.Stated) (own : List (Nat × Nat)) (s : S)
    (rdW : Nat × Nat → Sound.MsgQ) (d : Pinned) (a : K9.Part) (ha : K9.segAt? s = some a)
    (hRd : ∀ name, K6Name name → Rd.forms b name s = k6Silent P states b name s)
    (hok : (parOf W.hS (workOf W)).ok = true)
    (hT : K6HeardAt W.hS (readsOf W) (parOf W.hS (workOf W)) s)
    (hmask : ∀ j, j < a.F.mf.size → (St.at1 s (Sound.dataQ own a rdW)).mask j = rd (d.2 j))
    (cells : S → Bound K → NCells) (lm : Nat) (nu : S → Bound K → _root_.Fo.Pl → K)
    (cU : Nat × String) (hArr : a.L.arrayOf[readsOf W]? = some cU)
    (hcell : ∀ pos, (St.at1 s (Sound.dataQ own a rdW)).cell cU.1 cU.2 0 pos =
      statedAll W P cells lm nu s (Sound.dataQ own a rdW) cU 0 pos)
    (hd1 : d.1.cell = (cells s (Sound.dataQ own a rdW)).cell)
    (hd2 : d.1.stream = (cells s (Sound.dataQ own a rdW)).stream)
    (hApart : ∀ e o tt, withTables P s = some e → e.here = .head o → o.t = some tt →
      TabsApart tt)
    (hBelow : ∀ e o tt F tr, withTables P s = some e → e.here = .head o → o.t = some tt →
      e.fork? = some F → F.trees[readsOf W]? = some tr → ∀ x ∈ tt.tab, x.2.1 + x.2.2 ≤ tr.K)
    (hbare : ∀ gk, s.lookHeard? = some gk → gk.cEnd.ents = #[])
    (hIn : ∀ name, K6Name name → K9.formsInT Rd own b name s = true) (hO : K6Out W s d) :
    WeightAt W s d.1.toCells d.2 ∧
      ∀ name, K6Name name → Sound.formsTQ Rd St own b name s rdW :=
  forms_of_k6Out W P l piece b states KS Rd St own s rdW d a ha hRd hok hT hmask
    (fun e v he hv => entriesAlike_of_statedAll W P cells lm nu s e a (Sound.dataQ own a rdW) _ d v
      he hv cU hArr hcell hd1 hd2 (fun o tt => hApart e o tt he)
      (fun o tt F tr => hBelow e o tt F tr he) _)
    hbare hIn hO

namespace Came

variable {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type} (arr : Nat → Nat → Nat)
  (msR : List Mem) (N : Numbers) (Wp : OnBytes.Model.Verify.Public) (layout : ReqLayout)
  (num : Nat → Nat → Nat) (n rb : Nat)

/-- **FROM K6Out AT compCut TO THE FORMS' SENTENCES.** The letters are k6Out_cut_of_forms'. -/
theorem forms_of_k6Out_cut (P8 : K8.ReadsQuiet.PH) (l piece : Nat)
    (states : Nat → List (K9.RunOf S))
    (KS : K6States Wp.hS (readsOf Wp) (parOf Wp.hS (workOf Wp)) l piece states 3)
    (Rd : K9.Readers) (St : Sound.Stated) (s : S) (aK : K9.Part) (cU : Nat × String)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (R : RecordDue arr N Wp layout num n rb P8 St states Rd s aK cU)
    (hok : (parOf Wp.hS (workOf Wp)).ok = true) (h1 : namedOnce arr N 24 n = true)
    (hIn : ∀ r, K6Name r → K9.formsInT Rd (N.sent 24 0) 3 r s = true)
    (hO : K6Out Wp s
      (compCut cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp layout num) Wp (plAt n rb) w)) :
    WeightAt Wp s (compCut cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp layout num) Wp (plAt
        n rb) w).1.toCells (compCut cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp layout num) Wp
            (plAt n rb) w).2 ∧
      ∀ r, K6Name r → Sound.formsTQ Rd St (N.sent 24 0) 3 r s (Sound.seatTab cs arr msR w) := by
  obtain ⟨ha, hlay, hD, ⟨o, x, ho, hx, hg, hnx, hrb⟩, hsz, hRd, hT, hArr, hsec, hApart, hBelow,
    hbare⟩ := R
  subst hlay
  subst hrb
  obtain ⟨e1, e2⟩ := comp_of_data cs arr msR N Wp (plAt n (aK.d.st.rowBits o .mask)) (N.sent 24 0)
    aK num w hD
  exact forms_of_k6Out_statedAll Wp P8 l piece 3 states KS Rd St (N.sent 24 0) s
    (Sound.seatTab cs arr msR w) _ aK ha hRd hok hT
    (fun j hj => by
      rw [(hsec _).1 j]
      exact mask_of_data cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp aK.L.check.rows.layout num)
        Wp (N.sent 24 0) aK w o n x ho hx hg hnx h1 j (Nat.lt_of_lt_of_le hj hsz))
    (cellsK6 Wp) Wp.hS.lmbH (nuK6 Wp) cU hArr (fun pos => (hsec _).2 pos) e1 e2 hApart hBelow
    hbare hIn hO

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.forms_of_k6Out_statedAll
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.forms_of_k6Out_cut
