-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6CutGuarded.lean: THE LAW OF THE SUB-PROTOCOL AT THE OUTPUT HEAD, WITH ITS
TWO SENTENCES ON THE WITNESS UNDER A GUARD: "the witness's cells hold an index"
(Johnson/Flat/LedgerClaim.lean: InRange).

Why. The law (Law/K6TiedCut.lean: k6_law_cut) reads the output matrix's weights off the witness as
whOf w.cells (Law/WhOf.lean): the output matrix of the index that the cells hold; 0 where they hold
none. The merge's files' sentence on the claim on the weights, and the lookup's caller, read the
cells themselves. So at a witness whose cells hold no index the
law's sentence behind ("opened": among it the claim on the weights) does not follow from what the
table of joints opens there, whatever is laid into the table's parameter for that claim. The items
that the table's row for this sub-protocol CLOSES stand under that guard on the witness, or under
one that gives it with the committed table's pin: so the guard may stand in front of the law's own
two sentences: Law/K6ItemsCut.lean's fourth tie hands it on to each of the four.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  meansCutG z: meansCut z, with "closed" and "opened" under the guard; "pins" as it was.
  k6_law_cutG: THE LAW AT meansCutG: from k6_law_cut, transcript by transcript (by
      Doomed.mono): under the guard it is the law; the pins ride back without it (Law/K6OwnW.lean:
      pinsW_back).

Every letter under "there is": none.
What it does not say. Nothing at a witness whose cells hold no index, but that the pins ride. Its
premises are k6_law_cut's. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K6TiedCut

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.OnPublicFiles.Flat (GE InRange)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.Sound (Piece Frame Sending Mem MsgT strsOf Fenced ErrBears kitK kitFs
  out_yes below_narrows out_behind)

variable {rows cols : Nat} (cs : OnBytes.Codes) {Xi P Tok : Type} (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp : P × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × S → Option (Fin rows → Fin cols → GE))
  (msR : List Mem) (N : Numbers) (s : ℕ → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (Wp : OnBytes.Model.Verify.Public)
  (pl : ℕ → ℕ × Bool × ℕ × ℕ) (fld : Fmt.Fld) (Fr : Frame)
  (q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT))

/-- **The law's three items, two of them under the guard on the witness.** -/
def meansCutG (z : P) :
    K6Item → S × Fr.E.Str → Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop
  | .pins, a, w => meansCut cs G arr smp decT msR N s seat Wp pl Fr z .pins a w
  | .closed, a, w => InRange w.cells → meansCut cs G arr smp decT msR N s seat Wp pl Fr z .closed a
      w
  | .opened, a, w => InRange w.cells → meansCut cs G arr smp decT msR N s seat Wp pl Fr z .opened a
      w

/-- **The law at the guarded items.** -/
theorem k6_law_cutG (hback : q.back = []) (hBl : Blind cs smp decT)
    (hP : PlanK6 cs arr msR N s seat Wp pl) (hF : Fenced q.base (ms0 msR N))
    (hlog : ∀ d, d ∈ toRDs q.ds → d.entry.logN ≤ 64)
    (hErr : ErrBears (_root_.Run.ckP fld)
      (fun j => kitK (toRDs q.ds) j *
        (priceAt (parOf Wp.hS (workOf Wp)) j * kitFs fld (toRDs q.ds) j)) (toRDs q.ds) 0 q.err)
    (z : P) (b6 : Block S Unit) (h6 : blockOf Wp 24 = some b6) :
    (⟨Sound.below b6, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (_root_.Run.ckP fld) Fr S Unit (Wit (Fin rows → Fin cols → GE) Tok MsgT)).Own
      (fun a => K6On Wp a.1) (fun b => K6After Wp b.1)
      (meansCutG cs G arr smp decT msR N s seat Wp pl Fr z) InK6 OutK6 := by
  have h := k6_law_cut cs G arr smp decT msR N s seat Wp pl fld Fr q hback hBl hP hF hlog hErr z b6
    h6
  have hrec : ∀ (a b : S × Fr.E.Str) τ,
      (⟨Sound.below b6, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (_root_.Run.ckP fld) Fr S Unit
          (Wit (Fin rows → Fin cols → GE) Tok MsgT)).ior.red.out a τ = some b →
      ∃ h, b.1 = { a.1 with here := h } := by
    intro a b τ hb
    obtain ⟨rs, gs, hd⟩ := out_yes (⟨Sound.below b6, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (_root_.Run.ckP fld) Fr S Unit (Wit (Fin rows → Fin cols → GE) Tok MsgT)) a b τ hb
    obtain ⟨o, F1, X, Q, _, _, _, e⟩ := record6 h6 ((below_narrows b6).2 _ _ _ _ hd)
    exact ⟨_, e⟩
  intro a ha
  refine _root_.Iop.Doomed.mono _ _ ?_ (h a ha)
  intro τ hτ b hb
  refine ⟨(hτ b hb).1, fun w hw i hi => ?_⟩
  rcases hi with rfl | rfl
  · intro hR
    refine (hτ b hb).2 w (fun j hj => ?_) .closed (Or.inl rfl)
    rcases hj with rfl | rfl
    · exact hw .opened (Or.inl rfl) hR
    · exact hw .pins (Or.inr rfl)
  · refine Came.pinsW_back cs G arr (fun t => smp (z, t)) (fun c t => decT c (z, t)) (ms0 msR N)
      (compCut cs arr msR N s seat Wp pl) (base24 cs arr msR N s seat) Wp (⟨Sound.below b6, q.base,
          q.ds, q.back, fun _ _ w => w, q.err⟩ :
      Piece (_root_.Run.ckP fld) Fr S Unit (Wit (Fin rows → Fin cols → GE) Tok MsgT)) hF ?_ ?_ a b τ
      hb w (hw .pins (Or.inr rfl))
    · intro a τ b hb x _
      obtain ⟨h, e⟩ := hrec a b τ hb
      show smp (z, b.1) x.1 x.2 = smp (z, a.1) x.1 x.2
      rw [e, hBl.smp]
    · intro a τ b hb
      obtain ⟨h, e⟩ := hrec a b τ hb
      have e2 := out_behind (⟨Sound.below b6, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (_root_.Run.ckP fld) Fr S Unit (Wit (Fin rows → Fin cols → GE) Tok MsgT)) a b τ hb
      show decT (strsOf Fr b.2).cell (z, b.1) = decT (strsOf Fr a.2).cell (z, a.1)
      rw [e, hBl.dec, e2]
      rfl

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.k6_law_cutG
