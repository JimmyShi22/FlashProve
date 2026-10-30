-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/PointAtLedger.lean: THE LAW AT "LIN point", TYPED AT ANOTHER FILLING OF THE
SHARED TABLE's LETTERS, CARRIED INTO THE LEDGER's PREMISE AT BLOCK 1, AT THE LEDGER's OWN FILLING
(pmK, mgK: Johnson/Desc/K14/Law/LedgerRow.lean). Theorems. A JOINING: no chance is counted here.

THE TWO FILLINGS. PmS, MgS: the promise's and the items' meanings at which the law stands: LETTERS
here; what is asked of them is said field by field (PromFits, MeanFits). THE LEDGER's LETTERS Pm₀
AND Mg₀ ARE LAID AS PmS AND MgS THEMSELVES: so the slot's own items and the book-keeping at border 1
are one by make. uS: the reader of the state at which MgS says "near", "RecRow" and "Omega is what
u gives": asked only: where the chain's statement has no message yet it is "o_u noted as the
message to come".
  prom_front       (f) the ledger's promise at border 1 gives PmS's.
  prom_behind      (b) inside the ledger's promise at 1, at a yes of the piece, PmS's promise at 2
                   gives the ledger's: shapeP by shape2 (had) and point_extras; the layout's test
                   by the codes kept; X by its own hand-on, a premise.
  rel_behind       (r') at border 2, inside the ledger's promise: mgK's items give MgS's.
  rel_front        (r) at border 1: MgS's items give mgK's.
  point_at_ledger  **the joint**: by step_carry (Johnson/Desc/Sound/StepCarry.lean): same key, same
                   extractor, same two lists of errors.
  point_at_ledgerN the same for the law at one list of errors for m slots (LeadsBN): so a law AT THE
                   CAP is carried as it stands: its radius e' is then the ledger's e'.
THE RADIUS. e' IS ONE LETTER ON BOTH SIDES: the radius at which MgS says "near" is the one at which
mgK says it, and so the one of which the ledger's count at "LOC" speaks. THAT IT IS THE PLAN's
RADIUS IS NOT SAID HERE: at a huge e' the law H may be true and hollow: whoever hands H at written
numbers brings that tie.
Limits. The law itself is the premise H. X is a letter: that a yes of the piece hands X 1 on to
X 2 (hX) and that X 1 gives "no message yet" (hsz) are premises. The number of o_u is 0. Nothing on
the front block, on "own 1 pt = δK + n δO", or on the ten blocks behind. No member. No soundness of
a verifier.

-/
import Johnson.Desc.Sound.StepCarry
import Johnson.Desc.Sound.PointTie
import Johnson.Desc.Sound.SamplesAtK14
import Johnson.Desc.K14.Law.LedgerRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block Strs Wit FileDescription Grows)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

variable {P₁ Cl Xi Cells Tok κ : Type} {Fr : Frame} (cs : OnBytes.Codes) (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp₂ : St → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells)
  (bkR : TreeBook → TreeBook) (N : NumbersS)
  (MgS : MeaningS St P₁ (Wit Cells Tok MsgT)) (PmS : PromMeaning St) (Oc : P₁ → Strs → Prop)
  (mem : ℕ → Option Mem) (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
  (e' n nO : ℕ) (Q : P14) (X : ℕ → St → Bool) (split : Bool) (uS : St → St)
  (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))

/-- What is asked of the promise's meaning at which the law stands. -/
structure PromFits : Prop where
  table : PmS.tablePromise = decodesOf decT₂
  noColl : PmS.noColl = noCollJT cs G smp₂ ms
  shown : PmS.shown = shownJT cs G ms
  two : ∀ s, PmS.shape 2 s = true → shape2 Q.par s = true

/-- What is asked of the items' meaning at which the law stands. -/
structure MeanFits : Prop where
  pinT : MgS.pinT = pinWOf decT₂
  nearU : ∀ s y w, MgS.nearU s y w ↔ NearAt OnBytes.Model.Reading.gl Q.par (uS s)
    (rgOf cs arr mem rd w) (colsOf y.cell) e'
  recRow : ∀ s w, MgS.recRow s w ↔ RecAll OnBytes.Model.Reading.gl Q.par (uS s)
    (rgOf cs arr mem rd w)
  omU : ∀ s w, MgS.omU s w ↔ OmU Q.par uS (rgOf cs arr mem rd) (omWK cs arr mem rd nO Q) s w

/-- No clause "nothing is left" stands at the borders 1 and 2. -/
theorem nothing_not_early (k : ℕ) (hk : k = 1 ∨ k = 2) : PromS.nothingLeft ∉ promsAt split k := by
  rcases hk with rfl | rfl <;> cases split <;> decide

/-- (f) In front. -/
theorem prom_front (hP : PromFits cs G smp₂ ms decT₂ PmS Q) (a : (P₁ × St) × Fr.E.Str)
    (h : onQ₂ N (pmK cs G smp₂ ms decT₂ bkR PmS n 0 nO Q X) Oc split f l 1 a) :
    onQ₂ N PmS Oc split f l 1 a := by
  refine ⟨fun c hc => ?_, h.2⟩
  have h0 := ((promQ_beside N _ split f l (besX Q X) 1 _).1 h.1).1 c hc
  cases c with
  | tablePromise =>
    show PmS.tablePromise _ _
    rw [hP.table]
    exact h0
  | noColl m =>
    show PmS.shown _ _ _ ∧ PmS.noColl _ _ _ _
    rw [hP.shown, hP.noColl]
    exact h0
  | nothingLeft => exact absurd hc (nothing_not_early split 1 (Or.inl rfl))
  | shape j =>
    obtain rfl := shape_mem split 1 j hc
    exact h0

/-- (b) Behind, at a yes. -/
theorem prom_behind (hP : PromFits cs G smp₂ ms decT₂ PmS Q)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : Q.par.S.sharedSplitNeeded = true)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (hx : x.b = heldW b1.retype)
    (hsz : ∀ s, X 1 s = true → s.st.oracles.size = 0)
    (hX : ∀ a τ b, x.ior.red.out a τ = some b → X 1 a.1.2 = true → X 2 b.1.2 = true)
    (a : (P₁ × St) × Fr.E.Str) (τ : Iop.Tr (uLT (ckP .two) x.ds)) (b : (P₁ × St) × Fr.E.Str)
    (ha : onQ₂ N (pmK cs G smp₂ ms decT₂ bkR PmS n 0 nO Q X) Oc split f l 1 a)
    (ho : x.ior.red.out a τ = some b) (hb : onQ₂ N PmS Oc split f l 2 b) :
    onQ₂ N (pmK cs G smp₂ ms decT₂ bkR PmS n 0 nO Q X) Oc split f l 2 b := by
  obtain ⟨rs, gs, hd⟩ := held_yes x b1.retype hx a τ b ho
  have hd' : b1.decide a.1.2 rs gs = .ok b.1.2 := hd
  have hbes : besX Q X 1 a.1.2 = true := ((promQ_beside N _ split f l (besX Q X) 1 _).1 ha.1).2
  obtain ⟨hlay, hX1⟩ := Bool.and_eq_true_iff.1 hbes
  have k1 := point_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl _ _ gs _ hd'
  obtain ⟨e1, e2, e3⟩ := point_extras Q.par hS 0 a.1.2 b.1.2 rs k1 (hsz _ hX1)
  have hcodes :=
    (Fence.keepsSmp_k14 Q b1 b2 b3 b4 b5 b6 b7 b8 hbl b1 (by simp) a.1.2 b.1.2 rs gs hd').1
  have hs2 : shape2 Q.par b.1.2 = true :=
    hP.two _ (hb.1 (.shape 2) (by simp [promsAt]))
  refine ⟨(promQ_beside N _ split f l (besX Q X) 2 _).2 ⟨fun c hc => ?_, ?_⟩, hb.2⟩
  · have h0 := hb.1 c hc
    cases c with
    | tablePromise =>
      have h1 : PmS.tablePromise _ _ := h0
      rw [hP.table] at h1
      exact h1
    | noColl m =>
      have h1 : PmS.shown _ _ _ ∧ PmS.noColl _ _ _ _ := h0
      rw [hP.shown, hP.noColl] at h1
      exact h1
    | nothingLeft => exact absurd hc (nothing_not_early split 2 (Or.inr rfl))
    | shape j =>
      obtain rfl := shape_mem split 2 j hc
      show shapeP Q.par 0 b.1.2 = true
      unfold shapeP
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨hs2, e1⟩, e2⟩, e3⟩
  · exact Bool.and_eq_true_iff.2 ⟨layX_codes Q 1 2 a.1.2 b.1.2 hcodes hlay, hX a τ b ho hX1⟩

/-- What is open, of the shared items, at border 2. -/
theorem openSh_two_is (i : ItemS) (h : openAfter (insSh split) (outsSh split) startSh 2 i) :
    i = .omU ∨ i = .nearU ∨ i = .recRow ∨ i = .pinT := by
  have h' := (openShL_iff split 2 i).1 h
  cases split
  · have e : ∀ j ∈ openL (insLSh false) (outsLSh false) startLSh 2,
        j = ItemS.omU ∨ j = .nearU ∨ j = .recRow ∨ j = .pinT := by decide
    exact e i h'
  · have e : ∀ j ∈ openL (insLSh true) (outsLSh true) startLSh 2,
        j = ItemS.omU ∨ j = .nearU ∨ j = .recRow ∨ j = .pinT := by decide
    exact e i h'

/-- (r') Behind, inside the ledger's promise. -/
theorem rel_behind (hM : MeanFits cs arr decT₂ MgS mem rd e' nO Q uS)
    (hu : ∀ s : St, s.st.oracles.size = 0 → uS s = withNext Q.par s)
    (b : (P₁ × St) × Fr.E.Str) (w : Wit Cells Tok MsgT)
    (hb : onQ₂ N (pmK cs G smp₂ ms decT₂ bkR PmS n 0 nO Q X) Oc split f l 2 b)
    (h : relQ₂ N (mgK cs G arr smp₂ ms decT₂ MgS mem rd e' n nO Q) split f l 2 b w) :
    relQ₂ N MgS split f l 2 b w := by
  have hsh : shapeP Q.par 0 b.1.2 = true :=
    ((promQ_beside N _ split f l (besX Q X) 2 _).1 hb.1).1 (.shape 2) (by simp [promsAt])
  have hz : b.1.2.st.oracles.size = 0 :=
    ((midB_iff 0 b.1.2).1 ((shapeP_iff Q.par 0 b.1.2).1 hsh).2.2.2).1
  have e : uRK Q.par ((actQ N f l 2).2 b).1 = uS ((actQ N f l 2).2 b).1 :=
    (uRK_next Q.par b.1.2 hz).trans (hu b.1.2 hz).symm
  refine ⟨fun i hi => ?_, h.2⟩
  have h0 := h.1 i hi
  rcases openSh_two_is split i hi with rfl | rfl | rfl | rfl
  · refine (hM.omU _ _).2 ?_
    have h1 : OmU Q.par (uRK Q.par) (rgOf cs arr mem rd) (omWK cs arr mem rd nO Q)
      ((actQ N f l 2).2 b).1 w := h0
    unfold OmU at h1 ⊢
    rw [← e]
    exact h1
  · refine (hM.nearU _ _ _).2 ?_
    rw [← e]
    exact h0
  · refine (hM.recRow _ _).2 ?_
    rw [← e]
    exact h0
  · show MgS.pinT _ _ _
    rw [hM.pinT]
    exact h0

/-- (r) In front. -/
theorem rel_front (hM : MeanFits cs arr decT₂ MgS mem rd e' nO Q uS)
    (a : (P₁ × St) × Fr.E.Str) (w : Wit Cells Tok MsgT) (h : relQ₂ N MgS split f l 1 a w) :
    relQ₂ N (mgK cs G arr smp₂ ms decT₂ MgS mem rd e' n nO Q) split f l 1 a w := by
  refine ⟨fun i hi => ?_, h.2⟩
  have h0 := h.1 i hi
  obtain rfl := openSh_one split i hi
  have h1 : MgS.pinT _ _ _ := h0
  rw [hM.pinT] at h1
  exact h1

/-- **THE JOINT.** -/
theorem point_at_ledger (hP : PromFits cs G smp₂ ms decT₂ PmS Q)
    (hM : MeanFits cs arr decT₂ MgS mem rd e' nO Q uS)
    (hu : ∀ s : St, s.st.oracles.size = 0 → uS s = withNext Q.par s)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : Q.par.S.sharedSplitNeeded = true)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (hx : x.b = heldW b1.retype)
    (hsz : ∀ s, X 1 s = true → s.st.oracles.size = 0)
    (hX : ∀ a τ b, x.ior.red.out a τ = some b → X 1 a.1.2 = true → X 2 b.1.2 = true)
    (ext : ℕ → (P₁ × St) × Fr.E.Str → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (key : (P₁ × St) × Fr.E.Str → κ) (δK δO : Err (uLT (ckP .two) x.ds))
    (H : x.ior.red.LeadsB key (onQ₂ N PmS Oc split f l 1) (stepAt N MgS PmS Oc split f l ext 1)
      δK δO) :
    x.ior.red.LeadsB key (onQ₂ N (pmK cs G smp₂ ms decT₂ bkR PmS n 0 nO Q X) Oc split f l 1)
      (stepAt N (mgK cs G arr smp₂ ms decT₂ MgS mem rd e' n nO Q)
        (pmK cs G smp₂ ms decT₂ bkR PmS n 0 nO Q X) Oc split f l ext 1) δK δO :=
  step_carry N MgS _ PmS _ Oc split f l ext 1 x key δK δO H
    (prom_front cs G smp₂ ms decT₂ bkR N PmS Oc n nO Q X split f l hP)
    (prom_behind cs G smp₂ ms decT₂ bkR N PmS Oc n nO Q X split f l hP b1 b2 b3 b4 b5 b6 b7 b8 hbl
      hS x hx hsz hX)
    (fun _ _ b w _ _ hb h =>
      rel_behind cs G arr smp₂ ms decT₂ bkR N MgS PmS Oc mem rd e' n nO Q X split uS f l hM hu b w
        hb h)
    (fun a w _ h => rel_front cs G arr smp₂ ms decT₂ N MgS mem rd e' n nO Q split uS f l hM a w h)

/-- **THE JOINT, at one list of errors for m slots.** -/
theorem point_at_ledgerN (hP : PromFits cs G smp₂ ms decT₂ PmS Q)
    (hM : MeanFits cs arr decT₂ MgS mem rd e' nO Q uS)
    (hu : ∀ s : St, s.st.oracles.size = 0 → uS s = withNext Q.par s)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : Q.par.S.sharedSplitNeeded = true)
    (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)) (hx : x.b = heldW b1.retype)
    (hsz : ∀ s, X 1 s = true → s.st.oracles.size = 0)
    (hX : ∀ a τ b, x.ior.red.out a τ = some b → X 1 a.1.2 = true → X 2 b.1.2 = true)
    (ext : ℕ → (P₁ × St) × Fr.E.Str → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
    (key : (P₁ × St) × Fr.E.Str → κ) (m : ℕ) (ε : Err (uLT (ckP .two) x.ds))
    (H : x.ior.red.LeadsBN key (onQ₂ N PmS Oc split f l 1) (stepAt N MgS PmS Oc split f l ext 1)
      m ε) :
    x.ior.red.LeadsBN key (onQ₂ N (pmK cs G smp₂ ms decT₂ bkR PmS n 0 nO Q X) Oc split f l 1)
      (stepAt N (mgK cs G arr smp₂ ms decT₂ MgS mem rd e' n nO Q)
        (pmK cs G smp₂ ms decT₂ bkR PmS n 0 nO Q X) Oc split f l ext 1) m ε :=
  step_carryN N MgS _ PmS _ Oc split f l ext 1 x key m ε H
    (prom_front cs G smp₂ ms decT₂ bkR N PmS Oc n nO Q X split f l hP)
    (prom_behind cs G smp₂ ms decT₂ bkR N PmS Oc n nO Q X split f l hP b1 b2 b3 b4 b5 b6 b7 b8 hbl
      hS x hx hsz hX)
    (fun _ _ b w _ _ hb h =>
      rel_behind cs G arr smp₂ ms decT₂ bkR N MgS PmS Oc mem rd e' n nO Q X split uS f l hM hu b w
        hb h)
    (fun a w _ h => rel_front cs G arr smp₂ ms decT₂ N MgS mem rd e' n nO Q split uS f l hM a w h)

end Desc.K14.Law

#print axioms Desc.K14.Law.point_at_ledger
#print axioms Desc.K14.Law.point_at_ledgerN
