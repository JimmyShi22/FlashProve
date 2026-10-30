-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SeamCore.lean: **THE SEAM AT THE SHARED CHAIN's TWO PROXIMITY TESTS, CUT DOWN TO ITS CORE: "ONE TUPLE OF TYPED MESSAGES".** Statements and proofs.

nine_paid | ten_paid (NineAt.lean | TenAt.lean) take the seam as one premise: K12's conclusion at the record behind the door in (QN π (NTuple …)) gives TestSays: there are words that are a candidate at every member and at which every closed class says its
claim. Here Say is the filling SayK (Johnson/Desc/K14/Law/LedgerSay.lean), and the half on the classes is paid (SeamRows.lean). WHAT IS LEFT IS NAMED:
  TupleNine | TupleTen   THE CORE: under the promise at the border, AT A YES OF THE PIECE (words_tuple, Johnson/Desc/K12/Law/TupleWords.lean, asks facts that a yes alone gives), from K12's conclusion: there is ONE TUPLE m OF TYPED MESSAGES (one for each member of the list ms, in the row words_are_committed's types) such that
                         (i) every row that the test takes in says its claim of the words built of m (wordsT cs mem rd m), at the statement behind the test's beginning · (ii) m is a candidate at the laid and at the kept message.
                         NO CLASS, NO SLICE, NO TABLE OF ROWS STANDS IN IT: it is a translation between K12's files' letters (the witness's shares; strOf; the seed) and that row's (Tup cs; wordsOf; smpAt).
  **seam_nine | seam_ten**   nine_paid's | ten_paid's premise seam, TO THE LETTER, at Say := SayK …: from the core · "no open row is of the kind sample" inside the promise (OpenKinds: a part of Tidy: tidY) · num at the members' numbers.
By: rows_nine | rows_ten (SeamRows.lean) · membX 9 | 10 (the group's members) · x_numbers (they are messages of the record).
Limits. THE CORE IS A PREMISE. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.SeamRows
import Johnson.Desc.Sound.NineAt
import Johnson.Desc.Sound.TenAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker Desc.Plain Johnson.Pack Cb
open Iop Prob _root_.Run
open OnBytes.Means (Words AllSay OpenKinds)
open VerifiableInference.Desc (Block FileDescription Strs Wit)
open VerifiableInference.Desc.K12 (P12 T12)
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open H2K.Pin (NTuple)
open _root_.Desc.K14.Law (SayK wordsT rowW)

variable (cs : Codes) {Xi P₁ Cl Cells Tok : Type} (G : FileDescription Xi) (ms : List Mem) (N : NumbersS)
  (Pm₀ : PromMeaning St) (Oc : P₁ → Strs → Prop) {Fr : Frame} (oNo : Mem → ℕ) (P : P14)
  (sentU : Array OracleNotice) (layU layO : TreeLay)
  (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))
  (mem : ℕ → Option Mem) (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
  (Q : Par) (n : ℕ) (num : Msg2 → ℕ) (π : P12) (t₁ t₂ c : ℕ) (rad : Sg → ℕ) (rdN : ℕ → ℕ)
  (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))

/-- **THE CORE AT THE TEST ON G_u.** -/
def TupleNine : Prop :=
  ∀ a τ b t, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a →
    x.ior.red.out a τ = some b → inGu a.1.2 = .ok t → QN π (NTuple Fr π (noAt t₁ t₂ c) rad rdN) (t, a.2) →
    ∀ G0, a.1.2.st.groups[a.1.2.loc.gU]? = some G0 →
    ∃ m : VerifiableInference.Desc.Sound.Tup cs,
      AllSay OnBytes.Model.Reading.gl (begun a.1.2.st a.1.2.loc.gU G0)
        (runRows a.1.2.st G0).toList (wordsT cs mem rd m) ∧
      ∀ μ, μ = Msg2.oU ∨ μ ∈ [Msg2.oSp] →
        candT cs G (smpSt cs oNo stSh) ms N μ ((actQ N f l 9).2 a) m

/-- **THE CORE AT THE TEST ON G_omega.** -/
def TupleTen : Prop :=
  ∀ a τ b t, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 10 a →
    x.ior.red.out a τ = some b → inGomega a.1.2 = .ok t → QN π (NTuple Fr π (noAt t₁ t₂ c) rad rdN) (t, a.2) →
    ∀ G0, a.1.2.st.groups[a.1.2.loc.gOmega]? = some G0 →
    ∃ m : VerifiableInference.Desc.Sound.Tup cs,
      AllSay OnBytes.Model.Reading.gl (begun a.1.2.st a.1.2.loc.gOmega G0)
        (runRows a.1.2.st G0).toList (wordsT cs mem rd m) ∧
      ∀ μ, μ = Msg2.oSp ∨ μ ∈ [Msg2.oOmega] →
        candT cs G (smpSt cs oNo stSh) ms N μ ((actQ N f l 10).2 a) m

/-- **nine_paid's seam, AT SayK.** -/
theorem seam_nine (hsU : sentU.size = 2) (hsO : (withOmega P.S).size = 2)
    (core : TupleNine cs G ms N Pm₀ Oc oNo P sentU layU layO f l mem rd π t₁ t₂ c rad rdN x)
    (hK : ∀ a, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a →
      OpenKinds a.1.2.st)
    (hnU : num .oU = 0) :
    ∀ a τ b t, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a →
      x.ior.red.out a τ = some b → inGu a.1.2 = .ok t → QN π (NTuple Fr π (noAt t₁ t₂ c) rad rdN) (t, a.2) →
      TestSays N f l (SayK cs mem rd Q n num) (candT cs G (smpSt cs oNo stSh) ms N) 9 .oU [.oSp]
        [.sample .oU, .recG, .loc, .foldU] a := by
  intro a τ b t ha hout ht hq
  have hX := x_of_on cs G ms N Pm₀ Oc oNo P sentU layU layO f l 9 a ha
  obtain ⟨_, hmem, _, _, _, _⟩ :=
    (membX789 _ _ 9 (.inr (.inr rfl))).1 ((sharedX_parts P sentU layU layO 9 _).1 hX).2.2.1
  unfold memOf at hmem
  obtain ⟨G0, hG0, hmm⟩ := Option.map_eq_some_iff.1 hmem
  obtain ⟨m, hall, hc⟩ := core a τ b t ha hout ht hq G0 hG0
  have lt := x_numbers P sentU layU layO 9 (.inl rfl) _ hX hsU hsO 0 (.inl rfl)
  refine ⟨m, hc, rows_nine Q n num a.1.2 G0 hG0 (hK a ha) _ hall ?_ a.1.2.st.oracles[0] ?_⟩
  · rw [hnU, hmm]
    simp
  · rw [hnU]
    exact Array.getElem?_eq_getElem lt

/-- **ten_paid's seam, AT SayK.** -/
theorem seam_ten (hsU : sentU.size = 2) (hsO : (withOmega P.S).size = 2)
    (core : TupleTen cs G ms N Pm₀ Oc oNo P sentU layU layO f l mem rd π t₁ t₂ c rad rdN x)
    (hK : ∀ a, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 10 a →
      OpenKinds a.1.2.st)
    (hnO : num .oOmega = sentU.size) (hnS : num .oSp = sentU.size + 1) :
    ∀ a τ b t, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 10 a →
      x.ior.red.out a τ = some b → inGomega a.1.2 = .ok t → QN π (NTuple Fr π (noAt t₁ t₂ c) rad rdN) (t, a.2) →
      TestSays N f l (SayK cs mem rd Q n num) (candT cs G (smpSt cs oNo stSh) ms N) 10 .oSp
        [.oOmega] [.sample .oOmega, .sample .oSp, .foldOmega] a := by
  intro a τ b t ha hout ht hq
  have hX := x_of_on cs G ms N Pm₀ Oc oNo P sentU layU layO f l 10 a ha
  have hmem := membX_ten _ _ ((sharedX_parts P sentU layU layO 10 _).1 hX).2.2.1
  unfold memOf at hmem
  obtain ⟨G0, hG0, hmm⟩ := Option.map_eq_some_iff.1 hmem
  obtain ⟨m, hall, hc⟩ := core a τ b t ha hout ht hq G0 hG0
  have ltO := x_numbers P sentU layU layO 10 (.inr rfl) _ hX hsU hsO sentU.size (.inr (.inl rfl))
  have ltS := x_numbers P sentU layU layO 10 (.inr rfl) _ hX hsU hsO (sentU.size + 1)
    (.inr (.inr rfl))
  refine ⟨m, hc, rows_ten Q n num a.1.2 G0 hG0 (hK a ha) _ hall ?_ a.1.2.st.oracles[sentU.size] ?_ ?_
    a.1.2.st.oracles[sentU.size + 1] ?_⟩
  · rw [hnO, hmm]
    simp
  · rw [hnO]
    exact Array.getElem?_eq_getElem ltO
  · rw [hnS, hmm]
    simp
  · rw [hnS]
    exact Array.getElem?_eq_getElem ltS

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.seam_nine
#print axioms Desc.K14.Law.Fence.seam_ten
