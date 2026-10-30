-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
The premises are not shown to be satisfiable; and the piece's errors are asked to be the law's own
list: at a piece that bears the cap: Johnson/Desc/First/Look/K3CallsStatedCap.lean.
Johnson/Desc/First/Look/K3CallsStated.lean: THE CALLS' END THEOREMS AT WHAT IS SEATED: at a piece
that holds "below B'", B' any block that narrows the value of K3.theStated at the address of a
link's lookup on the calls. Two theorems: attention, the layers. Carriages: k3_att_goodIn_via and
k3_lay_goodIn_via laid into k3_seated_goodIn (Johnson/Desc/Sound/K3Seated.lean).
NO SOUNDNESS OF THE PROTOCOL IS CLAIMED.

OBJECT: the value B of K3.theStated claim readers X codes shape a
  (Johnson/Desc/First/Look/K3Stated.lean), and any block B' that narrows it (what a seat lays: a
  guard on the mark, another name).
USER: K3CallsStatedCap.lean (k3_att_stated, k3_lay_stated); K3CallsStatedYes.lean, K3HeadStated.lean
  and others (quiet_calls_same).
LETTERS: a: an address with a.link = some i, a.piece = K3.pieceAt X i false; x: ANY place whose
  parameters are placeAt X i false's value (lookAt X i false's own value is one; so is its copy with
  the made record laid anew); the setting: Params.settingOf X.P.frame; guests := [].

How it goes. k3_seated_goodIn asks the kind's law at below (K3.Law.blockVia (K3.seatOfLookupOnDigitsOrCalls claim
digits) a.piece laid sent P []) at the address's own arguments. At the calls' address digits is
false (the two pieces' numbers part), seatOfLookupOnDigitsOrCalls claim false is seatCalls claim, and P is
P.ofPlace (settingOf X.P.frame) false x. The step behind the lookup: none at an attention link and
at the head; at a layers' link a test that returns the record itself (quietLook_ok): so the
condition and the relation behind stay as they are.

Limits. hOk: the seated block's own test on the plan says yes: a public premise (the carriage hands
blockVia's planOk on from it). The premises on the readers of samples are asked at every pair of
arguments (what must have been sent; the count of padding places) AT WHICH blockVia's OWN TEST ON
THE PLAN SAYS YES. All other premises of the two
_via theorems stay. That B' narrows B is a premise. The lift over the public part is not here.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.Sound.K3Seated
import Johnson.Desc.First.Look.K3QuietLaws
import Johnson.Desc.First.Look.K3AttVia
import Johnson.Desc.First.Look.K3LayVia

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-- The two lookups of a link stand at two pieces. -/
theorem pieceAt_ne (X : Verify.Public) (i : ℕ) :
    Desc.K3.pieceAt X i true ≠ Desc.K3.pieceAt X i false := by
  unfold Desc.K3.pieceAt
  split <;> decide

/-- **Behind the lookup on the calls no step turns the record.** -/
theorem quiet_calls_same (X : Verify.Public) (a : Desc.Place) (i : ℕ) (hl : a.link = some i)
    (hp : a.piece = Desc.K3.pieceAt X i false) (f : Desc.First.S → Except String Desc.First.S)
    (hf : (a.link.bind fun j => Desc.K3.quietAt X j (a.piece == Desc.K3.pieceAt X j true)) = some f)
    (s t : Desc.First.S) (h : f s = .ok t) : t = s := by
  rw [hl] at hf
  have e : (a.piece == Desc.K3.pieceAt X i true) = false := by
    rw [hp]
    exact beq_false_of_ne (pieceAt_ne X i).symm
  have hf' : Desc.K3.quietAt X i false = some f := by
    rw [← e]
    exact hf
  have key : f = Desc.K3.quietLook X.y.fo := by
    unfold Desc.K3.quietAt at hf'
    dsimp only at hf'
    simp only [Bool.false_eq_true, if_false] at hf'
    split at hf'
    · cases hf'
    · split at hf'
      all_goals first
        | exact (Option.some.inj hf').symm
        | cases hf'
        | (split at hf' <;> first | exact (Option.some.inj hf').symm | cases hf')
  subst key
  exact (Desc.K3.quietLook_ok _ s t h).1

section
variable {Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {X : Verify.Public} {i : ℕ} {x : Desc.First.Look.Place} {A : Attention.Shape} {tl : HTailF2}
  {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x
local notation "theR" => attRider x A tl D rad extNone Unit

/-- **THE END THEOREM AT WHAT IS SEATED, at an attention link.** -/
theorem k3_att_stated (claim : Aff → Cl) (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
    (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place)
    (B B' : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (hN : B'.Narrows B)
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) (hp : p.b = below B')
    (hl : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i false)
    (e : placeAt X i false = some theP)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w)
    (H : AttOK (Params.settingOf X.P.frame) x A tl D rad)
    (hr : (theP).entries.isSome = true) (hR : List.Forall₂ SameAs p.ds (theP).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [theR]).ε theR) = some p.err)
    (hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smp s' = smp s)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) :
    p.GoodIn
      (AttOn G x D rad seatT smp (Desc.K3.seatCalls claim).fork (OwnIs D x.link))
      (AttOn' G x D rad seatT smp (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link))
      (AttFront G x A tl D rad seatT arr smp)
      (AttBehind G x A tl D rad seatT arr smp (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard) := by
  refine k3_seated_goodIn claim readers X codes shape a B B' h hOk hN p hp _
    (AttOn' G x D rad seatT smp (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard
      (OwnIs D x.link)) _ _
    (AttBehind G x A tl D rad seatT arr smp (Desc.K3.seatCalls claim).fork
      (Desc.K3.seatCalls claim).heard) _ ?_ ?_ ?_
  · intro j digits P sent laid hj hpj hP _ _ hplan
    obtain rfl : i = j := Option.some.inj (hl.symm.trans hj)
    cases digits with
    | true => exact absurd (hpj.symm.trans hpc) (pieceAt_ne X i)
    | false =>
      have eP : P = theP := Option.some.inj (hP.symm.trans e)
      subst eP
      exact k3_att_goodIn_via G seatT arr smp claim a.piece laid sent [] _ rfl
        hplan hback hext H hr hR hε (hsmp sent laid hplan) hseat σ₀
  · intro f hf s' t y ht ho
    obtain rfl := quiet_calls_same X a i hl hpc f hf s' t ht
    exact ⟨ho, fun _ hw => hw⟩
  · intro _
    exact ⟨fun _ hb => hb, fun _ _ hw => hw⟩

end

section
variable {Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {X : Verify.Public} {i : ℕ} {x : Desc.First.Look.Place} {q : LayPub} {tl : HTailF2}
  {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E}
  {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  (smpW : Desc.First.S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg)

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x
local notation "theR" => layRider x q tl D rad oW wOf nr nc extNone Unit

/-- **THE END THEOREM AT WHAT IS SEATED, at a layers' link.** -/
theorem k3_lay_stated (claim : Aff → Cl) (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
    (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place)
    (B B' : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (hN : B'.Narrows B)
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) (hp : p.b = below B')
    (hl : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i false)
    (e : placeAt X i false = some theP)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w)
    (H : LayOK (Params.settingOf X.P.frame) x)
    (hpl : (Forest.planeCols x.fs x.lm).toBool = true)
    (hr : (theP).entries.isSome = true) (hR : List.Forall₂ SameAs p.ds (theP).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [theR]).ε theR) = some p.err)
    (hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smp s' = smp s)
    (hsmpW : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smpW s' = smpW s)
    (hstrW : ∀ y (τ : Tr (uLT (ckP .two) p.ds)),
      strW (behind (ckP .two) Fr p.base p.ds y τ) = strW y)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp) :
    p.GoodIn
      (LayOn G x D rad oW seatT smp smpW strW (Desc.K3.seatCalls claim).fork (OwnIs D x.link))
      (LayOn' G x D rad oW seatT smp smpW strW (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link))
      (LayFront G x q tl D rad oW wOf nr nc seatT arr smp smpW strW msgW)
      (LayBehind G x q tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard) := by
  refine k3_seated_goodIn claim readers X codes shape a B B' h hOk hN p hp _
    (LayOn' G x D rad oW seatT smp smpW strW (Desc.K3.seatCalls claim).fork
      (Desc.K3.seatCalls claim).heard (OwnIs D x.link)) _ _
    (LayBehind G x q tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
      (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard) _ ?_ ?_ ?_
  · intro j digits P sent laid hj hpj hP _ _ hplan
    obtain rfl : i = j := Option.some.inj (hl.symm.trans hj)
    cases digits with
    | true => exact absurd (hpj.symm.trans hpc) (pieceAt_ne X i)
    | false =>
      have eP : P = theP := Option.some.inj (hP.symm.trans e)
      subst eP
      exact k3_lay_goodIn_via G seatT arr smp smpW strW msgW claim a.piece laid sent [] _ rfl
        hplan hback hext H hpl hr hR hε (hsmp sent laid hplan) (hsmpW sent laid hplan) hstrW
        hseat σ₀ σW₀
  · intro f hf s' t y ht ho
    obtain rfl := quiet_calls_same X a i hl hpc f hf s' t ht
    exact ⟨ho, fun _ hw => hw⟩
  · intro _
    exact ⟨fun _ hb => hb, fun _ _ hw => hw⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.quiet_calls_same
#print axioms VerifiableInference.OnPublicFiles.k3_att_stated
#print axioms VerifiableInference.OnPublicFiles.k3_lay_stated
