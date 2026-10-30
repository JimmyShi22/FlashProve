-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerByMake.lean: FOUR PREMISES OF THE SHARED CHAIN's LEDGER AT THE CAP
(ledger_at_cap, Johnson/Desc/K14/Law/LedgerAtCap.lean: hop · hf1 · hfb · hcap) ARE FACTS OF HOW A
DESCRIPTION's PIECES ARE MADE: no kind's law, no chance. Statements with their proofs.
  eachCapped_cutRow   the maker's cut at a family of extractors and errors that is at the cap
                      (AtCap, Johnson/Desc/Sound/BoundsAtCap.lean): each piece's errors are the cap
  hcap_of_cut         so at the shared row of a T that is the maker's (Three.IsCut)
  hop_of_own          where the pieces fit (Three.Fits: their data in a row are the chain's data):
                      what holds of every round of the chain's data holds of every round of every
                      piece: "it opens no tree below t₁"
  front_of_make       hf1 ∧ hfb: frontByMake
                      (Johnson/Desc/Sound/SharedJointCountFront.lean), at letters
  four_by_make        **the four binders, to the letter, at letters f, PT, MM** with
                      (atDesc F T).p₂ = f and (atDesc F T).l₂ = PT :: MM
  four_at_pieces      **the same at the maker's own value** T := piecesAt C F D …: OfDesc, Fits and
                      the cut ARE NO PREMISES THERE: paidAtDesc
                      (Johnson/Desc/Sound/PaidAtDesc.lean) from F.data file = .ok D and F.sealLast
OBJECT   (atDesc F T).p₂ :: (atDesc F T).l₂, F any description
USER     ledger_at_cap's hop · hf1 · hfb · hcap: not called here
LEFT     at four_at_pieces: F.data file = .ok D · F.sealLast = true · the three chains' blocks by
         name · AtCap rest₂ (restCap pays it: atCap_restCap) · the shared chain's first block says
         "ok" and declares no round (quiet_ok) · N.lo = D.t₁ · the two equations of letters ·
         hown : ∀ d ∈ D.ds₂, ∀ j ∈ d.opens, D.t₁ ≤ j: THE END OF opens_own_stretch
         (Johnson/Desc/K12/Law/OpensOwn.lean: from F.data file = .ok D alone): NOT CALLED HERE:
         it is called in Johnson/Desc/K14/Law/LedgerOpensOwn.lean (hown_of_data).
What is not claimed. That the seated description's T is the maker's at the cap. Nothing on
soundness.

-/
import Johnson.Desc.Sound.SharedJointCountFront
import Johnson.Desc.Sound.SharedJointCountRowE
import Johnson.Desc.Sound.BoundsAtCap
import Johnson.Desc.Sound.PaidAtDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open _root_.Iop (Err)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared

/-! ## 1 The cap -/

/-- **The maker's cut at the cap.** -/
theorem eachCapped_cutRow {C : CK} {F : Frame} {S Cl W : Type}
    (rest : (i : ℕ) → (ds : List RDT) → Rest C F S W ds) (hc : AtCap rest)
    (putBack : List Fmt.RoundView) : ∀ (l : List (Block S Cl)) (b : Block S Cl) (i base : ℕ)
      (ds : List RDT), EachCapped 128
        ((cutRow rest putBack i base ds b l).1 :: (cutRow rest putBack i base ds b l).2)
  | [], b, i, base, ds => fun p hp => by
    obtain rfl : p = pieceOf b base ds putBack (rest i ds) := by
      simpa [cutRow] using hp
    exact hc i ds
  | b' :: l, b, i, base, ds => fun p hp => by
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hc i _
    · exact eachCapped_cutRow rest hc putBack l b' (i + 1) _ _ p hp

section
variable {C : CK} {D : WholeD} {all : List LeftT} {Y S₁ S₂ S₃ X₁ X₂ Cl W : Type}
  (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W)

/-- **hcap, at a T that is the maker's.** -/
theorem hcap_of_cut (b₂ : Block S₂ Cl) (l₂ : List (Block S₂ Cl))
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest C (frameAt D all D.key₂ T.ft₂) S₂ W ds)
    (hc₂ : (T.p₂, T.l₂) = cutRow rest₂ [] 0 D.t₁ D.ds₂ b₂ l₂) (hc : AtCap rest₂) :
    EachCapped 128 (T.p₂ :: T.l₂) := by
  have h1 : T.p₂ = _ := congrArg Prod.fst hc₂
  have h2 : T.l₂ = _ := congrArg Prod.snd hc₂
  rw [h1, h2]
  exact eachCapped_cutRow rest₂ hc [] l₂ b₂ 0 D.t₁ D.ds₂

/-! ## 2 The trees that are opened -/

/-- **hop, where the pieces fit.** -/
theorem hop_of_own (hf : T.Fits) (hown : ∀ d ∈ D.ds₂, ∀ j ∈ d.opens, D.t₁ ≤ j) :
    ∀ x ∈ T.p₂ :: T.l₂, ∀ d₀ ∈ x.ds, ∀ j ∈ d₀.opens, D.t₁ ≤ j := fun x hx d₀ hd j hj =>
  hown d₀ (by
    rw [← hf.data₂]
    exact List.mem_flatMap.2 ⟨x, hx, hd⟩) j hj

end

/-! ## 3 At a description, at letters -/

section
variable {C : CK} {D : WholeD} {all : List LeftT} {Xi X₁ X₂ Wt : Type} (F : FileDescription Xi)
  (T : ThreeAt C D all F X₁ X₂ Wt)
  (f PT : Piece C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl Wt)
  (MM : List (Piece C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) F.Cl Wt))
  (hp : (atDesc F T).p₂ = f) (hl : (atDesc F T).l₂ = PT :: MM)
include hp hl

/-- **hf1 ∧ hfb.** -/
theorem front_of_make (hO : OfDesc F T) (hf : (atDesc F T).Fits) (fb : Block F.S₂ F.Cl)
    (rest : List (Block F.S₂ F.Cl)) (hfl : F.shared.blocksInOrder = fb :: rest)
    (hok : ∀ s rs gs, fb.decide s rs gs = .ok s) (hr : fb.rounds = []) :
    (∀ a τ b, f.ior.red.out a τ = some b → b.1 = a.1) ∧ PT.base = f.base := by
  subst hp
  exact frontByMake C D all Xi X₁ X₂ Wt F T fb rest PT MM hO hf hfl hok hr hl

/-- **THE FOUR BINDERS, TO THE LETTER.** -/
theorem four_by_make (hO : OfDesc F T) (hf : (atDesc F T).Fits) (fb : Block F.S₂ F.Cl)
    (rest : List (Block F.S₂ F.Cl)) (hfl : F.shared.blocksInOrder = fb :: rest)
    (hok : ∀ s rs gs, fb.decide s rs gs = .ok s) (hr : fb.rounds = [])
    (b₂ : Block ((F.XiPub × F.S₁) × F.S₂) F.Cl) (l₂ : List (Block ((F.XiPub × F.S₁) × F.S₂) F.Cl))
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D all D.key₂ (atDesc F T).ft₂) ((F.XiPub × F.S₁) × F.S₂) Wt ds)
    (hc₂ : ((atDesc F T).p₂, (atDesc F T).l₂) = cutRow rest₂ [] 0 D.t₁ D.ds₂ b₂ l₂)
    (hc : AtCap rest₂) (hown : ∀ d ∈ D.ds₂, ∀ j ∈ d.opens, D.t₁ ≤ j) (N : NumbersS)
    (hlo : N.lo = D.t₁) :
    (∀ x ∈ MM, ∀ d₀ ∈ x.ds, ∀ j ∈ d₀.opens, N.lo ≤ j) ∧
      (∀ a τ b, f.ior.red.out a τ = some b → b.1 = a.1) ∧ PT.base = f.base ∧
      EachCapped 128 (f :: PT :: MM) := by
  obtain ⟨h1, h2⟩ := front_of_make F T f PT MM hp hl hO hf fb rest hfl hok hr
  refine ⟨fun x hx d₀ hd j hj => ?_, h1, h2, ?_⟩
  · rw [hlo]
    exact hop_of_own (atDesc F T) hf hown x
      (by rw [hl]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)) d₀ hd j hj
  · rw [← hp, ← hl]
    exact hcap_of_cut (atDesc F T) b₂ l₂ rest₂ hc₂ hc

end

/-! ## 4 At the maker's own value -/

/-- **THE FOUR BINDERS AT piecesAt.** -/
theorem four_at_pieces {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (hD : F.data file = .ok D) (hs : F.sealLast = true) (C : CK) (b₁ : Block F.S₁ F.Cl)
    (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl) (l₂ : List (Block F.S₂ F.Cl))
    (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl)) (h₁ : F.first.blocksInOrder = b₁ :: l₁)
    (h₂ : F.shared.blocksInOrder = b₂ :: l₂) (h₃ : F.second.blocksInOrder = b₃ :: l₃)
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest C (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber) ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (hc : AtCap rest₂) (hok : ∀ s rs gs, b₂.decide s rs gs = .ok s)
    (hr : b₂.rounds = []) (hown : ∀ d ∈ D.ds₂, ∀ j ∈ d.opens, D.t₁ ≤ j) (N : NumbersS)
    (hlo : N.lo = D.t₁)
    (f PT : Piece C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) F.Cl W)
    (MM : List (Piece C (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) F.Cl W))
    (hp : (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).p₂ = f)
    (hl : (atDesc F (piecesAt C F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)).l₂ = PT :: MM) :
    (∀ x ∈ MM, ∀ d₀ ∈ x.ds, ∀ j ∈ d₀.opens, N.lo ≤ j) ∧
      (∀ a τ b, f.ior.red.out a τ = some b → b.1 = a.1) ∧ PT.base = f.base ∧
      EachCapped 128 (f :: PT :: MM) := by
  obtain ⟨hO, hf, -⟩ := paidAtDesc Xi W F file D hD hs C b₁ l₁ b₂ l₂ b₃ l₃ h₁ h₂ h₃ rest₁ rest₂
    rest₃ d wEnd
  exact four_by_make F _ f PT MM hp hl hO hf b₂ l₂ h₂ hok hr (held b₂) (l₂.map held) rest₂ rfl hc
    hown N hlo

end Desc.K14.Law
