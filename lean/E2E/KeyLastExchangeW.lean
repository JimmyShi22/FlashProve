-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastExchangeW.lean: the exchange at the last chain's first member where the words are read off the witness through the
record (the library's `words`, `Reads`, `DotSem`: Johnson/Desc/Third/Law/Row0Words.lean): a message's number in a statement goes to a
component of the witness by the record's book, so the record behind and the record in front may read differently. The forward
twin of `row0_backW`.

  `row0_forthW`: behind a yes.
  `exchangeS_firstW`: `ExchangeS` at member 0 of a last thread whose letter `ML` says `RowsHold` through the record.

What stays open. The family `words`, `omW`, `wv`, the fence `Ok`, and `hrows`, `hdot`, `hat` at a stand.
Nothing on soundness, completeness, hiding or binding.
-/
import E2E.KeyLastExchange
import Johnson.Desc.Third.Law.Row0Words

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLastChain
open OnBytes OnBytes.Params
open OnBytes.Means (Words)
open ProofFile.Honest
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Third (S₃ P₁₄ batchLinearConstraintsSecondPart)
open VerifiableInference.Desc.Third.Law (Says AtDot Names RowsHold DotHolds Reads DotSem says_congr dotEq_congr
  law_k14Second)
open VerifiableInference.Desc.Last (ItemL)

section forth
variable {K : Type} [Field K] (ρ : Model.Reading K) {Wt : Type}

/-- **Behind a yes, with the words read through the record.** -/
theorem row0_forthW (p : P₁₄) (Ok : S₃ → S₃ → Prop) (words : S₃ → Wt → Words K) (omW wv : Wt → Nat → K)
    (hR : Reads p Ok words omW wv) (s s' : S₃) (ok : Ok s s') (h : Says p s s')
    (hk : VerifiableInference.Desc.Later.Carries s.st s'.st) (a : AtDot p s) (n : Names s) (w : Wt)
    (hs : RowsHold ρ s (words s w)) (hd : DotSem ρ p omW wv s w) : RowsHold ρ s' (words s' w) := by
  refine row0_forth ρ p s s' h hk a n (words s' w) (fun G hG r hr => ?_) ?_
  · exact (says_congr ρ s.st r _ _ (hR.older s s' w ok h)).2 (hs G hG r hr)
  · obtain ⟨b, hb, he⟩ := hd
    exact ⟨b, hb, dotEq_congr _ _ _ _ _ _ _ _ (fun y hy => (hR.omega s s' w ok h y hy).symm)
      (fun c hc => (hR.w s s' w ok h c hc).symm) he⟩

end forth

section exchange
variable {Bk : ProverCoinCounts} {S₂ Cl W₀ Rc Ix Tr X P₁ Wt K : Type} [Field K] (ρ : Model.Reading K)
  (L : LastThread.Letters Bk S₂ S₃ Cl W₀ Rc Ix Tr X P₁ Wt) (p : P₁₄)
  (Ok : S₃ → S₃ → Prop) (words : S₃ → Wt → Words K) (omW wv : Wt → Nat → K)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc Ix Tr) X → Prop)

/-- **The exchange at member 0, with the words read through the record.** -/
theorem exchangeS_firstW
    (hblk : ∀ blk, L.thread.bs[0]? = some blk →
      blk.rounds = [] ∧ blk.decide = (batchLinearConstraintsSecondPart p : Block S₃ Cl).decide)
    (hML : ∀ s w, L.ML.rows s w ↔ RowsHold ρ s (words s w)) (hR : Reads p Ok words omW wv)
    (hok : ∀ k s m E s', ThrS L.thread Said 0 k s m E → Says p s s' → Ok s s')
    (hat : ∀ k s m E, ThrS L.thread Said 0 k s m E → AtDot p s ∧ Names s)
    (hrows : ∀ k s m E ds, ThrS L.thread Said 0 k s m E →
      RowsHold ρ s (words s (L.thread.wit k m.st.input (m.st.heard ++ ds))))
    (hdot : ∀ k s m E ds, ThrS L.thread Said 0 k s m E →
      DotSem ρ p omW wv s (L.thread.wit k m.st.input (m.st.heard ++ ds))) :
    ExchangeS L.thread Said 0 := by
  intro blk hb k s m E ds y cols s' hT hd hS ds' i hi
  obtain ⟨hr, hdec⟩ := hblk blk hb
  have hi' : i = ItemL.rows := by
    have ho : (LastRows.rows 0).owes = [ItemL.rows] := by decide
    have hi₂ : i ∈ (LastRows.rows 0).owes := hi
    rw [ho] at hi₂
    exact List.mem_singleton.1 hi₂
  subst hi'
  obtain ⟨hM, hst⟩ := hS
  rw [hr] at hd
  obtain rfl : ds = [] := by
    cases ds with
    | nil => rfl
    | cons _ _ => cases hd
  obtain ⟨⟨l, -, hy⟩, hc⟩ := hM
  have hym : y = ([], m) := by
    cases l with
    | nil =>
      simp only [play] at hy
      cases hy
      rfl
    | cons _ _ => simp [play] at hy
  subst hym
  obtain ⟨gs, hdc⟩ := _root_.Desc.K14.Law.step_decides _ blk s s' _ cols _ hst
  rw [hdec] at hdc
  have hk := (law_k14Second (Cl := Cl) p).1 _ _ _ _ hdc
  have hsay := (law_k14Second (Cl := Cl) p).2 _ _ _ _ hdc
  obtain ⟨ha, hn⟩ := hat k s m E hT
  show L.ML.rows s' (L.thread.wit k m.st.input (m.st.heard ++ ds'))
  exact (hML _ _).2 (row0_forthW ρ p Ok words omW wv hR s s' (hok k s m E s' hT hsay) hsay hk ha hn _
    (hrows k s m E ds' hT) (hdot k s m E ds' hT))

end exchange

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.row0_forthW
#print axioms AtPublicFiles.KeyLastChain.exchangeS_firstW
