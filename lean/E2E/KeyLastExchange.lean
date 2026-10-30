-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
E2E/KeyLastExchange.lean: the exchange at the last chain's first member ("K14, second part"), forwards: from the open rows
in front and (Dot)'s equation, every open row of the own group behind the block holds. The library's `row0_back`
(Johnson/Desc/Third/Law/Row0.lean) goes backwards, for soundness; both halves of its two laws are 'iff's, so this is the
same proof read the other way.

Main names.
  `row0_forth`: behind a yes of the block.
  `exchangeS_first₃`: `ExchangeS` at member 0 of a last thread whose letter `ML` says `RowsHold`.

What stays open. That the rows in front hold and that (Dot)'s equation holds are premises `hrows`, `hdot`, read at the
thread's items: which term of the witness says so is the first chain's and the shared chain's matter. `AtDot` and `Names` at
the state are premises `hat`.
Nothing on soundness, completeness, hiding or binding.
-/
import Johnson.Desc.Third.Law.Row0
import Johnson.Desc.ProofFile.Honest.Thread.Last
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.K14.Law.Step

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyLastChain
open OnBytes OnBytes.Params
open OnBytes.Means (Words)
open ProofFile.Honest
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Third (S₃ P₁₄ batchLinearConstraintsSecondPart)
open VerifiableInference.Desc.Third.Law (Says AtDot Names RowsHold DotHolds own_same old_says dot_means
  law_k14Second)
open VerifiableInference.Desc.Last (ItemL)

section forth
variable {K : Type} [Field K] (ρ : Model.Reading K)

/-- **Behind a yes of the block, from the rows in front and (Dot)'s equation, the rows behind hold.** -/
theorem row0_forth (p : P₁₄) (s s' : S₃) (h : Says p s s') (hk : VerifiableInference.Desc.Later.Carries s.st s'.st)
    (a : AtDot p s) (n : Names s) (m : Words K) (hs : RowsHold ρ s m) (hd : DotHolds ρ p s m) :
    RowsHold ρ s' m := by
  intro G' hG' r hr
  rw [own_same p s s' h] at hG'
  obtain ⟨b, G, G₂, dot, hb, hG, hG₂, hrows, hm⟩ := dot_means ρ p s s' h a
  obtain rfl : G₂ = G' := Option.some.inj (hG₂.symm.trans hG')
  rw [hrows, Array.toList_push, List.mem_append] at hr
  rcases hr with hr | hr
  · exact (old_says ρ s s' hk r (n G hG r hr) m).2 (hs G hG r hr)
  · obtain rfl : r = dot := by simpa using hr
    obtain ⟨b', hb', he⟩ := hd
    obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
    exact (hm m).2 he

end forth

section exchange
variable {Bk : ProverCoinCounts} {S₂ Cl W₀ Rc Ix Tr X P₁ Wt K : Type} [Field K] (ρ : Model.Reading K)
  (L : LastThread.Letters Bk S₂ S₃ Cl W₀ Rc Ix Tr X P₁ Wt) (p : P₁₄) (words : Wt → Words K)
  (Said : Nat → Coins Bk → Mid (Local W₀ Rc Ix Tr) X → Prop)

/-- **The exchange at member 0.** hblk: the member decides as the library's block, and has no round. hML: what the letter
says. hat, hrows, hdot: at a stand of the pair, at every continuation. -/
theorem exchangeS_first₃
    (hblk : ∀ blk, L.thread.bs[0]? = some blk →
      blk.rounds = [] ∧ blk.decide = (batchLinearConstraintsSecondPart p : Block S₃ Cl).decide)
    (hML : ∀ s w, L.ML.rows s w ↔ RowsHold ρ s (words w))
    (hat : ∀ k s m E, ThrS L.thread Said 0 k s m E → AtDot p s ∧ Names s)
    (hrows : ∀ k s m E ds, ThrS L.thread Said 0 k s m E →
      RowsHold ρ s (words (L.thread.wit k m.st.input (m.st.heard ++ ds))))
    (hdot : ∀ k s m E ds, ThrS L.thread Said 0 k s m E →
      DotHolds ρ p s (words (L.thread.wit k m.st.input (m.st.heard ++ ds)))) :
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
  exact (hML _ _).2 (row0_forth ρ p s s' hsay hk ha hn _ (hrows k s m E ds' hT) (hdot k s m E ds' hT))

end exchange

end AtPublicFiles.KeyLastChain

#print axioms AtPublicFiles.KeyLastChain.row0_forth
#print axioms AtPublicFiles.KeyLastChain.exchangeS_first₃
