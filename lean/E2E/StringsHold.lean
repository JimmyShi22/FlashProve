-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/StringsHold.lean: what a produced proof of the scheme (Johnson/WholeKey/Defs.lean) opens of the
committed tables: exactly the positions that the verifier reads.

Summary. That a proof is produced says nothing about its content. The compiled prover's text fixes
what it opens (`finish`, `extK`, OnBytes/Prover/Defs.lean), and the committer and the prover give it
the encoder's tables `L.encodeIndex i r` (`commitAt`, `linkO`, `proveAt`), whatever the provers' strategies
send. The results hold for any interface and wiring, any three provers, all oracle functions, all
coins and all search limits. No probability occurs.

Main results.
  `opens_of_prove`: whatever the compiled prover of one slot returns satisfies `OpensOf`, at the
    verifier messages of the transcript as it was hashed.
  `OpensOf Q wq x y xt π ρ` states: at each position p that the verifier reads for the instance x
    and the verifier messages ρ, `π.ext p` is the symbol at p of the external strings y, with the
    salt of its leaf and the leaf's path in the trees xt; at every other position it is nothing.
    Where nothing is read, it says that nothing is opened.
  `key_opens`, `link_opens`, `session_opens`: a produced proof for the first table, for the link of
    the copy at a given place, or for a session satisfies `OpensOf`, at some verifier messages ρ,
    with y := `L.encodeIndex i c.r`, `(L.encodeIndex i c.r, L.encodeIndex i e.r)` or `L.encodeIndex i e.r`, where i is the index and
    e the copy at the sampled place. By the lemmas of Johnson/WholeKey/Complete.lean on values under
    fixed oracle functions.

Terms: E2E/HidingTerms.lean.

Limits. This file does not prove:
- that anything is read (at the verifier's parameters: E2E/StringsHoldAtInput.lean,
  E2E/StringsHoldLink.lean);
- how many columns are opened, or which: the positions depend on the verifier messages;
- anything about `π.opens`, the openings of the strategies' own oracle messages, or about the plain
  parts;
- that a column tells anything about the index, or nothing;
- that a proof is produced, or that the verifier accepts it;
- anything on completeness, on soundness or on what is hidden.

Definitions and helper lemmas.
  `shown_some`: what is given out as a proof is what a run returned.


-/
import Johnson.WholeKey.Complete

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.Shown
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## 1. One slot -/

section One
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}
variable (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L)
  (σ : Strat Q.loc.shape Unit) (co : Coins lam L) (cap : ℕ → ℕ)

/-- **What a proof opens of the external strings y**, at the verifier messages ρ: at each position
that the verifier reads: the symbol of y there, with the salt of its leaf and the leaf's path, out
of the trees xt; at every other position nothing. -/
def OpensOf (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape) : Prop :=
  (∀ p, p ∈ Q.loc.extReads x ρ → π.ext p = some ⟨E.rd y p,
      ((xt (wq.ext.which p)).inp (wq.ext.leaf p)).salt,
      pathOf (xt (wq.ext.which p)).lv (wq.ext.leaf p)⟩) ∧
    ∀ p, p ∉ Q.loc.extReads x ρ → π.ext p = none

/-- **Whatever the compiled prover of one slot returns opens just that**, at the verifier messages
of the transcript as it was hashed: for all oracle functions, strategies, coins and search
limits. -/
theorem opens_of_prove (g : Fam (typedOracleFamily lam K L)) (π : OneProtocolProof lam Q) (τ : Tr Q.loc.shape)
    (h : (proveX t Q wq embS embP xin cms x y xt σ co cap).det g = .ok (π, τ)) :
    OpensOf Q wq x y xt π τ.rho := by
  unfold proveX at h
  rw [OComp.det_bind] at h
  cases hz : (chainO t cms (xin x) co cap Q.loc.shape Q.ann wq.sh embS embP 0 .first σ).det g with
  | noFormat => rw [hz] at h; cases h
  | ranOut j => rw [hz] at h; cases h
  | ok z =>
    rw [hz] at h
    have h' : (Res.ok (finish Q wq x y xt co z, trK Q.loc.shape z.2.1 z.1) :
        Res (OneProtocolProof lam Q × Tr Q.loc.shape)) = .ok (π, τ) := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Res.ok.inj h')
    rw [rho_trK]
    constructor
    · intro p hp
      simp only [finish, extK]
      split
      · rfl
      · rename_i hn
        exact absurd (by simpa using hp) hn
    · intro p hp
      simp only [finish, extK]
      split
      · rename_i hy
        exact absurd (by simpa using hy) hp
      · rfl

end One

/-! ## 2. The scheme, for any three provers -/

theorem shown_some {P : Type} {s : Shape} {stop : Rho s → Bool} {r : Res (P × Tr s)} {π : P}
    (h : shown stop r = some π) : ∃ τ, r = .ok (π, τ) := by
  cases r with
  | noFormat => cases h
  | ranOut j => cases h
  | ok a =>
    have h' : (if stop a.2.rho then none else some a.1) = some π := h
    split at h'
    · cases h'
    · obtain rfl := Option.some.inj h'
      exact ⟨a.2, rfl⟩

section Whole
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)
  (g : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))

/-- **A produced proof for the first table opens the columns of the encoder's table of the index i
that the verifier reads at some verifier messages**, and nothing else of the table: for all oracle
functions and all coins. -/
theorem key_opens (i : I) (c : DrawC lam L Bd aT aL h.KT h.KL) (π : OneProtocolProof lam (batTC L aT))
    (hπ : ((commitAt W S cA h i c).det g).1.piT = some π) :
    ∃ ρ, OpensOf (batTC L aT) (wTC W) (L.recOf i c.r (tabG W S h g i c.r c.s).seed) (L.encodeIndex i c.r)
      (fun _ => (tabG W S h g i c.r c.s).tree) π ρ := by
  rw [det_commitAt] at hπ
  obtain ⟨τ, hτ⟩ := shown_some hπ
  exact ⟨τ.rho, opens_of_prove _ _ _ _ _ _ _ _ _ _ _ _ _ g π τ hτ⟩

/-- **A produced link proof for the copy at place j opens the columns of the encoder's two tables of
the index i that the verifier reads at some verifier messages**: the first table's and that copy's.
-/
theorem link_opens (i : I) (c : DrawC lam L Bd aT aL h.KT h.KL) (j : ℕ)
    (e : DrawCopy lam L Bd aT aL h.KL) (hj : c.copies[j]? = some e)
    (l : Dig lam × L.Rec × Option (OneProtocolProof lam (batLC L aL)))
    (hl : ((commitAt W S cA h i c).det g).1.links[j]? = some l) (π : OneProtocolProof lam (batLC L aL))
    (hπ : l.2.2 = some π) :
    ∃ ρ, OpensOf (batLC L aL) (wLC W)
      (L.recOf i c.r (tabG W S h g i c.r c.s).seed, L.recOf i e.r (tabG W S h g i e.r e.s).seed)
      (L.encodeIndex i c.r, L.encodeIndex i e.r)
      (fun k => if k = 0 then (tabG W S h g i c.r c.s).tree else (tabG W S h g i e.r e.s).tree)
      π ρ := by
  rw [det_commitAt] at hl
  have hl' : (c.copies.map fun e => (linkO W cA h i (tabG W S h g i c.r c.s)
      (tabG W S h g i e.r e.s) e).det g)[j]? = some l := hl
  rw [List.getElem?_map, hj, Option.map_some, det_linkO] at hl'
  obtain rfl := Option.some.inj hl'
  obtain ⟨τ, hτ⟩ := shown_some hπ
  exact ⟨τ.rho, opens_of_prove _ _ _ _ _ _ _ _ _ _ _ _ _ g π τ hτ⟩

/-- **A produced proof of a session opens the columns that the verifier reads, at some verifier
messages, of the encoder's table of the index i for the copy at the sampled place.** -/
theorem session_opens (i : I) (x : X) (c : DrawC lam L Bd aT aL h.KT h.KL)
    (e : DrawCopy lam L Bd aT aL h.KL) (dP : DrawP lam L Bd aT aL h.KB)
    (hj : c.copies[dP.j]? = some e) (π : OneProtocolProof lam L.onlineBatch)
    (hπ : ((proveAt W cA r₀ h ((commitAt W S cA h i c).det g).2 x dP).det g).piB = some π) :
    ∃ ρ, OpensOf L.onlineBatch (wBC W) (x, L.recOf i e.r (tabG W S h g i e.r e.s).seed) (L.encodeIndex i e.r)
      (fun _ => (tabG W S h g i e.r e.s).tree) π ρ := by
  have ht : ((commitAt W S cA h i c).det g).2.copies[dP.j]? = some (tabG W S h g i e.r e.s) := by
    rw [det_commitAt]
    show (c.copies.map fun e => tabG W S h g i e.r e.s)[dP.j]? = _
    rw [List.getElem?_map, hj]
    rfl
  rw [det_proveAt W cA r₀ h g _ x dP _ ht] at hπ
  obtain ⟨τ, hτ⟩ := shown_some hπ
  have hi : ((commitAt W S cA h i c).det g).2.i = i := by rw [det_commitAt]
  rw [hi] at hτ
  exact ⟨τ.rho, opens_of_prove _ _ _ _ _ _ _ _ _ _ _ _ _ g π τ hτ⟩

end Whole

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.shown_some
#print axioms AtPublicFiles.Shown.key_opens
#print axioms AtPublicFiles.Shown.link_opens
#print axioms AtPublicFiles.Shown.session_opens
#print axioms AtPublicFiles.Shown.opens_of_prove
