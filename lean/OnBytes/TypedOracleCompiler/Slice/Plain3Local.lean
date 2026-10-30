-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Plain3Local.lean.
TWO: CUT OVER THE SIBLING's RD (a list of trees a round) after a file of this project that is not in
this library; the head below is that file's, to the letter but for the paths of files that are not
in this library; a wiring IS given: Plain3Wire.lean.

A file of this project that is not in this library: the verifier of the protocol in three stretches
is local, for every
decision.

The decision of `Plain3 G dec` (here OnBytes/TypedOracleCompiler/Slice/Plain3.lean's; the head's own file is not in
this library) depends on the prover's oracles and on
the stored table only at the positions that the protocol names as read (Iop/InteractiveOracleProof.lean: `IsLocal`).
This holds by the form of the three views and of the test on the stored table's symbols: each column
that a view shows, and each symbol that the test looks at, stands at a position that the drawn
positions ask for, and the positions read are all of these. There is no hypothesis: not on the
decision, not on the lists of rounds, not on the keys, not on the seams. A tree may be opened behind
several rounds, and by another stretch than the one that sent it.

Main theorems: `okOn_congr`, `viewOn_congr` (one stretch), `Stretches.col_congr`, `plain3_local`.

Not claimed. Nothing on soundness. How many positions are read is not counted here.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Plain3Views
import Run.PlanQXLawsProofs

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open _root_.Iop TypedOracleCompiler.Run

/-! ## One stretch -/

section
variable (C : PQ.CK) (a : ℕ) (all ds : List PQ.RD) (xs : List PQ.XO)
  (y y' : Fin (2 ^ a) → PQ.SgX) (τ τ' : Tr (PQ.uL C ds))

/-- Two stretches with the same verifier messages have the same draws. -/
theorem drOn_congr (hρ : τ.rho = τ'.rho) : drOn C ds τ = drOn C ds τ' := by
  unfold drOn
  rw [PQ.rhoS_eq, PQ.rhoS_eq, hρ]

/-- If two stored tables agree at a position that is asked for, the test on the symbol's position
has the same outcome. -/
theorem carried_congr (q : Ask) (he : ∀ p, Ask.ext a q = some p → y p = y' p) :
    Ask.carried a y q = Ask.carried a y' q := by
  cases q with
  | own n x => rfl
  | stored k x =>
    show (if h : x < 2 ^ a then (y ⟨x, h⟩).1 == x else false) =
      (if h : x < 2 ^ a then (y' ⟨x, h⟩).1 == x else false)
    by_cases hx : x < 2 ^ a
    · rw [dif_pos hx, dif_pos hx, he ⟨x, hx⟩ (dif_pos hx)]
    · rw [dif_neg hx, dif_neg hx]

/-- If two stored tables agree at a position that is asked for, and two families of columns at a
tree's position that is asked for, a view shows the same entry. -/
theorem shown_congr (key : ℕ → ℕ) (col col' : ℕ → ℕ → Option (List UInt64)) (q : Ask)
    (he : ∀ p, Ask.ext a q = some p → y p = y' p)
    (hc : ∀ n x, q = Ask.own n x → col n x = col' n x) :
    Ask.shown a key y col q = Ask.shown a key y' col' q := by
  cases q with
  | own n x =>
    show (col n x).map _ = (col' n x).map _
    rw [hc n x rfl]
  | stored k x =>
    show (if h : x < 2 ^ a then some (k, x, (y ⟨x, h⟩).2) else none) =
      (if h : x < 2 ^ a then some (k, x, (y' ⟨x, h⟩).2) else none)
    by_cases hx : x < 2 ^ a
    · rw [dif_pos hx, dif_pos hx, he ⟨x, hx⟩ (dif_pos hx)]
    · rw [dif_neg hx, dif_neg hx]

/-- The three tests on a stretch depend on the verifier messages, and on the stored table where the
draws ask for it. -/
theorem okOn_congr (hρ : τ.rho = τ'.rho)
    (he : ∀ q ∈ asksL a all xs 0 ds (drOn C ds τ), ∀ p, Ask.ext a q = some p → y p = y' p) :
    okOn C a all ds xs y τ = okOn C a all ds xs y' τ' := by
  have hd := drOn_congr C ds τ τ' hρ
  have hc : carries1 a all ds xs (drOn C ds τ) y = carries1 a all ds xs (drOn C ds τ) y' :=
    PQ.all_congr_mem _ _ _ fun q hq => carried_congr a y y' q (he q hq)
  unfold okOn
  rw [hc, ← hd, PQ.rhoS_eq, PQ.rhoS_eq, hρ]

/-- The view of a stretch depends on the verifier messages, the plain parts, and the stored table
and the columns where the draws ask for them. -/
theorem viewOn_congr (key : ℕ → ℕ) (col col' : ℕ → ℕ → Option (List UInt64))
    (hρ : τ.rho = τ'.rho) (hp : τ.plains = τ'.plains)
    (he : ∀ q ∈ asksL a all xs 0 ds (drOn C ds τ), ∀ p, Ask.ext a q = some p → y p = y' p)
    (hc : ∀ n x, Ask.own n x ∈ asksL a all xs 0 ds (drOn C ds τ) → col n x = col' n x) :
    viewOn C a all ds xs key y col τ = viewOn C a all ds xs key y' col' τ' := by
  unfold viewOn
  rw [PQ.rvS_congr C ds τ τ' hρ hp, ← drOn_congr C ds τ τ' hρ]
  congr 1
  exact PQ.filterMap_congr_mem _ _ _ fun q hq =>
    shown_congr a y y' key col col' q (he q hq) fun n x e => hc n x (e ▸ hq)

end

/-! ## Three stretches -/

/-- Two transcripts that agree at the position of a column have the same column there. -/
theorem Stretches.col_congr (G : Stretches) (τ τ' : Tr G.sh) (n x : ℕ)
    (h : ∀ p, G.pos n x = some p → τ.read p = τ'.read p) :
    G.col (G.tr₁ τ) (G.tr₂ τ) (G.tr₃ τ) n x = G.col (G.tr₁ τ') (G.tr₂ τ') (G.tr₃ τ') n x := by
  unfold Stretches.col
  unfold Stretches.pos at h
  by_cases h1 : n < nTrees G.ds₁
  · rw [if_pos h1, if_pos h1]
    rw [if_pos h1] at h
    exact PQ.colAtS_congr G.C G.ds₁ _ _ _ _ fun p hp =>
      (G.read_in₁ τ τ' p).1 (h _ (by rw [hp]; rfl))
  · rw [if_neg h1, if_neg h1]
    rw [if_neg h1] at h
    by_cases h2 : n - nTrees G.ds₁ < nTrees G.ds₂
    · rw [if_pos h2, if_pos h2]
      rw [if_pos h2] at h
      exact PQ.colAtS_congr G.C G.ds₂ _ _ _ _ fun p hp =>
        (G.read_in₂ τ τ' p).1 (h _ (by rw [hp]; rfl))
    · rw [if_neg h2, if_neg h2]
      rw [if_neg h2] at h
      exact PQ.colAtS_congr G.C G.ds₃ _ _ _ _ fun p hp =>
        (G.read_in₃ τ τ' p).1 (h _ (by rw [hp]; rfl))

/-- The verifier is local, for every decision. -/
theorem plain3_local (G : Stretches) (dec : PQ.View → PQ.View → PQ.View → Bool) :
    (Plain3 G dec).IsLocal := by
  intro x y y' τ τ' hρ hp he hr
  have he' : ∀ q ∈ G.asksAt τ.rho, ∀ p, Ask.ext G.a q = some p → y p = y' p := fun q hq p h =>
    he p (List.mem_toFinset.2 (List.mem_filterMap.2 ⟨q, hq, h⟩))
  have hc : ∀ n x, Ask.own n x ∈ G.asksAt τ.rho →
      G.col (G.tr₁ τ) (G.tr₂ τ) (G.tr₃ τ) n x = G.col (G.tr₁ τ') (G.tr₂ τ') (G.tr₃ τ') n x :=
    fun n x hq => G.col_congr τ τ' n x fun p h =>
      hr p (List.mem_toFinset.2 (List.mem_filterMap.2 ⟨_, hq, h⟩))
  have r1 : (G.tr₁ τ).rho = (G.tr₁ τ').rho := by rw [G.rho_tr₁, G.rho_tr₁, hρ]
  have r2 : (G.tr₂ τ).rho = (G.tr₂ τ').rho := by rw [G.rho_tr₂, G.rho_tr₂, hρ]
  have r3 : (G.tr₃ τ).rho = (G.tr₃ τ').rho := by rw [G.rho_tr₃, G.rho_tr₃, hρ]
  have m1 : ∀ q ∈ asksL G.a G.all G.xs₁ 0 G.ds₁ (drOn G.C G.ds₁ (G.tr₁ τ)), q ∈ G.asksAt τ.rho :=
    fun q hq => by rw [G.dr_tr₁] at hq; exact List.mem_append_left _ hq
  have m2 : ∀ q ∈ asksL G.a G.all G.xs₂ 0 G.ds₂ (drOn G.C G.ds₂ (G.tr₂ τ)), q ∈ G.asksAt τ.rho :=
    fun q hq => by
      rw [G.dr_tr₂] at hq; exact List.mem_append_right _ (List.mem_append_left _ hq)
  have m3 : ∀ q ∈ asksL G.a G.all G.xs₃ 0 G.ds₃ (drOn G.C G.ds₃ (G.tr₃ τ)), q ∈ G.asksAt τ.rho :=
    fun q hq => by
      rw [G.dr_tr₃] at hq; exact List.mem_append_right _ (List.mem_append_right _ hq)
  rw [G.accept_eq, G.accept_eq]
  unfold Stretches.accOn Stretches.view₁ Stretches.view₂ Stretches.view₃
  rw [okOn_congr G.C G.a G.all G.ds₁ G.xs₁ y y' _ _ r1 fun q hq => he' q (m1 q hq),
    okOn_congr G.C G.a G.all G.ds₂ G.xs₂ y y' _ _ r2 fun q hq => he' q (m2 q hq),
    okOn_congr G.C G.a G.all G.ds₃ G.xs₃ y y' _ _ r3 fun q hq => he' q (m3 q hq),
    viewOn_congr G.C G.a G.all G.ds₁ G.xs₁ y y' _ _ G.key₁ _ _ r1 (G.plains_tr₁ τ τ' hp)
      (fun q hq => he' q (m1 q hq)) fun n x hq => hc n x (m1 _ hq),
    viewOn_congr G.C G.a G.all G.ds₂ G.xs₂ y y' _ _ G.key₂ _ _ r2 (G.plains_tr₂ τ τ' hp)
      (fun q hq => he' q (m2 q hq)) fun n x hq => hc n x (m2 _ hq),
    viewOn_congr G.C G.a G.all G.ds₃ G.xs₃ y y' _ _ G.key₃ _ _ r3 (G.plains_tr₃ τ τ' hp)
      (fun q hq => he' q (m3 q hq)) fun n x hq => hc n x (m3 _ hq)]

end TypedOracleCompiler.Slice
