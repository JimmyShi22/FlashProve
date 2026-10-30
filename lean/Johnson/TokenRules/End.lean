-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRules/End.lean: TWO TOOLS FOR A COMPILED RUN AS A TOKEN PROGRAM: coins that are values
leave the state alone; and what is known of the two tokens of a leaf.

General lemmas. This file states no goal of the release. The token programs are a device of one step
of a proof of index privacy and stand in no statement on the scheme.

  safe_bitsT, safe_digT, safe_digsT, safe_drawD   The coins of a run that are values and no tokens
                 (the padding's and the slot's letters are fixed; the sibling digests and the string
                 behind the slot's value are drawn) keep the rules and leave the state as it is; and
                 there are as many sibling digests as the run's letters say.
  toksAt_some, toksAt_none   the tokens that are shown when a leaf is opened: the leaf's two tokens,
                 or none where the tree has no such leaf.
  toksAt_ok      each of them is a token of the tree; it exists; and what it depends on are the two
                 tokens themselves and the further tokens of the tree's leaves.
Johnson/TokenRules/EndC.lean calls them.
Limits. Tools alone: nothing is said here on a whole run.

-/
import Johnson.TokenRel.Rules

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenRules
open _root_.Compile hiding ON ON.leaf ON.node ON.ann ON.other
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.TokenRel
open _root_.Compile.GlueB (GCall GAdm)
open _root_.Compile.Disc (Rules nEv)
open _root_.Compile.Batch.Disc
open _root_.Compile.DeferRun (Marks)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks
open _root_.Compile.Disc
  (afterPlain afterFresh afterMark afterReveal length_afterFresh length_afterMark mem_evs_afterMark
    cnt1)

/-- what a run does (Compile/Batch/DisciplineRun.lean) -/
local notation "RunO" => _root_.Compile.Batch.Disc.Run

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## Coins that are values leave the state alone -/

section Coins
variable {Rl : Rules (typedOracleFamily lam K L)}

theorem safe_bitsT (ℓ : ℕ) (d : DSt (typedOracleFamily lam K L)) :
    SafeO Rl (bitsT (K := K) (L := L) ℓ) d fun _ d' => d' = d := by
  unfold bitsT
  intro _
  exact rfl

theorem safe_digT (d : DSt (typedOracleFamily lam K L)) :
    SafeO Rl (digT (lam := lam) (K := K) (L := L)) d fun _ d' => d' = d := by
  unfold digT
  intro _
  exact rfl

theorem safe_digsT : ∀ (n : ℕ) (d : DSt (typedOracleFamily lam K L)),
    SafeO Rl (digsT (lam := lam) (K := K) (L := L) n) d fun ds d' => d' = d ∧ ds.length = n
  | 0, _ => ⟨rfl, rfl⟩
  | n + 1, d => by
      rw [digsT]
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_digT d))
      rintro c _ rfl
      refine SafeO.bind _ _ _ (SafeO.mono ?_ _ _ (safe_digsT n _))
      rintro ds _ ⟨rfl, hl⟩
      exact ⟨rfl, by rw [List.length_cons, hl]⟩

/-- The coins that are values: the state stays, and there are as many sibling digests as the
request tree is deep. -/
theorem safe_drawD (ln : RunLen lam L) (d : DSt (typedOracleFamily lam K L)) :
    SafeO Rl (drawD (K := K) ln) d fun cd d' => d' = d ∧ cd.path.length = ln.dq := by
  unfold drawD
  refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_bitsT ln.rs d))
  rintro u _ rfl
  refine SafeO.bind _ _ _ (SafeO.mono ?_ _ _ (safe_digsT ln.dq _))
  rintro ds _ ⟨rfl, hl⟩
  exact ⟨rfl, hl⟩

end Coins

/-! ## The two tokens of an opened leaf -/

theorem toksAt_some {T : TreeT lam L} {j : ℕ} {a : Tok × Tok} (e : T.tok[j]? = some a) :
    T.toksAt j = [a.1, a.2] := by
  unfold TreeT.toksAt
  simp only [e]

theorem toksAt_none {T : TreeT lam L} {j : ℕ} (e : T.tok[j]? = none) : T.toksAt j = [] := by
  unfold TreeT.toksAt
  simp only [e]

/-- A token that is shown when leaf j is opened is a token of the tree; it exists; and what it
depends on is shown with it, or is in us. -/
theorem toksAt_ok {d : DSt (typedOracleFamily lam K L)} {us : List Tok} {T : TreeT lam L} (h : TreeOKT d us T)
    (j : ℕ) {u : Tok} (hu : u ∈ T.toksAt j) :
    TreeTokT T u ∧ u < d.vals.length ∧ Deps d u (T.toksAt j ++ us) := by
  cases e : T.tok[j]? with
  | none =>
      rw [toksAt_none e] at hu
      exact absurd hu List.not_mem_nil
  | some a =>
      rw [toksAt_some e] at hu ⊢
      have ha : a ∈ T.tok := List.mem_of_getElem? e
      obtain ⟨h1, h2, h3, h4⟩ := h a ha
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ⟨⟨a, ha, Or.inl rfl⟩, h1, h3.mono fun v hv => List.mem_cons_of_mem _ hv⟩
      · rw [List.mem_singleton.mp hu]
        exact ⟨⟨a, ha, Or.inr rfl⟩, h2, h4.mono fun v hv => absurd hv List.not_mem_nil⟩

end OnBytes.TokenRules

#print axioms OnBytes.TokenRules.safe_drawD
#print axioms OnBytes.TokenRules.toksAt_ok
