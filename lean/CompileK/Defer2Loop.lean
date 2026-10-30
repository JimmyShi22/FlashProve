-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Loop.lean: one chain query of the compiled prover, with proof of work or without, for
the lemma on deferred programming of the random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean). A
Fiat-Shamir evaluation, with a test (a loop of tries) or without (Compile/Batch/Prover.lean: `fbT`,
`fbTw`, `fbW`, `fbG`), obeys the discipline with joint charges (`SafeO2`), if the number of later
tries is at most mG; and it adds at the vertex oracles only evaluations whose further tokens are new
(`Tries.gj`); each under the hypotheses of its statement.

The analogues for `SafeO2` (CompileK/Defer2Safe.lean) of Part 2 of
Compile/Batch/DisciplineLoop.lean; laws of `Tries` (Part 1 of that file: marked evaluations that are
all charged to one token and hold the same further tokens). Nothing assumed beyond the hypotheses of
the statements and whatever the arguments hold as proofs.

Main names:
  `safe2_fbG`: the title's first half; see its docstring.
  Against Compile/Batch/DisciplineLoop.lean `safe2_fbW` and `safe2_fbG` have one premise more:
    g.more ≤ mG; `safe2_fbTw`: j < mG (`rulesB` allows all further names; the hypothesis of
    CompileK/SpecDefer2.lean needs finitely many classes).
  `Tries.tidy2`: from an orderly state (`hd`), marked evaluations at oracles without joint charges
    keep the state's upward side (`Tidy2`).
  `Tries.gj`: such evaluations, though they may hold a tree's root among their further tokens, add
    at the vertex oracles only evaluations whose further tokens are new (`GJ NoTok`).

Words used in this file. The discipline with joint charges, the vertex oracles: the paragraph "Words
used in this file." of CompileK/Defer2Chain.lean's head holds here too.

Terms: lean/GLOSSARY.md: chain query, tries, ghost (a further name is a ghost name).
-/
import CompileK.Defer2Kit
import Compile.Batch.DisciplineLoop

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc (Rules afterMark mem_evs_afterMark cnt1 length_afterMark)

theorem fbw_memG {mG : ℕ} (t : Tag) {j : ℕ} (hj : j < mG) : OracleName.fbw t j ∈ osBG mG := by
  refine Finset.mem_union_right _ ?_
  cases t
  · exact Finset.mem_union_left
      _ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, rfl⟩))
  · exact Finset.mem_union_left
      _ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, rfl⟩))
  · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, rfl⟩)

theorem osTry_memG {mG : ℕ} (t : Tag) {n : ℕ} (hn : n ≤ mG) :
    ∀ o ∈ osTry t n, o ∈ osBG mG := fun o ho => by
  rcases mem_osTry.mp ho with rfl | ⟨k, hk, rfl⟩
  · exact osB_sub mG (fb_mem_osB t)
  · exact fbw_memG t (lt_of_lt_of_le hk hn)

theorem osTry_notJ (t : Tag) (n : ℕ) : ∀ o ∈ osTry t n, Jt o = false := fun o ho => by
  rcases mem_osTry.mp ho with rfl | ⟨k, _, rfl⟩ <;> simp [Jt]

section Generic
variable {S : OSpec} {sp : Split S} {Rl : Rules S} {t : Tok} {us : List Tok} {d d' : DSt S}
  {os : List S.ι} {tls : List Tok}

theorem Tries.tidy2 {Jo : S.ι → Bool} {ℓ2 : S.ι → ℕ} (h : Tries sp t us d os tls d')
    (hd : TidyO Rl d) (h2 : Tidy2 Jo ℓ2 d) (hJ : ∀ o ∈ os, Jo o = false) : Tidy2 Jo ℓ2 d' := by
  intro e he hJe
  rcases h.mem_evs e he with he | ⟨_, _, _, ho⟩
  · exact Tidy2.ext (d := d) (d' := d') hd h2
      (h.run (R := fun _ => False) (e := fun _ => 0)).grows.vals h.shown e he hJe
  · rw [hJ _ ho] at hJe
    simp at hJe

end Generic

section Scheme
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params} {mG : ℕ} {β C P : Type}
  {chal : Blk lam K → C} {t : Tag} {i : ℕ} {tk : Tok} {us : List Tok} {root : Option Tok}
  {hd : List Bits → Bits → Head lam X} {hinj : ∀ vs, Function.Injective (hd vs)}
  {emb : P → PlainPart (shapeOf L t) (annOf L t)} {α : P}

theorem Tries.gj {d d' : DSt (spec lam K L)} {tk : Tok} {vs tls : List Tok} {os : List OracleName}
    (h : Tries (split lam K L) tk vs d os tls d') (hJ : ∀ o ∈ os, Jt o = false) : GJ NoTok d d' :=
  ⟨h.length_le, fun e' he' hJe => by
    rcases h.mem_evs e' he' with he | ⟨_, _, _, ho⟩
    · exact Or.inl ⟨e', he, rfl, rfl, rfl⟩
    · rw [hJ _ ho] at hJe
      simp at hJe⟩

/-- a later try, from a state that the loop has reached -/
theorem safe2_fbTw {d d₁ : DSt (spec lam K L)} (h : LoopPre p d t tk (us ++ root.toList)) {j : ℕ}
    (hj : j < mG) {tls : List Tok}
    (hT : Tries (split lam K L) tk (us ++ root.toList) d (osTry t j) tls d₁)
    (pl : PlainPart (shapeOf L t) (annOf L t)) (k : Blk lam K → Tok → St lam K L β)
    (Q : β → DSt (spec lam K L) → Prop)
    (hk : ∀ bl d',
      Tries (split lam K L) tk (us ++ root.toList) d (osTry t (j + 1))
        (tls ++ [d₁.vals.length]) d' →
      SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (k bl d₁.vals.length) d' Q) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (fbTw t j i tk us root hd hinj pl k) d₁ Q := by
  have hl : Len d₁ tk (d.val tk).length :=
    (show Len d tk (d.val tk).length from ⟨h.free.lt, rfl⟩).grows
      (hT.run (R := fun _ => False) (e := fun _ => 0)).grows
  refine ⟨fun u hu => lt_of_lt_of_le (h.lt u hu) hT.length_le, h.not_mem,
    hT.freeAt (h.freeW j) (fbw_not_mem_osTry t j), ?_, fbw_memG t hj,
    jmark_none (by simp [Jt]) _ _ _, fun r T => ?_⟩
  · show min p.sFS lam ≤ _
    rw [hl.2]
    exact h.bits
  · exact hk _ _ (osTry_succ t j ▸ Tries.snoc hT (OracleName.fbw t j) _ r T)

theorem safe2_fbW {d : DSt (spec lam K L)} (h : LoopPre p d t tk (us ++ root.toList)) (g : GrW C P)
    (hm : g.more ≤ mG) (k : ℕ → List Tok → Blk lam K → Tok → St lam K L β)
    (Q : β → DSt (spec lam K L) → Prop)
    (hk : ∀ m dd bl tl d', dd.length = m → m ≤ g.more →
      Tries (split lam K L) tk (us ++ root.toList) d (osTry t m) (dd.reverse ++ [tl]) d' →
      SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (k m dd bl tl) d' Q) :
    ∀ (n j : ℕ) (dd : List Tok) (d₁ : DSt (spec lam K L)), dd.length = j + 1 → j + 1 + n = g.more →
      Tries (split lam K L) tk (us ++ root.toList) d (osTry t j) dd.reverse d₁ →
      SafeO2 (rulesT K L lam p mG) Jt (ellT lam)
        (fbW g chal t i tk us root hd hinj emb α k n j dd) d₁ Q
  | 0, j, dd, d₁, h1, h2, hT =>
    safe2_fbTw h (by omega) hT _ _ Q fun bl d' hT' => hk _ _ bl _ d' h1 (by omega) hT'
  | n + 1, j, dd, d₁, h1, h2, hT => safe2_fbTw h (by omega) hT _ _ Q fun bl d' hT' => by
      split
      · exact hk _ _ bl _ d' h1 (by omega) hT'
      · exact safe2_fbW h g hm k Q hk n (j + 1) (d₁.vals.length :: dd) d' (by simp [h1])
          (by omega) (by rw [List.reverse_cons]; exact hT')

/-- the first try -/
theorem safe2_fbT0 {d : DSt (spec lam K L)}
    (h : LoopPre p d t tk (us ++ root.toList)) (pl : PlainPart (shapeOf L t) (annOf L t))
    (k : Blk lam K → Tok → St lam K L β) (Q : β → DSt (spec lam K L) → Prop)
    (hk : ∀ bl d', Tries (split lam K L) tk (us ++ root.toList) d (osTry t 0) [d.vals.length] d' →
      SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (k bl d.vals.length) d' Q) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (fbT t i tk us root hd hinj pl k) d Q :=
  ⟨h.lt, h.not_mem, h.free, h.bits, osB_sub mG (fb_mem_osB t), jmark_none (by simp [Jt]) _ _ _,
    fun r T => hk _ _ (Tries.one d (OracleName.fb t) _ r T)⟩

/-- A Fiat-Shamir evaluation, with a test or without, obeys the rules, and ends in Q, if what
follows is safe from every state that the loop can reach, for what the loop can hand over; under `h`
and `hm`. -/
theorem safe2_fbG {d : DSt (spec lam K L)} (h : LoopPre p d t tk (us ++ root.toList))
    (gr : Option (GrW C P)) (hm : ∀ g, gr = some g → g.more ≤ mG)
    (k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β) (Q : β → DSt (spec lam K L) → Prop)
    (hk : ∀ nc dd bl tl d', Kept gr nc dd →
      Tries (split lam K L) tk (us ++ root.toList) d (osTry t (nc.getD 0)) (dd.reverse ++ [tl]) d' →
      SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (k nc dd bl tl) d' Q) :
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam)
      (fbG gr chal t i tk us root hd hinj emb α k) d Q := by
  cases gr with
  | none =>
    show SafeO2 _ _ _ (fbT t i tk us root hd hinj (emb α) (k none [])) d Q
    exact safe2_fbT0 h _ _ Q fun bl d' hT => hk none [] bl _ d' ⟨rfl, rfl, fun g e => by cases e⟩ hT
  | some g =>
    have hk' : ∀ m dd bl tl d', dd.length = m → m ≤ g.more →
        Tries (split lam K L) tk (us ++ root.toList) d (osTry t m) (dd.reverse ++ [tl]) d' →
        SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (k (some m) dd bl tl)
          d' Q := fun m dd bl tl d' h1 h2 hT =>
      hk (some m) dd bl tl d' ⟨rfl, h1, fun g' e => by cases e; exact h2⟩ hT
    show SafeO2 _ _ _ (fbTG g chal t i tk us root hd hinj emb α fun m => k (some m)) d Q
    unfold fbTG
    split
    · exact safe2_fbT0 h _ _ Q fun bl d' hT => hk' 0 [] bl _ d' rfl (Nat.zero_le _) hT
    · rename_i n hn
      refine safe2_fbT0 h _ _ Q fun bl d' hT => ?_
      split
      · exact hk' 0 [] bl _ d' rfl (Nat.zero_le _) hT
      · exact safe2_fbW h g (hm g rfl) (fun m => k (some m)) Q hk' n 0
          [d.vals.length] d' rfl (by omega) hT


end Scheme

end Compile.Batch.Disc
