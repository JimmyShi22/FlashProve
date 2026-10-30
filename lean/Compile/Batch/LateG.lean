-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/LateG.lean: a Fiat-Shamir query with proof-of-work bits (the search over nonces `fbG`,
Compile/Batch/Prover.lean; its form in `LStep`, `fbGL`, Compile/Batch/Mirror.lean) in the
relation `Rom.Late` (Rom/DeferLate.lean, with `Ctx`, `Clo`: context, closure) (words of this
library: lean/GLOSSARY.md).
  `late_fbT1`, `late_fbTw1`     one query, to `fb t` and under the ghost name `fbw t j`: the context
                                learns the closure `cloFb`, `cloFbw` (Compile/Batch/Mirror.lean) at
                                the charged token
  `late_fbW`                    the attempts after the first, by induction on how many may still
                                come. The induction keeps: the context knows the closures of the
                                attempts 0, .., j (`setW`); dd holds the chaining values of the j +
                                1 failed attempts, all at least n₀ and below the bound
  `late_fbG`                    the search: `fbG` and `fbGL` are related, under hs, if what follows
                                is related under the context that knows the closures of all attempts
                                that were made (`setFb`), for everything that the search can pass on
                                (`Kept`, Compile/Batch/ProverG.lean)
  For `setW`, `setFb` (Compile/Batch/Mirror.lean) the second section has what
  Compile/Batch/Late1.lean has for `Ctx.set` (but for `Ext.set`; for `setW`: `baseUp_set` alone).
Limits: nothing on distributions (the argument h of `fbGL` is `none`: every answer is sampled from
all answers); nothing on whole rounds.

The induction follows `fbW_indK` of Compile/Batch/ProverG.lean.
-/
import Compile.Batch.SpecLoop
import Compile.Batch.Late1

noncomputable section

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

section
variable {α β : Type} {post : ℕ → Cx lam K L → α → β → Prop} (t : Tag) (i : ℕ) (tk : Tok)
  (us : List Tok) (root : Option Tok) (hd : List Bits → Bits → Head lam X)
  (hinj : ∀ vs, Function.Injective (hd vs))

/-- One query to `fb t`, under `hs`: related if the continuations are, under the context with
`cloFb` at tk. -/
theorem late_fbT1 (pl : PlainPart (shapeOf L t) (annOf L t))
    {k : Blk lam K → Tok → St lam K L α} {k' : Blk lam K → Tok → Lp lam K L β} {n : ℕ}
    {Γ : Cx lam K L} (has : Bool) (hs : root.isSome = has)
    (h : ∀ bl tl, n ≤ tl →
      Late post (tl + 1) (Γ.set tk (OracleName.fb t) (cloFb K t i hd has us.length pl)) (k bl tl)
        (k' bl tl)) :
    Late post n Γ (fbT t i tk us root hd hinj pl k)
      (fbL t tk (us ++ root.toList) ⟨Finset.univ, Finset.univ_nonempty⟩ k') := by
  subst hs
  cases root <;> exact Late.marked h

/-- The same for one query under the ghost name `fbw t j`, with `cloFbw`. -/
theorem late_fbTw1 (j : ℕ) (pl : PlainPart (shapeOf L t) (annOf L t))
    {k : Blk lam K → Tok → St lam K L α} {k' : Blk lam K → Tok → Lp lam K L β} {n : ℕ}
    {Γ : Cx lam K L} (has : Bool) (hs : root.isSome = has)
    (h : ∀ bl tl, n ≤ tl →
      Late post (tl + 1) (Γ.set tk (OracleName.fbw t j) (cloFbw K t j i hd has us.length pl)) (k bl tl)
        (k' bl tl)) :
    Late post n Γ (fbTw t j i tk us root hd hinj pl k)
      (fbLw t j tk (us ++ root.toList) ⟨Finset.univ, Finset.univ_nonempty⟩ k') := by
  subst hs
  cases root <;> exact Late.marked h

variable {r : Round} {a : RAnn r} (w : WireRB lam K r a) {P : Type} (g : GrW r.Chal P)
  (emb : P → PlainPart (shapeOf L t) (annOf L t)) (pl : P)

/-- The attempts after the first, under the hypotheses below. Γ₀: the context after attempt 0. -/
theorem late_fbW {k : ℕ → List Tok → Blk lam K → Tok → St lam K L α}
    {k' : ℕ → List Tok → Blk lam K → Tok → Lp lam K L β} (n₀ : ℕ) (Γ₀ : Cx lam K L)
    (has : Bool) (hs : root.isSome = has)
    (h : ∀ m dd bl tl, dd.length = m → m ≤ g.more → n₀ ≤ tl → (∀ u ∈ dd, n₀ ≤ u ∧ u < tl) →
      Late post (tl + 1) (setW t tk i hd has us.length (fun j => emb (g.put j pl)) Γ₀ m)
        (k m dd bl tl) (k' m dd bl tl)) :
    ∀ (m j : ℕ) (dd : List Tok) (n : ℕ), dd.length = j + 1 → j + 1 + m = g.more →
      n₀ ≤ n → (∀ u ∈ dd, n₀ ≤ u ∧ u < n) →
      Late post n (setW t tk i hd has us.length (fun j => emb (g.put j pl)) Γ₀ j)
        (fbW g w.chal t i tk us root hd hinj emb pl k m j dd)
        (fbWL w g (ansB w) t tk (us ++ root.toList) none k' m j dd)
  | 0, j, dd, n, h1, h2, h3, h4 =>
      late_fbTw1 t i tk us root hd hinj j _ has hs fun bl tl htl =>
        h (j + 1) dd bl tl h1 (by omega) (h3.trans htl) fun u hu =>
          ⟨(h4 u hu).1, lt_of_lt_of_le (h4 u hu).2 htl⟩
  | m + 1, j, dd, n, h1, h2, h3, h4 =>
      late_fbTw1 t i tk us root hd hinj j _ has hs fun bl tl htl => by
        by_cases hok : g.ok (w.chal bl) = true
        · rw [if_pos hok, if_pos hok]
          exact h (j + 1) dd bl tl h1 (by omega) (h3.trans htl) fun u hu =>
            ⟨(h4 u hu).1, lt_of_lt_of_le (h4 u hu).2 htl⟩
        · rw [if_neg hok, if_neg hok]
          refine late_fbW n₀ Γ₀ has hs h m (j + 1) (tl :: dd) (tl + 1) (by simp [h1]) (by omega)
            (by omega) fun u hu => ?_
          rcases List.mem_cons.1 hu with rfl | hu
          · exact ⟨h3.trans htl, Nat.lt_succ_self _⟩
          · exact ⟨(h4 u hu).1, Nat.lt_succ_of_lt (lt_of_lt_of_le (h4 u hu).2 htl)⟩

end

/-- The search, under `hs`: `fbG` and `fbGL` are related if the continuations are, for all that the
search can pass on (`Kept`), under the context `setFb`. -/
theorem late_fbG {r : Round} {a : RAnn r} (w : WireRB lam K r a) {P α β : Type}
    (gr : Option (GrW r.Chal P)) {post : ℕ → Cx lam K L → α → β → Prop} (t : Tag) (i : ℕ) (tk : Tok)
    (us : List Tok) (root : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (pl : P)
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L α}
    {k' : Option ℕ → List Tok → Blk lam K → Tok → Lp lam K L β} {n : ℕ} {Γ : Cx lam K L}
    (has : Bool) (hs : root.isSome = has)
    (h : ∀ nc dd bl tl, Kept gr nc dd → n ≤ tl → (∀ u ∈ dd, n ≤ u ∧ u < tl) →
      Late post (tl + 1) (setFb gr t [tk] i hd has us.length emb pl (nc.getD 0) Γ)
        (k nc dd bl tl) (k' nc dd bl tl)) :
    Late post n Γ (fbG gr w.chal t i tk us root hd hinj emb pl k)
      (fbGL w gr (ansB w) t tk (us ++ root.toList) none k') := by
  cases gr with
  | none =>
    exact late_fbT1 t i tk us root hd hinj _ has hs fun bl tl htl =>
      h none [] bl tl ⟨rfl, rfl, fun g e => by cases e⟩ htl (fun u hu => by cases hu)
  | some g =>
    have hk : ∀ m dd bl tl, dd.length = m → m ≤ g.more → n ≤ tl → (∀ u ∈ dd, n ≤ u ∧ u < tl) →
        Late post (tl + 1)
          (setW t tk i hd has us.length (fun j => emb (g.put j pl))
            (Γ.set tk (OracleName.fb t) (cloFb K t i hd has us.length (emb (g.put 0 pl)))) m)
          (k (some m) dd bl tl) (k' (some m) dd bl tl) :=
      fun m dd bl tl h1 h2 h3 h4 =>
        h (some m) dd bl tl ⟨rfl, h1, fun g' e => by cases e; exact h2⟩ h3 h4
    show Late post n Γ (fbTG g w.chal t i tk us root hd hinj emb pl fun m => k (some m))
      (fbTGL w g (ansB w) t tk (us ++ root.toList) none fun m => k' (some m))
    unfold fbTG fbTGL
    cases e : g.more with
    | zero =>
      exact late_fbT1 t i tk us root hd hinj _ has hs fun bl tl htl =>
        hk 0 [] bl tl rfl (Nat.zero_le _) htl (fun u hu => by cases hu)
    | succ m =>
      refine late_fbT1 t i tk us root hd hinj _ has hs fun bl tl htl => ?_
      by_cases hok : g.ok (w.chal bl) = true
      · rw [if_pos hok, if_pos hok]
        exact hk 0 [] bl tl rfl (Nat.zero_le _) htl (fun u hu => by cases hu)
      · rw [if_neg hok, if_neg hok]
        refine late_fbW t i tk us root hd hinj w g emb pl n _ has hs hk m 0 [tl] (tl + 1) rfl
          (by omega) (by omega) fun u hu => ?_
        obtain rfl := List.mem_singleton.1 hu
        exact ⟨htl, Nat.lt_succ_self _⟩

/-! ## What a context knows after the queries of one round: the lemmas on Ctx.set of
Compile/Batch/Late1.lean, for setW and setFb (but for `Ext.set`; for setW: `baseUp_set` alone) -/

section Kit
variable (t : Tag) (u : Tok) (i : ℕ) (hd : List Bits → Bits → Head lam X) (has : Bool) (rtAt : ℕ)

theorem setW_ne_tok (pl : ℕ → PlainPart (shapeOf L t) (annOf L t)) (Γ : Cx lam K L) {v : Tok} (h : v ≠ u) :
    ∀ m, setW t u i hd has rtAt pl Γ m v = Γ v
  | 0 => rfl
  | m + 1 => (funext fun o => Ctx.set_ne_tok _ h _ _ o).trans (setW_ne_tok pl Γ h m)

/-- under h0 (an entry of Γ at u is one of Γ' or has Q): an entry of setW over Γ at u is one of setW
over Γ' or has Q -/
theorem setW_cases (pl : ℕ → PlainPart (shapeOf L t) (annOf L t)) (Γ Γ' : Cx lam K L)
    {Q : ∀ o : OracleName, Clo (spec lam K L) o → Prop}
    (h0 : ∀ o pt, Γ u o = some pt → Γ' u o = some pt ∨ Q o pt) :
    ∀ m o pt, setW t u i hd has rtAt pl Γ m u o = some pt →
      setW t u i hd has rtAt pl Γ' m u o = some pt ∨ Q o pt
  | 0, o, pt, hp => h0 o pt hp
  | m + 1, o, pt, hp => by
      by_cases ho : o = OracleName.fbw t m
      · subst ho
        rw [show setW t u i hd has rtAt pl Γ (m + 1) =
                (setW t u i hd has rtAt pl Γ m).set
                  u (OracleName.fbw t m) (cloFbw K t m i hd has rtAt (pl (m + 1))) from rfl,
          Ctx.set_same] at hp
        exact Or.inl (by rw [show setW t u i hd has rtAt pl Γ' (m + 1) = (setW t u i hd has rtAt pl Γ' m).set u (OracleName.fbw t m) (cloFbw K t m i hd has rtAt (pl (m + 1))) from rfl, Ctx.set_same]; exact hp)
      · rw [show setW t u i hd has rtAt pl Γ (m + 1) =
                (setW t u i hd has rtAt pl Γ m).set
                  u (OracleName.fbw t m) (cloFbw K t m i hd has rtAt (pl (m + 1))) from rfl,
          Ctx.set_ne_oracle _ u ho] at hp
        rw [show setW t u i hd has rtAt pl Γ' (m + 1) =
                (setW t u i hd has rtAt pl Γ' m).set
                  u (OracleName.fbw t m) (cloFbw K t m i hd has rtAt (pl (m + 1))) from rfl,
          Ctx.set_ne_oracle _ u ho]
        exact setW_cases pl Γ Γ' h0 m o pt hp

theorem baseUp_setW (pl : ℕ → PlainPart (shapeOf L t) (annOf L t)) (Pc : Cx lam K L)
    {v : Tok} (h : BaseUp Pc v) :
    ∀ m, BaseUp (setW t u i hd has rtAt pl Pc m) v
  | 0 => h
  | m + 1 => baseUp_set _ (baseUp_setW pl Pc h m) u _ fun _ => rfl

variable {C P : Type} (gr : Option (GrW C P))
  (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P) (m : ℕ)

theorem setFb_ne_tok (Γ : Cx lam K L) {v : Tok} (h : v ≠ u) :
    setFb gr t [u] i hd has rtAt emb α m Γ v = Γ v := by
  cases gr with
  | none => exact funext fun o => Ctx.set_ne_tok Γ h _ _ o
  | some g =>
    exact (setW_ne_tok t u i hd has rtAt _ _ h m).trans (funext fun o => Ctx.set_ne_tok Γ h _ _ o)

/-- only the first token of the list matters -/
theorem setFb_cons (l : List Tok) (Γ : Cx lam K L) :
    setFb gr t (u :: l) i hd has rtAt emb α m Γ = setFb gr t [u] i hd has rtAt emb α m Γ := rfl

theorem setFb_ne (Pc : Cx lam K L) {l : List Tok} {v : Tok} (h : v ∉ l) :
    setFb gr t l i hd has rtAt emb α m Pc v = Pc v := by
  cases l with
  | nil => rfl
  | cons b l => exact setFb_ne_tok t b i hd has rtAt gr emb α m Pc fun e => h (by rw [e]; simp)

/-- An entry at u is one of the new ones, whatever the context below is, or an old one. -/
theorem setFb_cases (Γ Γ' : Cx lam K L) (o : OracleName) (pt : Clo (spec lam K L) o)
    (hp : setFb gr t [u] i hd has rtAt emb α m Γ u o = some pt) :
    setFb gr t [u] i hd has rtAt emb α m Γ' u o = some pt ∨ Γ u o = some pt := by
  have h0 : ∀ (c : Clo (spec lam K L) (OracleName.fb t)) o pt, (Γ.set u (OracleName.fb t) c) u o = some pt →
      (Γ'.set u (OracleName.fb t) c) u o = some pt ∨ Γ u o = some pt := fun c o pt hp => by
    by_cases ho : o = OracleName.fb t
    · subst ho
      rw [Ctx.set_same] at hp
      exact Or.inl (by rw [Ctx.set_same]; exact hp)
    · rw [Ctx.set_ne_oracle Γ u ho] at hp
      exact Or.inr hp
  cases gr with
  | none => exact h0 _ o pt hp
  | some g =>
    exact setW_cases t u i hd has rtAt _ _ _ (Q := fun o pt => Γ u o = some pt) (h0 _) m o pt hp

theorem fut_setFb {n n' : ℕ} {Γ : Cx lam K L} (h : Fut n Γ) (hu : n' > u) (hn : n ≤ n') :
    Fut n' (setFb gr t [u] i hd has rtAt emb α m Γ) := fun v hv o => by
  rw [setFb_ne_tok t u i hd has rtAt gr emb α m Γ (Nat.ne_of_gt (lt_of_lt_of_le hu hv))]
  exact h v (le_trans hn hv) o

/-- If, at u, `Pc` has the entries of Γ (h) and those of setFb over the empty context (hP), it has
those of setFb over Γ. -/
theorem cov_setFb_of {Γ Pc : Cx lam K L} (h : Cov Γ u Pc)
    (hP : Cov (setFb gr t [u] i hd has rtAt emb α m (Ctx.empty _)) u Pc) :
    Cov (setFb gr t [u] i hd has rtAt emb α m Γ) u Pc :=
  fun o pt hp =>
    (setFb_cases t u i hd has rtAt gr emb α m Γ (Ctx.empty _) o pt hp).elim (hP o pt) (h o pt)

theorem cov_setFb_ne {Γ Pc : Cx lam K L} {v : Tok} (h : Cov Γ v Pc) (hne : v ≠ u) :
    Cov (setFb gr t [u] i hd has rtAt emb α m Γ) v Pc :=
  h.congr (setFb_ne_tok t u i hd has rtAt gr emb α m Γ hne)

/-- the context that the release supplies has the new entries: setFb over any context has those of
setFb over the empty one -/
theorem cov_setFb (Pc : Cx lam K L) (l : List Tok) :
    Cov (setFb gr t [u] i hd has rtAt emb α m (Ctx.empty _)) u
      (setFb gr t (u :: l) i hd has rtAt emb α m Pc) :=
  fun o pt hp =>
    (setFb_cases t u i hd has rtAt gr emb α m (Ctx.empty _) Pc o pt hp).elim id fun h =>
      absurd h (by simp [Ctx.empty])

theorem baseUp_setFb (Pc : Cx lam K L) {v : Tok} (h : BaseUp Pc v) (l : List Tok) :
    BaseUp (setFb gr t l i hd has rtAt emb α m Pc) v := by
  cases l with
  | nil => exact h
  | cons b l =>
    cases gr with
    | none => exact baseUp_set Pc h b _ fun _ => rfl
    | some g => exact baseUp_setW t b i hd has rtAt _ _ (baseUp_set Pc h b _ fun _ => rfl) m

/-- without proof-of-work bits the number of the final attempt does not matter -/
theorem setFb_none (l : List Tok) (m' : ℕ) (Pc : Cx lam K L) :
    setFb (none : Option (GrW C P)) t l i hd has rtAt emb α m Pc =
      setFb (none : Option (GrW C P)) t l i hd has rtAt emb α m' Pc := by
  cases l <;> rfl

/-- The list of the numbers of final attempts, as `ctxB` reads it: a round with proof-of-work bits
takes the first; the prover has noted it exactly if the round has such bits (`hK`). -/
theorem setFb_kept {nc : Option ℕ} (hK : nc.isSome = gr.isSome) (N : List ℕ)
    (l : List Tok) (Pc : Cx lam K L) :
    setFb gr t l i hd has rtAt emb α ((nc.toList ++ N).headD 0) Pc =
      setFb gr t l i hd has rtAt emb α (nc.getD 0) Pc := by
  cases gr with
  | none => exact setFb_none t i hd has rtAt emb α _ l _ Pc
  | some g =>
    cases nc with
    | none => cases hK
    | some m => rfl

theorem restN_kept {nc : Option ℕ} (hK : nc.isSome = gr.isSome) (N : List ℕ) :
    restN gr (nc.toList ++ N) = N := by
  cases gr with
  | none =>
    cases nc with
    | none => rfl
    | some m => cases hK
  | some g =>
    cases nc with
    | none => cases hK
    | some m => rfl

theorem toList_reverse (nc : Option ℕ) : nc.toList.reverse = nc.toList := by cases nc <;> rfl

end Kit

end Compile.Batch
