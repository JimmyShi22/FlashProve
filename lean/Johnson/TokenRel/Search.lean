-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRel/Search.lean: A FIAT-SHAMIR QUERY OF THE CHAIN, WITH A SEARCH FOR A NONCE OR
WITHOUT, AS A TOKEN PROGRAM, KEEPS THE RULES (fbT, searchT, fsT, Johnson/TokenSide/Chain.lean). The
query to g and the request path are in Johnson/TokenRel/Path.lean.

General lemmas. This file states no goal of the release. The token programs are a device of one step
of a proof of index privacy and stand in no statement on the scheme.

All tries of one search are charged to one token tk, each under a name of its own (oName t n), so
the rule "a token is charged once at each oracle" is kept as long as tk can be charged under every
name from the current try's on. Each try's tail is a new token that nothing holds. What a query
returns (HitOK): the final try's tail and the tails of the failed tries are new, nothing holds them;
and tk now depends on these tails and on what it depended on before.

  cntTries t n fuel   the tries number n, .., n + fuel - 1, oracle by oracle.
  mFs t b cp          one Fiat-Shamir query: one evaluation at fb t; with a test (b), one at fbw t k
                      for each k < cp.
Follows the pattern of Compile/Batch/DisciplineLoop.lean and DisciplineReq.lean, at one slot.

-/
import Johnson.TokenRel.Trees

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenRel
open _root_.Compile hiding ON ON.leaf ON.node ON.ann ON.other
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey OnBytes.TokenSide OnBytes.TokenRules
open _root_.Compile.Disc (Rules nEv)
open _root_.Compile.Batch.Disc
open _root_.Compile.DeferRun (qa)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout Marks
open _root_.Compile.Disc
  (afterPlain afterFresh afterMark afterReveal length_afterFresh length_afterMark mem_evs_afterMark
    cnt1 val_of_prefix val_afterFresh)

/-- what a run does (Compile/Batch/DisciplineRun.lean) -/
local notation "RunO" => _root_.Compile.Batch.Disc.Run

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {bl bf : ℕ}
  {sd : (t : Tag) → FbIn lam L t → Prop}

/-! ## Names -/

theorem oName_inj {t : Tag} : ∀ {m n : ℕ}, oName t m = oName t n → m = n
  | 0, 0, _ => rfl
  | 0, _ + 1, h => nomatch h
  | _ + 1, 0, h => nomatch h
  | m + 1, n + 1, h => by
      have h' : OracleName.fbw t m = OracleName.fbw t n := h
      cases h'
      rfl

theorem tl_oName (t : Tag) (n : ℕ) : (splitT lam K L).tl (oName t n) = lam := by
  cases n <;> rfl

theorem oName_ne_leaf (t : Tag) (n : ℕ) : ¬ oName t n = OracleName.leaf := by
  cases n <;> exact fun h => nomatch h

/-! ## Counts -/

/-- the tries number n, .., n + fuel - 1 -/
def cntTries (t : Tag) : ℕ → ℕ → OracleName → ℕ
  | _, 0, _ => 0
  | n, fuel + 1, o => (if o = oName t n then 1 else 0) + cntTries t (n + 1) fuel o

/-- one Fiat-Shamir query; b: has it a test?; cp: the cap -/
def mFs (t : Tag) (b : Bool) (cp : ℕ) : OracleName → ℕ
  | .fb t' => if t' = t then 1 else 0
  | .fbw t' k => if t' = t ∧ b = true ∧ k < cp then 1 else 0
  | _ => 0

theorem cntTries_fb (t t' : Tag) : ∀ (fuel n : ℕ),
    cntTries t n fuel (.fb t') ≤ if t' = t ∧ n = 0 then 1 else 0
  | 0, _ => Nat.zero_le _
  | fuel + 1, n => by
      have ih := cntTries_fb t t' fuel (n + 1)
      rw [if_neg (fun h => Nat.succ_ne_zero n h.2)] at ih
      rw [cntTries, Nat.le_zero.mp ih, Nat.add_zero]
      cases n with
      | zero =>
          by_cases h : t' = t
          · subst h; simp [oName]
          · simp [oName, h]
      | succ n => simp [oName]

theorem cntTries_fbw (t t' : Tag) (k : ℕ) : ∀ (fuel n : ℕ),
    cntTries t n fuel (.fbw t' k) ≤ if t' = t ∧ n ≤ k + 1 ∧ k + 1 < n + fuel then 1 else 0
  | 0, _ => Nat.zero_le _
  | fuel + 1, n => by
      have ih := cntTries_fbw t t' k fuel (n + 1)
      rw [cntTries]
      by_cases h : t' = t
      · subst h
        simp only [true_and] at ih ⊢
        have e : (OracleName.fbw t' k = oName t' n) ↔ n = k + 1 := by
          cases n with
          | zero => simp [oName]
          | succ n => simp [oName, eq_comm]
        simp only [e]
        split_ifs at ih ⊢ <;> omega
      · simp only [h, false_and, if_false] at ih ⊢
        have e : ¬ (OracleName.fbw t' k = oName t n) := by
          cases n with
          | zero => simp [oName]
          | succ n => simp [oName, h]
        rw [if_neg e]
        omega

theorem cntTries_other (t : Tag) (o : OracleName) (h : ∀ m, o ≠ oName t m) : ∀ (fuel n : ℕ),
    cntTries t n fuel o = 0
  | 0, _ => rfl
  | fuel + 1, n => by rw [cntTries, if_neg (h n), cntTries_other t o h fuel (n + 1)]

theorem cntTries_le (t : Tag) (cp : ℕ) (o : OracleName) : cntTries t 0 (cp + 1) o ≤ mFs t true cp o := by
  cases o with
  | fb t' => exact le_trans (cntTries_fb t t' _ _) (by simp [mFs])
  | fbw t' k =>
      refine le_trans (cntTries_fbw t t' k _ _) ?_
      show _ ≤ if t' = t ∧ true = true ∧ k < cp then 1 else 0
      by_cases h : t' = t ∧ k < cp
      · have e : (if t' = t ∧ true = true ∧ k < cp then 1 else 0) = 1 := if_pos ⟨h.1, rfl, h.2⟩
        rw [e]
        split_ifs <;> omega
      · have e : (if t' = t ∧ 0 ≤ k + 1 ∧ k + 1 < 0 + (cp + 1) then 1 else 0) = 0 :=
          if_neg fun h' => h ⟨h'.1, by have := h'.2.2; omega⟩
        rw [e]
        exact Nat.zero_le _
  | _ => exact le_of_eq (cntTries_other t _ (fun m => by cases m <;> exact fun h => nomatch h) _ _)

/-! ## One try -/

theorem safe_fbT (t : Tag) (n i : ℕ) (tk : Tok) (us : List Tok)
    (hd' : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd' vs))
    (rt : List (Dig lam)) (pl : PlainPart (shapeOf L t) (annOf L t)) {d : DSt (typedOracleFamily lam K L)}
    (hd : TidyO (rulesT K L lam bl bf sd) d) (hus : ∀ u ∈ us, u < d.vals.length) (htu : tk ∉ us)
    (hf : FreeAt d (oName t n) tk) (hb : bf ≤ (d.val tk).length) :
    SafeO (rulesT K L lam bl bf sd) (fbT (K := K) t n i tk us hd' hinj rt pl) d fun a d' =>
      MarkedAt (rulesT K L lam bl bf sd) (splitT lam K L) d d' (oName t n) tk us a.2 := by
  cases n with
  | zero =>
      refine SafeO.mono ?_ _ _ (safe_mark hd hus htu hf hb (fun _ => by trivial) _ _ _)
      rintro a d' ⟨r, e, rfl, hm, _⟩
      exact hm
  | succ n =>
      refine SafeO.mono ?_ _ _ (safe_mark hd hus htu hf hb (fun _ => by trivial) _ _ _)
      rintro a d' ⟨r, e, rfl, hm, _⟩
      exact hm

/-! ## The search -/

/-- what a query of the chain adds: no leaf, charged to tk -/
def OffBy (tk : Tok) (e : Ev (typedOracleFamily lam K L)) : Prop := e.o ≠ OracleName.leaf ∧ e.charged = tk

/-- What holds of what a Fiat-Shamir query has returned. n₀: the tokens from n₀ on are new; tk: the
charged token; l: what tk depended on before, with the further tokens of the query. -/
structure HitOK (n₀ : ℕ) (d : DSt (typedOracleFamily lam K L)) (tk : Tok) (l : List Tok) {P : Type}
    (q : Hit lam K P) : Prop where
  unt : Untouched d q.tl
  len : Len d q.tl lam
  new : n₀ ≤ q.tl
  dead : ∀ u ∈ q.dead, n₀ ≤ u ∧ Untouched d u
  deps : Deps d tk ((q.tl :: q.dead) ++ l)

theorem safe_searchT {C P : Type} (gr : GrW C P) (chal : (Fin K → Dig lam) → C) (t : Tag) (i : ℕ)
    (tk : Tok) (us : List Tok) (hd' : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd' vs)) (rt : List (Dig lam))
    (f : P → PlainPart (shapeOf L t) (annOf L t)) (α : P) (n₀ nb : ℕ) (l : List Tok) (hb : bf ≤ nb)
    (htk : tk < n₀) (hus : ∀ u ∈ us, u < n₀) (htu : tk ∉ us) (hul : ∀ u ∈ us, u ∈ l) :
    ∀ (fuel n : ℕ) (dd : List Tok) (d : DSt (typedOracleFamily lam K L)),
      TidyO (rulesT K L lam bl bf sd) d → n₀ ≤ d.vals.length → Len d tk nb →
      (∀ m, n ≤ m → FreeAt d (oName t m) tk) → Deps d tk (dd ++ l) →
      (∀ u ∈ dd, n₀ ≤ u ∧ Untouched d u) →
    SafeO (rulesT K L lam bl bf sd)
      (searchT gr chal (fun n α => fbT (K := K) t n i tk us hd' hinj rt (f α)) α fuel n dd) d
      fun r d' =>
      TidyO (rulesT K L lam bl bf sd) d' ∧
      RunO (fun u => u = tk) (fun u => u = tk ∨ u ∈ us) noTok zr (cntTries t n fuel) d d' ∧
      Adds (OffBy tk) d d' ∧ ∀ q, r = some q → HitOK n₀ d' tk l q
  | 0, _, _, d, hd, _, _, _, _, _ => ⟨hd, Run.refl d, Adds.refl _ d, fun _ h => nomatch h⟩
  | fuel + 1, n, dd, d, hd, hn, hl, hfr, hdp, hdd => by
      rw [searchT]
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_fbT t n i tk us hd' hinj rt _ hd
        (fun u hu => lt_of_lt_of_le (hus u hu) hn) htu (hfr n le_rfl)
        (hb.trans (le_of_eq hl.2.symm))))
      rintro a d₁ hm
      have hnew : n₀ ≤ a.2 := hn.trans (le_of_eq hm.eq.symm)
      have hadd : Adds (OffBy tk) d d₁ := hm.adds.mono fun e _ h =>
        ⟨fun hc => oName_ne_leaf t n (h.1.symm.trans hc), h.2⟩
      have hdd₁ : ∀ u ∈ a.2 :: dd, n₀ ≤ u ∧ Untouched d₁ u := fun u hu => by
        rcases List.mem_cons.mp hu with rfl | hu
        · exact ⟨hnew, hm.unt⟩
        · refine ⟨(hdd u hu).1, (hdd u hu).2.grows hm.run.grows (fun h => ?_) (fun h => h)⟩
          rcases h with rfl | h
          · exact absurd htk (Nat.not_lt.mpr (hdd _ hu).1)
          · exact absurd (hus u h) (Nat.not_lt.mpr (hdd u hu).1)
      have hdp₁ : Deps d₁ tk ((a.2 :: dd) ++ l) := (hm.deps _ hdp).mono fun v hv => by
        simp only [List.cons_append, List.mem_cons, List.mem_append] at hv ⊢
        rcases hv with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (hul v h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      have hcnt : ∀ o, cnt1 (S := typedOracleFamily lam K L) (oName t n) 1 o + cntTries t (n + 1) fuel o ≤
          cntTries t n (fuel + 1) o := fun o => by
        rw [cntTries]
        exact le_of_eq rfl
      split
      · refine ⟨hm.tidy, hm.run.mono (fun _ h => Or.inl h) (fun _ h => Or.inl h)
          (fun _ h => Or.inl h) (fun _ => le_rfl)
          (fun o => le_trans (Nat.le_add_right _ _) (hcnt o)), hadd, ?_⟩
        rintro q hq
        cases hq
        have hlen := hm.len
        rw [tl_oName] at hlen
        exact ⟨hm.unt, hlen, hnew,
          fun u hu => hdd₁ u (List.mem_cons_of_mem _ hu), hdp₁⟩
      · refine SafeO.mono ?_ _ d₁ (safe_searchT gr chal t i tk us hd' hinj rt f α n₀ nb l hb htk hus
          htu hul fuel (n + 1) (a.2 :: dd) d₁ hm.tidy (le_trans hn hm.run.length_le)
          (hl.grows hm.run.grows)
          (fun m hm' => hm.free _ _
            (fun h => absurd (oName_inj h) (Nat.ne_of_gt (Nat.lt_of_succ_le hm')))
            (hfr m (Nat.le_of_succ_le hm'))) hdp₁ hdd₁)
        rintro r d₂ ⟨hd₂, hr₂, ha₂, hq⟩
        exact ⟨hd₂, hm.run.trans hr₂ (fun _ h => Or.inl h) (fun _ h => Or.inl h)
          (fun _ h => Or.inl h) (fun _ => le_rfl) hcnt, hadd.trans ha₂, hq⟩

/-- **A Fiat-Shamir query, with a test or without.** -/
theorem safe_fsT {C P : Type} (gr : Option (GrW C P)) (cp : ℕ) (chal : (Fin K → Dig lam) → C)
    (t : Tag) (i : ℕ) (tk : Tok) (us : List Tok) (hd' : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd' vs)) (rt : List (Dig lam))
    (f : P → PlainPart (shapeOf L t) (annOf L t)) (α : P) {nb : ℕ} (l : List Tok) (hb : bf ≤ nb)
    {d : DSt (typedOracleFamily lam K L)} (hd : TidyO (rulesT K L lam bl bf sd) d)
    (hus : ∀ u ∈ us, u < d.vals.length) (htu : tk ∉ us) (hul : ∀ u ∈ us, u ∈ l)
    (hlive : Live d t tk nb) (hdp : Deps d tk l) :
    SafeO (rulesT K L lam bl bf sd)
      (fsT gr cp chal (fun n α => fbT (K := K) t n i tk us hd' hinj rt (f α)) α) d fun r d' =>
      TidyO (rulesT K L lam bl bf sd) d' ∧
      RunO (fun u => u = tk) (fun u => u = tk ∨ u ∈ us) noTok zr (mFs t gr.isSome cp) d d' ∧
      Adds (OffBy tk) d d' ∧ ∀ q, r = some q → HitOK d.vals.length d' tk l q := by
  cases gr with
  | none =>
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_fbT t 0 i tk us hd' hinj rt _ hd hus htu
        (hlive.free 0) (hb.trans (le_of_eq hlive.len.2.symm))))
      rintro a d₁ hm
      refine ⟨hm.tidy, hm.run.mono (fun _ h => Or.inl h) (fun _ h => Or.inl h)
        (fun _ h => Or.inl h) (fun _ => le_rfl) (fun o => ?_),
        hm.adds.mono fun e _ h => ⟨fun hc => oName_ne_leaf t 0 (h.1.symm.trans hc), h.2⟩, ?_⟩
      · show (if o = oName t 0 then 1 else 0) ≤ _
        split
        · rename_i h
          rw [h]
          simp [mFs, oName]
        · exact Nat.zero_le _
      · rintro q hq
        cases hq
        refine ⟨hm.unt, hm.len, le_of_eq hm.eq.symm, fun _ h => absurd h List.not_mem_nil,
          (hm.deps _ hdp).mono fun v hv => ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at hv ⊢
        rcases hv with h | h | h
        · exact Or.inl h
        · exact Or.inr (hul v h)
        · exact Or.inr h
  | some g =>
      refine SafeO.mono ?_ _ d (safe_searchT g chal t i tk us hd' hinj rt f α d.vals.length nb l hb
        hlive.len.1 hus htu hul (cp + 1) 0 [] d hd le_rfl hlive.len (fun m _ => hlive.free m) hdp
        (fun _ h => absurd h List.not_mem_nil))
      rintro r d₁ ⟨hd₁, hr₁, ha₁, hq⟩
      exact ⟨hd₁, hr₁.mono (fun _ h => Or.inl h) (fun _ h => Or.inl h) (fun _ h => Or.inl h)
        (fun _ => le_rfl) (cntTries_le t cp), ha₁, hq⟩

end OnBytes.TokenRel

#print axioms OnBytes.TokenRel.safe_fsT
