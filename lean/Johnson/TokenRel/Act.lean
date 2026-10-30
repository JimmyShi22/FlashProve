-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRel/Act.lean: WHAT A ROUND OF THE CHAIN DOES TO THE INVARIANT, case by case of kind and
phase; the invariant along the round's trees; the counts of a round.

General lemmas. This file states no goal of the release. The token programs are a device of one step
of a proof of index privacy and stand in no statement on the scheme.

  ActOK, act_one   A round with one Fiat-Shamir query (actT, Johnson/TokenSide/Chain.lean, five
                   cases of kind and phase): the charged token is the first salt or a token of the
                   phase, the further tokens are tokens of the phase; the charged token can be
                   charged under every name of the tag and is long enough; and once the query is
                   made, the next phase's tokens can be charged in their turn.
  act_join         The joining round: the kind is "shared", the phase is "local".
  CI.trees         The invariant stays along the trees of a round, whose leaves hold the first salt.
  run_seq, run_cc  Two runs one after the other, the counts added; a run under wider sets.
  eRun_step, mChain_step, mChain_join   the counts of a round and of the rounds behind it are within
                   the counts from that round on.

-/
import Johnson.TokenRel.Path

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

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## Runs -/

section Runs
variable {S : OSpec} {Cc Ch Cc₂ Ch₂ : Tok → Prop} {e₁ M₁ e₂ M₂ : S.ι → ℕ} {d d' d'' : DSt S}

theorem run_seq (h₁ : RunO Cc Ch noTok e₁ M₁ d d') (h₂ : RunO Cc₂ Ch₂ noTok e₂ M₂ d' d'')
    (hCc : ∀ t, Cc₂ t → Cc t ∨ d.vals.length ≤ t) (hCh : ∀ t, Ch₂ t → Ch t ∨ d.vals.length ≤ t) :
    RunO Cc Ch noTok (fun o => e₁ o + e₂ o) (fun o => M₁ o + M₂ o) d d'' :=
  h₁.trans h₂ hCc hCh (fun _ h => Or.inl h) (fun _ => le_rfl) (fun _ => le_rfl)

theorem run_cc (h : RunO Cc₂ Ch₂ noTok e₁ M₁ d d') (hCc : ∀ t, Cc₂ t → Cc t ∨ d.vals.length ≤ t)
    (hCh : ∀ t, Ch₂ t → Ch t ∨ d.vals.length ≤ t) : RunO Cc Ch noTok e₁ M₁ d d' :=
  h.mono hCc hCh (fun _ h => Or.inl h) (fun _ => le_rfl) (fun _ => le_rfl)

end Runs

/-! ## A round with one Fiat-Shamir query -/

/-- See the head. -/
structure ActOK (d : DSt (typedOracleFamily lam K L)) (t : Tag) (salt sFS bf : ℕ) (ph : PhT) (kd : Kind)
    (tk : Tok) (us : List Tok) (own : Bool) (next : Tok → PhT) : Prop where
  tk_ph : PhTok salt ph tk
  us_ph : ∀ u ∈ us, u ∈ phToks ph
  htu : tk ∉ us
  live : ∃ nb, bf ≤ nb ∧ Live d t tk nb
  own_eq : (own = true ∧ kd = .lo) ∨ (own = false ∧ kd = .sh)
  next_ok : ∀ (e M : OracleName → ℕ) (d' : DSt (typedOracleFamily lam K L)) (v : Tok),
    GrowsO (fun u => u = tk ∨ u ∈ us) noTok e M d d' → Untouched d' v → Len d' v lam →
    d.vals.length ≤ v → PhOK d' t salt sFS (next v)
  next_toks : ∀ v u, u ∈ phToks (next v) → u = v ∨ u ∈ phToks ph
  jn : (kd = .lo ∧ ∀ v (s : Shape) (A : RoundSplits s), jOf (next v) s A = jOf ph s A) ∨
    ∀ v (s : Shape) (A : RoundSplits s), jOf (next v) s A = 0

theorem act_one {d : DSt (typedOracleFamily lam K L)} {t : Tag} {salt sFS bf : ℕ} {V : List Tok} {ph : PhT}
    {kd : Kind} {cms : List (Dig lam)} {x : Option X} {tk : Tok} {us : List Tok}
    {hd : List Bits → Bits → Head lam X}
    {inj : ∀ (xl : Option X) (vs : List Bits), Function.Injective fun v => (hd vs v).withLate xl}
    {own : Bool} {next : Tok → PhT} (hbS : bf ≤ sFS) (hbL : bf ≤ lam) (h : CI d t salt sFS V ph)
    (he : actT cms x salt kd ph = some (.one tk us hd inj own next)) :
    ActOK d t salt sFS bf ph kd tk us own next := by
  have hs : salt < d.vals.length := (h.deps salt h.salt_mem).1
  cases kd with
  | sh =>
    cases ph with
    | first => simp [actT] at he
    | loc tk' => simp [actT] at he
    | aft tk' c => simp [actT] at he
    | shr tk0 c =>
      simp only [actT, Option.some.injEq, ActT.one.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
      obtain ⟨_, h2, h3, h4, h5, h6⟩ := h.ph_ok
      exact
        { tk_ph := Or.inr List.mem_cons_self
          us_ph := fun _ h => absurd h List.not_mem_nil
          htu := List.not_mem_nil
          live := ⟨lam, hbL, fun _ => h4.freeAt _, h5⟩
          own_eq := Or.inr ⟨rfl, rfl⟩
          next_ok := fun _ _ d' v hg hu hl hv =>
            ⟨(lt_of_lt_of_le hs hv).ne', h2, (lt_of_lt_of_le h6.len.1 hv).ne, hu, hl,
              fun m => (h6.free m).grows hg
                (fun hc => hc.elim h3 fun h => absurd h List.not_mem_nil) (fun h => h),
              h6.len.grows hg⟩
          next_toks := fun v u hu => by
            simp only [phToks, List.mem_cons, List.not_mem_nil, or_false] at hu ⊢
            tauto
          jn := Or.inr fun _ _ _ => rfl }
  | lo =>
    cases ph with
    | first =>
      simp only [actT, Option.some.injEq, ActT.one.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
      exact
        { tk_ph := Or.inl rfl
          us_ph := fun _ h => absurd h List.not_mem_nil
          htu := List.not_mem_nil
          live := ⟨sFS, hbS, h.ph_ok⟩
          own_eq := Or.inl ⟨rfl, rfl⟩
          next_ok := fun _ _ d' v _ hu hl hv => ⟨(lt_of_lt_of_le hs hv).ne', hu, hl⟩
          next_toks := fun v u hu => Or.inl (List.mem_singleton.mp hu)
          jn := Or.inl ⟨rfl, fun _ _ _ => rfl⟩ }
    | loc tk' =>
      simp only [actT, Option.some.injEq, ActT.one.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
      obtain ⟨_, h2, h3⟩ := h.ph_ok
      exact
        { tk_ph := Or.inr List.mem_cons_self
          us_ph := fun _ h => absurd h List.not_mem_nil
          htu := List.not_mem_nil
          live := ⟨lam, hbL, fun _ => h2.freeAt _, h3⟩
          own_eq := Or.inl ⟨rfl, rfl⟩
          next_ok := fun _ _ d' v _ hu hl hv => ⟨(lt_of_lt_of_le hs hv).ne', hu, hl⟩
          next_toks := fun v u hu => Or.inl (List.mem_singleton.mp hu)
          jn := Or.inl ⟨rfl, fun _ _ _ => rfl⟩ }
    | shr tk0 c =>
      simp only [actT, Option.some.injEq, ActT.one.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
      obtain ⟨_, _, h3, _, _, h6⟩ := h.ph_ok
      exact
        { tk_ph := Or.inr (List.mem_cons_of_mem _ List.mem_cons_self)
          us_ph := fun u hu => by rw [List.mem_singleton.mp hu]; exact List.mem_cons_self
          htu := fun hc => h3 (List.mem_singleton.mp hc)
          live := ⟨lam, hbL, h6⟩
          own_eq := Or.inl ⟨rfl, rfl⟩
          next_ok := fun _ _ d' v _ hu hl hv => ⟨(lt_of_lt_of_le hs hv).ne', hu, hl⟩
          next_toks := fun v u hu => Or.inl (List.mem_singleton.mp hu)
          jn := Or.inr fun _ _ _ => rfl }
    | aft tk' c =>
      simp only [actT, Option.some.injEq, ActT.one.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
      obtain ⟨_, h2, h3⟩ := h.ph_ok
      exact
        { tk_ph := Or.inr List.mem_cons_self
          us_ph := fun _ h => absurd h List.not_mem_nil
          htu := List.not_mem_nil
          live := ⟨lam, hbL, fun _ => h2.freeAt _, h3⟩
          own_eq := Or.inl ⟨rfl, rfl⟩
          next_ok := fun _ _ d' v _ hu hl hv => ⟨(lt_of_lt_of_le hs hv).ne', hu, hl⟩
          next_toks := fun v u hu => Or.inl (List.mem_singleton.mp hu)
          jn := Or.inr fun _ _ _ => rfl }

theorem act_join {salt : Tok} {ph : PhT} {kd : Kind} {cms : List (Dig lam)} {x : Option X}
    {tk : Tok} (he : actT cms x salt kd ph = some (.join tk)) : kd = .sh ∧ ph = .loc tk := by
  cases kd with
  | sh =>
    cases ph with
    | first => simp [actT] at he
    | loc tk' =>
      simp only [actT, Option.some.injEq, ActT.join.injEq] at he
      exact ⟨rfl, by rw [he]⟩
    | aft tk' c => simp [actT] at he
    | shr tk0 c => simp [actT] at he
  | lo => cases ph <;> simp [actT] at he

/-! ## The invariant along the trees of a round -/

theorem PhTok.mem {d : DSt (typedOracleFamily lam K L)} {t : Tag} {salt sFS : ℕ} {V : List Tok} {ph : PhT}
    (h : CI d t salt sFS V ph) {u : Tok} (hu : PhTok salt ph u) : u ∈ V := by
  rcases hu with rfl | hu
  · exact h.salt_mem
  · exact h.ph_mem u hu

theorem CI.trees {d d' : DSt (typedOracleFamily lam K L)} {t : Tag} {salt sFS : ℕ} {V : List Tok} {ph : PhT}
    {e M : OracleName → ℕ} (h : CI d t salt sFS V ph)
    (hr : RunO noTok (fun u => u ∈ [salt]) noTok e M d d')
    (hk : KeepsFree (fun o => o = OracleName.leaf) d d') : CI d' t salt sFS V ph where
  salt_mem := h.salt_mem
  ph_mem := h.ph_mem
  deps := ClV.keeps h.deps hr.charges fun _ _ h => h
  ph_ok := by
    have hlive : ∀ {u n}, Live d t u n → Live d' t u n := fun hl =>
      ⟨fun m => hk _ _ (oName_ne_leaf t m) (hl.free m), hl.len.grows hr.grows⟩
    have hunt : ∀ {u}, u ≠ salt → Untouched d u → Untouched d' u := fun hne hu =>
      hu.grows hr.grows (fun hc => hne (List.mem_singleton.mp hc)) (fun h => h)
    cases ph with
    | first => exact hlive h.ph_ok
    | loc tk =>
      obtain ⟨h1, h2, h3⟩ := h.ph_ok
      exact ⟨h1, hunt h1 h2, h3.grows hr.grows⟩
    | shr tk0 c =>
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h.ph_ok
      exact ⟨h1, h2, h3, hunt h1 h4, h5.grows hr.grows, hlive h6⟩
    | aft tk c =>
      obtain ⟨h1, h2, h3⟩ := h.ph_ok
      exact ⟨h1, hunt h1 h2, h3.grows hr.grows⟩

/-! ## Counts -/

theorem jOf_lo {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s} (hk : a.kind = .lo) (ph : PhT) :
    jOf ph (r :: s) (a, A) = jOf ph s A := by
  cases ph <;> simp [jOf, joinsT, hk]

theorem jOf_sh {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s} (hk : a.kind = .sh) (tk : Tok) :
    jOf (.loc tk) (r :: s) (a, A) = 1 := by
  simp [jOf, joinsT, hk]

theorem hasTest_lo {r : Round} {a : RAnn r} {w : WireRB lam K r a} (hk : a.kind = .lo) :
    TokenSide.hasTest w = w.grJ.isSome := by
  simp [TokenSide.hasTest, hk]

theorem hasTest_sh {r : Round} {a : RAnn r} {w : WireRB lam K r a} (hk : a.kind = .sh) :
    TokenSide.hasTest w = w.gr0.isSome := by
  simp [TokenSide.hasTest, hk]

theorem eRun_join {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
    (W : RoundsQueryLayout lam K s A) (o : OracleName) :
    cnt1 (S := typedOracleFamily lam K L) OracleName.node (nLv w.depthJ) o +
        (cnt1 (S := typedOracleFamily lam K L) OracleName.node (nLv w.depth0) o + (0 + 0 + 0 + 0 + eRun s A W o)) ≤
      eRun (r :: s) (a, A) (w, W) o := by
  cases o with
  | node =>
      show nLv w.depthJ + (nLv w.depth0 + (0 + 0 + 0 + 0 + cLeaves s A W)) ≤
        ((w.depthJ.map fun d => 2 ^ d).sum + (w.depth0.map fun d => 2 ^ d).sum) + cLeaves s A W
      unfold nLv
      omega
  | _ => exact Nat.le_refl 0

theorem eRun_step {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
    (W : RoundsQueryLayout lam K s A) (nl : ℕ) (hnl : nl ≤ nLv w.depthJ + nLv w.depth0) (o : OracleName) :
    cnt1 (S := typedOracleFamily lam K L) OracleName.node nl o + eRun s A W o ≤ eRun (r :: s) (a, A) (w, W) o := by
  unfold nLv at hnl
  cases o with
  | node =>
      show nl + cLeaves s A W ≤
        ((w.depthJ.map fun d => 2 ^ d).sum + (w.depth0.map fun d => 2 ^ d).sum) + cLeaves s A W
      omega
  | _ => exact Nat.le_refl 0

theorem mChain_step (t : Tag) {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s)
    (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A) (cap : ℕ → ℕ) (dq i : ℕ) (ph ph' : PhT)
    (nl : ℕ) (b : Bool) (hnl : nl ≤ nLv w.depthJ + nLv w.depth0) (hb : b = TokenSide.hasTest w)
    (hj : jOf ph' s A ≤ jOf ph (r :: s) (a, A)) (o : OracleName) :
    cnt1 (S := typedOracleFamily lam K L) OracleName.leaf nl o +
        (mFs t b (cap i) o + mChain t s A W cap dq (i + 1) ph' o) ≤
      mChain t (r :: s) (a, A) (w, W) cap dq i ph o := by
  unfold nLv at hnl
  subst hb
  cases o with
  | leaf =>
      show nl + (0 + cLeaves s A W) ≤
        ((w.depthJ.map fun d => 2 ^ d).sum + (w.depth0.map fun d => 2 ^ d).sum) + cLeaves s A W
      omega
  | rleaf =>
      show 0 + (0 + jOf ph' s A) ≤ jOf ph (r :: s) (a, A)
      omega
  | rnode =>
      show 0 + (0 + jOf ph' s A * dq) ≤ jOf ph (r :: s) (a, A) * dq
      have := Nat.mul_le_mul_right dq hj
      omega
  | fb t' =>
      show 0 + ((if t' = t then 1 else 0) + (if t' = t then s.length else 0)) ≤
        if t' = t then s.length + 1 else 0
      split_ifs <;> omega
  | fbw t' k =>
      show 0 + ((if t' = t ∧ TokenSide.hasTest w = true ∧ k < cap i then 1 else 0) +
          (if t' = t then cTry k cap s A W (i + 1) else 0)) ≤
        if t' = t then (if TokenSide.hasTest w = true ∧ k < cap i then 1 else 0) +
          cTry k cap s A W (i + 1) else 0
      by_cases h : t' = t
      · simp only [h, true_and, if_true]
        omega
      · simp [h]
  | g t' =>
      show 0 + (0 + (if t' = t then jOf ph' s A else 0)) ≤
        if t' = t then jOf ph (r :: s) (a, A) else 0
      split_ifs <;> omega
  | _ => exact Nat.le_refl 0

theorem mChain_join (t : Tag) {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s)
    (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A) (cap : ℕ → ℕ) (dq i : ℕ) (tk : Tok) (ph' : PhT)
    (hk : a.kind = .sh) (hj : jOf ph' s A = 0) (o : OracleName) :
    cnt1 (S := typedOracleFamily lam K L) OracleName.leaf (nLv w.depthJ) o +
        (cnt1 (S := typedOracleFamily lam K L) OracleName.leaf (nLv w.depth0) o +
          (cnt1 (S := typedOracleFamily lam K L) (OracleName.g t) 1 o + cnt1 (S := typedOracleFamily lam K L) OracleName.rleaf 1 o +
            cnt1 (S := typedOracleFamily lam K L) OracleName.rnode dq o + mFs t w.gr0.isSome (cap i) o +
            mChain t s A W cap dq (i + 1) ph' o)) ≤
      mChain t (r :: s) (a, A) (w, W) cap dq i (.loc tk) o := by
  have h1 : jOf (.loc tk) (r :: s) (a, A) = 1 := jOf_sh hk tk
  have ht : TokenSide.hasTest w = w.gr0.isSome := hasTest_sh hk
  cases o with
  | leaf =>
      show nLv w.depthJ + (nLv w.depth0 + (0 + 0 + 0 + 0 + cLeaves s A W)) ≤
        ((w.depthJ.map fun d => 2 ^ d).sum + (w.depth0.map fun d => 2 ^ d).sum) + cLeaves s A W
      unfold nLv
      omega
  | rleaf =>
      show 0 + (0 + (0 + 1 + 0 + 0 + jOf ph' s A)) ≤ jOf (.loc tk) (r :: s) (a, A)
      omega
  | rnode =>
      show 0 + (0 + (0 + 0 + dq + 0 + jOf ph' s A * dq)) ≤ jOf (.loc tk) (r :: s) (a, A) * dq
      rw [h1, hj]
      omega
  | fb t' =>
      show 0 + (0 + (0 + 0 + 0 + (if t' = t then 1 else 0) + (if t' = t then s.length else 0))) ≤
        if t' = t then s.length + 1 else 0
      split_ifs <;> omega
  | fbw t' k =>
      show 0 + (0 + (0 + 0 + 0 + (if t' = t ∧ w.gr0.isSome = true ∧ k < cap i then 1 else 0) +
          (if t' = t then cTry k cap s A W (i + 1) else 0))) ≤
        if t' = t then (if TokenSide.hasTest w = true ∧ k < cap i then 1 else 0) +
          cTry k cap s A W (i + 1) else 0
      rw [ht]
      by_cases h : t' = t
      · simp only [h, true_and, if_true]
        omega
      · simp [h]
  | g t' =>
      show 0 + (0 + ((if OracleName.g t' = OracleName.g t then 1 else 0) + 0 + 0 + 0 +
          (if t' = t then jOf ph' s A else 0))) ≤
        if t' = t then jOf (.loc tk) (r :: s) (a, A) else 0
      rw [h1, hj]
      by_cases h : t' = t
      · simp [h]
      · simp [h]
  | _ => exact Nat.le_refl 0

end OnBytes.TokenRel

#print axioms OnBytes.TokenRel.act_one
#print axioms OnBytes.TokenRel.act_join
