-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRel/Path.lean: LISTS OF TOKENS THAT ARE CLOSED, and the joining round's evaluations (g,
the request tree's leaf, the request path) as token programs.

General lemmas. This file states no goal of the release. The token programs are a device of one step
of a proof of index privacy and stand in no statement on the scheme.

  ClV d V   The list V is closed in the state d: each of its tokens exists, and the tail and the
            further tokens of each evaluation that is charged to it are in V. It is the clause
            "deps" of the chain's invariant (CI, Johnson/TokenRel/Inv.lean).
  ClV.perm, ClV.keeps, ClV.mark, ClV.hit   It hangs on membership alone; it stays along a run that
            charges none of its tokens; one marked evaluation that is charged to a token of V and
            holds tokens of V alone adds its tail; a Fiat-Shamir query adds the tails of all tries.
  safe_gT, safe_rleafT, safe_climbT   the programs keep the rules.
Follows the pattern of Compile/Batch/DisciplineReq.lean, at one slot.

-/
import Johnson.TokenRel.Search

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

/-! ## Closed lists -/

section Closed
variable {S : OSpec} {sp : Split S} {Rl : Rules S}

/-- See the head. -/
def ClV (d : DSt S) (V : List Tok) : Prop := ∀ u ∈ V, u < d.vals.length ∧ Deps d u V

theorem ClV.perm {d : DSt S} {V V' : List Tok} (h : ClV d V) (hp : ∀ u, u ∈ V' ↔ u ∈ V) :
    ClV d V' := fun u hu =>
  ⟨(h u ((hp u).mp hu)).1, (h u ((hp u).mp hu)).2.mono fun v hv => (hp v).mpr hv⟩

theorem ClV.keeps {d d' : DSt S} {V : List Tok} {Cc : Tok → Prop} (h : ClV d V)
    (hc : Charges Cc d d') (hn : ∀ u ∈ V, ¬ Cc u) : ClV d' V := fun u hu =>
  ⟨lt_of_lt_of_le (h u hu).1 hc.vals.length_le, (h u hu).2.keeps (h u hu).1 hc (hn u hu)⟩

/-- A run that charges of the old tokens tk alone, after which tk depends on N and V alone, and
nothing holds the tokens of N: V grows by N. -/
theorem ClV.extend {d d' : DSt S} {V N : List Tok} {tk : Tok} (h : ClV d V)
    (hc : Charges (fun u => u = tk) d d') (hdp : Deps d' tk (N ++ V))
    (hN : ∀ u ∈ N, Untouched d' u) : ClV d' (N ++ V) := fun u hu => by
  rcases List.mem_append.mp hu with hu | hu
  · exact ⟨(hN u hu).lt, (hN u hu).deps _⟩
  · refine ⟨lt_of_lt_of_le (h u hu).1 hc.vals.length_le, ?_⟩
    by_cases e : u = tk
    · rw [e]
      exact hdp
    · exact ((h u hu).2.keeps (h u hu).1 hc e).mono fun v hv => List.mem_append_right _ hv

theorem ClV.mark {d d' : DSt S} {V us : List Tok} {o : S.ι} {t e : Tok} (h : ClV d V)
    (hm : MarkedAt Rl sp d d' o t us e) (ht : t ∈ V) (hus : ∀ u ∈ us, u ∈ V) :
    ClV d' (e :: V) :=
  ClV.extend (N := [e]) h hm.run.charges
    ((hm.deps V (h t ht).2).mono fun v hv => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_append] at hv ⊢
      rcases hv with h | h | h
      · exact Or.inl h
      · exact Or.inr (hus v h)
      · exact Or.inr h)
    (fun u hu => by rw [List.mem_singleton.mp hu]; exact hm.unt)

/-- one marked evaluation without further tokens, as a run -/
theorem MarkedAt.run0 {d d' : DSt S} {o : S.ι} {t e : Tok} (hm : MarkedAt Rl sp d d' o t [] e) :
    RunO (fun u => u = t) (fun u => u = t) noTok zr (cnt1 o 1) d d' :=
  hm.run.mono (fun _ h => Or.inl h)
    (fun _ h => h.elim Or.inl fun h => absurd h List.not_mem_nil) (fun _ h => Or.inl h)
    (fun _ => le_rfl) (fun _ => le_rfl)

end Closed

theorem ClV.hit {d d' : DSt (typedOracleFamily lam K L)} {V : List Tok} {tk : Tok} {n₀ : ℕ} {P : Type}
    {q : Hit lam K P} (h : ClV d V) (hc : Charges (fun u => u = tk) d d')
    (hq : HitOK n₀ d' tk V q) : ClV d' ((q.tl :: q.dead) ++ V) :=
  ClV.extend h hc hq.deps fun u hu => by
    rcases List.mem_cons.mp hu with rfl | hu
    · exact hq.unt
    · exact (hq.dead u hu).2

/-! ## The joining round's evaluations -/

theorem safe_gT (t : Tag) (i : ℕ) (tk : Tok) (rt : List (Dig lam))
    (pl : PlainPart (shapeOf L t) (annOf L t)) {d : DSt (typedOracleFamily lam K L)}
    (hd : TidyO (rulesT K L lam bl bf sd) d) (hu : Untouched d tk) (hl : Len d tk lam) :
    SafeO (rulesT K L lam bl bf sd) (gT (K := K) t i tk rt pl) d fun c d' =>
      MarkedAt (rulesT K L lam bl bf sd) (splitT lam K L) d d' (OracleName.g t) tk [] c := by
  refine SafeO.mono ?_ _ _ (safe_mark hd (fun _ h => absurd h List.not_mem_nil) List.not_mem_nil
    (hu.freeAt (OracleName.g t)) (le_of_eq hl.2.symm) (fun _ => by trivial) _ _ _)
  rintro a d' ⟨r, e, rfl, hm, _⟩
  exact hm

theorem safe_rleafT (c : Tok) (rs : Bits) {d : DSt (typedOracleFamily lam K L)}
    (hd : TidyO (rulesT K L lam bl bf sd) d) (hu : Untouched d c) (hl : Len d c lam) :
    SafeO (rulesT K L lam bl bf sd) (rleafT (K := K) (L := L) c rs) d fun e d' =>
      MarkedAt (rulesT K L lam bl bf sd) (splitT lam K L) d d' OracleName.rleaf c [] e := by
  refine SafeO.mono ?_ _ _ (safe_mark hd (fun _ h => absurd h List.not_mem_nil) List.not_mem_nil
    (hu.freeAt OracleName.rleaf) (le_of_eq hl.2.symm) (fun _ => by trivial) _ _ _)
  rintro a d' ⟨r, e, rfl, hm, _⟩
  exact hm

theorem safe_rnode (j : ℕ) (c : Tok) (s : Dig lam) {d : DSt (typedOracleFamily lam K L)}
    (hd : TidyO (rulesT K L lam bl bf sd) d) (hu : Untouched d c) (hl : Len d c lam) :
    SafeO (rulesT K L lam bl bf sd)
      (if j % 2 = 0 then rnodeL (K := K) (L := L) c s else rnodeR s c) d fun e d' =>
      MarkedAt (rulesT K L lam bl bf sd) (splitT lam K L) d d' OracleName.rnode c [] e := by
  split
  · refine SafeO.mono ?_ _ _ (safe_mark hd (fun _ h => absurd h List.not_mem_nil) List.not_mem_nil
      (hu.freeAt OracleName.rnode) (le_of_eq hl.2.symm) (fun _ => by trivial) _ _ _)
    rintro a d' ⟨r, e, rfl, hm, _⟩
    exact hm
  · refine SafeO.mono ?_ _ _ (safe_mark hd (fun _ h => absurd h List.not_mem_nil) List.not_mem_nil
      (hu.freeAt OracleName.rnode) (le_of_eq hl.2.symm) (fun _ => by trivial) _ _ _)
    rintro a d' ⟨r, e, rfl, hm, _⟩
    exact hm

/-- **The request path**: from a token c of a closed list V that nothing holds. The list grows by
the path's tokens; nothing holds the root's token, which is c or one of them. -/
theorem safe_climbT : ∀ (ss : List (Dig lam)) (j : ℕ) (c : Tok) (V : List Tok)
    (d : DSt (typedOracleFamily lam K L)), TidyO (rulesT K L lam bl bf sd) d → ClV d V → c ∈ V →
      Untouched d c → Len d c lam →
    SafeO (rulesT K L lam bl bf sd) (climbT (K := K) (L := L) ss j c) d fun r d' =>
      TidyO (rulesT K L lam bl bf sd) d' ∧
      RunO (fun u => u = c) (fun u => u = c) noTok zr (cnt1 OracleName.rnode ss.length) d d' ∧
      ClV d' (r.2 ++ V) ∧ (r.1 = c ∨ r.1 ∈ r.2) ∧ Untouched d' r.1 ∧ Len d' r.1 lam ∧
      (∀ u ∈ r.2, d.vals.length ≤ u) ∧
      Adds (fun e => e.o ≠ OracleName.leaf ∧ (e.charged = c ∨ e.charged ∈ r.2)) d d'
  | [], _, _, _, d, hd, hV, _, hu, hl =>
      ⟨hd, Run.refl d, hV, Or.inl rfl, hu, hl, fun _ h => absurd h List.not_mem_nil, Adds.refl _ d⟩
  | s :: ss, j, c, V, d, hd, hV, hc, hu, hl => by
      rw [climbT]
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_rnode j c s hd hu hl))
      rintro u d₁ hm
      refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_climbT ss (j / 2) u (u :: V) d₁ hm.tidy
        (hV.mark hm hc fun _ h => absurd h List.not_mem_nil) List.mem_cons_self hm.unt hm.len))
      rintro r d₂ ⟨hd₂, hr₂, hV₂, hmem, hu₂, hl₂, hnew, ha₂⟩
      refine ⟨hd₂, hm.run0.trans hr₂ (fun _ h => Or.inr (le_of_eq (h.trans hm.eq).symm))
        (fun _ h => Or.inr (le_of_eq (h.trans hm.eq).symm)) (fun _ h => Or.inl h)
        (fun _ => le_rfl) ?_, hV₂.perm fun v => ?_, ?_, hu₂, hl₂, ?_,
        (hm.adds.mono fun e _ h => ⟨(fun hc => nomatch h.1.symm.trans hc), Or.inl h.2⟩).trans
          (ha₂.mono fun e _ h => ⟨h.1, Or.inr (h.2.elim (fun h' => h' ▸ List.mem_cons_self)
            fun h' => List.mem_cons_of_mem _ h')⟩)⟩
      · intro o
        simp only [cnt1, List.length_cons]
        split <;> omega
      · simp only [List.cons_append, List.mem_cons, List.mem_append]
        tauto
      · rcases hmem with h | h
        · exact Or.inr (h ▸ List.mem_cons_self)
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact le_of_eq hm.eq.symm
        · exact le_trans hm.run.length_le (hnew v hv)

end OnBytes.TokenRel

#print axioms OnBytes.TokenRel.safe_climbT
