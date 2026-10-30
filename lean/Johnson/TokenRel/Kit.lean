-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenRel/Kit.lean: SMALL TOOLS ON TOKEN PROGRAMS, beside the library's calculus for the
rules of deferred programming (Compile/Batch/Discipline.lean, DisciplineKit.lean,
DisciplineRun.lean), which is called and not written again. General in the family of oracles.

General lemmas. This file states no goal of the release. The token programs are a device of one step
of a proof of index privacy and stand in no statement on the scheme.

The files of this folder walk the token programs of Johnson/TokenSide/ once and show of them all
that the rules of deferred programming ask AND what the rule of release asks
(Johnson/TokenRules/ReleaseSpec.lean): which evaluations a run adds, to which tokens they are
charged, and, for leaves, at which points and with which answers.

  KeepsFree P d d'   A token that can be charged at an oracle outside P in the state d can still be
                     charged there in d'.
  run_ofPlain        An ordinary query as a run (Run, Compile/Batch/DisciplineRun.lean).
  Adds P d d'        The evaluations of d' are those of d, unchanged, and then new ones, of each of
                     which P holds: what a run that reveals nothing does to the list.
  filter_adds        The evaluations that are charged to a token stay, if no new one is charged to
                     it.
  MarkedAt           All that is used of the state after one marked evaluation.
  safe_mark          One marked evaluation keeps the rules and ends in MarkedAt, with what the state
                     notes of the evaluation written out.

-/
import Johnson.TokenRules.ReleaseSpec

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

section Kit
variable {S : OSpec} {sp : Split S} {Rl : Rules S} {α : Type}

/-- no evaluation -/
abbrev zr : S.ι → ℕ := fun _ => 0

/-- See the head. -/
def KeepsFree (P : S.ι → Prop) (d d' : DSt S) : Prop :=
  ∀ o u, ¬ P o → FreeAt d o u → FreeAt d' o u

theorem KeepsFree.refl (P : S.ι → Prop) (d : DSt S) : KeepsFree P d d := fun _ _ _ h => h

theorem KeepsFree.trans {P : S.ι → Prop} {d d' d'' : DSt S} (h₁ : KeepsFree P d d')
    (h₂ : KeepsFree P d' d'') : KeepsFree P d d'' := fun o u ho h => h₂ o u ho (h₁ o u ho h)

theorem KeepsFree.ofPlain (P : S.ι → Prop) (d : DSt S) (o : S.ι) (T : Table S) :
    KeepsFree P d (afterPlain d o T) := fun _ _ _ h => ⟨h.lt, h.not_shown, h.fresh⟩

theorem KeepsFree.ofFresh (P : S.ι → Prop) (d : DSt S) (v : Bits) :
    KeepsFree P d (afterFresh d v) := fun _ _ _ h =>
  ⟨by rw [length_afterFresh]; exact Nat.lt_succ_of_lt h.lt, h.not_shown, h.fresh⟩

theorem KeepsFree.ofMark (d : DSt S) (o : S.ι) (t : Tok) (us : List Tok) (P : S.Dom o)
    (r : S.Rng o) (T : Table S) :
    KeepsFree (fun o' => o' = o) d (afterMark sp d o t us P r T) := fun o' u ho h =>
  ⟨by rw [length_afterMark]; exact Nat.lt_succ_of_lt h.lt, h.not_shown, fun e he heo => by
    rcases mem_evs_afterMark he with he | rfl
    · exact h.fresh e he heo
    · exact absurd heo.symm ho⟩

theorem run_ofPlain {Cc Ch R : Tok → Prop} {M : S.ι → ℕ} (d : DSt S) (o : S.ι) (T : Table S) :
    RunO Cc Ch R (cnt1 o 1) M d (afterPlain d o T) :=
  ⟨GrowsO.ofPlain d o T, (GrowsO.ofPlain (Ch := Cc) (R := R) (M := M) d o T).charges,
    fun e₀ h => ⟨e₀, h, rfl, rfl, rfl, rfl⟩⟩

/-! ### What a run that reveals nothing adds to the list of evaluations -/

/-- The evaluations of d' are those of d, unchanged, and then new ones, of each of which P holds. -/
def Adds (P : Ev S → Prop) (d d' : DSt S) : Prop :=
  ∃ new, d'.evs = d.evs ++ new ∧ ∀ e ∈ new, P e

theorem Adds.refl (P : Ev S → Prop) (d : DSt S) : Adds P d d :=
  ⟨[], (List.append_nil _).symm, fun _ h => absurd h List.not_mem_nil⟩

theorem Adds.trans {P : Ev S → Prop} {d d' d'' : DSt S} (h₁ : Adds P d d') (h₂ : Adds P d' d'') :
    Adds P d d'' := by
  obtain ⟨n₁, e₁, p₁⟩ := h₁
  obtain ⟨n₂, e₂, p₂⟩ := h₂
  exact ⟨n₁ ++ n₂, by rw [e₂, e₁, List.append_assoc],
    fun e he => (List.mem_append.mp he).elim (p₁ e) (p₂ e)⟩

/-- A weaker clause; what is known of all evaluations of d' may be used. -/
theorem Adds.mono {P P' : Ev S → Prop} {d d' : DSt S} (h : Adds P d d')
    (hp : ∀ e ∈ d'.evs, P e → P' e) : Adds P' d d' := by
  obtain ⟨n, e, p⟩ := h
  exact ⟨n, e, fun x hx => hp x (by rw [e]; exact List.mem_append_right _ hx) (p x hx)⟩

theorem Adds.ofPlain (P : Ev S → Prop) (d : DSt S) (o : S.ι) (T : Table S) :
    Adds P d (afterPlain d o T) :=
  ⟨[], (List.append_nil _).symm, fun _ h => absurd h List.not_mem_nil⟩

theorem Adds.ofFresh (P : Ev S → Prop) (d : DSt S) (v : Bits) : Adds P d (afterFresh d v) :=
  ⟨[], (List.append_nil _).symm, fun _ h => absurd h List.not_mem_nil⟩

/-- The evaluations that are charged to s stay the same along a run that charges s no more. -/
theorem filter_adds {P : Ev S → Prop} {d d' : DSt S} (h : Adds P d d') {s : Tok}
    (hP : ∀ e, P e → e.charged ≠ s) :
    (d'.evs.filter fun e => e.charged == s) = d.evs.filter fun e => e.charged == s := by
  obtain ⟨n, e, p⟩ := h
  have h0 : (n.filter fun e => e.charged == s) = [] :=
    List.filter_eq_nil_iff.mpr fun x hx => by simpa using hP x (p x hx)
  rw [e, List.filter_append, h0, List.append_nil]

/-- The state d' after one marked evaluation at o from d, charged to t, with the further tokens us;
e: the token of the tail. -/
structure MarkedAt (Rl : Rules S) (sp : Split S) (d d' : DSt S) (o : S.ι) (t : Tok)
    (us : List Tok) (e : Tok) : Prop where
  tidy : TidyO Rl d'
  eq : e = d.vals.length
  run : RunO (fun u => u = t) (fun u => u = t ∨ u ∈ us) noTok zr (cnt1 o 1) d d'
  free : KeepsFree (fun o' => o' = o) d d'
  unt : Untouched d' e
  len : Len d' e (sp.tl o)
  deps : ∀ l, Deps d t l → Deps d' t (e :: (us ++ l))
  evs : ∃ (P : S.Dom o) (r : S.Rng o), d'.evs = d.evs ++ [⟨o, P, r, t, us, e, false⟩]

/-- One marked evaluation, whose result is a function of the visible part and the tail's token. -/
theorem safe_mark {d : DSt S} {o : S.ι} {t : Tok} {us : List Tok} (hd : TidyO Rl d)
    (hus : ∀ u ∈ us, u < d.vals.length) (htu : t ∉ us) (hf : FreeAt d o t)
    (hb : Rl.bits o ≤ (d.val t).length) (hmk : ∀ P, Rl.Mk o P)
    (pt : Bits → List Bits → S.Dom o) (inj : ∀ vs, Function.Injective fun v => pt v vs)
    (f : sp.Vis o → Tok → α) :
    SafeO Rl (Step.marked o t us pt inj fun v e => Step.pure (f v e)) d fun a d' =>
      ∃ r e, a = f (sp.split o r).1 e ∧ MarkedAt Rl sp d d' o t us e ∧
        d'.evs = d.evs ++ [⟨o, pt (d.val t) (us.map d.val), r, t, us, e, false⟩] :=
  ⟨hus, htu, hf, hb, hmk _, fun r T => ⟨r, _, rfl,
    { tidy := hd.mark hus htu hf _ hb (hmk _) r T
      evs := ⟨_, r, rfl⟩
      eq := rfl
      run := Run.ofMark d o t us _ r T
      free := KeepsFree.ofMark d o t us _ r T
      unt := Untouched.of_tail hd hf.lt hus _ r T
      len := Len.of_tail d o t us _ r T
      deps := fun _ h => Deps.of_mark h _ r T }, rfl⟩⟩

theorem MarkedAt.adds {d d' : DSt S} {o : S.ι} {t e : Tok} {us : List Tok}
    (hm : MarkedAt Rl sp d d' o t us e) : Adds (fun e' => e'.o = o ∧ e'.charged = t) d d' := by
  obtain ⟨P, r, h⟩ := hm.evs
  exact ⟨_, h, fun x hx => by rw [List.mem_singleton.mp hx]; exact ⟨rfl, rfl⟩⟩

end Kit


end OnBytes.TokenRel

#print axioms OnBytes.TokenRel.safe_mark
