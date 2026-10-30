-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/KeepsAny.lean: A FIELD OF THE RECORD IS KEPT BY THE TWO MOVES OF A LINK,
AT EACH OF THE THREE SORTS, FOR WHATEVER FIELD RESTS UNDER FOUR WRITINGS: `MoveKeeps f`
(Johnson/Desc/First/Batch/Law/KeepsField.lean) at `moves₁ L rl ++ moves₂ L`, from the ties of the
assembly (PayLayers.lean, PayAttention.lean, PayHead.lean). KeepsRuns.lean said it of the mark of
failure alone; here the field is a letter.

Why. What the table's promise reads of the record (the mark, the rows that are owed a count, the
book, the statement's groups) must ride over the link's three pieces. Each is a function f of the
record. All that the runs of a link write, as far as the assembly knows them, is: the smallness
test's record; the open segment's ledger; what a run of the layers' own kind writes; the head's
ledger.

What is said.
  `FieldRests f`: f rests under these four writings. `hands_keeps`, `idle_keeps`, `merge_keeps`,
    `join_keepsF`, `k8Run_keeps`, `k8LsTail_keeps`, `k8Tests_keeps`: so each known run keeps f.
    `keeps_layers`, `keeps_attention`, `keeps_head`: **the duty of both moves at each sort**, from
    `FieldRests f`, the sort's Take and, as it stands, the same duty of the lookup's runs.
    `rests_failed`, `rests_owed`, `rests_book`: the mark, the rows owed (`K9.owedOf`) and the book
    rest.

Limits. IMPLICATIONS, as the three structures are. The lookup's runs' duty stays a premise. Nothing
on soundness.

-/
import Johnson.Desc.First.Link.Law.KeepsRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Wrote frontAtC backAtC)
open VerifiableInference.Desc.First.MergeLaw (claim_inv)
open Johnson.Desc.First.ForkMerge (headMergeClaim)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K4Run
open VerifiableInference.Desc.StillRun
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open K5Law

variable {β γ : Type}

/-- **The field rests under the four writings.** -/
structure FieldRests (f : S → γ) : Prop where
  tl : ∀ s tl, f (s.putTl tl) = f s
  fork : ∀ s G, f (s.putFork G) = f s
  wrote : ∀ e a G e₁, Wrote e a G e₁ → f e₁ = f e
  head : ∀ (s : S) (a : First.HeadOwn) (G : Fork), s.here = .head a →
    f { s with here := .head { a with F := G } } = f s

variable (f : S → γ)

/-- A run that hands the record back keeps every field. -/
theorem hands_keeps {run : ℕ → S → Except String (List Claim × S)}
    (hh : ∀ n e c e₁, run n e = .ok (c, e₁) → e₁ = e) (n : ℕ) (e : S) (c : List Claim) (e₁ : S)
    (hr : run n e = .ok (c, e₁)) : f e₁ = f e := by
  rw [hh n e c e₁ hr]

theorem idle_keeps {run : ℕ → S → Except String (List Claim × S)} (h : Idle run) (n : ℕ) (e : S)
    (c : List Claim) (e₁ : S) (hr : run n e = .ok (c, e₁)) : f e₁ = f e := by
  obtain rfl : e = e₁ := congrArg Prod.snd (Except.ok.inj ((h n e).symm.trans hr))
  rfl

variable {f}

theorem merge_keeps (R : FieldRests f) (n : ℕ) (e : S) (c : List Claim) (e₁ : S)
    (hr : headMergeClaim n e = .ok (c, e₁)) : f e₁ = f e := by
  obtain ⟨a, wo, G, h1, hwo, rfl, rfl, hrunG⟩ := claim_inv hr
  exact R.head e a G h1

theorem join_keepsF (R : FieldRests f) (h : OnBytes.Model.Head.Shape) (iU3 : ℕ) (p : Par) (n : ℕ)
    (e : S) (c : List Claim) (e₁ : S)
    (hr : K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3)) n e = .ok (c, e₁)) :
    f e₁ = f e := by
  obtain ⟨a, i, h1, rfl⟩ := join_hands h iU3 p n e c e₁ hr
  exact R.head e a _ h1

theorem k8Run_keeps (R : FieldRests f) (front : ℕ) (e e₁ : S) (c : List Claim)
    (h : k8Run.2 front e = .ok (c, e₁)) : f e₁ = f e := by
  obtain ⟨G, tl, funs, tl', F1, _, _, _, _, rfl⟩ := k8Run_ok front e e₁ c h
  rw [R.fork, R.tl]

theorem k8LsTail_keeps (R : FieldRests f) (e e₁ : S) (h : k8LsTail e = .ok e₁) : f e₁ = f e := by
  obtain ⟨G, tl, _, _, rfl⟩ := k8LsTail_ok e e₁ h
  exact R.tl e _

theorem k8Tests_keeps (R : FieldRests f) (nU : Array ℕ) (e e₁ : S)
    (h : k8Tests nU e = .ok e₁) : f e₁ = f e := by
  obtain ⟨G, tl, g, _, _, _, _, _, rfl⟩ := k8Tests_ok nU e e₁ h
  rw [R.fork, R.tl]

/-- **BOTH MOVES OF A LAYERS' LINK KEEP THE FIELD.** -/
theorem keeps_layers (R : FieldRests f) {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .layers L) {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {p : OnBytes.Desc.First.K4.Par} {nU : Array ℕ}
    {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : LayersTake L u ψ Ok Fu p nU ent tm4 t3 l3)
    (k3f : ∀ o ∈ [(1, "objects"), (6, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → f e₁ = f e)
    (rl : List (TermedRun S (Q β) Cb.Gl.E)) :
    ∀ m ∈ moves₁ L rl ++ moves₂ (α := Phi β) L, MoveKeeps f m.move := by
  obtain ⟨eo, ea⟩ := order_at hL
  refine moves_keepL f L rl ?_ ?_
  · rw [eo, order_layers]
    refine ⟨k3f _ (by simp),
      fun run h => keep_under _ (A.ties.tGuests 1 (by simp) run h) (idle_keeps f fun _ _ => rfl),
      fun run h n e c e₁ hr => ?_, k3f _ (by simp),
      fun run h => keep_under _ (A.ties.tGuests 6 (by simp) run h) (idle_keeps f fun _ _ => rfl),
      fun run h => ?_, fun run h n e c e₁ hr => ?_⟩
    · obtain ⟨r, h0, hu⟩ := A.ties.tFront run h
      obtain ⟨a, _, _, G, _, _, _, hw⟩ := frontAtC h0 (hu n e c e₁ hr)
      exact R.wrote _ _ _ _ hw
    · exact keep_under _ (A.ties.tEq run h) fun n e c e₁ hr => k8Run_keeps R n e e₁ c hr
    · obtain ⟨r, h0, hu⟩ := A.ties.tBack run h
      obtain ⟨a, _, _, G, _, _, _, hw⟩ := backAtC h0 (hu n e c e₁ hr)
      exact R.wrote _ _ _ _ hw
  · rw [ea, after_layers]
    refine ⟨fun run h => ?_, fun run h e e₁ hr => ?_, fun run h => ?_⟩
    · exact keepAfter_under _ (A.ties.tLs run h) (k8LsTail_keeps R)
    · obtain ⟨r, h0, hu⟩ := A.ties.tFree run h
      obtain ⟨a, hw⟩ := k4_freeSlot_wrote h0 (hu e e₁ hr)
      exact R.wrote _ _ _ _ hw
    · exact keepAfter_under _ (A.ties.tTests run h) (k8Tests_keeps R nU)

/-- **BOTH MOVES OF AN ATTENTION LINK KEEP THE FIELD.** -/
theorem keeps_attention (R : FieldRests f) {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .attention L) {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)}
    {c : First.Att.P.ParC} {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : AttTake L u ψ Ok Fu rd c nU ent tm4 t3 l3)
    (k3f : ∀ o ∈ [(1, "objects"), (2, "join"), (1, "planes"), (6, "objects")], ∀ run,
      At L o run → ∀ n e c' e₁, run n e = .ok (c', e₁) → f e₁ = f e)
    (rl : List (TermedRun S (Q β) Cb.Gl.E)) :
    ∀ m ∈ moves₁ L rl ++ moves₂ (α := Phi β) L, MoveKeeps f m.move := by
  obtain ⟨eo, ea⟩ := order_at hL
  refine moves_keepL f L rl ?_ ?_
  · rw [eo, order_attention]
    refine ⟨k3f _ (by simp),
      fun run h => keep_under _ (A.ties.tGuests 1 (by simp) run h) (idle_keeps f fun _ _ => rfl),
      fun run h => ?_, fun run h => ?_, k3f _ (by simp), fun run h => ?_, k3f _ (by simp),
      k3f _ (by simp),
      fun run h => keep_under _ (A.ties.tGuests 6 (by simp) run h) (idle_keeps f fun _ _ => rfl),
      fun run h => ?_⟩
    · exact keep_under _ (A.ties.tFirst run h)
        (hands_keeps f (still_first (phiAll u ψ) Ok rd c A.hrd A.okK5).hands)
    · exact keep_under _ (A.ties.tKeys run h) (hands_keeps f (still_keys (phiAll u ψ) Ok c).hands)
    · exact keep_under _ (A.ties.tSecond run h)
        (hands_keeps f (still_second (phiAll u ψ) Ok rd c A.hrd A.okK5).hands)
    · exact keep_under _ (A.ties.tEq run h) fun n e c' e₁ hr => k8Run_keeps R n e e₁ c' hr
  · rw [ea, after_attention]
    refine ⟨fun run h => ?_, fun run h => ?_⟩
    · exact keepAfter_under _ (A.ties.tLs run h) (k8LsTail_keeps R)
    · exact keepAfter_under _ (A.ties.tTests run h) (k8Tests_keeps R nU)

/-- **BOTH MOVES OF THE HEAD's LINK KEEP THE FIELD.** -/
theorem keeps_head (R : FieldRests f) {l : ℕ} {L : Link S Claim}
    (hL : SegAt l .head L) {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop}
    {Fu : S → Prop} {h : OnBytes.Model.Head.Shape} {iU3 l' piece : ℕ} {p : Par}
    {kap : Phi β → Option Seen} {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : HeadTake L u ψ Ok Fu h iU3 l' piece p kap nU ent tm4 t3 l3)
    (k3f : ∀ o ∈ [(2, "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → f e₁ = f e)
    (rl : List (TermedRun S (Q β) Cb.Gl.E)) :
    ∀ m ∈ moves₁ L rl ++ moves₂ (α := Phi β) L, MoveKeeps f m.move := by
  obtain ⟨eo, ea⟩ := order_at hL
  have k6 : ∀ name ∈ ["norm", "policy", "logits"], ∀ run, At L (3, name) run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → f e₁ = f e := fun name hn run hr => by
    obtain ⟨r, h0, hu⟩ := A.ties.tK6 name hn run hr
    exact keep_under _ hu (hands_keeps f
      (k6_still h iU3 p (phiAll u ψ) Ok kap A.hkap A.okK6 l' piece name r h0).hands)
  refine moves_keepL f L rl ?_ ?_
  · rw [eo, order_head]
    refine ⟨k3f _ (by simp),
      fun run hr => keep_under _ (A.ties.tGuests 2 (by simp) run hr) (idle_keeps f fun _ _ => rfl),
      k6 "norm" (by simp), fun run hr => ?_, k6 "policy" (by simp), k3f _ (by simp),
      k3f _ (by simp),
      fun run hr => keep_under _ (A.ties.tGuests 7 (by simp) run hr) (idle_keeps f fun _ _ => rfl),
      fun run hr => ?_, k6 "logits" (by simp), fun run hr => ?_⟩
    · exact keep_under _ (A.ties.tJoin run hr) (join_keepsF R h iU3 p)
    · exact keep_under _ (A.ties.tEq run hr) fun n e c e₁ hr => k8Run_keeps R n e e₁ c hr
    · exact keep_under _ (A.ties.tMerge run hr) (merge_keeps R)
  · rw [ea, after_head]
    refine ⟨fun run hr => ?_, fun run hr => ?_⟩
    · exact keepAfter_under _ (A.ties.tLs run hr) (k8LsTail_keeps R)
    · exact keepAfter_under _ (A.ties.tTests run hr) (k8Tests_keeps R nU)


/-! ## Three fields that rest -/

/-- The two puts turn «here» alone. -/
theorem putTl_here (s : S) (tl : HTailF2) : ∃ x, s.putTl tl = { s with here := x } := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [S.putTl, ho]
  | _ => exact ⟨_, rfl⟩

theorem putFork_here (s : S) (G : Fork) : ∃ x, s.putFork G = { s with here := x } := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here with
  | head x => by_cases ho : x.opened = true <;> simp [S.putFork, ho]
  | _ => exact ⟨_, rfl⟩

/-- The mark rests. -/
theorem rests_failed : FieldRests (·.failed) where
  tl s tl := by obtain ⟨x, e⟩ := putTl_here s tl; rw [e]
  fork s G := by obtain ⟨x, e⟩ := putFork_here s G; rw [e]
  wrote _ _ _ _ hw := wrote_failed hw
  head _ _ _ _ := rfl

/-- The book rests. -/
theorem rests_book : FieldRests (·.book) where
  tl s tl := by obtain ⟨x, e⟩ := putTl_here s tl; rw [e]
  fork s G := by obtain ⟨x, e⟩ := putFork_here s G; rw [e]
  wrote _ _ _ _ hw := by obtain ⟨_, rfl⟩ := hw; rfl
  head _ _ _ _ := rfl

/-- The rows that are owed a count rest: a run of the layers' own kind reads the debt once through
the lens, which turns «some 0» to «none»: the reading of the rows owed takes the two alike. -/
theorem rests_owed : FieldRests K9.owedOf where
  tl s tl := by obtain ⟨x, e⟩ := putTl_here s tl; rw [e]; rfl
  fork s G := by obtain ⟨x, e⟩ := putFork_here s G; rw [e]; rfl
  wrote e _ _ _ hw := by
    obtain ⟨_, rfl⟩ := hw
    unfold K9.owedOf S.noneWaits
    cases h : e.rowsOwed with
    | none => rfl
    | some r =>
      cases r with
      | zero => rfl
      | succ k => rfl
  head _ _ _ _ := rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.keeps_layers
#print axioms VerifiableInference.Desc.LinkJoin.keeps_attention
#print axioms VerifiableInference.Desc.LinkJoin.keeps_head
#print axioms VerifiableInference.Desc.LinkJoin.rests_failed
#print axioms VerifiableInference.Desc.LinkJoin.rests_book
#print axioms VerifiableInference.Desc.LinkJoin.rests_owed
