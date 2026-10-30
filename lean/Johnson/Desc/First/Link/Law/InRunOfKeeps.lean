-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/InRunOfKeeps.lean (kind K9): THE FIELD inRun OF A LINK's «REST» (`CoreRest2`, LinkRestAtSort2.lean): «behind a yes of the runs behind the batching (`L.runBehind`), before the piece's end, every entry that
the open segment's data read lies inside the ranges of the member at its seat» (`InsideAt`): FROM THE SAME SENTENCE AT THE STATE IN FRONT OF THESE RUNS, AT ALL THREE SORTS OF LINK. Definitions and theorems.

Why. The state behind `L.runBehind` is not itself «reached»: so the payer of inSeg | inTot (`insideAt_reached`, PartFitsReached.lean) does not speak of it. That file's `insideAt_congr` says what `InsideAt` reads of a part: the link's
own copy of the calls' state, the statement, the book, and the ledger's two numbers. The runs behind the batching (K8.lsTail · free-slot · K8.tests) turn none of these.

What is said.
  `insF e`: **the reading**: the open link's record, the statement, the book, and the open ledger's two numbers (`sl`: its slots; its list of coefficients' length).
  `insF_putTl`, `insF_putFork`, `insF_ls`, `insF_tests`, `insF_free`: the two layings and the three runs keep it.
  `insF_after_layers`, `insF_after_attention`, `insF_after_head`: so every run of the sort's order behind the batching keeps it: from the sort's Take's ties alone (NO clause on the lookup's runs is asked).
  `inRun_of_keeps`: **the field's text**, general in the link and in the condition on1: from: every run behind the batching keeps insF · at on1 a part is there [the field Ahs1] · at on1 `InsideAt` holds of the part.
  AT THE THREE SORTS: `inRun_of_keeps … (insF_after_layers hL A) …` and its two likes: one call each: not named here.

Limits. IMPLICATIONS. «`InsideAt` at the part of a state with on1» is a premise: the form of inTot, one border earlier: `insideAt_reached` serves it (the place in front of the sub-protocol behind the batching lies within its bound on
the piece's number). The Takes are premises. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.PartFitsReached
import Johnson.Desc.First.Link.Law.JoinKeeps
import Johnson.Desc.First.Link.Law.SlotsRuns
import Johnson.Desc.First.Link.Law.RelRuns
import Johnson.Desc.First.Batch.BlindK3
import Johnson.Desc.First.LedgerLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Wrote)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.K4Run (k4_freeSlot_wrote)
open VerifiableInference.Desc.Kinds.Head (Par)
open VerifiableInference.Desc.Kinds.Head.Law (Seen)

variable {β : Type} {F : Frame}

/-- **What `InsideAt` reads of the state.** -/
def insF (e : S) : Option LinkCtx × Statement × TreeBook × Option (ℕ × ℕ) :=
  (e.link?, e.st, e.book, e.fork?.map sl)

theorem insF_putTl (e : S) (tl : HTailF2) : insF (e.putTl tl) = insF e := by
  unfold insF
  rw [First.K8.putTl_link, First.K8.putTl_fork, (rb_putTl e tl).st, (rb_putTl e tl).book]

theorem insF_putFork (e : S) (G₀ G : Fork) (hF : e.fork? = some G₀) (h : sl G = sl G₀) :
    insF (e.putFork G) = insF e := by
  unfold insF
  rw [link_putFork, (rb_putFork e G).st, (rb_putFork e G).book, First.fork_putFork e G₀ G hF, hF]
  show (_, _, _, some (sl G)) = (_, _, _, some (sl G₀))
  rw [h]

theorem insF_ls (e e₁ : S) (h : k8LsTail e = .ok e₁) : insF e₁ = insF e := by
  obtain ⟨G, tl, _, _, rfl⟩ := k8LsTail_ok e e₁ h
  exact insF_putTl e _

theorem insF_tests (nU : Array ℕ) (e e₁ : S) (h : k8Tests nU e = .ok e₁) : insF e₁ = insF e := by
  obtain ⟨G, tl, g, hF, _, _, _, _, rfl⟩ := k8Tests_ok nU e e₁ h
  exact (insF_putFork _ G _ (by rw [First.K8.putTl_fork]; exact hF)
    (sameSlots_of fun sh => (slots_rests sh).coef tl g G)).trans (insF_putTl e tl)

theorem insF_free {e e₁ : S} {a : First.LayOwn} (hw : Wrote e a a.F e₁) : insF e₁ = insF e := by
  obtain ⟨h1, rfl⟩ := hw
  unfold insF
  simp [S.link?, S.fork?, h1]

/-! ## The three sorts' orders behind the batching -/

theorem insF_after_layers {l : ℕ} {L : Link S Claim} (hL : SegAt l .layers L) {u : HTailF2}
    {ψ : S → β} {Ok : Q β → Prop} {Fu : S → Prop} {p : OnBytes.Desc.First.K4.Par} {nU : Array ℕ}
    {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : LayersTake L u ψ Ok Fu p nU ent tm4 t3 l3) :
    ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → insF e₁ = insF e := by
  obtain ⟨-, ea⟩ := order_at hL
  rw [ea, after_layers]
  refine ⟨fun run h => ?_, fun run h e e₁ hr => ?_, fun run h => ?_⟩
  · exact relAfter_under (B := fun e e₁ => insF e₁ = insF e) (A.ties.tLs run h) insF_ls
  · obtain ⟨r, h0, hu⟩ := A.ties.tFree run h
    obtain ⟨a, hw⟩ := k4_freeSlot_wrote h0 (hu e e₁ hr)
    exact insF_free hw
  · exact relAfter_under (B := fun e e₁ => insF e₁ = insF e) (A.ties.tTests run h) (insF_tests nU)

theorem insF_after_attention {l : ℕ} {L : Link S Claim} (hL : SegAt l .attention L)
    {u : HTailF2} {ψ : S → β} {Ok : Q β → Prop} {Fu : S → Prop}
    {rd : Phi β → Option (Forest.Heard × First.Att.P.Heard)} {c : First.Att.P.ParC}
    {nU : Array ℕ} {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8}
    {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : AttTake L u ψ Ok Fu rd c nU ent tm4 t3 l3) :
    ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → insF e₁ = insF e := by
  obtain ⟨-, ea⟩ := order_at hL
  rw [ea, after_attention]
  refine ⟨fun run h => ?_, fun run h => ?_⟩
  · exact relAfter_under (B := fun e e₁ => insF e₁ = insF e) (A.ties.tLs run h) insF_ls
  · exact relAfter_under (B := fun e e₁ => insF e₁ = insF e) (A.ties.tTests run h) (insF_tests nU)

theorem insF_after_head {l : ℕ} {L : Link S Claim} (hL : SegAt l .head L) {u : HTailF2}
    {ψ : S → β} {Ok : Q β → Prop} {Fu : S → Prop} {h : OnBytes.Model.Head.Shape}
    {iU3 l' piece : ℕ} {p : Par} {kap : Phi β → Option Seen} {nU : Array ℕ}
    {ent : Q β → Bound GE8 → ℕ → ℕ → ℕ → GE8} {tm4 : ℕ → Q β → Bound GE8 → List (ℕ × GE8)}
    {t3 : ℕ × String → ℕ → Q β → Bound GE8 → List (ℕ × GE8)} {l3 : ℕ × String → Q β → ℕ}
    (A : HeadTake L u ψ Ok Fu h iU3 l' piece p kap nU ent tm4 t3 l3) :
    ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ → insF e₁ = insF e := by
  obtain ⟨-, ea⟩ := order_at hL
  rw [ea, after_head]
  refine ⟨fun run hr => ?_, fun run hr => ?_⟩
  · exact relAfter_under (B := fun e e₁ => insF e₁ = insF e) (A.ties.tLs run hr) insF_ls
  · exact relAfter_under (B := fun e e₁ => insF e₁ = insF e) (A.ties.tTests run hr)
      (insF_tests nU)

/-! ## The field -/

/-- **THE FIELD inRun, GENERAL IN THE LINK.** -/
theorem inRun_of_keeps (cs : OnBytes.Codes) (ms : List Mem) (own : List (ℕ × ℕ))
    (L : Link S Claim)
    (hq : ∀ o ∈ L.orderAfter, ∀ run, AtAfter L o run → ∀ e e₁, run e = .ok e₁ →
      insF e₁ = insF e)
    (on1 : S × F.E.Str → Prop) (hs1 : ∀ b, on1 b → (atS.get? b.1).isSome = true)
    (hin : ∀ b, on1 b → ∀ x, atS.get? b.1 = some x → InsideAt cs ms own x) :
    ∀ b, on1 b → ∀ s' a, L.runBehind b.1 = .ok s' → atS.get? s' = some a →
      InsideAt cs ms own a := by
  intro b hb s' a hr ha
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (hs1 b hb)
  have e : insF s' = insF b.1 := runBehind_keep insF L hq b.1 s' hr
  unfold insF at e
  obtain ⟨e1, e⟩ := Prod.mk.inj e
  obtain ⟨e2, e⟩ := Prod.mk.inj e
  obtain ⟨e3, e4⟩ := Prod.mk.inj e
  obtain ⟨a1, a2⟩ := part_reads s' a ha
  obtain ⟨x1, x2⟩ := part_reads b.1 x hx
  have hL : a.L = x.L := Option.some.inj (a1.symm.trans (e1.trans x1))
  rw [K9.get_fork s' a ha, K9.get_fork b.1 x hx] at e4
  have h4 : sl a.F = sl x.F := Option.some.inj e4
  obtain ⟨n1, n2⟩ := Prod.mk.inj h4
  refine insideAt_congr (hin b hb x hx) (by rw [hL]) (a2.trans (e2.trans x2.symm))
    ((part_bookOf s' a ha).trans (e3.trans (part_bookOf b.1 x hx).symm)) fun j hj => ?_
  rw [← n1, ← n2]
  exact hj

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.insF_ls
#print axioms VerifiableInference.Desc.LinkJoin.insF_tests
#print axioms VerifiableInference.Desc.LinkJoin.insF_free
#print axioms VerifiableInference.Desc.LinkJoin.insF_after_layers
#print axioms VerifiableInference.Desc.LinkJoin.insF_after_attention
#print axioms VerifiableInference.Desc.LinkJoin.insF_after_head
#print axioms VerifiableInference.Desc.LinkJoin.inRun_of_keeps
