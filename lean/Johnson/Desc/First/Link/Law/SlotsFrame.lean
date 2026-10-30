-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SlotsFrame.lean: THE LINK's FRAME; K11.
ONE OF FOURTEEN FILES THAT CARRY "THE OPEN LEDGER's TWO NUMBERS" (how many slots it has: ns; how
many coefficients its list LS has) ALONG THE FIRST CHAIN: `SlotsInv nsOf s`: where a ledger and a
link are open, the two numbers are the plan's nsOf at that link's number. Their top:
Johnson/LPFK9R/SlotsSeat.lean.
The walk is adapted from LooksFrame.lean (beside this file): that file's theorems on the arrays'
looks, carried over by program to the two numbers, name by name (…looks… ↦ …slots…; else a letter S
behind the name), and righted by hand where the ground fact is another.
That file is imported for what it holds that does not speak of looks.
Limits. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LooksFrame
import Johnson.Desc.First.Link.Law.LooksWalk
import Johnson.Desc.First.Link.Law.SlotsWalk
import Johnson.Desc.First.Link.Law.FlLooks
import Johnson.Desc.First.Link.Law.FlSlots
import Johnson.Desc.BlockKeeps
import Johnson.Top.H0.Walk.FrameLaw
import Johnson.Desc.Kinds.Law.Heard
import Johnson.Desc.First.Fork.MergeKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk (LinkPub startFork emptySlots weightsAtZero layFront openAtt openLay
  openLayZero clearWith)
open Johnson.Desc.First.ForkMerge (mergeHear headMergeDecide headClaimMergeKind)

/-! ## The frame -/

theorem laid_keepsS (nsOf : ℕ → ℕ × ℕ) {l : ℕ} {s t : S} (h : layFront l s = .ok t) :
    KeepsSlots nsOf s t := by
  rw [(Johnson.Desc.First.Walk.Law.layFront_ok h).1]
  exact keeps_reflS nsOf s

theorem cleared_keepsS (nsOf : ℕ → ℕ × ℕ) {X : LinkPub} {counts : S → Except String Unit}
    {left : S → Option WsForkOut} {row : Johnson.Desc.First.Walk.RowFn} {s t : S}
    (h : clearWith X counts left row s = .ok t) : KeepsSlots nsOf s t := by
  obtain ⟨_, _, _, _, _, _, _, _, hb, _⟩ := Johnson.Desc.First.Walk.Law.clearWith_ok h
  exact keeps_noneS nsOf (fork_none_between hb)

/-! ## The maker -/

/-- **Behind the step the open ledger is the one laid off arrays with the link's two numbers.** -/
theorem keeps_laidS (nsOf : ℕ → ℕ × ℕ) {s t : S} (F0 : Fork) (ns : ℕ) (L : LinkCtx)
    (hf : t.fork? = some (emptySlots (weightsAtZero F0) ns)) (hl : t.link? = some L)
    (hsh : nsOf L.link = (ns, ns)) : KeepsSlots nsOf s t := by
  refine keeps_of_casesS nsOf fun G' L' hG hL' => Or.inl ?_
  rw [← Option.some.inj (hf.symm.trans hG), ← Option.some.inj (hl.symm.trans hL'), hsh]
  exact slots_laid F0 ns

/-- **«Opened» at an attention link.** -/
theorem openAtt_makesS (nsOf : ℕ → ℕ × ℕ) {P : Johnson.Desc.First.Walk.AttPar} {s t : S}
    (h : openAtt P s = .ok t) (hsh : nsOf P.l = (P.ns, P.ns)) :
    KeepsSlots nsOf s t := by
  obtain ⟨_, _, _, _, h5, h6, _⟩ := Johnson.Desc.First.Walk.Law.openAtt_ok h
  exact keeps_laidS nsOf P.X.Fp P.ns _ h6 h5 hsh

/-- **«Opened» at a layers' link.** -/
theorem openLay_makesS (nsOf : ℕ → ℕ × ℕ) {P : Johnson.Desc.First.Walk.LayPar} {s t : S}
    (h : openLay P s = .ok t) (hsh : nsOf P.l = (P.ns, P.ns)) :
    KeepsSlots nsOf s t := by
  obtain ⟨_, _, _, _, _, h5, h6, _⟩ := Johnson.Desc.First.Walk.Law.openLay_ok h
  exact keeps_laidS nsOf P.X.Fp P.ns _ h6 h5 hsh

/-- **«Opened» at the first link.** -/
theorem openLayZero_makesS (nsOf : ℕ → ℕ × ℕ) {P : Johnson.Desc.First.Walk.LayPar}
    {fvs : List Bool} {kCol : ℕ} {s t : S} (h : openLayZero P fvs kCol s = .ok t)
    (hsh : nsOf 0 = (P.ns, P.ns)) : KeepsSlots nsOf s t := by
  obtain ⟨_, _, _, _, _, h5, h6, _⟩ := Johnson.Desc.First.Walk.Law.openLayZero_ok h
  exact keeps_laidS nsOf P.X.Fp P.ns _ h6 h5 hsh

/-! ## K7 -/

/-- **K7: the reply**, at any seat whose laying leaves the two readings. -/
theorem k7_stepsS {Cl : Type} (nsOf : ℕ → ℕ × ℕ) (L : Kinds.Reply.Seat S)
    (hL : ∀ s x, (L.setReply s x).fork? = s.fork? ∧ (L.setReply s x).link? = s.link?)
    (link piece V : ℕ) : (Kinds.Reply.kind (Cl := Cl) L link piece V).Steps (KeepsSlots nsOf) := by
  intro s rs gs s' h
  obtain ⟨_, x, _, _, _, rfl⟩ := Kinds.Head.Law.k7_ok h
  exact keeps_sameS nsOf (hL s x).1 (by rw [(hL s x).2])

/-! ## K11 -/

/-- The merge's hearing leaves the two numbers. -/
theorem mergeHear_slots {lay : WsLay} {cl : Array WsClaim} {sv : Array ℕ} {F G : Fork}
    {t u : Tape} {wo : WsForkOut} (h : mergeHear lay cl sv F t = .ok (wo, G, u)) :
    FlS.SameSlots F G := by
  unfold mergeHear at h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨_, _, h⟩ := K9L.ok_bind h
  obtain ⟨⟨rho, F1, t1⟩, e1, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨⟨v, F2, t2⟩, e2, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨⟨p, F3, t3⟩, e3, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨⟨⟨rm, p4⟩, F4, t4⟩, e4, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨⟨⟨sFv, p5⟩, F5, t5⟩, e5, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain ⟨⟨fvp, F6, t6⟩, e6, h⟩ := K9L.ok_bind h
  dsimp only at h
  obtain rfl : F6 = G := congrArg (·.2.1) (Except.ok.inj h)
  exact (((((FlS.StaysS.same (named_some e1)).trans (FlS.StaysS.same (named_some e2))).trans
    (FlS.StaysS.same (named_some e3))).trans (FlS.StaysS.same (named_some e4))).trans
    (FlS.StaysS.same (named_some e5))).trans (FlS.StaysS.same (named_some e6))

/-- **K11: the merge of the claims on the weights.** -/
theorem k11_stepsS (nsOf : ℕ → ℕ × ℕ) (P : Johnson.Desc.First.ForkMerge.HeadMergeP) :
    (headClaimMergeKind P).Steps (KeepsSlots nsOf) := by
  intro s rs gs s' h
  have h' : headMergeDecide P s rs = .ok s' := h
  unfold headMergeDecide at h'
  split at h'
  · rename_i a ha
    obtain ⟨_, ho, h'⟩ := K9L.ok_bind h'
    obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨t, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨claim, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨x, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨⟨wo, F, t'⟩, hm, h'⟩ := K9L.ok_bind h'
    dsimp only at h'
    obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
    obtain ⟨_, _, h'⟩ := K9L.ok_bind h'
    have hop : a.opened = true := by
      cases e : a.opened with
      | true => rfl
      | false =>
        rw [e] at ho
        exact nomatch ho
    obtain rfl := Except.ok.inj h'
    refine keeps_of_casesS nsOf fun G' L' hG hL' => Or.inr ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
    · simp [S.fork?, ha, hop]
    · simp [S.link?, ha, hop]
    · have e : some a.L = some L' := by simpa [S.link?, hop] using hL'
      exact congrArg (·.link) (Option.some.inj e)
    · have e : some ({ F with planClaimsF := P.nLin } : Fork) = some G' := by
        simpa [S.fork?, hop] using hG
      rw [← Option.some.inj e]
      exact (mergeHear_slots hm : sl F = sl a.F)
  · exact nomatch h'

end VerifiableInference.Desc.LinkJoin
