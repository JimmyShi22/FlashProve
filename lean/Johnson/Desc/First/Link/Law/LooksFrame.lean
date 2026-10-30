-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LooksFrame.lean: THE LINK's FRAME, THE MAKER, THE REPLY (K7) AND THE
MERGE
(K11): THEIR SHARES OF THE WALK OF Johnson/Desc/First/Link/Law/LooksWalk.lean («the ledger's arrays
have the plan's shapes»). Theorems. No text already in the library turns.

  `fork_none_between`: between two links no ledger is open.
  `steps_quiet`: a sub-protocol without a round steps as its function does. `steps_andThen`: two
    sub-protocols joined as one (`Block.andThen`): so a step without a round that is joined behind a
    sending or a lookup is asked for itself.
  THE FRAME. `laid_keeps`: «laid» (`layFront`) hands the state on (`layFront_ok`,
    Johnson/Top/H0/Walk/FrameLaw.lean); `laid_between`: AND IN FRONT OF IT NO LEDGER IS OPEN: what
    `hasFork_reach_from` asks at a link's first border. `cleared_keeps`: «cleared» (`clearWith`)
    leaves the state between two links: no ledger behind.
  THE MAKER. `keeps_laid`: behind the step the open ledger is the one that is laid off a list of
    arrays whose looks are `shOf` of the open link's number. `openAtt_makes`, `openLay_makes`,
    `openLayZero_makes`: **«opened» at an attention link, a layers' link, the first link**
    (`openAtt_ok`, `openLay_ok`, `openLayZero_ok`: the ledger behind is `startFork P.X P.ns`), UNDER
    ONE PREMISE ON THE PLAN: `shOf` at the link's number is the looks of P.X.Fp's arrays.
  K7. `k7_steps`: the reply, at any seat whose laying leaves the two readings.
  K11. `mergeHear_looks`: the merge's hearing is six steps of the plain engine, each with its
    instance in Johnson/Desc/First/Link/Law/FlLooks.lean: NO PREMISE ON THE SIZES. `k11_steps`:
    **(headClaimMergeKind P).Steps (KeepsLooks shOf)**.
Limits. NOT HERE: THE HEAD's LINK's MAKER (its ledger is laid by the code switch into a part that is
not yet opened, and opened by a later step: `keeps_laid` is the tool, the two steps' texts are not
read here) · that the IOP's own sub-protocols at these places stand under these functions (the
seats' ties) · the premise on `shOf`. THE DECISIONS ALONE. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LooksWalk
import Johnson.Desc.First.Link.Law.FlLooks
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

/-- Between two links no ledger is open. -/
theorem fork_none_between {s : S} (h : s.atBetween = true) : s.fork? = none := by
  unfold S.atBetween at h
  unfold S.fork?
  split at h
  · rename_i hb
    rw [hb]
  · exact nomatch h

/-- A sub-protocol without a round steps as its function does. -/
theorem steps_quiet {Cl : Type} {R : S → S → Prop} (n : String) (chain : ℕ) (link : Option ℕ)
    (piece : ℕ) (f : S → Except String S) (hf : ∀ s s', f s = .ok s' → R s s') :
    (roundlessBlock (Cl := Cl) n chain link piece f).Steps R := fun s _ _ s' h => hf s s' h

/-- Two sub-protocols joined as one. -/
theorem steps_andThen {Cl : Type} (shOf : ℕ → List Look) (n : String) (p q : Block S Cl)
    (hp : p.Steps (KeepsLooks shOf)) (hq : q.Steps (KeepsLooks shOf)) :
    (p.andThen n q).Steps (KeepsLooks shOf) :=
  Keeps.andThen_decides (KeepsLooks shOf) (keeps_trans shOf) n p q hp hq

/-! ## The frame -/

theorem laid_keeps (shOf : ℕ → List Look) {l : ℕ} {s t : S} (h : layFront l s = .ok t) :
    KeepsLooks shOf s t := by
  rw [(Johnson.Desc.First.Walk.Law.layFront_ok h).1]
  exact keeps_refl shOf s

/-- In front of «laid», and behind it, no ledger is open. -/
theorem laid_between {l : ℕ} {s t : S} (h : layFront l s = .ok t) :
    s.fork? = none ∧ t.fork? = none := by
  obtain ⟨e, hb, _⟩ := Johnson.Desc.First.Walk.Law.layFront_ok h
  rw [e]
  exact ⟨fork_none_between hb, fork_none_between hb⟩

theorem cleared_keeps (shOf : ℕ → List Look) {X : LinkPub} {counts : S → Except String Unit}
    {left : S → Option WsForkOut} {row : Johnson.Desc.First.Walk.RowFn} {s t : S}
    (h : clearWith X counts left row s = .ok t) : KeepsLooks shOf s t := by
  obtain ⟨_, _, _, _, _, _, _, _, hb, _⟩ := Johnson.Desc.First.Walk.Law.clearWith_ok h
  exact keeps_none shOf (fork_none_between hb)

/-! ## The maker -/

/-- **Behind the step the open ledger is the one laid off arrays with the link's looks.** -/
theorem keeps_laid (shOf : ℕ → List Look) {s t : S} (F0 : Fork) (ns : ℕ) (L : LinkCtx)
    (hf : t.fork? = some (emptySlots (weightsAtZero F0) ns)) (hl : t.link? = some L)
    (hsh : shOf L.link = F0.trees.toList.map look) : KeepsLooks shOf s t := by
  refine keeps_of_cases shOf fun G' L' hG hL' => Or.inl ?_
  rw [← Option.some.inj (hf.symm.trans hG), ← Option.some.inj (hl.symm.trans hL'), hsh]
  exact looks_laid F0 ns

/-- **«Opened» at an attention link.** -/
theorem openAtt_makes (shOf : ℕ → List Look) {P : Johnson.Desc.First.Walk.AttPar} {s t : S}
    (h : openAtt P s = .ok t) (hsh : shOf P.l = P.X.Fp.trees.toList.map look) :
    KeepsLooks shOf s t := by
  obtain ⟨_, _, _, _, h5, h6, _⟩ := Johnson.Desc.First.Walk.Law.openAtt_ok h
  exact keeps_laid shOf P.X.Fp P.ns _ h6 h5 hsh

/-- **«Opened» at a layers' link.** -/
theorem openLay_makes (shOf : ℕ → List Look) {P : Johnson.Desc.First.Walk.LayPar} {s t : S}
    (h : openLay P s = .ok t) (hsh : shOf P.l = P.X.Fp.trees.toList.map look) :
    KeepsLooks shOf s t := by
  obtain ⟨_, _, _, _, _, h5, h6, _⟩ := Johnson.Desc.First.Walk.Law.openLay_ok h
  exact keeps_laid shOf P.X.Fp P.ns _ h6 h5 hsh

/-- **«Opened» at the first link.** -/
theorem openLayZero_makes (shOf : ℕ → List Look) {P : Johnson.Desc.First.Walk.LayPar}
    {fvs : List Bool} {kCol : ℕ} {s t : S} (h : openLayZero P fvs kCol s = .ok t)
    (hsh : shOf 0 = P.X.Fp.trees.toList.map look) : KeepsLooks shOf s t := by
  obtain ⟨_, _, _, _, _, h5, h6, _⟩ := Johnson.Desc.First.Walk.Law.openLayZero_ok h
  exact keeps_laid shOf P.X.Fp P.ns _ h6 h5 hsh

/-! ## K7 -/

/-- **K7: the reply**, at any seat whose laying leaves the two readings. -/
theorem k7_steps {Cl : Type} (shOf : ℕ → List Look) (L : Kinds.Reply.Seat S)
    (hL : ∀ s x, (L.setReply s x).fork? = s.fork? ∧ (L.setReply s x).link? = s.link?)
    (link piece V : ℕ) : (Kinds.Reply.kind (Cl := Cl) L link piece V).Steps (KeepsLooks shOf) := by
  intro s rs gs s' h
  obtain ⟨_, x, _, _, _, rfl⟩ := Kinds.Head.Law.k7_ok h
  exact keeps_same shOf (hL s x).1 (by rw [(hL s x).2])

/-! ## K11 -/

theorem named_some {α : Type} {n : String} {x : Option α} {y : α} (h : named n x = .ok y) :
    x = some y := by
  cases x with
  | none => exact nomatch h
  | some z => exact congrArg some (Except.ok.inj h)

/-- The merge's hearing leaves the looks. -/
theorem mergeHear_looks {lay : WsLay} {cl : Array WsClaim} {sv : Array ℕ} {F G : Fork}
    {t u : Tape} {wo : WsForkOut} (h : mergeHear lay cl sv F t = .ok (wo, G, u)) :
    FlL.SameLooks F G := by
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
  exact (((((FlL.Stays.same (named_some e1)).trans (FlL.Stays.same (named_some e2))).trans
    (FlL.Stays.same (named_some e3))).trans (FlL.Stays.same (named_some e4))).trans
    (FlL.Stays.same (named_some e5))).trans (FlL.Stays.same (named_some e6))

/-- **K11: the merge of the claims on the weights.** -/
theorem k11_steps (shOf : ℕ → List Look) (P : Johnson.Desc.First.ForkMerge.HeadMergeP) :
    (headClaimMergeKind P).Steps (KeepsLooks shOf) := by
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
    refine keeps_of_cases shOf fun G' L' hG hL' => Or.inr ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
    · simp [S.fork?, ha, hop]
    · simp [S.link?, ha, hop]
    · have e : some a.L = some L' := by simpa [S.link?, hop] using hL'
      exact congrArg (·.link) (Option.some.inj e)
    · have e : some ({ F with planClaimsF := P.nLin } : Fork) = some G' := by
        simpa [S.fork?, hop] using hG
      rw [← Option.some.inj e]
      exact (mergeHear_looks hm : F.trees.map look = a.F.trees.map look)
  · exact nomatch h'

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.steps_andThen
#print axioms VerifiableInference.Desc.LinkJoin.laid_keeps
#print axioms VerifiableInference.Desc.LinkJoin.laid_between
#print axioms VerifiableInference.Desc.LinkJoin.cleared_keeps
#print axioms VerifiableInference.Desc.LinkJoin.keeps_laid
#print axioms VerifiableInference.Desc.LinkJoin.openAtt_makes
#print axioms VerifiableInference.Desc.LinkJoin.openLay_makes
#print axioms VerifiableInference.Desc.LinkJoin.openLayZero_makes
#print axioms VerifiableInference.Desc.LinkJoin.k7_steps
#print axioms VerifiableInference.Desc.LinkJoin.mergeHear_looks
#print axioms VerifiableInference.Desc.LinkJoin.k11_steps
