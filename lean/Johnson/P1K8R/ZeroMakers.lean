-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/ZeroMakers.lean: THE FRAME's OWN STEPS (LAID, OPENED, CLEARED), THE REPLY (K7) AND THE
MERGE (K11) STEP IN `KeepsZero`. WHERE A LEDGER IS LAID OFF A PLAN, THE PREMISE IS THAT THE PLAN's
ROWS BEGIN AT COLUMN 0 (`AllZero`), IN THE PLACE OF THE LIBRARY's EQUATION ON THE LINK's LOOKS:
THESE FOUR STATEMENTS AND PROOFS ARE TURNED BY HAND. MADE BY PROGRAM FROM THE LIBRARY's
Johnson/Desc/First/Link/Law/LooksFrame.lean, WITH THE ROWS' FIRST COLUMNS (`l0s`,
Johnson/P1K8R/ZeroFrame.lean) IN THE PLACE OF THE ARRAYS' LOOKS AND `KeepsZero` IN THE PLACE OF
KeepsLooks: every declaration of that file that names the looks, or leans on one that does, under a
new name; the others are called where they lie. None of the library's goals. No prover stands in it;
nothing on completeness, soundness or hiding.

  `kzs_andThen`, `laid_kz`, `cleared_kz`   two sub-protocols joined; the frame's "laid" and
      "cleared"
  **`kz_laid`**, `openAtt_makesZ`, `openLay_makesZ`, `openLayZero_makesZ`   the makers
  `k7_kz`, `mergeHear_l0s`, **`k11_kz`**   the reply; the merge
Limits. THE DECISIONS ALONE. The makers' premise, `AllZero` of the plan's ledger, is shown of no
plan here (Johnson/P1K8R/ZeroSeat.lean pays it). Nothing on any reached state.

-/
import Johnson.P1K8R.ZeroFl
import Johnson.Desc.First.Link.Law.LooksFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk (LinkPub startFork emptySlots weightsAtZero layFront openAtt openLay
  openLayZero clearWith)
open Johnson.Desc.First.ForkMerge (mergeHear headMergeDecide headClaimMergeKind)
open P1K8 (l0At AllZero l0s ZeroInv KeepsZero allZero_map allZero_trees allZero_frame l0s_of_frame
  l0s_of_sums l0s_rows_map l0s_rows_modify allZero_laid allZero_start fill_l0s allZero_fill
  allZero_rests kz_refl kz_trans kz_of_cases kz_same kz_none zeroInv_none kz_trees)

/-- Two sub-protocols joined as one. -/
theorem kzs_andThen {Cl : Type} (n : String) (p q : Block S Cl)
    (hp : p.Steps KeepsZero) (hq : q.Steps KeepsZero) :
    (p.andThen n q).Steps KeepsZero :=
  Keeps.andThen_decides KeepsZero kz_trans n p q hp hq

/-! ## The frame -/

theorem laid_kz {l : ℕ} {s t : S} (h : layFront l s = .ok t) :
    KeepsZero s t := by
  rw [(Johnson.Desc.First.Walk.Law.layFront_ok h).1]
  exact kz_refl s

theorem cleared_kz {X : LinkPub} {counts : S → Except String Unit}
    {left : S → Option WsForkOut} {row : Johnson.Desc.First.Walk.RowFn} {s t : S}
    (h : clearWith X counts left row s = .ok t) : KeepsZero s t := by
  obtain ⟨_, _, _, _, _, _, _, _, hb, _⟩ := Johnson.Desc.First.Walk.Law.clearWith_ok h
  exact kz_none (fork_none_between hb)

/-! ## The maker -/

/-- **Behind the step the open ledger is the one laid off arrays whose rows begin at column 0.** -/
theorem kz_laid {s t : S} (F0 : Fork) (ns : ℕ)
    (hf : t.fork? = some (emptySlots (weightsAtZero F0) ns)) (hz : AllZero F0) :
    KeepsZero s t := by
  refine kz_of_cases fun G' hG => Or.inl ?_
  rw [← Option.some.inj (hf.symm.trans hG)]
  exact allZero_laid ns hz

/-- **«Opened» at an attention link.** -/
theorem openAtt_makesZ {P : Johnson.Desc.First.Walk.AttPar} {s t : S}
    (h : openAtt P s = .ok t) (hz : AllZero P.X.Fp) :
    KeepsZero s t := by
  obtain ⟨_, _, _, _, _, h6, _⟩ := Johnson.Desc.First.Walk.Law.openAtt_ok h
  exact kz_laid P.X.Fp P.ns h6 hz

/-- **«Opened» at a layers' link.** -/
theorem openLay_makesZ {P : Johnson.Desc.First.Walk.LayPar} {s t : S}
    (h : openLay P s = .ok t) (hz : AllZero P.X.Fp) :
    KeepsZero s t := by
  obtain ⟨_, _, _, _, _, _, h6, _⟩ := Johnson.Desc.First.Walk.Law.openLay_ok h
  exact kz_laid P.X.Fp P.ns h6 hz

/-- **«Opened» at the first link.** -/
theorem openLayZero_makesZ {P : Johnson.Desc.First.Walk.LayPar}
    {fvs : List Bool} {kCol : ℕ} {s t : S} (h : openLayZero P fvs kCol s = .ok t)
    (hz : AllZero P.X.Fp) : KeepsZero s t := by
  obtain ⟨_, _, _, _, _, _, h6, _⟩ := Johnson.Desc.First.Walk.Law.openLayZero_ok h
  exact kz_laid P.X.Fp P.ns h6 hz

/-! ## K7 -/

/-- **K7: the reply**, at any seat whose laying leaves the two readings. -/
theorem k7_kz {Cl : Type} (L : Kinds.Reply.Seat S)
    (hL : ∀ s x, (L.setReply s x).fork? = s.fork? ∧ (L.setReply s x).link? = s.link?)
    (link piece V : ℕ) : (Kinds.Reply.kind (Cl := Cl) L link piece V).Steps KeepsZero := by
  intro s rs gs s' h
  obtain ⟨_, x, _, _, _, rfl⟩ := Kinds.Head.Law.k7_ok h
  exact kzL_same (hL s x).1 (by rw [(hL s x).2])

/-! ## K11 -/

/-- The merge's hearing leaves the first columns. -/
theorem mergeHear_l0s {lay : WsLay} {cl : Array WsClaim} {sv : Array ℕ} {F G : Fork}
    {t u : Tape} {wo : WsForkOut} (h : mergeHear lay cl sv F t = .ok (wo, G, u)) :
    FlL.SameL0 F G := by
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
  exact (((((FlL.StaysZ.same (named_some e1)).trans (FlL.StaysZ.same (named_some e2))).trans
    (FlL.StaysZ.same (named_some e3))).trans (FlL.StaysZ.same (named_some e4))).trans
    (FlL.StaysZ.same (named_some e5))).trans (FlL.StaysZ.same (named_some e6))

/-- **K11: the merge of the claims on the weights.** -/
theorem k11_kz (P : Johnson.Desc.First.ForkMerge.HeadMergeP) :
    (headClaimMergeKind P).Steps KeepsZero := by
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
    refine kzL_of_cases fun G' L' hG hL' => Or.inr ⟨a.F, a.L, ?_, ?_, ?_, ?_⟩
    · simp [S.fork?, ha, hop]
    · simp [S.link?, ha, hop]
    · have e : some a.L = some L' := by simpa [S.link?, hop] using hL'
      exact congrArg (·.link) (Option.some.inj e)
    · have e : some ({ F with planClaimsF := P.nLin } : Fork) = some G' := by
        simpa [S.fork?, hop] using hG
      rw [← Option.some.inj e]
      exact (mergeHear_l0s hm : F.trees.map l0s = a.F.trees.map l0s)
  · exact nomatch h'

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.kzs_andThen
#print axioms VerifiableInference.Desc.LinkJoin.laid_kz
#print axioms VerifiableInference.Desc.LinkJoin.cleared_kz
#print axioms VerifiableInference.Desc.LinkJoin.kz_laid
#print axioms VerifiableInference.Desc.LinkJoin.openAtt_makesZ
#print axioms VerifiableInference.Desc.LinkJoin.openLay_makesZ
#print axioms VerifiableInference.Desc.LinkJoin.openLayZero_makesZ
#print axioms VerifiableInference.Desc.LinkJoin.k7_kz
#print axioms VerifiableInference.Desc.LinkJoin.mergeHear_l0s
#print axioms VerifiableInference.Desc.LinkJoin.k11_kz
