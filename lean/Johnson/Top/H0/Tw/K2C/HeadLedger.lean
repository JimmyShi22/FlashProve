-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/HeadLedger.lean: the kind «the code switch»: WHO LAYS THE SUB-PROOF's LEDGER
AT THE HEAD's LINK, AND WHAT IS LAID. NO BLOCK IMPORTS THIS FILE. At the head's link the ledger
(the record's Fork) is laid by the second half of the place «H:2», the quiet step "H.1.quiet"
(headOpenQ, K2C/Head.lean), behind the switch of the same place: until then the link counts as not
opened and S.fork? answers nothing.
  headOpenQ_fork   a yes of "H.1.quiet": S.fork? behind it is just emptySlots (weightsAtZero {
                   trees := P.X.Fp.trees }) P.hp.ns
  headOpenQ_laid   so: its four arrays on slots (gotF · vp · mf · LS) have one entry a slot, the
                   number of slots is the letter P.hp.ns, and the next free slot is 0
  headOpenQ_none   in front of it S.fork? answers nothing
  placeH2_fork     the whole place «H:2» (the switch, then "H.1.quiet"): the same ledger behind it
A frame fact: it reads off what the text lays. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.AsksWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)
open Johnson.Desc.First.Walk (emptySlots weightsAtZero)

theorem headOpenQ_fork {P : HeadPar} {s s' : S} (h : headOpenQ P s = .ok s') :
    s'.fork? = some (emptySlots (weightsAtZero { trees := P.X.Fp.trees }) P.hp.ns) := by
  obtain ⟨_, ⟨b', hb', ho⟩, _⟩ := headOpenOpens P s s' h
  obtain ⟨a, st, f, mine, L, out, y, cov, s₁, b, k⟩ := (headOpenQ_iff P s s').1 h
  have e : s'.here = .head { b with
      L := L, F := emptySlots (weightsAtZero { trees := P.X.Fp.trees }) P.hp.ns } := by
    rw [k.out']
  rw [hb'] at e
  injection e with e
  unfold S.fork?
  rw [hb']
  simp only [ho, if_true]
  rw [e]

theorem headOpenQ_laid {P : HeadPar} {s s' : S} (h : headOpenQ P s = .ok s') :
    ∃ F, s'.fork? = some F ∧ F.ns = P.hp.ns ∧ F.gotF.size = F.ns ∧ F.vp.size = F.ns ∧
      F.mf.size = F.ns ∧ F.LS.size = F.ns ∧ F.next = 0 :=
  ⟨_, headOpenQ_fork h, rfl, by simp [emptySlots], by simp [emptySlots], by simp [emptySlots],
    by simp [emptySlots], rfl⟩

theorem headOpenQ_none {P : HeadPar} {s s' : S} (h : headOpenQ P s = .ok s') : s.fork? = none := by
  obtain ⟨⟨a, ha, ho⟩, _, _⟩ := headOpenOpens P s s' h
  unfold S.fork?
  rw [ha]
  simp [ho]

theorem placeH2_fork {p : P2} {n : String} {P : HeadPar} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : ((codeSwitchKind p : Block S Unit).andThen n (headOpened n p.place P)).decide s rs gs = .ok s') :
    s'.fork? = some (emptySlots (weightsAtZero { trees := P.X.Fp.trees }) P.hp.ns) := by
  simp only [Block.andThen] at h
  obtain ⟨s₁, _, h₂⟩ := bindOk h
  exact headOpenQ_fork h₂

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.headOpenQ_fork
#print axioms VerifiableInference.Desc.First.K2.headOpenQ_laid
#print axioms VerifiableInference.Desc.First.K2.placeH2_fork
