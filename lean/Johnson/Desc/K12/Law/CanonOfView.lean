-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.CanonOk
/-
Johnson/Desc/K12/Law/CanonOfView.lean: canonOk (Johnson/Desc/K12/Law/CanonOk.lean: every element that a round drew has its three words below the field's size) FED FROM viewWordsBelowPrime (Johnson/Desc/Block.lean: the decision's own test on a whole view). NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. NO NEW MATHEMATICS.
WHY. accK_yes_real_const | _own (Johnson/Desc/K12/Law/AccKConst.lean | AccKOwn.lean) take «canonOk rs' = true» as a premise, and no block asks it: Block.step asks roundsFit, the columns and the kind's decide, and none of these holds a word against the prime. The decision asks it ONCE, on each whole view, in front of the folds (runCore: three calls of viewWordsBelowPrime). So the premise is paid at the whole view and carried down to a block's stretch.
  primeW_toNat          the prime as a word is the field's size (Fmt.Fld.two.p).
  canonE_of_lt          viewWordsBelowPrime's clause on a drawn element is canonE's yes.
  canonOk_of_okViewW    viewWordsBelowPrime v = true ⇒ canonOk v.rounds = true.
  canonOk_sublist       canonOk goes down to every sublist.
  canonOk_withSealW     viewWordsBelowPrime v = true ⇒ canonOk (withEmptySealRound v).rounds = true: the round that the first chain's fold lays behind the view draws nothing.
  sublist_withSealW     a sublist of the view's rounds is one of the rounds with the seal's round behind them: so ONE form serves all three chains.
  canonOk_tail          viewWordsBelowPrime v = true, and r0 :: rs' a sublist of (withEmptySealRound v).rounds ⇒ canonOk rs' = true: the premise hcan as the two tops take it.
No sorry and no axiom of our own stands in this file.
LIMITS. (1) THAT A BLOCK's ROUNDS ARE A SUBLIST OF THE VIEW's IS A PREMISE HERE (hin): it is the fold's to pay (each block takes its own rounds off the front of the list: Johnson/Desc/K12/Law/CanonAtFold.lean's stretch_sublist). hin TIES THE VIEW TO rs' FOR canonOk ALONE, and for nothing else: a sublist, not a stretch, since canonOk is an «all». (2) One direction: viewWordsBelowPrime asks more (the items' words, the opened columns' words): nothing of that is spent here. (3) Nothing is said of the sealed digest: it is no element.
-/
set_option autoImplicit false
namespace H2K.First
open VerifiableInference.Desc VerifiableInference.Desc.K12

theorem primeW_toNat : fieldPrimeWord.toNat = Fmt.Fld.two.p := by decide

theorem canonE_of_lt (x : Fmt.Ext)
    (h : (x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true) : canonE x = true := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold canonE
  simp only [Bool.and_eq_true, decide_eq_true_eq, ← primeW_toNat]
  exact ⟨⟨UInt64.lt_iff_toNat_lt.1 h.1.1, UInt64.lt_iff_toNat_lt.1 h.1.2⟩,
    UInt64.lt_iff_toNat_lt.1 h.2⟩

/-- The decision's test on a whole view gives canonOk of all its rounds. -/
theorem canonOk_of_okViewW (v : Fmt.View) (h : viewWordsBelowPrime v = true) : canonOk v.rounds = true := by
  unfold viewWordsBelowPrime at h
  rw [Bool.and_eq_true] at h
  unfold canonOk
  rw [List.all_eq_true]
  intro r hr
  have h1 := List.all_eq_true.1 h.1 r hr
  rw [Bool.and_eq_true] at h1
  rw [List.all_eq_true]
  intro x hx
  exact canonE_of_lt x (List.all_eq_true.1 h1.1 x hx)

theorem canonOk_sublist {l l' : List Fmt.RoundView} (hs : l.Sublist l') (h : canonOk l' = true) :
    canonOk l = true := by
  unfold canonOk at h ⊢
  rw [List.all_eq_true] at h ⊢
  exact fun r hr => h r (hs.subset hr)

theorem canonOk_withSealW (v : Fmt.View) (h : viewWordsBelowPrime v = true) :
    canonOk (withEmptySealRound v).rounds = true := by
  have h0 := canonOk_of_okViewW v h
  unfold canonOk at h0 ⊢
  show (v.rounds ++ [(⟨[], ⟨[], [], [], none⟩⟩ : Fmt.RoundView)]).all _ = true
  rw [List.all_append, h0]
  rfl

theorem sublist_withSealW {l : List Fmt.RoundView} (v : Fmt.View) (h : l.Sublist v.rounds) :
    l.Sublist (withEmptySealRound v).rounds :=
  h.trans (List.sublist_append_left _ _)

/-- THE PREMISE «canonOk rs' = true» OF accK_yes_real_const | _own, PAID BY THE DECISION's OWN TEST ON THE WHOLE VIEW. -/
theorem canonOk_tail {v : Fmt.View} (hv : viewWordsBelowPrime v = true) {r0 : Fmt.RoundView} {rs' : List Fmt.RoundView}
    (hin : (r0 :: rs').Sublist (withEmptySealRound v).rounds) : canonOk rs' = true :=
  canonOk_sublist ((List.sublist_cons_self r0 rs').trans hin) (canonOk_withSealW v hv)

end H2K.First

#print axioms H2K.First.primeW_toNat
#print axioms H2K.First.canonOk_of_okViewW
#print axioms H2K.First.canonOk_withSealW
#print axioms H2K.First.canonOk_tail
