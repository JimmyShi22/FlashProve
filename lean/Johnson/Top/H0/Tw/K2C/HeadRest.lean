-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/HeadRest.lean: the kind «the code switch»: WHAT THE WHOLE PLACE «H:2» LEAVES
OF THE HEAD's OWN PART OF THE RECORD: the switch writes of it the two fields kept and ids; the
record's own opening and "H.1.quiet" write opened, L and F: every other field passes unturned. NO
BLOCK IMPORTS THIS FILE.
  SameRest a b       the two parts agree in x · t · tl · claim · wo · Fm · slot · squaresP ·
                     lookHeard and fr
  switchHead_rest    a yes of the decision at a record that stands in the head's link
  headOpenQ_rest     a yes of "H.1.quiet"
  placeH2_rest       the whole place «H:2» (the switch, then "H.1.quiet")
  placeH2_noTables   so: where the tables are not laid in front of «H:2» (t = none), they are not
                     laid behind it
A frame fact: it says what the text does not write. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.HeadLedger
import Johnson.Top.H0.Tw.K2C.StandsBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)
open _root_.Tw.K2 (sendByL8)

/-- The fields of the head's part that the place «H:2» does not write. -/
def SameRest (a b : HeadOwn) : Prop :=
  b.fr = a.fr ∧ b.x = a.x ∧ b.t = a.t ∧ b.tl = a.tl ∧ b.claim = a.claim ∧ b.wo = a.wo ∧
    b.Fm = a.Fm ∧ b.slot = a.slot ∧ b.squaresP = a.squaresP ∧ b.lookHeard = a.lookHeard

theorem SameRest.trans {a b c : HeadOwn} (h : SameRest a b) (k : SameRest b c) : SameRest a c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10⟩ := k
  exact ⟨k1.trans h1, k2.trans h2, k3.trans h3, k4.trans h4, k5.trans h5, k6.trans h6,
    k7.trans h7, k8.trans h8, k9.trans h9, k10.trans h10⟩

theorem switchHead_rest {snd : _root_.Tw.K2.SendFn} {p : P2} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {a : HeadOwn}
    (h : decideWith snd p s rs gs = .ok s') (ha : s.here = .head a) :
    ∃ b, s'.here = .head b ∧ SameRest a b := by
  obtain ⟨r₁, r₂, a', G, w, roots, rfl, k⟩ := head_inv (head_of_head h ha) h
  have e : a' = a := by
    have := k.hHere.symm.trans ha
    injection this
  subst e
  refine ⟨{ a' with kept := w.out.kept, ids := w.out.others }, by rw [k.hOut], ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem headOpenQ_rest {P : HeadPar} {s s' : S} {a : HeadOwn} (h : headOpenQ P s = .ok s')
    (ha : s.here = .head a) : ∃ b, s'.here = .head b ∧ SameRest a b := by
  obtain ⟨a', st, f, mine, L, out, y, cov, s₁, b, k⟩ := (headOpenQ_iff P s s').1 h
  have e : a' = a := by
    have := k.here.symm.trans ha
    injection this
  subst e
  have h1 : s₁ = s.openHead := openHeadQ k.opens
  have h2 : s.openHead.here =
      .head { a' with opened := true, L := { a'.L with check := s.check } } := by
    unfold S.openHead
    rw [ha]
    simp [k.fresh]
  have h3 : b = { a' with opened := true, L := { a'.L with check := s.check } } := by
    have := k.opened.symm.trans (h1 ▸ h2)
    injection this
  subst h3
  have h4 : ∃ c : HeadOwn, s'.here = .head c ∧
      c = { ({ a' with opened := true, L := { a'.L with check := s.check } } : HeadOwn) with
        L := L
        F := Johnson.Desc.First.Walk.emptySlots
          (Johnson.Desc.First.Walk.weightsAtZero { trees := P.X.Fp.trees }) P.hp.ns } :=
    ⟨_, by rw [k.out'], rfl⟩
  obtain ⟨c, hc, rfl⟩ := h4
  exact ⟨_, hc, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem placeH2_rest {p : P2} {n : String} {P : HeadPar} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {a : HeadOwn}
    (h : ((codeSwitchKind p : Block S Unit).andThen n (headOpened n p.place P)).decide s rs gs = .ok s')
    (ha : s.here = .head a) : ∃ b, s'.here = .head b ∧ SameRest a b := by
  simp only [Block.andThen] at h
  obtain ⟨m, h₁, h₂⟩ := bindOk h
  obtain ⟨c, hc, r1⟩ := switchHead_rest (snd := sendByL8) (p := p) h₁ ha
  obtain ⟨b, hb, r2⟩ := headOpenQ_rest (P := P) h₂ hc
  exact ⟨b, hb, r1.trans r2⟩

theorem placeH2_noTables {p : P2} {n : String} {P : HeadPar} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : ((codeSwitchKind p : Block S Unit).andThen n (headOpened n p.place P)).decide s rs gs = .ok s')
    (hs : ∃ o, s.here = .head o ∧ o.t = none) : ∃ o', s'.here = .head o' ∧ o'.t = none := by
  obtain ⟨o, ho, ht⟩ := hs
  obtain ⟨b, hb, r⟩ := placeH2_rest h ho
  exact ⟨b, hb, r.2.2.1.trans ht⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.placeH2_rest
#print axioms VerifiableInference.Desc.First.K2.placeH2_noTables
