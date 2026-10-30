-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/KeepsWhole.lean: the kind «the code switch»: A YES OF THE SWITCH KEEPS, FROM
THE RECORD's STATEMENT IN FRONT TO THE STATEMENT BEHIND, EVERY RELATION THAT THE PLAIN GROUND's
FUNCTIONS KEEP: the sending in the midst included. NO BLOCK IMPORTS THIS FILE. K2C/Keeps.lean's
yes_keeps has the relation on both sides of the sending and leaves the sending itself to its own
law. Here the sending is walked too: inside sendP the statement is written by the receiving and by
the admitting of each sampled message alone.
  sampleLoop_keeps · sendP_keepsAll   a yes of sendP at the plain ground keeps R (GENERAL: not the
                                   switch's alone)
  yes_keeps_whole   decideWith sendByL8 p s rs gs = .ok s' → R s.st s'.st, for every R with
                    GroundKeeps R
  yes_grows         at R := Grows (Johnson/Desc/Grows.lean): the statement only grows
  yes_codes         so: s'.st.codes = s.st.codes: THE RECORD's CODES PASS THE SWITCH UNTURNED
  headFrontQ_codes · headOpenQ_codes · finishFrontQ_codes · finishBehindQ_codes   the four quiet
                                                                                  steps: the like
A frame fact. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.SendsOn
import Johnson.Top.H0.Tw.K2C.BookKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (sendByL8)
open VerifiableInference.Desc.Ground (GroundKeeps groundKeeps_grows)

variable {R : Statement → Statement → Prop}

theorem sampleLoop_keeps (H : GroundKeeps R) {p : Desc.Plain.GPar} {codes : Codes}
    {seeds : List SampleSeed} :
    ∀ (l : List (Nat × OracleShape)) (ys : List E) (d d' : Desc.Plain.DState Unit) (left : List E),
      Desc.Plain.sampleLoop Desc.Plain.groundG p codes seeds l ys d = some (d', left) → R d.st d'.st
  | [], ys, d, d', left, h => by
    simp only [Desc.Plain.sampleLoop, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact H.refl _
  | (o, s) :: l, ys, d, d', left, h => by
    simp only [Desc.Plain.sampleLoop] at h
    split at h
    · cases h
    · rename_i rows ys' _
      split at h
      · cases h
      · rename_i d₁ ha
        exact H.trans (H.admit d d₁ o rows ha) (sampleLoop_keeps H l ys' d₁ d' left h)

theorem sendP_keepsAll (H : GroundKeeps R) {p : Desc.Plain.GPar} {own : Bool}
    {d d' : Desc.Plain.DState Unit} {sent : Array OracleNotice} {r₁ r₂ : Fmt.RoundView} {ids sd an need}
    (h : Desc.Plain.sendP Desc.Plain.groundG p own d sent r₁ r₂ = some (ids, sd, an, need, d')) :
    R d.st d'.st := by
  unfold Desc.Plain.sendP at h
  obtain ⟨⟨ids', d₁⟩, h1, h⟩ := optBindB h
  dsimp only at h
  obtain ⟨shapes, _, h⟩ := optBindB h
  obtain ⟨seeds, _, h⟩ := optBindB h
  obtain ⟨an', _, h⟩ := optBindB h
  split at h
  · obtain ⟨⟨d₂, left⟩, h2, h⟩ := optBindB h
    dsimp only at h
    split at h
    · cases h
      exact H.trans (H.recv _ _ _ _ _ h1) (sampleLoop_keeps H _ _ _ _ _ h2)
    · cases h
  · cases h

theorem yes_keeps_whole (H : GroundKeeps R) {p : P2} {s : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {s' : S}
    (h : decideWith sendByL8 p s rs gs = .ok s') : R s.st s'.st := by
  obtain ⟨r₁, r₂, x, ids, sd, an, took, d', _, hs, h1, h2⟩ := yes_keeps H h
  exact H.trans h1 (H.trans (sendP_keepsAll H hs) h2)

theorem yes_grows {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (h : decideWith sendByL8 p s rs gs = .ok s') : Desc.Grows s.st s'.st :=
  yes_keeps_whole groundKeeps_grows h

theorem yes_codes {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (h : decideWith sendByL8 p s rs gs = .ok s') : s'.st.codes = s.st.codes :=
  (yes_grows h).1

theorem headOpenQ_codes {P : HeadPar} {s s' : S} (h : headOpenQ P s = .ok s') :
    s'.st.codes = s.st.codes := (headOpenQ_keeps groundKeeps_grows h).1

theorem finishFrontQ_codes {s s' : S} (h : finishFrontQ s = .ok s') : s'.st.codes = s.st.codes :=
  (finishFrontQ_keeps groundKeeps_grows h).1

theorem finishBehindQ_codes {s s' : S} (h : finishBehindQ s = .ok s') :
    s'.st.codes = s.st.codes := by rw [finishBehindQ_st h]

theorem headFrontQ_codes {tl : HTailF2} {s s' : S} (h : headFrontQ tl s = .ok s') :
    s'.st.codes = s.st.codes := by
  obtain ⟨x, s₁, a, k⟩ := (headFrontQ_iff tl s s').1 h
  rw [k.out]
  exact (firstFront_keeps groundKeeps_grows k.front).1

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.sendP_keepsAll
#print axioms VerifiableInference.Desc.First.K2.yes_keeps_whole
#print axioms VerifiableInference.Desc.First.K2.yes_codes
#print axioms VerifiableInference.Desc.First.K2.headFrontQ_codes
