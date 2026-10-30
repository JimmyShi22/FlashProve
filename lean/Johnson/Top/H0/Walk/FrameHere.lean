-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameHere.lean: the link's part of the record behind "opened", to the letter: at
a yes of openAtt, openLay or openLayZero the field "here" is the plan's letters and the chain's own
state of the calls, and nothing else: so whatever a public condition reads of the link's part at
that record (the ledger, the lookups' state, the smallness test's record, the link's own context)
is a computation on the plan's letters and s.check.

  openedAtt_here, openedLay_here, openedZero_here

No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameTiedRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

theorem openedAtt_here {P : AttPar} {s t : S} (h : openAtt P s = .ok t) :
    t.here = .att { L := { check := s.check, link := P.l, arrayOf := P.X.arrayOf, list := P.X.Tp },
                    F := startFork P.X P.ns,
                    tl := { P.tl₀ with funClosed := false, foldDrawn := 0 },
                    d := default, x := default } := by
  obtain ⟨_, _, _, _, h5, h6, _⟩ := Law.openAtt_ok h
  have h7 := Law.openAtt_tl h
  obtain ⟨a, e⟩ := openAtt_eq h
  subst e
  simp only [S.link?, S.fork?, S.tl?, Option.some.injEq] at h5 h6 h7
  simp only [h5, h6, h7]

theorem openedLay_here {P : LayPar} {s t : S} (h : openLay P s = .ok t) :
    t.here = .lay { L := { check := s.check, link := P.l, arrayOf := P.X.arrayOf, list := P.X.Tp },
                    F := startFork P.X P.ns, tl := P.tl₀ } := by
  obtain ⟨_, _, _, _, _, h5, h6, _⟩ := Law.openLay_ok h
  obtain ⟨a, e⟩ := openLay_eq h
  subst e
  simp only [S.link?, S.fork?, Option.some.injEq] at h5 h6
  simp only [h5, h6]

theorem openedZero_here {P : LayPar} {fvs : List Bool} {kCol : Nat} {s t : S}
    (h : openLayZero P fvs kCol s = .ok t) :
    t.here = .lay { L := { check := s.check, link := 0, arrayOf := P.X.arrayOf, list := P.X.Tp },
                    F := startFork P.X P.ns, tl := P.tl₀ } := by
  obtain ⟨_, _, _, _, _, h5, h6, _⟩ := Law.openLayZero_ok h
  obtain ⟨a, e⟩ := openLayZero_eq h
  subst e
  simp only [S.link?, S.fork?, Option.some.injEq] at h5 h6
  simp only [h5, h6]

#print axioms openedAtt_here
#print axioms openedLay_here
#print axioms openedZero_here

end Johnson.Desc.First.Walk.Tied
