-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Tail/PlacesOne.lean: where no place of the vector of reads is named twice, the read that
`itU` (Cb/Pv/Tail/Places.lean) finds at a place is the one that is known to stand there.

`itU` is found by choice. A frame's forms of the late entries are written with it, so whoever has to
show something of these forms must know which read was chosen. If two tables, columns or segments
stood at one place, nothing would say which.

Main names:
  `Apart t`: no two of table, column and segment stand at one place.
  `tabAtP`: the read of segment sg of table number n at column c.
  `itU_eq`: under `Apart`, at the place of (n, c, sg), `itU` is `tabAtP` of these.

Limits: `Apart` is a premise.


Terms: lean/GLOSSARY.md.
-/
import Cb.Pv.Tail.Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Tail

/-- No two of table, column and segment stand at one place of the vector of reads. -/
def Apart (t : TSize) : Prop :=
  ∀ (n : ℕ) (T : Tab) (c sg n' : ℕ) (T' : Tab) (c' sg' : ℕ),
    t.tabs[n]? = some T → T.mat < t.NM → c < t.k T.mat → sg < t.m T.mat / T.len →
    t.tabs[n']? = some T' → T'.mat < t.NM → c' < t.k T'.mat → sg' < t.m T'.mat / T'.len →
    T.start + c * (t.m T.mat / T.len) + sg = T'.start + c' * (t.m T'.mat / T'.len) + sg' →
    n = n' ∧ c = c' ∧ sg = sg'

/-- The read of segment sg of table number n at column c. -/
def tabAtP (t : TSize) {n : ℕ} {T : Tab} {c sg : ℕ} (h1 : t.tabs[n]? = some T)
    (h2 : T.mat < t.NM) (h3 : c < t.k T.mat) (h4 : sg < t.m T.mat / T.len) : JTab t.size :=
  ⟨⟨T.mat, h2⟩, ⟨t.enc T.mat n sg, t.enc_lt h1 h4⟩, ⟨c, h3⟩⟩

theorem tabAtP_congr (t : TSize) {n n' : ℕ} {T T' : Tab} {c c' sg sg' : ℕ}
    (h1 : t.tabs[n]? = some T) (h2 : T.mat < t.NM) (h3 : c < t.k T.mat)
    (h4 : sg < t.m T.mat / T.len) (h1' : t.tabs[n']? = some T') (h2' : T'.mat < t.NM)
    (h3' : c' < t.k T'.mat) (h4' : sg' < t.m T'.mat / T'.len) (e1 : n = n') (e2 : T = T')
    (e3 : c = c') (e4 : sg = sg') : tabAtP t h1 h2 h3 h4 = tabAtP t h1' h2' h3' h4' := by
  subst e1 e2 e3 e4
  rfl

/-- Where no place is named twice, the read that is found is the read that is known. -/
theorem itU_eq {t : TSize} {N : ℕ} (ha : Apart t) (j : JU t N) {n : ℕ} {T : Tab} {c sg : ℕ}
    (h1 : t.tabs[n]? = some T) (h2 : T.mat < t.NM) (h3 : c < t.k T.mat)
    (h4 : sg < t.m T.mat / T.len)
    (hp : (j.1 : ℕ) = T.start + c * (t.m T.mat / T.len) + sg) :
    itU j = tabAtP t h1 h2 h3 h4 := by
  have h := j.2.choose_spec.choose_spec.choose_spec.choose_spec
  obtain ⟨e1, e3, e4⟩ := ha _ _ _ _ n T c sg h.1 h.2.1 h.2.2.1 h.2.2.2.1 h1 h2 h3 h4
    (h.2.2.2.2.symm.trans hp)
  have e2 : j.2.choose_spec.choose = T :=
    Option.some.inj (h.1.symm.trans ((congrArg (fun i => t.tabs[i]?) e1).trans h1))
  exact tabAtP_congr t h.1 h.2.1 h.2.2.1 h.2.2.2.1 h1 h2 h3 h4 e1 e2 e3 e4

end Cb.Pv.Tail

#print axioms Cb.Pv.Tail.itU_eq
