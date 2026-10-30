--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/YesRecAt.lean: the function of the place "(rec_gamma)" of the linear claim's
shared rounds returns a state, which is written out.

The place lets o_u join its group and lays one constraint for each seed of the key.

The function is the own text of the IOP as written in Lean (Johnson/Desc/K14/Text.lean). The
sub-protocol's decide function is that function under the names of its tests. A decision is the
format's step (Johnson/Desc/Block.lean: Block.step), which tests the rounds' form and the columns in
front of the decide function. That the eight decide functions return .ok: Returned.decides
(Johnson/Desc/K14/Honest/YesChain.lean). That the eight steps do: eight_steps_hold
(Johnson/Desc/K14/Honest/ChainSteps.lean).

On the key. The place asks that the key's sizes fit and that no seed of the key has the factor 0:
two of its three named tests, word for word. They are premises here (hkey, hbeta). At a key that
fails them the place rejects whatever a prover sends. In the release a key's seeds follow from the
committed table's name by the hash: so "no seed has the factor 0" is no choice of an honest
committer's. A statement on honest provers above this file has to carry it among what a valid
instance is, or to bound the chance of it over the random oracle.

Main name: laysRec_returns.

What is not claimed. That a decision accepts. That the facts in front hold at any state. Nothing on
what the constraints mean, on soundness, on completeness or on hiding.

-/
import Johnson.Desc.K14.Honest.YesFacts
import Johnson.Desc.Key.Laid.Draws
import Johnson.Desc.Key.Laid.Joined

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Slice (withMessageInGroup withRows)
open OnBytes.Means (addRowsP_of_fits)
open VerifiableInference.Desc.Ground (ok)
open VerifiableInference.Desc.Key (entered entered_has joined_groupAt mapM_some)
open VerifiableInference.Desc.Own (keyFits allZero)

/-- **The function of "(rec_gamma)" returns**: o_u has joined its group G, and the constraints, one
for each seed of the key, stand behind the group's rows. hkey, hbeta: the tests on the key. -/
theorem laysRec_returns (p : Par) (d : St) (rs : List Fmt.RoundView) (h : FrontU p d [])
    (hkey : keyFits d.loc.key p.S.fold.index = true)
    (hbeta : (d.loc.key.seeds.all (!allZero ·.beta)) = true) :
    ∃ G rows, d.st.groups[d.loc.gU]? = some G ∧ Law.recRows p d.loc = some rows ∧
      laysRec p d rs = some { d with
        st := (withRows (withMessageInGroup d.st d.loc.gU d.loc.oU.oracle false G) d.loc.gU rows) } := by
  obtain ⟨G, hG, hcode, hmask, hrun, hmem⟩ := h.gU
  obtain ⟨x, hx, hs, hsam, hp⟩ := h.u
  have R := shapeSizes_of d.st.codes p.S h.lin
  obtain ⟨k1, k2, k3⟩ := (VerifiableInference.Desc.Own.keyFits_iff _ _).1 hkey
  have hw := weights_size p d h.psi
  have hok : ok (laysRecL p d.loc) = true := by
    simp only [ok, laysRecL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      beq_iff_eq]
    refine ⟨hkey, hbeta, ?_⟩
    unfold gamma
    rw [List.length_drop, h.psi]
    unfold LinShape.kCol
    omega
  obtain ⟨hsh, _⟩ := (VerifiableInference.Desc.Own.linFits_iff d.st.codes p.S).1 h.lin
  have hj := joinP_of d d.loc.gU d.loc.oU.oracle G x hG hx hsam hrun
    (Or.inr (by rw [hs, hcode]))
    (by
      rcases hsh.2.2.2.2.2.2.2.2.1 with e | e
      · exact Or.inl (by rw [hs]; exact e)
      · exact Or.inr (by rw [hs, hmask]; exact e))
    (not_contains_of hmem _ (by simp))
  have hG1 : (withMessageInGroup d.st d.loc.gU d.loc.oU.oracle false G).groups[d.loc.gU]? =
      some (entered G d.loc.oU.oracle false) := joined_groupAt _ _ _ _ _ hG
  have hS0 := sits_u h.lin h.u (entered G d.loc.oU.oracle false) (entered_has _ _ _)
  rw [← h.lay] at hS0
  have hS1 := hS0.alike (alike_joined d.st d.loc.gU d.loc.oU.oracle false G)
    (entered G d.loc.oU.oracle false) (entered_has G d.loc.oU.oracle false)
  obtain ⟨rows, hm⟩ := mapM_makes (fun x : SampleSeed × Nat =>
      recGamma p.S.fold.index x.1 x.2 (weights p.S d.loc) d.loc.key.record d.loc.oU)
    d.loc.key.seeds.zipIdx (by
      intro a ha
      have ha' : d.loc.key.seeds[a.2]? = some a.1 := List.mem_zipIdx_iff_getElem?.1 ha
      exact recGamma_makes _ _ _ _ _ _ (k3 _ (List.mem_of_getElem? ha')) hw k1
        (by rw [← k2]; exact (List.getElem?_eq_some_iff.1 ha').1))
  have ha := addRowsP_of_fits
    ({ d with st := withMessageInGroup d.st d.loc.gU d.loc.oU.oracle false G } : St) d.loc.gU
    (entered G d.loc.oU.oracle false) rows hG1 hrun (by
      intro row hrow
      obtain ⟨a, ha, e⟩ := (mapM_some _ _ _ hm).2 row hrow
      have ha' : d.loc.key.seeds[a.2]? = some a.1 := List.mem_zipIdx_iff_getElem?.1 ha
      exact recGamma_fits _ _ _ _ _ _ _ _ row _ R.indexOk (k3 _ (List.mem_of_getElem? ha')) e hS1
        (by rw [h.lay]; exact R.cube) R.ell)
  refine ⟨G, rows, hG, hm, ?_⟩
  unfold laysRec
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff]
  exact ⟨(), by simp [guard, hok], _, hj, rows, hm, ha⟩

end Desc.K14.Honest

#print axioms Desc.K14.Honest.laysRec_returns
