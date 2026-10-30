-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ReadsLiveAtLayers.lean: the proof of the statement of
Johnson/P1K8R/ReadsLiveAtLayersStatement.lean, to the letter, and one helper. Lemmas; none of the
library's goals.

TWO FURTHER TEXTS. `ztF_of_hear` IS FIVE LINES OF THE PROOF OF THE LIBRARY's `pub34_of_hear`
(Johnson/Road/K4/PubOfHear.lean), WRITTEN A FURTHER TIME: that lemma has the equation as a field of
a structure that it makes under premises on the lookup's return which are not in hand here. THE FIVE
LINES STAND TYPED ONCE MORE: `ProofFile.Honest.K4.W.zt_of_hear`
(Johnson/Desc/ProofFile/Honest/K4/Law/W/OneTie.lean, another group of authors', a file that is not
in this library): the second clause here, at o.v.y for P.y: SO THIS IS THE THIRD TEXT; that file
stands over its authors' files of the honest side, which would come to lie beneath this one. THE
SEVEN LINES THAT PAY THE TWO PREMISES OF `k4_heard_at_front` FROM hOk ARE THE FIRST LINES OF
`runAsks_at_batch` (Johnson/Desc/ProofFile/Honest/K4/Law/RunsAtBatch.lean, another group of
authors'), which ends elsewhere.

How. `list_at_layers` (ListAtLayers.lean): the smallness test's list is the list of the return o
that the state holds; its matrices and their number are the plan's. `k4_heard_at_front`
(Johnson/Desc/First/Link/Law/K4AtFront.lean): o is a return of the own rounds' text at the plan, at
some fo with o.H.fo = fo; its premises by `flat_planOk` (Johnson/P1K2R/SitsDoor.lean) and
`sized_upTo` (Johnson/Desc/First/Look/K03RowsBare.lean). `hear_public`
(OnBytes/Desc/First/K4/HearPublic.lean): at such a return the laying, the points and the list.
`ztF_of_hear`: the token point is the last lt coordinates of the lookup's (`hear_calls`,
`hearTerms_keeps`, HearCalls.lean; `hearNorms_public`, NormsPublic.lean). `layPremises`
(LayPremises.lean): the premises on public data. `layLiveTables`
(Johnson/Desc/K8/Honest/LayLiveTables.lean): so every matrix has a live table. `tiesLaid_at_batch`
(TiesAtBatch.lean), `readsLive_of` (Johnson/Desc/K8/Honest/ReadsLiveOf.lean): so the test says yes.
The line that takes the instance Inst.Model.Scl.ref off stands as in K4AtFront.lean, whose lemma is
called.

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.P1K8R.ReadsLiveAtLayersStatement
import Johnson.P1K8R.ListAtLayers
import Johnson.P1K8R.LayPremises
import Johnson.P1K8R.TiesAtBatch
import Johnson.Desc.K8.Honest.LayLiveTables
import Johnson.Desc.K8.Honest.ReadsLiveOf
import Johnson.Desc.First.Link.Law.K4AtFront
import Johnson.Desc.First.Link.Law.FitsMsBuilt
import Johnson.Desc.First.Look.K03RowsBare
import Johnson.P1K2R.SitsDoor
import OnBytes.Desc.First.K4.HearPublic
import OnBytes.Desc.First.K4.HearCalls
import OnBytes.Desc.First.K4.NormsPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.K8.Honest (tiesLaid readsLive readsLive_of layLiveTables)
open OnBytes.Desc.First.K4 (hear engFl)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- At a return of the own rounds' text: the lookup's return is borne as it came, and the token
point is the last lt coordinates of its point. -/
theorem ztF_of_hear {P : Layer.Pub} {hp : Layer.HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t u : OnBytes.K.Kc.Tape} {o : Layer.Own}
    (h : hear engFl P hp g fo F t = some (o, G, u)) :
    o.H.fo = fo ∧ lastOf o.H.fo.zx P.y.h.lt = .ok o.H.ztF := by
  obtain ⟨-, H1, G1, u1, G2, u2, n1, n2, -⟩ := OnBytes.Desc.First.K4.hear_calls h
  obtain ⟨-, -, -, -, -, -, q5, q6⟩ := OnBytes.Desc.First.K4.hearNorms_public n1
  obtain ⟨kfo, -, -, -, kzt, -⟩ := OnBytes.Desc.First.K4.hearTerms_keeps n2
  have efo : o.H.fo = fo := by rw [kfo, q6]
  refine ⟨efo, ?_⟩
  rw [efo, kzt]
  exact OnBytes.Road.ok_of_toOption q5

/-- **In front of a layers' segment's batching the test says yes.** -/
theorem readsLive_at_layers : ReadsLiveAtLayers := by
  intro P pp lay F Z Bs base c A B hS hR O hOk g hg z s' h hF
  obtain ⟨hp, tl, o, hG, etl, eo, c1, c2, c3⟩ :=
    list_at_layers P pp lay F Z Bs base c A B hS hR O ProofFile.InstPub (ProofFile.startS Z) g hg z s' h
  -- what the state holds is a return of the own rounds' text
  have hpl := P1K2.flat_planOk O hOk
  obtain ⟨-, R, C, hfold⟩ := h.fold
  have hk : 28 * g + 9 = 14 * (2 * g) + 6 + 2 + 1 := by omega
  rw [hk] at hfold
  obtain ⟨G', hG', hZ'⟩ := VerifiableInference.OnPublicFiles.sized_upTo hS hR O hOk (2 * g) (by omega) 6
    (by omega) hfold
  obtain ⟨x, tokv, fo, F₄, o', G, -, t, u, -, xg, xP, xG, hh, -, -, -, ho', -⟩ :=
    VerifiableInference.Desc.LinkJoin.k4_heard_at_front hS hR O hpl hg h ⟨G', hG', hZ'⟩
  obtain rfl : o' = o := Option.some.inj (ho'.symm.trans eo)
  obtain rfl : hp = x.2.hp := Option.some.inj (hG.symm.trans xG)
  have hh' : hear engFl { x.2.P with tokv := tokv } x.2.hp x.2.g fo F₄ t = some (o', G, u) := hh
  obtain ⟨-, -, iU3, tab, laid, nU3, TS, claimsP, pts, hd2, -, -, hlay, -, -, -, -, -, hpts,
    hfuns⟩ := OnBytes.Desc.First.K4.hear_public hh'
  obtain ⟨efo, hzt⟩ := ztF_of_hear hh'
  -- at the public part's letters
  have hlay' : Layer.layTables ((Bs.G₀.W.layers.tails.getD g {}).mats.map fun M => (M.m, M.k))
      (Layer.tableAsks Bs.G₀.W.layers.y Bs.G₀.W.layers.rd g) 0 = some (tab, laid, nU3) := by
    rw [← xP, ← xg]
    exact hlay
  have hpts' : Layer.pointsOf Bs.G₀.W.layers.y o'.H o'.hd (some hd2) = some pts := by
    rw [← xP]
    exact hpts
  have hfuns' : Layer.funsOf Bs.G₀.W.layers.y o'.H.fo pts laid = some o'.funs := by
    rw [← xP, efo]
    exact hfuns
  have hzt' : lastOf o'.H.fo.zx Bs.G₀.W.layers.y.h.lt = .ok o'.H.ztF := by
    rw [← xP]
    exact hzt
  have hpub : Verify.publicOf P.pol P.KL (some lay) = .ok Bs.G₀.W := by
    rw [ProofFile.Law.blankBy_W O.blank]
    exact VerifiableInference.Desc.LinkJoin.public_of_pub O.pub
  obtain ⟨p1, ⟨m1, m2, m3, m4, m5, m6⟩, p3, p4, p5, p6, p7, p8, p9, p10⟩ :=
    layPremises P pp (some lay) Bs.G₀.W g x.2.hp hS hR hpub hg xG
  obtain ⟨tl', e2, hT⟩ := tiesLaid_at_batch hS hR O (l := 2 * g) (by omega)
    (show Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * (2 * g) + (if 2 * g = 24 then 11 else 9)) (z, s') by
      rw [if_neg (by omega), show 14 * (2 * g) + 9 = 28 * g + 9 by omega]
      exact h)
  obtain rfl : tl = tl' := Option.some.inj (etl.symm.trans e2)
  refine ⟨tl, etl, readsLive_of tl hT ?_⟩
  exact layLiveTables Bs.G₀.W.layers.y Bs.G₀.W.layers.rd g _ o'.H o'.hd (some hd2) pts
    (tab, laid, nU3) o'.funs tl p1 m1 m2 m3 m4 m5 m6 hpts' hzt' hlay' hfuns' c1
    (fun M => by rw [c2]; exact p3 M) (by rw [c3]; exact p4) p5 p6 p7 p8 p9 p10 (hF o' eo)

end P1K8

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms P1K8.ztF_of_hear
#print axioms P1K8.readsLive_at_layers
