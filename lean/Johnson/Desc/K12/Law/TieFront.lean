-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TieFront.lean: "a sampled member without a candidate leaves few bad draws",
from Booleans alone, at the batching's own letters; and "not a bad draw gives the chain's premise".
Statements and proofs.

There is no new mathematics.
Main names:
  `hno_of_good`: from ¬ BadDraws s e S' g L rows y (readE x), Bat.combine S' g ⟨L, rows⟩ x = some
    row and row.kept = #[]: ∀ w, ¬ s.RIn e (stmG s row, y) w, which is the premise hno of
    `chain_many` and `k12_lemma`. By unfolding.
  `begun_samples`: the beginning of a test (the library's `begun`: the members' ledgers closed, the
    group marked) turns no sample row: by the library's `closeLedgers_get`.
  `oracle_made`: `Made p t a L D` gives D.st.oracles[o]? = t.st.oracles[o]? for every message o of
    the record, in both arms of the mask (the library's `stSent_old` where the fold brings its own).
  `few_draws_front`: S: the statement in front of the batching, with the group G at g and the layout
    L; t.st = begun S g G; the rows: runRows S G (all as `bat_ok` gives them). From `Good` (`gpOk`),
    `Made`, the yes of `siteL`, the yes of `sampleL` at the member's message in D.st, `StageJ`
    (`johOk`), hfit, `combineAt` and the layout's four numbers: ∃ seed row0 tt β: Send.form
    D.st.codes sh id seed 0 = some row0 ∧ x.sampleRows.toList = [{ row0 with target := tt }] ∧ bitsZ
    ≤ the point's length ∧ β = the factor read ∧ (no candidate for the member's word as sent at
    ((the point read, β), tt read) → cnt (BadDraws (sgOf a) e t.st g L (runRows S G) (the law's
    word)) ≤ (sgOf a).lstJ e · ((runRows S G).size − 1)).
  `few_draws_front_all`: the same for every seed, row0, tt and β with these four facts (∀ in the
    place of ∃): a spender that comes with its own seed, the drawn one, plugs it in directly; no
    injectivity of `Send.form` in the point's prefix is wanted.
The seed is tied to the record in the conclusion (without that the "there is" would be worth little:
a seed at which some word has a candidate makes the implication true for nothing).
So the three statements are one for a member's sample row: D.st (the plain data's) = t.st (behind)
by `oracle_made`; t.st against S (in front) by `begun_samples`; and the row stands in runRows S G by
`sample_mem_runRows`.
Every premise is now a Boolean that has been evaluated, a lemma, or arithmetic on the letter e0:
`gpOk`, `siteOk`, `johOk`, `combineAt`, the layout's four numbers, `sampleOk` (at the proximity
tests of the two example proofs); `made_of`, `bat_ok` (hG, hLf, hst); hfit.
Limits:
(1) The seed is read back off the row: that it is the prefix of the point that the verifier drew,
and when, is for the law of the sending; the sample that Johnson/Desc/Sound/ reads is to come off
the chain's record.
(2) e0 must be the radius that the signature there gives the member.
(3) `strOf` is our own definition of "the word as sent".
(4) It is a count of values θ, with no game: the round "BAT" in front of the chain's rounds is not
treated here.
(5) One member a call; members without a sample: nothing.
(6) The Booleans' yes are held by runs alone.
(7) As in the files on the batching's converse under Johnson/Desc/Means, which lie beneath: nothing
on who draws the batching's element, or when, or on how its readings are spread over the field.
No soundness is claimed, and nothing is said on hiding.
Lemmas called (none runs in a context of `verify-on-bytes`): `closeLedgers_get`
(OnBytes/Slice/BlkProxEarlierMessagesAndGroups.lean), `stSent_old` (OnBytes/Slice/BlkStLaws.lean); `combineAt_gives`,
`layout_eq`; `few_draws_made`, `sample_of_L`, `sample_mem_runRows`, `shapes_back`,
`shapesKeep_made`, `recvP_ok`.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the
file's end.

-/
import Johnson.Desc.K12.Law.TieMade
import Johnson.Desc.K12.Law.SampleLaw
import OnBytes.Slice.BlkProxEarlierMessagesAndGroups

set_option autoImplicit false
namespace H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Run
open H2K.First (Seat1 Plain gpL gpG gpP good_of_ok oM oZ skM skZ Good Made entered)
open H2K.Pub (sgOf)

/-- Not a bad draw ⇒ the chain's premise: where the drawn element x, read, is none of the bad
values, the claim that the batching returns at x has no witness within e of y. By unfolding
BadDraws. -/
theorem hno_of_good {s : Sg} {e : ℕ} {S' : Statement} {g : Nat} {L : GroupLayout} {rows : Array Row}
    {y : s.cIn.Word} {x : E} {row : GroupRow} (hb : ¬ BadDraws s e S' g L rows y (readE x))
    (hc : Bat.combine S' g ⟨L, rows⟩ x = some row) (hk : row.kept = #[]) :
    ∀ w, ¬ s.RIn e (stmG s row, y) w :=
  fun w hw => hb ⟨x, row, rfl, hc, hk, w, hw⟩

/-- The beginning of a test turns no sample row. -/
theorem begun_samples (S : Statement) (g : Nat) (G : Group) (o : Nat) (x' : OnBytes.Oracle)
    (h : (begun S g G).oracles[o]? = some x') :
    ∃ x, S.oracles[o]? = some x ∧ x.sampleRows = x'.sampleRows := by
  have e : (begun S g G).oracles[o]? = (S.oracles[o]?).map fun x =>
      if o ∈ G.members.toList then shut x else x := closeLedgers_get _ _ _
  rw [e] at h
  obtain ⟨x, hx, h⟩ := Option.map_eq_some_iff.1 h
  refine ⟨x, hx, ?_⟩
  subst h
  split <;> rfl

/-- The plain data's statement has the record's messages as they are: in both arms of the mask. -/
theorem oracle_made {p : P12} {t : T12} {a : Fmt.M1.Stage} {L : GroupLayout} {D : Plain}
    (hm : Made p t a L D) (o : Nat) (ho : o < t.st.oracles.size) :
    D.st.oracles[o]? = t.st.oracles[o]? := by
  obtain ⟨cu, _, he⟩ := hm.ent
  unfold entered at he
  split at he
  · have e : t.st = D.st := congrArg (fun x => x.2.1) (Option.some.inj he)
    rw [← e]
  · obtain ⟨x, hx, he⟩ := Option.bind_eq_some_iff.1 he
    obtain ⟨id, _, he⟩ := Option.map_eq_some_iff.1 he
    have e : x.2.st = D.st := congrArg (fun x => x.2.1) he
    rw [← e]
    obtain ⟨ids, d1⟩ := x
    obtain ⟨lay, _, _, _, rfl⟩ := H2K.Sw.recvP_ok hx
    exact stSent_old _ _ o ho

/-- The road from Booleans alone, at the batching's own letters. S: the statement in front of
the batching, with the group G at g and the layout L (what bat_ok gives); t: the record behind, t.st
= begun S g G; the rows are runRows S G. h: gpOk's clauses; hm: gpOf's make; j: a member; hs:
siteL's yes; hx | hq: the member's message in the plain data's statement and sampleL's yes at it;
hJ: StageJ at e (johOk); hfit; ht: combineAt; the layout's four numbers. Then there is a seed, tied
to the record in the conclusion itself (the record's one sample row is { Send.form … at that seed
with target := tt }; the point at least as long as the cube; β the factor, a unit), such that, at
the sample made of it (the point read, β, the answer tt read): if the member's word as sent has no
candidate at it, the values of the drawn element at which the batched claim has a witness within e
of the law's word are at most lstJ e · (the number of rows − 1). -/
theorem few_draws_front {F : ℕ} {a : Fmt.M1.Stage} {row : GroupRow} {D : Plain} {p : P12} {t : T12}
    {L : GroupLayout} (h : Good F a row D) (hm : Made p t a L D) (S : Statement) (g : Nat) (G :
        Group)
    (hG : S.groups[g]? = some G) (hLf : S.layout g = some L) (hst : t.st = begun S g G)
    (rd : ℕ → ℕ) (dM : Fin D.mems.length → PQ.RD) (dF : PQ.RD) (os : ∀ i, (wRound (dM i)).Orc)
    (j : Fin D.mems.length) (e0 : ℕ) (hs : ok (siteL D.st.codes a (D.mems.get j)) = true)
    (x : OnBytes.Oracle) (hx : D.st.oracles[(D.mems.get j).id]? = some x)
    (hq : ok (sampleL D.st.codes (D.mems.get j) x) = true)
    (e : ℕ) (hJ : (sgOf a).StageJ e)
    (hfit : e < (e0 + 1) * 2 ^ ((sgOf a).C.a - aOf D.st.codes (D.mems.get j).sh))
    (ht : combineAt t.st g ⟨L, runRows S G⟩ = true)
    (hk : L.k = (sgOf a).h + (sgOf a).g) (hh : L.h = (sgOf a).h)
    (hl : 2 ^ L.logEll = (sgOf a).C.l) (hz : 2 ^ L.logEllZk = (sgOf a).Z.l) :
    ∃ (seed : SampleSeed) (row0 : Row) (tt : E) (β : GEˣ),
      Send.form D.st.codes (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0 ∧
      x.sampleRows.toList = [{ row0 with target := tt }] ∧
      bitsZ D.st.codes (D.mems.get j).sh ≤ seed.z.length ∧ (β : GE) = readE seed.beta ∧
      ((∀ m, ¬ (portOmZ D.st.codes (D.mems.get j).sh e0).Cand
          (strOf D.st.codes (D.mems.get j).sh e0 (layOf (D.mems.get j)) (dM j) (os j))
          ((readP (bitsZ D.st.codes (D.mems.get j).sh) seed.z, β), fun _ => readE tt) m) →
        cnt (BadDraws (sgOf a) e t.st g L (runRows S G)
          ((gpG h rd).word fun i => ((gpG h rd).mb i).ofOrc ((gpP h rd dM dF).lay i) (dM i) (os
              i))) ≤
          (sgOf a).lstJ e * ((runRows S G).size - 1)) := by
  obtain ⟨seed, row0, tt, β, hform, hrows, hzl, hβ, h1, hc, hlM, hlZ⟩ := sample_of_L hq
  have hLm : L.members = G.members := by
    have e' := layout_eq S g G hG
    rw [hLf] at e'
    rw [Option.some.inj e']
    rfl
  have hmem : (D.mems.get j).id ∈ G.members.toList := by
    have := (hm.mem j).1
    rw [hLm, ← Array.getElem?_toList] at this
    exact List.mem_of_getElem? this
  obtain ⟨G', _, _, hOk, _⟩ := combineAt_gives ht
  have hlt : (D.mems.get j).id < t.st.oracles.size := by
    rcases Nat.lt_or_ge (D.mems.get j).id t.st.oracles.size with q | q
    · exact q
    · exfalso
      obtain ⟨y, hy, _⟩ := shapes_back hm t.st (shapesKeep_made hm) (by
        intro o ho
        have hG' : t.st.groups[g]? = some G' := by assumption
        have e' := layout_eq t.st g G' hG'
        have hL' : t.st.layout g = some L := by assumption
        rw [hL'] at e'
        have : L.members = G'.members := by rw [Option.some.inj e']; rfl
        rw [this] at ho
        exact hOk.there o ho) j
      rw [Array.getElem?_eq_none q] at hy
      cases hy
  have hxt : t.st.oracles[(D.mems.get j).id]? = some x := by rw [← oracle_made hm _ hlt]; exact hx
  rw [hst] at hxt
  obtain ⟨x0, hx0, es⟩ := begun_samples S g G _ x hxt
  have hr : { row0 with target := tt } ∈ (runRows S G).toList :=
    sample_mem_runRows S G _ x0 hmem hx0 _ (by rw [es, hrows]; exact List.mem_singleton.2 rfl)
  exact ⟨seed, row0, tt, β, hform, hrows, hzl, hβ, fun hno => few_draws_made h hm rd dM dF os j e0
      hs e
    hJ hfit g _ ht hk hh hl hz seed row0 hform tt hr h1 hc hzl β hβ hlM hlZ hno⟩

/-- The same for every seed at which Send.form gives the record's row (∀ in the place of ∃): so
a spender that comes with its own seed (the drawn one) plugs it in directly, and no injectivity of
Send.form is wanted. sampleL's yes is spent for what does not hang on the seed (one answer · the
case · the two powers of two); few_draws_front shows that the range is not empty. -/
theorem few_draws_front_all {F : ℕ} {a : Fmt.M1.Stage} {row : GroupRow} {D : Plain} {p : P12} {t :
    T12}
    {L : GroupLayout} (h : Good F a row D) (hm : Made p t a L D) (S : Statement) (g : Nat) (G :
        Group)
    (hG : S.groups[g]? = some G) (hLf : S.layout g = some L) (hst : t.st = begun S g G)
    (rd : ℕ → ℕ) (dM : Fin D.mems.length → PQ.RD) (dF : PQ.RD) (os : ∀ i, (wRound (dM i)).Orc)
    (j : Fin D.mems.length) (e0 : ℕ) (hs : ok (siteL D.st.codes a (D.mems.get j)) = true)
    (x : OnBytes.Oracle) (hx : D.st.oracles[(D.mems.get j).id]? = some x)
    (hq : ok (sampleL D.st.codes (D.mems.get j) x) = true)
    (e : ℕ) (hJ : (sgOf a).StageJ e)
    (hfit : e < (e0 + 1) * 2 ^ ((sgOf a).C.a - aOf D.st.codes (D.mems.get j).sh))
    (ht : combineAt t.st g ⟨L, runRows S G⟩ = true)
    (hk : L.k = (sgOf a).h + (sgOf a).g) (hh : L.h = (sgOf a).h)
    (hl : 2 ^ L.logEll = (sgOf a).C.l) (hz : 2 ^ L.logEllZk = (sgOf a).Z.l)
    (seed : SampleSeed) (row0 : Row) (tt : E) (β : GEˣ)
    (hform : Send.form D.st.codes (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0)
    (hrows : x.sampleRows.toList = [{ row0 with target := tt }])
    (hzl : bitsZ D.st.codes (D.mems.get j).sh ≤ seed.z.length) (hβ : (β : GE) = readE seed.beta)
    (hno : ∀ m, ¬ (portOmZ D.st.codes (D.mems.get j).sh e0).Cand
      (strOf D.st.codes (D.mems.get j).sh e0 (layOf (D.mems.get j)) (dM j) (os j))
      ((readP (bitsZ D.st.codes (D.mems.get j).sh) seed.z, β), fun _ => readE tt) m) :
    cnt (BadDraws (sgOf a) e t.st g L (runRows S G)
      ((gpG h rd).word fun i => ((gpG h rd).mb i).ofOrc ((gpP h rd dM dF).lay i) (dM i) (os i))) ≤
      (sgOf a).lstJ e * ((runRows S G).size - 1) := by
  obtain ⟨_, _, _, _, _, _, _, _, h1, hc, hlM, hlZ⟩ := sample_of_L hq
  have hLm : L.members = G.members := by
    have e' := layout_eq S g G hG
    rw [hLf] at e'
    rw [Option.some.inj e']
    rfl
  have hmem : (D.mems.get j).id ∈ G.members.toList := by
    have := (hm.mem j).1
    rw [hLm, ← Array.getElem?_toList] at this
    exact List.mem_of_getElem? this
  obtain ⟨G', _, _, hOk, _⟩ := combineAt_gives ht
  have hlt : (D.mems.get j).id < t.st.oracles.size := by
    rcases Nat.lt_or_ge (D.mems.get j).id t.st.oracles.size with q | q
    · exact q
    · exfalso
      obtain ⟨y, hy, _⟩ := shapes_back hm t.st (shapesKeep_made hm) (by
        intro o ho
        have hG' : t.st.groups[g]? = some G' := by assumption
        have e' := layout_eq t.st g G' hG'
        have hL' : t.st.layout g = some L := by assumption
        rw [hL'] at e'
        have : L.members = G'.members := by rw [Option.some.inj e']; rfl
        rw [this] at ho
        exact hOk.there o ho) j
      rw [Array.getElem?_eq_none q] at hy
      cases hy
  have hxt : t.st.oracles[(D.mems.get j).id]? = some x := by rw [← oracle_made hm _ hlt]; exact hx
  rw [hst] at hxt
  obtain ⟨x0, hx0, es⟩ := begun_samples S g G _ x hxt
  have hr : { row0 with target := tt } ∈ (runRows S G).toList :=
    sample_mem_runRows S G _ x0 hmem hx0 _ (by rw [es, hrows]; exact List.mem_singleton.2 rfl)
  exact few_draws_made h hm rd dM dF os j e0 hs e hJ hfit g _ ht hk hh hl hz seed row0 hform tt hr
      h1 hc
    hzl β hβ hlM hlZ hno

end H2K.Pin

#print axioms H2K.Pin.hno_of_good
#print axioms H2K.Pin.begun_samples
#print axioms H2K.Pin.oracle_made
#print axioms H2K.Pin.few_draws_front
#print axioms H2K.Pin.few_draws_front_all
