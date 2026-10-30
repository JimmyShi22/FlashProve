-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/TupleRoad.lean: either one tuple of candidates of which the batched rows hold,
or few draws: in the shape of `TestGivesCand`. Statements and proofs.

`TestGivesCand` is that of Johnson/Desc/Sound/WordsLaw.lean. There is no new mathematics.
Why: `few_draws_front` (Johnson/Desc/K12/Law/TieFront.lean) says: some member without a candidate
gives few draws. By contraposition that gives each member a candidate: one for each, with nothing
that ties them. `TestGivesCand` asks one tuple c of candidates such that what the row asks in front
(ins: the rows on the group) holds of the witness laid by c. The tie is there all along: the
candidates are the shares of one near witness, of whose own words all the batched rows hold.
Main names:
  `cand_of_near1`: one message: a witness w within e of a word y that holds the message's sent word
    at a seat, whose share has the sample's answers: the share is a candidate (the library's
    `Site.share` and `sig_inList_iff`). `noneNear_of_noCand1` is its contrapositive.
  `near_or_few`: at a stage with `StageJ`: either there is a witness within e of y of whose own
    words all the rows hold, or cnt (BadDraws …) ≤ lstJ e · (rows.size − 1): `NoneNear` or not;
    `batCatches_joh`.
  `tuple_or_few`: at the law's own word, at the batching's own letters (S in front, G, L, t.st =
    begun S g G, runRows S G), from `Good`, `Made`, `StageJ`, `combineAt` and the layout's four
    numbers: either ∃ one w: within e of the law's word ∧ AllSay rdE t.st (runRows S G).toList (w's
    own words) ∧ for every member j (with the yes of `siteL` and of `sampleL`, a radius e0 that e
    fits in leaves, and any seed at which `Send.form` gives the record's sample row): the share of
    that w at j is a candidate of `strOf` (the member's word as sent) at the sample ((the seed's
    point read, β), the answer read); or few draws.
Read with `TestGivesCand`: c x := the share of w at x; "∀ x ∈ mine, CandAt …" is the third conjunct;
"ins a w'" for the w' laid by c is `AllSay` at w's own words, which at the members' entries are the
shares (`words_share`, Johnson/Desc/K12/Law/ShareWords.lean) and are 0 on the rows that no member
has (`blank_of_near`).
Limits:
(1) No game: a count of the drawn element's values beside a dichotomy. `Doomed` over the piece's
rounds wants the round "BAT" in front of the chain's (`bat_game`,
Johnson/Top/H0/BatGame/DrawCatches.lean [not in this library]) and `k12_lemma` behind
`hno_of_good`.
(2) The letters are this folder's own: `strOf` for `wordAt` of Johnson/Desc/Sound/MsgSig.lean
(Johnson/Desc/K12/Law/StrRows.lean: one form, under two premises on the tenant's words; `rowAt`
copied there, not held by a compile); the seed for the sample there (`SeedIs`); e0 for the
signature's radius (l.get i).2, with hfit as a premise on it; `AllSay` for ins. That is a reading:
the lemma that turns `AllSay` at w's own words into "the rows hold of the tuple c" (words built from
c alone: `words_share` at every member, `blank_of_near` elsewhere) is not typed here;
Johnson/Desc/K12/Law/TupleWords.lean has it.
(3) The members are the group's: "mine" there must be these. The proximity test's group has no kept
member (the block's guard on the layout's kept list) and the fold's fresh mask is no member: a kept
or an unsampled tenant among "mine" gets nothing here.
(4) Members without a sample: no conjunct.
(5) The Booleans' yes are held by runs alone.
(6) As in the files on the batching's converse under Johnson/Desc/Means, which lie beneath: nothing
on who draws the batching's element, or when, or on how its readings are spread over the field.
No soundness is claimed, and nothing is said on hiding.
Lemmas called (none runs in a context of `verify-on-bytes`): `Site.share`, `sig_inList_iff`;
`combineAt_gives`, `layout_eq`, `layFacts`; `batCatches_joh`, `tie_gpG`, `answers_of_says_g`,
`sample_of_L`, `sample_mem_runRows`, `begun_samples`, `oracle_made`, `codes_made`, `rowsBlank_law`,
`shapes_back`, `shapesKeep_made`, `find_of_nodup`.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the
file's end.

-/
import Johnson.Desc.K12.Law.TieFront

set_option autoImplicit false
namespace H2K.Pin
open Cb Cb.Ood Iop Prob OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Johnson.Pack
open OnBytes.Means H2K.ClaimSays
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Run
open H2K.First (Seat1 Plain gpL gpG gpP good_of_ok oM oZ skM skZ Good Made entered)
open H2K.Pub (sgOf)

/-- The positive form, one message: the share of a near witness, of whose own words the message's
sample row holds, is a candidate. (noneNear_of_noCand1 is its contrapositive.) -/
theorem cand_of_near1 (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (e0 : ℕ) {s : Sg}
    (σs : Site s (mbOfShape cs sh e0)) (f : (portOmZ cs sh e0).Str) (smp : (portOmZ cs sh e0).Smp)
    (e : ℕ) (hfit : e < (e0 + 1) * 2 ^ (s.C.a - aOf cs sh)) (y : s.cIn.Word)
    (hT : σs.Tie ((portOmZ cs sh e0).upW f) y) (w : s.cIn.N.Wit)
    (hn : offCnt (Ex := s.cIn.ext) y (s.cIn.N.enc w.1 w.2) ≤ e)
    (ha : (portOmZ cs sh e0).Z.val smp.1 (fun j => w.1 (σs.atJ j)) = smp.2) :
    (portOmZ cs sh e0).Cand f smp (fun j => w.1 (σs.atJ j)) := by
  obtain ⟨r', hr'⟩ := σs.share hT hfit w hn
  exact ⟨(sig_inList_iff GE (portOmZ cs sh e0) f _).1 ⟨(_, r'), hr', rfl⟩, ha⟩

/-- Either one near witness of whose words all the rows hold, or few draws. -/
theorem near_or_few (s : Sg) (e : ℕ) (hJ : s.StageJ e) (S' : Statement) (g : Nat) (L : GroupLayout)
    (rows : Array Row) (y : s.cIn.Word) (ht : combineAt S' g ⟨L, rows⟩ = true)
    (hk : L.k = s.h + s.g) (hh : L.h = s.h) (hl : 2 ^ L.logEll = s.C.l)
    (hz : 2 ^ L.logEllZk = s.Z.l) :
    (∃ w : s.cIn.N.Wit, offCnt (Ex := s.cIn.ext) y (s.cIn.N.enc w.1 w.2) ≤ e ∧
      AllSay rdE S' rows.toList (H2K.ClaimSays.wordsOf S' L (tabOf s w.1))) ∨
    cnt (BadDraws s e S' g L rows y) ≤ s.lstJ e * (rows.size - 1) := by
  by_cases hN : NoneNear s e S' L rows y
  · exact .inr (batCatches_joh s e hJ S' g L rows y ht hk hh hl hz hN)
  · left
    unfold NoneNear at hN
    simp only [not_forall, Classical.not_not] at hN
    obtain ⟨w, hn, hall⟩ := hN
    exact ⟨w, hn, hall⟩

/-- One tuple of candidates, or few draws: at the law's own word, at the batching's own letters,
from Booleans. Either there is one witness w within e of the law's word, of whose own words all the
batched rows hold, and the share of that one w at every member j (with siteL's and sampleL's yes, a
radius e0 that e fits in leaves, and any seed at which Send.form gives the record's sample row) is A
candidate of the member's word as sent at that sample; or the values of the drawn element at which
the batched claim has a witness within e are at most lstJ e · (the number of rows − 1). -/
theorem tuple_or_few {F : ℕ} {a : Fmt.M1.Stage} {row : GroupRow} {D : Plain} {p : P12} {t : T12}
    {L : GroupLayout} (h : Good F a row D) (hm : Made p t a L D) (S : Statement) (g : Nat) (G :
        Group)
    (hG : S.groups[g]? = some G) (hLf : S.layout g = some L) (hst : t.st = begun S g G)
    (rd : ℕ → ℕ) (dM : Fin D.mems.length → PQ.RD) (dF : PQ.RD) (os : ∀ i, (wRound (dM i)).Orc)
    (e : ℕ) (hJ : (sgOf a).StageJ e) (ht : combineAt t.st g ⟨L, runRows S G⟩ = true)
    (hk : L.k = (sgOf a).h + (sgOf a).g) (hh : L.h = (sgOf a).h)
    (hl : 2 ^ L.logEll = (sgOf a).C.l) (hz : 2 ^ L.logEllZk = (sgOf a).Z.l) :
    (∃ w : (sgOf a).cIn.N.Wit,
      offCnt (Ex := (sgOf a).cIn.ext)
        ((gpG h rd).word fun i => ((gpG h rd).mb i).ofOrc ((gpP h rd dM dF).lay i) (dM i) (os i))
        ((sgOf a).cIn.N.enc w.1 w.2) ≤ e ∧
      AllSay rdE t.st (runRows S G).toList (H2K.ClaimSays.wordsOf t.st L (tabOf (sgOf a) w.1)) ∧
      ∀ (j : Fin D.mems.length) (e0 : ℕ)
        (hs : ok (siteL D.st.codes a (D.mems.get j)) = true) (x : OnBytes.Oracle),
        D.st.oracles[(D.mems.get j).id]? = some x →
        ok (sampleL D.st.codes (D.mems.get j) x) = true →
        e < (e0 + 1) * 2 ^ ((sgOf a).C.a - aOf D.st.codes (D.mems.get j).sh) →
        ∀ (seed : SampleSeed) (row0 : Row) (tt : E) (β : GEˣ),
        Send.form D.st.codes (D.mems.get j).sh (D.mems.get j).id seed 0 = some row0 →
        x.sampleRows.toList = [{ row0 with target := tt }] →
        bitsZ D.st.codes (D.mems.get j).sh ≤ seed.z.length → (β : GE) = readE seed.beta →
        (portOmZ D.st.codes (D.mems.get j).sh e0).Cand
          (strOf D.st.codes (D.mems.get j).sh e0 (layOf (D.mems.get j)) (dM j) (os j))
          ((readP (bitsZ D.st.codes (D.mems.get j).sh) seed.z, β), fun _ => readE tt)
          (fun q => w.1
            ((siteOf D.st.codes a (D.mems.get j) e0 (oM D.L j.val) (oZ D.L j.val) hs).atJ q))) ∨
    cnt (BadDraws (sgOf a) e t.st g L (runRows S G)
      ((gpG h rd).word fun i => ((gpG h rd).mb i).ofOrc ((gpP h rd dM dF).lay i) (dM i) (os i))) ≤
      (sgOf a).lstJ e * ((runRows S G).size - 1) := by
  rcases near_or_few (sgOf a) e hJ t.st g L (runRows S G) _ ht hk hh hl hz with ⟨w, hn, hall⟩ | hfew
  · refine .inl ⟨w, hn, hall, fun j e0 hs x hx hq hfit seed row0 tt β hform hrows hzl hβ => ?_⟩
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
    obtain ⟨G', hG', hL'', hOk, _⟩ := combineAt_gives ht
    have hL' : t.st.layout g = some L := hL''
    have hLm' : L.members = G'.members := by
      have e' := layout_eq t.st g G' hG'
      rw [hL'] at e'
      rw [Option.some.inj e']
      rfl
    obtain ⟨x1, hx1, ex1⟩ := shapes_back hm t.st (shapesKeep_made hm)
      (by rw [hLm']; exact hOk.there) j
    have hlt : (D.mems.get j).id < t.st.oracles.size := by
      rcases Nat.lt_or_ge (D.mems.get j).id t.st.oracles.size with q | q
      · exact q
      · rw [Array.getElem?_eq_none q] at hx1
        cases hx1
    have hxt : t.st.oracles[(D.mems.get j).id]? = some x := by
      rw [← oracle_made hm _ hlt]
      exact hx
    have hxt' := hxt
    rw [hst] at hxt'
    obtain ⟨x0, hx0, es⟩ := begun_samples S g G _ x hxt'
    have hr : { row0 with target := tt } ∈ (runRows S G).toList :=
      sample_mem_runRows S G _ x0 hmem hx0 _ (by rw [es, hrows]; exact List.mem_singleton.2 rfl)
    have hfind := find_of_nodup (by rw [hLm']; exact hOk.nodup) (hm.mem j).1
    have hy := rowsBlank_law h hm rd g G' hG' hL' hOk hk hh
      (fun i => ((gpG h rd).mb i).ofOrc ((gpP h rd dM dF).lay i) (dM i) (os i))
    have hF := layFacts hG' hL' hOk
    have hcs := codes_made hm
    have ex : x.shape = (D.mems.get j).sh := by
      rw [hx1] at hxt
      rw [← Option.some.inj hxt]
      exact ex1
    have hLD := hm.lay
    subst hLD
    refine cand_of_near1 D.st.codes (D.mems.get j).sh e0 _ _ _ e hfit _
      (tie_gpG h rd dM dF os j e0 hs) w hn ?_
    exact answers_of_says_g hJ.sized e hJ.joh.1 t.st G' D.L hF _ hy (D.mems.get j).id j.val x hxt
      D.st.codes hcs _ ex e0 _ (oM D.L j.val) (oZ D.L j.val) (fun _ => rfl) (fun _ => rfl) (h.roomM
          j)
      (h.roomZ j) hfind (h.kept _)
      (fun h0 => by
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (h.firstM j h0)
        unfold oM
        rw [hv]
        rfl)
      (fun h0 => by
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (h.firstZ j h0)
        unfold oZ
        rw [hv]
        rfl)
      hk hh seed row0 hform tt h1 hc hzl β hβ hlM hlZ w hn (hall _ hr)
  · exact .inr hfew

end H2K.Pin

#print axioms H2K.Pin.cand_of_near1
#print axioms H2K.Pin.near_or_few
#print axioms H2K.Pin.tuple_or_few
