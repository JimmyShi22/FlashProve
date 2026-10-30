-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/FormBehind.lean: THE FIRST CHAIN's CLAUSE (P) PAST «BEHIND
THE BATCHING», WHERE THE PROMISE's MEANING IS THE LIBRARY's COMPOSED ONE. `form_next_quiet`
(Honest/Law/NoHouse/FormNext.lean) leaves six premises on the public book-keeping behind. THE
LIBRARY PAYS THE LIKE AT ITS OWN PROMISE, AT JUST THIS MEMBER (`mgRides_at`,
Johnson/Desc/First/Link/Law/MgRidesAt.lean; `h12_mg`, RidesAtMg.lean). Here its pieces are called at
our letters: where the letters' meaning of the promise is `mgAll 𝔇 mgBase`, from two Bools on the
table and the written list of places (`linkFit`, `pubFit9`), the place, the plan's two counts, and
FOUR SENTENCES ON THE TWO STATES: the library's `Rb`; `rest9` alike; «the ledger is well laid» is
kept; «the one sum can be taken» behind.

WHAT THIS IS. A conditional lemma on a definition of ours: calls of the library's `fit_behind`,
`fit9_at`, `shape_step`, `pubHeld_step`, `sameOn_of`, `held_rides`, `mgAll_pubP_said`, as the
library's own `mgRides_at` and `rec_of_rb` call them. What these take for the oracles' strings
(`OracleAsks`) is not wanted: at the honest letters decodes, shown and no collision are true by the
letters' text, and «held» reads the statement and the book alone. None of the library's goals.

  `form_next_behind`

WHO IS MEANT TO PAY WHICH PREMISE. hfit, hpf: at the full size the library's `P5J.linkFit_links`,
`pubFit9_links` (by the kernel). ht, hm: the plan's counts (the library's RidesAtMg.lean names a
«CountsFit.lean» for them: NO FILE OF THAT NAME LIES IN THE LIBRARY AS WE HOLD IT: no payer known).
R, hrest, hled: behind that member's step the library's `rb_behind` (BkLink.lean), `rest_behind`
(Rest9.lean), `ledger_behind` (SizedRides.lean), UNDER THE RUNS' SHARE (`LinkShare`,
RidesAtMg.lean): the ties of the link's entries to the known runs are owed. htot: on the honest side
the item totalB's own second conjunct.

Limits. A RULE OVER LETTERS. NOT ONE OF THE PREMISES IS SHOWN HERE AT THE PROTOCOL. Nothing on any
property.

-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.FormNext
import Johnson.Desc.First.Link.Law.MgRidesAt
import Johnson.Desc.First.Link.Law.LinkPlacesFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Block Place Strs Wit)
open VerifiableInference.Desc.First (S ModelPart Item Pub Numbers Meaning onAt openSets pubSets start
  rowOf pubRowM pubStep stepOpen quietRow shapeAt pubHeld sampledIn bookAt)
open VerifiableInference.Desc.Sound (MgData mgAll mgBase MsgT CellsQ moreAll mgAll_pub
  mgAll_more_base mgAll_pubP_said)
open VerifiableInference.Desc.LinkJoin (Rb rest9 ledgerOk linkFit pubFit9 hearN fit_behind fit9_at
  shape_step pubHeld_step sameOn_of held_rides notLeft)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X : Type}
variable {Xi' P Tok : Type} {rows cols nR : Nat} {X' : OnBytes.Model.Verify.Public}

/-- **(P) behind «behind the batching».** b: the member's number; m: its segment's; p, p': its place
and the next. s, s': the verifier's state in front and behind. -/
theorem form_next_behind (𝔇 : MgData Xi' P Tok rows cols nR X')
    (L : Letters Bk Cl W₀ Rc Xi Tr X P (CellsQ rows cols) Tok MsgT)
    (hMg : L.MgP = mgAll 𝔇 mgBase) {b m : Nat} {p p' : Place}
    (hfit : linkFit L.links L.ps = true) (hpf : pubFit9 true moreAll L.links L.ps = true)
    (hp : L.ps[b]? = some p) (hp' : L.ps[b + 1]? = some p') (hl : p.link = some m)
    (hpc : p.piece = hearN L.links m + 2)
    (ht : L.N.treesAt L.ps[b + 1]? = L.N.treesAt L.ps[b]?)
    (hm : L.N.msgsAt L.ps[b + 1]? = L.N.msgsAt L.ps[b]?) {k : Coins Bk} {s s' : S}
    {μ : Mid (Local W₀ Rc Xi Tr) X} (hF : L.thread.Form b k s μ) (R : Rb s s')
    (hrest : ∃ L₀ F₀ t₀, rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s)
    (hled : ledgerOk s = true → ledgerOk s' = true)
    (htot : VerifiableInference.Desc.K9.totalIn (𝔇.pubD.N.group m) s' = true) :
    L.thread.Form (b + 1) k s' μ := by
  obtain ⟨⟨n1, n2⟩, hq, hw⟩ := fit_behind L.links L.ps hfit b m p p' hp hp' hl hpc
  obtain ⟨L₀, F₀, t₀, hr9⟩ := hrest
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 hF.1
  have hon : onAt L.N L.mgP L.links L.ps[b]?
      ((openSets L.links L.ps (start L.links))[b]?.getD [])
      ((pubSets L.mgP.more L.links L.ps)[b]?.getD []) (L.pubOf μ.st.input.x, s) noStrs := hF.2
  have hsh : shapeAt L.links L.ps[b]? s = true := by
    have h := hon
    unfold onAt at h
    rcases h.2 with h' | h'
    · exact absurd h0 h'
    · have h1 := h'.1
      simp only [Bool.and_eq_true] at h1
      exact h1.1.1.1.1.1
  have hmore : L.mgP.more = moreAll := by
    show L.MgP.more = moreAll
    rw [hMg]
    exact mgAll_more_base 𝔇
  have hpubE : L.mgP.pub = (mgAll 𝔇 mgBase).pub := by
    show L.MgP.pub = _
    rw [hMg]
  obtain ⟨hB, hnl⟩ := fit9_at moreAll L.links L.ps hpf b m 2 p hp hl hpc (Or.inr (Or.inl rfl))
  refine form_next_quiet L hp hq hF R.failed (by rw [R.st]) (by rw [R.book]) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hp']
    rw [hp] at hsh
    exact shape_step L.links p p' s s' hsh R.stand n1 n2 (Or.inr hw) R.num
  · intro hb
    unfold bookAt at hb ⊢
    rw [R.book, R.st, ht, hm]
    exact hb
  · show L.MgP.inOrder (L.pubOf μ.st.input.x, s) = true →
      L.MgP.inOrder (L.pubOf μ.st.input.x, s') = true
    rw [hMg]
    exact fun h => h
  · rw [hmore]
    intro h
    exact pubHeld_step L.mgP 𝔇.pubD _ (hpubE.trans (mgAll_pub 𝔇 mgBase)) _ _ _ _ _
      (L.pubOf μ.st.input.x) s s' hB (sameOn_of 𝔇.pubD L₀ F₀ t₀ s s' R hr9) (fun _ => rfl) hled
      (fun q hq' => by
        rw [if_pos rfl] at hq'
        obtain rfl : q = .totalIn m := by simpa using hq'
        rw [hpubE]
        exact htot) h
  · rw [hmore]
    intro _ q hq'
    have h1 := List.all_eq_true.1 hnl q hq'
    show L.MgP.pubP q (L.pubOf μ.st.input.x, s')
    rw [hMg]
    cases q with
    | left _ => simp [notLeft] at h1
    | leftOn _ => simp [notLeft] at h1
    | hasRow _ => trivial
    | _ => exact mgAll_pubP_said 𝔇 _ _ h1
  · intro x _ h
    have h' : L.MgP.held x.1 x.2 (L.pubOf μ.st.input.x, s) = true := h
    show L.MgP.held x.1 x.2 (L.pubOf μ.st.input.x, s') = true
    rw [hMg] at h' ⊢
    exact held_rides s s' R x.1 x.2 h'

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.form_next_behind
