-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/H3/Guards.lean: the kind "lookup" (K3): four statements
against hollowness of `k3Marks_hM_blocks` (Honest/K3/Good/H3/Join.lean): that it speaks at every
site; that data such as it asks exist; that its hypothesis on the letter runs over something; that
two marks stand at each site's place. Theorems.

Terms. Honest/K3/GLOSSARY.md: see there mark (in the frame's sense), site, member and flat list.

What is shown.
  `site_has_behind`: conditional on `P5J.AtMgA` and the cut: the member at a site's place lies in
    pre₁ with a member of pre₁ behind it.
  `site_data_exist`: conditional on `P5J.AtMgA`: data that bear the member's rounds exist.
  `capRounds_laid`: at every listed number the plan has an entry, and its name a kind.
  `site_two_marks`: both marks of a site stand in the list. No hypothesis but the site.
Helpers: `border_le`, `split_two`, `laid_has`, `data_of`.

How `site_has_behind` goes. Under the head the flat list's length is a written number
(`atRow_length`, Johnson/Desc/Kinds/Law/RowLenAtConst.lean). A site's place
stands at the written number `borderOf s.link s.digits` of the written list of places
(`site_border`, Honest/K3/Law/Thread/SiteAtLetters.lean), and the link is below 25. The rest is
arithmetic.

Hypotheses that remain. `h`: `P5J.AtMgA`. `cut`: the flat list is pre₁ and one sub-protocol behind
it. `h2`, `h1`, `hes`: as in Honest/K3/Good/H3/Spots.lean and Entries.lean.

Users. None.

Limits. No instance of `P5J.AtMgA` is exhibited in this file. Nothing here says that the hypothesis
on the letter holds at a number at which the bound says something.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.H3.Join
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteAtLetters
import Johnson.Desc.Kinds.Law.RowLenAtConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K3 (entriesV entriesFit)
open VerifiableInference.Desc.First (blockPlaces)
open VerifiableInference.Desc.First.Att.P (KindGood)
open VerifiableInference.Desc.Sound.MgAt (ixOf borderOf)
open OnBytes.Maker (RDT WholeD)
open P5J (AtMgA TS)

/-! ## 1 The join speaks at every site -/

/-- Below 25 links a lookup's border is at most 345. -/
theorem border_le (l : Nat) (hl : l < 25) (d : Bool) : borderOf l d ≤ 345 := by
  unfold borderOf ixOf
  split <;> split <;> omega

/-- A list is cut in front of two neighbours. -/
theorem split_two {α : Type} (l : List α) (n : Nat) (h : n + 1 < l.length) :
    l = l.take n ++ l[n]'(by omega) :: l[n + 1]'h :: l.drop (n + 2) := by
  conv_lhs => rw [← List.take_append_drop n l, List.drop_eq_getElem_cons (by omega : n < l.length),
    List.drop_eq_getElem_cons h]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL on the head and the cut: THE JOIN SPEAKS AT EVERY SITE: the member at a
site's place lies in pre₁ with a member of pre₁ behind it. -/
theorem site_has_behind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pre₁ : List (Block TS ProofFile.Cl)}
    {e₁ : Block TS ProofFile.Cl} (cut : cF.blocksInOrder = pre₁ ++ [e₁]) (s : Site) (hs : s ∈ lookSites Zp) :
    ∃ A b b' B, pre₁ = A ++ b :: b' :: B ∧ b.place = s.at_.place := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨lot, hl, hls⟩ := Law.lot_of_site _ _ _ _ _ Zp Bs base cF _ _ O s hs
  obtain ⟨h25, hps, _⟩ := Law.AtThr.site_border h s hs lot hl hls
  have hlen := VerifiableInference.Desc.Kinds.Head.Law.atRow_length h.toAtMg
  have hb := border_le s.link h25 s.digits
  have hpre : pre₁.length = 357 := by
    have e := congrArg List.length cut
    rw [List.length_append, List.length_singleton, hlen] at e
    omega
  have hn : borderOf s.link s.digits + 1 < pre₁.length := by omega
  refine ⟨_, _, _, _, split_two pre₁ (borderOf s.link s.digits) hn, ?_⟩
  have hP : blockPlaces cF.blocksInOrder = P5J.At.ps := P5J.At.places_paid h.scope h.reads h.laid
  rw [← hP] at hps
  unfold blockPlaces at hps
  rw [List.getElem?_map, cut, List.getElem?_append_left (by omega),
    List.getElem?_eq_getElem (by omega)] at hps
  exact Option.some.inj hps

/-! ## 2 Data exist -/

/-- Data that bear a list of declared rounds whose names have kinds. -/
theorem data_of : ∀ zs : List Fmt.DeclaredRound, (∀ z ∈ zs, ∃ k, Fmt.kindOf z.entry.name = some k) →
    ∃ dsb : List RDT, List.Forall₂ KindFits dsb zs
  | [], _ => ⟨[], .nil⟩
  | z :: zs, h => by
    obtain ⟨k, hk⟩ := h z List.mem_cons_self
    obtain ⟨ds, hds⟩ := data_of zs fun z' hz' => h z' (List.mem_cons_of_mem _ hz')
    exact ⟨
      { entry := z.entry, kind := k, items := [], trees := [], opens := [], stored := [] } :: ds,
      .cons (And.intro rfl hk) hds⟩

/-- CONDITIONAL on the head: data that bear the member's rounds exist. Some data: they are made up
in the proof (no item, no tree, no opening): never that they are the description's own. -/
theorem site_data_exist (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (b : Block TS ProofFile.Cl) (hb : b ∈ cF.blocksInOrder) (hp : b.place = s.at_.place) :
    ∃ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds := by
  obtain ⟨hr, hes⟩ := member_at_site h s hs b hb hp
  rw [hr]
  refine data_of _ fun z hz => ?_
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
  obtain ⟨_, _, k, hk, _⟩ := entriesV_tame _ _ (fit_mem _ _ hes e he)
  exact ⟨k, hk⟩

/-! ## 3 The hypothesis on the letter runs over something -/

/-- At a number at which the verifier's list has an entry, the plan has one, and its name a kind. -/
theorem laid_has (f : LFace) (es : List Fmt.Entry) (hes : entriesFit f es = true) (n : Nat)
    (en : Fmt.Entry) (h : (entriesV f)[n]? = some en) :
    ∃ e k, es[n]? = some e ∧ Fmt.kindOf e.name = some k := by
  obtain ⟨e, he, e2⟩ := fit_at f es hes n en h
  obtain ⟨_, _, k, hk, _⟩ := entriesV_tame f en (List.mem_of_getElem? h)
  have n1 : e.name = en.name := congrArg (·.name) e2
  exact ⟨e, k, he, by rw [n1]; exact hk⟩

/-- THE PREMISE's «∀» RUNS OVER SOMETHING: at every listed number the plan has an entry,
and its name a kind. -/
theorem capRounds_laid (f : LFace) (h2 : 2 ≤ f.planes) (h1 : ∀ v ∈ f.parts, 1 ≤ v)
    (es : List Fmt.Entry) (hes : entriesFit f es = true) :
    ∀ n ∈ capRounds f, ∃ e k, es[n]? = some e ∧ Fmt.kindOf e.name = some k := by
  intro n hn
  unfold capRounds at hn
  rcases List.mem_append.1 hn with h | h
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    have hl : SpotLaid f e.spot := by
      rcases List.mem_append.1 he with h' | h'
      · obtain ⟨p, hp, hep⟩ := List.mem_flatMap.1 h'
        rw [spot_of_mem hep]
        exact spot_laid f h2 p hp
      · obtain ⟨p, hp, hep⟩ := List.mem_flatMap.1 h'
        rw [spot_of_mem hep]
        exact spotOut_laid f h2 h1 p hp
    unfold SpotLaid at hl
    obtain ⟨en, hen, _, _⟩ := hl
    exact laid_has f es hes _ en hen
  · obtain rfl := List.mem_singleton.1 h
    exact laid_has f es hes _ _ (alpha_laid f h2)

/-! ## 4 Two marks a site -/

/-- The filter is not empty: two marks at each site's place. -/
theorem site_two_marks (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) (s : Site) (hs : s ∈ lookSites Zp) :
    markK3 s.at_.place s.at_.face ∈ k3Marks Zp G₀ ∧ markOut s.at_.place s.at_.face ∈ k3Marks Zp G₀
    := by
  unfold k3Marks
  exact ⟨List.mem_flatMap.2 ⟨s, hs, List.mem_cons_self⟩,
    List.mem_flatMap.2 ⟨s, hs, List.mem_cons_of_mem _ List.mem_cons_self⟩⟩

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.border_le
#print axioms ProofFile.Honest.K3.Good.split_two
#print axioms ProofFile.Honest.K3.Good.site_has_behind
#print axioms ProofFile.Honest.K3.Good.data_of
#print axioms ProofFile.Honest.K3.Good.site_data_exist
#print axioms ProofFile.Honest.K3.Good.laid_has
#print axioms ProofFile.Honest.K3.Good.capRounds_laid
#print axioms ProofFile.Honest.K3.Good.site_two_marks
