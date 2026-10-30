-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/FillHonest.lean: CONDITIONAL: what the promise of the table of the
verifier's blocks needs in order to ride over the block of an attention segment's own rounds
(`K5Fill`, seventeen fields, Johnson/Desc/First/Att/K05T2.lean), at a filling Mg of this sort: its
tests with code are the library's composed ones over any base (`pubAll D base`); of its three
sentences on the strings (the stored table decodes; a tenant's tree shows all its leaves; no two
members answer a sample alike) each holds outright; and no public item that is open in front is one
of the five names that stand at the library's wider filling alone (the premise hnw; at the head's
letters the clause `narrow` of `AtBorder`, Johnson/Desc/K5/Honest/Law/BehindAtHead.lean).

Why. The library has `K5Fill` at its wider filling (`k5Fill_plus`,
Johnson/Desc/First/Att/Door/Law/K5FillPlus.lean), where the three sentences are equations with
terms on the strings. At a filling in which they hold outright the two fields on them are
trivial. The other fifteen read the tests with code, what the items say beside them, "held" and
"in order" alone; their proofs follow that file's, field by field. Where that file spends the wider
base (eight items that answer alike in front and behind) the answer is carried over by
`plus_same` (Johnson/Desc/First/Att/Door/Law/PlusBridge.lean): away from the five names the two
functions agree.

Main name: `k5Fill_honest`.
Limits. Conditional on every premise in the statement; none is shown to be met here.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.Door.Law.K5FillPlus
import Johnson.Desc.First.Att.Door.Law.PlusBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (placeAt k3SortAt)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.Desc.First.Att.P (behind hear Heard K5Fill fork_front sized_of_B
  hear_below)
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.OnPublicFiles (k3LeftItemAt k3LeftOnItemAt)
open H2K5.Door

/-- **The seventeen fields at a filling whose three sentences on the strings hold outright.**
Conditional:
  hpub: the tests with code are the composed ones over the base;
  hPl, hPlo: what the two items on the lookup's leavings say;
  hheld: "held" reads the statement and the book alone;
  hdec, hshown, hnc: the three sentences on the strings hold outright;
  hin, h0: "in order" is a test in0 that rides over the lay, and a test on the public part;
  hatt .. hs7: facts on the composed data at the attention segment m;
  hQ: every public item that is open in front is one of a written list;
  hnw: none of them is one of the five names of the wider filling;
  hPo: what an item says beside its test holds at every state, at the items that the law touches.
L, M: free letters of the lemma that carries the answers over. -/
theorem k5Fill_honest {Pp Cells Tok : Type} (D : PubData) (base : Pub → Pp × S → Bool)
    (Mg : Meaning Pp (Wit Cells Tok MsgT)) (π : Pp) (L : Laid) (M : List OracleShape)
    (hpub : Mg.pub = pubAll D base)
    (hPl : ∀ m a, Mg.pubP (.left m) a = k3LeftItemAt D.d3.X m a.2)
    (hPlo : ∀ m a, Mg.pubP (.leftOn m) a = k3LeftOnItemAt D.d3.X m a.2)
    (hheld : Mg.held = fun j t (a : Pp × S) => smpHeld a.2.st a.2.book j t)
    (hdec : ∀ a y, Mg.decodes a y) (hshown : ∀ j t y, Mg.shown j t y)
    (hnc : ∀ j t a y, Mg.noColl j t a y) (in0 : Pp × S → Bool) (c5 : Pp → Bool)
    (hin : ∀ a : Pp × S, Mg.inOrder a = (in0 a && c5 a.1)) {m first nsPlan : Nat}
    (hatt : D.d5.isAtt m = true) (hlay : isLay D.links m = false)
    (hf : D.d5.first? m = some first) (hn : D.nsOf m = some nsPlan) {pC pD : Look.P}
    (hpC : placeAt D.d3.X m false = some pC) (hpD : placeAt D.d3.X m true = some pD)
    (hs2 : k3SortAt D.d3.X m 2 = some false) (hs7 : k3SortAt D.d3.X m 7 = some true)
    (h0 : ∀ s a h G, s.here = .att a → in0 (π, s) = true → in0 (π, behind s a h G) = true)
    (N : Numbers) (O : List Item) (Q : List Pub) (Fr : Frame) (bs : Nat)
    (own : Params.AttentionRounds)
    (hQ : ∀ q ∈ Q, q ∈ ten m ∨ q ∈ quiet9 m ∨ q = .more (some m) "ledger.treesAre" ∨
      q = .more (some m) "K5.lookLeft")
    (hnw : ∀ q ∈ Q, isWideQ q = false)
    (hPo : ∀ q a, (q ∈ Q ∨ q ∈ made3 m) → (∀ m', q ≠ .left m') → (∀ m', q ≠ .leftOn m') →
      Mg.pubP q a) :
    K5Fill Mg N π Fr bs m O Q own pC pD (D.d3.arrayOf.getD m #[]) first nsPlan where
  decodes := fun _ _ _ _ _ _ _ _ _ _ _ => hdec _ _
  inOrder := fun s a h G _ e _ => by
    rw [hin, hin]
    simp only [Bool.and_eq_true]
    rintro ⟨a1, a2⟩
    exact ⟨h0 s a h G e a1, a2⟩
  held := fun x _ s a h G _ _ _ => at_held D.d5 Mg π hheld x.1 x.2 s a h G
  strs := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => ⟨hshown _ _ _, hnc _ _ _ _⟩
  ledger := fun s => by rw [hpub]; rfl
  lookOut := fun s => by rw [hpub]; exact pubAll_lookOut_at D base π hpC hs2 s
  callerIn := fun s => by
    rw [hpub, pubAll_callerIn_att D base m hlay hatt, hf]
    rfl
  lookIn := fun s => by rw [hpub]; exact pubAll_lookIn_at D base π hpD hs7 s
  linkFresh := fun s => by rw [hpub]; rfl
  freeAbove := fun s => by
    rw [hpub, pubAll_freeAbove, hn]
    exact (keeper_freeAbove_is nsPlan s).trans (freeAboveB_is nsPlan s)
  leftOnB := fun s => by rw [hpub]; rfl
  lookInP := fun s => hPo _ _ (Or.inr (by simp [made3])) (fun _ => by simp) (fun _ => by simp)
  leftOn := at7_leftOn D Mg π hPl hPlo m own
  rides := fun q hq n1 n2 n3 n4 n5 n6 n7 s a h G rs e hh hz hv => by
    rw [hpub] at hv ⊢
    rcases hQ q hq with ht | ht | ht | ht
    · simp only [ten, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hv
      · exact absurd rfl n1
      · exact absurd rfl n3
      · exact absurd rfl n4
      · rw [pubAll_more_readsThere D base m hatt] at hv ⊢
        exact readsThereB_behind D.d5.W (D.d5.ownOf m) e hh hz hv
      · rw [pubAll_more_liveReq D base m hatt] at hv ⊢
        exact liveReqB_behind (bornOf D.d5.shape m) e hv
      · exact absurd rfl n2
      · exact absurd rfl n5
      · exact absurd rfl n6
      · exact absurd rfl n7
    · rw [← plus_same D L M base (hnw q hq), pubAll_quiet9 D L M base π m q ht s a h G e,
        plus_same D L M base (hnw q hq)]
      exact hv
    · subst ht
      rw [pubAll_more_treesAre] at hv ⊢
      rw [fork_front e] at hz
      obtain ⟨_, bl⟩ := hear_below hh (sized_of_B hz)
      unfold FillSent.treesAreB at hv ⊢
      rw [fork_front e] at hv
      show (Option.any (fun U : Fork =>
        decide (U.trees.toList.map FillSent.treeLook = D.dS.trees m)) (some G)) = true
      simp only [Option.any_some] at hv ⊢
      rw [bl.trees]
      exact hv
    · subst ht
      have hw : isWideQ (.more (some m) "K5.lookLeft") = true := rfl
      rw [hnw _ hq] at hw
      cases hw
  indexIs := fun s a h G _ e _ hv => by
    rw [hpub] at hv ⊢
    exact hv
  indexThere := fun s a h G _ e _ hv => by
    rw [hpub] at hv ⊢
    exact hv
  ridesP := fun q hq _ n6 _ s a h G _ _ _ _ => by
    refine hPo q _ (Or.inl hq) ?_ ?_
    · intro m' hm'
      subst hm'
      rcases hQ _ hq with ht | ht | ht | ht
      · simp only [ten, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or,
          Pub.left.injEq] at ht
        exact n6 (by rw [ht])
      · simp [quiet9] at ht
      · simp at ht
      · simp at ht
    · intro m' hm'
      subst hm'
      rcases hQ _ hq with ht | ht | ht | ht
      · simp [ten] at ht
      · simp [quiet9] at ht
      · simp at ht
      · simp at ht

end H2K5.Honest

#print axioms H2K5.Honest.k5Fill_honest
