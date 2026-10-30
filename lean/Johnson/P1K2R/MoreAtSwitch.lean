-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/MoreAtSwitch.lean (over MoreAtEQ.lean, Johnson/IMR/TableW.lean, PubRides.lean
and Johnson/Desc/Sound/MoreAll.lean): code switching (K2): THE FIELD «more» OF ITS THREE
SHARES, AT E := EQ («in order» and the public items' test of the table of joints' promise), AT THE
COMPOSED PUBLIC TESTS (pubAll) AND THE ROWS OF EXTRA PUBLIC TESTS (moreAll). NO BLOCK
IMPORTS THIS FILE.
  askedW M k     the public items that the promise asks at border k of the written list: open
                 there, or tied to an item that is open there
  madeAt l · behindAt l   what a link's first place makes (six names; eight at an attention link)
                          · what is asked behind it
  asked_links · asked_head · asked_finish   BY LEAN's KERNEL, AT ALL 25: in front of a link's
                                            switch: [unheard, indexIs, indexThere]; behind: these
                                            with madeAt l between · at 339: [tokenSmall, indexIs,
                                            indexThere] and these with six made · at 353:
                                            [indexIs, indexThere] ON BOTH SIDES: NOTHING IS MADE
  asked_wrong    a negative test
  more_link · more_head · more_finish   X k at E := EQ in front · Mg.pub = pubAll D base · Mg.more
                                        = moreAll · «in order» rides · s'.out = s.out · no oracle
                                        message is taken away · (at 339: «tokenSmall» rides) ·
                                        every made item's test holds behind ⟹ EQ Mg linksW placesW
                                        z (k + 1) s' = true. AT THE FINISH NO MAKING IS ASKED.
LEFT: the makings (they read the open link's own part of the state, which the frame's «opened» |
"H.1.quiet" lays): ledger · lookIn · linkFresh · freeAbove · "frame.sentIs" · "ledger.treesAre" ·
at attention links "K5.readsThere" · "K5.liveReq" · «tokenSmall» rides at 339 · that the step
leaves out and takes no message away (K2's own laws and the doors'). No soundness is claimed.

-/
import Johnson.P1K2R.MoreAtEQ
import Johnson.IMR.TableW
import Johnson.Top.H0.Tw.K2C.PubRides
import Johnson.Desc.Sound.MoreAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart Numbers Pub More Meaning PubData pubAll pubSets
  pubOfItems)
open VerifiableInference.Desc.First.K2 (pub_rides3)
open VerifiableInference.Desc.Sound (moreAll)
open IM (XK openAt linksW placesW subW)

/-- What the promise asks of public items at border k of the written list. -/
def askedW (M : More) (k : Nat) : List Pub :=
  ((pubSets M linksW placesW)[k]?).getD [] ++ pubOfItems (openAt linksW placesW k)

/-- What a link's first place makes. pc: the piece at which the first lookup stands. -/
def madeAt (l pc : Nat) (att : Bool) : List Pub :=
  [.ledger l, .lookIn l pc, .linkFresh l, .freeAbove l, .more (some l) "frame.sentIs",
    .more (some l) "ledger.treesAre"] ++
  (if att then [.more (some l) "K5.readsThere", .more (some l) "K5.liveReq"] else [])

def askedB (k : Nat) (front behind : List Pub) : Bool :=
  decide (askedW moreAll k = front) && decide (askedW moreAll (k + 1) = behind)

set_option maxRecDepth 1000000 in
theorem asked_links : ((List.range' 1 23).all fun l =>
    askedB (14 * l + 2) [.unheard, .indexIs, .indexThere]
      (.unheard :: madeAt l 2 (decide (subW l = .attention)) ++ [.indexIs, .indexThere])) =
    true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem asked_head : askedB 339 [.tokenSmall, .indexIs, .indexThere]
    (.tokenSmall :: madeAt 24 3 false ++ [.indexIs, .indexThere]) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem asked_finish : askedB 353 [.indexIs, .indexThere] [.indexIs, .indexThere] = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem asked_wrong : askedB 353 [.indexIs] [.indexIs, .indexThere] = false := by
  decide +kernel

theorem asked_parts {k : Nat} {front behind : List Pub} (h : askedB k front behind = true) :
    askedW moreAll k = front ∧ askedW moreAll (k + 1) = behind := by
  unfold askedB at h
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
  exact h

variable {P W : Type}

/-- The rule at a switch: rd the items that ride, made those that are made. -/
theorem more_at {N : Numbers} {Mg : Meaning P W} {z : P} {k : Nat} {s s' : S}
    {front behind : List Pub} (hA : askedB k front behind = true) (hmore : Mg.more = moreAll)
    (hx : XK N linksW placesW (EQ Mg linksW placesW z) k s = true)
    (hIn : Mg.inOrder (z, s) = true → Mg.inOrder (z, s') = true)
    (hk : ∀ q ∈ behind, q ∈ front → Mg.pub q (z, s) = true → Mg.pub q (z, s') = true)
    (hm : ∀ q ∈ behind, ¬ q ∈ front → Mg.pub q (z, s') = true) :
    EQ Mg linksW placesW z (k + 1) s' = true := by
  obtain ⟨e1, e2⟩ := asked_parts hA
  have f1 : pubAt Mg linksW placesW k ++ pubOfItems (openAt linksW placesW k) = front := by
    unfold pubAt
    rw [hmore]
    exact e1
  have f2 : pubAt Mg linksW placesW (k + 1) ++ pubOfItems (openAt linksW placesW (k + 1)) =
      behind := by
    unfold pubAt
    rw [hmore]
    exact e2
  refine more_of_pub hx hIn ?_ ?_
  · rw [f1, f2]
    exact hk
  · rw [f1, f2]
    exact hm

theorem more_finish {N : Numbers} {Mg : Meaning P W} {z : P} {s s' : S} (D : PubData)
    (base : Pub → P × S → Bool) (hpub : Mg.pub = pubAll D base) (hmore : Mg.more = moreAll)
    (hx : XK N linksW placesW (EQ Mg linksW placesW z) 353 s = true)
    (hIn : Mg.inOrder (z, s) = true → Mg.inOrder (z, s') = true) (ho : s'.out = s.out)
    (ht : ∀ j : Nat, (s.st.oracles[j]?).isSome = true → (s'.st.oracles[j]?).isSome = true) :
    EQ Mg linksW placesW z (353 + 1) s' = true := by
  refine more_at asked_finish hmore hx hIn (fun q hq _ h => ?_) fun q hq hn => absurd hq hn
  rw [hpub] at h ⊢
  exact pub_rides3 D base z ho ht q (List.mem_cons_of_mem _ hq) h

theorem more_link {N : Numbers} {Mg : Meaning P W} {z : P} {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24)
    {s s' : S} (D : PubData) (base : Pub → P × S → Bool) (hpub : Mg.pub = pubAll D base)
    (hmore : Mg.more = moreAll)
    (hx : XK N linksW placesW (EQ Mg linksW placesW z) (14 * l + 2) s = true)
    (hIn : Mg.inOrder (z, s) = true → Mg.inOrder (z, s') = true) (ho : s'.out = s.out)
    (ht : ∀ j : Nat, (s.st.oracles[j]?).isSome = true → (s'.st.oracles[j]?).isSome = true)
    (hMade : ∀ q ∈ madeAt l 2 (decide (subW l = .attention)), Mg.pub q (z, s') = true) :
    EQ Mg linksW placesW z (14 * l + 2 + 1) s' = true := by
  have hA := List.all_eq_true.1 asked_links l (List.mem_range'_1.2 ⟨h1, by omega⟩)
  refine more_at hA hmore hx hIn (fun q _ hf h => ?_) fun q hq hn => ?_
  · rw [hpub] at h ⊢
    exact pub_rides3 D base z ho ht q hf h
  · rcases List.mem_cons.1 hq with rfl | hq
    · exact absurd (List.mem_cons_self) hn
    · rcases List.mem_append.1 hq with hq | hq
      · exact hMade q hq
      · exact absurd (List.mem_cons_of_mem _ hq) hn

theorem more_head {N : Numbers} {Mg : Meaning P W} {z : P} {s s' : S} (D : PubData)
    (base : Pub → P × S → Bool) (hpub : Mg.pub = pubAll D base) (hmore : Mg.more = moreAll)
    (hx : XK N linksW placesW (EQ Mg linksW placesW z) 339 s = true)
    (hIn : Mg.inOrder (z, s) = true → Mg.inOrder (z, s') = true) (ho : s'.out = s.out)
    (ht : ∀ j : Nat, (s.st.oracles[j]?).isSome = true → (s'.st.oracles[j]?).isSome = true)
    (htok : Mg.pub .tokenSmall (z, s) = true → Mg.pub .tokenSmall (z, s') = true)
    (hMade : ∀ q ∈ madeAt 24 3 false, Mg.pub q (z, s') = true) :
    EQ Mg linksW placesW z (339 + 1) s' = true := by
  refine more_at asked_head hmore hx hIn (fun q _ hf h => ?_) fun q hq hn => ?_
  · rcases List.mem_cons.1 hf with rfl | hf
    · exact htok h
    · rw [hpub] at h ⊢
      exact pub_rides3 D base z ho ht q (List.mem_cons_of_mem _ hf) h
  · rcases List.mem_cons.1 hq with rfl | hq
    · exact absurd (List.mem_cons_self) hn
    · rcases List.mem_append.1 hq with hq | hq
      · exact hMade q hq
      · exact absurd (List.mem_cons_of_mem _ hq) hn

end P1K2

#print axioms P1K2.asked_links
#print axioms P1K2.asked_head
#print axioms P1K2.asked_finish
#print axioms P1K2.more_link
#print axioms P1K2.more_head
#print axioms P1K2.more_finish
