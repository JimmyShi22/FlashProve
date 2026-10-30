-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5FillPlus.lean: kind K5: K5Fill, ALL SEVENTEEN FIELDS
(Johnson/Desc/First/Att/K05T2.lean: what the table's promise in front of the kind's sub-protocol
needs in order to ride over it), AT ANY FILLING Mg WHOSE TESTS OF THE PUBLIC ITEMS ARE THE COMPOSED
TOWER OVER THE WIDER FOOT:
Mg.pub = pubAll D (pubPlus L M D.d3 base) (Johnson/Desc/First/Att/Door/Law/PlusAt.lean), and whose
"in order" is ((in0 a && c5 a.1) && "the statement's codes are cs").

After K5FillAt.lean (not in this library; at another form of the composed filling): what stays is
taken over line for line, by program. WHAT TURNS: the list of the other files' items that answer
alike in front of and behind the kind's lay (quiet9: eight;
with ledger.treesAre and K5.lookLeft apart, which want the hearing's return)
· the field inOrder. PREMISES: as there, BUT
hPo ("what an item says beside its test holds") IS ASKED ONLY AT THE ITEMS THAT THE LAW
TOUCHES: those open in front and made3: at the composed meaning's closed constant (P5J.mgAtAll) the base's sentence is
"somebody answers for the item" (a written table), false at an item outside the table: so a
form at every item cannot be met there. ON THE TABLE: hlow · hQ: every public item that is open
in front of the kind's sub-protocol is one of the ten, one of quiet9's eight, ledger.treesAre or
K5.lookLeft [evaluated at two written lists of segments: see the sheet that goes with the file].
THREE OF quiet9's NAMES HAVE LEFT THE TABLE (K12.seatsCarried · K12.msgShapes · frame.liveIs), A
FOURTH AND A FIFTH NEVER STOOD THERE (K5.rowsBare · K5.lookLeft): they stand at
the wider filling alone. Both are dropped by the kind's own row; K5Fill.rides asks every open item
but seven to ride all the same. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.First.Att.Door.Law.LayKeeps
import Johnson.Desc.First.Att.Door.Law.FillK5Sentences
import Johnson.Desc.First.Att.Door.Law.PlusAt
import Johnson.Desc.First.Att.K05HearBelow
import Johnson.Desc.First.Att.Door.Law.FillK5Pins
import Johnson.Desc.First.Att.Door.Law.FillK5Tie
import Johnson.Desc.First.Att.Door.Law.FillK5Keeper
import Johnson.Desc.First.Look.K3Fill
import Johnson.Desc.First.Att.K05LeftOn

set_option autoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (placeAt k3SortAt lookInC lookOutC linkFreshC liveIsC)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.Desc.First.Att.P (behind hear Heard SameBelow K5Fill later_behind fork_front link_front sized_of_B hear_below Below)
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.OnPublicFiles (k3LeftItemAt k3LeftOnItemAt leftOn_of_left leftOn_stays)

/-- A form that names what is there and filled names it in every later ledger. -/
theorem namedB_later {F G : Fork} (lt : _root_.Fo.Later F G) {f : Aff} (h : FillBare.namedB F f = true) : FillBare.namedB G f = true := by
  unfold FillBare.namedB at h ⊢
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h ⊢
  refine ⟨h.1, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 x hx
  exact ⟨by rw [lt.ns]; exact h1, (lt.keep x.1 h2).1⟩

/-- **The test leftAtB (Johnson/Desc/First/FillBare.lean) on what the lookup argument has left rides
to a later ledger that holds, below the next free number, just what the earlier one holds.** -/
theorem leftAtB_later {g : Forest.Heard} {F G : Fork} (lt : _root_.Fo.Later F G) (bl : Below F G) (h : FillBare.leftAtB g F = true) :
    FillBare.leftAtB g G = true := by
  unfold FillBare.leftAtB at h ⊢
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨⟨⟨⟨⟨⟨fun f hf => namedB_later lt (h1 f hf), namedB_later lt h2⟩, namedB_later lt h3⟩, namedB_later lt h4⟩, h5⟩,
    Nat.le_trans h6 lt.next⟩, ?_⟩
  unfold FillBare.winFreeB at h7 ⊢
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h7 ⊢
  intro i hi
  obtain ⟨c1, c2⟩ := h7 i hi
  refine ⟨by rw [lt.ns]; exact c1, ?_⟩
  rw [(bl.2.2 (g.leaves.first + i) (by omega)).2.2 false]
  exact c2

/-- Three of the four public items that the kind's row makes (the fourth, leftOn m, has a sentence
of its own). -/
def made3 (m : Nat) : List Pub := [.lookIn m 7, .more (some m) "K5.okAt", .more (some m) "K5.plain"]

/-- The items of other files that are shown to answer alike in front of and behind the kind's lay.
-/
def quiet9 (m : Nat) : List Pub :=
  [.unheard, .indexIs, .indexThere, .more none "K12.seatsCarried", .more none "K12.msgShapes", .more (some m) "frame.liveIs",
    .more (some m) "frame.sentIs", .more (some m) "K5.rowsBare"]

section
variable {Pp : Type} (D : PubData) (L : Laid) (M : List OracleShape) (base : Pub → Pp × S → Bool) (π : Pp)

/-- **At each of the eight the composed tests answer alike in front of and behind the kind's lay**,
where an attention segment is open. -/
theorem pubAll_quiet9 (m : Nat) (q : Pub) (hq : q ∈ quiet9 m) (s : S) (a : AttOwn) (h : Heard) (G : Fork) (e : s.here = .att a) :
    pubAll D (pubPlus L M D.d3 base) q (π, behind s a h G) = pubAll D (pubPlus L M D.d3 base) q (π, s) := by
  simp only [quiet9, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rw [pubAll_plus_live, pubAll_plus_live]
    show liveIsC D.d3 (behind s a h G) = liveIsC D.d3 s
    unfold liveIsC S.live
    have h1 : (behind s a h G).link? = some a.L := rfl
    rw [h1, link_front e]
  · rw [pubAll_more_sentIs, pubAll_more_sentIs]
    unfold FillSent.sentIsB
    have h1 : (behind s a h G).link? = some a.L := rfl
    rw [h1, link_front e]
  · rw [pubAll_plus_bare, pubAll_plus_bare]
    show bareAttB (behind s a h G) = bareAttB s
    unfold bareAttB
    rw [e]
    rfl

end

section
variable {Pp : Type} (D : PubData) (base : Pub → Pp × S → Bool) (π : Pp)

theorem pubAll_lookOut_at {m : Nat} {pC : Look.P} (hpC : placeAt D.d3.X m false = some pC) (hs2 : k3SortAt D.d3.X m 2 = some false)
    (s : S) : pubAll D base (.lookOut m 2) (π, s) = K3.k3OnOut pC s := by
  rw [pubAll_lookOut D base m 2 false hs2]
  show ((placeAt D.d3.X m false).any fun p => K3.k3OnOut p s) = _
  rw [hpC]
  rfl

theorem pubAll_lookIn_at {m : Nat} {pD : Look.P} (hpD : placeAt D.d3.X m true = some pD) (hs7 : k3SortAt D.d3.X m 7 = some true)
    (s : S) : pubAll D base (.lookIn m 7) (π, s) =
      (K3.k3OnIn pD s && s.link?.any fun L => L.link == pD.link && L.arrayOf == D.d3.arrayOf.getD m #[]) := by
  rw [pubAll_lookIn D base m 7 true hs7]
  show ((placeAt D.d3.X m true).any fun p => _) = _
  rw [hpD]
  rfl

end

section
variable {Pp Xi Cells Tok : Type} (D : PubData) (base : Pub → Pp × S → Bool) (Mg : Meaning Pp (Wit Cells Tok MsgT)) (π : Pp)

/-- **K5Fill.leftOn at the lookup argument's two Props.** -/
theorem at7_leftOn (hPl : ∀ m a, Mg.pubP (.left m) a = k3LeftItemAt D.d3.X m a.2)
    (hPlo : ∀ m a, Mg.pubP (.leftOn m) a = k3LeftOnItemAt D.d3.X m a.2) (m : Nat) (own : Params.AttentionRounds) :
    ∀ s a h G rs, s.here = .att a → hear own (a.F, rs, 0) = some (h, G, [], 0) → s.fork?.any K3.sizedB = true →
      Mg.pubP (.left m) (π, s) → Mg.pubP (.leftOn m) (π, behind s a h G) := by
  intro s a h G rs e hh hz hL
  rw [hPl] at hL
  rw [hPlo]
  obtain ⟨p, hp, L⟩ := hL
  rw [fork_front e] at hz
  obtain ⟨l1, l2⟩ := later_behind hh (sized_of_B hz)
  have l2' : OnBytes.PscRun.Sized G := by
    obtain ⟨z1, z2, z3⟩ := l2
    exact ⟨z1, z2, z3⟩
  refine ⟨p, hp, leftOn_stays (s := s) (Fs := a.F) (Ft := G) ?_ (fork_front e) rfl l1 l2' (leftOn_of_left L)⟩
  show (behind s a h G).lookHeard? = s.lookHeard?
  unfold S.lookHeard?
  rw [e]
  rfl

/-- **K5Fill, WHOLE.** -/
theorem k5Fill_plus (L : Laid) (M : List OracleShape) (base0 : Pub → Pp × S → Bool) (hbase : base = pubPlus L M D.d3 base0)
    (hpub : Mg.pub = pubAll D base)
    (hPl : ∀ m a, Mg.pubP (.left m) a = k3LeftItemAt D.d3.X m a.2)
    (hPlo : ∀ m a, Mg.pubP (.leftOn m) a = k3LeftOnItemAt D.d3.X m a.2)
    (hheld : Mg.held = fun j t (a : Pp × S) => smpHeld a.2.st a.2.book j t)
    (cs : OnBytes.Codes) (G0 : FileDescription Xi)
    (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp) (ms : List Mem)
    (hshown : Mg.shown = shownJT cs G0 ms) (hnc : Mg.noColl = noCollJT cs G0 smp ms)
    (decT : (Nat → Option (Nat × List UInt64)) → Pp × S → Option Cells) (hdec : Mg.decodes = decodesOf decT)
    (in0 : Pp × S → Bool) (cs' : Codes) (c5 : Pp → Bool)
    (hin : ∀ a : Pp × S, Mg.inOrder a = ((in0 a && c5 a.1) && decide (a.2.st.codes = cs')))
    {m first nsPlan : Nat} (hatt : D.d5.isAtt m = true) (hlay : isLay D.links m = false) (hf : D.d5.first? m = some first)
    (hn : D.nsOf m = some nsPlan)
    {pC pD : Look.P} (hpC : placeAt D.d3.X m false = some pC) (hpD : placeAt D.d3.X m true = some pD)
    (hs2 : k3SortAt D.d3.X m 2 = some false) (hs7 : k3SortAt D.d3.X m 7 = some true)
    (hT : ∀ c s a h G, s.here = .att a → decT c (π, behind s a h G) = decT c (π, s))
    (hsmp : ∀ s a h Gk, s.here = .att a → smp (π, behind s a h Gk) = smp (π, s))
    (h0 : ∀ s a h G, s.here = .att a → in0 (π, s) = true → in0 (π, behind s a h G) = true)
    (N : Numbers) (O : List Item) (Q : List Pub) (Fr : Frame) (bs : Nat) (own : Params.AttentionRounds)
    (hlow : ∀ x ∈ sampledIn N O, x.1 < bs)
    (hQ : ∀ q ∈ Q, q ∈ ten m ∨ q ∈ quiet9 m ∨ q = .more (some m) "ledger.treesAre" ∨ q = .more (some m) "K5.lookLeft")
    (hPo : ∀ q a, (q ∈ Q ∨ q ∈ made3 m) → (∀ m', q ≠ .left m') → (∀ m', q ≠ .leftOn m') → Mg.pubP q a) :
    K5Fill Mg N π Fr bs m O Q own pC pD (D.d3.arrayOf.getD m #[]) first nsPlan where
  decodes := fun s a h G _ y y' e _ hy => at_decodes D.d5 Mg π decT hT hdec s a h G y y' e hy
  inOrder := fun s a h G _ e _ => by
    rw [hin, hin]
    simp only [Bool.and_eq_true]
    rintro ⟨⟨a1, a2⟩, a3⟩
    exact ⟨⟨h0 s a h G e a1, a2⟩, a3⟩
  held := fun x _ s a h G _ _ _ => at_held D.d5 Mg π hheld x.1 x.2 s a h G
  strs := fun x hx s a h G _ y y' e _ hy => at_strs D.d5 Mg π cs G0 smp ms hsmp hshown hnc (hlow x hx) s a h G y y' e hy
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
    · rw [hbase] at hv ⊢
      rw [pubAll_quiet9 D L M base0 π m q ht s a h G e]; exact hv
    · subst ht
      rw [pubAll_more_treesAre] at hv ⊢
      rw [fork_front e] at hz
      obtain ⟨_, bl⟩ := hear_below hh (sized_of_B hz)
      unfold FillSent.treesAreB at hv ⊢
      rw [fork_front e] at hv
      show (Option.any (fun U : Fork => decide (U.trees.toList.map FillSent.treeLook = D.dS.trees m)) (some G)) = true
      simp only [Option.any_some] at hv ⊢
      rw [bl.trees]
      exact hv
    · subst ht
      rw [hbase, pubAll_plus_left] at hv ⊢
      rw [fork_front e] at hz
      obtain ⟨_, bl⟩ := hear_below hh (sized_of_B hz)
      obtain ⟨lt, _⟩ := later_behind hh (sized_of_B hz)
      unfold leftAttB at hv ⊢
      rw [e] at hv
      have hv' : (a.lookHeard.any fun g => FillBare.leftAtB g a.F) = true := hv
      show (a.lookHeard.any fun g => FillBare.leftAtB g G) = true
      cases hl : a.lookHeard with
      | none => rw [hl] at hv'; cases hv'
      | some g =>
        rw [hl] at hv'
        exact leftAtB_later lt bl hv'
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
      · simp only [ten, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or, Pub.left.injEq] at ht
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

end

#print axioms leftAtB_later
#print axioms pubAll_quiet9
#print axioms pubAll_lookOut_at
#print axioms pubAll_lookIn_at
#print axioms at7_leftOn
#print axioms k5Fill_plus

end H2K5.Door
