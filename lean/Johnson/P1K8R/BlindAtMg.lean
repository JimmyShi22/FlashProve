-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/BlindAtMg.lean: THE SMALLNESS TEST's DRAW AT THE COMPOSED MEANING: DrawBlind
(Johnson/Desc/First/K8/TieRides.lean), ALL ELEVEN FIELDS, AT mgAll 𝔇 mgBase (
Johnson/Desc/Sound/MgAll.lean | MgBase.lean), AT EACH OF THE 25 PLACES OF
THE WRITTEN LIST, FROM WHAT THE PARAMETERS 𝔇 OWE.
WHAT IS SAID.
  drawBlind_mg     l ≤ 24 · 𝔇.links = linksFull · MgOwes 𝔇 l base · two equations on 𝔇.N (the draw's row sends no tree and no message) ⟹ DrawBlind 𝔇.N (mgAll 𝔇 mgBase) linksFull (flatPlacesOf linksFull true) (ixOf l) base (oSMg 𝔇 l).
  oSMg 𝔇 l         what the draw must MAKE behind itself: formsInA (𝔇.Rd l) (𝔇.N.sent l) (𝔇.N.group l) (pcOf l − 1) "K8.equations" at the state behind: the public test that the table ties to the run of forms "small", which the draw's row opens. NOT SHOWN HERE: it is taken in hand.
  MgOwes 𝔇 l base  SEVEN FIELDS: decT · smp · H.req have one value in front of the draw's yes and behind it · headPart · wt go back over the draw · the readers of the runs that the table names at the segment's pieces IN FRONT OF the draw's (k < pcOf l) are blind · the fence: every tenant of a pin that is open in front of the draw sits in a tree below base (the index masks' tenant and those of the segment's first two sendings among them: MgOwes.fenceI | fenceS, by a closed fact on the table).
  mg_decodes | mg_inOrder | mg_held | mg_shown | mg_noColl | mg_pub | mg_pubP: the promise's clauses · mg_back: every sort of item that rides goes back over the draw: parts of later segments' relations · the committed table's pin · the pile · the index masks' pin · the segment's rows · its pending claim on the weights · the forms of its earlier runs · mg_pin_back: what the row reads.
  k8_pub_full | k8_rider_full: the kernel's closed facts (TableAtK8.lean) as statements on members; the second over the table's own openIsList | openL_iff_openSets.
LIMITS. MgOwes IS SHOWN AT NO VALUE OF 𝔇: NOT AT THE CLOSED CONSTANT (P5J.mgAtAll, Johnson/P5J/MgAtAll.lean) EITHER: WHETHER ITS SEVEN FIELDS CAN BE MET TOGETHER IS NOT SHOWN: NO EXAMPLE. At the written lists of links and places. No soundness. Nothing on hiding.
-/
import Johnson.P1K8R.RunsAhead
import Johnson.Desc.Sound.MgBase
import Johnson.Desc.Sound.ReadsTreeAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc (Place KindName Strs Wit smpHeld)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers flatPlacesOf openSets pubSets
  start stepOpen pubStep pubRowM rowOf pubOfItems pubHeld sampledIn pubAll)
open VerifiableInference.Desc.First.K8 (Drawn SameBelow TlBlind k8Sort pubAll_blind blind_fork
  blind_lookHeard blind_st blind_book blind_out blind_leftOf blind_segAt blind_mergeOf blind_formsIn
  DrawBlind)

theorem blind_leftOn (X : OnBytes.Model.Verify.Public) (m : Nat) (s t : S) (h : Drawn s t)
    (hp : VerifiableInference.OnPublicFiles.k3LeftOnItemAt X m s) :
    VerifiableInference.OnPublicFiles.k3LeftOnItemAt X m t := by
  obtain ⟨p, hp1, ⟨hh, e, F, F', G, g, rs, q1, q2, q3, q4, q5, q6, q7⟩, hb⟩ := hp
  refine ⟨p, hp1, ⟨hh, e, F, F', G, g, rs, q1, q2, q3, ?_, ?_, q6, q7⟩, fun g' hg => hb g' ?_⟩
  · exact (blind_lookHeard s t h).trans q4
  · exact (blind_fork s t h).trans q5
  · exact (blind_lookHeard s t h).symm.trans hg


/-! ## The oracles' sentences: the state's side -/

section
variable (cs : OnBytes.Codes) {Xi A Cells Tok : Type} (G : VerifiableInference.Desc.FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem)

theorem noCollJT_state (j t : ℕ) (a a' : A) (y : Strs) (h : smp a' = smp a)
    (hp : noCollJT cs G smp ms j t a y) : noCollJT cs G smp ms j t a' y := by
  intro x hx hs
  obtain ⟨σ, hσ, h1, h2⟩ := hp x hx hs
  refine ⟨σ, ?_, h1, h2⟩
  show smp a' x.1 x.2 = some σ
  rw [h]
  exact hσ

theorem pinJT_state (j t : ℕ) (a a' : A) (y : Strs) (w : Wit Cells Tok MsgT) (h : smp a' = smp a)
    (hp : pinJT cs G arr smp ms j t a y w) : pinJT cs G arr smp ms j t a' y w := by
  refine ⟨hp.1, fun x hx hs => ?_⟩
  obtain ⟨σ, hσ, h1, h2⟩ := hp.2 x hx hs
  refine ⟨σ, ?_, h1, h2⟩
  show smp a' x.1 x.2 = some σ
  rw [h]
  exact hσ

end

/-! ## The promise's clauses at the composed meaning over its closed base -/

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)

theorem mg_decodes (hd : ∀ c z, TlBlind fun s => 𝔇.decT c (z, s)) (base : ℕ) (z : P) (s t : S)
    (y y' : Strs) (h : Drawn s t) (hy : SameBelow base y y')
    (hp : (mgAll 𝔇 mgBase).decodes (z, s) y) : (mgAll 𝔇 mgBase).decodes (z, t) y' := by
  rw [mgAll_decodes] at hp ⊢
  unfold decodesOf at hp ⊢
  have e : 𝔇.decT y.cell (z, t) = 𝔇.decT y.cell (z, s) := hd y.cell z s t h
  rw [hy.1, e]
  exact hp

theorem mg_inOrder (z : P) (s t : S) (hp : (mgAll 𝔇 mgBase).inOrder (z, s) = true) :
    (mgAll 𝔇 mgBase).inOrder (z, t) = true := hp

theorem mg_held (z : P) (s t : S) (h : Drawn s t) (j i : ℕ)
    (hp : (mgAll 𝔇 mgBase).held j i (z, s) = true) : (mgAll 𝔇 mgBase).held j i (z, t) = true := by
  rw [mgAll_held] at hp ⊢
  show smpHeld t.st t.book j i = true
  rw [blind_st s t h, blind_book s t h]
  exact hp

theorem mg_shown (base : ℕ) (y y' : Strs) (hy : SameBelow base y y') (j i : ℕ) (hj : j < base)
    (hp : (mgAll 𝔇 mgBase).shown j i y) : (mgAll 𝔇 mgBase).shown j i y' := by
  rw [mgAll_shown] at hp ⊢
  exact shownJT_col 𝔇.cs 𝔇.G 𝔇.ms j i y y' (fun x => hy.2 j x hj) hp

theorem mg_noColl (hs : ∀ z, TlBlind fun s => 𝔇.smp (z, s)) (base : ℕ) (z : P) (s t : S)
    (y y' : Strs) (h : Drawn s t) (hy : SameBelow base y y') (j i : ℕ) (hj : j < base)
    (hp : (mgAll 𝔇 mgBase).noColl j i (z, s) y) : (mgAll 𝔇 mgBase).noColl j i (z, t) y' := by
  rw [mgAll_noColl] at hp ⊢
  exact noCollJT_col 𝔇.cs 𝔇.G 𝔇.smp 𝔇.ms j i (z, t) y y' (fun x => hy.2 j x hj)
    (noCollJT_state 𝔇.cs 𝔇.G 𝔇.smp 𝔇.ms j i (z, s) (z, t) y (hs z s t h) hp)

/-- A pin goes BACK over the draw. -/
theorem mg_pin_back (hs : ∀ z, TlBlind fun s => 𝔇.smp (z, s)) (base : ℕ) (z : P) (s t : S)
    (y y' : Strs) (w : Wit (CellsQ rows cols) Tok MsgT) (h : Drawn s t) (hy : SameBelow base y y')
    (j i : ℕ) (hj : j < base) (hp : (mgAll 𝔇 mgBase).pin j i (z, t) y' w) :
    (mgAll 𝔇 mgBase).pin j i (z, s) y w := by
  rw [mgAll_pin] at hp ⊢
  exact pinJT_col 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms j i (z, s) y' y w
    (fun x => (hy.2 j x hj).symm)
    (pinJT_state 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms j i (z, t) (z, s) y' w (hs z s t h).symm hp)

end

/-! ## The items that ride past the draw, one sort at a time -/

theorem blind_rows : TlBlind VerifiableInference.Desc.First.S.rows := fun s t h => by
  refine VerifiableInference.Desc.First.K8.drawn_ind (motive := fun s t => t.rows = s.rows)
    ?_ ?_ ?_ h <;> intros <;> simp_all [VerifiableInference.Desc.First.S.rows]

theorem blind_classRows (N : Numbers) (m : ℕ) (c : VerifiableInference.Desc.First.RowClass) :
    TlBlind (VerifiableInference.Desc.First.classRows N m c) := fun s t h => by
  unfold VerifiableInference.Desc.First.classRows
  rw [blind_st s t h, blind_book s t h]

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X)

theorem blind_rw13 (z : P) : TlBlind fun s => 𝔇.rw13 (z, s) := fun s t h => by
  funext w
  show VerifiableInference.Desc.K13.Law.rwBook 𝔇.arr 𝔇.mat13 (z, t) w =
    VerifiableInference.Desc.K13.Law.rwBook 𝔇.arr 𝔇.mat13 (z, s) w
  unfold VerifiableInference.Desc.K13.Law.rwBook
  show (⟨_, _⟩ : VerifiableInference.Desc.K13.Law.Wit _ _ _) = ⟨_, _⟩
  simp only [blind_st s t h, blind_book s t h]

/-- **What the composed meaning's parameters owe for the draw in segment l.** -/
structure MgOwes (l base : ℕ) : Prop where
  decT : ∀ c z, TlBlind fun s => 𝔇.decT c (z, s)
  smp : ∀ z, TlBlind fun s => 𝔇.smp (z, s)
  req : ∀ z, TlBlind fun s => 𝔇.H.req (z, s)
  head : ∀ p i z s t y y' w, Drawn s t → SameBelow base y y' →
    𝔇.headPart p i (z, t) y' w → 𝔇.headPart p i (z, s) y w
  wt : ∀ z s t y y' w, Drawn s t → SameBelow base y y' → 𝔇.wt l (z, t) y' w → 𝔇.wt l (z, s) y w
  readers : ∀ k r, k < pcOf l → ∀ p ∈ 𝔇.runs l k r, TlBlind ((𝔇.Rd l).forms p.1 p.2)
  fence : ∀ x ∈ sampledIn 𝔇.N
    ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[ixOf l]?.getD []),
    x.1 < base

variable {𝔇}

/-- The fence at the index masks' tenant: its pin is open in front of the draw. -/
theorem MgOwes.fenceI {l base : ℕ} (hl : l ≤ 24) (O : MgOwes 𝔇 l base) : 𝔇.N.index.1 < base :=
  O.fence _ (List.mem_flatMap.2 ⟨Item.pinI, (k8_pins_open hl).1, List.mem_singleton.2 rfl⟩)

/-- The fence at the tenants of the segment's first two sendings. -/
theorem MgOwes.fenceS {l base : ℕ} (hl : l ≤ 24) (O : MgOwes 𝔇 l base) (t : ℕ) (x : ℕ × ℕ)
    (hx : x ∈ 𝔇.N.sent l t) (ht : t < 2) : x.1 < base := by
  refine O.fence x (List.mem_flatMap.2 ⟨Item.pin l t, ?_, hx⟩)
  rcases Nat.lt_succ_iff_lt_or_eq.1 ht with h0 | rfl
  · obtain rfl : t = 0 := Nat.lt_one_iff.1 h0
    exact (k8_pins_open hl).2.1
  · exact (k8_pins_open hl).2.2

theorem mg_back {l base : ℕ} (hl : l ≤ 24) (hL : 𝔇.links = linksFull) (O : MgOwes 𝔇 l base)
    (i : Item) (hi : k8ItemSort l i = true) (z : P)
    (s t : S) (y y' : Strs) (w : Wit (CellsQ rows cols) Tok MsgT) (h : Drawn s t)
    (hy : SameBelow base y y') (hp : i.holds 𝔇.N (mgAll 𝔇 mgBase) (z, t) y' w) :
    i.holds 𝔇.N (mgAll 𝔇 mgBase) (z, s) y w := by
  cases i with
  | constr m p =>
    simp only [k8ItemSort, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hi
    have hp' : P5J.constrQAt (VerifiableInference.OnPublicFiles.headLink X) 𝔇.put (oneDec 𝔇.decT 𝔇.H) 𝔇.headPart 𝔇.digitsPart m p
        (z, t) y' w := hp
    show P5J.constrQAt (VerifiableInference.OnPublicFiles.headLink X) 𝔇.put (oneDec 𝔇.decT 𝔇.H) 𝔇.headPart 𝔇.digitsPart m p
        (z, s) y w
    unfold P5J.constrQAt at hp' ⊢
    rw [if_neg hi.2] at hp' ⊢
    refine ⟨hp'.1, fun M j hM hH => ?_⟩
    have e1 : 𝔇.decT y'.cell (z, t) = 𝔇.decT y.cell (z, s) := by
      rw [hy.1]
      exact O.decT y.cell z s t h
    have h2 := hp'.2 M j (e1.trans hM) hH
    have e2 : 𝔇.H.req (z, t) = 𝔇.H.req (z, s) := O.req z s t h
    by_cases hm : m = VerifiableInference.OnPublicFiles.headLink X
    · rw [if_pos hm] at h2 ⊢
      exact O.head p j z s t y y' w h hy h2
    · rw [if_neg hm] at h2 ⊢
      by_cases he : m % 2 = 0
      · rw [if_pos he] at h2 ⊢
        have e3 : (oneDec 𝔇.decT 𝔇.H).req (z, t) = (oneDec 𝔇.decT 𝔇.H).req (z, s) := e2
        rw [← e3]
        exact h2
      · rw [if_neg he] at h2 ⊢
        exact h2
  | pinW =>
    have hp' : pinWOf 𝔇.decT (z, t) y' w := hp
    show pinWOf 𝔇.decT (z, s) y w
    unfold pinWOf at hp' ⊢
    rw [← hp', hy.1]
    exact (O.decT y.cell z s t h).symm
  | pile =>
    have hp' : VerifiableInference.Desc.K13.Law.RowsTrue (𝔇.rw13 (z, t)) t w := hp
    show VerifiableInference.Desc.K13.Law.RowsTrue (𝔇.rw13 (z, s)) s w
    unfold VerifiableInference.Desc.K13.Law.RowsTrue at hp' ⊢
    have e : 𝔇.rw13 (z, t) = 𝔇.rw13 (z, s) := blind_rw13 𝔇 z s t h
    rw [e, blind_rows s t h] at hp'
    exact hp'
  | pinI => exact mg_pin_back 𝔇 O.smp base z s t y y' w h hy _ _ (O.fenceI hl) hp
  | row m c =>
    have hp' : VerifiableInference.Desc.First.rowSays 𝔇.N
        (VerifiableInference.Desc.First.wordsAtFirst 𝔇.arr) m c (z, t) y' w := hp
    show VerifiableInference.Desc.First.rowSays 𝔇.N
        (VerifiableInference.Desc.First.wordsAtFirst 𝔇.arr) m c (z, s) y w
    unfold VerifiableInference.Desc.First.rowSays
      VerifiableInference.Desc.First.wordsAtFirst at hp' ⊢
    simp only [blind_st s t h, blind_book s t h, blind_classRows 𝔇.N m c s t h] at hp'
    exact hp'
  | wo m =>
    have hp' : VerifiableInference.Desc.First.FillP1.woAt 𝔇.d1 𝔇.rw13 m (z, t) y' w := hp
    show VerifiableInference.Desc.First.FillP1.woAt 𝔇.d1 𝔇.rw13 m (z, s) y w
    unfold VerifiableInference.Desc.First.FillP1.woAt at hp' ⊢
    intro r hr
    have e : 𝔇.rw13 (z, t) = 𝔇.rw13 (z, s) := blind_rw13 𝔇 z s t h
    rw [← e]
    refine hp' r ?_
    have e2 : Johnson.Desc.First.Walk.Law.rowAt 𝔇.d1.lay (𝔇.d1.ncl m) 𝔇.d1.lin t =
        Johnson.Desc.First.Walk.Law.rowAt 𝔇.d1.lay (𝔇.d1.ncl m) 𝔇.d1.lin s := by
      unfold Johnson.Desc.First.Walk.Law.rowAt Johnson.Desc.First.Walk.Law.rowBy
      rw [blind_leftOf s t h, blind_out s t h, blind_st s t h]
    exact e2.trans hr
  | forms m k r =>
    simp only [k8ItemSort, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hi
    obtain ⟨rfl, hk⟩ := hi
    have hp' : (∀ p ∈ 𝔇.runs m k r,
        if 𝔇.ah p.1 p.2 = true then
          formsQA (𝔇.N.sent m) (𝔇.N.group m) (𝔇.Rd m) p.1 p.2 t (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w)
        else formsQ (𝔇.Rd m) (𝔇.N.group m) p.1 p.2 t (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w)) ∧
        (r = "weights" → 𝔇.wt m (z, t) y' w) := hp
    show (∀ p ∈ 𝔇.runs m k r,
        if 𝔇.ah p.1 p.2 = true then
          formsQA (𝔇.N.sent m) (𝔇.N.group m) (𝔇.Rd m) p.1 p.2 s (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w)
        else formsQ (𝔇.Rd m) (𝔇.N.group m) p.1 p.2 s (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w)) ∧
        (r = "weights" → 𝔇.wt m (z, s) y w)
    refine ⟨fun p hpm => ?_, fun e => O.wt z s t y y' w h hy (hp'.2 e)⟩
    have hR := O.readers k r hk p hpm
    have ha : 𝔇.ah p.1 p.2 = false := runs_not_ahead hl k r hk p (by
      have hpm' : p ∈ runsAt 𝔇.links m k r := hpm
      rw [hL] at hpm'
      exact hpm')
    have h1 := hp'.1 p hpm
    have hn : ¬ 𝔇.ah p.1 p.2 = true := by rw [ha]; exact Bool.false_ne_true
    rw [if_neg hn] at h1 ⊢
    obtain ⟨a, R, e1, e2, e3, e4⟩ := h1
    refine ⟨a, R, (blind_segAt s t h).symm.trans e1, (hR s t h).symm.trans e2, e3, ?_⟩
    rw [← blind_mergeOf s t h]
    exact e4
  | _ => exact nomatch hi

end

/-! ## The fields on the public items, what rides, what the row reads; and the whole -/

/-- A closed fact: under the table's name (pcOf l, "small") stands the draw's one run. -/
theorem k8RunsB_full : ((List.range 25).all fun l =>
    runsAt linksFull l (pcOf l) "small" == [(pcOf l - 1, "K8.equations")]) = true := by decide

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  {𝔇 : MgData Xi P Tok rows cols nR X}

/-- What the draw must make behind itself, at the composed meaning. -/
def oSMg (𝔇 : MgData Xi P Tok rows cols nR X) (l : ℕ) : P → S → Strs → Prop :=
  fun _ t _ => VerifiableInference.Desc.K9.formsInA (𝔇.Rd l) (𝔇.N.sent l) (𝔇.N.group l)
    (pcOf l - 1) "K8.equations" t = true

theorem mg_new {l : ℕ} (hl : l ≤ 24) (hL : 𝔇.links = linksFull) (z : P) (t : S) (y' : Strs)
    (ho : oSMg 𝔇 l z t y') :
    (mgAll 𝔇 mgBase).pub (.formsIn l (pcOf l) "small") (z, t) = true := by
  have hr := List.all_eq_true.1 k8RunsB_full l (List.mem_range.2 (Nat.lt_succ_of_le hl))
  have hr' : runsAt linksFull l (pcOf l) "small" = [(pcOf l - 1, "K8.equations")] := by
    simpa using hr
  have e : 𝔇.pubD.runs l (pcOf l) "small" = [(pcOf l - 1, "K8.equations")] := by
    show runsAt 𝔇.links l (pcOf l) "small" = _
    rw [hL]
    exact hr'
  have ha : 𝔇.pubD.ah (pcOf l - 1) "K8.equations" = true := by
    show ("K8.equations" == "K8.equations") = true
    decide
  rw [mgAll_pub, VerifiableInference.Desc.First.pubAll_formsIn, e]
  simp only [List.all_cons, List.all_nil, Bool.and_true, ha, if_true]
  exact ho

theorem mg_formsBlind {l base : ℕ} (hl : l ≤ 24) (hL : 𝔇.links = linksFull) (O : MgOwes 𝔇 l base)
    (k : ℕ) (r : String) (hk : k < pcOf l) (p : ℕ × String) (hp : p ∈ 𝔇.pubD.runs l k r) :
    TlBlind fun s => if 𝔇.pubD.ah p.1 p.2 then
        VerifiableInference.Desc.K9.formsInA (𝔇.pubD.Rd l) (𝔇.pubD.N.sent l) (𝔇.pubD.N.group l)
          p.1 p.2 s
      else VerifiableInference.Desc.K9.formsIn (𝔇.pubD.Rd l) (𝔇.pubD.N.group l) p.1 p.2 s := by
  have hR := O.readers k r hk p hp
  have ha' : 𝔇.pubD.ah p.1 p.2 = false := runs_not_ahead hl k r hk p (by
    have hp' : p ∈ runsAt 𝔇.links l k r := hp
    rw [hL] at hp'
    exact hp')
  intro s t h
  simp only [ha', Bool.false_eq_true, if_false]
  exact blind_formsIn (𝔇.Rd l) (𝔇.N.group l) p.1 p.2 hR s t h

end

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  {𝔇 : MgData Xi P Tok rows cols nR X}

/-- The three conjuncts of the kernel's fact on the public items, at a place in hand. -/
theorem k8_pub_full {l : ℕ} (hl : l ≤ 24) {p : VerifiableInference.Desc.Place}
    (hp : (flatPlacesOf linksFull true)[ixOf l]? = some p) :
    (∀ q ∈ (pubSets mgMore linksFull (flatPlacesOf linksFull true))[ixOf l]?.getD [] ++
        pubOfItems ((openSets linksFull (flatPlacesOf linksFull true)
          (start linksFull))[ixOf l]?.getD []), k8Sort l (pcOf l) q = true) ∧
    (∀ q ∈ pubStep ((pubSets mgMore linksFull (flatPlacesOf linksFull true))[ixOf l]?.getD [])
          (pubRowM mgMore linksFull p) ++
        pubOfItems (stepOpen ((openSets linksFull (flatPlacesOf linksFull true)
          (start linksFull))[ixOf l]?.getD []) (rowOf linksFull p)),
      q ∈ (pubSets mgMore linksFull (flatPlacesOf linksFull true))[ixOf l]?.getD [] ++
        pubOfItems ((openSets linksFull (flatPlacesOf linksFull true)
          (start linksFull))[ixOf l]?.getD []) ∨ q = Pub.formsIn l (pcOf l) "small") ∧
    (∀ q ∈ pubStep ((pubSets mgMore linksFull (flatPlacesOf linksFull true))[ixOf l]?.getD [])
          (pubRowM mgMore linksFull p),
      q ∈ (pubSets mgMore linksFull (flatPlacesOf linksFull true))[ixOf l]?.getD []) := by
  have h := List.all_eq_true.1 k8PubB_full l (List.mem_range.2 (Nat.lt_succ_of_le hl))
  unfold k8PubAt at h
  simp only [hp, Bool.and_eq_true] at h
  refine ⟨fun q hq => List.all_eq_true.1 h.1.1 q hq, fun q hq => ?_, fun q hq => ?_⟩
  · have h2 := List.all_eq_true.1 h.1.2 q hq
    simpa using h2
  · have h3 := List.all_eq_true.1 h.2 q hq
    simpa using h3

theorem mg_pub {l base : ℕ} (hl : l ≤ 24) (hL : 𝔇.links = linksFull) (O : MgOwes 𝔇 l base) (z : P)
    (s t : S) (y' : Strs) (p : VerifiableInference.Desc.Place) (h : Drawn s t)
    (hp : (flatPlacesOf linksFull true)[ixOf l]? = some p) (ho : oSMg 𝔇 l z t y')
    (H : pubHeld (mgAll 𝔇 mgBase)
      ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[ixOf l]?.getD [])
      ((pubSets (mgAll 𝔇 mgBase).more linksFull (flatPlacesOf linksFull true))[ixOf l]?.getD [])
      (z, s) = true) :
    pubHeld (mgAll 𝔇 mgBase)
      (stepOpen ((openSets linksFull (flatPlacesOf linksFull true)
        (start linksFull))[ixOf l]?.getD []) (rowOf linksFull p))
      (pubStep ((pubSets (mgAll 𝔇 mgBase).more linksFull
        (flatPlacesOf linksFull true))[ixOf l]?.getD [])
        (pubRowM (mgAll 𝔇 mgBase).more linksFull p)) (z, t) = true := by
  rw [mgAll_more_base] at H ⊢
  obtain ⟨h1, h2, _⟩ := k8_pub_full hl hp
  unfold pubHeld at H ⊢
  refine List.all_eq_true.2 fun q hq => ?_
  rcases h2 q hq with hm | rfl
  · have hb : pubAll 𝔇.pubD (fun _ _ => false) q (z, t) = pubAll 𝔇.pubD (fun _ _ => false) q (z, s) :=
      pubAll_blind 𝔇.pubD l (pcOf l) q (h1 q hm) (fun k r hk p' hp' => mg_formsBlind hl hL O k r hk p' hp')
        z s t h
    have hs : pubAll 𝔇.pubD (fun _ _ => false) q (z, s) = true := List.all_eq_true.1 H q hm
    exact hb.trans hs
  · exact mg_new hl hL z t y' ho

theorem mg_pubP {l : ℕ} (hl : l ≤ 24) (z : P) (s t : S) (p : VerifiableInference.Desc.Place) (h : Drawn s t)
    (hp : (flatPlacesOf linksFull true)[ixOf l]? = some p)
    (H : ∀ q ∈ (pubSets (mgAll 𝔇 mgBase).more linksFull
      (flatPlacesOf linksFull true))[ixOf l]?.getD [], (mgAll 𝔇 mgBase).pubP q (z, s)) :
    ∀ q ∈ pubStep ((pubSets (mgAll 𝔇 mgBase).more linksFull
        (flatPlacesOf linksFull true))[ixOf l]?.getD [])
        (pubRowM (mgAll 𝔇 mgBase).more linksFull p), (mgAll 𝔇 mgBase).pubP q (z, t) := by
  rw [mgAll_more_base] at H ⊢
  obtain ⟨h1, _, h3⟩ := k8_pub_full hl hp
  intro q hq
  have hm := h3 q hq
  have hs := h1 q (List.mem_append_left _ hm)
  have hq' := H q hm
  cases q with
  | leftOn m => exact blind_leftOn X m s t h hq'
  | left m => exact nomatch hs
  | _ => exact hq'

/-- An item that is open in front of the draw and that its row neither closes nor reads is of one
of the riders' sorts. -/
theorem k8_rider_full {l : ℕ} (hl : l ≤ 24) (i : Item)
    (ho : openAfter (insQ linksFull (flatPlacesOf linksFull true))
      (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ start linksFull) (ixOf l) i)
    (hi : ¬ insQ linksFull (flatPlacesOf linksFull true) (ixOf l) i) : k8ItemSort l i = true := by
  obtain ⟨pK, _, eK, _⟩ := k8_step_full hl
  have hk : ixOf l ≤ (flatPlacesOf linksFull true).length :=
    Nat.le_of_lt (List.getElem?_eq_some_iff.1 eK).1
  have ht := tableOkB_full
  rw [Bool.and_eq_true] at ht
  have h1 : i ∈ openL (insL linksFull (flatPlacesOf linksFull true))
      (outsL linksFull (flatPlacesOf linksFull true)) (start linksFull) (ixOf l) :=
    (openIsList Item _ _ (start linksFull) (ixOf l) i).1 ho
  have h2 := (openL_iff_openSets linksFull (flatPlacesOf linksFull true) (start linksFull) ht.1 ht.2
    (by decide) (ixOf l) hk i).1 h1
  have h3 := List.all_eq_true.1 k8RidersB_full l (List.mem_range.2 (Nat.lt_succ_of_le hl))
  unfold k8RidersAt at h3
  refine List.all_eq_true.1 h3 i (List.mem_filter.2 ⟨h2, ?_⟩)
  have hi' : i ∉ insL linksFull (flatPlacesOf linksFull true) (ixOf l) := hi
  simpa using hi'

/-- **THE DRAW's BLINDNESSES AT THE COMPOSED MEANING OVER ITS CLOSED BASE, AT EACH OF THE 25
PLACES**, from what its parameters owe. -/
theorem drawBlind_mg {l base : ℕ} (hl : l ≤ 24) (hL : 𝔇.links = linksFull) (O : MgOwes 𝔇 l base)
    (hT : 𝔇.N.treesAt (flatPlacesOf linksFull true)[ixOf l + 1]? =
      𝔇.N.treesAt (flatPlacesOf linksFull true)[ixOf l]?)
    (hM : 𝔇.N.msgsAt (flatPlacesOf linksFull true)[ixOf l + 1]? =
      𝔇.N.msgsAt (flatPlacesOf linksFull true)[ixOf l]?) :
    DrawBlind 𝔇.N (mgAll 𝔇 mgBase) linksFull (flatPlacesOf linksFull true) (ixOf l) base
      (oSMg 𝔇 l) where
  decodes := fun z s t y y' h hy hp => mg_decodes 𝔇 O.decT base z s t y y' h hy hp
  inOrder := fun z s t _ hp => mg_inOrder 𝔇 z s t hp
  held := fun z s t h x _ hp => mg_held 𝔇 z s t h x.1 x.2 hp
  shown := fun y y' hy x hx hp => mg_shown 𝔇 base y y' hy x.1 x.2 (O.fence x hx) hp
  noColl := fun z s t y y' h hy x hx hp =>
    mg_noColl 𝔇 O.smp base z s t y y' h hy x.1 x.2 (O.fence x hx) hp
  pub := fun z s t y' p h hp _ ho H => mg_pub hl hL O z s t y' p h hp ho H
  pubP := fun z s t _ p h hp _ _ H => mg_pubP hl z s t p h hp H
  rides := fun z s t y y' w i h hy _ _ hall ho hi =>
    mg_back hl hL O i (k8_rider_full hl i ho hi) z s t y y' w h hy (hall i (Or.inl ⟨ho, hi⟩))
  reads := fun z s t y y' w i h hy _ hi hp => by
    rw [(k8_row_full hl).2.2] at hi
    rcases List.mem_cons.1 hi with rfl | hi
    · exact fun x hx => mg_pin_back 𝔇 O.smp base z s t y y' w h hy x.1 x.2
        (O.fenceS hl 0 x hx (by decide)) (hp x hx)
    · obtain rfl := List.mem_singleton.1 hi
      exact fun x hx => mg_pin_back 𝔇 O.smp base z s t y y' w h hy x.1 x.2
        (O.fenceS hl 1 x hx (by decide)) (hp x hx)
  trees := hT
  msgs := hM

end

end P1K8T

#print axioms P1K8T.blind_leftOn
#print axioms P1K8T.mg_back
#print axioms P1K8T.mg_pub
#print axioms P1K8T.mg_pubP
#print axioms P1K8T.k8_rider_full
#print axioms P1K8T.drawBlind_mg
