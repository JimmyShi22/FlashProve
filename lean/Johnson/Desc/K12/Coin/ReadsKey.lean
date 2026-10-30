-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/ReadsKey.lean: the game of the proximity test (the kind K12), first arm, in
the form with a key (`LeadsK`: one game for all the statements with one key) at a piece that holds
the seat as a description holds it. Definitions, statements and proofs.

Why. The rule that takes a description's pieces to the proof file's goal asks of the shared chain's
row a law with a key. `leadsK_of_lift` (Johnson/Desc/Plain/KeyAlone.lean) makes one of a law for one
statement, where the block is lifted, opens no tree of an earlier chain, and the relation is a
function of the two keys. The key (`actAt`, Johnson/Desc/Sound/SharedRule.lean) holds the chain's
own part of the record, the stored table, and the columns of the trees lo ≤ j < hi.
What the game's conclusion reads of the strings: `QN π (NTuple F π no rad rd) (t, y)` reads y in
`W0` alone (Johnson/Desc/K12/Coin/Sheet.lean), and there the columns of the trees number no z alone:
`colIn`'s inner term is the key's third part's.
The one obstacle and the way round. The numbering by labels (`nuOf π nl t`, GameLabels.lean) is read
off the record: at a record with silly labels nl may point outside lo ≤ j < hi. But nl is a letter
bound by `LabelsPub` alone, which speaks of the declared openings' labels only: `nlIn` is `nlAt`
(GameLabelsO.lean) at every declared label and never leaves the range. So the conclusion is a
function of the key at every record, and no yes is wanted.
What it is not, first.
  (1) The first arm alone, at a place all of whose first switch's openings are the chain's own.
  (2) `nlIn` is a tool inside the proofs: the tops stand at `nlAt`. The two numberings are one at
    the members' places wherever the conclusion holds: the conclusion hands on that the plain data
    meet the first switch's clauses, among them that the opened trees' labels are the declared ones
    (`qn_in_iff_at`).
  (3) All that stands first at the heads of GameAt.lean and LawAtTile.lean on the numbering by
    labels and on the errors stands here. No item and no spender is struck.
  (4) The middle clause of the rule's premise (the relation gives the next piece's promise) and the
    relation against the rule's own table are not met here.
  (5) `leadsK_of_leads_key` has no word of the kind in it: its home is beside `leadsK_of_lift`.
Main names.
  `nlIn`, `nlIn_range`, `labelsPub_in`.
  `SameCols`, `sameCols_of_key`, `W0_reads`, `qn_reads`: the conclusion reads the strings at the
    trees lo ≤ j < hi alone.
  `ntuple_no`, `label_in`, `nuOf_in_at`, `qn_in_iff_at`: the conclusion at `nlIn` is the conclusion
    at `nlAt`.
  `QV`, `qv_key`, `qv_in_iff_at`: the game's relation is carried by equal keys.
  `leadsK_of_leads_key`: a piece that holds `held B` and opens no tree below lo: a law for one
    statement whose relation is carried by equal keys is a law with the key.
  `held_sure`: such a piece leaves the held part as it is (`liftKeepsFirst`,
    Johnson/Desc/Sound/LiftRule.lean).
  `gameK_piece`: the game with the key, and the law of keys (`keyLaw_of_held`,
    Johnson/Desc/K12/Law/HeldKey.lean).
  `gameK_at_tile₂`: at the piece number pre.length of the second row of `piecesAt`
    (`tile_piece₂`, LawAtTile.lean); that the piece opens no tree of the first chain is
    `opens_own₂` (Johnson/Desc/K12/Law/OpensOwn.lean).
  `qn_readsM`: `qn_reads` where the members' trees alone have their numbers in the range.
    `leadsK_of_leads_keyOn`: `leadsK_of_leads_key` at any condition in front. `gameK_piece_le`,
    `gameK_at_tile₂_le`: the game with the key at every list of errors that is at least the law's
    own, round by round: so at whatever the tiling's family lays at the piece.
  `Rides`, `strs_ride`, `allOf_nodup`, `gameK_at_tile₂_ride`: a yes leaves the stored table's
    strings and every tree below the piece's base as they are: laid beside the game's relation, for
    certain.
  `atDesc_row₂`: the rule's pieces are those of `piecesAt`. `gameK_at_tile₂_cap`: where the family
    lays the cap at every piece: no premise on the errors is left; the law with the key and the law
    for a batch at every number of slots, at the cap.
Limits: those of the files called. No soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Coin.LawAtTile
import Johnson.Desc.K12.Law.HeldKey
import Johnson.Desc.K12.Law.OpensOwn
import Johnson.Desc.Sound.RunIsDecide
import Johnson.Desc.Sound.BoundsAtCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pub (johOk batV0 batPriceOk)
open H2K.JointK (keyLaw_of_held leadsK_of_held opens_own₂)
open Johnson.G.OfPlan (rootsOf)
open scoped ENNReal
open H2K.Member (numAt_own)
open H2K.First (opensOf gpL Plain good_of_ok made_of keyAt)
open H2K.JointK (WO)
open H2K.Pin (NTuple)

/-! ## A numbering of the labels that never leaves the range -/

/-- From a label to a tree's number through the file, at a chain whose trees begin at lo: never out
of lo ≤ j < lo + free. -/
def nlIn (π : P12) (lo ℓ : ℕ) : ℕ := lo + min (ℓ - π.nums.firstTree) (π.nums.free - 1)

theorem nlIn_range (π : P12) (lo ℓ : ℕ) (hf : 0 < π.nums.free) :
    lo ≤ nlIn π lo ℓ ∧ nlIn π lo ℓ < lo + π.nums.free := by
  unfold nlIn
  omega

theorem labelsPub_in (π : P12) (ch t₁ t₂ : ℕ) (h : ownLabelsFreeB π = true) :
    LabelsPub π (numAt t₁ t₂ ch) (nlIn π (numAt t₁ t₂ ch (.own 0))) (baseAt t₁ t₂ ch π) := by
  intro a rest hs o ho
  unfold ownLabelsFreeB at h
  rw [hs] at h
  have h1 := List.all_eq_true.1 h o ho
  obtain ⟨sh, src⟩ := o
  cases src with
  | taken c s => simp at h1
  | own n =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    obtain ⟨e1, e2⟩ := h1
    refine ⟨?_, ?_⟩
    · show numAt t₁ t₂ ch (.own n) = nlIn π (numAt t₁ t₂ ch (.own 0)) sh.tree
      unfold nlIn
      rw [e1, numAt_own, numAt_own]
      omega
    · show numAt t₁ t₂ ch (.own n) < numAt t₁ t₂ ch (.own π.nums.free)
      rw [numAt_own, numAt_own]
      omega

/-! ## What the conclusion reads of the strings -/

/-- Two lists of strings show the same columns at the trees lo ≤ j < hi. -/
def SameCols (F : Frame) (lo hi : ℕ) (y y' : F.E.Str) : Prop :=
  ∀ j x, lo ≤ j → j < hi → (posL F.all j x).map y.2 = (posL F.all j x).map y'.2

theorem sameCols_of_key {S S₀ : Type} (F : Frame) (get : S → S₀) (lo hi : ℕ)
    (a a' : S × F.E.Str) (h : (actAt F get lo hi).2 a = (actAt F get lo hi).2 a') :
    get a.1 = get a'.1 ∧ SameCols F lo hi a.2 a'.2 := by
  have h' : (get a.1, a.2.1,
      fun j x => if lo ≤ j ∧ j < hi then (posL F.all j x).map a.2.2 else none) =
      (get a'.1, a'.2.1,
        fun j x => if lo ≤ j ∧ j < hi then (posL F.all j x).map a'.2.2 else none) := h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h'
  obtain ⟨_, h3⟩ := Prod.mk.inj h2
  refine ⟨h1, fun j x hl hh => ?_⟩
  have e := congrFun (congrFun h3 j) x
  dsimp only at e
  rw [if_pos ⟨hl, hh⟩, if_pos ⟨hl, hh⟩] at e
  exact e

theorem W0_reads (F : Frame) (no : ℕ → ℕ) (book : TreeBook) (y y' : F.E.Str) (z lo hi : ℕ)
    (hz : lo ≤ no z ∧ no z < hi) (h : SameCols F lo hi y y') :
    W0 F no book y z = W0 F no book y' z := by
  have hc : ∀ x, colIn F y (no z) x = colIn F y' (no z) x := fun x => by
    unfold colIn
    rw [h (no z) x hz.1 hz.2]
  unfold W0 woIn
  simp only [hc]

/-- **The conclusion reads the strings at the trees lo ≤ j < hi alone.** -/
theorem qn_reads (F : Frame) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (lo hi : ℕ)
    (hno : ∀ z, lo ≤ no z ∧ no z < hi) (t : T12) (y y' : F.E.Str) (h : SameCols F lo hi y y')
    (hq : QN π (NTuple F π no rad rd) (t, y)) : QN π (NTuple F π no rad rd) (t, y') := by
  obtain ⟨a, rest, G0, Ly, D, hf, row₀, hok, hT⟩ := hq
  refine ⟨a, rest, G0, Ly, D, hf, row₀, hok, ?_⟩
  have hW : W0 F no D.book y' = W0 F no D.book y :=
    funext fun z => (W0_reads F no D.book y y' z lo hi (hno z) h).symm
  dsimp only at hT ⊢
  rw [hW]
  exact hT

/-- **The conclusion reads the strings at the trees lo ≤ j < hi alone**, where the members' trees
have their numbers there. Of the mask's tree it reads the round's shape alone: no string. -/
theorem qn_readsM (F : Frame) (π : P12) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (lo hi : ℕ)
    (t : T12)
    (hno : ∀ a rest G0 Ly D, Fixes π t a rest G0 Ly D → ∀ i : Fin D.mems.length,
      lo ≤ no (D.mems.get i).t ∧ no (D.mems.get i).t < hi)
    (y y' : F.E.Str) (h : SameCols F lo hi y y')
    (hq : QN π (NTuple F π no rad rd) (t, y)) : QN π (NTuple F π no rad rd) (t, y') := by
  obtain ⟨a, rest, G0, Ly, D, hf, row₀, hok, hT⟩ := hq
  refine ⟨a, rest, G0, Ly, D, hf, row₀, hok, ?_⟩
  have e1 : ∀ i, W0 F no D.book y (D.mems.get i).t = W0 F no D.book y' (D.mems.get i).t :=
    fun i => W0_reads F no D.book y y' _ lo hi (hno a rest G0 Ly D hf i) h
  have key : ∀ (wM wM' : Fin D.mems.length → WO), wM = wM' →
      H2K.Pin.TupleAt (good_of_ok π a row₀ D hok)
        { t with st := begun t.st t.g G0, pass := .claim row₀ Ly } Ly t.st G0 rd
        (fun i => (wM i).1) (W0 F no D.book y D.fresh.t).1 (fun i => (wM i).2)
        (rad (H2K.Pub.sgOf a)) →
      H2K.Pin.TupleAt (good_of_ok π a row₀ D hok)
        { t with st := begun t.st t.g G0, pass := .claim row₀ Ly } Ly t.st G0 rd
        (fun i => (wM' i).1) (W0 F no D.book y D.fresh.t).1 (fun i => (wM' i).2)
        (rad (H2K.Pub.sgOf a)) := by
    rintro _ _ rfl h'
    exact h'
  exact key (fun i => W0 F no D.book y (D.mems.get i).t)
    (fun i => W0 F no D.book y' (D.mems.get i).t) (funext e1) hT

/-! ## The two numberings are one wherever the conclusion holds -/

/-- "One tuple for all rows" reads a numbering at the members' places alone. (`ntuple_congr`,
Johnson/Desc/K12/Coin/LabelsToPlaces.lean, asks the mask's place too.) -/
theorem ntuple_no (F : Frame) (π : P12) (no no' : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (x : T12 × F.E.Str) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (G0 : Group)
    (Ly : GroupLayout) (D : Plain) (h1 : ∀ i, no (D.mems.get i).t = no' (D.mems.get i).t)
    (h : NTuple F π no rad rd x a rest G0 Ly D) : NTuple F π no' rad rd x a rest G0 Ly D := by
  have e1 : ∀ i, W0 F no D.book x.2 (D.mems.get i).t = W0 F no' D.book x.2 (D.mems.get i).t := by
    intro i
    unfold W0
    rw [h1 i]
  obtain ⟨row₀, hok, hT⟩ := h
  refine ⟨row₀, hok, ?_⟩
  have key : ∀ (wM wM' : Fin D.mems.length → WO), wM = wM' →
      H2K.Pin.TupleAt (good_of_ok π a row₀ D hok)
        { x.1 with st := begun x.1.st x.1.g G0, pass := .claim row₀ Ly } Ly x.1.st G0 rd
        (fun i => (wM i).1) (W0 F no D.book x.2 D.fresh.t).1 (fun i => (wM i).2)
        (rad (H2K.Pub.sgOf a)) →
      H2K.Pin.TupleAt (good_of_ok π a row₀ D hok)
        { x.1 with st := begun x.1.st x.1.g G0, pass := .claim row₀ Ly } Ly x.1.st G0 rd
        (fun i => (wM' i).1) (W0 F no D.book x.2 D.fresh.t).1 (fun i => (wM' i).2)
        (rad (H2K.Pub.sgOf a)) := by
    rintro _ _ rfl h'
    exact h'
  exact key (fun i => W0 F no D.book x.2 (D.mems.get i).t)
    (fun i => W0 F no' D.book x.2 (D.mems.get i).t) (funext e1) hT

/-- Where the plain data meet the first switch's clauses, the label of every tree that the switch
opens is firstTree + n with n < free. -/
theorem label_in (π : P12) (hlb : ownLabelsFreeB π = true) {t : T12} {a : Fmt.M1.Stage}
    {rest : List Fmt.M1.Stage} {G0 : Group} {Ly : GroupLayout} {D : Plain}
    (hf : Fixes π t a rest G0 Ly D) (row₀ : GroupRow)
    (hok : H2K.First.ok (gpL π a row₀ D) = true) (z : ℕ) (hz : z ∈ D.ts) :
    H2K.First.numAt D.book z - π.nums.firstTree < π.nums.free := by
  have hk := (good_of_ok π a row₀ D hok).keys
  have hm := made_of π _ a Ly D (hf.2.2.2 row₀)
  have h1 : keyAt π.nums.firstTree D.book z ∈ D.ts.map (keyAt π.nums.firstTree D.book) :=
    List.mem_map.2 ⟨z, hz, rfl⟩
  rw [← hk] at h1
  obtain ⟨o, ho, e⟩ := List.mem_map.1 h1
  rw [hm.opens] at ho
  unfold ownLabelsFreeB at hlb
  rw [hf.1] at hlb
  have h2 := List.all_eq_true.1 hlb o ho
  obtain ⟨sh, src⟩ := o
  cases src with
  | taken c s => simp at h2
  | own n =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h2
    obtain ⟨e1, e2⟩ := h2
    have e' : sh.tree - π.nums.firstTree = H2K.First.numAt D.book z - π.nums.firstTree := e
    rw [e1] at e'
    omega

theorem nuOf_in_at (π : P12) (lo : ℕ) (hlb : ownLabelsFreeB π = true) {t : T12}
    {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : Group} {Ly : GroupLayout} {D : Plain}
    (hf : Fixes π t a rest G0 Ly D) (row₀ : GroupRow)
    (hok : H2K.First.ok (gpL π a row₀ D) = true) (i : Fin D.mems.length) :
    nuOf π (nlIn π lo) t (D.mems.get i).t = nuOf π (nlAt π lo) t (D.mems.get i).t := by
  have hm := made_of π _ a Ly D (hf.2.2.2 row₀)
  have hz : (D.mems.get i).t ∈ D.ts := by
    rw [hm.ts]
    refine (Fmt.listOf_mem _ _).2 (List.mem_append_left _ ?_)
    exact List.mem_map.2 ⟨D.mems.get i, List.get_mem _ _, rfl⟩
  have h1 := label_in π hlb hf row₀ hok _ hz
  rw [nuOf_of_fixes hf, nuOf_of_fixes hf]
  unfold nlIn nlAt
  omega

/-- **The conclusion at `nlIn` is the conclusion at `nlAt`.** -/
theorem qn_in_iff_at (F : Frame) (π : P12) (lo : ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (hlb : ownLabelsFreeB π = true) (x : T12 × F.E.Str) :
    QN π (NTuple F π (nuOf π (nlIn π lo) x.1) rad rd) x ↔
      QN π (NTuple F π (nuOf π (nlAt π lo) x.1) rad rd) x := by
  constructor
  · rintro ⟨a, rest, G0, Ly, D, hf, hN⟩
    obtain ⟨row₀, hok, _⟩ := id hN
    exact ⟨a, rest, G0, Ly, D, hf, ntuple_no F π _ _ rad rd x a rest G0 Ly D
      (fun i => nuOf_in_at π lo hlb hf row₀ hok i) hN⟩
  · rintro ⟨a, rest, G0, Ly, D, hf, hN⟩
    obtain ⟨row₀, hok, _⟩ := id hN
    exact ⟨a, rest, G0, Ly, D, hf, ntuple_no F π _ _ rad rd x a rest G0 Ly D
      (fun i => (nuOf_in_at π lo hlb hf row₀ hok i).symm) hN⟩

/-! ## The game's relation and the keys -/

/-- The game's relation, without the clause on the held part. -/
def QV {P S : Type} (F : Frame) (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rd : ℕ → ℕ)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (a b : (P × S) × F.E.Str) : Prop :=
  ∃ t t', enter a.1.2 = .ok t ∧ leave a.1.2 t' = .ok b.1.2 ∧
    QN π (NTuple F π (nuOf π nl t) (fun s => r s.st) rd) (t, a.2)

theorem qv_key {P S : Type} (F : Frame) (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ)
    (rd : ℕ → ℕ) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (lo hi hi' : ℕ) (hnl : ∀ ℓ, lo ≤ nl ℓ ∧ nl ℓ < hi) (a a' b b' : (P × S) × F.E.Str)
    (ha : (actAt F (Prod.snd : P × S → S) lo hi).2 a = (actAt F (Prod.snd : P × S → S) lo hi).2 a')
    (hb : (actAt F (Prod.snd : P × S → S) lo hi').2 b =
      (actAt F (Prod.snd : P × S → S) lo hi').2 b')
    (hq : QV F π nl r rd enter leave a b) : QV F π nl r rd enter leave a' b' := by
  obtain ⟨ea, hs⟩ := sameCols_of_key F Prod.snd lo hi a a' ha
  obtain ⟨eb, _⟩ := sameCols_of_key F Prod.snd lo hi' b b' hb
  obtain ⟨t, t', h1, h2, h3⟩ := hq
  have ea' : a.1.2 = a'.1.2 := ea
  have eb' : b.1.2 = b'.1.2 := eb
  refine ⟨t, t', ?_, ?_, qn_reads F π _ _ rd lo hi (fun _ => hnl _) t a.2 a'.2 hs h3⟩
  · rw [← ea']
    exact h1
  · rw [← ea', ← eb']
    exact h2

theorem qv_in_iff_at {P S : Type} (F : Frame) (π : P12) (lo : ℕ) (r : Fmt.M1.Stage → ℕ)
    (rd : ℕ → ℕ) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (hlb : ownLabelsFreeB π = true) (a b : (P × S) × F.E.Str) :
    QV F π (nlIn π lo) r rd enter leave a b ↔ QV F π (nlAt π lo) r rd enter leave a b := by
  constructor
  · rintro ⟨t, t', h1, h2, h3⟩
    exact ⟨t, t', h1, h2, (qn_in_iff_at F π lo _ rd hlb (t, a.2)).1 h3⟩
  · rintro ⟨t, t', h1, h2, h3⟩
    exact ⟨t, t', h1, h2, (qn_in_iff_at F π lo _ rd hlb (t, a.2)).2 h3⟩

section
variable {P S Cl W : Type} {C : PQ.CK} {F : Frame}

/-- **A law for one statement whose relation is carried by equal keys is a law with the key**, at a
piece that holds `held B` and opens no tree below lo. -/
theorem leadsK_of_leads_key (p : Piece C F (P × S) Cl W) (B : Block S Cl) (hb : p.b = held B)
    (lo : ℕ) (ho : ∀ d ∈ p.ds, ∀ j ∈ d.opens, lo ≤ j)
    (Q : (P × S) × F.E.Str → (P × S) × F.E.Str → Prop)
    (hQ : ∀ a a' b b', (actAt F (Prod.snd : P × S → S) lo p.base).2 a =
        (actAt F (Prod.snd : P × S → S) lo p.base).2 a' →
      (actAt F (Prod.snd : P × S → S) lo (p.base + p.trees)).2 b =
        (actAt F (Prod.snd : P × S → S) lo (p.base + p.trees)).2 b' → Q a b → Q a' b')
    (h : p.ior.red.Leads (fun _ => True) Q p.err) :
    p.ior.red.LeadsK (actAt F (Prod.snd : P × S → S) lo p.base).2 (fun _ => True) Q p.err := by
  have h1 : p.ior.red.Leads (fun _ => True)
      (fun a b => (fun κ κ' => ∃ a₀ b₀, (actAt F (Prod.snd : P × S → S) lo p.base).2 a₀ = κ ∧
          (actAt F (Prod.snd : P × S → S) lo (p.base + p.trees)).2 b₀ = κ' ∧ Q a₀ b₀)
        ((actAt F (Prod.snd : P × S → S) lo p.base).2 a)
        ((actAt F (Prod.snd : P × S → S) lo (p.base + p.trees)).2 b)) p.err :=
    h.conseq (fun _ x => x) fun a _ b _ _ hq => ⟨a, b, rfl, rfl, hq⟩
  have h2 := leadsK_of_held p B lo hb ho (fun _ => True)
    (fun κ κ' => ∃ a₀ b₀, (actAt F (Prod.snd : P × S → S) lo p.base).2 a₀ = κ ∧
      (actAt F (Prod.snd : P × S → S) lo (p.base + p.trees)).2 b₀ = κ' ∧ Q a₀ b₀) h1
  exact h2.conseq (fun _ x => x) fun a _ b _ _ hq => by
    obtain ⟨a₀, b₀, ea, eb, hq₀⟩ := hq
    exact hQ a₀ a b₀ b ea eb hq₀

/-- **A law for one statement whose relation is carried by equal keys is a law with the key**, at a
piece that holds `held B` and opens no tree below lo; at any condition in front. -/
theorem leadsK_of_leads_keyOn (p : Piece C F (P × S) Cl W) (B : Block S Cl) (hb : p.b = held B)
    (lo : ℕ) (ho : ∀ d ∈ p.ds, ∀ j ∈ d.opens, lo ≤ j) (on : (P × S) × F.E.Str → Prop)
    (Q : (P × S) × F.E.Str → (P × S) × F.E.Str → Prop)
    (hQ : ∀ a a' b b', (actAt F (Prod.snd : P × S → S) lo p.base).2 a =
        (actAt F (Prod.snd : P × S → S) lo p.base).2 a' →
      (actAt F (Prod.snd : P × S → S) lo (p.base + p.trees)).2 b =
        (actAt F (Prod.snd : P × S → S) lo (p.base + p.trees)).2 b' →
      on a → on a' → Q a b → Q a' b')
    (h : p.ior.red.Leads on Q p.err) :
    p.ior.red.LeadsK (actAt F (Prod.snd : P × S → S) lo p.base).2 on Q p.err := by
  have h1 : p.ior.red.Leads on
      (fun a b => (fun κ κ' => ∃ a₀ b₀, (actAt F (Prod.snd : P × S → S) lo p.base).2 a₀ = κ ∧
          (actAt F (Prod.snd : P × S → S) lo (p.base + p.trees)).2 b₀ = κ' ∧ on a₀ ∧ Q a₀ b₀)
        ((actAt F (Prod.snd : P × S → S) lo p.base).2 a)
        ((actAt F (Prod.snd : P × S → S) lo (p.base + p.trees)).2 b)) p.err :=
    h.conseq (fun _ x => x) fun a _ b ha _ hq => ⟨a, b, rfl, rfl, ha, hq⟩
  have h2 := leadsK_of_held p B lo hb ho on
    (fun κ κ' => ∃ a₀ b₀, (actAt F (Prod.snd : P × S → S) lo p.base).2 a₀ = κ ∧
      (actAt F (Prod.snd : P × S → S) lo (p.base + p.trees)).2 b₀ = κ' ∧ on a₀ ∧ Q a₀ b₀) h1
  exact h2.conseq (fun _ x => x) fun a _ b ha _ hq => by
    obtain ⟨a₀, b₀, ea, eb, ha₀, hq₀⟩ := hq
    exact hQ a₀ a b₀ b ea eb ha₀ ha hq₀

/-- «At most», along an equation of stretches. -/
theorem le_of_heq {ds ds' : List RDT} (h : ds = ds') (ε₀ ε₁ : Err (uLT C ds))
    (ε₀' ε₁' : Err (uLT C ds')) (h0 : HEq ε₀ ε₀') (h1 : HEq ε₁ ε₁') (hle : Err.le ε₀' ε₁') :
    Err.le ε₀ ε₁ := by
  subst h
  rw [eq_of_heq h0, eq_of_heq h1]
  exact hle

/-- Such a piece leaves the held part as it is. -/
theorem held_sure (p : Piece C F (P × S) Cl W) (B : Block S Cl) (hb : p.b = held B)
    (a b : (P × S) × F.E.Str) (τ : Iop.Tr (uLT C p.ds)) (h : p.ior.red.out a τ = some b) :
    b.1 = (a.1.1, b.1.2) := by
  obtain ⟨pb, pbase, pds, pback, pext, perr⟩ := p
  dsimp only at hb
  subst hb
  have h' : ((⟨below B, pbase, pds, pback, fun _ _ w => w, perr⟩ : Piece C F S Cl W).lift Prod.snd
      fun (t : P × S) s => (t.1, s)).ior.red.out a τ = some b := h
  exact Prod.ext (liftKeepsFirst P S Cl W C F
    (⟨below B, pbase, pds, pback, fun _ _ w => w, perr⟩ : Piece C F S Cl W) a b τ h') rfl

end

/-! ## The game with the key -/

/-- **At any piece that holds the seat's entry as a description holds it.** lo: the number of the
chain's first own tree. -/
theorem gameK_piece (P S Cl' : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (ch t₁ t₂ : ℕ)
    (rd : ℕ → ℕ) (dB : RDT) (dt : List RDT) (e : ℕ) (εt : Err (uLT (ckP .two) dt))
    (r : Fmt.M1.Stage → ℕ) (p : Piece (ckP .two) F (P × S) Cl' W) (B : Block S Cl')
    (hb : p.b = held B) (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) B)
    (h0 : p.back = []) (hbase : p.base = baseAt t₁ t₂ ch π) (hds : p.ds = dB :: dt)
    (herr : HEq p.err ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
    (hA : AtPlace F π (numAt t₁ t₂ ch) Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st)
      (baseAt t₁ t₂ ch π) dB dt εt)
    (hj : johOk π r = true) (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e)
    (hlb : ownLabelsFreeB π = true) (hf : 0 < π.nums.free) (lo : ℕ)
    (hlo : numAt t₁ t₂ ch (.own 0) = lo) (ho : ∀ d ∈ p.ds, ∀ j ∈ d.opens, lo ≤ j) :
    p.ior.red.LeadsK (actAt F (Prod.snd : P × S → S) lo p.base).2 (fun _ => True)
        (fun a b => QV F π (nlAt π lo) r rd enter leave a b ∧ b.1 = (a.1.1, b.1.2)) p.err ∧
      p.ior.red.KeyLaw (actAt F (Prod.snd : P × S → S) lo p.base).2
        (actAt F (Prod.snd : P × S → S) lo (p.base + p.trees)).2 := by
  subst hlo
  have hL := k12_game_alikeV P S Cl' enter leave F W π (numAt t₁ t₂ ch)
    (nlAt π (numAt t₁ t₂ ch (.own 0))) Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st) rd
    (baseAt t₁ t₂ ch π) dB dt e εt r p (by rw [hb]; exact hal.held) h0 hbase hds herr hA
    (fun _ => rfl) hj (H2K.Made.batOneOk_of_planOk guardedProximityTestParts π hA.planOk) hle
    (labelsPub_own π ch t₁ t₂ hlb)
  have hL' : p.ior.red.Leads (fun _ => True)
      (QV F π (nlAt π (numAt t₁ t₂ ch (.own 0))) r rd enter leave) p.err :=
    hL.conseq (fun _ x => x) fun _ _ _ _ _ hq => hq.1
  have hnl : ∀ ℓ, numAt t₁ t₂ ch (.own 0) ≤ nlIn π (numAt t₁ t₂ ch (.own 0)) ℓ ∧
      nlIn π (numAt t₁ t₂ ch (.own 0)) ℓ < p.base := by
    intro ℓ
    have h1 := nlIn_range π (numAt t₁ t₂ ch (.own 0)) ℓ hf
    have h2 : p.base = numAt t₁ t₂ ch (.own 0) + π.nums.free := by
      rw [hbase]
      show numAt t₁ t₂ ch (.own π.nums.free) = _
      rw [numAt_own, numAt_own]
      omega
    rw [h2]
    exact h1
  have hK := leadsK_of_leads_key p B hb (numAt t₁ t₂ ch (.own 0)) ho _
    (fun a a' b b' ha hb' hq => (qv_in_iff_at F π _ r rd enter leave hlb a' b').1
      (qv_key F π _ r rd enter leave _ _ _ hnl a a' b b' ha hb'
        ((qv_in_iff_at F π _ r rd enter leave hlb a b).2 hq))) hL'
  exact ⟨hK.beside_sure _ fun a τ b _ hout => held_sure p B hb a b τ hout,
    keyLaw_of_held p B _ hb ho⟩

/-- **AT THE SHARED CHAIN's PIECE NUMBER pre.length OF `piecesAt`**: the game with the key, the law
of keys, and the whole entry of errors below 2⁻¹ ^ k. That the family's errors at that number are
"BAT"'s count times the sampler's number and the place's own errors is a premise (`herr`). -/
theorem gameK_at_tile₂ {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber)
        ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (π : P12) (r : Fmt.M1.Stage → ℕ) (k : ℕ)
    (enter : F.S₂ → Except String T12) (leave : F.S₂ → T12 → Except String F.S₂)
    (pre : List (Block F.S₂ F.Cl)) (B b' : Block F.S₂ F.Cl) (post : List (Block F.S₂ F.Cl))
    (hfl : F.shared.blocksInOrder = b₂ :: l₂) (hcut : b₂ :: l₂ = pre ++ B :: b' :: post)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) B)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ k)) (hj : johOk π r = true)
    (hbat : batPriceOk π r k = true) (ho : π.nums.ownMask = false)
    (hlb : ownLabelsFreeB π = true) (hf : 0 < π.nums.free) (rd : ℕ → ℕ)
    (herr : ∀ dB dt, (D.ds₂.drop (pre.flatMap (·.rounds)).length).take
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt →
      ∀ ds', ds' = dB :: dt → HEq (rest₂ (0 + pre.length) ds').err
        ((batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) :
          Err (uLT (ckP .two) (dB :: dt)))) :
    ∃ p dB dt,
      ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂)[pre.length]? =
        some p ∧
      p.b = held B ∧
      p.base = D.t₁ + nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length) ∧ p.ds = dB :: dt ∧
      HEq p.err ((batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) :
        Err (uLT (ckP .two) (dB :: dt))) ∧
      Err.Below (s := uLT (ckP .two) (dB :: dt))
        (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) ((2 : ℝ≥0∞)⁻¹ ^ k) ∧
      p.ior.red.LeadsK
        (actAt (frameAt D (allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2 (fun _ => True)
        (fun a b => QV (frameAt D (allOf D) D.key₂ 0) π (nlAt π F.t₁) r rd enter leave a b ∧
          b.1 = (a.1.1, b.1.2)) p.err ∧
      p.ior.red.KeyLaw
        (actAt (frameAt D (allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2
        (actAt (frameAt D (allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          (p.base + p.trees)).2 := by
  obtain ⟨p, dB, dt, hrow, hpb, hp0, hpbase, hpds, hlist, hperr, hb0, _, hAt, hsm⟩ :=
    tile_piece₂ F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r k pre B b' post hfl hcut
      hal.rounds hfree hp hC hj hbat ho
  have hho : ∀ x ∈ p.ds, ∀ j ∈ x.opens, F.t₁ ≤ j := by
    intro x hx
    rw [hpds, ← hlist] at hx
    exact opens_own₂ F file D h x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have hA' : AtPlace (frameAt D (allOf D) D.key₂ 0) π (numAt F.t₁ F.t₂ 1) Sg.lstJ Sg.flC Sg.flZ
      Sg.flZ (fun s => r s.st) (baseAt F.t₁ F.t₂ 1 π) dB dt (errJ π r dt) := by
    rw [← hb0]
    exact hAt
  obtain ⟨hK, hLaw⟩ := gameK_piece (F.XiPub × F.S₁) F.S₂ F.Cl enter leave _ W π 1 F.t₁ F.t₂ rd dB
    dt _ (errJ π r dt) r p B hpb hal hp0 (hpbase.trans hb0) hpds (hperr _ (herr dB dt hlist)) hA'
    hj (Nat.le_refl _) hlb hf F.t₁ (by simp [numAt]) hho
  exact ⟨p, dB, dt, hrow, hpb, hpbase, hpds, hperr _ (herr dB dt hlist), hsm, hK, hLaw⟩

/-- **The same at every greater list of errors**: the piece's own errors need only be at least
(e, εt), round by round. -/
theorem gameK_piece_le (P S Cl' : Type) (enter : S → Except String T12)
    (leave : S → T12 → Except String S) (F : Frame) (W : Type) (π : P12) (ch t₁ t₂ : ℕ)
    (rd : ℕ → ℕ) (dB : RDT) (dt : List RDT) (e : ℕ) (εt : Err (uLT (ckP .two) dt))
    (r : Fmt.M1.Stage → ℕ) (p : Piece (ckP .two) F (P × S) Cl' W) (B : Block S Cl')
    (hb : p.b = held B) (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) B)
    (h0 : p.back = []) (hbase : p.base = baseAt t₁ t₂ ch π) (hds : p.ds = dB :: dt)
    (hε : ∀ ε₀ : Err (uLT (ckP .two) p.ds),
      HEq ε₀ ((e, εt) : Err (uLT (ckP .two) (dB :: dt))) → Err.le ε₀ p.err)
    (hA : AtPlace F π (numAt t₁ t₂ ch) Sg.lstJ Sg.flC Sg.flZ Sg.flZ (fun s => r s.st)
      (baseAt t₁ t₂ ch π) dB dt εt)
    (hj : johOk π r = true) (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e)
    (hlb : ownLabelsFreeB π = true) (hf : 0 < π.nums.free) (lo : ℕ)
    (hlo : numAt t₁ t₂ ch (.own 0) = lo) (ho : ∀ d ∈ p.ds, ∀ j ∈ d.opens, lo ≤ j) :
    p.ior.red.LeadsK (actAt F (Prod.snd : P × S → S) lo p.base).2 (fun _ => True)
        (fun a b => QV F π (nlAt π lo) r rd enter leave a b ∧ b.1 = (a.1.1, b.1.2)) p.err ∧
      p.ior.red.KeyLaw (actAt F (Prod.snd : P × S → S) lo p.base).2
        (actAt F (Prod.snd : P × S → S) lo (p.base + p.trees)).2 := by
  obtain ⟨pb, pbase, pds, pback, pext, perr⟩ := p
  dsimp only at hb h0 hbase hds hε ho
  subst hds
  have h := gameK_piece P S Cl' enter leave F W π ch t₁ t₂ rd dB dt e εt r
    (⟨pb, pbase, dB :: dt, pback, pext, (e, εt)⟩ : Piece (ckP .two) F (P × S) Cl' W) B hb hal h0
    hbase rfl HEq.rfl hA hj hle hlb hf lo hlo ho
  exact ⟨h.1.mono_err (hε _ HEq.rfl), h.2⟩

/-- **At that piece, WHATEVER the family of extractors and errors lays there**, if only its errors
are at least "BAT"'s count times the sampler's number and the place's own errors, round by round
(`herr`); and that pair is below 2⁻¹ ^ k. Where the family lays the cap (`Err.cap k`), `herr` is
`Err.le_cap_of_below_inv` (Iop/ErrCap.lean) of that. -/
theorem gameK_at_tile₂_le {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber)
        ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (π : P12) (r : Fmt.M1.Stage → ℕ) (k : ℕ)
    (enter : F.S₂ → Except String T12) (leave : F.S₂ → T12 → Except String F.S₂)
    (pre : List (Block F.S₂ F.Cl)) (B b' : Block F.S₂ F.Cl) (post : List (Block F.S₂ F.Cl))
    (hfl : F.shared.blocksInOrder = b₂ :: l₂) (hcut : b₂ :: l₂ = pre ++ B :: b' :: post)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) B)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ k)) (hj : johOk π r = true)
    (hbat : batPriceOk π r k = true) (ho : π.nums.ownMask = false)
    (hlb : ownLabelsFreeB π = true) (hf : 0 < π.nums.free) (rd : ℕ → ℕ)
    (herr : ∀ dB dt, (D.ds₂.drop (pre.flatMap (·.rounds)).length).take
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt →
      Err.le (s := uLT (ckP .two) (dB :: dt))
        (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt)
        (rest₂ (0 + pre.length) (dB :: dt)).err) :
    ∃ p dB dt,
      ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂)[pre.length]? =
        some p ∧
      p.b = held B ∧
      p.base = D.t₁ + nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length) ∧ p.ds = dB :: dt ∧
      HEq p.err (rest₂ (0 + pre.length) (dB :: dt)).err ∧
      Err.Below (s := uLT (ckP .two) (dB :: dt))
        (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) ((2 : ℝ≥0∞)⁻¹ ^ k) ∧
      p.ior.red.LeadsK
        (actAt (frameAt D (allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2 (fun _ => True)
        (fun a b => QV (frameAt D (allOf D) D.key₂ 0) π (nlAt π F.t₁) r rd enter leave a b ∧
          b.1 = (a.1.1, b.1.2)) p.err ∧
      p.ior.red.KeyLaw
        (actAt (frameAt D (allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2
        (actAt (frameAt D (allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          (p.base + p.trees)).2 := by
  obtain ⟨p, dB, dt, hrow, hpb, hp0, hpbase, hpds, hlist, hperr, hb0, _, hAt, hsm⟩ :=
    tile_piece₂ F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r k pre B b' post hfl hcut
      hal.rounds hfree hp hC hj hbat ho
  have hho : ∀ x ∈ p.ds, ∀ j ∈ x.opens, F.t₁ ≤ j := by
    intro x hx
    rw [hpds, ← hlist] at hx
    exact opens_own₂ F file D h x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  have hA' : AtPlace (frameAt D (allOf D) D.key₂ 0) π (numAt F.t₁ F.t₂ 1) Sg.lstJ Sg.flC Sg.flZ
      Sg.flZ (fun s => r s.st) (baseAt F.t₁ F.t₂ 1 π) dB dt (errJ π r dt) := by
    rw [← hb0]
    exact hAt
  have hpe : HEq p.err (rest₂ (0 + pre.length) (dB :: dt)).err :=
    hperr _ fun ds' e => by
      subst e
      exact HEq.rfl
  obtain ⟨hK, hLaw⟩ := gameK_piece_le (F.XiPub × F.S₁) F.S₂ F.Cl enter leave _ W π 1 F.t₁ F.t₂ rd
    dB dt _ (errJ π r dt) r p B hpb hal hp0 (hpbase.trans hb0) hpds
    (fun ε₀ h0 => le_of_heq hpds ε₀ p.err _ _ h0 hpe (herr dB dt hlist)) hA' hj (Nat.le_refl _)
    hlb hf F.t₁ (by simp [numAt]) hho
  exact ⟨p, dB, dt, hrow, hpb, hpbase, hpds, hpe, hsm, hK, hLaw⟩

/-! ## What rides of the strings, for certain -/

/-- The strings behind are the strings in front at the stored table and at every tree below c. (Seen
from a reader's side: `ReadsBelow`, `ReadsBelow.imp`, Johnson/Desc/Sound/RunIsDecide.lean.) -/
def Rides (F : Frame) {S : Type} (c : ℕ) (a b : S × F.E.Str) : Prop :=
  b.2.1 = a.2.1 ∧ ∀ q : PosL F.all, (F.all.get q.1).no < c → b.2.2 q = a.2.2 q

/-- A yes of any piece: by `sLeft_old` (RunIsDecide.lean). No kind is named. -/
theorem strs_ride {S Cl W : Type} {C : PQ.CK} {F : Frame} (p : Piece C F S Cl W)
    (hnd : (F.all.map (·.no)).Nodup) (a b : S × F.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (h : p.ior.red.out a τ = some b) : Rides F p.base a b := by
  have h' : ((p.ior.out a.1 a.2 τ).map fun xo => (xo, p.ior.imp a.2 τ)) = some b := h
  obtain ⟨xo, _, rfl⟩ := Option.map_eq_some_iff.1 h'
  exact ⟨rfl, fun q hq => sLeft_old hnd p.ds p.base a.2 τ q hq⟩

theorem allOf_nodup (D : WholeD) : ((allOf D).map (·.no)).Nodup := by
  unfold VerifiableInference.Desc.Sound.allOf
  rw [List.map_map]
  have e : ((fun x : LeftT => x.no) ∘ fun j => (⟨j, (D.depth j).getD 0⟩ : LeftT)) = id := rfl
  rw [e, List.map_id]
  exact List.nodup_range ..

/-- **`gameK_at_tile₂_le` with what rides of the strings laid beside.** -/
theorem gameK_at_tile₂_ride {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber)
        ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (π : P12) (r : Fmt.M1.Stage → ℕ) (k : ℕ)
    (enter : F.S₂ → Except String T12) (leave : F.S₂ → T12 → Except String F.S₂)
    (pre : List (Block F.S₂ F.Cl)) (B b' : Block F.S₂ F.Cl) (post : List (Block F.S₂ F.Cl))
    (hfl : F.shared.blocksInOrder = b₂ :: l₂) (hcut : b₂ :: l₂ = pre ++ B :: b' :: post)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) B)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ k)) (hj : johOk π r = true)
    (hbat : batPriceOk π r k = true) (ho : π.nums.ownMask = false)
    (hlb : ownLabelsFreeB π = true) (hf : 0 < π.nums.free) (rd : ℕ → ℕ)
    (herr : ∀ dB dt, (D.ds₂.drop (pre.flatMap (·.rounds)).length).take
        (proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.length = dB :: dt →
      Err.le (s := uLT (ckP .two) (dB :: dt))
        (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt)
        (rest₂ (0 + pre.length) (dB :: dt)).err) :
    ∃ p dB dt,
      ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂)[pre.length]? =
        some p ∧
      p.b = held B ∧
      p.base = D.t₁ + nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length) ∧ p.ds = dB :: dt ∧
      HEq p.err (rest₂ (0 + pre.length) (dB :: dt)).err ∧
      Err.Below (s := uLT (ckP .two) (dB :: dt))
        (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) ((2 : ℝ≥0∞)⁻¹ ^ k) ∧
      p.ior.red.LeadsK
        (actAt (frameAt D (allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2 (fun _ => True)
        (fun a b => (QV (frameAt D (allOf D) D.key₂ 0) π (nlAt π F.t₁) r rd enter leave a b ∧
          b.1 = (a.1.1, b.1.2)) ∧ Rides (frameAt D (allOf D) D.key₂ 0) p.base a b) p.err ∧
      p.ior.red.KeyLaw
        (actAt (frameAt D (allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2
        (actAt (frameAt D (allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          (p.base + p.trees)).2 := by
  obtain ⟨p, dB, dt, hrow, hpb, hpbase, hpds, hpe, hsm, hK, hLaw⟩ :=
    gameK_at_tile₂_le F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r k enter leave pre B
      b' post hfl hcut hal hfree hp hC hj hbat ho hlb hf rd herr
  exact ⟨p, dB, dt, hrow, hpb, hpbase, hpds, hpe, hsm,
    hK.beside_sure _ fun a τ b _ hout => strs_ride p (allOf_nodup D) a b τ hout, hLaw⟩

/-! ## At the letters of record -/

/-- The filling that is meant lays other starts and ends; the pieces are the same. -/
theorem atDesc_row₂ {C : PQ.CK} {D : WholeD} {all : List LeftT} {Xi X₁ X₂ W : Type}
    (F : FileDescription Xi) (T : ThreeAt C D all F X₁ X₂ W) :
    (atDesc F T).p₂ :: (atDesc F T).l₂ = T.p₂ :: T.l₂ := rfl

/-- **WHERE EVERY PIECE's ERRORS ARE THE CAP** (`AtCap`, Johnson/Desc/Sound/BoundsAtCap.lean): no
premise on the errors is left: the law with the key, and so the law for a batch at every number of
slots (`LeadsK.bothN`), stand at the piece's own errors, the cap. A second road to the same piece
goes from a row that bears the law's own errors (`gameK_at_tile₂`) by a carriage between two cuts
(Johnson/Desc/Sound/CutAtCap.lean [not in this library]): the two meet here. -/
theorem gameK_at_tile₂_cap {Xi W : Type} (F : FileDescription Xi) (file : String) (D : WholeD)
    (h : F.data file = .ok D)
    (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
    (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) (F.XiPub × F.S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₂ 0) ((F.XiPub × F.S₁) × F.S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) →
      Rest (ckP .two) (frameAt D (allOf D) D.key₃ F.lastChainFirstTreeNumber)
        ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
    (d wEnd : W) (π : P12) (r : Fmt.M1.Stage → ℕ)
    (enter : F.S₂ → Except String T12) (leave : F.S₂ → T12 → Except String F.S₂)
    (pre : List (Block F.S₂ F.Cl)) (B b' : Block F.S₂ F.Cl) (post : List (Block F.S₂ F.Cl))
    (hfl : F.shared.blocksInOrder = b₂ :: l₂) (hcut : b₂ :: l₂ = pre ++ B :: b' :: post)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) B)
    (hfree : π.nums.free = rootsOf (pre.flatMap (·.rounds)))
    (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (hC : ChainAt π r ((2 : ℝ≥0∞)⁻¹ ^ 128)) (hj : johOk π r = true)
    (hbat : batPriceOk π r 128 = true) (ho : π.nums.ownMask = false)
    (hlb : ownLabelsFreeB π = true) (hf : 0 < π.nums.free) (rd : ℕ → ℕ) (hcap : AtCap rest₂)
    (N : ℕ) :
    ∃ p,
      ((piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).p₂ ::
        (piecesAt (ckP .two) F D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd).l₂)[pre.length]? =
        some p ∧
      p.b = held B ∧
      p.base = D.t₁ + nTrees (D.ds₂.take (pre.flatMap (·.rounds)).length) ∧
      p.ior.red.LeadsK
        (actAt (frameAt D (allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2 (fun _ => True)
        (fun a b => (QV (frameAt D (allOf D) D.key₂ 0) π (nlAt π F.t₁) r rd enter leave a b ∧
          b.1 = (a.1.1, b.1.2)) ∧ Rides (frameAt D (allOf D) D.key₂ 0) p.base a b) p.err ∧
      p.ior.red.LeadsBN
        (actAt (frameAt D (allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2 (fun _ => True)
        (fun a b => (QV (frameAt D (allOf D) D.key₂ 0) π (nlAt π F.t₁) r rd enter leave a b ∧
          b.1 = (a.1.1, b.1.2)) ∧ Rides (frameAt D (allOf D) D.key₂ 0) p.base a b) N p.err ∧
      p.ior.red.KeyLaw
        (actAt (frameAt D (allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          p.base).2
        (actAt (frameAt D (allOf D) D.key₂ 0) (Prod.snd : (F.XiPub × F.S₁) × F.S₂ → F.S₂) F.t₁
          (p.base + p.trees)).2 := by
  obtain ⟨p, dB, dt, hrow, hpb, hpbase, _, _, _, hK, hLaw⟩ :=
    gameK_at_tile₂_ride F file D h b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd π r 128 enter leave
      pre B b' post hfl hcut hal hfree hp hC hj hbat ho hlb hf rd fun dB dt hc => by
        obtain ⟨dB', dt', hc', _, hsm⟩ := atPlace_tile₂ F file D h D.key₂ 0 π r 128 pre B
          (b' :: post) (hfl.trans hcut) hal.rounds hfree hp hC hj hbat ho
        obtain ⟨rfl, rfl⟩ := List.cons.inj (hc.symm.trans hc')
        rw [hcap (0 + pre.length) (dB :: dt)]
        exact Err.le_cap_of_below_inv 128 _ hsm
  exact ⟨p, hrow, hpb, hpbase, hK, hK.bothN N, hLaw⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.labelsPub_in
#print axioms VerifiableInference.Desc.K12.Coin.qn_reads
#print axioms VerifiableInference.Desc.K12.Coin.qn_in_iff_at
#print axioms VerifiableInference.Desc.K12.Coin.qv_key
#print axioms VerifiableInference.Desc.K12.Coin.leadsK_of_leads_key
#print axioms VerifiableInference.Desc.K12.Coin.held_sure
#print axioms VerifiableInference.Desc.K12.Coin.gameK_piece
#print axioms VerifiableInference.Desc.K12.Coin.gameK_at_tile₂
#print axioms VerifiableInference.Desc.K12.Coin.qn_readsM
#print axioms VerifiableInference.Desc.K12.Coin.leadsK_of_leads_keyOn
#print axioms VerifiableInference.Desc.K12.Coin.gameK_piece_le
#print axioms VerifiableInference.Desc.K12.Coin.gameK_at_tile₂_le
#print axioms VerifiableInference.Desc.K12.Coin.strs_ride
#print axioms VerifiableInference.Desc.K12.Coin.allOf_nodup
#print axioms VerifiableInference.Desc.K12.Coin.gameK_at_tile₂_ride
#print axioms VerifiableInference.Desc.K12.Coin.atDesc_row₂
#print axioms VerifiableInference.Desc.K12.Coin.gameK_at_tile₂_cap
