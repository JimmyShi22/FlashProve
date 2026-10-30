-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Shape/Seat.lean: what the output head's four runs of claims read of the first
chain's state, as a shape; the leaves' shapes at the seat; and the seat's three readers' returns as
tests on that shape.

What it is not. No law on a value but one: which test of the readers is on values is said by name
(endsB), and nothing is shown of it. It does not say that a state with such a view is ever reached.
It is tied to no one form of the whole chain's shape: `View` holds just what these runs read; how a
view is read off the chain's shape is said elsewhere. Nothing on any property of the protocol. It
stands on Parts.lean, Tail.lean, Own.lean and HeadHeard.lean of Johnson/Desc/First/Shape/.

All four runs read the state through lettersAt (Johnson/Desc/Kinds/HeadFrame.lean) at the seat
seatAt (Johnson/Stored/HeadSeatAt.lean): given, heard, reads.

  `View`, `viewOf`   a reply was heard · the ledger's shape · the shape of what the lookup's hearing
                laid · the shape of the squares' level's sumcheck · the shape of what the head's own
                rounds heard · the table of the tables of reads: where the chain stands in the
                head's link, opened, and the last four are laid
  `hidSh`, `leftSh`, `placeSh`, `leavesAt`   the leaves' shapes, of a view's parts
  `givenB`, `heardB`, `readsB`, `lettersB`   the readers' tests that a shape can answer
  `endsB`       THE ONE TEST ON VALUES: each call's key point ends in the lookup's point
  `leaves_at`   where the seat's heard and reads return at a state with a view: LeavesAre
  `heard_iff`, `reads_iff`, `given_iff`, `letters_iff`   each reader returns just where its test
                accepts (given: and endsB)
  `view_of_letters`   where lettersAt returns there is a view
BENEATH THESE, small laws, each said at its place: of what a view is made (view_spec, fork_at,
look_at, view_look) · when a chain of options returns (bind_isSome, mapM_isSome, all_and,
zip_fst_map) · the ledger's marks (got_getD, *_isSome) · what the way back hands out (allOf_spec,
sumOf_spec, hid_var, hids_var) · a sumcheck's own form (varOf_d, hiding_len, onSlots_sh,
rowFormSh_noTerm, left_sh) · cols_at · leaves_mk (LeavesAre at letters handed in as terms) · the
letters in front (zk_size, test_split, given_isSome, letters_isSome).

-/
import Johnson.Desc.K6.Shape.Keys
import Johnson.Desc.First.Shape.HeadHeard
import Johnson.Stored.HeadAddsAtS
import Johnson.Desc.Kinds.Law.RunsStill
import Johnson.Desc.Kinds.Law.HeardBack
import Johnson.Desc.Kinds.Law.WeightAtSame
import Johnson.Desc.Part.MaskedSumSound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Shape
open OnBytes (E zeroE)
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (AffSh affSh PscSh pscSh LedSh ledSh heardAll HeadHeardSh
  headHeardSh TscSh tscSh rowFormSh affSh_addMul affSh_add affSh_sub)

local infixl:65 " ⋆ " => AffSh.append

/-! ## The view -/

/-- The shape of what a lookup's hearing laid, under a name that is free here. -/
abbrev LookSh : Type := VerifiableInference.Desc.First.Shape.HeardAll

/-- What the four runs read of the state, without a field element. -/
structure View where
  /-- a next token was heard -/
  reply : Bool
  /-- the ledger -/
  led : LedSh
  /-- what the lookup's hearing laid -/
  look : LookSh
  /-- the state of the squares' level's sumcheck -/
  Q : PscSh
  /-- what the head's own rounds heard -/
  X : HeadHeardSh
  /-- for each table of reads: its name, its first entry, its length -/
  tab : List (String × Nat × Nat)

/-- The view at a state: where the chain stands in the head's link, the link is opened, and the
lookup's hearing, the level's sumcheck, the head's hearing and the tables are laid. -/
def viewOf (s : S) : Option View :=
  match s.here with
  | .head o =>
    if o.opened then
      o.lookHeard.bind fun g => o.squaresP.bind fun q => o.x.bind fun x => o.t.map fun tt =>
        { reply := s.out.reply.isSome, led := ledSh o.F, look := heardAll g, Q := pscSh q,
          X := headHeardSh x, tab := tt.tab }
    else none
  | _ => none

/-! ## The leaves' shapes -/

/-- Hidden scalar number i of n that lie under the slots from first on; beyond: no term. -/
def hidSh (first n i : Nat) : AffSh := if i < n then slotSh (first + i) else noTerm

/-- How many coefficients the hiding polynomial has, of its variables' numbers of coefficients: each
variable has one less than its number, the last all. -/
def hidLen : List Nat → Nat
  | [] => 0
  | [k] => k
  | k :: rest => (k - 1) + hidLen rest

/-- The form that a sumcheck leaves: its own slots from the first on, then the start form's terms.
Only variables that have a challenge count. -/
def leftSh (p : PscSh) : AffSh :=
  rowFormSh p.first (hidLen (p.degrees.take p.challenges)) p.start noTerm

/-- Entry i of the table of reads of that name: one entry of array iU3, which has K columns. -/
def placeSh (tab : List (String × Nat × Nat)) (iU3 K : Nat) (name : String) (i : Nat) : AffSh :=
  let pos := ((tab.find? fun e => e.1 == name).map (·.2.1)).getD 0 + i
  AffSh.mk [(iU3, pos / K, pos % K)] []

/-- The names of the normalization's seven reads' tables. -/
def nameN : FinalNorm.Read → String
  | .streamAtSquares => "xbL@Z_V" | .streamAtNormed => "xbL@Y_N"
  | .actAtKeys => "hd@zt_FC" | .rowAtKeys => "hr@zt_ROW" | .rowAtPV => "hr@P_V"
  | .rowAtProducts => "hr@r_tV" | .rowAtNormed => "hr@rt_N"

/-- The names of the head's five reads' tables. -/
def nameH : Read → String
  | .wideAtKeys => "hf@Z" | .wideAtCosts => "hf@phiZ" | .actAtLogits => "hd@r_H"
  | .rowAtCosts => "hr@phiC" | .rowCount => "hr@rhoC"

/-- **The leaves' shapes at the seat.** -/
def leavesAt (X : HeadHeardSh) (Q : PscSh) (tab : List (String × Nat × Nat)) (iU3 K : Nat) :
    LeafSh where
  W := hidSh X.sW 9
  P := hidSh X.sPv 7
  sqLeft := leftSh Q
  sqEnd := fun j => if j = 0 then slotSh X.wpl.sL else if j = 1 then slotSh X.wpl.sR else noTerm
  prLeft := leftSh X.tV.p
  prClaimed := slotSh X.tV.sCl
  prEnd := hidSh X.tV.sEnd 4
  nmLeft := leftSh X.tN.p
  nmClaimed := slotSh X.tN.sCl
  nmEnd := hidSh X.tN.sEnd 2
  lgLeft := leftSh X.tH.p
  lgClaimed := slotSh X.tH.sCl
  lgEnd := hidSh X.tH.sEnd 2
  entryN := fun r i => placeSh tab iU3 K (nameN r) i
  wide := placeSh tab iU3 K "hf@Z"
  entryH := fun r i => placeSh tab iU3 K (nameH r) i

/-- The number of columns of array number iU3; 0 where there is none. -/
def colsOf (L : LedSh) (iU3 : Nat) : Nat := (L.treeAt iU3).K

/-- The leaves' shapes at a view. -/
def View.leaves (v : View) (iU3 : Nat) : LeafSh :=
  leavesAt v.X v.Q v.tab iU3 (colsOf v.led iU3)

/-! ## The readers' tests -/

/-- Slot j is there and filled. -/
def filledB (L : LedSh) (j : Nat) : Bool := Decidable.decide (j < L.ns) && L.got.getD j false

/-- The n slots from first on are there and filled. -/
def filledRun (L : LedSh) (first n : Nat) : Bool :=
  (List.range n).all fun i => filledB L (first + i)

/-- A token sumcheck's claimed sum and its n end values are filled. -/
def tscB (L : LedSh) (t : TscSh) (n : Nat) : Bool := filledB L t.sCl && filledRun L t.sEnd n

/-- What was heard is read back: each of the slots that it names is filled, and the two
lists of powers have a second member. -/
def heardB (X : HeadHeardSh) (L : LedSh) : Bool :=
  filledRun L X.sW 9 && Decidable.decide (1 < X.gp) && filledB L X.wpl.sL && filledB L X.wpl.sR &&
    filledRun L X.sPv 7 && Decidable.decide (1 < X.omV) && tscB L X.tV 4 && tscB L X.tN 2 &&
    tscB L X.tH 2

/-- The reads' places are read: the reads' array is there with a column, and each of the twelve
tables is found and long enough. -/
def readsB (h : OnBytes.Model.Head.Shape) (tab : List (String × Nat × Nat)) (iU3 : Nat)
    (L : LedSh) : Bool :=
  Decidable.decide (iU3 < L.trees.length) && !(colsOf L iU3 == 0) &&
    (readsNeed h).all fun n => (tab.find? fun e => e.1 == n.1).any fun e => Nat.ble n.2 e.2.2

/-- The letters in front of the hearing are read, as far as a shape can say: a next token was heard,
and each call's key point has its size. -/
def givenB (p : Par) (G : LookSh) (reply : Bool) : Bool :=
  let _ := p.sizes
  reply && callList.zipIdx.all fun c => G.zk.getD c.2 0 == lJ p.floor c.1 + Norm.lt

/-- **THE ONE TEST ON VALUES**: the last ls + lt coordinates of each call's key point are those of
the lookup's point. -/
def endsB (p : Par) (g : OnBytes.Model.Forest.Heard) : Bool :=
  let _ := p.sizes
  callList.zipIdx.all fun c =>
    Point.last (g.zk.getD c.2 #[]) (Norm.ls + Norm.lt) == Point.last g.zx (Norm.ls + Norm.lt)

/-- All three readers' tests on the shape. -/
def lettersB (p : Par) (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (v : View) : Bool :=
  givenB p v.look v.reply && heardB v.X v.led && readsB h v.tab iU3 v.led

/-! ## The laws -/

/-- Where there is a view: the fields of which it is made. -/
theorem view_spec {s : S} {v : View} (hv : viewOf s = some v) :
    ∃ o g q x tt, s.here = .head o ∧ o.opened = true ∧ o.lookHeard = some g ∧
      o.squaresP = some q ∧ o.x = some x ∧ o.t = some tt ∧
      v = { reply := s.out.reply.isSome, led := ledSh o.F, look := heardAll g, Q := pscSh q,
            X := headHeardSh x, tab := tt.tab } := by
  unfold viewOf at hv
  cases hh : s.here with
  | head o =>
    rw [hh] at hv
    dsimp only at hv
    by_cases ho : o.opened = true
    · rw [if_pos ho] at hv
      obtain ⟨g, hg, h1⟩ := Option.bind_eq_some_iff.mp hv
      obtain ⟨q, hq, h2⟩ := Option.bind_eq_some_iff.mp h1
      obtain ⟨x, hx, h3⟩ := Option.bind_eq_some_iff.mp h2
      obtain ⟨tt, ht, h4⟩ := Option.map_eq_some_iff.mp h3
      exact ⟨o, g, q, x, tt, rfl, ho, hg, hq, hx, ht, h4.symm⟩
    · rw [if_neg ho] at hv
      cases hv
  | _ =>
    rw [hh] at hv
    cases hv

/-- In the head's link, opened, the state's own readers give the link's fields. -/
theorem fork_at {s : S} {o : VerifiableInference.Desc.First.HeadOwn} (hh : s.here = .head o)
    (ho : o.opened = true) : s.fork? = some o.F := by
  unfold S.fork?
  rw [hh]
  simp only [ho, if_true]

theorem look_at {s : S} {o : VerifiableInference.Desc.First.HeadOwn} (hh : s.here = .head o)
    (ho : o.opened = true) : s.lookHeard? = o.lookHeard := by
  unfold S.lookHeard?
  rw [hh]
  simp only [ho, if_true]

/-! ### Options -/

theorem bind_isSome {α β : Type} (o : Option α) (f : α → Option β) (b : Bool)
    (hb : ∀ a, o = some a → (f a).isSome = b) : (o.bind f).isSome = (o.isSome && b) := by
  cases o with
  | none => rfl
  | some a => exact hb a rfl

theorem mapM_isSome {α β : Type} (f : α → Option β) :
    ∀ l : List α, (l.mapM f).isSome = l.all fun a => (f a).isSome
  | [] => by simp
  | a :: l => by
    rw [List.mapM_cons, List.all_cons, ← mapM_isSome f l]
    cases f a with
    | none => rfl
    | some b =>
      cases l.mapM f with
      | none => rfl
      | some bs => rfl

theorem all_and {α : Type} (a b : α → Bool) :
    ∀ l : List α, (l.all fun x => a x && b x) = (l.all a && l.all b)
  | [] => rfl
  | x :: l => by
    rw [List.all_cons, List.all_cons, List.all_cons, all_and a b l]
    cases a x <;> cases b x <;> cases l.all a <;> cases l.all b <;> rfl

theorem zip_fst_map {α β γ : Type} (f : α → γ) :
    ∀ (l : List α) (r : List β), (l.zip r).map (fun x => f x.1) = (l.map f).take r.length
  | [], _ => by simp
  | _ :: _, [] => by simp
  | a :: l, b :: r => by
    simp only [List.zip_cons_cons, List.map_cons, List.length_cons, List.take_succ_cons]
    rw [zip_fst_map f l r]

/-! ### The ledger's marks -/

theorem got_getD (F : Fork) (j : Nat) : F.gotF.toList.getD j false = F.gotF.getD j false := by
  simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]

theorem hidAt_isSome (F : Fork) (j : Nat) : (hidAt F j).isSome = filledB (ledSh F) j := by
  unfold hidAt
  rw [Option.isSome_map]
  show (F.shown j).isSome = (Decidable.decide (j < F.ns) && F.gotF.toList.getD j false)
  rw [got_getD]
  unfold Fork.shown
  cases (Decidable.decide (j < F.ns) && F.gotF.getD j false) <;> rfl

theorem hidsAt_isSome (F : Fork) (j n : Nat) :
    (hidsAt F j n).isSome = filledRun (ledSh F) j n := by
  unfold hidsAt filledRun
  rw [Option.isSome_map, mapM_isSome]
  simp only [hidAt_isSome]

theorem sumOf_isSome (F : Fork) (t : OnBytes.Model.Tsc) (r : Point) (n : Nat) :
    (sumOf F t r n).isSome = tscB (ledSh F) (tscSh t) n := by
  unfold sumOf tscB
  refine (bind_isSome _ _ _ fun c _ => bind_isSome _ _ true fun es _ => rfl).trans ?_
  rw [hidAt_isSome, hidsAt_isSome, Bool.and_true]
  rfl

theorem size_isSome (a : Array E) : (a[1]?).isSome = Decidable.decide (1 < a.size) := by
  by_cases h1 : 1 < a.size
  · simp [h1]
  · simp [h1]

theorem allOf_isSome (F : Fork) (x : OnBytes.Model.Head.Heard)
    (sq : Option Part.MaskedSum.Heard) :
    (allOf F x sq).isSome = heardB (headHeardSh x) (ledSh F) := by
  unfold allOf heardB
  refine (bind_isSome _ _ _ fun _ _ => bind_isSome _ _ _ fun _ _ => bind_isSome _ _ _ fun _ _ =>
    bind_isSome _ _ _ fun _ _ => bind_isSome _ _ _ fun _ _ => bind_isSome _ _ _ fun _ _ =>
    bind_isSome _ _ _ fun _ _ => bind_isSome _ _ _ fun _ _ =>
    bind_isSome _ _ true fun _ _ => rfl).trans ?_
  rw [hidsAt_isSome, size_isSome, hidAt_isSome, hidAt_isSome, hidsAt_isSome, size_isSome,
    sumOf_isSome, sumOf_isSome, sumOf_isSome, Bool.and_true]
  simp only [Bool.and_assoc]
  rfl

/-! ### What the way back hands out -/

theorem allOf_spec {F : Fork} {x : OnBytes.Model.Head.Heard} {sq : Option Part.MaskedSum.Heard}
    {H : HeardAll} (e : allOf F x sq = some H) :
    ∃ W gam e0 e1 P om pr nm lg, hidsAt F x.sW 9 = some W ∧ hidAt F x.wpl.sL = some e0 ∧
      hidAt F x.wpl.sR = some e1 ∧ hidsAt F x.sPv 7 = some P ∧
      sumOf F x.tV x.tV.r 4 = some pr ∧ sumOf F x.tN x.tN.r 2 = some nm ∧
      sumOf F x.tH (x.tH.r ++ x.rs.reverse) 2 = some lg ∧
      H = ({ pV := x.PV, W := W, gam := gam, rhoI := #[]
             squares := { r := x.wpl.r, ends := #[e0, e1], down := x.wpl.tau, psc := sq }
             P := P, om := om, products := pr }, { normed := nm }, { logits := lg }) := by
  unfold allOf at e
  obtain ⟨W, h1, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨gam, _, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨e0, h3, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨e1, h4, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨P, h5, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨om, _, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨pr, h7, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨nm, h8, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨lg, h9, e⟩ := Option.bind_eq_some_iff.mp e
  exact ⟨W, gam, e0, e1, P, om, pr, nm, lg, h1, h3, h4, h5, h7, h8, h9,
    (Option.some.inj e).symm⟩

theorem sumOf_spec {F : Fork} {t : OnBytes.Model.Tsc} {r : Point} {n : Nat} {sm : Sum}
    (e : sumOf F t r n = some sm) :
    ∃ c es, hidAt F t.sCl = some c ∧ hidsAt F t.sEnd n = some es ∧
      sm = { r := r, claimed := c, ends := es, psc := some (keptOf t.p t.sEnd) } := by
  unfold sumOf at e
  obtain ⟨c, h1, e⟩ := Option.bind_eq_some_iff.mp e
  obtain ⟨es, h2, e⟩ := Option.bind_eq_some_iff.mp e
  exact ⟨c, es, h1, h2, (Option.some.inj e).symm⟩

theorem hid_var {F : Fork} {j : Nat} {a : Hid} (e : hidAt F j = some a) :
    affSh a.var = slotSh j := by
  rw [(Law.hidAt_spec e).1]
  rfl

theorem hids_var {F : Fork} {j n : Nat} {a : Array Hid} (e : hidsAt F j n = some a) (i : Nat) :
    affSh (a.getD i {}).var = hidSh j n i := by
  unfold hidSh
  obtain ⟨hs, hi⟩ := Law.hidsAt_spec e
  by_cases hn : i < n
  · rw [if_pos hn]
    exact hid_var (hi i hn)
  · rw [if_neg hn]
    have e0 : a.getD i {} = {} := by
      have : ¬ i < a.size := by omega
      simp [Array.getD, this]
    rw [e0]
    rfl

/-! ### A sumcheck's own form -/

theorem varOf_d (w : OnBytes.Psc.Weight) : (varOf w).d = w.d := by
  unfold varOf
  split <;> rfl

theorem hiding_len : ∀ vr : List (Part.MaskedSum.Var × E),
    (Part.MaskedSum.hidingAt vr).1.length = hidLen (vr.map fun x => x.1.d)
  | [] => rfl
  | [(v, r)] => by
    show (Part.MaskedSum.powersFrom r v.d OnBytes.oneE).length = v.d
    rw [Part.MaskedSum.powersFrom_length]
  | (v, r) :: y :: rest => by
    have ih := hiding_len (y :: rest)
    show (Part.MaskedSum.powersFrom r (v.d - 1) _ ++
      (Part.MaskedSum.hidingAt (y :: rest)).1).length =
        (v.d - 1) + hidLen ((y :: rest).map fun x => x.1.d)
    rw [List.length_append, Part.MaskedSum.powersFrom_length, ih]

theorem onSlots_sh : ∀ (u : List E) (first : Nat) (f : Aff),
    affSh (Part.MaskedSum.onSlots f first u) =
      affSh f ⋆ AffSh.mk [] (List.range' first u.length)
  | [], first, f => (append_noTerm (affSh f)).symm
  | x :: u, first, f => by
    show affSh (Part.MaskedSum.onSlots (Aff.addMul f (Aff.slot first) x) (first + 1) u) = _
    rw [onSlots_sh u (first + 1), affSh_addMul, append_assoc]
    rfl

theorem rowFormSh_noTerm (first n : Nat) (st : AffSh) :
    rowFormSh first n st noTerm = AffSh.mk [] (List.range' first n) ⋆ st := by
  obtain ⟨e, s⟩ := st
  show (e ++ [], List.range' first n ++ s ++ []) = ([] ++ e, List.range' first n ++ s)
  simp

theorem cols_at {F : Fork} {iU3 : Nat} {tr : OnBytes.Model.HTree} (e : F.trees[iU3]? = some tr) :
    colsOf (ledSh F) iU3 = tr.K := by
  show ((F.trees.toList.map VerifiableInference.Desc.First.Shape.treeSh).getD iU3 _).K = tr.K
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList, e]
  rfl

/-- LeavesAre at letters that are handed in as terms: so that a caller need not bind a class. -/
theorem leaves_mk (N : Norm.Heard) (Fn : FinalNorm.Heard) (Hd : Heard) (R1 : FinalNorm.Reads)
    (R2 : Reads) (L : LeafSh) (W : ∀ s, affSh (N.W.getD s {}).var = L.W s)
    (P : ∀ n, affSh (N.P.getD n {}).var = L.P n)
    (sqLeft : ∀ S0, affSh (N.squares.left S0) = L.sqLeft)
    (sqEnd : ∀ j, affSh (N.squares.end_ j).var = L.sqEnd j)
    (prLeft : ∀ S0, affSh (N.products.left S0) = L.prLeft)
    (prClaimed : affSh N.products.claimed.var = L.prClaimed)
    (prEnd : ∀ j, affSh (N.products.end_ j).var = L.prEnd j)
    (nmLeft : ∀ S0, affSh (Fn.normed.left S0) = L.nmLeft)
    (nmClaimed : affSh Fn.normed.claimed.var = L.nmClaimed)
    (nmEnd : ∀ j, affSh (Fn.normed.end_ j).var = L.nmEnd j)
    (lgLeft : ∀ S0, affSh (Hd.logits.left S0) = L.lgLeft)
    (lgClaimed : affSh Hd.logits.claimed.var = L.lgClaimed)
    (lgEnd : ∀ j, affSh (Hd.logits.end_ j).var = L.lgEnd j)
    (entryN : ∀ r i, affSh (R1.entry r i) = L.entryN r i)
    (wide : ∀ i, affSh (R1.wide i) = L.wide i)
    (entryH : ∀ r i, affSh (R2.entry r i) = L.entryH r i) : @LeavesAre N Fn Hd R1 R2 L :=
  @LeavesAre.mk N Fn Hd R1 R2 L W P sqLeft sqEnd prLeft prClaimed prEnd nmLeft nmClaimed nmEnd
    lgLeft lgClaimed lgEnd entryN wide entryH

/-! ### The letters in front -/

theorem zk_size (g : OnBytes.Model.Forest.Heard) (c : Nat) :
    (heardAll g).zk.getD c 0 = (g.zk.getD c #[]).size := by
  show (g.zk.toList.map (·.size)).getD c 0 = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getD_eq_getD_getElem?]
  cases g.zk[c]? <;> rfl

/-- The third test of `given`, cut in two: the sizes; the values. -/
theorem test_split [Sizes] (floor : Nat) (zx : Point) (zk : Nat → Point) :
    ((fromLookup floor zx zk).calls.zipIdx.all fun c =>
      (zk c.2).size == lJ floor c.1.2 + Norm.lt &&
        (zk c.2).last (Norm.ls + Norm.lt) == zx.last (Norm.ls + Norm.lt)) =
    ((callList.zipIdx.all fun c => (zk c.2).size == lJ floor c.1 + Norm.lt) &&
      callList.zipIdx.all fun c =>
        (zk c.2).last (Norm.ls + Norm.lt) == zx.last (Norm.ls + Norm.lt)) := by
  rw [← all_and, ← calls_keys_all floor zx zk, List.zipIdx_map, List.all_map]
  rfl

/-- Where the lookup's points are laid and a token was heard, `given` returns just where its third
test accepts. -/
theorem given_isSome {S' : Type} (p : Par) (L : Seat S') (s : S') (z : Point × (Nat → Point))
    (y : Nat) (hz : L.lookup s = some z) (hy : Reply.token L.toSeat s = some y) :
    (given p L s).toOption.isSome =
      (let _ := p.sizes
       (fromLookup p.floor z.1 z.2).calls.zipIdx.all fun c =>
        (z.2 c.2).size == lJ p.floor c.1.2 + Norm.lt &&
          (z.2 c.2).last (Norm.ls + Norm.lt) == z.1.last (Norm.ls + Norm.lt)) := by
  unfold given
  rw [hz, hy]
  letI := p.sizes
  by_cases ht : ((fromLookup p.floor z.1 z.2).calls.zipIdx.all fun c =>
      (z.2 c.2).size == lJ p.floor c.1.2 + Norm.lt &&
        (z.2 c.2).last (Norm.ls + Norm.lt) == z.1.last (Norm.ls + Norm.lt)) = true
  · simp only [named, need, bind, Except.bind, ht, if_true, pure, Except.pure]
    rfl
  · have hf := eq_false_of_ne_true ht
    simp only [named, need, bind, Except.bind, hf, pure, Except.pure]
    rfl

theorem letters_isSome {S' : Type} (p : Par) (L : Seat S') (s : S') :
    (lettersAt p L s).toOption.isSome =
      ((given p L s).toOption.isSome && (L.heard s).isSome && (L.reads s).isSome) := by
  unfold lettersAt
  cases given p L s with
  | error m => rfl
  | ok g =>
    cases L.heard s with
    | none => rfl
    | some H =>
      cases L.reads s with
      | none => rfl
      | some x => rfl

section Laws
variable (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par)

/-- A view's lookup's shape is the shape of what the state's own reader gives. -/
theorem view_look {s : S} {v : View} (hv : viewOf s = some v) :
    ∃ g, s.lookHeard? = some g ∧ v.look = heardAll g := by
  obtain ⟨o, g, q, x, tt, hh, ho, hg, _, _, _, rfl⟩ := view_spec hv
  exact ⟨g, (look_at hh ho).trans hg, rfl⟩

/-- The form that a sumcheck leaves, as the seat reads the sumcheck back. -/
theorem left_sh (q : OnBytes.Model.Psc) (sEnd : Nat) (S0 : E) :
    affSh (Part.MaskedSum.rowForm (keptOf q sEnd) S0 {}) = leftSh (pscSh q) := by
  have hd : ((keptOf q sEnd).vars.zip (keptOf q sEnd).r).map (fun x => x.1.d) =
      (pscSh q).degrees.take (pscSh q).challenges := by
    show ((q.vars.toList.map varOf).zip q.r.toList).map (fun x => x.1.d) =
      (q.vars.toList.map (·.d)).take q.r.size
    rw [zip_fst_map (fun v : Part.MaskedSum.Var => v.d), List.map_map, Array.length_toList]
    congr 1
    exact List.map_congr_left fun w _ => varOf_d w
  unfold leftSh
  rw [rowFormSh_noTerm, ← hd, ← hiding_len]
  show affSh (Aff.addMul (Aff.addMul (Part.MaskedSum.onSlots (Aff.ofConst _) q.first
    (Part.MaskedSum.hidingAt ((keptOf q sEnd).vars.zip (keptOf q sEnd).r)).1)
    (Aff.ofConst _ - q.start) _) {} _) = _
  rw [affSh_addMul, affSh_addMul, onSlots_sh, affSh_sub, affSh_const, affSh_const, affSh_empty,
    noTerm_append, noTerm_append, append_noTerm]
  rfl

/-- **Where the seat's heard and reads return at a state with a view, the leaves have the view's
shapes.** -/
theorem leaves_at {s : S} {v : View} (hv : viewOf s = some v) {H : HeardAll}
    (hH : (seatAt h iU3).heard s = some H) {x : FinalNorm.Reads × Reads}
    (hx : (seatAt h iU3).reads s = some x) :
    letI : Norm.Heard := H.1
    letI : FinalNorm.Heard := H.2.1
    letI : Heard := H.2.2
    letI : FinalNorm.Reads := x.1
    letI : Reads := x.2
    LeavesAre (v.leaves iU3) := by
  obtain ⟨o, g, q, x0, tt, hh, ho, _, hq, hx0, ht, rfl⟩ := view_spec hv
  have eH : allOf o.F x0 (some (keptOf q x0.wpl.sL)) = some H := by
    have e' : (match s.here with
      | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
        allOf o.F x (some (keptOf q x.wpl.sL))
      | _ => none) = some H := hH
    rw [hh] at e'
    dsimp only at e'
    rw [hq, hx0] at e'
    exact e'
  obtain ⟨W, gam, e0, e1, P, om, pr, nm, lg, h1, h3, h4, h5, h7, h8, h9, rfl⟩ := allOf_spec eH
  obtain ⟨c7, es7, a7, b7, rfl⟩ := sumOf_spec h7
  obtain ⟨c8, es8, a8, b8, rfl⟩ := sumOf_spec h8
  obtain ⟨c9, es9, a9, b9, rfl⟩ := sumOf_spec h9
  have hf := fork_at hh ho
  unfold seatAt at hx
  dsimp only at hx
  rw [hh, hf] at hx
  dsimp only at hx
  rw [ht, Option.bind_some] at hx
  obtain ⟨tr, htr, e2⟩ := Option.bind_eq_some_iff.mp hx
  have hK := cols_at htr
  split at e2
  · cases e2
  · have e3 := Option.some.inj e2
    subst e3
    refine leaves_mk _ _ _ _ _ _ (hids_var h1) (hids_var h5) (fun S0 => left_sh q _ S0)
      (fun j => ?_) (fun S0 => left_sh x0.tV.p _ S0) (hid_var a7) (hids_var b7)
      (fun S0 => left_sh x0.tN.p _ S0) (hid_var a8) (hids_var b8)
      (fun S0 => left_sh x0.tH.p _ S0) (hid_var a9) (hids_var b9)
      (fun r i => ?_) (fun i => ?_) (fun r i => ?_)
    · show affSh ((#[e0, e1] : Array Hid).getD j {}).var =
        (if j = 0 then slotSh x0.wpl.sL else if j = 1 then slotSh x0.wpl.sR else noTerm)
      match j with
      | 0 => exact hid_var h3
      | 1 => exact hid_var h4
      | _ + 2 => rfl
    · show _ = placeSh tt.tab iU3 (colsOf (ledSh o.F) iU3) (nameN r) i
      rw [hK]
      cases r <;> rfl
    · show _ = placeSh tt.tab iU3 (colsOf (ledSh o.F) iU3) "hf@Z" i
      rw [hK]
      rfl
    · show _ = placeSh tt.tab iU3 (colsOf (ledSh o.F) iU3) (nameH r) i
      rw [hK]
      cases r <;> rfl

theorem heard_iff {s : S} {v : View} (hv : viewOf s = some v) :
    ((seatAt h iU3).heard s).isSome = heardB v.X v.led := by
  obtain ⟨o, g, q, x0, tt, hh, ho, _, hq, hx0, _, rfl⟩ := view_spec hv
  have e : (seatAt h iU3).heard s = allOf o.F x0 (some (keptOf q x0.wpl.sL)) := by
    show (match s.here with
      | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
        allOf o.F x (some (keptOf q x.wpl.sL))
      | _ => none) = _
    rw [hh]
    dsimp only
    rw [hq, hx0]
    rfl
  rw [e]
  exact allOf_isSome _ _ _

theorem reads_iff {s : S} {v : View} (hv : viewOf s = some v) :
    ((seatAt h iU3).reads s).isSome = readsB h v.tab iU3 v.led := by
  obtain ⟨o, g, q, x0, tt, hh, ho, _, _, _, ht, rfl⟩ := view_spec hv
  have hf := fork_at hh ho
  unfold seatAt readsB
  dsimp only
  rw [hh, hf]
  dsimp only
  rw [ht, Option.bind_some]
  have hlen : (ledSh o.F).trees.length = o.F.trees.size := by
    show (o.F.trees.toList.map VerifiableInference.Desc.First.Shape.treeSh).length = _
    rw [List.length_map, Array.length_toList]
  rw [hlen]
  cases htr : o.F.trees[iU3]? with
  | none =>
    have hn : ¬ iU3 < o.F.trees.size := by
      intro hlt
      rw [Array.getElem?_eq_getElem hlt] at htr
      cases htr
    rw [Option.bind_none, decide_eq_false hn]
    rfl
  | some tr =>
    have hlt : iU3 < o.F.trees.size := by
      by_contra hn
      rw [Array.getElem?_eq_none (by omega)] at htr
      cases htr
    rw [Option.bind_some, cols_at htr, decide_eq_true hlt]
    generalize (tr.K == 0) = b1
    generalize ((readsNeed h).all fun n =>
      (tt.tab.find? fun e => e.1 == n.1).any fun e => Nat.ble n.2 e.2.2) = b2
    cases b1 <;> cases b2 <;> rfl

theorem given_iff {s : S} {v : View} (hv : viewOf s = some v)
    {g : OnBytes.Model.Forest.Heard} (hg : s.lookHeard? = some g) :
    (given p (seatAt h iU3) s).toOption.isSome = (givenB p v.look v.reply && endsB p g) := by
  obtain ⟨o, g0, q, x0, tt, hh, ho, hg0, _, _, _, rfl⟩ := view_spec hv
  have hgg : g0 = g := by
    have e := (look_at hh ho).symm.trans hg
    rw [hg0] at e
    exact Option.some.inj e
  subst hgg
  have hz : (seatAt h iU3).lookup s = some (g0.zx, fun c => g0.zk.getD c #[]) := by
    show s.lookHeard?.map _ = _
    rw [hg]
    rfl
  cases hr : s.out.reply with
  | none =>
    have hy : Reply.token (seatAt h iU3).toSeat s = none := by
      show (s.out.reply).map _ = none
      rw [hr]
      rfl
    unfold given
    rw [hz, hy]
    rfl
  | some y =>
    have hys : (Reply.token (seatAt h iU3).toSeat s).isSome = true := by
      show ((s.out.reply).map _).isSome = true
      rw [hr]
      rfl
    obtain ⟨t, hy⟩ := Option.isSome_iff_exists.mp hys
    rw [given_isSome p (seatAt h iU3) s _ t hz hy]
    show _ = (givenB p (heardAll g0) true && endsB p g0)
    unfold givenB endsB
    simp only [zk_size, Bool.true_and]
    exact @test_split p.sizes p.floor g0.zx fun c => g0.zk.getD c #[]

/-- **The letters are read just where the three tests on the shape and the one on values
accept.** -/
theorem letters_iff {s : S} {v : View} (hv : viewOf s = some v)
    {g : OnBytes.Model.Forest.Heard} (hg : s.lookHeard? = some g) :
    (lettersAt p (seatAt h iU3) s).toOption.isSome = (lettersB p h iU3 v && endsB p g) := by
  rw [letters_isSome, given_iff h iU3 p hv hg, heard_iff h iU3 hv, reads_iff h iU3 hv]
  unfold lettersB
  cases givenB p v.look v.reply <;> cases endsB p g <;> cases heardB v.X v.led <;>
    cases readsB h v.tab iU3 v.led <;> rfl

/-- Where the letters are read there is a view. -/
theorem view_of_letters {s : S} {w : Given × Behind × Places}
    (e : lettersAt p (seatAt h iU3) s = .ok w) : (viewOf s).isSome = true := by
  obtain ⟨H, x, e1, e2, e3, _⟩ := Law.lettersAt_ok h iU3 p e
  obtain ⟨z, y, hz, _, _, _⟩ := Law.Came.given_ok p (seatAt h iU3) s w.1 e1
  have hz' : s.lookHeard?.map (fun g => (g.zx, fun c => g.zk.getD c #[])) = some z := hz
  obtain ⟨g, hg, _⟩ := Option.map_eq_some_iff.mp hz'
  cases hh : s.here with
  | head o =>
    have ho : o.opened = true := by
      by_contra hn
      unfold S.lookHeard? at hg
      rw [hh] at hg
      simp [hn] at hg
    have hgo : o.lookHeard = some g := (look_at hh ho).symm.trans hg
    have e2' : (match s.here with
      | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
        allOf o.F x (some (keptOf q x.wpl.sL))
      | _ => none) = some H := e2
    rw [hh] at e2'
    dsimp only at e2'
    obtain ⟨q, hq, e2''⟩ := Option.bind_eq_some_iff.mp e2'
    obtain ⟨x0, hx0, _⟩ := Option.bind_eq_some_iff.mp e2''
    have hf := fork_at hh ho
    unfold seatAt at e3
    dsimp only at e3
    rw [hh, hf] at e3
    dsimp only at e3
    obtain ⟨tt, ht, _⟩ := Option.bind_eq_some_iff.mp e3
    unfold viewOf
    rw [hh]
    dsimp only
    rw [if_pos ho, hgo, hq, hx0, ht]
    rfl
  | _ =>
    exfalso
    have hN : (seatAt h iU3).heard s = none := by
      show (match s.here with
        | .head o => o.squaresP.bind fun q => o.x.bind fun x =>
          allOf o.F x (some (keptOf q x.wpl.sL))
        | _ => none) = none
      rw [hh]
    rw [hN] at e2
    cases e2

end Laws

end VerifiableInference.Desc.Kinds.Head.Shape

#print axioms VerifiableInference.Desc.Kinds.Head.Shape.view_spec
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.fork_at
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.look_at
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.bind_isSome
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.mapM_isSome
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.all_and
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.zip_fst_map
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.got_getD
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.hidAt_isSome
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.hidsAt_isSome
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.sumOf_isSome
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.size_isSome
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.allOf_isSome
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.allOf_spec
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.sumOf_spec
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.hid_var
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.hids_var
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.varOf_d
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.hiding_len
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.onSlots_sh
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.rowFormSh_noTerm
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.cols_at
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.leaves_mk
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.zk_size
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.test_split
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.given_isSome
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.letters_isSome
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.view_look
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.left_sh
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.leaves_at
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.heard_iff
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.reads_iff
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.given_iff
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.letters_iff
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.view_of_letters
