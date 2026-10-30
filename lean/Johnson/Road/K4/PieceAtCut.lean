-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/PieceAtCut.lean: FROM A LAW OF K4's BLOCK AT THE FIRST CHAIN's OWN RECORD TO THE
PIECE THAT THE MAKER OF THE PIECES CUTS. The rule of composition's pieces have one maker (`cutRow`,
`pieceOf`, Johnson/Desc/Sound/Tiles.lean; at a description: `piecesAt`,
Johnson/Desc/Sound/PaidAtDesc.lean). Its piece at a block bk of a chain is typed at the pair of what
was handed to the chain and the chain's own record, and holds `held bk`: `(below bk).lift Prod.snd
…`. A kind's law is typed at the chain's own record, at a piece that holds `below bk`. Here the two
are joined; and the piece's block, its rounds behind and its stretch are read off the maker's text,
its errors under `AtCap`. Book-keeping: a definition, statements and proofs; no round is evaluated.
Nearest kin, in the plain form: Johnson/Desc/Plain/PaidKeeps.lean ("for every t").

  `goodIn_lift_pair`: `liftGoodIn` (Johnson/Desc/Sound/LiftRule.lean) WITH A PARAMETER: where a
    piece has `GoodIn` at conditions and relations that hang on a letter z, for every z, the piece
    lifted to the pair has `GoodIn` at the same, read at z := the pair's first part. (`GoodIn` is
    asked statement by statement, and a lifted block leaves the first part.)
  `goodIn_ext`: `GoodIn` reads a piece's extractor at a yes alone: another extractor that agrees
    there has it too.
  `twin bk base ds e`: the piece at the chain's own record: `below bk`, the stretch ds, no round
    behind, the identity as its extractor, the errors e.
  `goodIn_pieceOf_held`: so the maker's piece `pieceOf (held bk) base ds [] x` has `GoodIn`, read at
    the pair, where the twin has it for every z and x's extractor is the identity at a yes.
  `cutRow_mem`: every piece that the maker cuts is `pieceOf b base' ds' back' (rest i' ds')` for a
    block b of the row; `cutRow_back`: all but the row's last have no round behind.
  `cutRow_err`: under `AtCap rest` (Johnson/Desc/Sound/BoundsAtCap.lean) every piece's errors are
    the cap.
  `rdtOf_of_roundIs`, `mapM_of_along`, `k4Ds_of_along`: THE STRETCH: where a piece's block declares
    K4's rounds (`Declares`, Johnson/Road/K4/PieceTiled.lean), its stretch has as many rounds, and
    `RoundIs` holds along it (Johnson/Desc/Sound/Stretch.lean: `stretchOfData` shows that of every
    piece of a description's rows), the stretch IS K4's written rounds: `k4Ds par = some pc.ds`.

Limits. That the family rest is the cap's, and that its extractor at K4's number is the identity at
a yes, are premises: the maker takes rest as a letter. That K4's block is not its chain's last is
not said. Which block of a description's first chain stands at K4's place is not said. Nothing on
soundness.
-/
import Johnson.Desc.Sound.PaidAtDesc
import Johnson.Desc.Sound.LiftRule
import Johnson.Desc.Sound.Stretch
import Johnson.Desc.Sound.BoundsAtCap
import Johnson.Road.K4.PieceTiled

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open OnBytes.Desc.First.K4
open _root_.Run.PQ (CK)
open _root_.Iop (Err Doomed)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound

variable {P T Cl W : Type} {C : CK} {F : Frame}

/-! ### The lift, with a parameter -/

/-- **One law for every z, at the chain's own record, gives the law of the lifted piece, read at
z := the pair's first part.** -/
theorem goodIn_lift_pair (q : Piece C F T Cl W) (on on' : P → T × F.E.Str → Prop)
    (R R' : P → T × F.E.Str → W → Prop) (h : ∀ z, q.GoodIn (on z) (on' z) (R z) (R' z)) :
    (q.lift Prod.snd fun (t : P × T) s => (t.1, s)).GoodIn
      (fun a => on a.1.1 (a.1.2, a.2)) (fun a => on' a.1.1 (a.1.2, a.2))
      (fun a w => R a.1.1 (a.1.2, a.2) w) (fun a w => R' a.1.1 (a.1.2, a.2) w) := by
  intro a ha
  have k := liftGoodIn (P × T) T Cl W C F Prod.snd (fun t s => (t.1, s)) q (on a.1.1) (on' a.1.1)
    (R a.1.1) (R' a.1.1) (fun _ _ => rfl) (fun _ _ _ => rfl) (h a.1.1) a ha
  refine Doomed.mono _ _ ?_ k
  intro τ hτ b hb
  have hb' := hb
  rw [liftOut (P × T) T Cl W C F Prod.snd (fun t s => (t.1, s)) q (fun _ _ => rfl)
    (fun _ _ _ => rfl) a τ] at hb'
  obtain ⟨b₀, _, rfl⟩ := Option.map_eq_some_iff.1 hb'
  exact hτ _ hb

/-- **`GoodIn` reads the extractor at a yes alone.** -/
theorem goodIn_ext (q : Piece C F T Cl W) (x : T × F.E.Str → Iop.Tr (uLT C q.ds) → W → W)
    (hx : ∀ a τ b w, q.ior.red.out a τ = some b → x a τ w = q.ext a τ w)
    {on on' : T × F.E.Str → Prop} {R R' : T × F.E.Str → W → Prop} (h : q.GoodIn on on' R R') :
    ({ q with ext := x } : Piece C F T Cl W).GoodIn on on' R R' := by
  intro a ha
  refine Doomed.mono _ _ ?_ (h a ha)
  intro τ hτ b hb
  obtain ⟨h1, h2⟩ := hτ b hb
  refine ⟨h1, fun w hw => ?_⟩
  have k := h2 w hw
  rw [← hx a τ b w hb] at k
  exact k

/-- The piece at the chain's own record: `below bk`, no round behind, the identity as extractor. -/
def twin (bk : Block T Cl) (base : ℕ) (ds : List RDT) (e : Err (uLT C ds)) : Piece C F T Cl W :=
  ⟨below bk, base, ds, [], fun _ _ w => w, e⟩

/-- **The maker's piece at a block that is not the row's last has the twin's law, read at the
pair**, where the twin has it for every z and the maker's extractor is the identity at a yes. -/
theorem goodIn_pieceOf_held (bk : Block T Cl) (base : ℕ) (ds : List RDT)
    (x : Rest C F (P × T) W ds) (on on' : P → T × F.E.Str → Prop)
    (R R' : P → T × F.E.Str → W → Prop)
    (h : ∀ z, (twin bk base ds x.err : Piece C F T Cl W).GoodIn (on z) (on' z) (R z) (R' z))
    (hx : ∀ a τ b w, (pieceOf (held bk) base ds [] x).ior.red.out a τ = some b →
      x.ext a τ w = w) :
    (pieceOf (held bk) base ds [] x).GoodIn
      (fun a => on a.1.1 (a.1.2, a.2)) (fun a => on' a.1.1 (a.1.2, a.2))
      (fun a w => R a.1.1 (a.1.2, a.2) w) (fun a w => R' a.1.1 (a.1.2, a.2) w) :=
  goodIn_ext ((twin bk base ds x.err : Piece C F T Cl W).lift Prod.snd
    fun (t : P × T) s => (t.1, s)) x.ext (fun a τ b w hb => hx a τ b w hb)
    (goodIn_lift_pair _ on on' R R' h)

/-! ### The maker's text -/

/-- Every piece that the maker cuts is `pieceOf` of a block of the row at `rest`'s value (its rounds
behind: `cutRow_back`). -/
theorem cutRow_mem (rest : (i : ℕ) → (ds : List RDT) → Rest C F T W ds) (putBack : List Fmt.RoundView) :
    ∀ (l : List (Block T Cl)) (b : Block T Cl) (i base : ℕ) (ds : List RDT),
      ∀ p ∈ (cutRow rest putBack i base ds b l).1 :: (cutRow rest putBack i base ds b l).2,
        ∃ b' ∈ b :: l, ∃ (i' base' : ℕ) (ds' : List RDT) (back' : List Fmt.RoundView),
          p = pieceOf b' base' ds' back' (rest i' ds')
  | [], b, i, base, ds, p, hp => by
    rw [cutRow_nil] at hp
    have e : p = pieceOf b base ds putBack (rest i ds) := by simpa using hp
    exact ⟨b, List.mem_cons_self, i, base, ds, putBack, e⟩
  | b' :: l, b, i, base, ds, p, hp => by
    rw [cutRow_cons] at hp
    rcases List.mem_cons.1 hp with e | hp
    · exact ⟨b, List.mem_cons_self, i, base, _, [], e⟩
    · obtain ⟨c, hc, r⟩ := cutRow_mem rest putBack l b' (i + 1) _ _ p hp
      exact ⟨c, List.mem_cons_of_mem _ hc, r⟩

/-- **Under `AtCap` every piece that the maker cuts has the cap as its errors.** -/
theorem cutRow_err (rest : (i : ℕ) → (ds : List RDT) → Rest C F T W ds) (hc : AtCap rest)
    (putBack : List Fmt.RoundView) (l : List (Block T Cl)) (b : Block T Cl) (i base : ℕ) (ds : List RDT)
    (p : Piece C F T Cl W)
    (hp : p ∈ (cutRow rest putBack i base ds b l).1 :: (cutRow rest putBack i base ds b l).2) :
    p.err = Err.cap 128 (uLT C p.ds) := by
  obtain ⟨_, _, i', _, ds', _, rfl⟩ := cutRow_mem rest putBack l b i base ds p hp
  exact hc i' ds'

/-- **All but the row's last have no round behind**: number k of the row, where a number k + 1
stands. -/
theorem cutRow_back (rest : (i : ℕ) → (ds : List RDT) → Rest C F T W ds) (putBack : List Fmt.RoundView) :
    ∀ (l : List (Block T Cl)) (b : Block T Cl) (i base : ℕ) (ds : List RDT) (k : ℕ)
      (p : Piece C F T Cl W), k < l.length →
      ((cutRow rest putBack i base ds b l).1 :: (cutRow rest putBack i base ds b l).2)[k]? =
        some p → p.back = []
  | [], _, _, _, _, _, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | b' :: l, b, i, base, ds, 0, p, _, hp => by
    rw [cutRow_cons, List.getElem?_cons_zero] at hp
    obtain rfl := Option.some.inj hp
    rfl
  | b' :: l, b, i, base, ds, k + 1, p, hk, hp => by
    rw [cutRow_cons, List.getElem?_cons_succ] at hp
    exact cutRow_back rest putBack l b' (i + 1) _ _ k p (Nat.lt_of_succ_lt_succ hk) hp

/-! ### The stretch at K4's block -/

/-- A round's data that are those of a declared round without an opening whose entry says no root
are what `rdtOf` makes of the entry. -/
theorem rdtOf_of_roundIs {num : Fmt.TreeSource → ℕ} {e : Fmt.Entry} {d : RDT}
    (h : RoundIs num ({ entry := e } : Fmt.DeclaredRound) d) (hr : e.roots = 0) :
    Desc.First.K4.rdtOf e = some d := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  obtain ⟨⟨en, kd, it, tr, op⟩, st⟩ := d
  have t0 : tr = [] := List.eq_nil_of_length_eq_zero (h6.trans hr)
  have e1 : en = e := h1
  have e3 : it = e.cut := h3
  have e4 : st = [] := h4
  have e5 : op = [] := h5
  have e2 : Fmt.kindOf e.name = some kd := h2
  subst e1 e3 e4 e5 t0
  unfold Desc.First.K4.rdtOf
  rw [e2]
  rfl

/-- Along a list of entries. -/
theorem mapM_of_along {num : Fmt.TreeSource → ℕ} : ∀ (es : List Fmt.Entry) (ds : List RDT),
    (∀ e ∈ es, e.roots = 0) → ds.length = es.length →
    Along (RoundIs num) (es.map fun e => ({ entry := e } : Fmt.DeclaredRound)) ds →
    es.mapM Desc.First.K4.rdtOf = some ds
  | [], [], _, _, _ => by simp
  | [], _ :: _, _, hl, _ => by cases hl
  | _ :: _, [], _, hl, _ => by cases hl
  | e :: es, d :: ds, hr, hl, h => by
    have h' : RoundIs num ({ entry := e } : Fmt.DeclaredRound) d ∧
        Along (RoundIs num) (es.map fun e => ({ entry := e } : Fmt.DeclaredRound)) ds := h
    have k1 := rdtOf_of_roundIs h'.1 (hr e List.mem_cons_self)
    have k2 := mapM_of_along es ds (fun x hx => hr x (List.mem_cons_of_mem _ hx))
      (Nat.succ.inj hl) h'.2
    rw [List.mapM_cons, k1, k2]
    rfl

/-- **The stretch of a piece whose block declares K4's rounds IS K4's written rounds**, where
`RoundIs` holds along it and it has as many rounds as the block declares. -/
theorem k4Ds_of_along {num : Fmt.TreeSource → ℕ} (pc : Piece C F T Cl W) {par : Par}
    (hd : Declares pc.b par) (hl : pc.ds.length = pc.b.rounds.length)
    (h : Along (RoundIs num) pc.b.rounds pc.ds) : k4Ds par = some pc.ds := by
  rw [hd] at h hl
  refine mapM_of_along _ _ (fun e he => ?_) (by simpa using hl) h
  have he' : e ∈ (rounds par.P par.hp par.g).map entryOf := he
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp he'
  rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.goodIn_lift_pair
#print axioms OnBytes.Road.K4.goodIn_ext
#print axioms OnBytes.Road.K4.goodIn_pieceOf_held
#print axioms OnBytes.Road.K4.cutRow_mem
#print axioms OnBytes.Road.K4.cutRow_err
#print axioms OnBytes.Road.K4.cutRow_back
#print axioms OnBytes.Road.K4.k4Ds_of_along
