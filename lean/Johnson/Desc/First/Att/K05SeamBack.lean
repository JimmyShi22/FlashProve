-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05SeamBack.lean: THE SEAM, THE OTHER WAY: WHERE THE KIND's PIECE PUTS OUT.
So
that the five theorems of Att/K05Seam.lean, which all begin "where the piece puts out", are not
idle.

Main names:
  `gots_allE`: a message all of whose items are scalars shows just these items, as scalars.
  `isEl`, `collect_fit`, `collect_rest`, `drawn_fit`: what the format's record of a written round's
    typed values holds: as many elements as the entry draws; no position, no matrix entry; an
    element that is drawn "never 0" is not (0, 0, 0).
  `written_fits`: AT EVERY WRITTEN TRANSCRIPT of `written p` the view passes the general step's
    roundsFit, and has the kind's shape (Fits).
  `groupsOf_none`, `step_of_decide`: a block none of whose rounds stores or opens anything reads no
    column: where the rounds fit, as a step it is its decision.
  `wants_none`, `full_none`, `piece_out_of_step`: GENERAL: a piece whose stretch opens nothing and
    reads nothing stored, and has as many written rounds as the block declares: where the work
    passes and the block says yes as a step on no column, the piece puts out just that.
  `seam_owed`, `seam_listed`, `seam_trees`: the kind's piece at `written p` has the rule's two
    conditions on one piece (Piece.Owed, Piece.Listed: the parts of Tiled) and sends no tree.
  `block_out`: so for ANY block with the kind's ROUNDS at `written p`: where the work passes, it
  puts
    out just what its decision hands on.
  `seam_accepts`: **the kind's own piece puts out at EVERY written transcript whose work passes**,
  if
    planOk p = true, nothing is owed, the ledger in front is Sized and has room, and the seat lays
    whatever is heard.
  `passing`, `passing_passes`, `seam_member`: there is such a transcript: so there are (a, τ, b).
  `freshLedger`, `ledgerSeat`, `seam_member_fresh`: the premises on the seat are met together: at
  the
    seat whose record is the ledger itself and a ledger of free slots, at every place with
    planOk p = true. `toyPar`, `toy_planOk`: there is such a place: a small made-up one.

Premises of seam_accepts | seam_member: those named. Limits. `ledgerSeat` is not the first chain's
seat, and `toyPar` is no place of a real plan: planOk is evaluated at no real place here. It is no
honest run: the kind's hearing
tests the shape and the room, nothing of the values: nothing is said on whether any claim holds of
what is put out. That the premises on the seat hold at the first chain's carried record is not
shown.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Seam
import Johnson.Desc.First.Att.K5Returns
import Johnson.Desc.Part.MaskedSumTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Flat OnBytes.Maker Fo.Peel
open VerifiableInference.Desc (Block OpenedColumn chainAt foldBlocks roundsFit drawsMarkedNonzeroHaveNonzeroWords noDigest itemOf groupsOf
  regroup need)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Fit Fits scalars)
open VerifiableInference.Desc.Sound (Frame Piece)
open _root_.Run (ckP)
open _root_.Run.PQ (CK PlainOf)

/-! ## What a written round shows -/

/-- A message all of whose items are scalars. -/
theorem gots_allE : ∀ (l : List Fmt.Item), (∀ it ∈ l, it = Fmt.Item.e) → ∀ x : PlainOf l,
    (PlainOf.gots l x).map itemOf = l ∧
      ∃ s, scalars (PlainOf.gots l x) = some s ∧ s.length = l.length
  | [], _, _ => ⟨rfl, [], rfl, rfl⟩
  | .e :: l, h, x => by
    obtain ⟨h1, s, h2, h3⟩ := gots_allE l (fun it hi => h it (List.mem_cons_of_mem _ hi))
      (x : Fmt.Ext × PlainOf l).2
    refine ⟨congrArg (Fmt.Item.e :: ·) h1, E.ofTriple (x : Fmt.Ext × PlainOf l).1 :: s, ?_,
      congrArg (· + 1) h3⟩
    show (scalars (PlainOf.gots l (x : Fmt.Ext × PlainOf l).2)).map _ = _
    rw [h2]
    rfl
  | .root :: _, h, _ => nomatch h _ List.mem_cons_self
  | .f :: _, h, _ => nomatch h _ List.mem_cons_self
  | .word :: _, h, _ => nomatch h _ List.mem_cons_self
  | .answer :: _, h, _ => nomatch h _ List.mem_cons_self

/-- The draws of elements. -/
def isEl : Fmt.Draw → Bool
  | .elem => true
  | .elemNZ => true
  | _ => false

theorem toU3_ne {e : _root_.Run.EV .two}
    (h : e ≠ (_root_.Run.zF .two, _root_.Run.zF .two, _root_.Run.zF .two)) :
    _root_.Run.toU3 e ≠ (0, 0, 0) := fun h0 =>
  h (_root_.Run.toU3_inj (h0.trans (by rfl)))

/-- As many elements as there are draws of elements; one that is drawn "never 0" is not (0, 0, 0).
-/
theorem collect_fit : ∀ (ds : List Fmt.Draw) (v : _root_.Run.Vals .two ds),
    (Fmt.collect (_root_.Run.outAll .two ds v)).elems.length = (ds.filter isEl).length ∧
      (((ds.filter isEl).zip (Fmt.collect (_root_.Run.outAll .two ds v)).elems).all fun x =>
        x.1 != .elemNZ || x.2 != (0, 0, 0)) = true
  | [], _ => ⟨rfl, rfl⟩
  | .elem :: ds, v => by
    obtain ⟨h1, h2⟩ := collect_fit ds v.2
    refine ⟨congrArg (· + 1) h1, ?_⟩
    show ((((Fmt.Draw.elem :: ds.filter isEl).zip (_ :: (Fmt.collect
      (_root_.Run.outAll .two ds v.2)).elems)).all _)) = true
    rw [List.zip_cons_cons, List.all_cons, h2]
    rfl
  | .elemNZ :: ds, v => by
    obtain ⟨h1, h2⟩ := collect_fit ds v.2
    refine ⟨congrArg (· + 1) h1, ?_⟩
    show ((((Fmt.Draw.elemNZ :: ds.filter isEl).zip (_root_.Run.toU3 v.1.1 :: (Fmt.collect
      (_root_.Run.outAll .two ds v.2)).elems)).all _)) = true
    rw [List.zip_cons_cons, List.all_cons, h2, Bool.and_true]
    have := toU3_ne v.1.2
    simp [this]
  | .pos _ :: ds, v => collect_fit ds v.2
  | .trits _ :: ds, v => collect_fit ds v.2
  | .sealed :: ds, v => collect_fit ds v.2

/-- No position and no matrix entry, where none is drawn. -/
theorem collect_rest : ∀ (ds : List Fmt.Draw) (v : _root_.Run.Vals .two ds),
    (∀ d ∈ ds, d = .elem ∨ d = .elemNZ ∨ d = .trits 0) →
    (Fmt.collect (_root_.Run.outAll .two ds v)).poss = [] ∧
      (Fmt.collect (_root_.Run.outAll .two ds v)).trits = []
  | [], _, _ => ⟨rfl, rfl⟩
  | .elem :: ds, v, h => collect_rest ds v.2 fun d hd => h d (List.mem_cons_of_mem _ hd)
  | .elemNZ :: ds, v, h => collect_rest ds v.2 fun d hd => h d (List.mem_cons_of_mem _ hd)
  | .trits n :: ds, v, h => by
    obtain ⟨h1, h2⟩ := collect_rest ds v.2 fun d hd => h d (List.mem_cons_of_mem _ hd)
    have hn : n = 0 := by
      rcases h _ List.mem_cons_self with e | e | e
      · cases e
      · cases e
      · exact Fmt.Draw.trits.inj e
    subst hn
    refine ⟨h1, ?_⟩
    show List.ofFn _ ++ (Fmt.collect (_root_.Run.outAll .two ds v.2)).trits = []
    rw [h2, List.ofFn_zero]
    rfl
  | .pos _ :: _, _, h => by
    rcases h _ List.mem_cons_self with e | e | e <;> cases e
  | .sealed :: _, _, h => by
    rcases h _ List.mem_cons_self with e | e | e <;> cases e

/-- **What the record of a round's typed values holds**, at an entry of the kind's sort. -/
theorem drawn_fit (e : Fmt.Entry) (k : Fmt.Kind) (he : EntOk e) (h1 : k ≠ .seeds) (h2 : k ≠ .sealed)
    (v : _root_.Run.Vals .two (Fmt.dsOf e k)) :
    (Fmt.collect (_root_.Run.outAll .two (Fmt.dsOf e k) v)).elems.length = e.drawE ∧
      (Fmt.collect (_root_.Run.outAll .two (Fmt.dsOf e k) v)).poss = [] ∧
      (Fmt.collect (_root_.Run.outAll .two (Fmt.dsOf e k) v)).trits = [] ∧
      (((Fmt.dsElems e k).zip (Fmt.collect (_root_.Run.outAll .two (Fmt.dsOf e k) v)).elems).all
        fun x => x.1 != .elemNZ || x.2 != (0, 0, 0)) = true := by
  obtain ⟨a1, _, a3, a4⟩ := he
  have d1 : Fmt.dsElems e k =
      List.replicate (e.drawE - e.drawNZ) Fmt.Draw.elem ++
        List.replicate e.drawNZ Fmt.Draw.elemNZ := by
    unfold Fmt.dsElems
    rw [if_neg h1]
  have d2 : Fmt.dsOf e k = Fmt.dsElems e k ++ [Fmt.Draw.trits 0] := by
    unfold Fmt.dsOf
    rw [a1, a3, if_neg h2]
    rfl
  have d3 : (Fmt.dsOf e k).filter isEl = Fmt.dsElems e k := by
    rw [d2, d1]
    simp [List.filter_append, isEl]
  obtain ⟨c1, c2⟩ := collect_fit (Fmt.dsOf e k) v
  obtain ⟨c3, c4⟩ := collect_rest (Fmt.dsOf e k) v (by
    intro d hd
    rw [d2, d1] at hd
    simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hd
    rcases hd with (⟨_, rfl⟩ | ⟨_, rfl⟩) | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl))
  rw [d3] at c1 c2
  refine ⟨?_, c3, c4, c2⟩
  rw [c1, d1, List.length_append, List.length_replicate, List.length_replicate]
  omega

/-- **At every written transcript of the kind's written rounds the view fits.** -/
theorem wr_fits : ∀ (l : List Fmt.DeclaredRound), (∀ r ∈ l, EntOk r.entry ∧ EntCut r.entry) →
    ∀ τ : Tr (uLT (ckP .two) (l.map wr)),
      roundsFit l (rvT (ckP .two) (l.map wr) τ) = true ∧
        Fits (l.map (·.entry)) ((rvT (ckP .two) (l.map wr) τ).map noDigest)
  | [], _, _ => ⟨rfl, trivial⟩
  | r :: l, h, (m, c, τ) => by
    obtain ⟨i1, i2⟩ := wr_fits l (fun x hx => h x (List.mem_cons_of_mem _ hx)) τ
    obtain ⟨ok, cut⟩ := h r List.mem_cons_self
    have hcut : r.items = List.replicate (r.entry.msg / 24) Fmt.Item.e := by
      show r.entry.cut = _
      unfold Fmt.Entry.cut
      rw [cut.answers, cut.roots]
      simp
    have hall : ∀ it ∈ r.items, it = Fmt.Item.e := fun it hi => by
      rw [hcut] at hi
      exact List.eq_of_mem_replicate hi
    have hk : Fmt.kindOf r.entry.name = some (wr r).kind := by
      show Fmt.kindOf r.entry.name = some ((Fmt.kindOf r.entry.name).getD .nothing)
      rcases cut.kind with e | e | e <;> rw [e] <;> rfl
    have k1 : (wr r).kind ≠ .seeds := by
      show (Fmt.kindOf r.entry.name).getD .nothing ≠ .seeds
      rcases cut.kind with e | e | e <;> rw [e] <;> decide
    have k2 : (wr r).kind ≠ .sealed := by
      show (Fmt.kindOf r.entry.name).getD .nothing ≠ .sealed
      rcases cut.kind with e | e | e <;> rw [e] <;> decide
    obtain ⟨g1, s, g2, g3⟩ := gots_allE r.items hall (GPlain.old (b := r.entry.work) m.2)
    obtain ⟨f1, f2, f3, f4⟩ := drawn_fit r.entry (wr r).kind ok k1 k2
      ((_root_.Run.bsRound .two r.entry (wr r).kind).φ (GChal.old (b := r.entry.work) c))
    have hfil : r.items.filter (· != .root) = r.items := by
      rw [List.filter_eq_self]
      intro it hi
      rw [hall it hi]
      rfl
    constructor
    · show roundsFit (r :: l) (⟨PlainOf.gots r.items (GPlain.old (b := r.entry.work) m.2),
        Fmt.collect (_root_.Run.outAll .two (Fmt.dsOf r.entry (wr r).kind)
          ((_root_.Run.bsRound .two r.entry (wr r).kind).φ (GChal.old (b := r.entry.work) c)))⟩ ::
        rvT (ckP .two) (l.map wr) τ) = true
      unfold roundsFit drawsMarkedNonzeroHaveNonzeroWords
      rw [i1, hk]
      simp only [g1, hfil, f1, f2, f3, ok.1, ok.2.2.1, Option.any_some, f4, List.length_nil,
        List.all_nil, beq_self_eq_true, Bool.and_self]
    · refine ⟨⟨⟨s, g2, ?_⟩, f1⟩, i2⟩
      rw [g3, hcut, List.length_replicate]
      obtain ⟨q, hq⟩ := cut.msg
      rw [hq]
      omega

theorem written_fits (p : Par) (τ : Tr (uLT (ckP .two) (written p))) :
    roundsFit (rounds p) (rvT (ckP .two) (written p) τ) = true ∧
      Fits ((rounds p).map (·.entry)) ((rvT (ckP .two) (written p) τ).map noDigest) :=
  wr_fits (rounds p)
    (fun r hr => ⟨rounds_ok p r.entry (List.mem_map_of_mem hr), rounds_cut p r hr⟩) τ

/-! ## A block that reads no column; a stretch that opens nothing -/

section
variable {S Cl W : Type} {C : CK} {F : Frame}

theorem groupsOf_none (ft : Nat) : ∀ (l : List Fmt.DeclaredRound) (R : List Fmt.Drawn),
    (∀ r ∈ l, r.stored = [] ∧ r.opens = []) → groupsOf ft l R = []
  | [], _, _ => by cases ‹List Fmt.Drawn› <;> rfl
  | _ :: _, [], _ => rfl
  | r :: l, D :: R, h => by
    obtain ⟨h1, h2⟩ := h r List.mem_cons_self
    unfold groupsOf
    rw [h1, h2, groupsOf_none ft l R fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

/-- Where the rounds fit, such a block is, as a step, its decision. -/
theorem step_of_decide (b : Block S Cl) (hb : ∀ r ∈ b.rounds, r.stored = [] ∧ r.opens = [])
    (ft : Nat) (s s' : S) (rs : List Fmt.RoundView) (hfit : roundsFit b.rounds rs = true)
    (hd : b.decide s (rs.map noDigest) [] = .ok s') : b.step ft s rs [] = .ok (s', 0) := by
  unfold Block.step
  rw [hfit, groupsOf_none ft b.rounds _ hb]
  simp only [need, List.flatMap_nil, List.length_nil, List.take_nil, List.map_nil, regroup]
  show (do let s' ← b.decide s (rs.map noDigest) []; pure (s', 0) : Except String (S × Nat)) = _
  rw [hd]
  rfl

theorem wants_none (a : ℕ) (dep : ℕ → Option ℕ) : ∀ (ds : List RDT) (R : List Fmt.Drawn),
    (∀ d ∈ ds, d.stored = [] ∧ d.opens = []) → wantsOf a dep ds R = []
  | [], _, _ => by cases ‹List Fmt.Drawn› <;> rfl
  | _ :: _, [], _ => rfl
  | d :: ds, D :: R, h => by
    obtain ⟨h1, h2⟩ := h d List.mem_cons_self
    unfold wantsOf
    rw [h1, h2, wants_none a dep ds R fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

theorem full_none : ∀ (ds : List RDT) (R : List Fmt.Drawn),
    (∀ d ∈ ds, d.stored = [] ∧ d.opens = []) → fullOf ds R = true
  | [], _, _ => by cases ‹List Fmt.Drawn› <;> rfl
  | _ :: _, [], _ => rfl
  | d :: ds, D :: R, h => by
    unfold fullOf
    rw [(h d List.mem_cons_self).1, full_none ds R fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

/-- **Where a piece whose stretch opens nothing puts out**: the converse of piece_out_step. -/
theorem piece_out_of_step (P : Piece C F S Cl W) (hb : P.back = [])
    (hn : ∀ d ∈ P.ds, d.stored = [] ∧ d.opens = []) (hl : P.b.rounds.length = P.ds.length)
    (a : S × F.E.Str) (τ : Tr (uLT C P.ds)) (s' : S)
    (hp : passT C P.ds (rhoT C P.ds τ) = true)
    (hs : P.b.step F.ft a.1 (rvT C P.ds τ) [] = .ok (s', 0)) :
    P.ior.red.out a τ = some (s', P.ior.imp a.2 τ) := by
  have hw : sWants C P.stage (rhoT C P.ds τ) = [] := wants_none _ _ _ _ hn
  have ht : sTests C P.stage a.2 τ = true := by
    unfold sTests
    rw [hw]
    show (passT C P.ds (rhoT C P.ds τ) && fullOf P.ds _ && sCarries P.stage a.2 []) = true
    rw [hp, full_none _ _ hn]
    rfl
  have hv : (sView C P.stage a.2 τ).opened = [] := by
    show List.filterMap _ (sWants C P.stage (rhoT C P.ds τ)) = []
    rw [hw]
    rfl
  have hlen : (rvT C P.ds τ).length = P.b.rounds.length := by
    rw [hl]
    exact Fo.Peel.rvT_length C P.ds τ
  have hc : chainAt P.b.name F.ft [P.b] a.1 ⟨rvT C P.ds τ, []⟩ = .ok s' := by
    unfold chainAt
    rw [if_neg (by simp)]
    have hf : foldBlocks F.ft [P.b] a.1 (rvT C P.ds τ) [] = .ok (s', [], []) := by
      simp only [foldBlocks, List.splitAt_eq, ← hlen, List.take_length, List.drop_length, ne_eq,
        not_true_eq_false, if_false, hs, List.drop_nil]
    simp only [hf]
  show ((if sTests C P.stage a.2 τ then P.run a.1 (sView C P.stage a.2 τ) else none).map fun xo =>
    (xo, P.ior.imp a.2 τ)) = _
  rw [if_pos ht]
  have hr : P.run a.1 (sView C P.stage a.2 τ) = some s' := by
    show (chainAt P.b.name F.ft [P.b] a.1
      ⟨rvT C P.ds τ ++ P.back, (sView C P.stage a.2 τ).opened⟩).toOption = some s'
    rw [hb, hv, List.append_nil, hc]
    rfl
  rw [hr]
  rfl

end

/-! ## At the kind's written rounds -/

section
variable {S Cl W : Type} {F : Frame}

theorem rounds_none (p : Par) : ∀ r ∈ rounds p, r.stored = [] ∧ r.opens = [] := by
  intro r hr
  unfold rounds at hr
  obtain ⟨e0, _, rfl⟩ := List.mem_map.1 hr
  exact ⟨rfl, rfl⟩

theorem written_none (p : Par) : ∀ d ∈ written p, d.stored = [] ∧ d.opens = [] := by
  intro d hd
  obtain ⟨r, _, rfl⟩ := List.mem_map.1 hd
  exact ⟨rfl, rfl⟩

theorem treeSh_none : ∀ (ds : List RDT), (∀ d ∈ ds, d.trees = []) → ∀ n, treeShT ds n = none
  | [], _, _ => rfl
  | d :: ds, h, n => by
    rw [treeShT_cons, h d List.mem_cons_self, List.length_nil, if_neg (Nat.not_lt_zero _)]
    exact treeSh_none ds (fun x hx => h x (List.mem_cons_of_mem _ hx)) _

theorem written_trees (p : Par) : ∀ d ∈ written p, d.trees = [] := by
  intro d hd
  obtain ⟨r, _, rfl⟩ := List.mem_map.1 hd
  rfl

/-- **The kind's piece is owed just its stretch** (Piece.Owed): as many written rounds as the block
declares; it reads no column and none is shown. -/
theorem seam_owed (seat : Seat S) (claims : List (String × (Nat → S → Except String (List Cl × S))))
    (p : Par) (base : ℕ) (err : Err (uLT (ckP .two) (written p))) :
    (k5Piece (W := W) (ckP .two) F seat claims p base (written p) err).Owed := by
  refine ⟨?_, fun y τ => ?_⟩
  · show (written p).length + 0 = (rounds p).length
    rw [written, List.length_map, Nat.add_zero]
  · show ((groupsOf F.ft (rounds p) _).flatMap id).length =
      (List.filterMap _ (wantsOf _ _ (written p) _)).length
    rw [groupsOf_none _ _ _ (rounds_none p), wants_none _ _ _ _ (written_none p)]
    rfl

/-- **Its trees are listed** (Piece.Listed): it sends none and opens none. -/
theorem seam_listed (seat : Seat S)
    (claims : List (String × (Nat → S → Except String (List Cl × S)))) (p : Par) (base : ℕ)
    (err : Err (uLT (ckP .two) (written p))) :
    (k5Piece (W := W) (ckP .two) F seat claims p base (written p) err).Listed := by
  refine ⟨fun n sh h => ?_, fun d hd j hj => ?_⟩
  · have h' : treeShT (written p) n = some sh := h
    rw [treeSh_none _ (written_trees p) n] at h'
    cases h'
  · have hd' : d ∈ written p := hd
    rw [(written_none p d hd').2] at hj
    cases hj

/-- It sends no tree: the next piece's base is this one's. -/
theorem seam_trees (seat : Seat S)
    (claims : List (String × (Nat → S → Except String (List Cl × S)))) (p : Par) (base : ℕ)
    (err : Err (uLT (ckP .two) (written p))) :
    (k5Piece (W := W) (ckP .two) F seat claims p base (written p) err).trees = 0 := by
  show ((written p).map (·.trees.length)).sum = 0
  rw [List.sum_eq_zero]
  intro x hx
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hx
  rw [written_trees p d hd]
  rfl

/-- **Any block with the kind's ROUNDS, at the kind's written rounds**: where the work passes it
puts
out just what its decision hands on. -/
theorem block_out (b : Block S Cl) (p : Par) (hb : b.rounds = rounds p) (base : ℕ)
    (ext : S × F.E.Str → Tr (uLT (ckP .two) (written p)) → W → W)
    (err : Err (uLT (ckP .two) (written p))) (a : S × F.E.Str)
    (τ : Tr (uLT (ckP .two) (written p))) (s' : S)
    (hp : passT (ckP .two) (written p) (rhoT (ckP .two) (written p) τ) = true)
    (hd : b.decide a.1 ((rvT (ckP .two) (written p) τ).map noDigest) [] = .ok s') :
    (⟨b, base, written p, [], ext, err⟩ : Piece (ckP .two) F S Cl W).ior.red.out a τ =
      some (s', (⟨b, base, written p, [], ext, err⟩ : Piece (ckP .two) F S Cl W).ior.imp a.2 τ) :=
  piece_out_of_step (⟨b, base, written p, [], ext, err⟩ : Piece (ckP .two) F S Cl W) rfl
    (written_none p)
    (by show b.rounds.length = (written p).length; rw [hb, written, List.length_map])
    a τ s' hp
    (step_of_decide b (by rw [hb]; exact rounds_none p) F.ft a.1 s' _
      (by rw [hb]; exact (written_fits p τ).1) hd)

/-- **THE KIND's OWN PIECE PUTS OUT AT EVERY WRITTEN TRANSCRIPT WHOSE WORK PASSES.** -/
theorem seam_accepts (seat : Seat S)
    (claims : List (String × (Nat → S → Except String (List Cl × S)))) (p : Par) (base : ℕ)
    (err : Err (uLT (ckP .two) (written p))) (hpl : planOk p = true) (a : S × F.E.Str) {F0 : Fork}
    (ho : seat.owed a.1 = none) (hl : seat.ledger a.1 = some F0) (hz : Sized F0)
    (hfree : MaskedSum.Free F0 F0.next (slotsOf (script p.own)))
    (hlay : ∀ h G, ∃ s', seat.lay a.1 h G = some s') (τ : Tr (uLT (ckP .two) (written p)))
    (hp : passT (ckP .two) (written p) (rhoT (ckP .two) (written p) τ) = true) :
    ∃ b, (k5Piece (W := W) (ckP .two) F seat claims p base (written p) err).ior.red.out a τ =
      some b := by
  obtain ⟨h, G, hh⟩ := hear_returns MaskedSum.partReturns p hpl hz (written_fits p τ).2 hfree
  obtain ⟨s', hs'⟩ := hlay h G
  exact ⟨_, block_out (attentionKind seat claims p) p rfl base (fun _ _ w => w) err a τ s' hp
    ((decide_lays seat p a.1 s' _).2 ⟨ho, F0, h, G, hl, hh, hs'⟩)⟩

/-- A written transcript whose work passes: the fixed messages; every bit of work 0. -/
noncomputable def passing (C : CK) : (ds : List RDT) → Tr (uLT C ds)
  | [] => ()
  | d :: ds => (((roundT C d).up.dOrc, (roundT C d).up.dPlain),
      GChal.zero d.entry.work (Classical.arbitrary (C.Ch d.entry d.kind)), passing C ds)

theorem passing_passes (C : CK) : ∀ ds : List RDT, passT C ds (rhoT C ds (passing C ds)) = true
  | [] => rfl
  | d :: ds => by
    show (GChal.pass (b := d.entry.work) (GChal.zero d.entry.work _) &&
      passT C ds (rhoT C ds (passing C ds))) = true
    rw [GChal.pass_zero, passing_passes C ds]
    rfl

/-- **There are (a, τ, b)**: the seam's theorems are not idle, at such a seat. -/
theorem seam_member (seat : Seat S)
    (claims : List (String × (Nat → S → Except String (List Cl × S)))) (p : Par) (base : ℕ)
    (err : Err (uLT (ckP .two) (written p))) (hpl : planOk p = true) (a : S × F.E.Str) {F0 : Fork}
    (ho : seat.owed a.1 = none) (hl : seat.ledger a.1 = some F0) (hz : Sized F0)
    (hfree : MaskedSum.Free F0 F0.next (slotsOf (script p.own)))
    (hlay : ∀ h G, ∃ s', seat.lay a.1 h G = some s') :
    ∃ τ b, (k5Piece (W := W) (ckP .two) F seat claims p base (written p) err).ior.red.out a τ =
      some b :=
  ⟨passing (ckP .two) (written p), seam_accepts seat claims p base err hpl a ho hl hz hfree hlay _
    (passing_passes _ _)⟩

/-- A ledger of n free slots. -/
def freshLedger (n : ℕ) : Fork :=
  { ns := n, vp := Array.replicate n zeroE, mf := Array.replicate n zeroE,
    gotF := Array.replicate n false }

/-- The seat at which the carried record is the ledger itself: nothing is owed; the ledger behind
the
hearing is laid. -/
def ledgerSeat : Seat Fork := ⟨some, fun _ => none, fun _ _ G => some G⟩

/-- **A closed member, at every place whose plan passes**: the seat's premises are met together. -/
theorem seam_member_fresh (claims : List (String × (Nat → Fork → Except String (List Cl × Fork))))
    (p : Par) (base : ℕ) (err : Err (uLT (ckP .two) (written p))) (hpl : planOk p = true)
    (y : F.E.Str) :
    ∃ τ b, (k5Piece (W := W) (ckP .two) F ledgerSeat claims p base (written p) err).ior.red.out
      (freshLedger (slotsOf (script p.own)), y) τ = some b :=
  seam_member ledgerSeat claims p base err hpl (freshLedger (slotsOf (script p.own)), y) rfl rfl
    ⟨Array.size_replicate, Array.size_replicate, Array.size_replicate⟩
    ⟨Array.size_replicate, Nat.le_of_eq (Nat.zero_add _), fun j _ hj => by
      have hj' : j < slotsOf (script p.own) := by
        have : j < 0 + slotsOf (script p.own) := hj
        omega
      show (Array.replicate (slotsOf (script p.own)) false).getD j true = false
      simp [Array.getD, hj']⟩
    (fun _ G => ⟨G, rfl⟩)

/-- A small place. -/
def toyPar : Par := ⟨0, 0, 0, ⟨1, 1, 1, 1, 2, [(1, 1), (1, 1)], 1, 1, 1, 1, 1, 1⟩, []⟩

/-- Its plan passes: so seam_member_fresh has a place. -/
theorem toy_planOk : planOk toyPar = true := by decide

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.written_fits
#print axioms VerifiableInference.Desc.First.Att.P.piece_out_of_step
#print axioms VerifiableInference.Desc.First.Att.P.seam_owed
#print axioms VerifiableInference.Desc.First.Att.P.seam_listed
#print axioms VerifiableInference.Desc.First.Att.P.seam_trees
#print axioms VerifiableInference.Desc.First.Att.P.block_out
#print axioms VerifiableInference.Desc.First.Att.P.seam_accepts
#print axioms VerifiableInference.Desc.First.Att.P.seam_member
#print axioms VerifiableInference.Desc.First.Att.P.seam_member_fresh
#print axioms VerifiableInference.Desc.First.Att.P.toy_planOk
