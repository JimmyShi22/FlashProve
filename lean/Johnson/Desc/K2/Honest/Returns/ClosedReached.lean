-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/ClosedReached.lean: AT A STATE THAT IS REACHED IN FRONT OF THE SWITCH
INTO A LATER GROUP, IN THE GOALS' SCOPE, THE WALK's FRAME IS WHAT THE LAST CLOSING RETURNED, AND THE
STATEMENT HAS GROWN OUT OF THE CLOSING's. SO WHAT THE LIBRARY SHOWS "RIGHT BEHIND THE CLOSING" HOLDS
IN FRONT OF THE SWITCH: ELEVEN CLAUSES OF THE LAW "THE KIND's OWN DECISION SAYS YES AT A SEGMENT's
FIRST PLACE" (`LinkPlain`, Returns/LinkSent.lean), WITH NO TEST ON THE PUBLIC PART: the eight of
`ReadFits` on the layout (challenges · maskVars · keptSize · mainSize · maskSize · fits · keptRows ·
fresh) and three of `OldFits` (mainVars · d0 · d1). Statements with their proofs: calls, one
recursion, cases.

  `closeFrame_shape` a yes of the frame's closing: the layout that it lays into the carried rows is
                    a fold's shape's that passed the test on shapes, at a statement out of which the
                    closing's own has grown; and the count of kept rows, as the program's text has
                    it
  `fold_keptCount` that text's loop is `keptCount`
  `grown_shape` a message keeps its shape where the statement grows
  `LayFits T old` the eight, at a statement and carried rows
  `layFits_of_close` `LayFits T x.1.rows` for what a closing returns, at every T grown out of its
                    statement: no state of the walk
  `LayFits.reads` the eight in `ReadFits`' own letters, at what the reading is handed
  `shut_st` the shutting leaves the statement
  `closed_behind_laid` THE BRIDGE, from the fold's return at the cut 14 (l + 1) + 2, l < 24
  `link_closed_reached` the like at a state reached over the wrapped list
  `link_lay_reached` `LayFits` at `frontAt s L Q`'s statement and carried rows, for all L and Q
  `link_carried_free` `OldFits.mainVars`, `d0`, `d1` there: Returns/PinReached.lean has them under
                    three named tests on the public part; here none is asked

By, all the library's: `closeFrame_iff`, `fold_iff` (Johnson/Desc/First/Close/Law/CloseMeans.lean) ·
`foldShapeFits_iff` (Johnson/Desc/Own/FoldMean.lean) · `fold_grows`, `framesOf_grows`
(Johnson/Goal/Meaning/GrowsSeated.lean) · `closeFrame_sizes`
(Johnson/Desc/First/Link/Law/CarriedSizes.lean) · `closeFrame_carried`
(Johnson/Desc/First/Close/Law/CarriedRows.lean) · `closeFrame_all`
(Johnson/Goal/Meaning/RecK10.lean) · `closing_yes`, `framesOf_clear` (Johnson/IMR/GroupTail.lean) ·
`shutting_opn`, `frame_walk_link`, `At.opn` (Johnson/IMR/FrameAll.lean) · `entry_at`,
`entry_at_zero` (Johnson/IMR/FrameEntry.lean) · `frame_of` (Johnson/IMR/FrameSeat.lean) · `close_of`
(Johnson/IMR/CloseSeat.lean) · `close_numbers` (Johnson/IMR/FirstSeats.lean) · `yes_alone`
(Johnson/IMR/SeatForm.lean) · `stand_putLink` (Johnson/Desc/First/Link/Law/RbDef.lean) ·
`layFront_ok` (Johnson/Top/H0/Walk/FrameLaw.lean) · `bindE` (Johnson/Goal/Meaning/RecRel.lean) ·
`fold_back`, `fold_next` (Johnson/IMR/FoldTools.lean) · `fold_cut` (Johnson/IMR/GroupRest.lean) ·
`reach_raw`, `Reach.fold` (Johnson/Top/H0/Walk/Reach.lean). Near relatives, not called: `tail_rows`
(Johnson/IMR/GroupTail.lean): at the same cut the layout's members and flags are the group's ·
`closing_opn` (Johnson/IMR/FrameAll.lean): the closing's seat, under "for some rows" ·
`first_behind_laid`, `owed_behind_laid` (Returns/FirstReached.lean, Returns/WaitsReached.lean): the
same walk, read for two other fields; its lines on the four seats stand here again; behind the
bridge the first of the two is `closeFrame_all`'s fourth clause.

Limits. The links' places alone. "Reached" is: over the list of the wrapped sub-protocols. THE
PREMISES IN FRONT ARE SHOWN MET TOGETHER BY NOBODY HERE: NO MEMBER. Not reached by this road:
`OldFits.rows`, `once`, `named`, `keptCode`, the test on the target, `TablesFit.bitsKept`. This
file's imports are heavy. Nothing on any property.



-/
import Johnson.Desc.K2.Honest.Returns.LinkReached
import Johnson.IMR.FrameAll
import Johnson.IMR.GroupTail
import Johnson.Goal.Meaning.GrowsSeated
import Johnson.Goal.Meaning.RecK10
import Johnson.Desc.First.Link.Law.CarriedSizes
import Johnson.Desc.First.Link.Law.RbDef

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (foldBlocks Block Chain FileDescription Grows)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (closeFrame closeFrame_iff fold_iff closeFrame_carried)
open VerifiableInference.Desc.LinkJoin (ColFits keptCount closeFrame_sizes stand_putLink)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open Johnson.Desc.First.Walk.Law (layFront_ok)
open Meaning.K2 (Opn frame_walk_link entry_at entry_at_zero framesOf_clear framesOf_grows
  fold_grows closing_yes shutting_opn closeFrame_all bindE fold_back fold_next fold_cut)
open _root_.Tw.K2 (SwIn)
open ProofFile (Cl)

/-! ## Right behind a closing: no state of the walk -/

/-- What a yes of the frame's closing says of the layout that it lays into the carried rows. -/
theorem closeFrame_shape {owed : Option Nat} {f : ReqFrame} {S₀ : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {x : ReqFrame × Statement}
    (h : closeFrame owed f S₀ es rs = .ok x) :
    ∃ (S₁ : Statement) (F : FoldShape), Own.FoldShapeFit S₁ F ∧ Grows S₁ x.2 ∧
      x.1.rows.layout = F.layout ∧
      x.1.rows.keptRows = (List.range F.layout.members.size).foldl (fun n i =>
        if F.layout.kept.getD i false then
          n + ((x.2.oracles[F.layout.members.getD i noId]?).map (·.shape.mainRows)).getD 0
        else n) 0 := by
  obtain ⟨-, Lk, -, Gf, -, -, rows, hc, e⟩ := (closeFrame_iff owed f S₀ es rs x.1 x.2).1 h
  obtain ⟨eB, es', rB, rs', -, -, m, -, row, L, S₁, -, -, hF⟩ := hc
  have hg := fold_grows ((fold_iff _ _ _ _ _ _ _ _).2 hF)
  obtain ⟨eE, eR, rE, rR, -, -, -, -, hshape, -, -, d2, -, sum, eps, -, -, gamma, claim, -, hout,
    hS'⟩ := hF
  refine ⟨S₁, _, (Own.foldShapeFits_iff _ _).1 hshape, hg, ?_, ?_⟩
  · rw [e]
    show rows.layout = _
    rw [hout]
    rfl
  · rw [e]
    show rows.keptRows = _
    rw [hout, hS']
    rfl

theorem fold_keptCount (L : GroupLayout) (a b : Nat → Nat) : ∀ (ws : List Nat) (n : Nat),
    (∀ w ∈ ws, a w = b w) →
    ws.foldl (fun n i => if L.kept.getD i false then n + a i else n) n = n + keptCount L b ws
  | [], n, _ => rfl
  | w :: ws, n, h => by
    rw [List.foldl_cons, fold_keptCount L a b ws _ fun v hv => h v (List.mem_cons_of_mem _ hv)]
    show _ = n + ((if L.kept.getD w false then b w else 0) + keptCount L b ws)
    rw [h w List.mem_cons_self]
    cases L.kept.getD w false
    · simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    · simp only [↓reduceIte]
      omega

/-- A message of a statement has its shape in every statement that has grown out of it. -/
theorem grown_shape {T T' : Statement} (hg : Grows T T') {o : Nat} {y : OnBytes.Oracle}
    (hy : T.oracles[o]? = some y) : (T'.oracles.getD o default).shape = y.shape := by
  obtain ⟨y', h1, h2, -⟩ := hg.2.2 o y hy
  rw [Array.getD_eq_getD_getElem?, h1]
  exact h2

/-- **Eight clauses of `ReadFits`** (Returns/Read.lean), at a statement T and carried rows: no field
of `LinkPlain`, but a bundle of eight of the thirteen of its field `reads`. -/
structure LayFits (T : Statement) (old : SingleRows) : Prop where
  challenges : old.gamma.length = old.layout.k
  maskVars : old.layout.h ≤ old.layout.k
  keptSize : old.layout.kept.size = old.layout.members.size
  mainSize : old.layout.mainFirst.size = old.layout.members.size
  maskSize : old.layout.maskFirst.size = old.layout.members.size
  fits : ∀ w (hw : w < old.layout.members.size), ColFits old.layout w
    (T.oracles.getD old.layout.members[w] default).shape.mainRows
    (T.oracles.getD old.layout.members[w] default).shape.maskRows
    (2 ^ old.layout.k) (2 ^ old.layout.h)
  keptRows : keptCount old.layout
    (fun w => (T.oracles.getD (old.layout.members.getD w 0) default).shape.mainRows)
    (List.range old.layout.members.size) = old.keptRows
  fresh : (T.oracles.getD old.fresh default).shape.maskRows = 2 ^ old.layout.h

/-- **The eight hold of what a closing returns, at every statement grown out of its own.** -/
theorem layFits_of_close {owed : Option Nat} {f : ReqFrame} {S₀ : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {x : ReqFrame × Statement}
    (h : closeFrame owed f S₀ es rs = .ok x) {T : Statement} (hg : Grows x.2 T) :
    LayFits T x.1.rows := by
  obtain ⟨S₁, F, ⟨c, zk, -, -, -, hk, -, -, s1, s2, s3, hmem, -⟩, g1, eL, eK⟩ := closeFrame_shape h
  obtain ⟨Gf, -, -, hgam, hk', hh', o, ho, hfr⟩ := closeFrame_sizes h
  have at_ : ∀ w (hw : w < F.layout.members.size) (d : Nat),
      F.layout.members.getD w d = F.layout.members[w] := fun w hw d => by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hw]
    rfl
  refine ⟨by rw [hgam, hk'], by rw [eL]; exact hk, by rw [eL]; exact s1, by rw [eL]; exact s2,
    by rw [eL]; exact s3, ?_, ?_, ?_⟩
  · rw [eL]
    intro w hw
    obtain ⟨y, hy, -, -, hmain, hmask⟩ := hmem w hw
    rw [at_ w hw] at hy
    rw [grown_shape (g1.trans hg) hy]
    constructor
    · cases hz : F.layout.maskFirst.getD w none with
      | none =>
        rw [hz] at hmask
        exact Or.inl hmask
      | some a =>
        rw [hz] at hmask
        exact Or.inr ⟨a, rfl, hmask.2⟩
    · cases hz : F.layout.mainFirst.getD w none with
      | none =>
        rw [hz] at hmain
        by_cases hkp : F.layout.kept.getD w false = true
        · exact Or.inl hkp
        · refine Or.inr (Or.inl ?_)
          by_contra hne
          exact hmain ⟨Nat.pos_of_ne_zero hne, by simpa using hkp⟩
      | some a =>
        rw [hz] at hmain
        exact Or.inr (Or.inr ⟨a, rfl, hmain.2⟩)
  · rw [eK, eL, fold_keptCount F.layout _
      (fun w => (T.oracles.getD (F.layout.members.getD w 0) default).shape.mainRows) _ 0
      (fun w hw => ?_), Nat.zero_add]
    have hw' : w < F.layout.members.size := List.mem_range.1 hw
    obtain ⟨y, hy, -⟩ := hmem w hw'
    obtain ⟨y₂, h2, e2, -⟩ := g1.2.2 _ y hy
    rw [h2]
    show y₂.shape.mainRows =
      (T.oracles.getD (F.layout.members.getD w 0) default).shape.mainRows
    rw [at_ w hw' 0, ← at_ w hw' noId, grown_shape (g1.trans hg) hy, e2]
  · rw [grown_shape hg ho, hfr, hh']

/-- The eight in `ReadFits`' own letters, at what the reading is handed. -/
theorem LayFits.reads {T : Statement} {old : SingleRows} (H : LayFits T old) {i : SwIn}
    (ho : i.old = old) (hs : i.st = T) :
    i.old.gamma.length = i.old.layout.k ∧ i.old.layout.h ≤ i.old.layout.k ∧
      i.old.layout.kept.size = i.old.layout.members.size ∧
      i.old.layout.mainFirst.size = i.old.layout.members.size ∧
      i.old.layout.maskFirst.size = i.old.layout.members.size ∧
      (∀ w (hw : w < i.old.layout.members.size), ColFits i.old.layout w
        (shapeAt i i.old.layout.members[w]).mainRows (shapeAt i i.old.layout.members[w]).maskRows
        (2 ^ i.old.layout.k) (2 ^ i.old.layout.h)) ∧
      keptCount i.old.layout (fun w => (shapeAt i (i.old.layout.members.getD w 0)).mainRows)
        (List.range i.old.layout.members.size) = i.old.keptRows ∧
      (shapeAt i i.old.fresh).maskRows = 2 ^ i.old.layout.h := by
  subst ho hs
  exact ⟨H.challenges, H.maskVars, H.keptSize, H.mainSize, H.maskSize, H.fits, H.keptRows, H.fresh⟩

/-! ## The walk from the closing to the next switch -/

/-- The shutting leaves the statement. -/
theorem shut_st {C : Type} (p : K9.Where) (piece : Nat) (s : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (s' : S)
    (h : (K9.shut (Cl := C) p piece).decide s rs gs = .ok s') : s'.st = s.st := by
  obtain ⟨L₁, -, h⟩ := bindE h
  cases h
  exact (stand_putLink s _).2.2.1

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **Behind "laid" of segment l + 1 the walk's frame is what the closing of segment l returned,
and the statement has grown out of the closing's.** -/
theorem closed_behind_laid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    ∃ (owed : Option Nat) (f : ReqFrame) (S₀ : Statement) (es : List Fmt.Entry)
      (rs : List Fmt.RoundView) (x : ReqFrame × Statement),
      closeFrame owed f S₀ es rs = .ok x ∧ t₀.check.frame = x.1 ∧ Grows x.2 t₀.st := by
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  -- "segment l + 1: laid" hands the state on
  obtain ⟨_, _, bL, _, _, -, -, -, -, efl, hlay, -, iL, -, dL, -⟩ := hfr (l + 1) (by omega)
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 14 * (l + 1) + 1) f₀
  obtain ⟨rsL, gsL, dl⟩ := fold_next iL fm f₀
  rw [dL] at dl
  have hlf := ((hlay tm t₀).1 dl).1
  rw [efl] at hlf
  obtain ⟨et, -⟩ := layFront_ok hlf
  -- "segment l: cleared"
  obtain ⟨Lk, g, _, _, bC, eL, hlen, hg, -, -, -, hclr, -, -, -, -, -, -, iC, -, dC⟩ :=
    hfr l (by omega)
  rw [if_neg (by omega : ¬ l = 24)] at hlen
  rw [hlen, show 14 * l + 7 + 7 = 14 * l + 13 + 1 by omega] at iC
  rw [show 14 * (l + 1) + 1 = 14 * l + 13 + 1 + 1 by omega] at fm
  obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := 14 * l + 13 + 1) fm
  obtain ⟨rsC, gsC, dc⟩ := fold_next iC fu fm
  rw [dC] at dc
  have hcf := ((hclr u tm).1 dc).1
  have hck := (framesOf_clear hfs g (List.mem_of_getElem? hg) u tm hcf).1
  have hgr : Grows u.st tm.st := (framesOf_grows hfs g (List.mem_of_getElem? hg)).2.2 u tm hcf
  -- the shutting and the closing
  obtain ⟨Lk', q, Q, eL', -, -, hall⟩ := IM.close_of hS hR O l (by omega)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain ⟨b₂, x₂, a1, a2, la₂⟩ := hall 2 .K9 rfl
  have j₂ := IM.close_numbers hS hR O (by omega : l < 25) eL a1
  have i₂ := j₂
  rw [hlen, show 14 * l + 7 + 4 + 2 = 14 * l + 13 by omega] at i₂
  rw [show 14 * l + Lk.hear.length + 4 + 2 = 14 * l + Lk.hear.length + 6 by omega] at j₂
  obtain ⟨v, Rv, Cv, fv⟩ := fold_back (k := 14 * l + 13) fu
  obtain ⟨rs₂, gs₂, d₂⟩ := fold_next i₂ fv fu
  have dx₂ : x₂.retype.decide v rs₂ gs₂ = .ok u :=
    ((IM.yes_alone la₂ (by intro k; cases k) v u rs₂ gs₂).1 d₂).1
  obtain rfl : K9.shut q (Q.piece + 1) = x₂ := Option.some.inj a2
  have est := shut_st (C := Unit) q (Q.piece + 1) v rs₂ gs₂ u dx₂
  obtain ⟨b₁, x₁, c1, c2, la₁⟩ := hall 1 .K10 rfl
  have i₁ := IM.close_numbers hS hR O (by omega : l < 25) eL c1
  rw [hlen, show 14 * l + 7 + 4 + 1 = 14 * l + 12 by omega] at i₁
  rw [show 14 * l + 13 = 14 * l + 12 + 1 by omega] at fv
  obtain ⟨w, Rw, Cw, fw⟩ := fold_back (k := 14 * l + 12) fv
  obtain ⟨rs₁, gs₁, d₁⟩ := fold_next i₁ fw fv
  have dx₁ : x₁.retype.decide w rs₁ gs₁ = .ok v :=
    ((IM.yes_alone la₁ (by intro k; cases k) w v rs₁ gs₁).1 d₁).1
  obtain rfl : K9.closing Q = x₁ := Option.some.inj c2
  -- in front of the closing a segment is open
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut (k := 14 * l + 3) 9
    (by rw [show 14 * l + 3 + 9 = 14 * l + 12 by omega]; exact fw)
  obtain ⟨t₃, r₃, c₃, g₃⟩ := fold_cut (k := 14 * l + 3 + 2) 7
    (by rw [show 14 * l + 3 + 2 + 7 = 14 * l + 12 by omega]; exact fw)
  obtain ⟨t₅, r₅, c₅, g₅⟩ := fold_cut (k := 14 * l + 3 + 4) 5
    (by rw [show 14 * l + 3 + 4 + 5 = 14 * l + 12 by omega]; exact fw)
  obtain ⟨f', H⟩ : ∃ f', Opn l f' t₁ := by
    rcases Nat.eq_zero_or_pos l with rfl | h1
    · obtain ⟨f', hA, -⟩ := entry_at_zero hS hR O f₁
      exact ⟨f', hA.opn⟩
    · obtain ⟨t₂, R₂, C₂, f₂⟩ := fold_back (k := 14 * l + 2) f₁
      obtain ⟨_, f', -, hA, -⟩ := entry_at hS hR O h1 h24 f₂ f₁
      exact ⟨f', hA.opn⟩
  obtain ⟨Lw, hLw, -, hLl⟩ := (frame_walk_link hS hR O h24 (n₃ := t₃.st.oracles.size)
    (n₅ := t₅.st.oracles.size) (fun t r q h => by rw [g₃] at h; cases h; rfl)
    (fun t r q h => by rw [g₅] at h; cases h; rfl) f₁ H).1 9 (by omega) w Rw Cw
    (by rw [show 14 * l + 3 + 9 = 14 * l + 12 by omega]; exact fw)
  obtain ⟨x, hx, hv, hvst⟩ := closing_yes (C := Unit) dx₁ hLw
  have Hv : Opn l x.1 v := ⟨_, hv, rfl, hLl⟩
  obtain ⟨Lu, hLu, hLuf, -⟩ := shutting_opn hS hR O (by omega : l < 25) eL j₂ d₂ Hv
  refine ⟨_, _, _, _, _, x, hx, ?_, ?_⟩
  · rw [et, hck]
    unfold S.live
    rw [hLu]
    exact hLuf
  · rw [et, ← hvst, ← est]
    exact hgr

/-- The like at a reached state. -/
theorem link_closed_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m : Nat} (h23 : m < 23) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s)) :
    ∃ (owed : Option Nat) (f : ReqFrame) (S₀ : Statement) (es : List Fmt.Entry)
      (rs : List Fmt.RoundView) (x : ReqFrame × Statement),
      closeFrame owed f S₀ es rs = .ok x ∧ s.check.frame = x.1 ∧ Grows x.2 s.st := by
  obtain ⟨-, rs, cols, hf⟩ := (reach_raw hr).fold
  exact closed_behind_laid hS hR O (by omega) hf

/-- **The eight of `ReadFits` on the layout, at the front's statement and carried rows.** -/
theorem link_lay_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m : Nat} (h23 : m < 23) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (L : Params.ReqLink) (Q : ReqGroup) :
    LayFits (frontAt s L Q).st (frontAt s L Q).f.rows := by
  obtain ⟨owed, f, S₀, es, rs, x, hx, hf, hg⟩ := link_closed_reached hS hR O h23 hr
  have H := layFits_of_close hx hg
  rw [← hf] at H
  exact ⟨H.challenges, H.maskVars, H.keptSize, H.mainSize, H.maskSize, H.fits, H.keptRows, H.fresh⟩

/-- **`OldFits.mainVars`, `d0`, `d1` with no test on the public part.** -/
theorem link_carried_free (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m : Nat} (h23 : m < 23) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (L : Params.ReqLink) (Q : ReqGroup) :
    (∀ v ∈ (frontAt s L Q).f.rows.c.tensors, v.vars =
        ((frontAt s L Q).st.codes.base.getD (frontAt s L Q).f.rows.code default).logEll) ∧
      ((frontAt s L Q).f.rows.d.getD 0 #[]).size ≤
        ((frontAt s L Q).st.codes.mask.getD (frontAt s L Q).f.rows.maskCode default).ell ∧
      ((frontAt s L Q).f.rows.d.getD 1 #[]).size ≤
        ((frontAt s L Q).st.codes.mask.getD (frontAt s L Q).f.rows.maskCode default).ell := by
  obtain ⟨owed, f, S₀, es, rs, x, hx, hf, hg⟩ := link_closed_reached hS hR O h23 hr
  obtain ⟨Gf, G, -, -, CO⟩ := closeFrame_carried hx
  obtain ⟨-, -, -, -, -, hcode, hmask, -, -⟩ := closeFrame_all (f' := x.1) (S' := x.2) hx
  show (∀ v ∈ s.check.frame.rows.c.tensors, v.vars =
      (s.st.codes.base.getD s.check.frame.rows.code default).logEll) ∧
    (s.check.frame.rows.d.getD 0 #[]).size ≤
      (s.st.codes.mask.getD s.check.frame.rows.maskCode default).ell ∧
    (s.check.frame.rows.d.getD 1 #[]).size ≤
      (s.st.codes.mask.getD s.check.frame.rows.maskCode default).ell
  rw [hf, hg.1, hcode, hmask]
  exact ⟨CO.vars, le_of_eq CO.d0, le_of_eq CO.d1⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.closeFrame_shape
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fold_keptCount
#print axioms VerifiableInference.Desc.K2.Honest.Returns.grown_shape
#print axioms VerifiableInference.Desc.K2.Honest.Returns.layFits_of_close
#print axioms VerifiableInference.Desc.K2.Honest.Returns.LayFits.reads
#print axioms VerifiableInference.Desc.K2.Honest.Returns.shut_st
#print axioms VerifiableInference.Desc.K2.Honest.Returns.closed_behind_laid
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_closed_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_lay_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_carried_free
