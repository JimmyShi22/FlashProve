-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadPoint.lean: one point serves all lookup calls of the output head: from the
verifier's own routine that hears the sub-proof's messages.

Johnson/Road/HeadLines.lean asks two things of the key point of a segment's call: the coordinates of
the columns end in the coordinates low of a block's features (in the record SegFit), and the
coordinates of the positions are u (the record PosFit). Johnson/Road/HeadLaid.lean shows the public
half of SegFit (SegLaid). This file shows the half on the point, and PosFit, of what the routine
hear (OnBytes/Model/HeadHeard.lean) returns in a run on a view, with
  low := the coordinates of x.Zl,   u j := coordinate ls + j of x.Zl,
where x.Zl is the last la = ls + lt coordinates of the lookup's point.

How. If hear succeeds, each of its steps has succeeded. Two tests matter. Forest.pad tests that each
call's key point has as many coordinates as the call's record says (a public condition), and the
layout writes lJ + lt there. mergedPoint tests that every call's key point ends in x.Zl. That is a
test on values: the dry run skips it. So the statements are on a run on a view.

What is left to another file. The record HeardFits gathers what is used of what hear returns. That
hear's value has it, in a run on a view, is shown in Johnson/Road/HeadView.lean: mergedPoint runs
after the lookup's routine, and its test counts only if the context is then still a view's.

Main definitions: HeardFits (what is used of what hear returns).
Main theorems: bind_ok, must_bind, test_bind, getAs_bind (how a routine that succeeds is taken
apart); testAs_view; replyToken_ok, mergedPoint_ok, pad_ok; hear_steps (hear, step by step, and
nothing else); clN_of_layout (the calls' records hold lJ + lt); zk_size, zk_end, Zl_size, Zl_parts;
point_of_call; segFit_of_run, posFit_of_run.

What is not claimed. That hear succeeds is a hypothesis. Nothing is said on the dry run, on what the
sumchecks that hear passes through show, or on how the point was drawn. The program does not import
this file.
-/
import Johnson.Road.HeadLaid
import Johnson.Road.FormsKeysShape
import OnBytes.Iop.GroundLaws
import OnBytes.Slice.BlkCalls

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open OnBytes.Model (Reading Fork SubM)

/-! ## A routine that succeeds, taken apart -/

/-- One routine after another. -/
theorem bind_ok {α β : Type} {m : SubM α} {f : α → SubM β} {F G : Fork} {C D : Ctx} {b : β}
    (h : Ok (m >>= f) F C b G D) : ∃ a F1 C1, Ok m F C a F1 C1 ∧ Ok (f a) F1 C1 b G D :=
  (ok_bind m f F G C D b).1 h

/-- A routine that returns a value at once. -/
theorem pure_ok {α : Type} {a b : α} {F G : Fork} {C D : Ctx}
    (h : Ok (pure a : SubM α) F C b G D) : b = a ∧ G = F ∧ D = C :=
  (ok_pure a b F G C D).1 h

/-- A public condition and what follows it. -/
theorem must_bind {β : Type} {n : String} {b : Bool} {f : Unit → SubM β} {F G : Fork} {C D : Ctx}
    {y : β} (h : Ok ((liftM (Model.mustAs n b) : SubM Unit) >>= f) F C y G D) :
    b = true ∧ Ok (f ()) F C y G D := by
  obtain ⟨u, F1, C1, h1, h2⟩ := bind_ok h
  obtain ⟨e1, rfl⟩ := (ok_lift _ _ _ _ _ _).1 h1
  obtain ⟨e2, rfl⟩ := (mustAs_ok _ _ _ _ _).1 e1
  exact ⟨e2, h2⟩

/-- A condition on values that passes in a run on a view was true, and it changes nothing. -/
theorem testAs_view (n : String) (b : Bool) (C D : Ctx) (u : Unit) (hd : C.ch.dry = false)
    (h : Model.testAs n b C = .ok (u, D)) : b = true ∧ D = C := by
  have h1 : (Model.testAs n b).Yields C u D := (Blk.yields_iff _ _ _ _).2 h
  unfold Model.testAs at h1
  rw [Blk.yields_bind] at h1
  obtain ⟨d, C1, k1, k2⟩ := h1
  obtain ⟨rfl, rfl⟩ := (Slice.yields_isDry _ _ _).1 k1
  rw [hd, Bool.or_false] at k2
  cases b with
  | true => exact ⟨rfl, ((Blk.yields_pure _ _ _ _).1 k2).2⟩
  | false =>
    have k3 : (Except.error { name := n } : Except Failure (Unit × Ctx)) = .ok (u, D) :=
      (Blk.yields_iff _ _ _ _).1 k2
    cases k3

/-- A condition on values and what follows it, in a run on a view. -/
theorem test_bind {β : Type} {n : String} {b : Bool} {f : Unit → SubM β} {F G : Fork} {C D : Ctx}
    {y : β} (hd : C.ch.dry = false)
    (h : Ok ((liftM (Model.testAs n b) : SubM Unit) >>= f) F C y G D) :
    b = true ∧ Ok (f ()) F C y G D := by
  obtain ⟨u, F1, C1, h1, h2⟩ := bind_ok h
  obtain ⟨e1, rfl⟩ := (ok_lift _ _ _ _ _ _).1 h1
  obtain ⟨e2, rfl⟩ := testAs_view _ _ _ _ _ hd e1
  exact ⟨e2, h2⟩

/-- Unwrapping an optional value, and what follows it. -/
theorem getAs_bind {α β : Type} {n : String} {x : Option α} {f : α → SubM β} {F G : Fork}
    {C D : Ctx} {y : β} (h : Ok ((liftM (Model.Head.getAs n x) : SubM α) >>= f) F C y G D) :
    ∃ a, x = some a ∧ Ok (f a) F C y G D := by
  obtain ⟨a, F1, C1, h1, h2⟩ := bind_ok h
  obtain ⟨e1, rfl⟩ := (ok_lift _ _ _ _ _ _).1 h1
  obtain ⟨e2, rfl⟩ := (getAs_ok _ _ _ _ _).1 e1
  exact ⟨a, e2, h2⟩

/-- Unwrapping an optional value by the routine of the sub-proof's type. -/
theorem subGet_ok {α : Type} {x : Option α} {F G : Fork} {C D : Ctx} {a : α}
    (h : Ok (SubM.get x) F C a G D) : x = some a ∧ G = F ∧ D = C := by
  obtain ⟨e, rfl⟩ := (ok_lift (Blk.get x) F G C D a).1 h
  obtain ⟨e2, rfl⟩ := (Blk.yields_get x a C D).1 ((Blk.yields_iff _ _ _ _).2 e)
  exact ⟨e2, rfl, rfl⟩

/-! ## The steps of hear that matter -/

/-- The reply's token, in a run on a view: an entry of the vocabulary; state and context are
left. -/
theorem replyToken_ok {plain : Array E} {V y : ℕ} {F G : Fork} {C D : Ctx}
    (hd : C.ch.dry = false) (h : Ok (Model.Head.replyToken plain V) F C y G D) :
    y < V ∧ G = F ∧ D = C := by
  unfold Model.Head.replyToken at h
  obtain ⟨-, h⟩ := must_bind h
  obtain ⟨e, h⟩ := test_bind hd h
  obtain ⟨rfl, e1, e2⟩ := pure_ok h
  exact ⟨of_decide_eq_true (and_true_split e).2, e1, e2⟩

/-- The last la coordinates of the lookup's point, in a run on a view: every call's key point ends
in them. -/
theorem mergedPoint_ok {h : Model.Head.Shape} {g1 : Model.Forest.Heard} {Zl : Array E}
    {F G : Fork} {C D : Ctx} (hd : C.ch.dry = false)
    (hm : Ok (Model.Head.mergedPoint h g1) F C Zl G D) :
    Model.lastOf g1.zx h.la = .ok Zl ∧
      (g1.zk.all fun zk => zk.extract (zk.size - h.la) zk.size == Zl) = true := by
  unfold Model.Head.mergedPoint at hm
  obtain ⟨Z, F1, C1, h1, h2⟩ := bind_ok hm
  clear hm
  obtain ⟨e1, rfl⟩ := (ok_lift _ _ _ _ _ _).1 h1
  obtain ⟨e2, rfl⟩ := (held_ok _ _ _ _).1 e1
  obtain ⟨e3, h3⟩ := test_bind hd h2
  obtain ⟨rfl, -, -⟩ := pure_ok h3
  exact ⟨e2, e3⟩

/-- The lookup's routine: the numbers are those that Forest.shape returns on the calls' records;
there is one key point for each call; and each has as many coordinates as its call's record says. -/
theorem pad_ok {calls : Array Model.Call} {pub : Array ℕ} {lid : ℕ} {F G : Fork} {C D : Ctx}
    {g : Model.Forest.Heard} (h : Ok (Model.Forest.pad calls pub lid) F C g G D) :
    ∃ h0, Model.Forest.shape calls lid = .ok h0 ∧ g.zk.size = h0.NC ∧
      ((List.range h0.NC).all fun c =>
        (g.zk.getD c #[]).size == ((h0.calls[c]?).map (·.n)).getD 0) = true := by
  unfold Model.Forest.pad at h
  obtain ⟨h0, _, _, k, h⟩ := bind_ok h
  obtain ⟨e0, -, -⟩ := subGet_ok k
  obtain ⟨_, _, _, -, h⟩ := bind_ok h
  obtain ⟨slot0, _, _, -, h⟩ := bind_ok h
  obtain ⟨o1, _, _, -, h⟩ := bind_ok h
  obtain ⟨o2, _, _, -, h⟩ := bind_ok h
  obtain ⟨o3, _, _, -, h⟩ := bind_ok h
  obtain ⟨⟨theta, alpha, a⟩, _, _, -, h⟩ := bind_ok h
  obtain ⟨t, _, _, -, h⟩ := bind_ok h
  obtain ⟨keys, _, _, -, h⟩ := bind_ok h
  obtain ⟨table, _, _, -, h⟩ := bind_ok h
  obtain ⟨-, h⟩ := must_bind h
  obtain ⟨leaves, _, _, -, h⟩ := bind_ok h
  obtain ⟨⟨zb0, leaves'⟩, _, _, -, h⟩ := bind_ok h
  obtain ⟨r5, _, _, -, h⟩ := bind_ok h
  obtain ⟨bits, _, _, -, h⟩ := bind_ok h
  obtain ⟨⟨zb1, bits'⟩, _, _, -, h⟩ := bind_ok h
  obtain ⟨⟨sBit, bits''⟩, _, _, -, h⟩ := bind_ok h
  obtain ⟨vBit, _, _, -, h⟩ := bind_ok h
  obtain ⟨⟨bitsRow, p'⟩, _, _, -, h⟩ := bind_ok h
  obtain ⟨s, _, _, -, h⟩ := bind_ok h
  obtain ⟨-, h⟩ := must_bind h
  obtain ⟨-, h⟩ := must_bind h
  obtain ⟨e, h⟩ := must_bind h
  obtain ⟨rfl, -, -⟩ := pure_ok h
  exact ⟨h0, ok_of_toOption e0, by simp, e⟩

/-- What is used of what hear returns, for the shape h, the layout L and the covered positions. -/
structure HeardFits (h : Model.Head.Shape) (L : Model.Head.HL) (cov : Model.Head.Covered)
    (x : Model.Head.Heard) : Prop where
  /-- the checked tokens, with the prover's token, an entry of the vocabulary -/
  win : ∃ yTok, yTok < h.V ∧ x.win = Model.Head.winOf cov h.T yTok
  /-- the lookup's test on the lengths of the calls' key points -/
  sizes : ∃ h0, Model.Forest.shape L.cl h.LIDB = .ok h0 ∧ x.g1.zk.size = h0.NC ∧
    ((List.range h0.NC).all fun c =>
      (x.g1.zk.getD c #[]).size == ((h0.calls[c]?).map (·.n)).getD 0) = true
  /-- the last la coordinates of the lookup's point -/
  Zl : Model.lastOf x.g1.zx h.la = .ok x.Zl
  /-- every call's key point ends in them -/
  ends : (x.g1.zk.all fun zk => zk.extract (zk.size - h.la) zk.size == x.Zl) = true
  /-- the two calls that the run knows by number -/
  qN : Model.Head.callNo L "NF" = some x.qN
  qH : Model.Head.callNo L "HD0" = some x.qH

/-- Keeping an intermediate value leaves the state. -/
theorem noteH_state {w : String} {v : E} {F G : Fork} {C D : Ctx} {u : Unit}
    (h : Ok (Model.Head.noteH w v) F C u G D) : F = G :=
  ((ok_lift _ _ _ _ _ _).1 h).2.symm

/-- **The routine hear, taken apart**: if it succeeds, each of its steps has succeeded, from the
state and the context that the step before has left, and what it returns is the record of the
steps' values. Nothing else is said. -/
theorem hear_steps {h : Model.Head.Shape} {L : Model.Head.HL} {hp : Model.Head.HPlanH2}
    {cov : Model.Head.Covered} {plain : Array E} {x : Model.Head.Heard} {F G : Fork} {C D : Ctx}
    (hx : Ok (Model.Head.hear h L hp cov plain) F C x G D) :
    ∃ yTok F1 C1 F2 C2 g1 F3 C3 Zl F4 C4 PV F5 C5 sW gp wpl F6 C6 sPv omV tV F7 C7 qN qH tN F8 C8
      tH rs F9 C9,
      Ok (Model.Head.replyToken plain h.V) F C yTok F1 C1 ∧
      Ok (SubM.slots hp.ns) F1 C1 () F2 C2 ∧
      Ok (Model.Forest.pad L.cl L.fs.pub h.LIDB) F2 C2 g1 F3 C3 ∧
      Ok (Model.Head.mergedPoint h g1) F3 C3 Zl F4 C4 ∧
      Ok (SubM.point .zero h.lt) F4 C4 PV F5 C5 ∧
      Ok (Model.Head.hearSquares h PV) F5 C5 (sW, gp, wpl) F6 C6 ∧
      Ok (Model.Head.hearProducts h PV) F6 C6 (sPv, omV, tV) F7 C7 ∧
      Model.Head.callNo L "NF" = some qN ∧ Model.Head.callNo L "HD0" = some qH ∧
      Ok (Model.Head.hearStream h (Model.Head.ztOf h L g1 qN)) F7 C7 tN F8 C8 ∧
      Ok (Model.Head.hearLogits h hp.lamS (Model.Head.ztOf h L g1 qH)) F8 C8 (tH, rs) F9 C9 ∧
      G = F9 ∧
      x = { win := Model.Head.winOf cov h.T yTok, g1 := g1, Zl := Zl, PV := PV, sW := sW,
            gp := gp, wpl := wpl, sPv := sPv, omV := omV, tV := tV, tN := tN, tH := tH, rs := rs,
            qN := qN, qH := qH } := by
  unfold Model.Head.hear at hx
  obtain ⟨yTok, F1, C1, k1, hx⟩ := bind_ok hx
  obtain ⟨u2, F2, C2, k2, hx⟩ := bind_ok hx
  obtain ⟨g1, F3, C3, k3, hx⟩ := bind_ok hx
  obtain ⟨Zl, F4, C4, k4, hx⟩ := bind_ok hx
  obtain ⟨PV, F5, C5, k5, hx⟩ := bind_ok hx
  obtain ⟨⟨sW, gp, wpl⟩, F6, C6, k6, hx⟩ := bind_ok hx
  obtain ⟨⟨sPv, omV, tV⟩, F7, C7, k7, hx⟩ := bind_ok hx
  obtain ⟨qN, hqN, hx⟩ := getAs_bind hx
  obtain ⟨qH, hqH, hx⟩ := getAs_bind hx
  obtain ⟨tN, F8, C8, k8, hx⟩ := bind_ok hx
  obtain ⟨⟨tH, rs⟩, F9, C9, k9, hx⟩ := bind_ok hx
  obtain ⟨_, A1, _, n1, hx⟩ := bind_ok hx
  obtain rfl := noteH_state n1
  obtain ⟨_, A2, _, n2, hx⟩ := bind_ok hx
  obtain rfl := noteH_state n2
  obtain ⟨_, A3, _, n3, hx⟩ := bind_ok hx
  obtain rfl := noteH_state n3
  obtain ⟨_, A4, _, n4, hx⟩ := bind_ok hx
  obtain rfl := noteH_state n4
  obtain ⟨_, A5, _, n5, hx⟩ := bind_ok hx
  obtain rfl := noteH_state n5
  obtain ⟨_, A6, _, n6, hx⟩ := bind_ok hx
  obtain rfl := noteH_state n6
  obtain ⟨_, A7, _, n7, hx⟩ := bind_ok hx
  obtain rfl := noteH_state n7
  obtain ⟨_, A8, _, n8, hx⟩ := bind_ok hx
  obtain rfl := noteH_state n8
  obtain ⟨_, A9, _, n9, hx⟩ := bind_ok hx
  obtain rfl := noteH_state n9
  obtain ⟨_, A10, _, n10, hx⟩ := bind_ok hx
  obtain rfl := noteH_state n10
  obtain ⟨_, A11, _, n11, hx⟩ := bind_ok hx
  obtain rfl := noteH_state n11
  obtain ⟨_, A12, _, n12, hx⟩ := bind_ok hx
  obtain rfl := noteH_state n12
  obtain ⟨ex, eG, -⟩ := pure_ok hx
  exact ⟨yTok, F1, C1, F2, C2, g1, F3, C3, Zl, F4, C4, PV, F5, C5, sW, gp, wpl, F6, C6, sPv, omV,
    tV, F7, C7, qN, qH, tN, F8, C8, tH, rs, F9, C9, k1, k2, k3, k4, k5, k6, k7, hqN, hqH, k8, k9,
    eG, ex⟩

/-! ## The calls' records -/

/-- The lookup's record of one call, as the function lookups writes it. -/
def callRec (h : Model.Head.Shape) (tauFC tauFE : Array F) (c : Model.CallD) : Model.Call :=
  let base : Model.Call :=
    { name := c.name, n := Model.Head.callBits h c, kappa := 5,
      k := if c.kind == "R8" then 8 else 16 }
  if c.kind == "FC" then { base with fn := 1, t0 := 32768, tau := some tauFC }
  else if c.kind == "FE" then { base with fn := 1, t0 := 0, tau := some tauFE }
  else base

/-- The function lookups writes one such record for each call. -/
theorem lookups_eq (h : Model.Head.Shape) (tauFC tauFE : Array F) (cs : List Model.CallD) :
    Model.Head.lookups h tauFC tauFE cs = (cs.map (callRec h tauFC tauFE)).toArray := rfl

/-- A call's record says: lJ + lt bits of a key's number. -/
theorem callRec_n (h : Model.Head.Shape) (tauFC tauFE : Array F) (c : Model.CallD) :
    (callRec h tauFC tauFE c).n = c.lJ + h.lt := by
  unfold callRec
  dsimp only
  split
  · rfl
  · split <;> rfl

/-- **The records of a layout that the verifier returns**: one for each call, and the record of
call q says lJ + lt. -/
theorem clN_of_layout {h : Model.Head.Shape} {tauFC : Array F} {L : Model.Head.HL}
    (hy : Model.Head.layout h tauFC = .ok L) :
    L.cl.size = L.calls.size ∧ ∀ q, q < L.calls.size →
      ((L.cl[q]?).map (·.n)).getD 0 = (L.calls.getD q default).lJ + h.lt := by
  unfold Model.Head.layout at hy
  obtain ⟨-, hy⟩ := ok_of_needed hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨L0, -, hy⟩ := ok_of_bind hy
  obtain ⟨cs, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_needed hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨fs, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_needed hy
  obtain ⟨kb, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨pub, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_needed hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  cases hy
  refine ⟨?_, fun q hq => ?_⟩
  · show ((Model.Head.lookups h tauFC (Model.Head.tauFEOf h.famF h.digSh h.tabS) cs).mapIdx
      fun q c => { c with iota := fs.iota.getD q 0 }).size = cs.toArray.size
    rw [lookups_eq]
    simp
  · have hq' : q < cs.length := by simpa using hq
    have e1 : (((cs.map (callRec h tauFC (Model.Head.tauFEOf h.famF h.digSh h.tabS))).toArray.mapIdx
        fun q c => { c with iota := fs.iota.getD q 0 })[q]?) =
        some { callRec h tauFC (Model.Head.tauFEOf h.famF h.digSh h.tabS) cs[q] with
          iota := fs.iota.getD q 0 } := by
      simp [hq']
    have e2 : cs.toArray.getD q default = cs[q] := by simp [Array.getD, hq']
    show ((((cs.map (callRec h tauFC (Model.Head.tauFEOf h.famF h.digSh h.tabS))).toArray.mapIdx
      fun q c => { c with iota := fs.iota.getD q 0 })[q]?).map (·.n)).getD 0 =
      (cs.toArray.getD q default).lJ + h.lt
    rw [e1, e2]
    exact callRec_n h tauFC _ cs[q]

/-! ## The point -/

/-- A search in an array finds what the search in its list finds. -/
theorem findIdx_toList {α : Type} (xs : Array α) (p : α → Bool) :
    xs.findIdx? p = xs.toList.findIdx? p := by
  cases xs
  simp

/-- The number of the call with a segment is the number of a call. -/
theorem callNo_lt {L : Model.Head.HL} {sn : String} {q : ℕ}
    (h : Model.Head.callNo L sn = some q) : q < L.calls.size := by
  unfold Model.Head.callNo at h
  rw [findIdx_toList, List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hq, -⟩ := h
  simpa using hq

/-- One more of the tests on the shape's words: a block's rows are the bits of a feature in its
block, then those of a position. -/
theorem AdmittedH.la_eq {h : Model.Head.Shape} {L : Model.Head.HL} (A : AdmittedH h L) :
    h.la = h.ls + h.lt := by
  have e := A.adm
  unfold Model.Head.admitted at e
  have p17 := and_true_split e
  have p16 := and_true_split p17.1
  have p15 := and_true_split p16.1
  have p14 := and_true_split p15.1
  have p13 := and_true_split p14.1
  have p12 := and_true_split p13.1
  have p11 := and_true_split p12.1
  have p10 := and_true_split p11.1
  have p9 := and_true_split p10.1
  have p8 := and_true_split p9.1
  have p7 := and_true_split p8.1
  have p6 := and_true_split p7.1
  have p5 := and_true_split p6.1
  have k : h.lt < h.la := of_decide_eq_true p5.2
  unfold Model.Head.Shape.ls
  omega

/-- A point z of lJ + lt coordinates that ends in the la = ls + lt coordinates Zl, cut into its
first lJ and its last lt coordinates. -/
theorem point_parts {K : Type} [Field K] (ρ : Reading K) {z Zl : Array E} {lJ ls lt la : ℕ}
    (hs : z.size = lJ + lt) (hla : la = ls + lt) (hl : ls ≤ lJ)
    (he : z.extract (z.size - la) z.size = Zl) :
    (z.extract 0 lJ).size = lJ ∧
    (∀ j, j < ls → pt ρ (z.extract 0 lJ) (lJ - ls + j) = pt ρ Zl j) ∧
    (z.extract lJ (lJ + lt)).size = lt ∧
    ∀ j, j < lt → pt ρ (z.extract lJ (lJ + lt)) j = pt ρ Zl (ls + j) := by
  subst he
  refine ⟨by rw [Array.size_extract]; omega, fun j hj => ?_, by rw [Array.size_extract]; omega,
    fun j hj => ?_⟩
  · unfold pt
    rw [getD_extract z (by omega) (by omega), getD_extract z (Nat.le_refl _) (by omega)]
    have e : 0 + (lJ - ls + j) = z.size - la + j := by omega
    rw [e]
  · unfold pt
    rw [getD_extract z (by omega) (by omega), getD_extract z (Nat.le_refl _) (by omega)]
    have e : lJ + j = z.size - la + (ls + j) := by omega
    rw [e]

section Point
variable {h : Model.Head.Shape} {tauFC : Array F} {L : Model.Head.HL}
  {cov : Model.Head.Covered} {x : Model.Head.Heard}
  (hy : Model.Head.layout h tauFC = .ok L) (X : HeardFits h L cov x)
include hy X

/-- The key point of call q has lJ + lt coordinates, and it is there. -/
theorem zk_size {q : ℕ} (hq : q < L.calls.size) :
    q < x.g1.zk.size ∧ (x.g1.zk.getD q #[]).size = (L.calls.getD q default).lJ + h.lt := by
  obtain ⟨h0, hs, hz, hall⟩ := X.sizes
  obtain ⟨a, b⟩ := shape_calls hs
  obtain ⟨c1, c2⟩ := clN_of_layout hy
  have hq0 : q < h0.NC := by rw [b, c1]; exact hq
  have k : ((x.g1.zk.getD q #[]).size == ((h0.calls[q]?).map (·.n)).getD 0) = true :=
    List.all_eq_true.mp hall q (List.mem_range.mpr hq0)
  rw [a, c2 q hq] at k
  exact ⟨by rw [hz]; exact hq0, eq_of_beq k⟩

/-- The key point of call q ends in x.Zl. -/
theorem zk_end {q : ℕ} (hq : q < L.calls.size) :
    (x.g1.zk.getD q #[]).extract ((x.g1.zk.getD q #[]).size - h.la) (x.g1.zk.getD q #[]).size =
      x.Zl := by
  have hz := (zk_size hy X hq).1
  have k := Array.all_eq_true.mp X.ends q hz
  have e : x.g1.zk.getD q #[] = x.g1.zk[q] := by simp [Array.getD, hz]
  rw [e]
  exact eq_of_beq k

omit hy in
/-- x.Zl has la coordinates. -/
theorem Zl_size : x.Zl.size = h.la := size_last X.Zl

omit X in
/-- Every call has at least as many columns as a block has features. -/
theorem ls_le_lJ {q : ℕ} (hq : q < L.calls.size) : h.ls ≤ (L.calls.getD q default).lJ := by
  obtain ⟨cs, -, hs, hL⟩ := (admittedH_of_layout hy).calls
  rw [hL] at hq ⊢
  have hq' : q < cs.length := by simpa using hq
  have e : cs.toArray.getD q default = cs[q] := by simp [Array.getD, hq']
  rw [e]
  exact lJ_of_callSizes h cs hs _ (List.getElem_mem hq')

/-- **The point of a call.** Its column coordinates are lJ and end in the first ls coordinates of
x.Zl; its position coordinates are lt, and they are the coordinates of x.Zl from ls on. -/
theorem point_of_call {K : Type} [Field K] (ρ : Reading K) {q : ℕ} (hq : q < L.calls.size) :
    (Model.Head.zjOf L x.g1 q).size = (L.calls.getD q default).lJ ∧
    (∀ j, j < h.ls → pt ρ (Model.Head.zjOf L x.g1 q) ((L.calls.getD q default).lJ - h.ls + j) =
      pt ρ x.Zl j) ∧
    (Model.Head.ztOf h L x.g1 q).size = h.lt ∧
    ∀ j, j < h.lt → pt ρ (Model.Head.ztOf h L x.g1 q) j = pt ρ x.Zl (h.ls + j) :=
  point_parts ρ (zk_size hy X hq).2 (admittedH_of_layout hy).la_eq (ls_le_lJ hy hq)
    (zk_end hy X hq)

/-- **The record SegFit**, from its public half: low is the coordinates of x.Zl. -/
theorem segFit_of_run {K : Type} [Field K] (ρ : Reading K) {R : Model.Head.Run} (e1 : R.h = h)
    (e2 : R.L = L) (e3 : R.x = x) {sn : String} {n : ℕ} (S : SegLaid R sn n) :
    SegFit ρ R sn n (pt ρ R.x.Zl) := by
  subst e1 e2 e3
  refine S.fit ρ fun q hq => ?_
  have P := point_of_call hy X ρ (callNo_lt hq)
  exact ⟨P.1, P.2.1⟩

/-- **The record PosFit**, for every name that has a call: u j is coordinate ls + j of x.Zl. -/
theorem posFit_of_run {K : Type} [Field K] (ρ : Reading K) {R : Model.Head.Run} (e1 : R.h = h)
    (e2 : R.L = L) (e3 : R.x = x) {sn : String} {q : ℕ}
    (hq : Model.Head.callNo R.L sn = some q) :
    PosFit ρ R sn (fun j => pt ρ R.x.Zl (R.h.ls + j)) := by
  subst e1 e2 e3
  have P := point_of_call hy X ρ (callNo_lt hq)
  exact ⟨q, hq, P.2.2.1, P.2.2.2⟩

/-- x.Zl has ls + lt coordinates: what a long table at this point asks. -/
theorem Zl_parts : x.Zl.size = h.ls + h.lt :=
  (Zl_size X).trans (admittedH_of_layout hy).la_eq

end Point

#print axioms hear_steps
#print axioms clN_of_layout
#print axioms point_of_call
#print axioms segFit_of_run
#print axioms posFit_of_run
#print axioms Zl_parts

end OnBytes.Road.Hd
