-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/G4/AnyCaller.lean: what the program's lookup verifier computes, call by call and with every
value named, at any caller that meets a short list of laws.

OnBytes/G4/RunValues.lean states the run of Lkp.verify as a function of the plain data at one
made-up caller. Here the caller is a letter. A `Caller` holds the lookup's public inputs, what
Lkp.verify is told (where the bits are read, the two messages that give mask entries, the group),
and a family of contexts `ctx`, indexed by what a run of the lookup turns: the plan's entries that
are left, the round that is open, the rounds that are left, the entry of the round closed last, the
state of the two ledgers, and the rows added to the group. `Caller.Laws` are equations on the
program's primitives at these contexts: receiving and closing a round, a note, taking mask entries
from either ledger, adding a row that is `Fine`, and that the messages are sampled; with what is
needed of `Fine` and of the ledgers' counts. From these laws alone each call of the lookup is an
equation whose right side is written out.

Main definitions: Caller, Caller.env, Caller.Laws, Caller.Stand, Caller.Stand.pscOut,
Caller.Stand.pscRow.
Main theorems: Caller.Laws.hearDraw_val, Caller.Laws.hearOne_val, Caller.Laws.hearMany_val,
Caller.Laws.hear_val, Caller.Laws.fresh_val, Caller.Laws.psc_val.
Not claimed. That any caller of the program meets the laws: that is shown caller by caller. Nothing
on soundness.


-/
import OnBytes.G4.RunRows

set_option autoImplicit false

namespace OnBytes.G4

open Blk

/-- A caller of the lookup, as far as a run of the lookup can tell. -/
structure Caller where
  /-- the lookup's public inputs -/
  S : Lkp.Public
  /-- where the bits of the multiplicities are read -/
  planesAt : Row → Tensor → Row
  /-- the message that gives the mask entries -/
  masks : Nat
  /-- the message that gives the two mask entries of each part's last key level -/
  keyMasks : Nat
  /-- the group to which the rows are added -/
  group : Nat
  /-- the state of the two ledgers -/
  Led : Type
  /-- the context: entries left, the open round, rounds left, the entry closed last, ledgers, rows
  -/
  ctx : List Fmt.Entry → Option Fmt.RoundView → List Fmt.RoundView → Option Fmt.Entry → Led → Array Row → Ctx
  /-- the next n entries of the first ledger, and the state after them -/
  take : Led → Nat → List Slot × Led
  /-- the next n entries of the second ledger, and the state after them -/
  takeKey : Led → Nat → List Slot × Led
  /-- how many entries the first ledger has left -/
  left : Led → Nat
  /-- how many entries the second ledger has left -/
  keyLeft : Led → Nat
  /-- a mask entry that a row of the group may read -/
  SlotOK : Slot → Prop
  /-- a row that the group takes -/
  Fine : Row → Prop

namespace Caller

/-- What the steps of the lookup are told. -/
def env (C : Caller) : Lkp.Env where
  S := C.S
  planesAt := C.planesAt
  masks := C.masks
  keyMasks := C.keyMasks
  group := C.group

/-- All mask entries of a form may be read by a row of the group. -/
def SlotsOK (C : Caller) (m : MaskForm) : Prop := ∀ p ∈ m, C.SlotOK p.1

/-- A claim at a point of n coordinates whose mask entries a row of the group may read. -/
def ClaimOK (C : Caller) (n : Nat) (c : PointClaim) : Prop := c.point.length = n ∧ C.SlotsOK c.masks

/-- The kept maps keep a row fine at points of n coordinates. -/
def MapsOK (C : Caller) (n : Nat) (kept : List MapAt) : Prop :=
  ∀ m ∈ kept, ∀ (row : Row) (point : List E) (coeff : E), C.Fine row → point.length = n →
    C.Fine (m row point coeff)

/-- What is asked of a caller: equations on the program's primitives at its contexts. -/
structure Laws (C : Caller) : Prop where
  /-- receiving all elements of a round that is not yet begun -/
  recv : ∀ es rs last σ rows (r : FlatRound),
    (Blk.recvEs r.sent.length) (C.ctx es none (r.rv :: rs) last σ rows) =
      .ok (r.sent, C.ctx es (openedCur r) (openedLeft r rs) last σ rows)
  /-- closing a round whose elements are received -/
  close : ∀ (e : Fmt.Entry) es rs last σ rows (r : FlatRound) (name : String) (kind : Fmt.Kind)
    (nz : Nat), e.name = name → e.drawNZ = nz → NoRows last → r.drawn.length = e.drawE → e.poss = 0
        →
    e.trits = 0 →
    (Blk.close name kind nz) (C.ctx (e :: es) (openedCur r) (openedLeft r rs) last σ rows) =
      .ok (r.rv.drawn, C.ctx es none rs (some e) σ rows)
  /-- a note turns nothing -/
  note : ∀ es cur rs last σ rows (what : String) (x : E),
    (Blk.note what x) (C.ctx es cur rs last σ rows) = .ok ((), C.ctx es cur rs last σ rows)
  /-- taking entries of the first ledger -/
  take : ∀ es rs last σ rows n, n ≤ C.left σ →
    (takeSlots C.masks n) (C.ctx es none rs last σ rows) =
      .ok ((C.take σ n).1, C.ctx es none rs last (C.take σ n).2 rows)
  /-- taking entries of the second ledger -/
  takeKey : ∀ es rs last σ rows n, n ≤ C.keyLeft σ →
    (takeSlots C.keyMasks n) (C.ctx es none rs last σ rows) =
      .ok ((C.takeKey σ n).1, C.ctx es none rs last (C.takeKey σ n).2 rows)
  /-- as many entries as asked -/
  takeLength : ∀ σ n, (C.take σ n).1.length = n
  /-- as many entries as asked -/
  takeKeyLength : ∀ σ n, (C.takeKey σ n).1.length = n
  /-- the first ledger's count after a take from it -/
  leftTake : ∀ σ n, n ≤ C.left σ → C.left (C.take σ n).2 = C.left σ - n
  /-- the second ledger's count after a take from the first -/
  keyLeftTake : ∀ σ n, C.keyLeft (C.take σ n).2 = C.keyLeft σ
  /-- the first ledger's count after a take from the second -/
  leftTakeKey : ∀ σ n, C.left (C.takeKey σ n).2 = C.left σ
  /-- the second ledger's count after a take from it -/
  keyLeftTakeKey : ∀ σ n, n ≤ C.keyLeft σ → C.keyLeft (C.takeKey σ n).2 = C.keyLeft σ - n
  /-- entries taken from the first ledger may be read by a row of the group. (Those of the second
  mask the two values shown at a part's last key level; they go on in the claim on the keys, into no
  row of the group.) -/
  takeOK : ∀ σ n, n ≤ C.left σ → ∀ s ∈ (C.take σ n).1, C.SlotOK s
  /-- a fine row goes into the group through the lookup's own door -/
  leave : ∀ es rs last σ rows (row : Row), C.Fine row →
    (Lkp.leave C.env row) (C.ctx es none rs last σ rows) =
      .ok ((), C.ctx es none rs last σ (rows.push row))
  /-- the row that has only a target is fine -/
  fineTarget : ∀ x : E, C.Fine { target := x }
  /-- a fine row stays fine when a mask entry is added -/
  fineUnit : ∀ (r : Row) (s : Slot) (x : E), C.Fine r → C.SlotOK s →
    C.Fine (r.addUnit s.oracle .mask s.index x)
  /-- a fine row stays fine when a vector of product form on the bits is added -/
  finePlanes : ∀ (r : Row) (v : Tensor), C.Fine r → v.vars = C.S.mu + C.S.d → v.ok = true →
    v.denseVars = [] → C.Fine (C.planesAt r v)
  /-- the messages that the lookup names are sampled -/
  sampled : ∀ es rs last σ rows (l : List Nat),
      (∀ o ∈ l, o = C.masks ∨ o = C.keyMasks ∨ o ∈ C.S.readFrom) →
    (Lkp.mustBeSampled l) (C.ctx es none rs last σ rows) = .ok ((), C.ctx es none rs last σ rows)

end Caller

variable {C : Caller}

/-! ## Rounds -/

/-- A round in which nothing is sent and n elements are drawn. -/
theorem Caller.Laws.hearDraw_val (L : C.Laws) (e : Fmt.Entry) (es rs last σ rows) (r : FlatRound)
    (name : String) (n : Nat) (h : Meets r e name 0 n 0) (hq : NoRows last) :
    (hearDraw name n) (C.ctx (e :: es) none (r.rv :: rs) last σ rows) =
      .ok (r.drawn, C.ctx es none rs (some e) σ rows) := by
  have hs : r.sent = [] := List.length_eq_zero_iff.1 h.sent
  have hc := L.close e es rs last σ rows r name .elems 0 h.name h.nz hq
    (h.drawn.trans h.drawE.symm) h.poss h.trits
  simp only [openedCur, openedLeft, hs, List.isEmpty_nil, if_true] at hc
  have h1 : (Blk.closeElems name) (C.ctx (e :: es) none (r.rv :: rs) last σ rows) =
      .ok (r.drawn, C.ctx es none rs (some e) σ rows) := by
    show ((Blk.close name .elems 0) >>= fun d => pure (d.elems.map E.ofTriple)) _ = _
    rw [bind_ok hc, pure_ok, drawn_elems]
  show ((Blk.closeElems name) >>= fun l => (Blk.must (l.length == n)) >>= fun _ => pure l) _ = _
  rw [bind_ok h1, bind_ok (must_ok (by simp [h.drawn]) _), pure_ok]

/-- A round in which n elements are sent and one is drawn. -/
theorem Caller.Laws.hearOne_val (L : C.Laws) (e : Fmt.Entry) (es rs last σ rows) (r : FlatRound)
    (name : String) (kind : Fmt.Kind) (n nz : Nat) (h : Meets r e name n 1 nz) (hq : NoRows last) :
    (Psc.hearOne name kind n nz) (C.ctx (e :: es) none (r.rv :: rs) last σ rows) =
      .ok (pairOf r, C.ctx es none rs (some e) σ rows) := by
  obtain ⟨g, hg⟩ := List.length_eq_one_iff.1 h.drawn
  have hc := L.close e es rs last σ rows r name kind nz h.name h.nz hq
    (h.drawn.trans h.drawE.symm) h.poss h.trits
  have h1 : (Blk.closeOne name kind nz)
      (C.ctx (e :: es) (openedCur r) (openedLeft r rs) last σ rows) =
      .ok (g, C.ctx es none rs (some e) σ rows) := by
    unfold Blk.closeOne
    rw [bind_ok hc]
    simp [FlatRound.rv, hg, pure_ok, E.ofTriple_triple]
  show ((Blk.recvEs n) >>= fun q => (Blk.closeOne name kind nz) >>= fun g => pure (q, g)) _ = _
  rw [← h.sent, bind_ok (L.recv (e :: es) rs last σ rows r), bind_ok h1, pure_ok]
  simp [pairOf, hg]

/-- The rounds of the variables of a sumcheck. -/
theorem Caller.Laws.hearMany_val (L : C.Laws) (work : Nat) (σ : C.Led) (rows : Array Row)
    (es' : List Fmt.Entry) :
    ∀ (ns : List Nat) (rs : List FlatRound) (last : Option Fmt.Entry), NoRows last →
      FitsAll rs (ns.map (fun n => (Psc.rOne "PSC round" .elems work n 0).entry) ++ es') →
      ∃ last', FitsAll (rs.drop ns.length) es' ∧ NoRows last' ∧
        (Psc.hearMany ns)
            (C.ctx (ns.map (fun n => (Psc.rOne "PSC round" .elems work n 0).entry) ++ es')
          none (rvs rs) last σ rows) =
          .ok ((rs.take ns.length).map pairOf, C.ctx es' none (rvs (rs.drop ns.length)) last' σ
              rows)
  | [], rs, last, hq, h => ⟨last, h, hq, rfl⟩
  | n :: ns, [], last, hq, h => by simp [FitsAll] at h
  | n :: ns, r :: rs, last, hq, h => by
    obtain ⟨hr, hrest⟩ := h
    have hm : Meets r (Psc.rOne "PSC round" .elems work n 0).entry "PSC round" n 1 0 :=
      meets_of_fits hr rfl rfl rfl rfl rfl rfl rfl
    have h1 := L.hearOne_val _
        (ns.map (fun n => (Psc.rOne "PSC round" .elems work n 0).entry) ++ es')
      (rvs rs) last σ rows r "PSC round" .elems n 0 hm hq
    obtain ⟨last', hf, hq', h2⟩ := Caller.Laws.hearMany_val L work σ rows es' ns rs _ hm.noRows
        hrest
    refine ⟨last', hf, hq', ?_⟩
    show ((Psc.hearOne "PSC round" .elems n 0) >>= fun a =>
      (Psc.hearMany ns) >>= fun l => pure (a :: l)) _ = _
    rw [show (List.map (fun n => (Psc.rOne "PSC round" .elems work n 0).entry) (n :: ns) ++ es') =
      (Psc.rOne "PSC round" .elems work n 0).entry ::
        (ns.map (fun n => (Psc.rOne "PSC round" .elems work n 0).entry) ++ es') from rfl]
    rw [show rvs (r :: rs) = r.rv :: rvs rs from rfl, bind_ok h1, bind_ok h2, pure_ok]
    rfl

/-- The round of the shown values. -/
theorem Caller.Laws.hearValues_val (L : C.Laws) {β : Type} (f : List E → Blk β) (e : Fmt.Entry)
    (es rs last σ rows) (r : FlatRound) (n : Nat) (h : Meets r e "PSC values" n 0 0)
    (hq : NoRows last) :
    ((Blk.recvEs n) >>= fun values => (Blk.closeEmpty "PSC values") >>= fun _ => f values)
      (C.ctx (e :: es) none (r.rv :: rs) last σ rows) =
      f r.sent (C.ctx es none rs (some e) σ rows) := by
  have hc := L.close e es rs last σ rows r "PSC values" .nothing 0 h.name h.nz hq
    (h.drawn.trans h.drawE.symm) h.poss h.trits
  have h1 : (Blk.closeEmpty "PSC values")
      (C.ctx (e :: es) (openedCur r) (openedLeft r rs) last σ rows) =
      .ok ((), C.ctx es none rs (some e) σ rows) := by
    show ((Blk.close "PSC values" .nothing) >>= fun _ => pure ()) _ = _
    rw [bind_ok hc, pure_ok]
  rw [← h.sent, bind_ok (L.recv (e :: es) rs last σ rows r), bind_ok h1]

/-- Reading the rounds of a sumcheck. -/
theorem Caller.Laws.hear_val (L : C.Laws) (work : Nat) (σ : C.Led) (rows : Array Row) (x : Psc.Size)
    (es' : List Fmt.Entry) (rs : List FlatRound) (last : Option Fmt.Entry) (hq : NoRows last)
    (h : FitsAll rs (pscEntries work x ++ es')) :
    ∃ last', FitsAll (restOf x rs) es' ∧ NoRows last' ∧
      (Psc.hear x) (C.ctx (pscEntries work x ++ es') none (rvs rs) last σ rows) =
        .ok (heardOf x rs, C.ctx es' none (rvs (restOf x rs)) last' σ rows) := by
  rw [pscEntries_eq] at h ⊢
  cases rs with
  | nil => simp [FitsAll] at h
  | cons r rs =>
    obtain ⟨hr, hrest⟩ := h
    have hm : Meets r (Psc.rOne "PSC epsilon" .join work 1 0).entry "PSC epsilon" 1 1 0 :=
      meets_of_fits hr rfl rfl rfl rfl rfl rfl rfl
    have h1 := L.hearOne_val _ ((x.degree.map (· - 1)).map
        (fun n => (Psc.rOne "PSC round" .elems work n 0).entry) ++
      ((if x.withY then
          [(Psc.rOne "PSC Y" .elems work x.degreeY 1).entry, (Psc.rValues x.values).entry]
        else []) ++ es')) (rvs rs) last σ rows r "PSC epsilon" .join 1 0 hm hq
    obtain ⟨mu, hmu⟩ := List.length_eq_one_iff.1 hm.sent
    obtain ⟨last1, hf1, hq1, h2⟩ := L.hearMany_val work σ rows _ _ rs _ hm.noRows hrest
    simp only [List.length_map] at hf1 h2
    unfold Psc.hear
    rw [show rvs (r :: rs) = r.rv :: rvs rs from rfl, bind_ok h1]
    simp only [pairOf, hmu, List.head?_cons]
    rw [bind_ok (get_ok mu _), bind_ok h2]
    cases hY : x.withY with
    | false =>
      simp only [hY, Bool.false_eq_true, if_false, List.nil_append] at hf1 ⊢
      refine ⟨last1, by simpa [restOf, hY] using hf1, hq1, ?_⟩
      simp [heardOf, restOf, hY, hmu, pure_ok]
    | true =>
      simp only [hY, if_true, List.cons_append, List.nil_append] at hf1 ⊢
      cases hd : rs.drop x.degree.length with
      | nil => simp [hd, FitsAll] at hf1
      | cons rY rs2 =>
        rw [hd] at hf1
        obtain ⟨hrY, hf2⟩ := hf1
        cases rs2 with
        | nil => simp [FitsAll] at hf2
        | cons rV rs3 =>
          obtain ⟨hrV, hf3⟩ := hf2
          have hmY : Meets rY (Psc.rOne "PSC Y" .elems work x.degreeY 1).entry "PSC Y" x.degreeY 1
              1 :=
            meets_of_fits hrY rfl rfl rfl rfl rfl rfl rfl
          have hmV : Meets rV (Psc.rValues x.values).entry "PSC values" x.values 0 0 :=
            meets_of_fits hrV rfl rfl rfl rfl rfl rfl rfl
          have h3 := L.hearOne_val _ ((Psc.rValues x.values).entry :: es')
            (rvs (rV :: rs3)) last1 σ rows rY "PSC Y" .elems x.degreeY 1 hmY hq1
          refine ⟨_, by simpa [restOf, hY, hd] using hf3, hmV.noRows, ?_⟩
          rw [show rvs (rY :: rV :: rs3) = rY.rv :: rvs (rV :: rs3) from rfl, bind_ok h3]
          rw [show rvs (rV :: rs3) = rV.rv :: rvs rs3 from rfl]
          rw [L.hearValues_val _ _ es' (rvs rs3) _ σ rows rV x.values hmV hmY.noRows]
          simp [heardOf, restOf, hY, hd, hmu, pairOf, pure_ok]

/-! ## Mask entries and rows -/

/-- The fresh mask entries of a sumcheck, and the ledgers after them. keys: the last two come from
the second ledger. -/
def Caller.freshOf (C : Caller) (σ : C.Led) (n : Nat) (keys : Bool) : List Slot × C.Led :=
  if keys then
    ((C.take σ (n - 2)).1 ++ (C.takeKey (C.take σ (n - 2)).2 2).1,
        (C.takeKey (C.take σ (n - 2)).2 2).2)
  else C.take σ n

/-- How many of n fresh entries come from the first ledger. -/
def ownOf (n : Nat) (keys : Bool) : Nat := if keys then n - 2 else n

/-- How many fresh entries come from the second ledger. -/
def keyOf (keys : Bool) : Nat := if keys then 2 else 0

/-- The fresh mask entries of a sumcheck, named. -/
theorem Caller.Laws.fresh_val (L : C.Laws) (es rs last rows) (σ : C.Led) (n : Nat) (keys : Bool)
    (h1 : ownOf n keys ≤ C.left σ) (h2 : keyOf keys ≤ C.keyLeft σ) (h3 : keys = true → 2 ≤ n) :
    (Lkp.fresh C.env n keys) (C.ctx es none rs last σ rows) =
        .ok ((C.freshOf σ n keys).1, C.ctx es none rs last (C.freshOf σ n keys).2 rows) ∧
      (C.freshOf σ n keys).1.length = n ∧
      (∀ s ∈ (C.freshOf σ n keys).1.take (ownOf n keys), C.SlotOK s) ∧
      C.left (C.freshOf σ n keys).2 = C.left σ - ownOf n keys ∧
      C.keyLeft (C.freshOf σ n keys).2 = C.keyLeft σ - keyOf keys := by
  cases keys with
  | false =>
    simp only [ownOf, keyOf, Bool.false_eq_true, if_false] at h1 h2 ⊢
    exact ⟨L.take es rs last σ rows n h1, L.takeLength σ n,
      fun s hs => L.takeOK σ n h1 s (List.mem_of_mem_take hs), L.leftTake σ n h1,
      by rw [Caller.freshOf]; simp [L.keyLeftTake]⟩
  | true =>
    have hn := h3 rfl
    simp only [ownOf, keyOf, if_true] at h1 h2 ⊢
    have hk : 2 ≤ C.keyLeft (C.take σ (n - 2)).2 := by rw [L.keyLeftTake]; exact h2
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show ((Blk.must (decide (2 ≤ n))) >>= fun _ => (takeSlots C.masks (n - 2)) >>= fun a =>
        (takeSlots C.keyMasks 2) >>= fun b => pure (a ++ b)) _ = _
      rw [bind_ok (must_ok (by simp [hn]) _), bind_ok (L.take es rs last σ rows (n - 2) h1),
        bind_ok (L.takeKey es rs last _ rows 2 hk), pure_ok]
      rfl
    · simp [Caller.freshOf, L.takeLength, L.takeKeyLength]
      omega
    · intro s hs
      have e : ((C.freshOf σ n true).1).take (n - 2) = (C.take σ (n - 2)).1 := by
        simp only [Caller.freshOf, if_true]
        rw [List.take_append_of_le_length (by rw [L.takeLength]; exact Nat.le_refl _),
          List.take_of_length_le (by rw [L.takeLength]; exact Nat.le_refl _)]
      rw [e] at hs
      exact L.takeOK σ _ h1 s hs
    · simp [Caller.freshOf, L.leftTakeKey, L.leftTake σ _ h1]
    · simp [Caller.freshOf, L.keyLeftTakeKey _ 2 hk, L.keyLeftTake]

/-- A row stays fine when mask entries that a row may read are added to it. -/
theorem Caller.Laws.fineMasks (L : C.Laws) : ∀ (m : MaskForm) (r : Row), C.Fine r → C.SlotsOK m →
    C.Fine (r.addMasks m)
  | [], _, h, _ => h
  | t :: m, r, h, hm =>
    Caller.Laws.fineMasks L m _ (L.fineUnit r t.1 t.2 h (hm t (by simp)))
      (fun p hp => hm p (by simp [hp]))

theorem Caller.fineFold (C : Caller) (n : Nat) (point : List E) (hp : point.length = n) :
    ∀ (l : List (MapAt × E)) (r : Row), (∀ q ∈ l, ∀ (row : Row) (pt : List E) (coeff : E),
      C.Fine row → pt.length = n → C.Fine (q.1 row pt coeff)) → C.Fine r →
    C.Fine (l.foldl (fun r p => p.1 r point p.2) r)
  | [], _, _, h => h
  | q :: l, r, hl, h =>
    Caller.fineFold C n point hp l _ (fun x hx => hl x (by simp [hx]))
        (hl q (by simp) r point q.2 h hp)

theorem Caller.slotsOK_scale {m : MaskForm} (x : E) (h : C.SlotsOK m) :
    C.SlotsOK (Psc.scaleForm x m) := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  exact h q hq

theorem Caller.slotsOK_append {a b : MaskForm} (ha : C.SlotsOK a) (hb : C.SlotsOK b) :
    C.SlotsOK (a ++ b) := by
  intro p hp
  rcases List.mem_append.1 hp with h | h
  · exact ha p h
  · exact hb p h

/-! ## Stands -/

/-- Where a run stands: the rounds that are left, the ledgers, the rows added. -/
structure Caller.Stand (C : Caller) where
  /-- the rounds that are left -/
  rounds : List FlatRound
  /-- the state of the two ledgers -/
  led : C.Led
  /-- the rows added to the group -/
  rows : Array Row

namespace Caller.Stand

/-- The context of a stand. -/
def ctx (s : C.Stand) (es : List Fmt.Entry) (last : Option Fmt.Entry) : Ctx :=
  C.ctx es none (rvs s.rounds) last s.led s.rows

/-- What one sumcheck hands on from a stand: the record that Psc.run gives (runValue,
OnBytes/G4/RunRows.lean) at the next mask entries and the next rounds, with the coordinates of its
points put back at their variables' places. -/
def pscOut (s : C.Stand) (c : Psc.Claim) (Sm : Psc.Summand) (keys : Bool) (place : List E → List E)
    :
    Psc.Out :=
  placed place (runValue c Sm (C.freshOf s.led (Psc.masksOf c Sm) keys).1
    (heardOf (Psc.sizeOf c Sm) s.rounds))

/-- The row that one sumcheck adds to the group: the row that Psc.rowU makes, written out. -/
def pscRow (s : C.Stand) (c : Psc.Claim) (Sm : Psc.Summand) (keys : Bool) (kept : List MapAt)
    (place : List E → List E) : Row :=
  (kept.zip (s.pscOut c Sm keys place).rowMaps).foldl
    (fun r p => p.1 r (s.pscOut c Sm keys place).point p.2)
    (({ target := (s.pscOut c Sm keys place).rowTarget } : Row).addMasks
      (s.pscOut c Sm keys place).rowMasks)

/-- The stand after one sumcheck. -/
def afterPsc (s : C.Stand) (c : Psc.Claim) (Sm : Psc.Summand) (keys : Bool) (kept : List MapAt)
    (place : List E → List E) : C.Stand where
  rounds := restOf (Psc.sizeOf c Sm) s.rounds
  led := (C.freshOf s.led (Psc.masksOf c Sm) keys).2
  rows := s.rows.push (s.pscRow c Sm keys kept place)

/-- The first element drawn in the next round. -/
def draw (s : C.Stand) : E := (s.rounds.headD default).drawn.headD zeroE

/-- All that is drawn in the next round. -/
def draws (s : C.Stand) : List E := (s.rounds.headD default).drawn

/-- The stand after the next round. -/
def next (s : C.Stand) : C.Stand := { s with rounds := s.rounds.tail }

end Caller.Stand

/-- A member of a zip has its first part among the first members of the first list. -/
theorem mem_zip_take {α β : Type} : ∀ {l : List α} {m : List β} {p : α × β}, p ∈ l.zip m →
    p.1 ∈ l.take m.length
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: l, b :: m, p, h => by
    simp only [List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · simp only [List.length_cons, List.take_succ_cons, List.mem_cons]
      exact Or.inr (mem_zip_take h)

theorem List.mem_of_mem_take_le {α : Type} {l : List α} {a b : Nat} {x : α} (h : a ≤ b)
    (hx : x ∈ l.take a) : x ∈ l.take b := by
  have e : l.take a = (l.take b).take a := by rw [List.take_take, Nat.min_eq_left h]
  rw [e] at hx
  exact List.mem_of_mem_take hx

/-- The form of a sumcheck's first polynomial has as many coefficients as Psc.hidingEntries says. -/
theorem walk_entries (c : Psc.Claim) (Sm : Psc.Summand) (h : Psc.Heard)
    (hl : h.rounds.map (fun p => p.1.length) = (Psc.varsOf c Sm).map (fun w => w.d - 1))
    (hd : ∀ w ∈ Psc.varsOf c Sm, 1 ≤ w.d) (hne : Psc.varsOf c Sm ≠ []) :
    (Psc.hidingWalk ((Psc.varsOf c Sm).zip (h.rounds.map (·.2)))).1.length =
      Psc.hidingEntries (Psc.varsOf c Sm) := by
  have hlen : h.rounds.length = (Psc.varsOf c Sm).length := by
    simpa using congrArg List.length hl
  rw [hidingWalk_length]
  · unfold Psc.hidingEntries
    congr 2
    have hz : ((Psc.varsOf c Sm).zip (h.rounds.map (·.2))).map Prod.fst = Psc.varsOf c Sm :=
      List.map_fst_zip (by simp [hlen])
    calc List.map (fun p => p.1.d - 1) ((Psc.varsOf c Sm).zip (h.rounds.map (·.2)))
        = List.map (fun w : Psc.Weight => w.d - 1)
            (((Psc.varsOf c Sm).zip (h.rounds.map (·.2))).map Prod.fst) := by
          rw [List.map_map]
          rfl
      _ = _ := by rw [hz]
  · intro hz
    have := congrArg List.length hz
    simp [hlen] at this
    exact hne this
  · intro p hp
    exact hd p.1 (List.of_mem_zip hp).1

/-- One sumcheck of the lookup, with every value named. -/
theorem Caller.Laws.psc_val (L : C.Laws) (work : Nat) (c : Psc.Claim) (Sm : Psc.Summand)
    (keys : Bool)
    (kept : List MapAt) (place : List E → List E) (es' : List Fmt.Entry) (s : C.Stand)
    (last : Option Fmt.Entry) (hq : NoRows last)
    (hfit : FitsAll s.rounds (pscEntries work (Psc.sizeOf c Sm) ++ es'))
    (hform : Psc.formOK c Sm = true) (ha : ∀ p y, (Sm.coeffs p y).length = 1 + Sm.kept)
    (hd : ∀ w ∈ Psc.varsOf c Sm, 1 ≤ w.d) (hne : Psc.varsOf c Sm ≠ [])
    (hle : c.vars.length ≤ (Psc.varsOf c Sm).length)
    (h1 : ownOf (Psc.masksOf c Sm) keys ≤ C.left s.led) (h2 : keyOf keys ≤ C.keyLeft s.led)
    (h3 : keys = true → 2 ≤ Psc.masksOf c Sm) (h4 : keyOf keys ≤ Sm.shown)
    (hm : C.SlotsOK c.masks) (hkept : kept.length = Sm.kept) (hmaps : C.MapsOK c.vars.length kept)
    (hplace : ∀ p, (place p).length = p.length) :
    ∃ last', FitsAll (s.afterPsc c Sm keys kept place).rounds es' ∧ NoRows last' ∧
      (Lkp.psc C.env c Sm keys kept place) (s.ctx (pscEntries work (Psc.sizeOf c Sm) ++ es') last) =
        .ok (s.pscOut c Sm keys place, (s.afterPsc c Sm keys kept place).ctx es' last') ∧
      (s.pscOut c Sm keys place).point.length = c.vars.length ∧
      (s.pscOut c Sm keys place).ends.length = Sm.shown ∧
      (∀ e ∈ (s.pscOut c Sm keys place).ends,
        e.point = (s.pscOut c Sm keys place).point ∧ (keys = false → C.SlotsOK e.masks)) ∧
      C.left (s.afterPsc c Sm keys kept place).led = C.left s.led - ownOf (Psc.masksOf c Sm) keys ∧
      C.keyLeft (s.afterPsc c Sm keys kept place).led = C.keyLeft s.led - keyOf keys := by
  obtain ⟨hfr, hfl, hfs, hleft, hkeyLeft⟩ := L.fresh_val (pscEntries work (Psc.sizeOf c Sm) ++ es')
    (rvs s.rounds) last s.rows s.led (Psc.masksOf c Sm) keys h1 h2 h3
  obtain ⟨last', hf', hq', hhear⟩ := L.hear_val work (C.freshOf s.led (Psc.masksOf c Sm) keys).2
      s.rows
    (Psc.sizeOf c Sm) es' s.rounds last hq hfit
  obtain ⟨hlens, hvals⟩ := heardOf_sizes work (Psc.sizeOf c Sm) es' s.rounds hfit
  rw [lens_eq] at hlens
  have hv : (heardOf (Psc.sizeOf c Sm) s.rounds).values.length = Sm.shown := by
    rw [hvals]
    unfold Psc.sizeOf
    by_cases h : Sm.shown = 0 <;> simp [h, Nat.pos_of_ne_zero]
  obtain ⟨o, ho, hO⟩ := run_some c Sm (C.freshOf s.led (Psc.masksOf c Sm) keys).1
    (heardOf (Psc.sizeOf c Sm) s.rounds) hform hfl hlens hv ha hd hne hle
  have hval := run_eq c Sm (C.freshOf s.led (Psc.masksOf c Sm) keys).1
    (heardOf (Psc.sizeOf c Sm) s.rounds) hform hfl hlens hv ha hd
  have hoval : o = runValue c Sm (C.freshOf s.led (Psc.masksOf c Sm) keys).1
      (heardOf (Psc.sizeOf c Sm) s.rounds) := by
    rw [ho] at hval
    exact Option.some.inj hval
  have hout : s.pscOut c Sm keys place = placed place o := by
    rw [hoval]
    rfl
  have hown : Psc.hidingEntries (Psc.varsOf c Sm) ≤ ownOf (Psc.masksOf c Sm) keys := by
    unfold ownOf keyOf at *
    unfold Psc.masksOf at *
    cases keys <;> simp at * <;> omega
  have hmasks : C.SlotsOK (s.pscOut c Sm keys place).rowMasks := by
    rw [hout]
    intro p hp
    have hp' : p ∈ (C.freshOf s.led (Psc.masksOf c Sm) keys).1.zip
        (Psc.hidingWalk ((Psc.varsOf c Sm).zip
          ((heardOf (Psc.sizeOf c Sm) s.rounds).rounds.map (·.2)))).1 ++
        Psc.scaleForm (mulE (heardOf (Psc.sizeOf c Sm) s.rounds).eps
          (Psc.hidingWalk ((Psc.varsOf c Sm).zip
            ((heardOf (Psc.sizeOf c Sm) s.rounds).rounds.map (·.2)))).2) c.masks := by
      rw [hoval] at hp
      exact hp
    rcases List.mem_append.1 hp' with h | h
    · have h5 := mem_zip_take h
      rw [walk_entries c Sm _ hlens hd hne] at h5
      exact hfs p.1 (List.mem_of_mem_take_le hown h5)
    · obtain ⟨q, hq1, rfl⟩ := List.mem_map.1 h
      exact hm q hq1
  have hpl : (s.pscOut c Sm keys place).point.length = c.vars.length := by
    rw [hout]
    show (place o.point).length = _
    rw [hplace, hO.point]
  have hrow : Psc.rowU (s.pscOut c Sm keys place) kept = some (s.pscRow c Sm keys kept place) ∧
      C.Fine (s.pscRow c Sm keys kept place) := by
    have hl : (kept.length == (s.pscOut c Sm keys place).rowMaps.length) = true := by
      rw [hout]
      show (kept.length == o.rowMaps.length) = true
      simp [hkept, hO.maps]
    have he : Psc.rowU (s.pscOut c Sm keys place) kept =
        some ((kept.zip (s.pscOut c Sm keys place).rowMaps).foldl
          (fun r p => p.1 r (s.pscOut c Sm keys place).point p.2)
          (({ target := (s.pscOut c Sm keys place).rowTarget } : Row).addMasks
            (s.pscOut c Sm keys place).rowMasks)) := by
      unfold Psc.rowU
      rw [if_pos hl]
    refine ⟨he, ?_⟩
    unfold Caller.Stand.pscRow
    apply C.fineFold c.vars.length _ hpl
    · intro q hq1
      exact hmaps q.1 (List.of_mem_zip hq1).1
    · exact L.fineMasks _ _ (L.fineTarget _) hmasks
  refine ⟨last', hf', hq', ?_, hpl, ?_, ?_, hleft, hkeyLeft⟩
  rotate_left
  · rw [hout]
    show (o.ends.map _).length = _
    rw [List.length_map, hO.ends]
  · rw [hout]
    intro e he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
    obtain ⟨h4, h5⟩ := hO.endsAt x hx
    clear h1 h2 h3
    refine ⟨by show place x.point = place o.point; rw [h4], ?_⟩
    intro hk p hp
    subst hk
    have h6 := h5 p hp
    apply hfs p.1
    rw [show ownOf (Psc.masksOf c Sm) false = Psc.masksOf c Sm from rfl, List.take_of_length_le
      (by rw [hfl]; exact Nat.le_refl _)]
    exact h6
  have hver : (Psc.verify c Sm (C.freshOf s.led (Psc.masksOf c Sm) keys).1)
      (C.ctx (pscEntries work (Psc.sizeOf c Sm) ++ es') none (rvs s.rounds) last
        (C.freshOf s.led (Psc.masksOf c Sm) keys).2 s.rows) =
      .ok (o, C.ctx es' none (rvs (restOf (Psc.sizeOf c Sm) s.rounds)) last'
        (C.freshOf s.led (Psc.masksOf c Sm) keys).2 s.rows) := by
    show ((Psc.hear (Psc.sizeOf c Sm)) >>= fun h =>
      Blk.get (Psc.run c Sm (C.freshOf s.led (Psc.masksOf c Sm) keys).1 h)) _ = _
    rw [bind_ok hhear, ho]
    rfl
  unfold Lkp.psc Caller.Stand.ctx
  rw [bind_ok hfr, bind_ok hver]
  show ((Blk.get (Psc.rowU (placed place o) kept)) >>= fun r =>
    (Lkp.leave C.env r) >>= fun _ => pure (placed place o)) _ = _
  rw [← hout, hrow.1, bind_ok (get_ok _ _), bind_ok (L.leave es' _ last' _ s.rows _ hrow.2),
      pure_ok]
  rfl

end OnBytes.G4
