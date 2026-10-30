-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/Any.lean: kind K5: the claims' law at every record of the kind's own:
no premise on the points, none on the tables. Johnson/Desc/First/Att/Claims/Top.lean speaks at
`inOld h`, the kind's record made of a plain record h of OnBytes/Model. The map from those records
to the kind's is onto: it forgets fields and joins nothing. So for every record i that the runs may
read, over a Geo that comes from a shape S, there is a plain record `oldOf S gL i` with stripIn i =
inOld (oldOf S gL i); and the runs never read funs (Johnson/Desc/First/Att/Claims/Seated.lean).
Hence the tie to the written lists holds on every seat.

Main names:
  `pwBack`, `sum3Back`, `sumDBack`, `remBack`, `scoreBack`, `divBack`, `maxBack`, `funBack`,
    `tabBack`: the kind's records as records of OnBytes/Model. A field that the kind's record lacks
    is set to a default (a sumcheck's nb and state p) or made of what the record holds: a plane
    claim's seg := `segOf` isD np, as toOwn (Johnson/Desc/First/Att/Left.lean) sets it; the tables'
    list funs := the kind's own list, record for record.
  `oldOf S gL i`, `strip_is_old`: i.g = geoOf S → i.zk = gL.zk → stripIn i = inOld (oldOf S gL i).
    `remBack_of`: back and forth at a plane claim whose seg is the one that isD and np tell.
  `Spec.FirstAny`, `SecondAny`, `WholeAny`, `LawAny`: the statements of Top.lean and Returns.lean at
    every such i.
Limits: `oldOf` feeds the written lists and what reads the fields above. A sumcheck's state p in it
is a default: a statement of OnBytes that asks something of that state is not met at it; the rows
here are the kind's own (rowU := SumP.row). What a statement on the forms' worth asks of h's other
fields must be shown of oldOf S gL i. That the tables which the claims read are those whose list the
smallness test closes is not said here (Johnson/Desc/First/Att/Claims/TablesAgree.lean,
Johnson/Desc/First/Att/Claims/TablesH.lean [not in this library]).
Used of OnBytes: plain records alone (PlaneClaim, Score, Divide, Attain, Sc3, Scd, PW, HFun, Tables,
ScoreTables, Heard, Shape, Plan, Forest.Heard as a field's type) and what
Johnson/Desc/First/Att/Claims/Top.lean names.
Not claimed: that a claim holds.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.Seated

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Pts TablesP ScoreT W1 RemP ScoreP DivP MaxP SumP geoOf ptsOfOwn w1Of sum3Of sumDOf)
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP PadIn)

def pwBack (v : Array W1) : Array PW := v.map fun x => { lam := x.lam, a := x.a, wp := x.wp }
def sum3Back (s : SumP) : Sc3 := { r := s.r, sEnd := s.ends, rowU := s.row }
def sumDBack (s : SumP) : Scd := { r := s.r, sEnd := s.ends, rowU := s.row }
/-- The list of keys of a plane claim, which the kind's record does not hold, from what it holds: three plane values: a remainder-table unit (rm | rd) · else a softmax-table unit (fm | fd); isD: on the diagonal. -/
def segOf (isD : Bool) (np : ℕ) : Attention.Seg :=
  if np = 3 then (if isD then Attention.Seg.rd else Attention.Seg.rm)
  else (if isD then Attention.Seg.fd else Attention.Seg.fm)
def remBack (c : RemP) : PlaneClaim :=
  { call := c.call, seg := segOf c.isD c.np, z := c.z, isD := c.isD, pw := pwBack c.pw, s0 := c.s0, np := c.np }
def scoreBack (k : ScoreP) : Score :=
  { call := k.call, claim := k.claim, seg := if k.below then Attention.Seg.fm else Attention.Seg.fd, pw := pwBack k.pw, zg := k.zg, zs := k.zs, zi := k.zi, zj := k.zj, wI := k.wI, s0 := k.s0, sc := sum3Back k.sc }
def divBack (d : DivP) : Divide :=
  { pwW := pwBack d.pwW, pwX := pwBack d.pwX, pwH := pwBack d.pwH, qWH := d.qWH, zsl := d.zsl, zgW := d.zgW, ziW := d.ziW, zcW := d.zcW, zgX := d.zgX, ziX := d.ziX, zgH := d.zgH, ziH := d.ziH, zcH := d.zcH
    s5 := d.s5, sIB := d.sIB, s5h := d.s5h, scE := sum3Back d.scE, gam := d.gam, sCl := d.sCl, vpm := sum3Back d.vpm, wJv := d.wJv, vpd := sum3Back d.vpd }
def maxBack (x : MaxP) : Attain :=
  { tg := x.tg, ti := x.ti, sM6 := x.sM6, scF := sum3Back x.scF, scd := sumDBack x.scd, scH := sum3Back x.scH }
/-- A table's record as that of OnBytes/Model: the same five fields. -/
def funBack (f : P.Fun1) : HFun := { mat := f.mat, len := f.len, phi := f.phi, tree := f.tree, start := f.start }
def tabBack (t : TablesP) : Attention.Tables :=
  { ptM := t.ptM, ptD := t.ptD, tA := t.tA, tVM := t.tVM, tVD := t.tVD
    score := t.score.map fun s => { tM := s.tM, tQ := s.tQ, tK := s.tK }
    hW := t.hW, hX := t.hX, hE := t.hE, hT := t.hT, hPi := t.hPi, hR2 := t.hR2, tO := t.tO
    qO := t.qO, qVM := t.qVM, qVD := t.qVD, qF := t.qF, qKx := t.qKx
    tBit0 := t.tBit0, tBit1 := t.tBit1, tPin := t.tPin, tabLen := t.tabLen, funs := t.funs.map funBack }

theorem map_map_id {α β : Type} (f : α → β) (g : β → α) (h : ∀ b, f (g b) = b) (v : Array β) :
    (v.map g).map f = v := by
  rw [Array.map_map]
  have : (f ∘ g) = id := funext h
  rw [this, Array.map_id]

theorem w1Of_back (v : Array W1) : w1Of (pwBack v) = v := map_map_id _ _ (fun _ => rfl) v
theorem sum3_back (s : SumP) : sum3Of (sum3Back s) = s := rfl
theorem sumD_back (s : SumP) : sumDOf (sumDBack s) = s := rfl

theorem remOf_back (c : RemP) : remOf (remBack c) = c := by
  unfold remOf remBack
  dsimp only
  rw [w1Of_back]

theorem pwBack_of (v : Array PW) : pwBack (w1Of v) = v := map_map_id _ _ (fun _ => rfl) v

/-- Back and forth, at a plane claim whose seg is the one that its isD and np tell. -/
theorem remBack_of (c : PlaneClaim) (h : c.seg = segOf c.isD c.np) : remBack (remOf c) = c := by
  unfold remBack remOf
  dsimp only
  rw [pwBack_of, ← h]

theorem scoreOf_back (k : ScoreP) : scoreOf (scoreBack k) = k := by
  unfold scoreOf scoreBack
  dsimp only
  rw [w1Of_back, sum3_back]
  cases k with
  | mk call claim below pw zg zs zi zj wI s0 sc => cases below <;> rfl

theorem divOf_back (d : DivP) : divOf (divBack d) = d := by
  unfold divOf divBack
  dsimp only
  rw [w1Of_back, w1Of_back, w1Of_back]
  rfl

theorem maxOf_back (x : MaxP) : maxOf (maxBack x) = x := rfl

theorem pts_back (p : Pts) :
    ptsOfOwn (p.planes.map remBack) (p.scores.map scoreBack) (divBack p.d) (maxBack p.x) = p := by
  have e : ptsOfOwn (p.planes.map remBack) (p.scores.map scoreBack) (divBack p.d) (maxBack p.x) =
      { planes := (p.planes.map remBack).map remOf, scores := (p.scores.map scoreBack).map scoreOf,
        d := divOf (divBack p.d), x := maxOf (maxBack p.x) } := rfl
  rw [e, map_map_id _ _ remOf_back, map_map_id _ _ scoreOf_back, divOf_back, maxOf_back]

theorem tabs_back (t : TablesP) : tabsOld (tabBack t) = stripT t := by
  unfold tabsOld tabBack stripT
  dsimp only
  rw [map_map_id _ _ (fun _ => rfl)]

/-- **The plain record of OnBytes/Model of which a record of the kind's own is made.** gL: the lookup's record (its key points are the runs'; the claims' lists read nothing else of it). -/
def oldOf (S : Shape) (gL : Forest.Heard) (i : P.Runs.In) : Attention.Heard :=
  { S := S, g := gL, planes := i.p.planes.map remBack, scores := i.p.scores.map scoreBack,
    d := divBack i.p.d, x := maxBack i.p.x, t := tabBack i.t, iU3 := i.iU3 }

theorem strip_is_old (S : Shape) (gL : Forest.Heard) (i : P.Runs.In) (hg : i.g = geoOf S)
    (hz : i.zk = gL.zk) : stripIn i = inOld (oldOf S gL i) := by
  unfold inOld oldOf stripIn
  dsimp only
  rw [pts_back, tabs_back, ← hg, ← hz]

namespace Spec

def FirstAny : Prop :=
  ∀ (A : Plan) (S : Shape) (gL : Forest.Heard) (i : P.Runs.In) (K : ℕ) (l : List Aff) (j : JoinsP),
    i.g = geoOf S → i.zk = gL.zk → A.NC = S.calls.size → P.Runs.firstRun i K = some (l, j) →
      l = Fo.claim3T (oldOf S gL i) K ++ (Fo.claim4T (oldOf S gL i) K ++ Fo.claim5T (oldOf S gL i) K) ∧
        j = jP (Fo.attJoinsT A (oldOf S gL i))

def SecondAny : Prop :=
  ∀ (S : Shape) (gL : Forest.Heard) (i : P.Runs.In) (K : ℕ) (l : List Aff),
    i.g = geoOf S → i.zk = gL.zk → P.Runs.secondRun i K = some l →
      l = Fo.claim6T (oldOf S gL i) K ++ (Fo.claim7T (oldOf S gL i) K ++ Fo.claim8T (oldOf S gL i) K)

def WholeAny : Prop :=
  ∀ (A : Plan) (S : Shape) (gL : Forest.Heard) (i : P.Runs.In) (K : ℕ) (k3 : PadIn)
    (l₁ l₂ : List Aff) (j : JoinsP) (kf : Array Aff),
    i.g = geoOf S → i.zk = gL.zk → A.NC = S.calls.size → P.Runs.firstRun i K = some (l₁, j) →
    P.Runs.keysRun i k3 j = some kf → P.Runs.secondRun i K = some l₂ →
      Fo.attT A (oldOf S gL i) K = gL.rows.toList ++ (l₁ ++ ([Fo.joinForm gL kf] ++ (l₂ ++
        (Fo.planeFormsT gL S.cf.lmb
          (fun e col => Fo.u3Form i.iU3 K ((if e == 0 then i.t.tBit0 else i.t.tBit1) + col))
          (fun col => Fo.u3Form i.iU3 K (i.t.tPin + col))).toList)))

/-- Both halves: where the three runs return at one record that agrees with i in what is public, they are, at i, the written lists: equations. -/
def LawAny : Prop :=
  ∀ (A : Plan) (S : Shape) (gL : Forest.Heard) (i i0 : P.Runs.In) (K : ℕ) (k3 : PadIn),
    i.g = geoOf S → i.zk = gL.zk → A.NC = S.calls.size → Same i i0 → AllReturn i0 K k3 →
      P.Runs.firstRun i K = some (Fo.claim3T (oldOf S gL i) K ++ (Fo.claim4T (oldOf S gL i) K ++
          Fo.claim5T (oldOf S gL i) K), jP (Fo.attJoinsT A (oldOf S gL i))) ∧
        P.Runs.keysRun i k3 (jP (Fo.attJoinsT A (oldOf S gL i))) =
          some (Fo.attJoinsT A (oldOf S gL i)).kf ∧
        P.Runs.secondRun i K = some (Fo.claim6T (oldOf S gL i) K ++ (Fo.claim7T (oldOf S gL i) K ++
          Fo.claim8T (oldOf S gL i) K))

end Spec

theorem first_any : Spec.FirstAny := fun A S gL i K l j hg hz hN hr =>
  first_is_of A (oldOf S gL i) i (strip_is_old S gL i hg hz) hN K l j hr

theorem second_any : Spec.SecondAny := fun S gL i K l hg hz hr =>
  second_is_of (oldOf S gL i) i (strip_is_old S gL i hg hz) K l hr

theorem whole_any : Spec.WholeAny := by
  intro A S gL i K k3 l₁ l₂ j kf hg hz hN h1 hk h2
  obtain ⟨e1, ej⟩ := first_any A S gL i K l₁ j hg hz hN h1
  have ek := keys_is _ _ _ _ hk
  have e2 := second_any S gL i K l₂ hg hz h2
  subst e1 e2 ej ek
  unfold Fo.attT
  simp only [List.append_assoc]
  rfl

theorem law_any : Spec.LawAny := by
  intro A S gL i i0 K k3 hg hz hN H h0
  obtain ⟨l₁, j, kf, l₂, h1, hk, h2⟩ := returns_where _ _ K k3 H h0
  obtain ⟨e1, ej⟩ := first_any A S gL i K l₁ j hg hz hN h1
  have ek := keys_is _ _ _ _ hk
  have e2 := second_any S gL i K l₂ hg hz h2
  subst e1 ej e2 ek
  exact ⟨h1, hk, h2⟩

end K5Law
