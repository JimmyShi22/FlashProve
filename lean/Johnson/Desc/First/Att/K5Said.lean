-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K5Said.lean: kind K5: what its four verbs have heard where they return: the
lists that the rounds hold, what the part's records hold of them, and what lies in the ledger.

Main names:
  `Open rs lead pre`: the first lead items of the first round left are the scalars pre, which wait
    for
    their message's end.
  `Put`, `Stays`, `Put.world`: what lies under a slot; that it still lies there in a later ledger;
    the hidden value under a slot in the ledger's world.
  `take_said`, `close_said`, `batch_said`, `sum_said` (`SumSaid`): the four verbs.

Premise: the ledger's three arrays have their length (Sized).
Sources (plain records, pure functions and lemmas on them; no routine that runs in a context):
OnBytes/Tie/Pv/Psc/Run/PscHide.lean (Sized, Filled, hideRun_ok); Run/ViewRounds.lean (RoundsAre,
partsRounds and their kin); Psc/PscView.lean (drawnOf); OnBytes/Tie/Pv/Att/HearStages.lean (PscH);
HearSaid.lean (Lies, got_both); OnBytes/Model/HideLaws.lean (Reading, Fork.worldOf).
Limits: one direction, from a return.
Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Att.HearSaid
import OnBytes.Tie.Pv.Psc.Run.ViewRounds
import Johnson.Desc.First.Att.K5Shape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.PscRun (drawnOf)
open OnBytes.Tie.Pv.Att (PscH Lies)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Sent VarsRead)

/-! ## Scalars -/

theorem scalars_holds : ∀ {l : List Fmt.ItemValue} {s : List E}, MaskedSum.scalars l = some s →
    l = s.map fun x => Fmt.ItemValue.e x.triple
  | [], s, h => by
    simp only [MaskedSum.scalars, Option.some.injEq] at h
    subst h
    rfl
  | .e u :: l, s, h => by
    simp only [MaskedSum.scalars, Option.map_eq_some_iff] at h
    obtain ⟨s', h1, h2⟩ := h
    subst h2
    rw [List.map_cons, ← scalars_holds h1]
    rfl
  | .f _ :: _, _, h => by cases h
  | .word _ :: _, _, h => by cases h
  | .root _ :: _, _, h => by cases h
  | .answer _ :: _, _, h => by cases h

theorem scalars_map : ∀ s : List E, MaskedSum.scalars (s.map fun x => Fmt.ItemValue.e x.triple) = some s
  | [] => rfl
  | x :: s => by
    show (MaskedSum.scalars (s.map fun x => Fmt.ItemValue.e x.triple)).map _ = _
    rw [scalars_map s]
    rfl

theorem scalars_take {l : List Fmt.ItemValue} {s : List E} (h : MaskedSum.scalars l = some s) (n : Nat) :
    MaskedSum.scalars (l.take n) = some (s.take n) := by
  rw [scalars_holds h, ← List.map_take]
  exact scalars_map _

theorem Sent.isRound {r : Fmt.RoundView} {n k : Nat} {s d : List E} (h : Sent r n k s d) : IsRound r (s, some d) :=
  ⟨scalars_holds h.1, fun l hl => by rw [← Option.some.inj hl, h.2.2.2]; rfl⟩

theorem Sent.isRound' {r : Fmt.RoundView} {n k : Nat} {s d : List E} (h : Sent r n k s d) : IsRound r (s, none) :=
  ⟨scalars_holds h.1, fun l hl => by cases hl⟩

theorem VarsRead.roundsAre : ∀ {vs : List Var} {used : List Fmt.RoundView} {l : List (List E × E)}, VarsRead vs used l →
    RoundsAre (l.map fun x => (x.1, some [x.2])) used ∧ l.map (·.1.length) = vs.map (·.d - 1)
  | [], [], [], _ => ⟨trivial, rfl⟩
  | _ :: _, _ :: _, (_, _) :: _, h => by
    obtain ⟨a, b⟩ := VarsRead.roundsAre h.2
    exact ⟨⟨Sent.isRound h.1, a⟩, by simp only [List.map_cons, b, h.1.2.1]⟩
  | [], [], _ :: _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, [], h => h.elim

/-! ## The scalars that wait -/

/-- The first lead items of the first round left are the scalars pre. -/
def Open : List Fmt.RoundView → Nat → List E → Prop
  | [], lead, pre => lead = 0 ∧ pre = []
  | r :: _, lead, pre => MaskedSum.scalars (r.vals.take lead) = some pre ∧ pre.length = lead

theorem open_zero : ∀ rs : List Fmt.RoundView, Open rs 0 []
  | [] => ⟨rfl, rfl⟩
  | _ :: _ => ⟨by simp [MaskedSum.scalars], rfl⟩

/-! ## What lies in the ledger, and stays -/

/-- Under slot j lies the scalar y with the factor f. -/
def Put (F : Fork) (j : Nat) (y f : E) : Prop :=
  F.gotF.getD j false = true ∧ F.vp.getD j zeroE = y ∧ F.mf.getD j zeroE = f

/-- What lies under a slot in F lies there in G. -/
def Stays (F G : Fork) : Prop := ∀ j y f, Put F j y f → Put G j y f

theorem Stays.refl (F : Fork) : Stays F F := fun _ _ _ h => h
theorem Stays.trans {F G H : Fork} (a : Stays F G) (b : Stays G H) : Stays F H := fun j y f h => b j y f (a j y f h)
theorem Put.lies {F : Fork} {j : Nat} {y f : E} (h : Put F j y f) : Lies F j y := ⟨h.1, h.2.1⟩

/-- A run of hidden values writes under slots that were empty. -/
theorem filled_stays {F G : Fork} {first : Nat} {l : List E} {factor : E} (a : Filled F G first l factor) :
    Stays F G := fun j y f h => by
  by_cases hr : j < first ∨ first + l.length ≤ j
  · obtain ⟨b1, b2, b3⟩ := a.other j hr
    exact ⟨by rw [b3 false]; exact h.1, by rw [b1]; exact h.2.1, by rw [b2]; exact h.2.2⟩
  · have hi : j - first < l.length := by omega
    obtain ⟨_, _, _, b4⟩ := a.here (j - first) hi
    rw [show first + (j - first) = j by omega] at b4
    exact (OnBytes.Tie.Pv.Att.got_both _ j h.1 b4).elim

theorem filled_put {F G : Fork} {first : Nat} {l : List E} {factor : E} (a : Filled F G first l factor) (i : Nat)
    (hi : i < l.length) : Put G (first + i) (l.getD i zeroE) factor := by
  obtain ⟨b1, b2, b3, _⟩ := a.here i hi
  exact ⟨b3, b1, b2⟩

theorem stays_next {F G : Fork} {n first : Nat} {l : List E} {factor : E}
    (a : Filled ({ F with next := n } : Fork) G first l factor) : Stays F G :=
  fun j y f h => filled_stays a j y f h

/-- The hidden value under a slot, in the ledger's world: what was shown less the factor times the
slot's mask entry. -/
theorem Put.world {K : Type} [CommRing K] (ρ : Reading K) {G : Fork} {j : Nat} {y f : E} (h : Put G j y f)
    (mask : Nat → K) (entry : Nat → Nat → Nat → K) :
    (G.worldOf ρ mask entry).slot j = ρ.val y - ρ.val f * mask j := by
  show ρ.val (G.vp.getD j zeroE) - ρ.val (G.mf.getD j zeroE) * mask j = _
  rw [h.2.1, h.2.2]

/-- n scalars are taken. -/
theorem take_said {n j lead lead' : Nat} {F G : Fork} {rs rs' : List Fmt.RoundView} {pre : List E}
    (h : take n (F, rs, lead) = some (j, G, rs', lead')) (hz : Sized F) (ho : Open rs lead pre) :
    ∃ v : List E, v.length = n ∧ rs' = rs ∧ Open rs' lead' (pre ++ v) ∧ j = F.next ∧ Sized G ∧ Stays F G ∧
      (∀ i, i < n → Put G (j + i) (v.getD i zeroE) oneE) ∧ G.next = F.next + n := by
  obtain ⟨e1, e2, e3, r, rest, v, a1, a2, a3, a4⟩ := take_spec h
  have hf := hideRun_ok _ _ _ _ _ a4 ⟨hz.vp, hz.mf, hz.got⟩
  rw [List.toList_toArray] at hf
  subst e1 e2 e3 a1
  refine ⟨v, a3, rfl, ⟨?_, by rw [List.length_append, ho.2, a3]⟩, rfl, hf.sized, stays_next hf,
    fun i hi => filled_put hf i (by rw [a3]; exact hi), hf.next⟩
  rw [List.take_add]
  exact scalars_append ho.1 a2

/-- A round is closed. -/
theorem close_said {n lead lead' : Nat} {F G : Fork} {rs rs' : List Fmt.RoundView} {d pre : List E}
    (h : close n (F, rs, lead) = some (d, G, rs', lead')) (ho : Open rs lead pre) :
    G = F ∧ lead' = 0 ∧ d.length = n ∧ ∃ r, rs = r :: rs' ∧ IsRound r (pre, some d) := by
  obtain ⟨e1, e2, r, a1, a2, a3, a4⟩ := close_spec h
  subst a1
  obtain ⟨b1, _⟩ := ho
  rw [← a2, List.take_length] at b1
  exact ⟨e1, e2, by rw [a4, List.length_map, a3], r, rfl, scalars_holds b1,
    fun l hl => by rw [← Option.some.inj hl, a4]; rfl⟩

/-- A batching element is drawn. -/
theorem batch_said {rows lead lead' : Nat} {F G : Fork} {rs rs' : List Fmt.RoundView} {w : Array E} {pre : List E}
    (h : batch rows (F, rs, lead) = some (w, G, rs', lead')) (ho : Open rs lead pre) :
    G = F ∧ lead' = 0 ∧ ∃ r x, rs = r :: rs' ∧ IsRound r (pre, some [x]) ∧
      w = (MaskedSum.powersFrom x rows oneE).toArray := by
  obtain ⟨e1, e2, r, x, a1, a2, a3, a4⟩ := batch_spec h
  subst a1
  obtain ⟨b1, _⟩ := ho
  rw [← a2, List.take_length] at b1
  exact ⟨e1, e2, r, x, rfl, ⟨scalars_holds b1, fun l hl => by rw [← Option.some.inj hl, ← a3]; rfl⟩, a4⟩

/-! ## A sumcheck -/

/-- Where the part's row returns: its write. -/
theorem row_write {h : MaskedSum.Heard} {S0 : E} {kept f : Aff} {F G : Fork}
    (hr : MaskedSum.row h S0 kept F = some (f, G)) :
    F.hideRun h.first (Array.replicate (MaskedSum.hidingAt (h.vars.zip h.r)).1.length zeroE) (subE zeroE oneE) =
      some G := by
  unfold MaskedSum.row at hr
  simp only [Option.bind_eq_bind] at hr
  obtain ⟨G', a1, a2⟩ := Option.bind_eq_some_iff.1 hr
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at a2
  rw [a1, a2.2]

/-- **What a sumcheck has heard**, with the part's record and the ledger. pre: the scalars that
waited. -/
structure SumSaid (C : Aff) (vs : List Var) (e : Ends) (F G : Fork) (pre : List E) (H : PscH) (used : List Fmt.RoundView)
    (hh : MaskedSum.Heard) : Prop where
  rounds : RoundsAre (partsRounds pre H.mu H.eps H.rs H.sentY H.beta H.v) used
  target : F.publicPart C = some hh.target
  start : hh.start = C
  eps : hh.eps = H.eps
  first : hh.first = F.next
  sEnd : hh.sEnd = F.next + MaskedSum.ownSlots (vs ++ [.point zeroE (e.dY + 1)])
  vars : hh.vars = vs ++ [.point zeroE (e.dY + 1)]
  r : hh.r = H.rs.map (·.2) ++ [H.beta]
  claim : hh.claim = MaskedSum.after (vs ++ [.point zeroE (e.dY + 1)]) (H.rs ++ [(H.sentY, H.beta)])
    (addE H.mu (mulE H.eps hh.target))
  lens : H.rs.map (·.1.length) = vs.map (·.d - 1)
  lenY : H.sentY.length = e.dY
  lenV : H.v.length = e.n
  shape : MaskedSum.shapeOk ⟨pre.length, vs, some e⟩ = true
  sized : Sized G
  stays : Stays F G
  next : G.next = hh.sEnd + e.n
  /-- the end values lie under their slots, with the factor beta -/
  ends : ∀ i, i < e.n → Put G (hh.sEnd + i) (H.v.getD i zeroE) H.beta
  /-- under the slots of the hiding polynomial's coefficients lies 0, with the factor -1 -/
  coefs : ∀ i, i < (MaskedSum.hidingAt (hh.vars.zip hh.r)).1.length → Put G (hh.first + i) zeroE (subE zeroE oneE)
  /-- the part's row has returned, from a ledger G1 -/
  row : ∃ (G1 : Fork) (f : Aff), MaskedSum.row hh zeroE {} G1 = some (f, G)

theorem sum_said {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard} {lead lead' : Nat} {F G : Fork}
    {rs rs' : List Fmt.RoundView} {pre : List E} (h : sum C (.sum vs e) (F, rs, lead) = some (hh, G, rs', lead'))
    (hz : Sized F) (ho : Open rs lead pre) :
    lead' = 0 ∧ ∃ (H : PscH) (used : List Fmt.RoundView), rs = used ++ rs' ∧ SumSaid C vs e F G pre H used hh := by
  obtain ⟨e1, e2, G1, f, a1, a2⟩ := sum_spec h
  obtain ⟨hs, T, R, b1, b2, b3, b4⟩ := MaskedSum.hear_spec a1
  obtain ⟨r0, used, rv, front, c1, c2, c3, c4, c5⟩ := MaskedSum.readAll_spec b2
  obtain ⟨u1, u2, l1, l2, d1, d2, d3, d4⟩ := c4.split
  obtain ⟨rY, sY, beta, f1, f2, f3⟩ := d4.one
  obtain ⟨g1, g2⟩ := VarsRead.roundsAre d3
  have hrs : rs = rs.take (vs.length + 3) ++ rs' := by rw [e1]; exact (List.take_append_drop _ _).symm
  -- the scalars that waited are the first message's front
  have hpre : pre = front := by
    rw [c1] at hrs
    rw [hrs] at ho
    have h1 := scalars_take c2.1 lead
    rw [ho.1] at h1
    have := Option.some.inj h1
    rw [this, ← c3, List.take_left']
    rfl
  subst hpre
  have hlast : (R.rounds.map (·.2)).getLastD zeroE = beta := by rw [d2, f2]; simp
  have hall : (⟨lead, vs, some e⟩ : MaskedSum.Call).all = vs ++ [.point zeroE (e.dY + 1)] := rfl
  rw [hall] at b3 b4
  rw [hlast, c5.2.1] at b4
  have F1 := hideRun_ok _ _ _ _ _ b4 ⟨hz.vp, hz.mf, hz.got⟩
  rw [List.toList_toArray] at F1
  have F2 := hideRun_ok _ _ _ _ _ (row_write a2) F1.sized
  rw [Array.toList_replicate] at F2
  have hsE : hh.sEnd = F.next + MaskedSum.ownSlots (vs ++ [.point zeroE (e.dY + 1)]) := by rw [b3]
  refine ⟨e2, ⟨R.mu, R.eps, l1, sY, beta, R.values⟩, rs.take (vs.length + 3), hrs, ?_⟩
  refine
    { rounds := ?_, target := by rw [b1, b3], start := by rw [b3], eps := by rw [b3], first := by rw [b3],
      sEnd := hsE, vars := by rw [b3], r := by rw [b3, d2, f2]; simp, claim := by rw [b3, d2, f2], lens := g2,
      lenY := f3.2.1, lenV := c5.2.1, shape := by rw [c3]; exact hs, sized := F2.sized,
      stays := (stays_next F1).trans (filled_stays F2),
      next := by rw [F2.next, F1.next, hsE],
      ends := fun i hi => filled_stays F2 _ _ _ (by rw [hsE]; exact filled_put F1 i (by rw [c5.2.1]; exact hi)),
      coefs := fun i hi => by
        have := filled_put F2 i (by rw [List.length_replicate]; exact hi)
        have e0 : (List.replicate (MaskedSum.hidingAt (hh.vars.zip hh.r)).1.length zeroE).getD i zeroE = zeroE := by
          simp [List.getD_eq_getElem?_getD, hi]
        rwa [e0] at this,
      row := ⟨G1, f, a2⟩ }
  rw [c1, d1, f1]
  show RoundsAre ((pre ++ [R.mu], some [R.eps]) :: (l1.map fun x => (x.1, some [x.2])) ++
    [(sY, some [beta]), (R.values, none)]) (r0 :: (u1 ++ [rY] ++ [rv]))
  have : r0 :: (u1 ++ [rY] ++ [rv]) = (r0 :: u1) ++ [rY, rv] := by simp
  rw [this]
  have k1 : RoundsAre ((pre ++ [R.mu], some [R.eps]) :: (l1.map fun x => (x.1, some [x.2]))) (r0 :: u1) :=
    ⟨Sent.isRound c2, g1⟩
  have k2 : RoundsAre [(sY, some [beta]), (R.values, none)] [rY, rv] := ⟨Sent.isRound f3, Sent.isRound' c5, trivial⟩
  exact RoundsAre.append k1 k2

end VerifiableInference.Desc.First.Att.P
