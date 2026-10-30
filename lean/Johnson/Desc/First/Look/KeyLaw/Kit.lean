-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Kit.lean: how a run of a flat function (Fl, OnBytes/K/Kc/Flat.lean)
that returns is taken apart: the rules for "do", for each small step, for the calls on the tape, and
for the four routines of the masked sumcheck.

Main names:
  bind_some, pure_some, must_some, need_some, ask_some, change_some, onTape_some, takeSlots_eq.
  recvLoop_spec, read_close, read_empty: elements taken off a round and the round's close: the round
    was just these elements and that draw.
  begin_fl, round_fl, ends_fl, row_fl: what pscBegin, roundIn, pscEnds and pscRow have read off the
    tape, done to the ledger and handed back.

Limits. Nothing is said where a function returns nothing.

-/
import OnBytes.K.Kc.FlatHear
import OnBytes.Tie.Pv.Psc.PscLater
import OnBytes.Tie.Pv.Psc.PscWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Aff Psc RoundName RoundForm)
open OnBytes.PscRun (took)

variable {α β : Type}

/-! ## "do" -/

theorem bind_some {x : Fl α} {f : α → Fl β} {F : Fork} {t : Tape} {r : β × Fork × Tape}
    (h : (x >>= f) F t = some r) : ∃ a G u, x F t = some (a, G, u) ∧ f a G u = some r := by
  have h' : Fl.andThen x f F t = some r := h
  unfold Fl.andThen at h'
  cases hx : x F t with
  | none => rw [hx] at h'; cases h'
  | some y =>
    obtain ⟨a, G, u⟩ := y
    rw [hx] at h'
    exact ⟨a, G, u, rfl, h'⟩

theorem pure_some {a : α} {F : Fork} {t : Tape} {r : α × Fork × Tape}
    (h : (pure a : Fl α) F t = some r) : r = (a, F, t) := by
  have h' : some (a, F, t) = some r := h
  exact (Option.some.inj h').symm

theorem must_some {b : Bool} {F G : Fork} {t u : Tape} {x : Unit}
    (h : Fl.must b F t = some (x, G, u)) : b = true ∧ G = F ∧ u = t := by
  unfold Fl.must at h
  cases b with
  | false => cases h
  | true =>
    have h' : some ((), F, t) = some (x, G, u) := h
    cases h'
    exact ⟨rfl, rfl, rfl⟩

theorem need_some {x : Option α} {F G : Fork} {t u : Tape} {a : α}
    (h : Fl.need x F t = some (a, G, u)) : x = some a ∧ G = F ∧ u = t := by
  unfold Fl.need at h
  cases x with
  | none => cases h
  | some y =>
    have h' : some (y, F, t) = some (a, G, u) := h
    cases h'
    exact ⟨rfl, rfl, rfl⟩

theorem ask_some {f : Fork → Option α} {F G : Fork} {t u : Tape} {a : α}
    (h : Fl.ask f F t = some (a, G, u)) : f F = some a ∧ G = F ∧ u = t := by
  unfold Fl.ask at h
  cases hf : f F with
  | none => rw [hf] at h; cases h
  | some y =>
    rw [hf] at h
    have h' : some (y, F, t) = some (a, G, u) := h
    cases h'
    exact ⟨rfl, rfl, rfl⟩

theorem change_some {f : Fork → Option Fork} {F G : Fork} {t u : Tape} {x : Unit}
    (h : Fl.change f F t = some (x, G, u)) : f F = some G ∧ u = t := by
  unfold Fl.change at h
  cases hf : f F with
  | none => rw [hf] at h; cases h
  | some y =>
    rw [hf] at h
    have h' : some ((), y, t) = some (x, G, u) := h
    cases h'
    exact ⟨rfl, rfl⟩

theorem onTape_some {g : Tape → Option (α × Tape)} {F G : Fork} {t u : Tape} {a : α}
    (h : Fl.onTape g F t = some (a, G, u)) : g t = some (a, u) ∧ G = F := by
  unfold Fl.onTape at h
  cases hg : g t with
  | none => rw [hg] at h; cases h
  | some y =>
    obtain ⟨y1, y2⟩ := y
    rw [hg] at h
    have h' : some (y1, F, y2) = some (a, G, u) := h
    cases h'
    exact ⟨rfl, rfl⟩

theorem takeSlots_eq (n : Nat) (F : Fork) (t : Tape) :
    Fl.takeSlots n F t = some (F.next, took F n, t) := rfl

theorem takeSlots_some {n : Nat} {F G : Fork} {t u : Tape} {a : Nat}
    (h : Fl.takeSlots n F t = some (a, G, u)) : a = F.next ∧ G = took F n ∧ u = t := by
  rw [takeSlots_eq] at h
  cases h
  exact ⟨rfl, rfl, rfl⟩

theorem slot_some {F G : Fork} {t u : Tape} {a : Nat}
    (h : Fl.slot F t = some (a, G, u)) : a = F.next ∧ G = F ∧ u = t := by
  have h' : some (F.next, F, t) = some (a, G, u) := h
  cases h'
  exact ⟨rfl, rfl, rfl⟩

theorem owe_some {what : String} {F G : Fork} {t u : Tape} {a : Nat}
    (h : Fl.owe what F t = some (a, G, u)) : G = (F.owe what).2 ∧ u = t := by
  have h' : some ((F.owe what).1, (F.owe what).2, t) = some (a, G, u) := h
  cases h'
  exact ⟨rfl, rfl⟩

/-! ## The tape -/

theorem recv_spec {t u : Tape} {x : E} (h : recv t = some (x, u)) :
    ∃ nm z w s d rest, t = ⟨nm, z, w, x :: s, d⟩ :: rest ∧ u = ⟨nm, z, w, s, d⟩ :: rest := by
  unfold recv at h
  split at h
  · cases h
    exact ⟨_, _, _, _, _, _, rfl, rfl⟩
  · cases h

/-- What the loop has taken stood in front of what is left of the open message. -/
theorem recvLoop_spec : ∀ (n : Nat) (a b : Array E) (t t1 : Tape), recvLoop n a t = some (b, t1) →
    ∃ pre : List E, pre.length = n ∧ b.toList = a.toList ++ pre ∧
      ∀ nm z w s d rest, t1 = ⟨nm, z, w, s, d⟩ :: rest → t = ⟨nm, z, w, pre ++ s, d⟩ :: rest
  | 0, a, b, t, t1, h => by
    have h' : some (a, t) = some (b, t1) := h
    cases h'
    exact ⟨[], rfl, by simp, fun _ _ _ _ _ _ e => e⟩
  | n + 1, a, b, t, t1, h => by
    unfold recvLoop at h
    cases hr : recv t with
    | none => rw [hr] at h; cases h
    | some y =>
      obtain ⟨x, u⟩ := y
      rw [hr] at h
      obtain ⟨nm0, z0, w0, s0, d0, rest0, e1, e2⟩ := recv_spec hr
      obtain ⟨pre, hl, hb, hp⟩ := recvLoop_spec n (a.push x) b u t1 h
      refine ⟨x :: pre, by simp [hl], by simp [hb], fun nm z w s d rest e => ?_⟩
      have := hp nm z w s d rest e
      rw [e2] at this
      cases this
      rw [e1]
      rfl

theorem closeOne_spec {name : String} {nz : Nat} {t u : Tape} {x : E}
    (h : closeOne name nz t = some (x, u)) : ∃ w, t = ⟨some name, nz, w, [], [x]⟩ :: u := by
  unfold closeOne at h
  split at h
  · split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      cases h
      obtain ⟨rfl, rfl⟩ := hc
      exact ⟨_, rfl⟩
    · cases h
  · cases h

theorem closeN_spec {name : String} {nz n : Nat} {t u : Tape} {d : List E}
    (h : closeN name nz n t = some (d, u)) :
    ∃ w, t = ⟨some name, nz, w, [], d⟩ :: u ∧ d.length = n := by
  unfold closeN at h
  split at h
  · split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      cases h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hc
      exact ⟨_, rfl, rfl⟩
    · cases h
  · cases h

/-- n elements are taken and the round is closed with one draw. -/
theorem read_close {n nz : Nat} {name : String} {t t1 u : Tape} {a : Array E} {x : E}
    (h1 : recvN n t = some (a, t1)) (h2 : closeOne name nz t1 = some (x, u)) :
    ∃ w, t = ⟨some name, nz, w, a.toList, [x]⟩ :: u ∧ a.size = n := by
  obtain ⟨w, rfl⟩ := closeOne_spec h2
  obtain ⟨pre, hl, hb, hp⟩ := recvLoop_spec n _ a t _ h1
  have hb' : a.toList = pre := by simpa using hb
  refine ⟨w, ?_, ?_⟩
  · rw [hp _ _ _ _ _ _ rfl, hb', List.append_nil]
  · rw [← Array.length_toList, hb', hl]

/-- n elements are taken and the round is closed without a draw. -/
theorem read_empty {n : Nat} {name : String} {t t1 u : Tape} {a : Array E} {x : Unit}
    (h1 : recvN n t = some (a, t1)) (h2 : Fl.emptyOn name t1 = some (x, u)) :
    ∃ w, t = ⟨some name, 0, w, a.toList, []⟩ :: u ∧ a.size = n := by
  unfold Fl.emptyOn at h2
  cases hc : closeN name 0 0 t1 with
  | none => rw [hc] at h2; cases h2
  | some y =>
    obtain ⟨d, u'⟩ := y
    rw [hc] at h2
    have h2' : some ((), u') = some (x, u) := h2
    cases h2'
    obtain ⟨w, rfl, hd⟩ := closeN_spec hc
    obtain rfl : d = [] := List.length_eq_zero_iff.1 hd
    obtain ⟨pre, hl, hb, hp⟩ := recvLoop_spec n _ a t _ h1
    have hb' : a.toList = pre := by simpa using hb
    refine ⟨w, ?_, ?_⟩
    · rw [hp _ _ _ _ _ _ rfl, hb', List.append_nil]
    · rw [← Array.length_toList, hb', hl]

/-- A round in which nothing is sent and one element is drawn. -/
theorem answer_fl {r : RoundName} {F G : Fork} {t u : Tape} {x : E}
    (h : Fl.answer r F t = some (x, G, u)) :
    ∃ w, t = ⟨some r.name, 0, w, [], [x]⟩ :: u ∧ G = F := by
  replace h := onTape_some h
  obtain ⟨h1, rfl⟩ := h
  obtain ⟨w, rfl⟩ := closeOne_spec h1
  exact ⟨w, rfl, rfl⟩

/-- A round in which nothing is sent and n elements are drawn. -/
theorem point_fl {r : RoundName} {n : Nat} {F G : Fork} {t u : Tape} {x : Array E}
    (h : Fl.point r n F t = some (x, G, u)) :
    ∃ w, t = ⟨some r.name, 0, w, [], x.toList⟩ :: u ∧ x.size = n ∧ G = F := by
  replace h := onTape_some h
  obtain ⟨h1, rfl⟩ := h
  unfold Fl.pointOn at h1
  cases hc : closeN r.name 0 n t with
  | none => rw [hc] at h1; cases h1
  | some y =>
    obtain ⟨d, u'⟩ := y
    rw [hc] at h1
    have h1' : some (d.toArray, u') = some (x, u) := h1
    cases h1'
    obtain ⟨w, rfl, hd⟩ := closeN_spec hc
    exact ⟨w, rfl, by simpa using hd, rfl⟩

/-! ## A round's key: what the flat functions read of it -/

/-- Name, how many draws are never 0, the elements sent, the elements drawn. -/
abbrev Key : Type := Option String × Nat × List E × List E

def key (r : FlatRound) : Key := (r.name, r.nz, r.sent, r.drawn)

def kr (name : RoundName) (nz : Nat) (sent drawn : List E) : Key := (some name.name, nz, sent,
    drawn)

/-- The keys of a masked sumcheck's rounds. -/
def pscKeys (mu eps : E) (rs : List (List E × E)) (y : Option ((List E × E) × List E)) : List Key :=
  kr .pscEpsilon 0 [mu] [eps] :: (rs.map fun r => kr .pscRound 0 r.1 [r.2]) ++
    match y with
    | none => []
    | some (ry, v) => [kr .pscY 1 ry.1 [ry.2], kr .pscValues 0 v []]

/-! ## The masked sumcheck's four routines -/

theorem begin_fl {C : Aff} {F G : Fork} {t u : Tape} {p : Psc}
    (h : Fl.pscBegin C F t = some (p, G, u)) :
    ∃ τ mu eps, F.publicPart C = some τ ∧
      t.map key = kr .pscEpsilon 0 [mu] [eps] :: u.map key ∧ G = took F 1 ∧
      p = { start := C, started := true, target := τ, first := F.next, eps := eps,
            claim := addE mu (mulE eps τ) } := by
  unfold Fl.pscBegin at h
  replace h := bind_some h
  obtain ⟨τ, G1, u1, h1, h⟩ := h
  replace h1 := ask_some h1
  obtain ⟨h1, rfl, rfl⟩ := h1
  replace h := bind_some h
  obtain ⟨q, G2, u2, h2, h⟩ := h
  cases pure_some h
  unfold Fl.pscBeginAt at h2
  replace h2 := bind_some h2
  obtain ⟨first, G3, u3, h3, h2⟩ := h2
  replace h3 := takeSlots_some h3
  obtain ⟨rfl, rfl, rfl⟩ := h3
  replace h2 := bind_some h2
  obtain ⟨mu, G4, u4, h4, h2⟩ := h2
  replace h4 := onTape_some h4
  obtain ⟨h4, rfl⟩ := h4
  replace h2 := bind_some h2
  obtain ⟨eps, G5, u5, h5, h2⟩ := h2
  replace h5 := onTape_some h5
  obtain ⟨h5, rfl⟩ := h5
  cases pure_some h2
  obtain ⟨w, rfl⟩ := closeOne_spec h5
  obtain ⟨nm, z, w', s, d, rest, e1, e2⟩ := recv_spec h4
  cases e2
  subst e1
  exact ⟨τ, mu, eps, h1, rfl, rfl, rfl⟩

theorem pscRound_fl {p p' : Psc} {w : OnBytes.Psc.Weight} {name : RoundName} {nz : Nat}
    {F G : Fork} {t u : Tape} {x : E}
    (h : Fl.pscRound p w (closeOne name.name nz) F t = some ((x, p'), G, u)) :
    ∃ sent : Array E, t.map key = kr name nz sent.toList [x] :: u.map key ∧ sent.size + 1 = w.d ∧
      G = took F (w.d - 1) ∧
      p' = { p with claim := OnBytes.Psc.polyAt (w.complete sent.toList p.claim) x,
                    vars := p.vars.push w, r := p.r.push x } := by
  unfold Fl.pscRound at h
  replace h := bind_some h
  obtain ⟨_, G1, u1, h1, h⟩ := h
  replace h1 := must_some h1
  obtain ⟨-, rfl, rfl⟩ := h1
  replace h := bind_some h
  obtain ⟨sent, G2, u2, h2, h⟩ := h
  replace h2 := onTape_some h2
  obtain ⟨h2, rfl⟩ := h2
  replace h := bind_some h
  obtain ⟨_, G3, u3, h3, h⟩ := h
  replace h3 := must_some h3
  obtain ⟨hs, rfl, rfl⟩ := h3
  replace h := bind_some h
  obtain ⟨r, G4, u4, h4, h⟩ := h
  replace h4 := onTape_some h4
  obtain ⟨h4, rfl⟩ := h4
  replace h := bind_some h
  obtain ⟨_, G5, u5, h5, h⟩ := h
  replace h5 := takeSlots_some h5
  obtain ⟨-, rfl, rfl⟩ := h5
  cases pure_some h
  obtain ⟨wr, rfl, -⟩ := read_close h2 h4
  exact ⟨sent, rfl, beq_iff_eq.1 hs, rfl, rfl⟩

theorem round_fl {form : RoundForm} {p p' : Psc} {z : E} {deg : Nat} {F G : Fork} {t u : Tape}
    {x : E} (h : Fl.roundIn form p z deg F t = some ((x, p'), G, u)) :
    ∃ (w : OnBytes.Psc.Weight) (sent : Array E), form.weight z deg = some w ∧
      t.map key = kr .pscRound 0 sent.toList [x] :: u.map key ∧ sent.size + 1 = w.d ∧
      G = took F (w.d - 1) ∧
      p' = { p with claim := OnBytes.Psc.polyAt (w.complete sent.toList p.claim) x,
                    vars := p.vars.push w, r := p.r.push x } := by
  unfold Fl.roundIn at h
  replace h := bind_some h
  obtain ⟨_, G1, u1, h1, h⟩ := h
  replace h1 := must_some h1
  obtain ⟨-, rfl, rfl⟩ := h1
  replace h := bind_some h
  obtain ⟨w, G2, u2, h2, h⟩ := h
  replace h2 := need_some h2
  obtain ⟨h2, rfl, rfl⟩ := h2
  obtain ⟨sent, e1, e2, e3, e4⟩ := pscRound_fl (name := .pscRound) h
  exact ⟨w, sent, h2, e1, e2, e3, e4⟩

theorem ends_fl {p p' : Psc} {dY n e : Nat} {F G : Fork} {t u : Tape}
    (h : Fl.pscEnds p dY n F t = some ((e, p'), G, u)) :
    ∃ (sent v : Array E) (beta : E),
      t.map key = kr .pscY 1 sent.toList [beta] :: kr .pscValues 0 v.toList [] :: u.map key ∧
      sent.size = dY ∧ v.size = n ∧ e = F.next + dY ∧
      (took (took F dY) n).hideRun e v beta = some G ∧
      p' = { p with
        claim := OnBytes.Psc.polyAt
          ((OnBytes.Psc.Weight.equality zeroE (dY + 1)).complete sent.toList p.claim) beta,
        vars := p.vars.push (OnBytes.Psc.Weight.equality zeroE (dY + 1)),
        r := p.r.push beta, ended := true } := by
  unfold Fl.pscEnds at h
  replace h := bind_some h
  obtain ⟨_, G1, u1, h1, h⟩ := h
  replace h1 := must_some h1
  obtain ⟨-, rfl, rfl⟩ := h1
  replace h := bind_some h
  obtain ⟨⟨beta, p1⟩, G2, u2, h2, h⟩ := h
  obtain ⟨sent, e1, e2, rfl, rfl⟩ := pscRound_fl (name := .pscY) h2
  replace h := bind_some h
  obtain ⟨v, G3, u3, h3, h⟩ := h
  replace h3 := onTape_some h3
  obtain ⟨h3, rfl⟩ := h3
  replace h := bind_some h
  obtain ⟨_, G4, u4, h4, h⟩ := h
  replace h4 := must_some h4
  obtain ⟨hv, rfl, rfl⟩ := h4
  replace h := bind_some h
  obtain ⟨_, G5, u5, h5, h⟩ := h
  replace h5 := onTape_some h5
  obtain ⟨h5, rfl⟩ := h5
  replace h := bind_some h
  obtain ⟨e', G6, u6, h6, h⟩ := h
  replace h6 := takeSlots_some h6
  obtain ⟨rfl, rfl, rfl⟩ := h6
  replace h := bind_some h
  obtain ⟨_, G7, u7, h7, h⟩ := h
  replace h7 := change_some h7
  obtain ⟨h7, rfl⟩ := h7
  cases pure_some h
  obtain ⟨wr, rfl, -⟩ := read_empty h3 h5
  have ed : (OnBytes.Psc.Weight.atZero (dY + 1)).d - 1 = dY := rfl
  refine ⟨sent, v, beta, ?_, ?_, beq_iff_eq.1 hv, rfl, h7, rfl⟩
  · rw [e1]; rfl
  · have : sent.size + 1 = dY + 1 := e2
    omega

theorem row_fl {p p' : Psc} {S0 : E} {kept row : Aff} {F G : Fork} {t u : Tape}
    (h : Fl.pscRow p S0 kept F t = some ((row, p'), G, u)) :
    F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G ∧ u = t ∧
      row = p.rowForm S0 kept := by
  unfold Fl.pscRow at h
  replace h := bind_some h
  obtain ⟨_, G1, u1, h1, h⟩ := h
  replace h1 := must_some h1
  obtain ⟨-, rfl, rfl⟩ := h1
  replace h := bind_some h
  obtain ⟨_, G2, u2, h2, h⟩ := h
  replace h2 := change_some h2
  obtain ⟨h2, rfl⟩ := h2
  cases pure_some h
  exact ⟨h2, rfl, rfl⟩

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.begin_fl
#print axioms VerifiableInference.Desc.K3.KeyLaw.round_fl
#print axioms VerifiableInference.Desc.K3.KeyLaw.ends_fl
#print axioms VerifiableInference.Desc.K3.KeyLaw.row_fl
