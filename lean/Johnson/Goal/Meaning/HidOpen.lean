-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidOpen.lean: in scope the records that the checks close are open; so ClosedAt
can be met at all 25 sub-proofs.

closedAt_met (Johnson/Goal/Meaning/HidClosed.lean) has a premise: each of the 25 records openAt X k
has its list of tables open (funClosed = false). At an attention sub-proof that holds by startRec's
text. At a group of layers and at the head it is the plan's own field. No maker of a plan's record
writes that field: the first (shapeF) builds the record anew, with the field's default, false, and
the others keep it. The library's lemmas on these makers state the list of matrices and its length;
this file walks the same steps for funClosed.

Main names:
  pieces_open, shape_open, addTrees_open, borderMeans_open, ownerHeld_open   the makers.
  planG_open, plan_open, planH2_open   the plans of the groups of layers and of the head.
  open_of_core   in scope (openAt X k).funClosed = false for k < 25.
  closedAt_core   so, in scope, ClosedAt X holds of the records that closeFuns makes of them, at
    every choice of the lists of tables.

What is not claimed. That openAt is the record which a run closes
(Johnson/Goal/Meaning/HidClosed.lean's head). The full size alone. The program does not import this
file.
-/
import Johnson.Goal.Meaning.HidClosed
import Johnson.Goal.Meaning.HidOwner

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes OnBytes.Road OnBytes.Road.L5
open OnBytes.Model (TMat HTailF2 T2Foreign Fork Tail2 Settings)
open OnBytes.Model.Layer (Lay Pub HPlan2 Scales planG plansFrom plansG)
open OnBytes.Model.Head (HL Border Owner HPlanH2 planH2 ownerHeld)
open OnBytes.Model.Verify (publicOf layerShape)

theorem pieces_open {t t' : HTailF2} (h : t.piecesF = .ok t') : t'.funClosed = t.funClosed := by
  unfold HTailF2.piecesF at h
  obtain ⟨bz, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨f9, -, h⟩ := ok_of_bind h
  obtain ⟨pub, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  have e := (Except.ok.inj h).symm
  subst e
  rfl

/-- shape builds the record anew: its list of tables is open. -/
theorem shape_open {tl t' : HTailF2} {m : Array TMat} {txOf : Array (Option ℕ)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : ℕ}
    (h : tl.shape m txOf f hasU tau = .ok t') : t'.funClosed = false := by
  unfold HTailF2.shape HTailF2.shapeF at h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨r1, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨r2, -, h⟩ := ok_of_bind h
  obtain ⟨r3, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  exact pieces_open h

theorem addTrees_open {tl : HTailF2} {F : Fork} {T : Tail2} {nU aTX : Array ℕ} {hb hbLine : ℕ}
    {r : HTailF2 × Fork × Tail2} (h : tl.addTrees F T nU aTX hb hbLine = .ok r) :
    r.1.funClosed = tl.funClosed := by
  unfold HTailF2.addTrees HTailF2.addTreesF at h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨r1, -, h⟩ := ok_of_bind h
  obtain ⟨r2, -, h⟩ := ok_of_bind h
  obtain ⟨r3, -, h⟩ := ok_of_bind h
  obtain ⟨r4, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨r5, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨r6, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  have e := (Except.ok.inj h).symm
  subst e
  rfl

theorem borderMeans_open {tl t' : HTailF2} {iF ownerNo index : ℕ}
    (h : tl.borderMeans iF ownerNo index = .ok t') : t'.funClosed = tl.funClosed := by
  unfold HTailF2.borderMeans at h
  split at h
  · cases h
  · split at h
    · cases h
    · have e := (Except.ok.inj h).symm
      subst e
      rfl

theorem ownerHeld_open {O : Owner} {NGr : ℕ} {tl tl' : HTailF2} {Fp : Fork} {Tp : Tail2}
    (h : ownerHeld O NGr tl Fp Tp = .ok tl') : tl'.funClosed = tl.funClosed := by
  unfold Model.Head.ownerHeld at h
  cases hb : O.tl.ix.TX.back? with
  | none =>
    simp only [hb] at h
    have h' : (Except.error "internal-h-owner-TX" : Except String HTailF2) = .ok tl' := h
    cases h'
  | some t =>
    simp only [hb] at h
    obtain ⟨last, -, h⟩ := ok_of_bind (x := (pure t : Except String ℕ)) h
    obtain ⟨-, -, h⟩ := ok_of_bind h
    obtain ⟨-, -, h⟩ := ok_of_bind h
    obtain ⟨t3, h3, h⟩ := ok_of_bind h
    obtain ⟨pe, -, h⟩ := ok_of_bind h
    obtain ⟨-, -, h⟩ := ok_of_bind h
    have e := (Except.ok.inj h).symm
    subst e
    exact borderMeans_open h3

/-- In the plan of a group of layers the record's list of tables is open. -/
theorem planG_open {P : Pub} {g : ℕ} {O : Option HPlan2} {hp : HPlan2}
    (h : planG P g O = .ok hp) : hp.tl.funClosed = false := by
  unfold planG at h
  obtain ⟨b, hb, h⟩ := ok_of_bind h
  obtain ⟨t1, h1, h⟩ := ok_of_bind h
  obtain ⟨a, ha, h⟩ := ok_of_bind h
  obtain ⟨Tp, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_refuse h
  have k2 : hp.tl.funClosed = a.1.funClosed := by
    cases O with
    | none =>
      obtain ⟨-, h⟩ := ok_of_refuse h
      obtain ⟨-, h⟩ := ok_of_refuse h
      have e := (Except.ok.inj h).symm
      subst e
      rfl
    | some O =>
      cases hb2 : O.tl.ix.TX.back? with
      | none =>
        simp only [hb2] at h
        have h' : (Except.error "internal-g-owner-shape" : Except String HPlan2) = .ok hp := h
        cases h'
      | some t =>
        simp only [hb2] at h
        obtain ⟨-, h⟩ := ok_of_refuse h
        obtain ⟨-, h⟩ := ok_of_refuse h
        obtain ⟨t3, h3, h⟩ := ok_of_bind h
        obtain ⟨pe, -, h⟩ := ok_of_bind h
        obtain ⟨-, h⟩ := ok_of_refuse h
        obtain ⟨-, h⟩ := ok_of_refuse h
        have e := (Except.ok.inj h).symm
        subst e
        have k := borderMeans_open h3
        exact k
  rw [k2, addTrees_open ha, shape_open h1]

theorem plan_open {P : Pub} {G : Array HPlan2} (hG : plansG P = .ok G) {g : ℕ} {hp : HPlan2}
    (hg : G[g]? = some hp) : hp.tl.funClosed = false := by
  unfold plansG at hG
  obtain ⟨l, hl, hG⟩ := ok_of_bind hG
  have e := (Except.ok.inj hG).symm
  subst e
  have hg' : l[g]? = some hp := by simpa using hg
  obtain ⟨O', hO⟩ := plansFrom_at _ _ 0 none l hl g hp hg'
  exact planG_open hO

/-- In the head's plan the record's list of tables is open. -/
theorem planH2_open {g : Settings} {h : Model.Head.Shape} {L : HL} {b : Border} {O : Owner}
    {NGr lkW : ℕ} {hp : HPlanH2} (hpl : planH2 g h L b O NGr lkW = .ok hp) :
    hp.tl.funClosed = false := by
  unfold Model.Head.planH2 at hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨pc, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  cases hs : O.tl.mats[O.iXO]? with
  | none =>
    simp only [hs] at hpl
    have h' : (Except.error "internal-h-owner-TX" : Except String HPlanH2) = .ok hp := hpl
    cases h'
  | some M0 =>
    simp only [hs] at hpl
    obtain ⟨stream, hst, hpl⟩ := ok_of_bind (x := (pure M0 : Except String TMat)) hpl
    obtain ⟨t1, h1, hpl⟩ := ok_of_bind hpl
    obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
    obtain ⟨r, hr, hpl⟩ := ok_of_bind hpl
    obtain ⟨t2, Fp, Tp⟩ := r
    obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
    obtain ⟨Tp2, -, hpl⟩ := ok_of_bind hpl
    obtain ⟨t3, h3, hpl⟩ := ok_of_bind hpl
    obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
    have e := (Except.ok.inj hpl).symm
    subst e
    show t3.funClosed = false
    rw [ownerHeld_open h3, addTrees_open hr, shape_open h1]

section Core
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **In scope the records that the checks close are open.** -/
theorem open_of_core (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) :
    ∀ k < 25, (openAt X k).funClosed = false := by
  intro k hk
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  unfold openAt
  by_cases ho : k % 2 = 1
  · rw [if_pos ho]
    rfl
  · rw [if_neg ho]
    by_cases h24 : k = 24
    · subst h24
      obtain ⟨H0, hH, e⟩ := (Hd.publicH_of_public h).plan
      have e1 : tlAt X 24 = H0.tl := by
        unfold tlAt
        rw [if_neg (by omega), if_pos rfl, e]
      rw [e1]
      exact planH2_open hH
    · obtain ⟨sc, rope, wsLay, V, tokv, set, hP, hG⟩ := Hd.public_plans h
      obtain ⟨P, e⟩ := planG_there h C (by omega : k / 2 < 12)
      have e1 : tlAt X k = P.tl := by
        unfold tlAt
        rw [if_neg (by omega), if_neg h24, if_pos (by omega), e]
        rfl
      rw [e1]
      exact plan_open hG e

/-- **In scope ClosedAt can be met at all 25 sub-proofs**, at every choice of the lists of tables.
-/
theorem closedAt_core (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    (funs : ℕ → Array Model.HFun) :
    ClosedAt X fun k => { openAt X k with funClosed := true, funs := funs k } :=
  closedAt_met X (open_of_core h C) funs

end Core

end Meaning

#print axioms Meaning.pieces_open
#print axioms Meaning.shape_open
#print axioms Meaning.addTrees_open
#print axioms Meaning.borderMeans_open
#print axioms Meaning.ownerHeld_open
#print axioms Meaning.planG_open
#print axioms Meaning.plan_open
#print axioms Meaning.planH2_open
#print axioms Meaning.open_of_core
#print axioms Meaning.closedAt_core
