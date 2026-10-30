-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/TablesOk.lean: AN INVARIANT OF THE FIRST CHAIN's STATE FOR THE OUTPUT HEAD's
READS' TABLES: where tables are laid, they are what the reads' quiet step would lay off this very
state. IT RIDES OVER BOTH LATER SUB-PROTOCOLS OF KIND K1, at every segment. A definition, and
statements with their proofs.

Why. Five runs of claims of the output head's segment read the tables (the field t). The reads' quiet
step (K8.ReadsQuiet.head, Johnson/Desc/K8/ReadsQuiet.lean) lays them anew and tests nowhere that none
was laid. So "what a run's reader answers in front of the reads' place it answers behind" fails at a
state in which OTHER tables are laid. The tables are no value of the plan alone: the step makes them
of the covered positions (off the request's words and the heard reply) and of what the head's own
rounds heard. Hence the invariant speaks of the state itself.

Main names:
  TablesOk h L hp s   h, L, hp: the three fields of the step's parameters that it reads.
  tablesOk_alike      it passes between two states that part in nothing but what a later commitment
                      writes (RestAlike, Johnson/Desc/K1/Law/RestDef.lean).
  QuietT · quietT_layers | _att | _head | _blockAt | _readsQuietAt | _orLoud: the reads' quiet step
                      at each sort of segment. tablesOk_behind: behind the output head's step it
                      holds with no premise in front.
  LaterT · laterT_commitAtS | _laterAt | _joined | _k1Reads · tablesOk_later: **both later
                      sub-protocols, at any segment, on any rounds.**
  tablesOk_none       where no tables are laid, or the state stands in no head, it holds.
What is not claimed. That it holds at a reached state. Nothing on soundness, on an honest prover or
on hiding.

-/
import Johnson.Desc.K1.Law.ReadersSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S Here HeadOwn)
open OnBytes.Model.Stages (LinkH)

variable {Cl : Type}

/-- **Where the output head's tables are laid, they are what the reads' quiet step would lay off this
very state.** -/
def TablesOk (h : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2) (s : S) : Prop :=
  ∀ a t, s.here = .head a → a.t = some t →
    ∃ cov x, s.covered h.T h.V = .ok cov ∧ a.x = some x ∧
      K8.ReadsQuiet.tables h L hp cov x = .ok t

section
variable (h : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2)

theorem tablesOk_none (s : S) (hn : ∀ a, s.here = .head a → a.t = none) : TablesOk h L hp s := by
  intro a t ha ht
  rw [hn a ha] at ht
  cases ht

/-- It passes between two states that part in what a later commitment writes alone. -/
theorem tablesOk_alike {s s' : S} (hA : RestAlike s s') (k : TablesOk h L hp s) :
    TablesOk h L hp s' := by
  intro a' t ha' ht
  have hh : (restOf s).here = (restOf s').here := congrArg S.here hA
  have hreq : s'.req = s.req := (congrArg S.req hA).symm
  have hout : s'.out = s.out := hA.out.symm
  cases ha : s.here with
  | head a =>
    have e1 : hereRest (.head a) = hereRest (.head a') := by
      rw [← ha, ← ha']
      exact hh
    have e2 := Here.head.inj e1
    have o1 : a.t = a'.t := by
      have := congrArg HeadOwn.t e2
      exact this
    have o2 : a.x = a'.x := by
      have := congrArg HeadOwn.x e2
      exact this
    obtain ⟨cov, x, c1, c2, c3⟩ := k a t ha (o1.trans ht)
    refine ⟨cov, x, ?_, o2.symm.trans c2, c3⟩
    unfold S.covered S.replyTok? S.coveredAt at c1 ⊢
    rw [hreq, hout]
    exact c1
  | _ =>
    exfalso
    have e1 : hereRest s.here = hereRest s'.here := hh
    rw [ha, ha'] at e1
    cases e1

/-- An accept of q keeps the invariant. -/
def QuietT (q : Block S Cl) : Prop :=
  ∀ s s' rs gs, q.decide s rs gs = .ok s' → TablesOk h L hp s → TablesOk h L hp s'

theorem quietT_layers (P : K8.ReadsQuiet.PG) : QuietT h L hp (K8.ReadsQuiet.layers P) := by
  intro s s' rs gs e _
  obtain ⟨a, own, tl', ha, _, _, rfl⟩ := K8.ReadsQuiet.layers_ok e
  intro a2 t h1 _
  cases h1

theorem quietT_att {W : Verify.Public} {l g : Nat} {q : Block S Unit}
    (hq : First.Att.readsAtO W l g = some q) : QuietT h L hp q := by
  unfold First.Att.readsAtO at hq
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 hq
  intro s s' rs gs e _
  obtain ⟨a, t, tl, ha, rfl⟩ := Meaning.K2.readsAtSO_eq e
  intro a2 t2 h1 _
  cases h1

end

/-- **Behind the output head's quiet step**: with no premise in front. -/
theorem tablesOk_behind (P : K8.ReadsQuiet.PH) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (e : (K8.ReadsQuiet.head P).decide s rs gs = .ok s') :
    TablesOk P.h P.L P.hp s' := by
  obtain ⟨a, cov, x, t, tl', ha, ho, hcov, hx, ht, _, rfl⟩ := K8.ReadsQuiet.head_ok e
  intro a2 t2 h1 h2
  obtain rfl := Here.head.inj h1
  obtain rfl : t = t2 := Option.some.inj h2
  exact ⟨cov, x, hcov, hx, ht⟩

theorem quietT_head (P : K8.ReadsQuiet.PH) : QuietT P.h P.L P.hp (K8.ReadsQuiet.head P) :=
  fun _ _ _ _ e _ => tablesOk_behind P e

theorem quietT_blockAt {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {H : Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat} {q : Block S Unit}
    (e : K8.ReadsQuiet.blockAt G hS HLy H kinds l = some q) : QuietT hS HLy H q := by
  unfold K8.ReadsQuiet.blockAt at e
  obtain ⟨k, -, e⟩ := Option.bind_eq_some_iff.1 e
  split at e
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 e
    exact quietT_layers _ _ _ _
  · split at e
    · obtain rfl := Option.some.inj e
      exact quietT_head _
    · cases e

theorem quietT_readsQuietAt {G : ProofFile.Ground} (l : Nat) (X : LinkH) (piece : Nat) (q : Block S Unit)
    (e : ProofFile.readsQuietAt G l X piece = some q) : QuietT G.W.hS G.W.HLy G.W.H q := by
  unfold ProofFile.readsQuietAt at e
  by_cases h1 : (X.kind == 1) = true
  · rw [if_pos h1] at e
    by_cases h2 : (piece == 4) = true
    · rw [if_pos h2] at e
      exact quietT_att _ _ _ e
    · rw [if_neg h2] at e
      cases e
  · rw [if_neg h1] at e
    by_cases h2 : (piece == (if X.kind == 0 then 4 else 5)) = true
    · rw [if_pos h2] at e
      exact quietT_blockAt e
    · rw [if_neg h2] at e
      cases e

theorem quietT_orLoud (name : String) (p : Place) (what : String) (G : ProofFile.Ground) (l : Nat)
    (X : LinkH) (piece : Nat) :
    QuietT G.W.hS G.W.HLy G.W.H (ProofFile.orLoud name p what (ProofFile.readsQuietAt G l X piece)) := by
  cases hq : ProofFile.readsQuietAt G l X piece with
  | none => exact fun s s' rs gs e => nomatch e
  | some q => exact quietT_readsQuietAt l X _ q hq

/-! ## Both later sub-protocols -/

section
variable (h : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2)

theorem laterT_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    QuietT h L hp (commitAtS P link moment arrays : Block S Cl) :=
  fun s s' rs gs e k => tablesOk_alike h L hp (commitAtS_alike P link moment arrays s s' rs gs e) k

theorem laterT_joined (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (nm : String)
    (q : Block S Cl) (hq : QuietT h L hp q) :
    QuietT h L hp (Block.andThen nm (commitAtS P link moment arrays) q) := by
  intro s s' rs gs e k
  have e' : ((commitAtS P link moment arrays : Block S Cl).decide s
      (rs.take (commitAtS P link moment arrays : Block S Cl).rounds.length)
      (gs.take (commitAtS P link moment arrays : Block S Cl).openings)).bind (fun s₁ =>
      q.decide s₁ (rs.drop (commitAtS P link moment arrays : Block S Cl).rounds.length)
        (gs.drop (commitAtS P link moment arrays : Block S Cl).openings)) = .ok s' := e
  obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 e'
  exact hq _ _ _ _ h2 (laterT_commitAtS h L hp P link moment arrays _ _ _ _ h1 k)

end

/-- **THE INVARIANT RIDES OVER BOTH LATER SUB-PROTOCOLS OF KIND K1**, at any segment, on any rounds. -/
theorem tablesOk_later (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (e : (blkL Z G₀ l d X arrs).decide s rs gs = .ok s')
    (k : TablesOk G₀.W.hS G₀.W.HLy G₀.W.H s) : TablesOk G₀.W.hS G₀.W.HLy G₀.W.H s' := by
  cases d with
  | true => exact laterT_commitAtS _ _ _ _ _ _ _ s s' rs gs e k
  | false => exact laterT_joined _ _ _ _ _ _ _ _ _ (quietT_orLoud _ _ _ G₀ l X _) s s' rs gs e k

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.tablesOk_none
#print axioms VerifiableInference.Desc.K1.tablesOk_alike
#print axioms VerifiableInference.Desc.K1.quietT_layers
#print axioms VerifiableInference.Desc.K1.quietT_att
#print axioms VerifiableInference.Desc.K1.tablesOk_behind
#print axioms VerifiableInference.Desc.K1.quietT_orLoud
#print axioms VerifiableInference.Desc.K1.laterT_commitAtS
#print axioms VerifiableInference.Desc.K1.laterT_joined
#print axioms VerifiableInference.Desc.K1.tablesOk_later
